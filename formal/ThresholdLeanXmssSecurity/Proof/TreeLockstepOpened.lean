import ThresholdLeanXmssSecurity.Proof.TreeLockstep
import ThresholdLeanXmssSecurity.Proof.TreeSetupKeys

/-!
# Synchronized replicated openings

`treeLockstep_open_phase_value` proves agreement at a synchronized replicated
opening from common held copies, using the actual messages and copy-hash log.
`treeLockstep_digest_round_histories` proves that a surviving continuation of
the synchronized digest round forces all honest held histories to agree.
Both preserve one common adversary reply, the ordered continuations, and the
original budget-collision guard, from arbitrary incoming caches and logs.

The exact target `TreeLockstepOpenedGoal` remains unchanged and unproved.
The remaining work is to align these boundaries with each batch of the
audited ceremony and transfer agreement of the recorded histories to the
rerandomized copies passed to its output opening. These are joint-run
obligations; unrestricted per-party replay does not retain them. No
counterexample to the target has been established.

The pinned and current leanVM proofs were searched for synchronized opening
lemmas. The MPClan routing is threshold-specific; the argument reuses
`main_open_hash_sent`, the honest-holder lemma, and the actual hash-log
traversal from `TreeSetupKeys`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

private theorem openedAnswer_mono {a b : TreeSimLog C} (hab : a ⊆ b)
    {q : Query C} {h : HashOutput} (ha : TreeSimHashAnswer a q h) :
    TreeSimHashAnswer b q h := ha.imp (fun x => hab x) (fun x => hab x)

section Copies
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

/-- MPClan reconstruction against the actual logged hashes. The log guard is
the original budget event, including both honest and adversarial queries. -/
theorem treeLockstep_copy_logged (D : C.Coalition) (count : ℕ)
    (v : C.Party → Shares C Bit) (V : Shares C Bit)
    (held : ∀ h T g, h ∉ D.1 → h ∈ C.holders T → g < count → v h T g = V T g)
    (ds : C.Party → List HashOutput)
    (lengths : ∀ h, h ∉ D.1 → (ds h).length = C.terms.length)
    (i : C.Party) (hi : i ∉ D.1) (inbox : Mail C E)
    (messages : ∀ h, h ∉ D.1 → inbox h = repOutbox K h (v h) count (ds h) i)
    (cds : List HashOutput) (clength : cds.length = C.terms.length)
    (log : TreeSimLog C) (good : ¬ TreeSimHashBudgetCollision log)
    (sentHashes : ∀ h T, h ∉ D.1 → ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
      TreeSimHashAnswer log (.copy (vector count (v h T))) u)
    (copyHashes : ∀ T, ∃ u, cds[C.terms.idxOf T]? = some u ∧
      TreeSimHashAnswer log (.copy (vector count (repCopy K i (v i) count inbox T))) u)
    (checked : repCheck K i inbox cds) (T : C.Term) (g : ℕ) (hg : g < count) :
    repCopy K i (v i) count inbox T g = V T g := by
  by_cases hiT : i ∈ C.holders T
  · simpa only [repCopy, if_pos hiT] using held i T g hi hiT hg
  by_cases owner : K.owner T ∉ D.1
  · have hne : i ≠ K.owner T := fun h => hiT (h ▸ K.owner_held T)
    simp only [repCopy, if_neg hiT, messages _ owner, repOutbox, if_neg hne,
      Msg.part, List.getElem?_cons_zero, Msg.bitAt]
    rw [getD_flatMap_vector _ _ _ T (List.mem_filter.2 ⟨mem_terms T, by simp [hiT]⟩)
      (terms_nodup.filter _) g hg]
    exact held _ T g owner (K.owner_held T) hg
  · obtain ⟨h, hhT, hhD⟩ := main_exists_honest_holder D T
    have hne : h ≠ K.owner T := fun e => owner (e ▸ hhD)
    have hc := checked T hiT h hhT hne
    dsimp only at hc
    rw [messages h hhD, main_open_hash_sent K i h (v h) count (ds h) (lengths h hhD) T hiT hhT hne,
      lookup_zip_idxOf C.terms cds clength T (mem_terms T)] at hc
    obtain ⟨u, hu, hs⟩ := sentHashes h T hhD
    obtain ⟨w, hw, hc'⟩ := copyHashes T
    rw [hu, hw] at hc
    cases Option.some.inj hc
    have he : vector count (v h T) = vector count (repCopy K i (v i) count inbox T) := by
      by_contra hn
      exact good ⟨.copy _, .copy _, u, trivial, trivial, fun e => hn (Query.copy.inj e), hs, hc'⟩
    have he := congrArg (fun l : List Bit => l.getD g 0) he
    have hv : ∀ f : ℕ → Bit, (vector count f).getD g 0 = f g := by
      intro f
      simp [vector, List.getD_eq_getElem?_getD, List.getElem?_range hg]
    rw [hv, hv] at he
    exact he.symm.trans (held h T g hhD hhT hg)

end Copies

section Opening
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)

/-- A successful head of the actual opening retains every checked hash in
the log and proves that no honest operator had already aborted. -/
theorem treeLockstep_open_head_logged (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) (s final : TreeSimState C)
    (out : ℕ → Bit)
    (run : (some out, final) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C)))).run s)) :
    i ∉ D.1 ∧ (∀ h, h ∉ D.1 → live h = true) ∧
    ∃ cds, cds.length = C.terms.length ∧
      (∀ T, ∃ u, cds[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer final.2 (.copy (vector count
          (treeSimOpenCopy K i count (v i) (treeSimOpenInbox K D live count v ds sent i) T))) u) ∧
      TreeSimOpenValid K i (treeSimOpenInbox K D live count v ds sent i) cds ∧
      out = fun g => ∑ T, treeSimOpenCopy K i count (v i)
        (treeSimOpenInbox K D live count v ds sent i) T g := by
  unfold treeSimOpenHead at run
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at run
  rw [if_neg hi] at run
  by_cases hl : live i = true
  swap
  · simp only [if_neg hl, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at run
  rw [if_pos hl] at run
  by_cases ha : anyAbort (treeSimOpenInbox K D live count v ds sent i) = true
  · simp only [if_pos ha, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at run
  rw [if_neg ha] at run
  simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
    mem_support_pure_iff, Prod.mk.injEq] at run
  obtain ⟨⟨cds, cache⟩, hashed, he, rfl⟩ := run
  dsimp only at he hashed
  split_ifs at he with checked
  have outputs := Option.some.inj he
  have evidence := treeSetup_hashes_logged prims D
    (fun T => Query.copy (vector count (treeSimOpenCopy K i count (v i)
      (treeSimOpenInbox K D live count v ds sent i) T))) C.terms s (cds, final) hashed
  refine ⟨hi, ?_, cds, evidence.length_eq.symm, ?_, checked, outputs⟩
  · intro h hh
    by_contra hn
    have abort : anyAbort (treeSimOpenInbox K D live count v ds sent i) = true := by
      apply List.any_eq_true.mpr
      exact ⟨h, List.mem_finRange h, by simp [treeSimOpenInbox, hh, hn, Msg.isAbort]⟩
    exact ha abort
  · intro T
    have hidx := idxOf_terms_lt T
    have hlen : C.terms.idxOf T < cds.length := evidence.length_eq ▸ hidx
    refine ⟨cds[C.terms.idxOf T], List.getElem?_eq_getElem hlen, ?_⟩
    simpa only [List.get_eq_getElem, List.getElem_idxOf] using evidence.get hidx hlen

/-- The actual opening head returns the common held value. Hash evidence for
outgoing frames comes from the preceding joint hash traversal. -/
theorem treeLockstep_open_head_value (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (V : Shares C Bit)
    (held : ∀ h T g, h ∉ D.1 → h ∈ C.holders T → g < count → v h T g = V T g)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (i : C.Party) (s final : TreeSimState C) (out : ℕ → Bit)
    (hashes : ∀ h, h ∉ D.1 → live h = true →
      (ds h).length = C.terms.length ∧ ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer s.2 (.copy (vector count (v h T))) u)
    (run : (some out, final) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C)))).run s))
    (good : ¬ TreeSimHashBudgetCollision final.2) :
    ∀ g < count, out g = shareValue V g := by
  have grows := (treeSimLoggedWorld_prefix prims D _ s (some out, final) run).subset
  obtain ⟨hi, hlive, cds, hlen, hc, checked, rfl⟩ :=
    treeLockstep_open_head_logged prims K D live count v ds sent i s final out run
  intro g hg
  apply Finset.sum_congr rfl
  intro T _
  apply treeLockstep_copy_logged K D count v V held ds
    (fun h hh => (hashes h hh (hlive h hh)).1) i hi _ ?_ cds hlen final.2 good ?_ hc checked T g hg
  · intro h hh
    simp only [treeSimOpenInbox, if_neg hh, if_pos (hlive h hh)]
    rfl
  · intro h T hh
    obtain ⟨u, hu, he⟩ := (hashes h hh (hlive h hh)).2 T
    exact ⟨u, hu, openedAnswer_mono grows he⟩

/-- The initial local-copy hashes of one synchronized opening. -/
def treeLockstepOpenHashes (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) : OracleComp (LocalSpec C) (C.Party → List HashOutput) :=
  Concrete.sequenceFin fun i => if i ∉ D.1 ∧ live i = true then
    liftComp (treeSimOpenCopyHashes count (v i)) (LocalSpec C) else pure []

theorem treeLockstep_open_hashes_logged (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (s : TreeSimState C)
    (r : (C.Party → List HashOutput) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (treeLockstepOpenHashes D live count v))).run s)) :
    ∀ i, i ∉ D.1 → live i = true → (r.1 i).length = C.terms.length ∧
      ∀ T, ∃ u, (r.1 i)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer r.2.2 (.copy (vector count (v i T))) u := by
  letI : Preorder (TreeSimState C) := {
    le := fun s t => s.2 ⊆ t.2
    le_refl := fun _ => List.Subset.refl _
    le_trans := fun _ _ _ => List.Subset.trans }
  rw [treeLockstepOpenHashes, free_sequenceFin, simulateQ_sequenceFin] at run
  apply (sequenceFin_state_post _
    (fun i ds cache => i ∉ D.1 → live i = true → ds.length = C.terms.length ∧
      ∀ T, ∃ u, ds[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer cache.2 (.copy (vector count (v i T))) u) ?_ ?_ s r run).2
  · intro i cache result hresult
    refine ⟨(treeSimLoggedWorld_prefix prims D _ cache result hresult).subset, ?_⟩
    intro hi hl
    rw [if_pos (And.intro hi hl)] at hresult
    have evidence := treeSetup_hashes_logged prims D
      (fun T => Query.copy (vector count (v i T))) C.terms cache result hresult
    refine ⟨evidence.length_eq.symm, fun T => ?_⟩
    have hidx := idxOf_terms_lt T
    have hlen : C.terms.idxOf T < result.1.length := evidence.length_eq ▸ hidx
    exact ⟨result.1[C.terms.idxOf T], List.getElem?_eq_getElem hlen,
      by simpa only [List.get_eq_getElem, List.getElem_idxOf] using evidence.get hidx hlen⟩
  · intro i ds cache next hle h hi hl
    refine ⟨(h hi hl).1, fun T => ?_⟩
    obtain ⟨u, hu, he⟩ := (h hi hl).2 T
    exact ⟨u, hu, openedAnswer_mono hle he⟩

/-- The synchronized initial hash pass exposes exactly the actual waiting programs. -/
theorem treeLockstep_open_start (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) :
    startSteps worldRoles D (fun i => if live i then
      openRep K (localContext i) (v i) count else (failure : PartyM C E RealSpec (ℕ → Bit))) =
      (do let ds ← free (treeLockstepOpenHashes D live count v)
          pure (treeSimOpenPartial K D live count v ds (fun _ out => pure out))) := by
  unfold startSteps treeLockstepOpenHashes
  rw [free_sequenceFin]
  have one : ∀ i : C.Party,
      (if i ∈ D.1 then pure (Step.done none) else worldRoles.honest
        (advance ((if live i then openRep K (localContext i) (v i) count else
          (failure : PartyM C E RealSpec (ℕ → Bit))).run))) =
      (do let ds ← free (if i ∉ D.1 ∧ live i = true then
            liftComp (treeSimOpenCopyHashes count (v i)) (LocalSpec C) else pure [])
          pure (if i ∈ D.1 then .done none else if live i then
            treeSimOpenStep K i count (v i) ds pure else .done none)) := by
    intro i
    by_cases hi : i ∈ D.1
    · simp only [hi, if_true, not_true_eq_false, false_and, if_false, free_pure, pure_bind]
    · by_cases hl : live i = true
      · simp only [hi, hl, if_false, if_true, not_false_eq_true, true_and]
        simpa only [bind_pure, map_eq_bind_pure_comp, Function.comp_def, localContext] using
          treeSim_open_entry K (localContext i) count (v i) pure
      · simp only [hi, hl, if_false, not_false_eq_true, true_and]
        rfl
  simp_rw [one]
  rw [sequenceFin_bind_pure]
  rfl

/-- One actual local transition at the opening round, retaining aborts and all hashes. -/
theorem treeLockstep_open_local (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) :
    free (roundLocal D (treeSimOpenPartial K D live count v ds (fun _ out => pure out)) sent i) =
      (Step.done <$> free (liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C))) := by
  have inbox : (fun j => if j ∈ D.1 then sent j i else
      (treeSimOpenPartial K D live count v ds (fun _ out => pure out) j).delivered i) =
      treeSimOpenInbox K D live count v ds sent i := by
    funext j
    by_cases hj : j ∈ D.1 <;> by_cases hl : live j = true <;>
      simp [treeSimOpenPartial, treeSimOpenStep, treeSimOpenInbox, Step.delivered, hj, hl]
  by_cases hi : i ∈ D.1
  · simp [roundLocal, treeSimOpenHead, treeSimOpenPartial, hi, free_pure]
  · by_cases hl : live i = true
    · simp only [roundLocal, if_neg hi, treeSimOpenPartial, if_pos hl, treeSimOpenStep]
      simp only [treeSimOpenPartial, treeSimOpenStep] at inbox
      rw [inbox]
      unfold treeSimOpenHead
      rw [if_neg hi, if_pos hl]
      unfold exchangeResume anyAbort
      dsimp only
      split_ifs with habort
      · rfl
      · simp only [advance_oracleStep_bind, free_bind, liftComp_bind, liftComp_pure, free_pure,
          map_bind, map_pure]
        apply bind_congr
        intro copyDigests
        unfold require
        split_ifs <;> simp <;> rfl
    · simp [roundLocal, treeSimOpenPartial, treeSimOpenHead, hi, hl, free_pure]

/-- The real synchronous round uses one adversary reply for all reconstructions. -/
theorem treeLockstep_open_round (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (count : ℕ) (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) :
    stepRound worldRoles D A noFunctionality state
      (treeSimOpenPartial K D live count v ds (fun _ out => pure out)) = (do
      let b ← worldRoles.adversary (A.round state fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then
          (treeSimOpenPartial K D live count v ds (fun _ out => pure out) i).outbox c else none)
      let outputs ← free (Concrete.sequenceFin fun i =>
        liftComp (treeSimOpenHead K D live count v ds b.2 i) (LocalSpec C))
      pure (b.1, (fun i => Step.done (outputs i)), b.2)) := by
  rw [stepRound_real]
  apply bind_congr
  rintro ⟨state', sent⟩
  dsimp only
  rw [free_sequenceFin, free_sequenceFin]
  simp_rw [treeLockstep_open_local K D]
  simp only [map_eq_bind_pure_comp, Function.comp_def, sequenceFin_bind_pure, bind_assoc, pure_bind]

/-- Normalization of a complete synchronized opening; later idle fuel does not
add another exchange or resample any copy hash. -/
theorem treeLockstep_open_phase (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (count : ℕ) (v : C.Party → Shares C Bit) :
    executePhase worldRoles D A noFunctionality (fuel + 1) state
      (fun i => openRep K (localContext i) (v i) count) = (do
      let ds ← free (treeLockstepOpenHashes D (fun _ => true) count v)
      let b ← worldRoles.adversary (A.round state fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then treeSimOpenOut K i count (v i) (ds i) c else none)
      let outputs ← free (Concrete.sequenceFin fun i =>
        liftComp (treeSimOpenHead K D (fun _ => true) count v ds b.2 i) (LocalSpec C))
      pure (b.1, outputs)) := by
  unfold executePhase
  rw [show startSteps worldRoles D (fun i => openRep K (localContext i) (v i) count) = _ from
    treeLockstep_open_start K D (fun _ => true) count v]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro ds
  have running : ¬ ∀ i, i ∉ D.1 →
      (treeSimOpenPartial K D (fun _ => true) count v ds (fun _ out => pure out) i).isDone := by
    intro h
    obtain ⟨i, hi⟩ := coalition_has_honest D
    simpa only [treeSimOpenPartial, if_neg hi, if_true, treeSimOpenStep, Step.isDone] using h i hi
  rw [executeRounds, if_neg running, treeLockstep_open_round]
  simp only [bind_assoc, pure_bind]
  have view : (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
      (treeSimOpenPartial K D (fun _ => true) count v ds (fun _ out => pure out) i).outbox c else none) =
      (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then treeSimOpenOut K i count (v i) (ds i) c else none) := by
    funext c i
    by_cases hi : i ∈ D.1 <;> simp [treeSimOpenPartial, treeSimOpenStep, Step.outbox, hi]
  rw [view]
  apply bind_congr
  intro b
  apply bind_congr
  intro outputs
  cases fuel <;> simp [executeRounds, Step.isDone, Step.output]

/-- Every successful result of the jointly scheduled opening equals the
common held sharing. The incoming caches and transcript are arbitrary. -/
theorem treeLockstep_open_phase_value (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (count : ℕ) (v : C.Party → Shares C Bit) (V : Shares C Bit)
    (held : ∀ h T g, h ∉ D.1 → h ∈ C.holders T → g < count → v h T g = V T g)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option (ℕ → Bit))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (fuel + 1) state
        (fun i => openRep K (localContext i) (v i) count))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) :
    ∀ i, i ∉ D.1 → ∀ out, r.1.2 i = some out →
      ∀ g < count, out g = shareValue V g := by
  rw [treeLockstep_open_phase] at run
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨⟨ds, s₁⟩, hashes, ⟨b, s₂⟩, hadv, ⟨outputs, s₃⟩, heads, rfl⟩ := run
  have evidence := treeLockstep_open_hashes_logged prims D (fun _ => true) count v s (ds, s₁) hashes
  have grows := (treeSimLoggedWorld_prefix prims D _ s₁ (b, s₂) hadv).subset
  letI : Preorder (TreeSimState C) := {
    le := fun s t => s.2 ⊆ t.2
    le_refl := fun _ => List.Subset.refl _
    le_trans := fun _ _ _ => List.Subset.trans }
  rw [free_sequenceFin, simulateQ_sequenceFin] at heads
  have result := support_sequenceFin_state s₁ _
    (fun i out cache => ∀ value, out = some value → ¬ TreeSimHashBudgetCollision cache.2 →
      ∀ g < count, value g = shareValue V g) ?_ ?_ s₂ grows (outputs, s₃) heads
  · intro i _ value hv
    exact result.2 i value hv good
  · intro i cache hcache next hnext
    refine ⟨(treeSimLoggedWorld_prefix prims D _ cache next hnext).subset, ?_⟩
    intro value hv hg
    rcases next with ⟨out, final⟩
    dsimp only at hv hg
    subst out
    apply treeLockstep_open_head_value prims K D (fun _ => true) count v V held ds b.2
      i cache final value ?_ hnext hg
    intro h hh hl
    obtain ⟨hlen, hs⟩ := evidence h hh hl
    refine ⟨hlen, fun T => ?_⟩
    obtain ⟨u, hu, he⟩ := hs T
    exact ⟨u, hu, openedAnswer_mono hcache he⟩
  · intro i out cache next h hle value hv hg
    apply h value hv
    rintro ⟨q, r, u, hq, hr, hne, hqu, hru⟩
    exact hg ⟨q, r, u, hq, hr, hne, openedAnswer_mono hle hqu, openedAnswer_mono hle hru⟩

end Opening

section Digests
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)

/-- Acceptance of one synchronous digest round forces equality of all honest
held histories. Salts may differ; both hash levels are covered by the log guard. -/
theorem treeLockstep_digest_accepted_histories (live : C.Party → Bool)
    (histories : C.Party → C.Term → List Bit) (ds : C.Party → List HashOutput)
    (log : TreeSimLog C)
    (recorded : ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T → ∃ salt h d,
      TreeSimHashAnswer log (.history (histories i T)) h ∧
      TreeSimHashAnswer log (.digest salt h) d ∧ (ds i)[C.terms.idxOf T]? = some d)
    (good : ¬ TreeSimHashBudgetCollision log) (sent : C.Party → Mail C E) (acceptedBy : C.Party)
    (accepted : treeSimCheckResult K D live (.digests ds) sent acceptedBy = some ()) :
    ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      histories i T = histories j T := by
  have all : ∀ h, h ∉ D.1 → live h = true := by
    intro h hh
    by_contra hn
    rw [treeStages_check_inactive K D live (.digests ds) ⟨h, hh, hn⟩] at accepted
    cases accepted
  have checked : TreeSimCheckAccept K (.digests ds) acceptedBy
      (treeSimCheckInbox D live (.digests ds) sent acceptedBy) := by
    unfold treeSimCheckResult at accepted
    split_ifs at accepted with hi hl ha checked
    exact checked
  have read : ∀ h, h ∉ D.1 →
      (if h = acceptedBy then ds acceptedBy else
        Msg.hashesOf (treeSimCheckInbox D live (.digests ds) sent acceptedBy h)) = ds h := by
    intro h hh
    by_cases he : h = acceptedBy
    · simp [he]
    · simp [he, Ne.symm he, treeSimCheckInbox, hh, all h hh, treeSimCheckOut, digestOutbox,
        Msg.hashesOf]
  intro T i j hi hj hiT hjT
  have equal := (checked T i hiT j hjT).1
  change (if i = acceptedBy then ds acceptedBy else
      Msg.hashesOf (treeSimCheckInbox D live (.digests ds) sent acceptedBy i))[C.terms.idxOf T]? =
    (if j = acceptedBy then ds acceptedBy else
      Msg.hashesOf (treeSimCheckInbox D live (.digests ds) sent acceptedBy j))[C.terms.idxOf T]? at equal
  rw [read i hi, read j hj] at equal
  obtain ⟨si, hi', di, hhi, hdi, ei⟩ := recorded i hi (all i hi) T hiT
  obtain ⟨sj, hj', dj, hhj, hdj, ej⟩ := recorded j hj (all j hj) T hjT
  have deq := Option.some.inj (ei.symm.trans (equal.trans ej))
  subst dj
  have he : hi' = hj' := by
    by_contra hn
    exact good ⟨.digest si hi', .digest sj hj', di, trivial, trivial,
      (fun h => hn (Query.digest.inj h).2), hdi, hdj⟩
  subst hj'
  by_contra hn
  exact good ⟨.history (histories i T), .history (histories j T), hi', trivial, trivial,
    (fun h => hn (Query.history.inj h)), hhi, hhj⟩

private theorem opened_resume_none {α β : Type} (k : C.Party → β → PartyM C E RealSpec α)
    (out : C.Party → Option β) (s : TreeSimState C)
    (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k out)).run s)) :
    ∀ i, out i = none → r.1 i = .done none := by
  apply treeStages_resumeAll_log prims D k out
    (fun i step _ => out i = none → step = .done none) (fun _ _ _ _ _ h => h) ?_ s r run
  intro i cache next hnext hn
  rw [hn] at hnext
  simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
    mem_support_pure_iff] at hnext
  exact congrArg Prod.fst hnext

include K in
/-- Actual digest queries, one common rushing reply, and the ordered saved
continuations. Any surviving continuation certifies common honest histories. -/
theorem treeLockstep_digest_round_histories
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (live : C.Party → Bool)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (salts : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Step C E RealSpec TreeOutput) × (C.Party → Mail C E)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (do
      let waiting ← treeSimResumeAll
        (fun i (_ : Unit) => (compareDigests (ctx i) (salts i)).run (st i) >>= k i)
        (fun i => if i ∈ D.1 then none else if live i then some () else none)
      stepRound worldRoles D A noFunctionality state waiting)).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2)
    (survives : ∃ i, r.1.2.1 i ≠ .done none) :
    ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (st i).history T = (st j).history T := by
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨before, hbefore, hround⟩ := run
  obtain ⟨ds, waiting, recorded⟩ :=
    treeStages_digest_partial_log prims K D live ctx self salts st k s before hbefore
  rw [waiting, treeSim_check_round_factor] at hround
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hround
  obtain ⟨adv, hadv, next, hnext, rfl⟩ := hround
  obtain ⟨i, hi⟩ := survives
  have passed : treeSimCheckResult K D live (.digests ds) adv.1.2 i = some () := by
    have hn := opened_resume_none prims D _ _ adv.2 next hnext i
    cases he : treeSimCheckResult K D live (.digests ds) adv.1.2 i with
    | none => exact (hi (hn he)).elim
    | some u => cases u; rfl
  apply treeLockstep_digest_accepted_histories K D live (fun i => (st i).history) ds next.2.2
    ?_ good adv.1.2 i passed
  have grows := ((treeSimLoggedWorld_prefix prims D _ before.2 adv hadv).trans
    (treeSimLoggedWorld_prefix prims D _ adv.2 next hnext)).subset
  intro h hh hl T hT
  obtain ⟨hist, digest, hh', hd, idx⟩ := recorded h hh hl T hT
  exact ⟨vector 256 (salts h T), hist, digest, openedAnswer_mono grows hh',
    openedAnswer_mono grows hd, idx⟩

end Digests

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_open_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_open_phase

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_open_phase_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_open_phase_value

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_digest_accepted_histories' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_digest_accepted_histories

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_digest_round_histories' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_digest_round_histories

end ThresholdLeanXmssSecurity
