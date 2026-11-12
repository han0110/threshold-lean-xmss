import VCVio.OracleComp.QueryTracking.SubSpec
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkFirstOpening
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkPointTransfer

/-!
# Agreement of successful signing heads

The opening window retains the actual last-batch width. Its construction
ports the scheduler assembly of `TreeCheckWalkFirstOpening.firstRunOpening`
and `window_of_send`, using `guarded_fields` on the same actual snapshot.
This avoids losing the width in the existential `OpeningWindow` interface.

Arbitrary matching heads transfer to the actual opening tails. Each tail's
own successful run supplies its copy hashes in the final clean log. The
common held values and earlier outputs then identify the public-choice code;
cache replay identifies the two successful choices.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
set_option linter.unusedSectionVars false
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckWalkHeadInputs
open TreeCheckWalkRecipe TreeCheckWalkCoverage TreeCheckWalkState TreeCheckWalkEntry
open TreeCheckWalkFirstOpening TreeCheckWalkPointTransfer TreeCheckWalkEncoding
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (D : C.Coalition)
variable (circuits : Circuits) (settings : Settings) (top : TopTree)
variable (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C))

def WidthWindow (A : Adversary C E (Keys C) PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) (q : TreeCheckWalkDef.Pending A) : Prop :=
  let count := width K D circuits settings (.bottom b) x
    ((firstChunks settings (.bottom b)).length - 1)
  ∃ (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (inbox : C.Party → Mail C E) (W : C.Party → List (List Bit))
    (recs : C.Party → List (TreeSimCheckBatchRecord C)),
    (∀ h, h ∉ D.1 → (ds h).length = C.terms.length ∧
      ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer q.world.2 (.copy (vector count (v h T))) u) ∧
    (∀ i, i ∉ D.1 → (recs i).length = (firstChunks settings (.bottom b)).length ∧
      ((q.program i).run = pure none ∨
        anyAbort (inbox i) = false ∧
        (∀ h, h ∉ D.1 → inbox i h = repOutbox K h (v h) count (ds h) i) ∧
        q.program i = treeLockstepLocalPrelude (openTail K i count (v i) (inbox i)) >>= fun _ =>
          treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys setup i⟩ top (.bottom b)
            ((some (W i ++ assemble
              (((firstChunks settings (.bottom b)).getD ((firstChunks settings (.bottom b)).length - 1) []).map
                (circuits (x (refHolder D K.publicTerm)).parameter ·.kind))
              (fun g => ∑ T, treeSimOpenCopy K i count (v i) (inbox i) T g)), recs i),
              signingInitial K D circuits settings (.bottom b) x))) ∧
    ((¬ TreeSimHashBudgetCollision q.world.2 ∧
        ∃ i, i ∉ D.1 ∧ (q.program i).run ≠ pure none) →
      (∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < count →
        v i T g = v (refHolder D T) T g) ∧
      ∀ i k, i ∉ D.1 → k ∉ D.1 → (q.program i).run ≠ pure none →
        (q.program k).run ≠ pure none → W i = W k)

theorem widthWindow_of_send (A : Adversary C E (Keys C) PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) (j : ℕ) (last : j + 1 = (firstChunks settings (.bottom b)).length)
    (q : TreeCheckWalkDef.Pending A) (live : C.Party → Bool) (f : SendFields C)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (program : q.program = TreeCheckWalkDef.resume D
      (treeSimOpenPartial K D live (width K D circuits settings (.bottom b) x j) f.shares ds
        (fieldsCont K D circuits settings top (.bottom b) x setup j f)) sent)
    (existsLive : ∃ i, i ∉ D.1 ∧ live i = true)
    (lengths : ∀ i, (f.records i).length = j)
    (logged : ∀ i, i ∉ D.1 → live i = true → (ds i).length = C.terms.length ∧
      ∀ T, ∃ u, (ds i)[C.terms.idxOf T]? = some u ∧ TreeSimHashAnswer q.world.2
        (.copy (vector (width K D circuits settings (.bottom b) x j) (f.shares i T))) u)
    (agreement : Guard D A q →
      (∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < width K D circuits settings (.bottom b) x j →
        f.shares i T g = f.shares (refHolder D T) T g) ∧
      ∀ i k, i ∉ D.1 → k ∉ D.1 → (q.program i).run ≠ pure none →
        (q.program k).run ≠ pure none → f.saved i = f.saved k) :
    WidthWindow K D circuits settings top x setup A b q := by
  obtain ⟨i₀, honest₀, live₀⟩ := existsLive
  let count := width K D circuits settings (.bottom b) x j
  let v := fun i => if i ∉ D.1 ∧ live i ≠ true then f.shares i₀ else f.shares i
  let hashes := fun i => if i ∉ D.1 ∧ live i ≠ true then ds i₀ else ds i
  let inbox := fun i => treeSimOpenInbox K D (fun _ => true) count v hashes sent i
  let out := fun i g => ∑ T, treeSimOpenCopy K i count (v i) (inbox i) T g
  let records := fun i => f.records i ++ [f.record i (out i)]
  have filled (all : ∀ i, i ∉ D.1 → live i = true) : v = f.shares ∧ hashes = ds := by
    constructor <;> funext i <;> dsimp only [v, hashes] <;>
      rw [if_neg (fun h => h.2 (all i h.1))]
  have mail (all : ∀ i, i ∉ D.1 → live i = true) (i) :
      inbox i = treeSimOpenInbox K D live count f.shares ds sent i := by
    rw [show inbox i = treeSimOpenInbox K D (fun _ => true) count v hashes sent i from rfl,
      (filled all).1, (filled all).2]
    funext h
    by_cases hh : h ∈ D.1
    · simp [treeSimOpenInbox, hh]
    · simp [treeSimOpenInbox, hh, all h hh]
  have resume (i) (hi : i ∉ D.1) := resume_open K D live count f.shares ds
    (fieldsCont K D circuits settings top (.bottom b) x setup j f) sent i hi
  have all_of_live (hg : Guard D A q) : ∀ i, i ∉ D.1 → live i = true := by
    obtain ⟨i, hi, hn⟩ := hg.2
    rcases resume i hi with dead | ⟨all, rest⟩
    · exact False.elim (hn (by simpa only [program] using dead))
    · exact all
  have jj : j = (firstChunks settings (.bottom b)).length - 1 := by omega
  change ∃ v ds inbox W recs, _
  rw [← jj]
  refine ⟨v, hashes, inbox, f.saved, records, ?_, ?_, ?_⟩
  · intro h hh
    by_cases hl : live h = true
    · simpa only [hashes, v, hl, ne_eq, not_true_eq_false, and_false, if_false] using logged h hh hl
    · simpa only [hashes, v, if_pos (And.intro hh hl)] using logged i₀ honest₀ live₀
  · intro i hi
    refine ⟨by simp only [records, List.length_append, List.length_singleton, lengths, last], ?_⟩
    rcases resume i hi with dead | ⟨all, noabort, honest, shape⟩
    · exact .inl (by simpa only [program] using dead)
    · refine .inr ⟨?_, ?_, ?_⟩
      · simpa only [mail all i] using noabort
      · intro h hh
        rw [mail all i, (filled all).1, (filled all).2]
        exact honest h hh
      · rw [program, shape]
        have jj : j = (firstChunks settings (.bottom b)).length - 1 := by omega
        simp only [mail all i, (filled all).1, fieldsCont, sendCont, records, out, count, jj]
  · intro hg
    obtain ⟨held, common⟩ := agreement hg
    have all := all_of_live hg
    rw [(filled all).1]
    exact ⟨held, common⟩

set_option maxHeartbeats 1500000 in
/-- Actual scheduler assembly retaining the opening width. -/
theorem widthWindow (prims : Primitives) (positive : 0 < settings.batchSize)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (dealt : DealtInputs D x)
    (p) (setupRun : p ∈ support (treeSaltSetup prims D A x z))
    (q) (reached : Reached prims D Z
      (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x p)
      (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings (.bottom b)).length) q) :
    WidthWindow K D circuits settings top x p.1.2 A b q := by
  have same (i) : (x i).parameter = (x (refHolder D K.publicTerm)).parameter := by
    as_aux_lemma =>
      obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
      rw [hx i, hx (refHolder D K.publicTerm)]
      rfl
  have pos := firstChunks_bottom_pos settings positive b
  obtain ⟨j, last⟩ : ∃ j, j + 1 = (firstChunks settings (.bottom b)).length :=
    ⟨(firstChunks settings (.bottom b)).length - 1, by omega⟩
  let n := batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter j +
    sendRounds circuits settings (x (refHolder D K.publicTerm)).parameter
      ((firstChunks settings (.bottom b)).getD j [])
  have rounds : batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings (.bottom b)).length = n + 1 := by
    as_aux_lemma =>
      rw [batchStart_last circuits settings (.bottom b) _ j last]
      simp only [n, batchRounds, sendRounds, Nat.add_assoc]
  rw [rounds] at reached
  obtain ⟨prev, fuel, started, reply, before, fuelLeft, startRun, nonterminal, replyRun, qeq, logPrefix⟩ :=
    reached_last D prims A Z _ n q reached
  obtain ⟨live, f, lengths, programs⟩ := pending_fields K D circuits settings top x prims positive b A Z p
    same j last prev before
  let count := width K D circuits settings (.bottom b) x j
  let k := fieldsCont K D circuits settings top (.bottom b) x p.1.2 j f
  have starts : startSteps worldRoles D prev.program = (do
      let ds ← free (treeLockstepOpenHashes D live count f.shares)
      pure (treeSimOpenPartial K D live count f.shares ds k)) :=
    (start_congr D _ _ programs).trans (open_start_live K D live count
      (fun i => ⟨i, x i, setupKeys p.1.2 i⟩) (fun _ => rfl) f.shares k)
  have actualStart := startRun
  rw [starts] at startRun
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at startRun
  obtain ⟨⟨ds, cache⟩, hashes, rfl⟩ := startRun
  have program : q.program = TreeCheckWalkDef.resume D
      (treeSimOpenPartial K D live count f.shares ds k) reply.1.2 := congrArg TreeCheckWalkDef.Pending.program qeq
  have existsLive : ∃ i, i ∉ D.1 ∧ live i = true := by
    as_aux_lemma =>
      by_contra hn
      push Not at hn
      apply nonterminal
      intro i hi
      simp [treeSimOpenPartial, hi, hn i hi, Step.isDone]
  have logs := treeLockstep_open_hashes_logged prims D live count f.shares prev.world (ds, cache) hashes
  have logged (i) (hi : i ∉ D.1) (hl : live i = true) : (ds i).length = C.terms.length ∧
      ∀ T, ∃ u, (ds i)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer q.world.2 (.copy (vector count (f.shares i T))) u := by
    as_aux_lemma =>
      obtain ⟨len, hs⟩ := logs i hi hl
      refine ⟨len, fun T => ?_⟩
      obtain ⟨u, hu, hit⟩ := hs T
      exact ⟨u, hu, hit.imp (fun h => logPrefix.subset h) (fun h => logPrefix.subset h)⟩
  by_cases guard : Guard D A q
  swap
  · exact widthWindow_of_send K D circuits settings top x p.1.2 A b j last q live f ds reply.1.2
      program existsLive lengths logged (fun h => (guard h).elim)
  have allLive : ∀ i, i ∉ D.1 → live i = true := by
    as_aux_lemma =>
      obtain ⟨i, hi, hn⟩ := guard.2
      rcases resume_open K D live count f.shares ds k reply.1.2 i hi with dead | ⟨all, _⟩
      · exact False.elim (hn (by simpa only [program] using dead))
      · exact all
  let out := ((prev.state, treeSimOpenPartial K D live count f.shares ds k), cache)
  have pending : out ∈ support (pendingSteps prims D A n
      (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x p)) := by
    as_aux_lemma =>
      have zero : out ∈ support (pendingSteps prims D A 0 prev) := by
        as_aux_lemma =>
          simp only [pendingSteps, executeSteps, simulateQ_bind, simulateQ_pure, StateT.run_bind,
            StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff]
          exact ⟨_, actualStart, rfl⟩
      simpa only [Nat.add_zero] using reached_pending D prims A Z _ prev n before 0 out zero
  have good : ¬ TreeSimHashBudgetCollision cache.2 :=
    fun h => guard.1 (treeSimHashBudgetCollision_mono logPrefix h)
  have stepLive (i) (hi : i ∉ D.1) : out.1.2 i ≠ .done none := by
    as_aux_lemma =>
      simp [out, treeSimOpenPartial, hi, allLive i hi, treeSimOpenStep]
  obtain ⟨f', ds', lengths', shapes, logs', held, common⟩ := guarded_fields K D circuits settings top x prims A b z
    p setupRun same j last out pending good stepLive
  have steps : treeSimOpenPartial K D live count f.shares ds k =
      treeSimOpenPartial K D (fun _ => true) count f'.shares ds'
        (fieldsCont K D circuits settings top (.bottom b) x p.1.2 j f') := by
    as_aux_lemma =>
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimOpenPartial, hi]
      · simpa only [out, treeSimOpenPartial, if_neg hi, if_true] using shapes i hi
  rw [steps] at program
  apply widthWindow_of_send K D circuits settings top x p.1.2 A b j last q (fun _ => true) f' ds' reply.1.2
    program ⟨refHolder D K.publicTerm, (refHolder_spec D K.publicTerm).2, rfl⟩ lengths'
  · intro i hi _
    obtain ⟨len, hs⟩ := logs' i hi
    refine ⟨len, fun T => ?_⟩
    obtain ⟨u, hu, hit⟩ := hs T
    exact ⟨u, hu, hit.imp (fun h => logPrefix.subset h) (fun h => logPrefix.subset h)⟩
  · intro _
    exact ⟨held, fun i k _ _ _ _ => common i k⟩


/-- The opening tail hashes copies, and makes no public `.hash` query. -/
theorem openTail_quiet (i : C.Party) (count : ℕ) (v : Shares C Bit) (inbox : Mail C E) :
    IsQueryBoundP (openTail K i count v inbox) LocalHash 0 := by
  unfold openTail
  refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun _ _ => isQueryBoundP_pure _ _ _)
  apply IsQueryBoundP.liftComp_subSpec (p := fun t => LocalHash (C := C) (.inr t))
    (fun _ => Iff.rfl)
  unfold treeSimOpenCopyHashes
  simpa using queryBound_mapM (fun t => LocalHash (C := C) (.inr t)) _ 0 C.terms
    (fun _ _ => HashQuiet.hash_zero _ (by simp [LocalHash]))

/-- A successful actual tail identifies its opened bits against the logged
honest copies, from its own arbitrary starting state. -/
theorem openTail_value (prims : Primitives) (count : ℕ)
    (v : C.Party → Shares C Bit) (V : Shares C Bit)
    (held : ∀ h T g, h ∉ D.1 → h ∈ C.holders T → g < count → v h T g = V T g)
    (ds : C.Party → List HashOutput) (i : C.Party) (hi : i ∉ D.1) (inbox : Mail C E)
    (messages : ∀ h, h ∉ D.1 → inbox h = repOutbox K h (v h) count (ds h) i)
    (s final : TreeSimState C)
    (hashes : ∀ h, h ∉ D.1 → (ds h).length = C.terms.length ∧
      ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer s.2 (.copy (vector count (v h T))) u)
    (run : (some (), final) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (openTail K i count (v i) inbox))).run s))
    (good : ¬ TreeSimHashBudgetCollision final.2) :
    ∀ g < count, (∑ T, treeSimOpenCopy K i count (v i) inbox T g) = shareValue V g := by
  have logPrefix := (treeSimLoggedWorld_prefix prims D _ s (some (), final) run).subset
  unfold openTail at run
  simp only [free_bind, free_pure, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff, Prod.mk.injEq] at run
  obtain ⟨⟨cds, cache⟩, hashed, eq, rfl⟩ := run
  dsimp only at eq hashed
  have checked : TreeSimOpenValid K i inbox cds := by
    split_ifs at eq with h
    · exact h
  have evidence := treeSetup_hashes_logged prims D
    (fun T => Query.copy (vector count (treeSimOpenCopy K i count (v i) inbox T)))
    C.terms s (cds, final) hashed
  have copies : ∀ T, ∃ u, cds[C.terms.idxOf T]? = some u ∧
      TreeSimHashAnswer final.2 (.copy (vector count (treeSimOpenCopy K i count (v i) inbox T))) u := by
    intro T
    have hidx := idxOf_terms_lt T
    have hlen : C.terms.idxOf T < cds.length := evidence.length_eq ▸ hidx
    refine ⟨cds[C.terms.idxOf T], List.getElem?_eq_getElem hlen, ?_⟩
    simpa only [List.get_eq_getElem, List.getElem_idxOf] using evidence.get hidx hlen
  intro g hg
  apply Finset.sum_congr rfl
  intro T _
  exact treeLockstep_copy_logged K D count v V held ds (fun h hh => (hashes h hh).1)
    i hi inbox messages cds evidence.length_eq.symm final.2 good
    (fun h T hh => by
      obtain ⟨u, hu, hit⟩ := (hashes h hh).2 T
      exact ⟨u, hu, hit.imp (fun h => logPrefix h) (fun h => logPrefix h)⟩)
    copies checked T g hg

attribute [local irreducible] treeLockstepPublicChoiceCode

/-- The original agreement statement for every matching point, with its
sequential cache extensions and its final budget-collision guard. -/
theorem signingHeadsAgree (prims : Primitives) : SigningHeadsAgree prims K circuits settings := by
  intro positive top b D A x z Z dealt p hp q reached point matching i k hi hk
    s₁ grows₁ prefix₁ c₁ a₁ run₁ s₂ grows₂ prefix₂ c₂ a₂ run₂ clean
  obtain ⟨v, ds, inbox, W, recs, logged, shapes, agreement⟩ :=
    widthWindow K circuits settings prims positive top b D A x z Z dealt p hp q reached
  let jobs := ((firstChunks settings (.bottom b)).getD
    ((firstChunks settings (.bottom b)).length - 1) []).map
      (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)
  let count := (outputsOf jobs).length
  let opened := fun h g => ∑ T, treeSimOpenCopy K h count (v h) (inbox h) T g
  let point₀ : SigningPoint C := ⟨fun h => W h ++ assemble jobs (opened h), recs,
    fun h => if (q.program h).run = pure none then pure none else openTail K h count (v h) (inbox h)⟩
  have matching₀ : SigningMatches K D A circuits settings top x p.1.2
      (firstChunks settings (.bottom b)).length b q point₀ := by
    refine ⟨fun h hh => (shapes h hh).1, fun h hh => ?_⟩
    dsimp only [point₀]
    split_ifs with dead
    · apply OptionT.ext
      simpa only [localPrelude_none, failure_bind, OptionT.run_failure] using dead
    · exact ((shapes h hh).2.resolve_left dead).2.2
  have quiet (h : C.Party) : IsQueryBoundP (point₀.tail h) LocalHash 0 := by
    dsimp only [point₀]
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact openTail_quiet K h count (v h) (inbox h)
  have actual₁ := head_transfer prims K D A circuits settings top x p.1.2 _ b q
    point point₀ matching matching₀ i hi (quiet i) s₁ a₁ c₁ run₁
  have actual₂ := head_transfer prims K D A circuits settings top x p.1.2 _ b q
    point point₀ matching matching₀ k hk (quiet k) s₂ a₂ c₂ run₂
  have live₁ : (q.program i).run ≠ pure none := by
    intro dead
    simp only [point₀, if_pos dead, signingHead_rejected, free_pure, simulateQ_pure,
      StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at actual₁
  have live₂ : (q.program k).run ≠ pure none := by
    intro dead
    simp only [point₀, if_pos dead, signingHead_rejected, free_pure, simulateQ_pure,
      StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at actual₂
  have prefixA : a₁.2 <+: a₂.2 := prefix₂.trans (treeSimLoggedWorld_prefix prims D _ s₂ _ run₂)
  have prefixQ : q.world.2 <+: a₂.2 := prefix₁.trans
    ((treeSimLoggedWorld_prefix prims D _ s₁ _ run₁).trans prefixA)
  obtain ⟨held, common⟩ := agreement ⟨fun bad => clean (treeSimHashBudgetCollision_mono prefixQ bad),
    i, hi, live₁⟩
  obtain ⟨t₁, tail₁, code₁⟩ := head_split prims D _ b _ _ s₁ a₁ c₁ actual₁
  obtain ⟨t₂, tail₂, code₂⟩ := head_split prims D _ b _ _ s₂ a₂ c₂ actual₂
  have hashes (s : TreeSimState C) (pref : q.world.2 <+: s.2) :
      ∀ h, h ∉ D.1 → (ds h).length = C.terms.length ∧
        ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
          TreeSimHashAnswer s.2 (.copy (vector count (v h T))) u := by
    intro h hh
    refine ⟨(logged h hh).1, fun T => ?_⟩
    obtain ⟨u, hu, hit⟩ := (logged h hh).2 T
    exact ⟨u, hu, hit.imp (fun h => pref.subset h) (fun h => pref.subset h)⟩
  have bits₁ := openTail_value K D prims count v (fun T => v (refHolder D T) T) held ds i hi
    (inbox i) (((shapes i hi).2.resolve_left live₁).2.1) s₁ t₁ (hashes s₁ prefix₁)
    (by simpa only [point₀, if_neg live₁] using tail₁)
    (fun bad => clean (treeSimHashBudgetCollision_mono
      ((treeSimLoggedWorld_prefix prims D _ t₁ _ code₁).trans prefixA) bad))
  have bits₂ := openTail_value K D prims count v (fun T => v (refHolder D T) T) held ds k hk
    (inbox k) (((shapes k hk).2.resolve_left live₂).2.1) s₂ t₂
    (hashes s₂ (prefix₁.trans ((treeSimLoggedWorld_prefix prims D _ s₁ _ run₁).trans prefix₂)))
    (by simpa only [point₀, if_neg live₂] using tail₂)
    (fun bad => clean (treeSimHashBudgetCollision_mono
      (treeSimLoggedWorld_prefix prims D _ t₂ _ code₂) bad))
  have outputs : point₀.outputs i = point₀.outputs k := by
    dsimp only [point₀]
    rw [common i k hi hk live₁ live₂]
    congr 1
    exact treeLockstep_assemble_congr jobs (opened i) (opened k)
      (fun g hg => (bits₁ g hg).trans (bits₂ g hg).symm)
  have parameters : (x i).parameter = (x k).parameter := by
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    rw [hx i, hx k]
    rfl
  have same : treeLockstepPublicChoiceCode (x i).parameter b (point₀.outputs i) =
      treeLockstepPublicChoiceCode (x k).parameter b (point₀.outputs k) := by rw [parameters, outputs]
  obtain ⟨before, public₁⟩ := signingHead_public prims D _ b _ _ s₁ a₁ c₁ actual₁
  obtain ⟨_, trace, _, ready⟩ := publicRun_replay prims D _ before (some c₁, a₁) public₁
  rw [same] at ready
  rcases signingHead_fixed prims D (x k).parameter b (point₀.outputs k) (point₀.tail k) a₁.1.1 c₁
      (fun cache grows => ⟨trace, ready cache grows⟩) s₂ grows₂ (some c₂, a₂) actual₂ with
    rejected | accepted
  · cases rejected
  · exact (Option.some.inj accepted).symm

end ThresholdLeanXmssSecurity.TreeCheckWalkHeadInputs

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkHeadInputs.widthWindow_of_send' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkHeadInputs.widthWindow_of_send

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkHeadInputs.widthWindow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkHeadInputs.widthWindow

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkHeadInputs.openTail_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkHeadInputs.openTail_quiet

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkHeadInputs.openTail_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkHeadInputs.openTail_value

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkHeadInputs.signingHeadsAgree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkHeadInputs.signingHeadsAgree
