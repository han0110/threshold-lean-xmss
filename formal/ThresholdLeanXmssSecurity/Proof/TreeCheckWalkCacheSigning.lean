import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkCache
import ThresholdLeanXmssSecurity.Proof.TreeCheckSigningClock
import ThresholdLeanXmssSecurity.Proof.TreeCheckSigningChoice
import ThresholdLeanXmssSecurity.Proof.TreeCheckSigningProbe

/-! # The original signing-checkpoint cache certificate

Actual local passes retain one common clock and a floor on every future
coin query. A live checkpoint probes that floor at its own hybrid label.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning
open TreeCheckWalkRecipe TreeCheckWalkState TreeCheckWalkEntry TreeCheckWalkEncoding
open TreeCheckHonestDisc TreeCheckHonestLog TreeCheckSigningDisc TreeCheckSigningClock
open TreeCheckCoinClock TreeCheckSigningChoice TreeCheckWalkCache TreeSimHashCount TreeCheckSeenCovered
attribute [local instance] Classical.propDecidable
attribute [local irreducible] treeLockstepPublicChoiceCode merkleNode merklePath Concrete.layerRoot tweakable
set_option maxRecDepth 4000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
variable {C : Committee} {E α : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (D : C.Coalition)
variable (K : Constants C E) (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C))
variable (j : ℕ) (Z : Distinguisher C A.State TreeOutput)

abbrev pass (p : TreeCheckWalkDef.Pending A) :=
  (simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D p.program)).run p.world

-- Port of selectPending_finish, retaining just the actual local pass.
theorem selectPending_pass
    (gate : C.Party → OracleComp (LocalSpec C) (Option α))
    (cont : C.Party → α → PartyM C E RealSpec (TreeCheckWalkDef.Output (C := C)))
    (p : TreeCheckWalkDef.Pending A)
    (source : ∀ i, i ∉ D.1 → p.program i = treeLockstepLocalOption (gate i) >>= cont i) :
    pass prims D A p = selectPending prims D A gate cont p >>= pass prims D A := by
  have start := TreeCheckWalkFirstOpening.start_congr D _ _ source
  unfold pass selectPending
  rw [start, start_select_programs]
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind]

-- The same port keeps the scheduler reply after the selected local pass.
theorem selectPending_next
    (gate : C.Party → OracleComp (LocalSpec C) (Option α))
    (cont : C.Party → α → PartyM C E RealSpec (TreeCheckWalkDef.Output (C := C)))
    (p : TreeCheckWalkDef.Pending A) (fuel : ℕ)
    (source : ∀ i, i ∉ D.1 → p.program i = treeLockstepLocalOption (gate i) >>= cont i) :
    TreeCheckWalkDef.next prims D Z fuel p =
      selectPending prims D A gate cont p >>= TreeCheckWalkDef.next prims D Z fuel := by
  have start := TreeCheckWalkFirstOpening.start_congr D _ _ source
  unfold TreeCheckWalkDef.next selectPending
  rw [start, start_select_programs]
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind]

-- Port of prepare_finish with the two smaller continuations above.
theorem prepare_pass (p : TreeCheckWalkDef.Pending A) :
    pass prims D A p =
      prepare prims K D A circuits settings top tree x setup j p >>= pass prims D A := by
  unfold prepare
  cases tree with
  | top => simp
  | bottom b =>
    dsimp only
    split_ifs with first found
    · apply selectPending_pass
      intro i hi
      rw [(Classical.choose_spec found).2 i hi, signingHead_program]
    · simp
    · simp

theorem prepare_next (fuel : ℕ) (p : TreeCheckWalkDef.Pending A) :
    TreeCheckWalkDef.next prims D Z fuel p =
      prepare prims K D A circuits settings top tree x setup j p >>= TreeCheckWalkDef.next prims D Z fuel := by
  unfold prepare
  cases tree with
  | top => simp
  | bottom b =>
    dsimp only
    split_ifs with first found
    · apply selectPending_next
      intro i hi
      rw [(Classical.choose_spec found).2 i hi, signingHead_program]
    · simp
    · simp

/-- Every hit's first pass is an actual reached pass, even after preparations
whose decoder tests miss. No recognition premise is used. -/
theorem walk_hit_pass (start : TreeCheckWalkDef.Pending A) :
    ∀ (fuel n : ℕ) (p : TreeCheckWalkDef.Pending A), Reached prims D Z start n p → p.fuel = fuel →
    ∀ c, .inl c ∈ support (walk prims K D A circuits settings top tree x setup j Z fuel p) →
    ∀ out ∈ support (pass prims D A c.1.1),
      ∃ m q, Reached prims D Z start m q ∧ out ∈ support (pass prims D A q)
  | fuel, n, p, reached, fuelLeft, c, run, out, localRun => by
    have same : ({p with fuel := fuel} : TreeCheckWalkDef.Pending A) = p := by
      cases p; simp_all
    cases fuel with
    | zero =>
      simp only [walk, same, mem_support_bind_iff] at run
      obtain ⟨current, prepared, run⟩ := run
      split_ifs at run with hit
      · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
        subst run
        refine ⟨n, p, reached, ?_⟩
        rw [prepare_pass prims D K A circuits settings top tree x setup j p, mem_support_bind_iff]
        exact ⟨current, prepared, localRun⟩
      · simp only [support_map, Set.mem_image] at run
        obtain ⟨_, _, impossible⟩ := run
        cases impossible
    | succ fuel =>
      simp only [walk, same, mem_support_bind_iff] at run
      obtain ⟨current, prepared, run⟩ := run
      split_ifs at run with hit
      · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
        subst run
        refine ⟨n, p, reached, ?_⟩
        rw [prepare_pass prims D K A circuits settings top tree x setup j p, mem_support_bind_iff]
        exact ⟨current, prepared, localRun⟩
      · rw [mem_support_bind_iff] at run
        obtain ⟨outcome, nextRun, run⟩ := run
        cases outcome with
        | inr terminal => simp only [mem_support_pure_iff] at run; cases run
        | inl pending =>
          have actual : .inl pending ∈ support (TreeCheckWalkDef.next prims D Z fuel p) := by
            rw [prepare_next prims D K A circuits settings top tree x setup j Z fuel p, mem_support_bind_iff]
            exact ⟨current, prepared, nextRun⟩
          exact walk_hit_pass start fuel (n + 1) pending (.next reached fuelLeft actual)
            (next_fuel prims D A Z fuel p pending actual) c run out localRun

/-- Split a scheduler path at an exchange count. -/
theorem reached_split {start q : TreeCheckWalkDef.Pending A} (n m : ℕ)
    (h : Reached prims D Z start (n + m) q) :
    ∃ p, Reached prims D Z start n p ∧ Reached prims D Z p m q := by
  induction m generalizing q with
  | zero => exact ⟨q, by simpa only [Nat.add_zero] using h, .start⟩
  | succ m ih =>
    rw [Nat.add_succ] at h
    cases h with
    | next before fuel run =>
      obtain ⟨p, first, rest⟩ := ih before
      exact ⟨p, first, .next rest fuel run⟩

theorem reached_prefix {start q : TreeCheckWalkDef.Pending A} {n : ℕ}
    (h : Reached prims D Z start n q) : start.world.2 <+: q.world.2 := by
  induction h with
  | start => exact List.prefix_refl _
  | next before fuel run ih => exact ih.trans (TreeCheckWalkDef.next_prefix prims D Z _ _ _ run)

theorem pass_residual (p : TreeCheckWalkDef.Pending A)
    (out : (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C))) × TreeSimState C)
    (run : out ∈ support (pass prims D A p)) (i : C.Party) (hi : i ∉ D.1) (inbox : Mail C E) :
    Residual 1 (p.program i).run (resumed (out.1 i) inbox) := by
  have steps := mem_support_sequenceFin_oc _ _ (treeCheck_logged_support prims D _ _ run) i
  simp only [if_neg hi, worldRoles] at steps
  exact Residual.of_advance (out.1 i) (treeSimCheck_support_free _ steps) inbox

-- Port of Disc.bind, restricting its continuation to the requested horizon.
theorem disc_bind_prefix {β : Type} {limit n : ℕ} {keys : Set HashOutput}
    {P : OracleComp (PartySpec C E RealSpec) (Option α)} (h : Disc limit keys P)
    (f : Option α → OracleComp (PartySpec C E RealSpec) (Option β))
    (rest : ∀ a, a ∈ support P → CheckDisc limit n ∅ (f a)) :
    CheckDisc limit n keys (P >>= f) := by
  induction P generalizing n keys with
  | pure a =>
    change CheckDisc limit n keys (f a)
    exact (rest a (by change a ∈ support (Pure.pure a : OracleComp (PartySpec C E RealSpec) _); simp)).mono
      le_rfl (Set.empty_subset _)
  | queryBind t k ih =>
    cases n with
    | zero => exact .zero _ _
    | succ n =>
      rcases t with (q | out) | impossible
      · refine .queryLocal _ _ _ _ (h (n + 1)).local_inv.1 fun r => ?_
        apply ih r (fun m => ?_) (fun a ha => ?_)
        · cases m with
          | zero => exact .zero _ _
          | succ m => exact (h (m + 1)).local_inv.2 r
        · apply rest a
          change a ∈ support (OracleComp.lift (OracleSpec.query
            (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= k)
          rw [mem_support_bind_iff]
          exact ⟨r, by simp; exact Set.mem_univ _, ha⟩
      · refine .round _ _ _ _ fun inbox => ?_
        apply ih inbox (fun m => (h (m + 1)).round_inv inbox) (fun a ha => ?_)
        apply (rest a ?_).antitone (Nat.le_succ n)
        change a ∈ support (OracleComp.lift (OracleSpec.query
          (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>= k)
        rw [mem_support_bind_iff]
        exact ⟨inbox, by simp; exact Set.mem_univ _, ha⟩
      · exact impossible.elim

theorem disc_party_prefix {β : Type} {limit n : ℕ} {p : PartyM C E RealSpec α}
    {f : α → PartyM C E RealSpec β} (h : Disc limit ∅ p.run)
    (rest : ∀ a, some a ∈ support p.run → CheckDisc limit n ∅ (f a).run) :
    CheckDisc limit n ∅ (p >>= f).run := by
  simp only [OptionT.run_bind, Option.elimM]
  apply disc_bind_prefix h
  intro a ha
  cases a with
  | none => exact .pure _ _ _
  | some a => exact rest a ha

theorem localOption_quiet (gate : OracleComp (LocalSpec C) (Option α))
    (quiet : IsQueryBoundP gate CheckQuery 0) :
    PartyBudget CheckQuery (treeLockstepLocalOption (E := E) gate) 0 := by
  unfold treeLockstepLocalOption
  refine (localStep_bound (E := E) (G := RealSpec) quiet).bind (m := 0) fun out => ?_
  cases out with
  | none => exact party_quiet_of_zero PartyBound.failure
  | some _ => exact .pure _

variable (b : Fin (2 ^ layerHeight))

/-- Opening the last first-run result and choosing its signing head is quiet
through the first exchange of every resulting caller. -/
theorem entry_first (positive : 0 < settings.batchSize) (i : C.Party)
    (outputs : List (List Bit)) (records : List (TreeSimCheckBatchRecord C))
    (tail : OracleComp (LocalSpec C) (Option Unit)) (quiet : IsQueryBoundP tail CheckQuery 0) (limit : ℕ) :
    CheckDisc limit 1 ∅
      (treeLockstepLocalPrelude tail >>= fun _ =>
        treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys setup i⟩ top (.bottom b)
          ((some outputs, records), signingInitial K D circuits settings (.bottom b) x)).run := by
  rw [signingHead_program]
  apply disc_party_prefix (Disc.of_quiet (localOption_quiet _ (head_quiet b _ _ _ quiet)))
  intro choice _
  obtain ⟨head, rest, chunks⟩ := signing_chunks_nonempty settings b positive choice.2.2
  rw [signingCont_caller K D circuits settings top x setup b (fun _ => outputs) (fun _ => records)
    choice head rest chunks i]
  exact sign_caller_first K D circuits settings top x setup b _ limit _ i (isQueryBoundP_pure _ _ _)

/-- The initial complete discipline includes its next quiet signing-entry pass. -/
theorem initial_entry_disc (positive : 0 < settings.batchSize) (dealt : DealtInputs D x)
    (start : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) (i : C.Party) :
    CheckDisc (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings (.bottom b)) (firstChunks settings (.bottom b)).length)
      (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings (.bottom b)).length + 1) ∅
      ((TreeCheckWalkDef.initial K circuits settings top (.bottom b) x start).program i).run := by
  have pos := firstChunks_bottom_pos settings positive b
  obtain ⟨head, rest, chunks⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos pos)
  rw [initial_program K D A circuits settings top (.bottom b) x start head rest chunks i, boundary_program]
  apply (initial_complete_checkDisc K D circuits settings top (.bottom b) x start.1.2 dealt i).of_residual
  intro Q run
  have same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter := by
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    rw [hx i, hx (refHolder D K.publicTerm)]; rfl
  rcases residual_first_entry_quiet K D circuits settings top (.bottom b) x start.1.2 pos
      (firstCaller start.1.2) i same (isQueryBoundP_pure _ _ _) ⟨[], rfl⟩ run with
    aborted | ⟨outputs, records, tail, quiet, rfl⟩
  · rw [aborted]; exact .pure _ _ _
  · simpa only [ite_self, signingInitial] using entry_first D K circuits settings top x start.1.2 b positive i outputs records tail quiet _

-- Port of reached_honest using exactly N passes rather than N+1.
theorem reached_honest_cut (limit N : ℕ) (start : TreeCheckWalkDef.Pending A)
    (honest : HonestCheckLog limit start.world.1.1 start.world.2)
    (disc : ∀ i, i ∉ D.1 → CheckDisc limit N ∅ (start.program i).run)
    {m : ℕ} {q : TreeCheckWalkDef.Pending A}
    (reached : Reached prims D Z start m q) (below : m ≤ N) :
    HonestCheckLog limit q.world.1.1 q.world.2 := by
  induction reached with
  | start => exact honest
  | @next n fuel p q reached fuelLeft run ih =>
    apply next_honest prims D limit Z fuel p q (ih (by omega)) _ run
    intro i hi
    exact ((disc i hi).residual (Reached.residual prims D Z reached i hi) (by omega)).antitone (by omega)

/-- The actual first-pass output carries a common log cutoff and future floor. -/
def PassClock (out : (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C))) × TreeSimState C) : Prop :=
  ∃ limit, HonestCheckLog limit out.2.1.1 out.2.2 ∧
    ∀ i, i ∉ D.1 → ∀ inbox, CheckFloor limit (resumed (out.1 i) inbox)

theorem signing_suffix_clock (caller : Caller C)
    (same : ∀ i, (x i).parameter = (x (refHolder D K.publicTerm)).parameter)
    (quiet : ∀ i, IsQueryBoundP (caller.tail i) CheckQuery 0)
    (current : (firstChunks settings (.bottom b)).length < treeBatches settings (.bottom b))
    (base q : TreeCheckWalkDef.Pending A) (t : ℕ)
    (common : ∀ i, i ∉ D.1 → (base.program i).run = pure none ∨
      Residual 1 (callerProgram K D circuits settings top (.bottom b) x setup
        (firstChunks settings (.bottom b)).length caller i).run (base.program i).run)
    (honest : ∀ limit, lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
        (lockstepChunks settings caller.encoding (.bottom b)) (firstChunks settings (.bottom b)).length ≤ limit →
      HonestCheckLog limit base.world.1.1 base.world.2)
    (reached : Reached prims D Z base t q)
    (out : (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C))) × TreeSimState C)
    (run : out ∈ support (pass prims D A q)) : PassClock D out := by
  obtain ⟨lower, clock⟩ := sign_caller_clock circuits settings K D top x setup b
    (firstChunks settings (.bottom b)).length (t + 2) le_rfl current caller
  set limit := callerClock circuits settings (x (refHolder D K.publicTerm)).parameter
    (lockstepChunks settings caller.encoding (.bottom b)) (firstChunks settings (.bottom b)).length (t + 2)
  have disc : ∀ i, i ∉ D.1 → CheckDisc limit (t + 1) ∅ (base.program i).run := by
    intro i hi
    rcases common i hi with aborted | residual
    · rw [aborted]; exact .pure _ _ _
    · simpa using ((clock i (same i) (quiet i)).1.residual residual (by omega))
  have log := reached_honest prims D limit t Z base (honest limit lower) disc reached le_rfl
  refine ⟨limit, start_honest prims D limit q.program ?_ q.world log out run, ?_⟩
  · intro i hi
    simpa using ((disc i hi).residual (Reached.residual prims D Z reached i hi) (by omega))
  · intro i hi inbox
    have tail := (Reached.residual prims D Z reached i hi).trans (pass_residual prims D A q out run i hi inbox)
    rcases common i hi with aborted | first
    · rw [aborted] at tail
      rw [tail.pure_inv]
      exact .pure _ _
    · apply (clock i (same i) (quiet i)).2
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using first.trans tail

/-- The quiet entry pass can be classified by its actual common choice. -/
theorem entry_pass_clock (positive : 0 < settings.batchSize) (dealt : DealtInputs D x)
    (z : Aux) (start : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (setupRun : start ∈ support (treeSaltSetup prims D A x z))
    (q : TreeCheckWalkDef.Pending A)
    (reached : Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x start)
      (batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
        (firstChunks settings (.bottom b)).length) q)
    (out : (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C))) × TreeSimState C)
    (run : out ∈ support (pass prims D A q)) (clean : ¬ TreeSimHashBudgetCollision out.2.2) :
    PassClock D out := by
  set N := batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
    (firstChunks settings (.bottom b)).length
  set S := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
    (firstChunks settings (.bottom b)) (firstChunks settings (.bottom b)).length
  have initialDisc := initial_entry_disc D K A circuits settings top x b positive dealt start
  have log := reached_honest prims D S N Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x start) (setup_honest prims D S A x z start setupRun)
    (fun i _ => initialDisc i) reached le_rfl
  have outLog : HonestCheckLog S out.2.1.1 out.2.2 := by
    apply start_honest prims D S q.program _ q.world log out run
    intro i hi
    simpa only [N, Nat.add_sub_cancel_left] using (initialDisc i).residual (Reached.residual prims D Z reached i hi) (by omega)
  obtain ⟨point, matching, allAbort | ⟨chosen, selected, selection, common⟩⟩ :=
    actual_pass_common prims D K circuits settings top b A x z Z positive dealt start setupRun q reached out run clean
  · refine ⟨S, outLog, ?_⟩
    intro i hi inbox
    rw [allAbort i hi]
    exact .pure _ _
  · have current : (firstChunks settings (.bottom b)).length < treeBatches settings (.bottom b) := by
      have chunks := signing_chunks_nonempty settings b positive chosen.value.2.2
      obtain ⟨head, rest, eq⟩ := chunks
      have len := lockstepChunks_length settings chosen.value.2.2 (.bottom b)
      simp only [lockstepChunks, firstChunks, treeLockstepFirstJobs, List.length_append, eq,
        List.length_cons] at len ⊢
      omega
    let caller := signingCaller point.outputs point.records (fun _ => pure (some chosen.value)) chosen.value
    obtain ⟨lower, clock⟩ := sign_caller_clock circuits settings K D top x start.1.2 b
      (firstChunks settings (.bottom b)).length 1 le_rfl current caller
    rw [signing_start] at lower
    refine ⟨_, outLog.mono lower le_rfl, ?_⟩
    intro i hi inbox
    rcases common i hi with aborted | residual
    · rw [aborted]; exact .pure _ _
    · have same : (x i).parameter = (x (refHolder D K.publicTerm)).parameter := by
        obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
        rw [hx i, hx (refHolder D K.publicTerm)]; rfl
      exact (clock i same (isQueryBoundP_pure _ _ _)).2 _ (residual inbox)

/-- Every clean reached local pass has a common clock; no decoded caller is
used to choose that clock. -/
theorem actual_pass_clock (positive : 0 < settings.batchSize) (dealt : DealtInputs D x)
    (current : (firstChunks settings (.bottom b)).length < treeBatches settings (.bottom b))
    (z : Aux) (start : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (setupRun : start ∈ support (treeSaltSetup prims D A x z))
    (m : ℕ) (q : TreeCheckWalkDef.Pending A)
    (reached : Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x start) m q)
    (out : (C.Party → Step C E RealSpec (TreeCheckWalkDef.Output (C := C))) × TreeSimState C)
    (run : out ∈ support (pass prims D A q)) (clean : ¬ TreeSimHashBudgetCollision out.2.2) :
    PassClock D out := by
  set N := batchStart circuits settings (.bottom b) (x (refHolder D K.publicTerm)).parameter
    (firstChunks settings (.bottom b)).length
  set S := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
    (firstChunks settings (.bottom b)) (firstChunks settings (.bottom b)).length
  set initial := TreeCheckWalkDef.initial K circuits settings top (.bottom b) x start
  have same (i) : (x i).parameter = (x (refHolder D K.publicTerm)).parameter := by
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    rw [hx i, hx (refHolder D K.publicTerm)]; rfl
  by_cases early : m + 1 ≤ N
  · obtain ⟨upper, disc, floor⟩ := initial_program_clock circuits settings K D top (.bottom b) x A start
      (firstChunks_bottom_pos settings positive b) dealt (m + 1) early
    set limit := callerClock circuits settings (x (refHolder D K.publicTerm)).parameter
      (firstChunks settings (.bottom b)) 0 (m + 1)
    have log := reached_honest prims D limit m Z initial (setup_honest prims D limit A x z start setupRun)
      (fun i _ => disc i) reached le_rfl
    refine ⟨limit, start_honest prims D limit q.program ?_ q.world log out run, ?_⟩
    · intro i hi
      simpa using (disc i).residual (Reached.residual prims D Z reached i hi) (by omega)
    · intro i hi inbox
      exact floor i _ ((Reached.residual prims D Z reached i hi).trans (pass_residual prims D A q out run i hi inbox))
  · by_cases atEntry : m = N
    · subst m
      exact entry_pass_clock prims D K A circuits settings top x Z b positive dealt z start setupRun q reached out run clean
    · have after : N + 1 ≤ m := by omega
      have split : Reached prims D Z initial (N + 1 + (m - (N + 1))) q := by
        simpa only [Nat.add_sub_of_le after] using reached
      obtain ⟨base, first, suffix⟩ := reached_split prims D A Z (N + 1) (m - (N + 1)) split
      obtain ⟨entry, fuel, started, reply, before, fuelLeft, firstRun, nonterminal, replyRun, baseEq, pref⟩ :=
        TreeCheckWalkFirstOpening.reached_last D prims A Z initial N base first
      have cleanFirst : ¬ TreeSimHashBudgetCollision started.2.2 := by
        intro bad
        apply clean
        exact treeSimHashBudgetCollision_mono
          ((pref.trans (reached_prefix prims D A Z suffix)).trans
            (treeSimLoggedWorld_prefix prims D _ _ _ run)) bad
      obtain ⟨point, matching, allAbort | ⟨chosen, selected, selection, common⟩⟩ :=
        actual_pass_common prims D K circuits settings top b A x z Z positive dealt start setupRun entry before
          started firstRun cleanFirst
      · exact False.elim (nonterminal (fun i hi => by rw [allAbort i hi]; trivial))
      · let caller := signingCaller point.outputs point.records (fun _ => pure (some chosen.value)) chosen.value
        have baseLog : HonestCheckLog S base.world.1.1 base.world.2 :=
          reached_honest_cut prims D A Z S (N + 1) initial (setup_honest prims D S A x z start setupRun)
            (fun i _ => initial_entry_disc D K A circuits settings top x b positive dealt start i) first le_rfl
        apply signing_suffix_clock prims D K A circuits settings top x start.1.2 Z b caller same
          (fun i => isQueryBoundP_pure _ _ _) current base q (m - (N + 1)) ?_ ?_ suffix out run
        · intro i hi
          rcases common i hi with aborted | residual
          · left
            rw [baseEq]
            simp only [TreeCheckWalkDef.resume, aborted]
            rfl
          · right
            let inbox := fun h => if h ∈ D.1 then reply.1.2 h i else (started.1 h).delivered i
            have h := residual inbox
            convert h using 1
            rw [baseEq]
            simp only [TreeCheckWalkDef.resume]
            cases started.1 i with
            | done output => rfl
            | wait output k => simp [hi, resumed, inbox]
            | call impossible k => exact impossible.elim
        · intro limit lower
          rw [signing_start] at lower
          exact baseLog.mono lower le_rfl

/-- The original signing-cache obligation, for the unchanged fixed family
and decoder, including its first signing checkpoint. -/
theorem walkCheckpointCacheSigning : WalkCheckpointCacheSigning prims K circuits settings := by
  intro positive top tree D A x z Z q dealt bounded small j setup setupRun bottom signing
  obtain ⟨b, rfl⟩ := bottom
  intro s run live c o eq
  rw [eq] at run live ⊢
  dsimp only [TreeCheckTailWalk.cut] at run live ⊢
  let W := family prims K circuits settings top (.bottom b) D A x Z q bounded j setup
  obtain ⟨r, contRun, bad, counted⟩ := live
  obtain ⟨parameter, seeds, pairs, i, value, records, hash, before, batch, after,
    keys, honest, accepted, _⟩ := bad.2.2
  have preRun : o ∈ support ((W.boundary c).pre prims K circuits settings D) := by
    with_reducible apply TreeCheckTailWalk.mem_support_cut_pre (W := W) (Z := Z) (c := c)
    with_reducible simpa only [W, TreeCheckTailWalk.cut] using run
  obtain ⟨out, outRun, grows, pref, transfer, probe⟩ := TreeCheckSigningProbe.source_probe K prims D A circuits settings
    top (.bottom b) x dealt z j Z (TreeCheckQueryBudget.ofBound bounded).step setup c o preRun r contRun bad i honest (value, records) accepted
  have hit : .inl c ∈ support W.pre := by
    with_reducible exact (TreeCheckWalkDef.index_support prims D Z K circuits settings W c o
      (by simpa only [W, TreeCheckTailWalk.cut] using run))
  with_reducible obtain ⟨m, pending, reached, actualRun⟩ := (walk_hit_pass prims D K A circuits settings top (.bottom b) x setup.1.2 j Z
    (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x setup)
    (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x setup).fuel 0
    (TreeCheckWalkDef.initial K circuits settings top (.bottom b) x setup) .start rfl c hit out outRun)
  have clean : ¬ TreeSimHashBudgetCollision out.2.2 := by
    intro collision
    apply bad.1
    exact treeSimHashBudgetCollision_mono
      (pref.trans (treeCheckBatchCont_log_prefix prims K circuits D A Z (W.boundary c).batch o r contRun)) collision
  obtain ⟨limit, outLog, floor⟩ := actual_pass_clock prims D K A circuits settings top x Z b positive dealt
    (by omega) z setup setupRun m pending reached out actualRun clean
  have covered : CoveredOn TreeCheckSeenCovered.TreeCheckSeenQuery o.2.1.1 o.2.2 := by
    have result := TreeCheckSeenCovered.walkCheckpoint_seen_covered prims K circuits settings
    unfold TreeCheckWalkRecipe.AtWalk at result
    with_reducible exact (result
      positive top (.bottom b) D A x z Z q dealt bounded small j setup setupRun c o
        (by simpa only [TreeCheckTailWalk.cut] using run))
  change SoundCache _ o.2.1.1 (treeCheckCountedSeen o.2.2) (priorKeys _ o.2.1.1)
  exact soundCache_of_covered_honest covered (transfer limit outLog) (probe limit (floor i honest))

end ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning.prepare_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning.prepare_pass

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning.prepare_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning.prepare_next

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning.walk_hit_pass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning.walk_hit_pass

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning.initial_entry_disc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning.initial_entry_disc

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning.actual_pass_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning.actual_pass_clock

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning.walkCheckpointCacheSigning' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCacheSigning.walkCheckpointCacheSigning
