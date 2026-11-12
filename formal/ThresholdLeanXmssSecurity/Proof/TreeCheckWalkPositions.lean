import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkOpenings
import ThresholdLeanXmssSecurity.Proof.TreeCheckAllHonestLinks

/-!
# Budget positions of the check walk

The query budget quantifies over every honest program. A scheduler prelude can
therefore be represented by a program retaining its actual adversary rounds
and its complete logged world. Local work between rounds may be placed at the
first honest operator; every such query still uses the same free oracle copy.
The representation preserves both caches and the classified query log.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckWalkPositions

attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
variable {C : Committee} {E : Type}

/-- A local prelude can move past earlier pure entries of an ordered pass. -/
theorem sequenceFin_prepend {m : Type → Type} [Monad m] [LawfulMonad m]
    {α : Type} (prelude : m Unit) : ∀ {n : ℕ} (entry : Fin n → m α) (slot : Fin n)
    (_earlier : ∀ i, i < slot → ∃ a, entry i = pure a),
    Concrete.sequenceFin (fun i => if i = slot then prelude >>= fun _ => entry i else entry i) =
      (prelude >>= fun _ => Concrete.sequenceFin entry)
  | 0, _, slot, _ => slot.elim0
  | n + 1, entry, slot, earlier => by
    cases slot using Fin.cases with
    | zero =>
      simp only [Concrete.sequenceFin, if_true, bind_assoc]
      apply bind_congr
      intro _
      apply bind_congr
      intro _
      have rest : (fun i : Fin n => if i.succ = 0 then prelude >>= fun _ => entry i.succ else entry i.succ) =
          fun i => entry i.succ := by funext i; rw [if_neg (Fin.succ_ne_zero i)]
      rw [rest]
    | succ slot =>
      obtain ⟨a, initial⟩ := earlier 0 (Fin.succ_pos slot)
      simp only [Concrete.sequenceFin, if_neg (Ne.symm (Fin.succ_ne_zero slot)), initial, pure_bind]
      have rest : (fun i : Fin n => if i.succ = slot.succ then prelude >>= fun _ => entry i.succ else entry i.succ) =
          fun i => if i = slot then prelude >>= fun _ => entry i.succ else entry i.succ := by
        funext i
        simp only [Fin.succ_inj]
      rw [rest, sequenceFin_prepend prelude (fun i : Fin n => entry i.succ) slot
        (fun i hi => earlier i.succ (Fin.succ_lt_succ_iff.mpr hi))]
      simp only [bind_assoc]

/-- There is a first honest operator in scheduler order. -/
theorem first_honest (D : C.Coalition) :
    ∃ h : C.Party, h ∉ D.1 ∧ ∀ i, i < h → i ∈ D.1 := by
  let honest := Finset.univ.filter fun i : C.Party => i ∉ D.1
  have nonempty : honest.Nonempty := by
    obtain ⟨i, hi⟩ := exists_honest D
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  refine ⟨honest.min' nonempty, (Finset.mem_filter.mp (Finset.min'_mem honest nonempty)).2, ?_⟩
  intro i before
  by_contra hi
  have lower := Finset.min'_le honest i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  exact (not_le_of_gt before) lower

/-- Place a free local prelude at the first honest operator of a phase. -/
def prepend {α : Type} (first : C.Party) (prelude : OracleComp (LocalSpec C) Unit)
    (program : C.Party → PartyM C E RealSpec α) (i : C.Party) : PartyM C E RealSpec α :=
  if i = first then localStep prelude >>= fun _ => program i else program i

/-- The ordered local pass executes the prepended work before every other local query. -/
theorem start_prepend {α : Type} (D : C.Coalition) (first : C.Party)
    (honest : first ∉ D.1) (earlier : ∀ i, i < first → i ∈ D.1)
    (prelude : OracleComp (LocalSpec C) Unit) (program : C.Party → PartyM C E RealSpec α) :
    startSteps worldRoles D (prepend first prelude program) =
      (free prelude >>= fun _ => startSteps worldRoles D program) := by
  unfold startSteps
  simp only [worldRoles_honest]
  rw [← sequenceFin_prepend (free prelude)
    (fun i => if i ∈ D.1 then pure (.done none) else free (advance (program i).run)) first
    (fun i hi => ⟨.done none, if_pos (earlier i hi)⟩)]
  congr 1
  funext i
  by_cases selected : i = first
  · subst i
    simp only [prepend, if_true, if_neg honest, advance_localStep_bind, free_bind]
  · simp only [prepend, if_neg selected]

/-- Adding local work at a phase boundary does not consume a scheduler round. -/
theorem phase_prepend {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (rounds : ℕ) (state : A.State)
    (first : C.Party) (honest : first ∉ D.1) (earlier : ∀ i, i < first → i ∈ D.1)
    (prelude : OracleComp (LocalSpec C) Unit) (program : C.Party → PartyM C E RealSpec α) :
    executePhase worldRoles D A noFunctionality rounds state (prepend first prelude program) =
      (free prelude >>= fun _ => executePhase worldRoles D A noFunctionality rounds state program) := by
  simp only [executePhase, start_prepend D first honest earlier, bind_assoc]

/-- An arbitrary budget-test program may retain an exchange without interpreting its inbox. -/
def pause {α : Type} (box : Mail C E) (program : PartyM C E RealSpec α) : PartyM C E RealSpec α :=
  OptionT.mk (OracleComp.queryBind (.inl (.inr box)) fun _ => program.run)

theorem advance_pause {α : Type} (box : Mail C E) (program : PartyM C E RealSpec α) :
    advance (pause box program).run = pure (.wait box (fun _ => program.run)) := rfl

/-- A retained exchange has the original adversary view and exactly one round of cost. -/
theorem phase_pause {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (rounds : ℕ) (state : A.State)
    (boxes : C.Party → Mail C E) (program : C.Party → PartyM C E RealSpec α) :
    executePhase worldRoles D A noFunctionality (rounds + 1) state
      (fun i => pause (boxes i) (program i)) = (do
        let reply ← worldRoles.adversary (A.round state fun c i =>
          if c ∈ D.1 ∧ i ∉ D.1 then boxes i c else none)
        executePhase worldRoles D A noFunctionality rounds reply.1 program) := by
  let steps : C.Party → Step C E RealSpec α :=
    fun i => if i ∈ D.1 then .done none else .wait (boxes i) (fun _ => (program i).run)
  have start : startSteps worldRoles D (fun i => pause (boxes i) (program i)) = pure steps := by
    unfold startSteps
    simp only [advance_pause, worldRoles_honest, free_pure]
    have pureStep i : (if i ∈ D.1 then pure (.done none) else
        pure (.wait (boxes i) (fun _ => (program i).run))) =
        (pure (steps i) : OracleComp (WorldSpec C) _) := by
      dsimp only [steps]
      split_ifs <;> rfl
    simp_rw [pureStep]
    exact sequenceFin_pure steps
  have pending : ¬ ∀ i, i ∉ D.1 → (steps i).isDone := by
    obtain ⟨i, honest⟩ := exists_honest D
    intro all
    simpa only [steps, if_neg honest, Step.isDone] using all i honest
  have view : (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none) =
      fun c i => if c ∈ D.1 ∧ i ∉ D.1 then boxes i c else none := by
    funext c i
    split_ifs with visible
    · simp only [steps, if_neg visible.2, Step.outbox]
    · rfl
  have locals (sent : C.Party → Mail C E) :
      free (Concrete.sequenceFin (roundLocal D steps sent)) = startSteps worldRoles D program := by
    rw [free_sequenceFin]
    unfold startSteps
    congr 1
    funext i
    by_cases corrupt : i ∈ D.1
    · simp [steps, corrupt, roundLocal, free_pure]
    · simp [steps, corrupt, roundLocal, worldRoles_honest]
  rw [executePhase, start, pure_bind, executeRounds, if_neg pending, stepRound_real, view]
  simp only [bind_assoc, pure_bind, locals, executePhase]

/-- A retained source history records the actual start, local work and adversary replies. -/
inductive Prefix (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux) :
    ℕ → A.State → TreeSimState C → Prop
  | initial (r : A.State × TreeSimState C)
      (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.adversary (A.start (corruptInputs D x) z))).run ((∅, ∅), []))) :
      Prefix prims D A x z 0 r.1 r.2
  | locals {n : ℕ} {state : A.State} {world : TreeSimState C} {α : Type}
      (prior : Prefix prims D A x z n state world) (p : OracleComp (LocalSpec C) α)
      (r : α × TreeSimState C)
      (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run world)) :
      Prefix prims D A x z n state r.2
  | round {n : ℕ} {state : A.State} {world : TreeSimState C}
      (prior : Prefix prims D A x z n state world) (boxes : C.Party → Mail C E)
      (r : (A.State × (C.Party → Mail C E)) × TreeSimState C)
      (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.adversary (A.round state fun c i =>
          if c ∈ D.1 ∧ i ∉ D.1 then boxes i c else none))).run world)) :
      Prefix prims D A x z (n + 1) r.1.1 r.2

/-- Every retained history can be followed by any honest phase in one real execution.
The witness program preserves the actual adversary state, both caches and the complete log. -/
theorem Prefix.realize {prims : Primitives} {D : C.Coalition}
    {A : Adversary C E (Keys C) PEmpty PEmpty} {x : C.Party → Keys C} {z : Aux}
    {n : ℕ} {state : A.State} {world : TreeSimState C}
    (history : Prefix prims D A x z n state world) {α : Type}
    (rounds : ℕ) (program : C.Party → PartyM C E RealSpec α)
    (out : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality rounds state program)).run world)) :
    ∃ full : C.Party → Keys C → PartyM C E RealSpec α,
      out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (realExecution D A noFunctionality (n + rounds) full x z)).run ((∅, ∅), [])) := by
  induction history generalizing rounds program out with
  | initial r initial =>
    refine ⟨fun i _ => program i, ?_⟩
    simp only [Nat.zero_add, realExecution, simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    exact ⟨r, initial, run⟩
  | @locals n state world β prior p r localRun ih =>
    obtain ⟨first, honest, earlier⟩ := first_honest D
    apply ih rounds (prepend first (p >>= fun _ => pure ()) program) out
    rw [phase_prepend D A rounds state first honest earlier]
    simp only [free_bind, free_pure, simulateQ_bind, StateT.run_bind,
      bind_assoc, pure_bind, mem_support_bind_iff]
    exact ⟨r, localRun, run⟩
  | @round n state world prior boxes r roundRun ih =>
    have next : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (rounds + 1) state
          (fun i => pause (boxes i) (program i)))).run world) := by
      rw [phase_pause]
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
      exact ⟨r, roundRun, run⟩
    obtain ⟨full, supported⟩ := ih (rounds + 1) (fun i => pause (boxes i) (program i)) out next
    refine ⟨full, ?_⟩
    simpa only [Nat.add_assoc, Nat.add_comm 1 rounds] using supported

/-- The initial local pass is one free local computation. -/
theorem start_free {α : Type} (D : C.Coalition)
    (program : C.Party → PartyM C E RealSpec α) :
    startSteps worldRoles D program = free (Concrete.sequenceFin fun i =>
      if i ∈ D.1 then pure (.done none) else advance (program i).run) := by
  rw [free_sequenceFin]
  unfold startSteps
  congr 1
  funext i
  split_ifs <;> rfl

/-- Actual scheduler executions extend the retained history by at most their fuel. -/
theorem Prefix.executeRounds {prims : Primitives} {D : C.Coalition}
    {A : Adversary C E (Keys C) PEmpty PEmpty} {x : C.Party → Keys C} {z : Aux}
    {n : ℕ} {state : A.State} {world : TreeSimState C}
    (history : Prefix prims D A x z n state world) {α : Type}
    (fuel : ℕ) (steps : C.Party → Step C E RealSpec α)
    (out : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (ThresholdLeanXmss.executeRounds worldRoles D A noFunctionality fuel state steps)).run world)) :
    ∃ spent, spent ≤ fuel ∧ Prefix prims D A x z (n + spent) out.1.1 out.2 := by
  induction fuel generalizing n state world steps with
  | zero =>
      simp only [ThresholdLeanXmss.executeRounds, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff] at run
      subst out
      exact ⟨0, Nat.le_refl _, by simpa using history⟩
  | succ fuel ih =>
      rw [ThresholdLeanXmss.executeRounds] at run
      split_ifs at run with stopped
      · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
        subst out
        exact ⟨0, Nat.zero_le _, by simpa using history⟩
      · rw [stepRound_real] at run
        simp only [bind_assoc, pure_bind, simulateQ_bind, StateT.run_bind,
          mem_support_bind_iff] at run
        obtain ⟨reply, replyRun, localsOut, localRun, rest⟩ := run
        have hr := history.round (fun i => (steps i).outbox) reply replyRun
        have hl := hr.locals (Concrete.sequenceFin (roundLocal D steps reply.1.2)) localsOut localRun
        obtain ⟨spent, bound, done⟩ := ih hl localsOut.1 rest
        exact ⟨spent + 1, by omega, by simpa only [Nat.add_assoc, Nat.add_comm 1 spent] using done⟩

/-- Any supported phase extends the exact history within its supplied round allowance. -/
theorem Prefix.phase {prims : Primitives} {D : C.Coalition}
    {A : Adversary C E (Keys C) PEmpty PEmpty} {x : C.Party → Keys C} {z : Aux}
    {n : ℕ} {state : A.State} {world : TreeSimState C}
    (history : Prefix prims D A x z n state world) {α : Type}
    (fuel : ℕ) (program : C.Party → PartyM C E RealSpec α)
    (out : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state program)).run world)) :
    ∃ spent, spent ≤ fuel ∧ Prefix prims D A x z (n + spent) out.1.1 out.2 := by
  simp only [executePhase, start_free, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨started, localRun, rest⟩ := run
  exact (history.locals _ started localRun).executeRounds fuel started.1 out rest

/-- The supported PRSS setup retains its actual prefix within setup fuel. -/
theorem setup_prefix (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : p ∈ support (treeSaltSetup prims D A x z)) :
    ∃ n, n ≤ setupRounds ∧ Prefix prims D A x z n p.1.1 p.2 := by
  simp only [treeSaltSetup, mem_support_bind_iff] at run
  obtain ⟨started, initialRun, phaseRun⟩ := run
  have history := Prefix.initial started initialRun
  obtain ⟨n, bound, result⟩ := history.phase setupRounds (fun i => prssSetup i) p
    (by simpa only [simulateQ_executePhase, treeSimRealRoles] using phaseRun)
  exact ⟨n, bound, by simpa only [Nat.zero_add] using result⟩

open TreeCheckWalkDef TreeCheckWalkRecipe

/-- Selection executes only free local work, in the original party order. -/
theorem select_free {α : Type} : ∀ {n : ℕ} (gate : Fin n → OracleComp (LocalSpec C) (Option α)),
    select (fun i => free (gate i)) = free (select gate)
  | 0, _ => by simp only [select, free_pure]
  | n + 1, gate => by
      simp only [select, free_bind]
      apply bind_congr
      intro value
      cases value with
      | some a => simp only [free_pure]
      | none =>
          rw [select_free]
          simp only [map_eq_bind_pure_comp, free_bind, Function.comp_apply, free_pure]
          rfl

/-- A selected local head extends the exact history without a scheduler round. -/
theorem selectPending_prefix {prims : Primitives} {D : C.Coalition}
    {A : Adversary C E (Keys C) PEmpty PEmpty} {x : C.Party → Keys C} {z : Aux}
    {n : ℕ} (p : Pending A) (history : Prefix prims D A x z n p.state p.world)
    {α : Type} (gate : C.Party → OracleComp (LocalSpec C) (Option α))
    (cont : C.Party → α → PartyM C E RealSpec (Output (C := C)))
    (selected : Pending A) (run : selected ∈ support (selectPending prims D A gate cont p)) :
    Prefix prims D A x z n selected.state selected.world := by
  simp only [selectPending, mem_support_bind_iff, mem_support_pure_iff, select_free] at run
  obtain ⟨out, localRun, rfl⟩ := run
  exact history.locals _ out localRun

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

omit [Fintype E] [DecidableEq E] in
/-- Preparation retains the full world and consumes no scheduler fuel. -/
theorem prepare_prefix {prims : Primitives} {D : C.Coalition}
    {A : Adversary C E (Keys C) PEmpty PEmpty} {x : C.Party → Keys C} {z : Aux}
    (K : Constants C E) (circuits : Circuits) (settings : Settings) (top : TopTree)
    (tree : Tree) (setup : C.Party → Option (PrssKeys C)) (j : ℕ)
    {n : ℕ} (p : Pending A) (history : Prefix prims D A x z n p.state p.world)
    (prepared : Pending A)
    (run : prepared ∈ support (prepare prims K D A circuits settings top tree x setup j p)) :
    Prefix prims D A x z n prepared.state prepared.world := by
  unfold prepare at run
  cases tree with
  | top => simpa only [mem_support_pure_iff] using run ▸ history
  | bottom b =>
      dsimp only at run
      split_ifs at run with first found
      · exact selectPending_prefix p history _ _ prepared run
      · simp only [mem_support_pure_iff] at run; subst prepared; exact history
      · simp only [mem_support_pure_iff] at run; subst prepared; exact history

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A nonterminal scheduler step appends exactly one actual adversary round. -/
theorem next_prefix {prims : Primitives} {D : C.Coalition}
    {A : Adversary C E (Keys C) PEmpty PEmpty} {x : C.Party → Keys C} {z : Aux}
    (Z : Distinguisher C A.State TreeOutput) {n : ℕ} (p : Pending A)
    (history : Prefix prims D A x z n p.state p.world) (fuel : ℕ) (pending : Pending A)
    (run : .inl pending ∈ support (next prims D Z fuel p)) :
    Prefix prims D A x z (n + 1) pending.state pending.world := by
  unfold next at run
  rw [mem_support_bind_iff] at run
  obtain ⟨started, startRun, run⟩ := run
  rw [start_free] at startRun
  have startedPrefix := history.locals _ started startRun
  split_ifs at run
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at run
    obtain ⟨out, _, impossible⟩ := run
    cases impossible
  · simp only [mem_support_bind_iff, mem_support_pure_iff, Sum.inl.injEq] at run
    obtain ⟨reply, replyRun, he⟩ := run
    cases he
    exact startedPrefix.round (fun i => (started.1 i).outbox) reply replyRun

omit [Fintype E] [DecidableEq E] in
/-- The source walk spends only its actual adversary rounds. -/
theorem walk_prefix {prims : Primitives} {D : C.Coalition}
    {A : Adversary C E (Keys C) PEmpty PEmpty} {x : C.Party → Keys C} {z : Aux}
    (K : Constants C E) (circuits : Circuits) (settings : Settings) (top : TopTree)
    (tree : Tree) (setup : C.Party → Option (PrssKeys C)) (j : ℕ)
    (Z : Distinguisher C A.State TreeOutput) (fuel : ℕ) {n total : ℕ} (p : Pending A)
    (history : Prefix prims D A x z n p.state p.world) (room : n + fuel ≤ total)
    (c : Decoded (decode prims K D A circuits settings top tree x setup j))
    (run : .inl c ∈ support (walk prims K D A circuits settings top tree x setup j Z fuel p)) :
    ∃ m, Prefix prims D A x z m c.1.1.state c.1.1.world ∧ m + c.1.1.fuel ≤ total := by
  induction fuel generalizing n p with
  | zero =>
      simp only [TreeCheckWalkRecipe.walk, mem_support_bind_iff] at run
      obtain ⟨current, hc, run⟩ := run
      have hprefix := prepare_prefix K circuits settings top tree setup j {p with fuel := 0} history current hc
      have hFuel := (prepare_fuel_prefix prims K D A circuits settings top tree x setup j _ _ hc).1
      split_ifs at run
      · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
        cases run
        exact ⟨n, hprefix, by simpa only [hFuel] using room⟩
      · simp only [support_map, Set.mem_image] at run
        obtain ⟨result, _, impossible⟩ := run
        cases impossible
  | succ fuel ih =>
      simp only [TreeCheckWalkRecipe.walk, mem_support_bind_iff] at run
      obtain ⟨current, hc, run⟩ := run
      have hprefix := prepare_prefix K circuits settings top tree setup j {p with fuel := fuel + 1}
        history current hc
      have hFuel := (prepare_fuel_prefix prims K D A circuits settings top tree x setup j _ _ hc).1
      split_ifs at run
      · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
        cases run
        exact ⟨n, hprefix, by simpa only [hFuel] using room⟩
      · rw [mem_support_bind_iff] at run
        obtain ⟨outcome, ho, run⟩ := run
        cases outcome with
        | inr result => simp only [mem_support_pure_iff] at run; cases run
        | inl pending =>
            exact ih pending (next_prefix Z current hprefix fuel pending ho) (by omega) run

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem world_phase_congr {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (p q : C.Party → PartyM C E RealSpec α) (same : ∀ i, i ∉ D.1 → p i = q i) :
    executePhase worldRoles D A noFunctionality fuel state p =
      executePhase worldRoles D A noFunctionality fuel state q := by
  unfold executePhase startSteps
  congr 2
  funext i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi]
  · simp only [if_neg hi, same i hi]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem resume_start {α β : Type} (D : C.Coalition)
    (k : C.Party → α → PartyM C E RealSpec β) (pref : C.Party → Option α) (data : C.Party → α)
    (corrupt : ∀ i, i ∈ D.1 → pref i = none)
    (present : ∀ i, i ∉ D.1 → pref i = some (data i)) :
    free (Concrete.sequenceFin fun i => continueStep (k i) (.done (pref i))) =
      startSteps worldRoles D (fun i => k i (data i)) := by
  unfold startSteps
  rw [free_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, corrupt i hi, continueStep, free_pure]
  · simp only [if_neg hi, present i hi, continueStep, worldRoles]

set_option maxRecDepth 2000 in
set_option maxHeartbeats 500000 in
/-- A successful nonempty check continuation has its full mandatory round allowance.
Honest tuple rows and their actual supported execution are retained. -/
theorem batchCont_fuel (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckTailBoundary A)
    (self : ∀ i, (b.batch.ctx i).self = i)
    (parameters : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (o : TreeCheckTailCheckpoint A) (preRun : o ∈ support (b.pre prims K circuits settings D))
    (r : TreeCheckTailResult A) (run : r ∈ support (treeCheckBatchCont prims K circuits D A Z b.batch o))
    (accepted : ∃ i value, r.1.2.2 i = some value)
    (nonzero : tupleCount (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) ≠ 0) :
    2 * halvings (tupleCount (b.batch.jobs.map (circuits b.batch.parameter ·.kind))) + 5 ≤ b.batch.fuel := by
  let data := fun i => treeCheckPrefixData (o.1.2 i)
  have live := treeCheckBatch_live prims K circuits D A Z b.batch o r run accepted
  have present i (hi : i ∉ D.1) : o.1.2 i = some (data i) := by
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (live i hi)
    simp only [data, treeCheckPrefixData, hp, Option.getD_some]
  have corrupt := treeStages_phase_corrupt (treeSimLoggedWorld prims D) D A
    (b.batch.rounds circuits settings) b.batch.state _ b.batch.world o
    (by simpa only [TreeCheckTailBoundary.pre, simulateQ_executePhase] using preRun)
  have counts i (hi : i ∉ D.1) : ((data i).2.1.2.map (·.count)).sum = (b.batch.counts circuits).sum := by
    obtain ⟨p, hp, _, _, _, hc, _⟩ := b.counts prims K circuits settings D Z self parameters o preRun r run accepted i hi
    have same : p = data i := Option.some.inj (hp.symm.trans (present i hi))
    rw [← same, hc]
  let tuples := fun i => if i ∈ D.1 then (data (refHolder D K.publicTerm)).2.1.2 else (data i).2.1.2
  have countsAll i : ((tuples i).map (·.count)).sum = (b.batch.counts circuits).sum := by
    dsimp only [tuples]
    split_ifs with hi
    · exact counts _ (refHolder_spec D K.publicTerm).2
    · exact counts i hi
  have normalized := world_phase_congr D A b.batch.fuel o.1.1
    (fun i => treeSimCheckBatchFinish K circuits (b.batch.ctx i) b.batch.jobs b.batch.initial (data i) >>= b.batch.k i)
    (fun i => (check K (b.batch.ctx i) (realCheckGadgets K (b.batch.ctx i)) (tuples i)).run (data i).2.2 >>=
      fun checked => openRep K (b.batch.ctx i) (data i).2.1.1
        (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length >>=
          batchOpeningCont circuits b.batch data i checked) (by
      intro i hi
      rw [treeLockstep_batchFinish_check]
      simp only [tuples, if_neg hi]
      congr 1
      funext checked
      unfold treeLockstepBatchCheckCont batchOpeningCont openingRecord
      rw [parameters i])
  unfold treeCheckBatchCont at run
  rw [resume_start D _ o.1.2 data corrupt present] at run
  have combined : (do
      let next ← (simulateQ (treeSimLoggedWorld prims D)
        (startSteps worldRoles D (fun i => treeSimCheckBatchFinish K circuits (b.batch.ctx i)
          b.batch.jobs b.batch.initial (data i) >>= b.batch.k i))).run o.2
      let out ← (simulateQ (treeSimLoggedWorld prims D)
        (executeRounds worldRoles D A noFunctionality b.batch.fuel o.1.1 next.1)).run next.2
      treeCheckObserve prims D A Z out) = (do
      let out ← (simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality b.batch.fuel o.1.1
          (fun i => treeSimCheckBatchFinish K circuits (b.batch.ctx i) b.batch.jobs b.batch.initial
            (data i) >>= b.batch.k i))).run o.2
      treeCheckObserve prims D A Z out) := by
    simp only [executePhase, simulateQ_bind, StateT.run_bind, bind_assoc]
  rw [combined, normalized] at run
  simp only [mem_support_bind_iff] at run
  obtain ⟨out, phaseRun, observation⟩ := run
  unfold treeCheckObserve at observation
  simp only [mem_support_bind_iff, mem_support_pure_iff] at observation
  obtain ⟨observed, observedRun, rfl⟩ := observation
  let count := (b.batch.counts circuits).sum
  let p := fun i => (check (G := RealSpec) K (b.batch.ctx i)
    (realCheckGadgets K (b.batch.ctx i)) (tuples i)).run (data i).2.2
  have timed i : TreeSimCheckTimed (2 * halvings count + 5) (p i).run := by
    have nz : ((tuples i).map (·.count)).sum ≠ 0 := by
      rw [countsAll i, TreeCheckBatchWalk.counts_sum]
      exact nonzero
    have h := treeLockstep_check_timed K (b.batch.ctx i) (tuples i) (data i).2.2 nz
    have hs : sliceBits ≤ halvings count := by unfold halvings; omega
    convert h using 1
    rw [countsAll i]
    dsimp only [count] at *
    omega
  have enough : 2 * halvings count + 5 ≤ b.batch.fuel := by
    with_reducible exact (timed_phase_fuel D A b.batch.fuel (2 * halvings count + 5) o.1.1 p
      (fun i checked => openRep K (b.batch.ctx i) (data i).2.1.1
        (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length >>=
          batchOpeningCont circuits b.batch data i checked) timed out.1
      (treeCheck_logged_support prims D _ _ phaseRun) accepted)
  simpa only [count, TreeCheckBatchWalk.counts_sum] using enough

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A retained history with check room gives the original concrete prefix position. -/
theorem Prefix.position {prims : Primitives} {D : C.Coalition}
    {A : Adversary C E (Keys C) PEmpty PEmpty} {x : C.Party → Keys C} {z : Aux}
    {circuits : Circuits} {settings : Settings} {Z : Distinguisher C A.State TreeOutput}
    {q count n : ℕ} (budget : TreeCheckQueryBudget A Z (ceremonyFuel circuits settings) q)
    (o : TreeCheckTailCheckpoint A) (history : Prefix prims D A x z n o.1.1 o.2)
    (room : n + (2 * halvings count + 5) ≤ ceremonyFuel circuits settings) :
    Nonempty (TreeCheckPrefixPosition prims circuits settings D A x z Z budget count o) := by
  let program : C.Party → PartyM C E RealSpec Unit := fun _ => pure ()
  let steps : C.Party → Step C E RealSpec Unit := fun i =>
    if i ∈ D.1 then .done none else .done (some ())
  have start : startSteps worldRoles D program = pure steps := by
    unfold startSteps
    have each i : (if i ∈ D.1 then pure (.done none) else
        worldRoles.honest (advance (program i).run)) =
        (pure (steps i) : OracleComp (WorldSpec C) _) := by
      dsimp only [program, steps]
      split_ifs <;> rfl
    simp_rw [each]
    exact sequenceFin_pure steps
  let out : (A.State × (C.Party → Option Unit)) × TreeSimState C :=
    ((o.1.1, fun i => (steps i).output), o.2)
  have run : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality 0 o.1.1 program)).run o.2) := by
    simp only [executePhase, start, pure_bind, ThresholdLeanXmss.executeRounds,
      simulateQ_pure, StateT.run_pure, mem_support_pure_iff]
    rfl
  obtain ⟨full, fullRun⟩ := history.realize 0 program out run
  exact ⟨⟨n, Unit, full, out, by simpa only [Nat.add_zero] using fullRun, rfl, rfl, room⟩⟩

/-- A supported left cut retains the same selected source witness. -/
theorem cut_walk_support (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (W : TreeCheckTailWalk A)
    (c : W.β) (o : TreeCheckTailCheckpoint A)
    (preRun : (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre) : .inl c ∈ support W.pre := by
  unfold TreeCheckTailWalk.cut at preRun
  rw [mem_support_bind_iff] at preRun
  obtain ⟨outcome, hs, ho⟩ := preRun
  cases outcome with
  | inl c' =>
      rw [support_map] at ho
      obtain ⟨o', _, he⟩ := ho
      cases he
      exact hs
  | inr r => simp only [mem_support_pure_iff] at ho; cases ho

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
/-- Source preparation and the batch prelude retain an exact bounded history. -/
theorem source_checkpoint_prefix (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (x : C.Party → Keys C) (z : Aux) (j : ℕ) (Z : Distinguisher C A.State TreeOutput)
    (step : ℕ) (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (setupRun : setup ∈ support (treeSaltSetup prims D A x z))
    (c : Decoded (decode prims K D A circuits settings top tree x setup.1.2 j))
    (o : TreeCheckTailCheckpoint A)
    (preRun : (.inl (c, o) : ((sourceWalk prims K D A circuits settings top tree x j Z step setup).cut
      prims K circuits settings D Z).σ) ∈ support
      ((sourceWalk prims K D A circuits settings top tree x j Z step setup).cut
        prims K circuits settings D Z).pre) :
    let b := (sourceWalk prims K D A circuits settings top tree x j Z step setup).boundary c
    ∃ n, Prefix prims D A x z n o.1.1 o.2 ∧ n + b.batch.fuel ≤ ceremonyFuel circuits settings := by
  let b := (sourceWalk prims K D A circuits settings top tree x j Z step setup).boundary c
  have batchRun : o ∈ support (b.pre prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre
      (prims := prims) (K := K) (circuits := circuits) (settings := settings) (D := D) (A := A) (Z := Z)
      (W := sourceWalk prims K D A circuits settings top tree x j Z step setup) (c := c) (o := o) preRun)
  have walkRun : .inl c ∈ support (sourceWalk prims K D A circuits settings top tree x j Z step setup).pre := by
    with_reducible exact (cut_walk_support prims K circuits settings D A Z
      (sourceWalk prims K D A circuits settings top tree x j Z step setup) c o preRun)
  obtain ⟨n, setupBound, initialPrefix⟩ := setup_prefix prims D A x z setup setupRun
  have room : n + (initial K circuits settings top tree x setup).fuel ≤ ceremonyFuel circuits settings := by
    dsimp only [initial, ceremonyFuel]
    omega
  obtain ⟨m, walked, remaining⟩ : ∃ m, Prefix prims D A x z m c.1.1.state c.1.1.world ∧
      m + c.1.1.fuel ≤ ceremonyFuel circuits settings := by
    with_reducible exact (walk_prefix K circuits settings top tree setup.1.2 j Z
      (initial K circuits settings top tree x setup).fuel (initial K circuits settings top tree x setup)
      initialPrefix room c walkRun)
  have fits := (decode_sound prims K D A circuits settings top tree x setup.1.2 j c).2.1
  obtain ⟨spent, bound, endpoint⟩ := walked.phase (b.batch.rounds circuits settings) _ o batchRun
  refine ⟨m + spent, endpoint, ?_⟩
  have fuel : b.batch.fuel = c.1.1.fuel - b.batch.rounds circuits settings := rfl
  rw [fuel]
  change b.batch.rounds circuits settings ≤ c.1.1.fuel at fits
  omega

set_option maxRecDepth 2000 in
/-- The live bad record forces a nonempty check at this same recognized boundary. -/
theorem source_count_ne_zero (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (x : C.Party → Keys C) (z : Aux) (j : Fin (treeBatches settings tree))
    (Z : Distinguisher C A.State TreeOutput) (step : ℕ)
    (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (c : Decoded (decode prims K D A circuits settings top tree x setup.1.2 j.val))
    (o : TreeCheckTailCheckpoint A) (r : TreeCheckTailResult A)
    (run : r ∈ support (((sourceWalk prims K D A circuits settings top tree x j.val Z step setup).cut
      prims K circuits settings D Z).cont (.inl (c, o))))
    (bad : TreeCheckBranchBad prims K circuits settings top tree D A x z j r) :
    let b := (sourceWalk prims K D A circuits settings top tree x j.val Z step setup).boundary c
    tupleCount (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) ≠ 0 := by
  obtain ⟨_, parameter, seeds, pairs, i, value, records, hash, before, batch, after,
    dealt, hi, result, _, _, listed, index, _, wrong, reference⟩ := bad.2
  obtain ⟨prss, valid⟩ := reference.records prims K circuits settings top tree D A parameter seeds
    pairs z r.2 hash i hi value records
  obtain ⟨context, valid⟩ := valid batch (by simp [listed])
  have parameterEq : batch.ctx.keys.parameter = parameter := by rw [context]; rfl
  have nonzero := valid.incorrect_count prims K circuits settings hash seeds
    (by simpa only [parameterEq] using wrong)
  obtain ⟨fuel, pref, audited, dealer, out, room, hpref, _, replay, accepted, _, _, hashes⟩ := reference
  let record : TreeCheckIndexedRecord prims circuits D A x j.val r :=
    ⟨parameter, seeds, pairs, i, value, records, hash, batch, pref, dealt, hi, result,
      by simp [listed, index], hpref, hashes, wrong⟩
  have metadata := sourceWalk_indexed_metadata prims K D A circuits settings top tree x j.val Z step
    setup c o r run record
  dsimp only
  rw [metadata.2.1, metadata.2.2]
  simpa only [record, parameterEq] using nonzero

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
/-- The exact numerical prefix-position clause for the frozen source family. -/
theorem prefixPositions (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) :
    TreeCheckAllHonestLinks.PrefixPositions prims K circuits settings := by
  intro hb top tree D A x z Z q dealt bounded small j setup setupRun c o preRun live
  obtain ⟨r, run, bad, counted⟩ := live
  let step := (TreeCheckQueryBudget.ofBound bounded).step
  let W := sourceWalk prims K D A circuits settings top tree x j.val Z step setup
  let b := W.boundary c
  obtain ⟨n, history, remaining⟩ : ∃ n, Prefix prims D A x z n o.1.1 o.2 ∧
      n + b.batch.fuel ≤ ceremonyFuel circuits settings := by
    with_reducible exact (source_checkpoint_prefix prims K D A circuits settings top tree x z
      j.val Z step setup setupRun c o preRun)
  have nonzero := source_count_ne_zero prims K D A circuits settings top tree x z j Z step setup c o r run bad
  have batchRun : o ∈ support (b.pre prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre
      (prims := prims) (K := K) (circuits := circuits) (settings := settings) (D := D) (A := A) (Z := Z)
      (W := W) (c := c) (o := o) preRun)
  have self i : (b.batch.ctx i).self = i := rfl
  have parameters i : (b.batch.ctx i).keys.parameter = b.batch.parameter := by
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    change (x i).parameter = (x (refHolder D K.publicTerm)).parameter
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl
  obtain ⟨_, parameter, seeds, pairs, i, value, records, hash, before, batch, after,
    hx, hi, result, rest⟩ := bad.2
  have enough := batchCont_fuel prims K circuits settings D A Z b self parameters o batchRun r run
    ⟨i, (value, records), result⟩ nonzero
  apply history.position (TreeCheckQueryBudget.ofBound bounded) o
  change n + (2 * halvings (tupleCount (b.batch.jobs.map (circuits b.batch.parameter ·.kind))) + 5) ≤ _
  omega

end ThresholdLeanXmssSecurity.TreeCheckWalkPositions

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkPositions.phase_prepend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkPositions.phase_prepend

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkPositions.Prefix.realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkPositions.Prefix.realize

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkPositions.prefixPositions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkPositions.prefixPositions
