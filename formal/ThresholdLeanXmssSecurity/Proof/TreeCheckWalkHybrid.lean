import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkTails

/-!
# Counted logs at pending-tail check cuts

The raw `seen` certificate is the set of cache inputs introduced by counted
world queries in the actual retained log. It includes setup commitments;
`restrictSeen` subsequently removes them from the coin/expansion certificate.
If a corrupt setup commitment is opened and the uncounted event is absent,
its counted query precedes that opening. It therefore reserves one query at
every later check cut, even when the same query was already cached.

Prefix accounting uses the original `IsQueryBounded` start/step/final witness.
The remaining check allowance is charged at that same step bound. All source
states and logs are retained, including selectively aborted operators.

-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false

noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- Counted cache inputs, including PRG stream-key entries and setup
commitments; free honest queries introduce no entry in this certificate. -/
def treeCheckCountedProjection : (WorldSpec C).Domain → Option (Query C)
  | .inl (.inl t) => soundQueryProjection t
  | _ => none

def treeCheckCountedQueries (log : TreeSimLog C) : List (Query C) :=
  log.filterMap fun row => treeCheckCountedProjection row.1

def treeCheckCountedSeen (log : TreeSimLog C) : Finset (Query C) :=
  (treeCheckCountedQueries log).toFinset

theorem treeCheckCountedProjection_charged (t : (WorldSpec C).Domain)
    (h : (treeCheckCountedProjection t).isSome) : WorldCounted t := by
  rcases t with (t | t) | t
  · exact soundQueryProjection_counted t h
  · simp [treeCheckCountedProjection] at h
  · simp [treeCheckCountedProjection] at h

/-- The raw certificate counts each queried input once, and hence costs no
more than the original counted-query budget of the actual logged prefix. -/
theorem treeCheckCountedQueries_bound {α : Type} (prims : Primitives) (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (n : ℕ) (bound : IsQueryBoundP p WorldCounted n)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    (treeCheckCountedQueries r.2.2).length ≤ (treeCheckCountedQueries s.2).length + n := by
  induction p using OracleComp.inductionOn generalizing n s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact Nat.le_add_right _ n
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at bound
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at run
    obtain ⟨mid, hmid, run⟩ := run
    have hb := ih mid.1 _ (bound.2 mid.1) mid.2 r run
    simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hmid
    obtain ⟨u, _, rfl⟩ := hmid
    simp only [treeCheckCountedQueries, List.filterMap_append, List.length_append,
      List.filterMap_cons, List.filterMap_nil] at hb
    dsimp only [treeCheckCountedQueries]
    cases hp : treeCheckCountedProjection t with
    | none =>
      simp only [hp] at hb
      by_cases ht : WorldCounted t <;>
        simp only [ht, if_true, if_false, List.length_nil] at hb <;> omega
    | some q =>
      have ht := treeCheckCountedProjection_charged t (by simp [hp])
      have hn := bound.1.resolve_left (not_not.mpr ht)
      simp only [hp, if_pos ht, List.length_cons, List.length_nil] at hb
      omega

theorem treeCheckCountedSeen_bound {α : Type} (prims : Primitives) (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (n : ℕ) (bound : IsQueryBoundP p WorldCounted n)
    (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run ((∅, ∅), []))) :
    (treeCheckCountedSeen r.2.2).card ≤ n := by
  exact (List.toFinset_card_le _).trans
    (by simpa only [treeCheckCountedQueries, List.filterMap_nil, List.length_nil, Nat.zero_add] using
      treeCheckCountedQueries_bound prims D p n bound ((∅, ∅), []) r run)

/-- An uncounted opening remains uncounted in every extension: later counted
queries cannot retroactively pay for the opening. -/
theorem treeCheckUncounted_mono (D : C.Coalition) {before after : TreeSimLog C}
    (hprefix : before <+: after) (uncounted : TreeCheckUncounted D before) :
    TreeCheckUncounted D after := by
  obtain ⟨rest, rfl⟩ := hprefix
  obtain ⟨pre, post, j, i, reveal, h, he, hj, hi, missing⟩ := uncounted
  exact ⟨pre, post ++ rest, j, i, reveal, h, by simp [he, List.append_assoc], hj, hi, missing⟩

/-- The counted witness lies in the log before the actual honest opening. -/
theorem treeCheck_counted_before_opening (D : C.Coalition)
    (pre post : TreeSimLog C) (j i : C.Party) (reveal : List HashOutput) (h : HashOutput)
    (hj : j ∈ D.1) (hi : i ∉ D.1)
    (counted : ¬ TreeCheckUncounted D (pre ++ freeEntry (.commit .prss j i reveal) h :: post)) :
    ∃ answer, countedEntry (.commit .prss j i reveal) answer ∈ pre := by
  by_contra absent
  push Not at absent
  exact counted ⟨pre, post, j, i, reveal, h, rfl, hj, hi, absent⟩

/-- A logged corrupt setup commitment, whether its recorded answer is from
the counted or free copy, supplies the exact extra query outside the check
projection when the uncounted event is absent. -/
theorem treeCheck_commitment_reserved (D : C.Coalition) (log : TreeSimLog C)
    (j i : C.Party) (reveal : List HashOutput) (h : HashOutput)
    (hj : j ∈ D.1) (hi : i ∉ D.1)
    (answer : TreeSimHashAnswer log (.commit .prss j i reveal) h)
    (counted : ¬ TreeCheckUncounted D log) :
    ∃ point ∈ treeCheckCountedSeen log, ¬ TreeCheckSeenQuery point := by
  have entry : ∃ answer, countedEntry (.commit .prss j i reveal) answer ∈ log := by
    rcases answer with free | paid
    · obtain ⟨pre, post, he, _⟩ := list_first_mem free
      obtain ⟨answer, mem⟩ := treeCheck_counted_before_opening D pre post j i reveal h hj hi
        (he ▸ counted)
      exact ⟨answer, he ▸ List.mem_append_left _ mem⟩
    · exact ⟨h, paid⟩
  obtain ⟨answer, entry⟩ := entry
  refine ⟨.commit .prss j i reveal, List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨_, entry, ?_⟩), ?_⟩
  · simp only [treeCheckCountedProjection, soundQueryProjection, IsFixed, reduceCtorEq,
      false_and, exists_false, if_false]
  · simp [TreeCheckSeenQuery]

/-- A successful reveal row retains every commitment hash it checked,
including answers read from a cache populated before the setup. -/
theorem treeCheck_reveal_commitments (prims : Primitives) (D : C.Coalition)
    (i : C.Party) (own : Parts C) (committed revealed : Mail C E) (s : TreeSimState C)
    (r : Option (PrssKeys C × List HashOutput) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (prssRevealData i own committed revealed))).run s)) :
    ∀ row, r.1 = some row → ∀ j : C.Party, ∃ h,
      TreeSimHashAnswer r.2.2 (.commit .prss j i (Msg.hashesOf (revealed j))) h := by
  unfold prssRevealData at run
  split_ifs at run with aborted
  · simp only [free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    intro row he
    cases he
  · unfold prssPostRevealData at run
    simp only [free_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
    obtain ⟨opens, hopen, run⟩ := run
    split_ifs at run with accepted
    · simp only [free_bind, free_pure, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at run
      obtain ⟨keys, hkeys, shared, hshared, rfl⟩ := run
      intro row _ j
      have hashes := treeSetup_hashes_logged prims D
        (fun j => Query.commit .prss j i (Msg.hashesOf (revealed j))) C.parties s opens hopen
      have hash := forall₂_getD_idxOf _ _ _ hashes j (by simp [Committee.parties]) 0
      have grows := ((treeSimLoggedWorld_prefix prims D _ opens.2 keys hkeys).trans
        (treeSimLoggedWorld_prefix prims D _ keys.2 shared hshared)).subset
      exact ⟨_, hash.imp (fun h => grows h) (fun h => grows h)⟩
    · simp only [free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      subst r
      intro row he
      cases he

/-- Commitment witnesses survive the ordered traversal of all reveal rows. -/
theorem treeCheck_revealRows_commitments (prims : Primitives) (D : C.Coalition)
    (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (s : TreeSimState C)
    (r : (C.Party → Option (PrssKeys C × List HashOutput)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (prssRevealRows D active parts committed sent))).run s)) :
    ∀ i row, r.1 i = some row → i ∉ D.1 ∧ ∀ j : C.Party, ∃ h,
      TreeSimHashAnswer r.2.2 (revealPoint D active parts sent i j) h := by
  letI : Preorder (TreeSimState C) := {
    le := fun s t => s.2 ⊆ t.2
    le_refl := fun _ => List.Subset.refl _
    le_trans := fun _ _ _ => List.Subset.trans }
  rw [prssRevealRows, free_sequenceFin, simulateQ_sequenceFin] at run
  apply (sequenceFin_state_post _
    (fun i out cache => ∀ row, out = some row → i ∉ D.1 ∧ ∀ j : C.Party, ∃ h,
      TreeSimHashAnswer cache.2 (revealPoint D active parts sent i j) h) ?_ ?_ s r run).2
  · intro i cache result hresult
    refine ⟨(treeSimLoggedWorld_prefix prims D _ cache result hresult).subset, ?_⟩
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hresult
      subst result
      intro row he
      cases he
    · by_cases ha : active i
      · simp only [if_neg hi, if_pos ha] at hresult
        exact fun row he => ⟨hi, treeCheck_reveal_commitments prims D i (parts i)
          (committed i) _ cache result hresult row he⟩
      · simp only [if_neg hi, if_neg ha, free_pure, simulateQ_pure, StateT.run_pure,
          mem_support_pure_iff] at hresult
        subst result
        intro row he
        cases he
  · intro i out cache next grows h row he
    obtain ⟨hi, hashes⟩ := h row he
    refine ⟨hi, fun j => ?_⟩
    obtain ⟨answer, hash⟩ := hashes j
    exact ⟨answer, hash.imp (fun h => grows h) (fun h => grows h)⟩

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- Any successful honest setup output certifies an opening of each corrupt
sender's commitment in that same setup log. -/
theorem treeCheck_setup_commitment (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (s : TreeSimState C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : p ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality
      setupRounds state (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s))
    (i : C.Party) (hi : i ∉ D.1) (keys : PrssKeys C) (present : p.1.2 i = some keys)
    (j : C.Party) :
    ∃ reveal h, TreeSimHashAnswer p.2.2 (.commit .prss j i reveal) h := by
  rw [treeSimRealRoles, ← simulateQ_executePhase] at run
  change p ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality (1 + 2) state
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))))).run s) at run
  rw [executePhase_prssSetup_prefix] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨data, _, adv, _, run⟩ := run
  split_ifs at run with aborted
  · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst p
    cases present
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
    obtain ⟨adv', _, rows, hrows, run⟩ := run
    have nonempty : rows.1 i ≠ none :=
      (finish_facts D prims A adv'.1.1 rows.1 rows.2 p run).1 i (by simp [present]) i hi
    obtain ⟨row, hrow⟩ := Option.ne_none_iff_exists'.mp nonempty
    obtain ⟨h, hash⟩ := (treeCheck_revealRows_commitments prims D _ _ _ _ adv'.2 rows hrows i row hrow).2 j
    have grows := (treeSimLoggedWorld_prefix prims D _ rows.2 p run).subset
    exact ⟨_, h, hash.imp (fun h => grows h) (fun h => grows h)⟩

/-- At any later retained prefix containing a successful setup, the absence
of the uncounted event supplies a real counted reserve. No freshness of the
commitment input is required. -/
theorem treeCheck_setup_reserved (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : p ∈ support (treeSaltSetup prims D A x z))
    (accepted : ∃ i, i ∉ D.1 ∧ (p.1.2 i).isSome) (corrupt : ∃ j, j ∈ D.1)
    (log : TreeSimLog C) (hprefix : p.2.2 <+: log) (counted : ¬ TreeCheckUncounted D log) :
    ∃ point ∈ treeCheckCountedSeen log, ¬ TreeCheckSeenQuery point := by
  obtain ⟨i, hi, accepted⟩ := accepted
  obtain ⟨keys, present⟩ := Option.isSome_iff_exists.mp accepted
  obtain ⟨j, hj⟩ := corrupt
  simp only [treeSaltSetup, mem_support_bind_iff] at run
  obtain ⟨start, _, run⟩ := run
  obtain ⟨reveal, h, hash⟩ := treeCheck_setup_commitment prims D A start.1 start.2 p run i hi keys present j
  exact treeCheck_commitment_reserved D log j i reveal h hj hi
    (hash.imp (fun h => hprefix.subset h) (fun h => hprefix.subset h)) counted

/-- The original all-answer budget witness, retained once for both the
actual prefix and the hybrid adversary's per-step allowance. -/
structure TreeCheckQueryBudget (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (fuel q : ℕ) where
  start : ℕ
  step : ℕ
  final : ℕ
  total : start + fuel * step + final ≤ q
  starts : ∀ x z, IsQueryBoundP (A.start x z) Counted start
  rounds : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step
  answers : ∀ state leak, IsQueryBoundP (A.answer state leak) Counted step
  observes : ∀ r, IsQueryBoundP (Z r) Counted final

def TreeCheckQueryBudget.ofBound {A : Adversary C E (Keys C) PEmpty PEmpty}
    {Z : Distinguisher C A.State TreeOutput} {fuel q : ℕ}
    (bounded : IsQueryBounded A Z fuel q) : TreeCheckQueryBudget A Z fuel q :=
  Classical.choice (by
    obtain ⟨start, step, final, total, starts, rounds, answers, observes⟩ := bounded
    exact ⟨⟨start, step, final, total, starts, rounds, answers, observes⟩⟩)

/-- A retained prefix executes at most its displayed number of adversary
steps. Honest local queries remain on the free side of the same world. -/
theorem TreeCheckQueryBudget.prefix_bound {A : Adversary C E (Keys C) PEmpty PEmpty}
    {Z : Distinguisher C A.State TreeOutput} {fuel q : ℕ}
    (budget : TreeCheckQueryBudget A Z fuel q) (D : C.Coalition) (n : ℕ)
    {α : Type} (program : C.Party → Keys C → PartyM C E RealSpec α)
    (x : C.Party → Keys C) (z : Aux) :
    IsQueryBoundP (realExecution D A noFunctionality n program x z) WorldCounted
      (budget.start + n * budget.step) := by
  unfold realExecution executePhase
  apply isQueryBoundP_bind (isQueryBoundP_adversary _ _ (budget.starts _ _))
  intro state _
  have initial : IsQueryBoundP (startSteps worldRoles D (fun i => program i (x i))) WorldCounted 0 := by
    apply isQueryBoundP_sequenceFin
    intro i
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_free _ _
  simpa only [Nat.zero_add] using isQueryBoundP_bind initial (fun steps _ =>
    isQueryBoundP_executeRounds D A noFunctionality budget.step budget.rounds
      (fun state inputs => isQueryBoundP_runFunctionality_noFunctionality D A state inputs budget.step)
      n state steps)

/-- Actual raw `seen` accounting follows from the prefix's position in the
original fuel budget; no event or actual log is replaced. -/
theorem TreeCheckQueryBudget.accounted {A : Adversary C E (Keys C) PEmpty PEmpty}
    {Z : Distinguisher C A.State TreeOutput} {fuel q : ℕ}
    (budget : TreeCheckQueryBudget A Z fuel q) (prims : Primitives) (D : C.Coalition)
    (n count : ℕ) (room : n + (2 * halvings count + 5) ≤ fuel)
    {α : Type} (program : C.Party → Keys C → PartyM C E RealSpec α)
    (x : C.Party → Keys C) (z : Aux)
    (out : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (realExecution D A noFunctionality n program x z)).run ((∅, ∅), []))) :
    (treeCheckCountedSeen out.2.2).card + (2 * halvings count + 5) * budget.step ≤ q := by
  have card := treeCheckCountedSeen_bound prims D _ _
    (budget.prefix_bound D n program x z) out run
  calc
    _ ≤ budget.start + n * budget.step + (2 * halvings count + 5) * budget.step :=
      Nat.add_le_add_right card _
    _ = budget.start + (n + (2 * halvings count + 5)) * budget.step := by
      simp only [Nat.add_mul, Nat.add_assoc]
    _ ≤ budget.start + fuel * budget.step + budget.final := by
      exact (Nat.add_le_add_left (Nat.mul_le_mul_right budget.step room) budget.start).trans
        (Nat.le_add_right _ _)
    _ ≤ q := budget.total

/-- A real batch continuation preserves its incoming log as a prefix,
through honest queries, future rounds and the final distinguisher. -/
theorem treeCheckBatchCont_log_prefix (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (b : TreeCheckBatchBoundary A)
    (o : TreeCheckTailCheckpoint A) (r : TreeCheckTailResult A)
    (run : r ∈ support (treeCheckBatchCont prims K circuits D A Z b o)) : o.2.2 <+: r.2 := by
  unfold treeCheckBatchCont treeCheckObserve at run
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at run
  obtain ⟨next, hn, out, ho, answer, ha, rfl⟩ := run
  exact (treeSimLoggedWorld_prefix prims D _ o.2 next hn).trans
    ((treeSimLoggedWorld_prefix prims D _ next.2 out ho).trans
      (treeSimLoggedWorld_prefix prims D _ out.2 answer ha))

/-- Countedness at a live tail-walk state already holds at that actual
checkpoint; a later counted query cannot repair an uncounted setup opening. -/
theorem TreeCheckTailWalk.live_counted (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))
    (W : TreeCheckTailWalk A) (c : W.β) (o : TreeCheckTailCheckpoint A)
    (live : (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
      (.inl (c, o))) : ¬ TreeCheckUncounted D o.2.2 := by
  obtain ⟨r, hr, _, counted⟩ := live
  exact fun uncounted => counted (treeCheckUncounted_mono D
    (treeCheckBatchCont_log_prefix prims K circuits D A Z (W.boundary c).batch o r hr) uncounted)

/-- The two presentations of the same after-setup program retain the same
full result and log; the stateful presentation additionally retains caches. -/
theorem treeCheckAfterSetup_eq_audit (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    treeCheckAfterSetup prims K circuits settings top tree D A x Z p =
      (fun out => (out.1, out.2.2)) <$>
        (simulateQ (treeSimLoggedWorld prims D)
          (auditAfterProgram K circuits settings top tree D A x Z p.1.1 p.1.2)).run p.2 := by
  simp only [treeCheckAfterSetup, auditAfterProgram, simulateQ_bind, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  simp only [ceremonyFuel, setupRounds, Nat.add_sub_cancel_left]

/-- A live cut from a true after-setup split forces some honest setup output
to be present; this premise need not be separately assumed by accounting. -/
theorem TreeCheckTailWalk.live_setup (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))
    (W : TreeCheckTailWalk A)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (split : W.Split prims K circuits settings D top tree x Z p)
    (s : (W.cut prims K circuits settings D Z).σ)
    (hs : s ∈ support (W.cut prims K circuits settings D Z).pre)
    (live : (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j s) :
    ∃ i, i ∉ D.1 ∧ (p.1.2 i).isSome := by
  obtain ⟨r, hr, bad, _⟩ := live
  have run : r ∈ support (treeCheckAfterSetup prims K circuits settings top tree D A x Z p) := by
    rw [W.cut_split split, mem_support_bind_iff]
    exact ⟨s, hs, hr⟩
  rw [treeCheckAfterSetup_eq_audit, support_map] at run
  obtain ⟨out, hout, he⟩ := run
  cases he
  obtain ⟨_, _, _, _, i, value, records, _, _, _, _, _, hi, output, _⟩ := bad.2
  by_contra missing
  have absent : ∀ i, i ∉ D.1 → p.1.2 i = none := by
    intro i hi
    by_cases h : p.1.2 i = none
    · exact h
    · exact (missing ⟨i, hi, Option.isSome_iff_ne_none.mpr h⟩).elim
  have none := auditAfter_none prims K circuits settings top tree D A x Z p.1.1 p.1.2
    absent p.2 out hout i hi
  rw [none] at output
  cases output

/-- Exact reserve for the raw hybrid certificate at a live checkpoint of
the fixed walk. Only setup-prefix provenance and the nonempty coalition
case need to be supplied by the global walk. -/
theorem TreeCheckTailWalk.reserved_from_setup (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))
    (W : TreeCheckTailWalk A)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (treeSaltSetup prims D A x z))
    (split : W.Split prims K circuits settings D top tree x Z p)
    (c : W.β) (o : TreeCheckTailCheckpoint A)
    (hs : (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre)
    (live : (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
      (.inl (c, o)))
    (hprefix : p.2.2 <+: o.2.2) (corrupt : ∃ i, i ∈ D.1)
    (seen : (W.hybrid c o).seen = treeCheckCountedSeen o.2.2) :
    ∃ point ∈ (W.hybrid c o).seen, ¬ TreeCheckSeenQuery point := by
  rw [seen]
  exact treeCheck_setup_reserved prims D A x z p hp
    (W.live_setup prims K circuits settings top tree D A x z Z j p split _ hs live)
    corrupt o.2.2 hprefix (W.live_counted prims K circuits settings top tree D A x z Z j c o live)

/-- One witness of the indexed bad event, including the coherent reference
prefix used for its dealer comparison. -/
structure TreeCheckIndexedRecord (prims : Primitives) (circuits : Circuits)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (j : ℕ) (r : TreeCheckTailResult A) where
  parameter : PublicParameter
  seeds : C.Term → HashOutput
  pairs : C.Pair → HashOutput
  party : C.Party
  output : TreeOutput
  records : List (TreeSimCheckBatchRecord C)
  hash : Query C → HashOutput
  record : TreeSimCheckBatchRecord C
  referenceLog : TreeSimLog C
  dealt : x = dealtKeys parameter seeds pairs
  honest : party ∉ D.1
  result : r.1.2.2 party = some (output, records)
  indexed : records[j]? = some record
  referencePrefix : referenceLog <+: r.2
  hashes : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ referenceLog →
    TreeSimCheckWorldHashes hash t u
  wrong : record.outputs ≠ record.jobs.map
    (fun job => ThresholdLeanXmssSecurity.D prims hash (evalJob circuits parameter seeds job))

/-- Select the bad record and its hash view together, from this event. -/
def treeCheckIndexedRecord (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (j : Fin (treeBatches settings tree)) (r : TreeCheckTailResult A)
    (bad : TreeCheckBranchBad prims K circuits settings top tree D A x z j r) :
    TreeCheckIndexedRecord prims circuits D A x j.val r :=
  Classical.choice (by
    obtain ⟨_, parameter, seeds, pairs, i, value, records, hash, before, batch, after,
      dealt, hi, result, _, _, listed, index, _, wrong, reference⟩ := bad.2
    obtain ⟨fuel, pref, audited, dealer, out, _, hpref, _, _, _, _, _, hashes⟩ := reference
    refine ⟨⟨parameter, seeds, pairs, i, value, records, hash, batch, pref, dealt, hi,
      result, ?_, hpref, hashes, wrong⟩⟩
    simp [listed, index])

/-- The scheduled opening head, with its own hash evidence and local states,
whose assembled output is the selected record. It assumes no dealer error,
no coherent hash function and no collision exclusion. -/
structure TreeCheckOpeningTrace (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (b : TreeCheckBatchBoundary A) (o : TreeCheckTailCheckpoint A)
    (record : TreeSimCheckBatchRecord C) where
  live : C.Party → Bool
  ds : C.Party → List HashOutput
  sent : C.Party → Mail C E
  party : C.Party
  before : TreeSimState C
  after : TreeSimState C
  output : ℕ → Bit
  hashes : ∀ h, h ∉ D.1 → live h = true →
    (ds h).length = C.terms.length ∧ ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
      TreeSimHashAnswer before.2 (.copy (vector
        (outputsOf (b.jobs.map (circuits b.parameter ·.kind))).length
        ((treeCheckPrefixData (o.1.2 h)).2.1.1 T))) u
  run : (some output, after) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (free (liftComp (treeSimOpenHead K D live
      (outputsOf (b.jobs.map (circuits b.parameter ·.kind))).length
      (fun h => (treeCheckPrefixData (o.1.2 h)).2.1.1) ds sent party) (LocalSpec C)))).run before)
  recorded : assemble (b.jobs.map (circuits b.parameter ·.kind)) output = record.outputs

/-- Indexed linkage derives all dealer and collision fields of the opening
certificate from this one bad run and this one retained opening head. -/
def treeCheckOpeningAt_of_indexed (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (j : ℕ) (r : TreeCheckTailResult A)
    (record : TreeCheckIndexedRecord prims circuits D A x j r)
    (b : TreeCheckBatchBoundary A) (o : TreeCheckTailCheckpoint A)
    (keys : ∀ h, h ∉ D.1 → (b.ctx h).keys = x h)
    (jobs : b.jobs = record.record.jobs) (parameter : b.parameter = record.parameter)
    (hprefix : o.2.2 <+: record.referenceLog)
    (trace : TreeCheckOpeningTrace prims K circuits D A b o record.record)
    (later : trace.after.2 <+: r.2) (good : ¬ TreeSimHashBudgetCollision r.2) :
    TreeCheckOpeningAt prims K circuits D A b o where
  seeds := record.seeds
  seed := fun h T hh held => by
    rw [keys h hh]
    simpa only [dealtKeys, if_pos held] using
      congrArg (fun x : C.Party → Keys C => (x h).seed T) record.dealt
  hash := record.hash
  rows := fun t u mem => record.hashes t u (hprefix.subset mem)
  live := trace.live
  ds := trace.ds
  sent := trace.sent
  party := trace.party
  before := trace.before
  after := trace.after
  output := trace.output
  hashes := trace.hashes
  run := trace.run
  good := by
    rintro ⟨a, b, h, ha, hb, different, ahash, bhash⟩
    exact good ⟨a, b, h, ha, hb, different,
      ahash.imp (fun h => later.subset h) (fun h => later.subset h),
      bhash.imp (fun h => later.subset h) (fun h => later.subset h)⟩
  wrong := by
    rw [trace.recorded, jobs, parameter]
    exact record.wrong

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (top : TopTree) (tree : Tree) (D : C.Coalition)
variable (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
variable (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))

/-- Provenance of the indexed record and its scheduled opening, at the same
checkpoint and the same bad continuation. -/
def TreeCheckTailWalk.IndexedOpening (W : TreeCheckTailWalk A) : Prop :=
  ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre →
    ∀ r ∈ support ((W.cut prims K circuits settings D Z).cont (.inl (c, o))),
      TreeCheckBranchBad prims K circuits settings top tree D A x z j r →
        ¬ TreeCheckUncounted D r.2 →
        ∃ record : TreeCheckIndexedRecord prims circuits D A x j.val r,
        (∀ h, h ∉ D.1 → ((W.boundary c).batch.ctx h).keys = x h) ∧
        (W.boundary c).batch.jobs = record.record.jobs ∧
        (W.boundary c).batch.parameter = record.parameter ∧
        o.2.2 <+: record.referenceLog ∧
        ∃ trace : TreeCheckOpeningTrace prims K circuits D A (W.boundary c).batch o record.record,
          trace.after.2 <+: r.2

theorem TreeCheckTailWalk.opening_of_indexed (W : TreeCheckTailWalk A)
    (indexed : W.IndexedOpening prims K circuits settings top tree D A x z Z j) :
    W.Opening prims K circuits settings D top tree x z Z j := by
  intro c o hs live
  obtain ⟨r, hr, bad, counted⟩ := live
  obtain ⟨record, keys, jobs, parameter, hprefix, trace, later⟩ := indexed c o hs r hr bad counted
  exact ⟨treeCheckOpeningAt_of_indexed prims K circuits D A x j.val r record
    (W.boundary c).batch o keys jobs parameter hprefix trace later bad.1⟩

/-- A nonaborted local continuation contains the actual successful opening
head before its continuation's local queries. The intermediate cache and log
are retained instead of replaying the opening from a different state. -/
theorem treeCheck_open_local_trace {α : Type} (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) (s : TreeSimState C)
    (out : Step C E RealSpec α × TreeSimState C)
    (run : out ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (roundLocal D (treeSimOpenPartial K D live count v ds k) sent i))).run s))
    (kept : out.1 ≠ .done none) :
    ∃ value after,
      (some value, after) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C)))).run s) ∧
      after.2 <+: out.2.2 := by
  rw [treeLockstep_open_local_factor] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨⟨value, after⟩, head, rest⟩ := run
  cases value with
  | none =>
    simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at rest
    exact (kept (congrArg Prod.fst rest)).elim
  | some value =>
    exact ⟨value, after, head, treeSimLoggedWorld_prefix prims D _ after out rest⟩

/-- The actual checkpoint state is reached by a bounded world prefix. The
honest program may stop at a local boundary before its next head, which is
why it is retained explicitly rather than replaced by a full-round snapshot. -/
structure TreeCheckPrefixPosition (budget : TreeCheckQueryBudget A Z (ceremonyFuel circuits settings) q)
    (count : ℕ) (checkpoint : TreeCheckTailCheckpoint A) where
  rounds : ℕ
  outputType : Type
  program : C.Party → Keys C → PartyM C E RealSpec outputType
  output : (A.State × (C.Party → Option outputType)) × TreeSimState C
  run : output ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (realExecution D A noFunctionality rounds program x z)).run ((∅, ∅), []))
  state : output.1.1 = checkpoint.1.1
  world : output.2 = checkpoint.2
  room : rounds + (2 * halvings count + 5) ≤ ceremonyFuel circuits settings

variable {prims K circuits settings top tree D A x z Z j}

/-- Numeric accounting at the same checkpoint follows from its actual
position and the fixed original budget. -/
theorem TreeCheckPrefixPosition.accounted {q count : ℕ}
    {budget : TreeCheckQueryBudget A Z (ceremonyFuel circuits settings) q}
    {checkpoint : TreeCheckTailCheckpoint A}
    (position : TreeCheckPrefixPosition prims circuits settings D A x z Z budget count checkpoint) :
    (treeCheckCountedSeen checkpoint.2.2).card + (2 * halvings count + 5) * budget.step ≤ q := by
  rw [← position.world]
  exact budget.accounted prims D position.rounds count position.room position.program x z
    position.output position.run

variable (prims K circuits settings top tree D A x z Z j)

/-- Source-level provenance at each supported live checkpoint. These fields
describe its retained setup prefix, actual counted log and remaining fuel. -/
def TreeCheckTailWalk.LogSources (q : ℕ)
    (budget : TreeCheckQueryBudget A Z (ceremonyFuel circuits settings) q)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (W : TreeCheckTailWalk A) : Prop :=
  ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre →
    (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
      (.inl (c, o)) →
    (W.hybrid c o).seen = treeCheckCountedSeen o.2.2 ∧
    (W.hybrid c o).step = budget.step ∧ p.2.2 <+: o.2.2 ∧ (∃ i, i ∈ D.1) ∧
    Nonempty (TreeCheckPrefixPosition prims circuits settings D A x z Z budget
      ((W.cut prims K circuits settings D Z).count (.inl (c, o))) o)

/-- The two raw budget obligations of `Prepared` follow together from the
same actual logs, prefix positions and original budget witness. -/
theorem TreeCheckTailWalk.accounting_of_sources (q : ℕ)
    (budget : TreeCheckQueryBudget A Z (ceremonyFuel circuits settings) q)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (treeSaltSetup prims D A x z)) (W : TreeCheckTailWalk A)
    (split : W.Split prims K circuits settings D top tree x Z p)
    (unreached : W.Unreached prims K circuits settings D top tree x z j)
    (source : W.LogSources prims K circuits settings top tree D A x z Z j q budget p) :
    (∀ s ∈ support (W.cut prims K circuits settings D Z).pre,
      (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j s →
      ((W.cut prims K circuits settings D Z).hybrid s).seen.card +
        (2 * halvings ((W.cut prims K circuits settings D Z).count s) + 5) *
          ((W.cut prims K circuits settings D Z).hybrid s).step ≤ q) ∧
    (∀ s ∈ support (W.cut prims K circuits settings D Z).pre,
      (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j s →
      ∃ point ∈ ((W.cut prims K circuits settings D Z).hybrid s).seen, ¬ TreeCheckSeenQuery point) := by
  have noFinished (r : TreeCheckTailResult A)
      (hs : (.inr r : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre)
      (live : (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
        (.inr r)) : False := by
    obtain ⟨r', hr, bad, counted⟩ := live
    have he : r' = r := by simpa only [TreeCheckTailWalk.cut, support_pure, Set.mem_singleton_iff] using hr
    subst r'
    exact unreached r (W.mem_support_cut_pre_inr hs) ⟨bad, counted⟩
  constructor
  · rintro (⟨c, o⟩ | r) hs live
    · obtain ⟨seen, step, _, _, ⟨position⟩⟩ := source c o hs live
      change (W.hybrid c o).seen.card + _ * (W.hybrid c o).step ≤ q
      rw [seen, step]
      exact position.accounted
    · exact (noFinished r hs live).elim
  · rintro (⟨c, o⟩ | r) hs live
    · obtain ⟨seen, _, hprefix, corrupt, _⟩ := source c o hs live
      exact W.reserved_from_setup prims K circuits settings top tree D A x z Z j p hp split
        c o hs live hprefix corrupt seen
    · exact (noFinished r hs live).elim

/-- All structural and hybrid clauses concern this one walk. Indexed
opening provenance and actual logged prefix positions replace the derived
`Opening`, `accounted` and `reserved` fields. -/
structure TreeCheckTailWalk.Sources (q : ℕ)
    (budget : TreeCheckQueryBudget A Z (ceremonyFuel circuits settings) q)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (W : TreeCheckTailWalk A) : Prop where
  split : W.Split prims K circuits settings D top tree x Z p
  standard : W.StandardTuples circuits D
  self : ∀ c i, ((W.boundary c).batch.ctx i).self = i
  jobs : (W.cut prims K circuits settings D Z).Jobs prims K circuits settings top tree D A x z j
  unreached : W.Unreached prims K circuits settings D top tree x z j
  consistent : W.Consistent prims K circuits settings D top tree x z Z j
  opening : W.IndexedOpening prims K circuits settings top tree D A x z Z j
  logs : W.LogSources prims K circuits settings top tree D A x z Z j q budget p
  queries : (W.cut prims K circuits settings D Z).Queries prims K circuits settings top tree D A x z j
  cache : (W.cut prims K circuits settings D Z).Cache prims K circuits settings top tree D A x z j
  prior : (W.cut prims K circuits settings D Z).Prior prims K circuits settings top tree D A x z j
  transport : (W.cut prims K circuits settings D Z).Transport prims K circuits settings top tree D A x z j

theorem TreeCheckTailWalk.prepared_of_sources (q : ℕ)
    (budget : TreeCheckQueryBudget A Z (ceremonyFuel circuits settings) q)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (treeSaltSetup prims D A x z)) (W : TreeCheckTailWalk A)
    (source : W.Sources prims K circuits settings top tree D A x z Z j q budget p) :
    W.Prepared prims K circuits settings top tree D A x z Z q j p := by
  obtain ⟨accounted, reserved⟩ := W.accounting_of_sources prims K circuits settings top tree D A x z Z j
    q budget p hp source.split source.unreached source.logs
  exact {
    split := source.split
    standard := source.standard
    self := source.self
    jobs := source.jobs
    unreached := source.unreached
    consistent := source.consistent
    opening := W.opening_of_indexed prims K circuits settings top tree D A x z Z j source.opening
    queries := source.queries
    cache := source.cache
    prior := source.prior
    accounted := accounted
    reserved := reserved
    transport := source.transport }

/-- Global source construction at the original quantifiers. The budget is
selected once from the given bound and every clause uses one walk witness. -/
def TreeCheckTailWalkSourceConstruction : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x →
      ∀ bounded : IsQueryBounded A Z (ceremonyFuel circuits settings) q, q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
        ∀ p ∈ support (treeSaltSetup prims D A x z), ∃ W : TreeCheckTailWalk A,
          W.Sources prims K circuits settings top tree D A x z Z j q
            (TreeCheckQueryBudget.ofBound bounded) p

theorem treeCheckTailWalkConstruction_of_sources
    (sources : TreeCheckTailWalkSourceConstruction prims K circuits settings) :
    TreeCheckTailWalkConstruction prims K circuits settings := by
  intro hbatch top tree D A x z Z q dealt bounded small j p hp
  obtain ⟨W, source⟩ := sources hbatch top tree D A x z Z q dealt bounded small j p hp
  exact ⟨W, W.prepared_of_sources prims K circuits settings top tree D A x z Z j q
    (TreeCheckQueryBudget.ofBound bounded) p hp source⟩

/-- The fixed source walk, its actual raw logs and its fixed `seen`
projection supply the original counted cut without any error loss. -/
theorem treeCheckCountedCutParts_of_tailSources
    (sources : TreeCheckTailWalkSourceConstruction prims K circuits settings) :
    TreeCheckCountedCutParts prims K circuits settings :=
  treeCheckCountedCutParts_of_tailConstruction prims K circuits settings
    (treeCheckTailWalkConstruction_of_sources prims K circuits settings sources)

/-- info: 'ThresholdLeanXmssSecurity.treeCheckCountedSeen_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckCountedSeen_bound

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_counted_before_opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_counted_before_opening

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_setup_commitment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_setup_commitment

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_setup_reserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_setup_reserved

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckQueryBudget.accounted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckQueryBudget.accounted

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailWalk.live_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailWalk.live_setup

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailWalk.reserved_from_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailWalk.reserved_from_setup

/-- info: 'ThresholdLeanXmssSecurity.treeCheckOpeningAt_of_indexed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckOpeningAt_of_indexed

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailWalk.opening_of_indexed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailWalk.opening_of_indexed

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_open_local_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_open_local_trace

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckPrefixPosition.accounted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckPrefixPosition.accounted

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailWalk.accounting_of_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailWalk.accounting_of_sources

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckTailWalk.prepared_of_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckTailWalk.prepared_of_sources

/-- info: 'ThresholdLeanXmssSecurity.treeCheckCountedCutParts_of_tailSources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckCountedCutParts_of_tailSources

end ThresholdLeanXmssSecurity
