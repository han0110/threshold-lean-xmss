import ThresholdLeanXmssSecurity.Proof.TreeCheckHonestDisc
import ThresholdLeanXmssSecurity.Proof.TreeCheckSeenCovered
import VCVio.OracleComp.SimSemantics.StateT.PreservesInv

/-!
# Honest check queries at first-run checkpoints

Free coin-key entries have labels below the checkpoint's batch start.
Free expansion entries use a key returned by an earlier coin at that cutoff.
The key witness is retained in the actual public cache.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false
set_option maxRecDepth 2000

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckHonestLog

open TreeCheckWalkDef (Decoded initial index_support)
open TreeCheckWalkRecipe TreeCheckWalkState TreeCheckHonestDisc TreeSimHashCount

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E α β : Type}

/-- Exactly the two free-query clauses needed at a first-run checkpoint. -/
def HonestCheckLog (limit : ℕ) (cache : HashCache C) (log : TreeSimLog C) : Prop :=
  (∀ tag label bits answer,
    (⟨.inr (.inr (.inl (.coinKey tag label bits))), answer⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log → label < limit) ∧
  (∀ key index answer,
    (⟨.inr (.inr (.inl (.expand key index))), answer⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log → key ∈ priorKeys limit cache)

theorem priorKeys_mono {limit limit' : ℕ} {cache cache' : HashCache C}
    (hl : limit ≤ limit') (hc : cache ≤ cache') : priorKeys limit cache ⊆ priorKeys limit' cache' := by
  intro key h
  obtain ⟨tag, label, bits, below, answer⟩ := (Finset.mem_filter.mp h).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, tag, label, bits, below.trans_le hl, hc answer⟩

theorem HonestCheckLog.mono {limit limit' : ℕ} {cache cache' : HashCache C} {log : TreeSimLog C}
    (h : HonestCheckLog limit cache log) (hl : limit ≤ limit') (hc : cache ≤ cache') :
    HonestCheckLog limit' cache' log :=
  ⟨fun _ _ _ _ mem => (h.1 _ _ _ _ mem).trans_le hl,
    fun _ _ _ mem => priorKeys_mono hl hc (h.2 _ _ _ mem)⟩

def EntryDisc (limit : ℕ) (cache : HashCache C) :
    ((t : (WorldSpec C).Domain) × (WorldSpec C).Range t) → Prop
  | ⟨.inr (.inr (.inl (.coinKey _ label _))), _⟩ => label < limit
  | ⟨.inr (.inr (.inl (.expand key _))), _⟩ => key ∈ priorKeys limit cache
  | _ => True

theorem honestCheckLog_iff {limit : ℕ} {cache : HashCache C} {log : TreeSimLog C} :
    HonestCheckLog limit cache log ↔ ∀ entry ∈ log, EntryDisc limit cache entry := by
  constructor
  · intro h ⟨t, answer⟩ mem
    rcases t with counted | (noise | (q | prg))
    · trivial
    · trivial
    · cases q <;> simp only [EntryDisc]
      all_goals first | trivial | exact h.1 _ _ _ _ mem | exact h.2 _ _ _ mem
    · trivial
  · intro h
    exact ⟨fun _ _ _ _ mem => h _ mem, fun _ _ _ mem => h _ mem⟩

theorem HonestCheckLog.append {limit : ℕ} {cache cache' : HashCache C} {log : TreeSimLog C}
    (h : HonestCheckLog limit cache log) (hc : cache ≤ cache')
    (entry : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t)
    (he : EntryDisc limit cache' entry) : HonestCheckLog limit cache' (log ++ [entry]) := by
  rw [honestCheckLog_iff] at ⊢
  intro e mem
  rcases List.mem_append.mp mem with old | new
  · exact honestCheckLog_iff.mp (h.mono le_rfl hc) e old
  · have eq : e = entry := by simpa only [List.mem_singleton] using new
    exact eq ▸ he

/-- The keys accumulated during a local pass have actual cached coin witnesses. -/
def KeysInCache (limit : ℕ) (keys : Set HashOutput) (cache : HashCache C) : Prop :=
  ∀ key ∈ keys, key ∈ priorKeys limit cache

theorem KeysInCache.mono {limit : ℕ} {keys : Set HashOutput} {cache cache' : HashCache C}
    (h : KeysInCache limit keys cache) (hc : cache ≤ cache') : KeysInCache limit keys cache' :=
  fun key mem => priorKeys_mono le_rfl hc (h key mem)

variable (prims : Primitives) (D : C.Coalition)

theorem free_coinKey_cached (s : TreeSimState C) (tag label : ℕ) (bits : List Bit)
    (r : HashOutput × TreeSimState C)
    (run : r ∈ support ((treeSimLoggedWorld prims D (.inr (.inr (.inl (.coinKey tag label bits))))).run s)) :
    r.2.1.1 (.coinKey tag label bits) = some r.1 := by
  simp only [treeSimLoggedWorld, StateT.run_mk, streamWorld, onHash, localAnswer, support_map] at run
  obtain ⟨p, hp, rfl⟩ := run
  obtain ⟨a, ha, rfl⟩ := hp
  exact (randomOracle_support (.coinKey tag label bits) s.1.1 a ha).2.1

theorem free_query (limit : ℕ) (keys : Set HashOutput) (q : (LocalSpec C).Domain)
    (s : TreeSimState C) (r : (LocalSpec C).Range q × TreeSimState C)
    (disc : LocalDisc limit keys q) (known : KeysInCache limit keys s.1.1)
    (honest : HonestCheckLog limit s.1.1 s.2)
    (run : r ∈ support ((treeSimLoggedWorld prims D (.inr q)).run s)) :
    HonestCheckLog limit r.2.1.1 r.2.2 ∧ KeysInCache limit (localKeys keys q r.1) r.2.1.1 := by
  have cached : ∀ tag label bits, q = .inr (.inl (.coinKey tag label bits)) →
      ∀ h : HashOutput, (⟨q, r.1⟩ : (q : (LocalSpec C).Domain) × (LocalSpec C).Range q) =
        ⟨.inr (.inl (.coinKey tag label bits)), h⟩ → r.2.1.1 (.coinKey tag label bits) = some h := by
    intro tag label bits eq h he
    subst q
    have same : r.1 = h := by simpa using he
    rw [← same]
    exact free_coinKey_cached prims D s tag label bits r run
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map] at run
  obtain ⟨p, hp, rfl⟩ := run
  have grow := treeSim_streamWorld_grows prims D (.inr q) s.1 p hp
  have known' := known.mono grow
  constructor
  · apply honest.append grow
    rcases q with noise | (q | prg)
    · trivial
    · cases q <;> simp only [EntryDisc, LocalDisc] at disc ⊢
      all_goals first | trivial | exact disc | exact known' _ disc
    · trivial
  · rcases q with noise | (q | prg)
    · exact known'
    · cases q <;> simp only [localKeys]
      all_goals try exact known'
      rename_i tag label bits
      intro key mem
      rcases Set.mem_insert_iff.mp mem with eq | old
      · subst key
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, tag, label, bits, disc,
          cached tag label bits rfl _ rfl⟩
      · exact known' _ old
    · exact known'

theorem counted_query (limit : ℕ) (q : (LocalSpec C).Domain)
    (s : TreeSimState C) (r : (LocalSpec C).Range q × TreeSimState C)
    (honest : HonestCheckLog limit s.1.1 s.2)
    (run : r ∈ support ((treeSimLoggedWorld prims D (.inl (.inl q))).run s)) :
    HonestCheckLog limit r.2.1.1 r.2.2 := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map] at run
  obtain ⟨p, hp, rfl⟩ := run
  exact honest.append (treeSim_streamWorld_grows prims D _ s.1 p hp) _ trivial

/-- General-key preservation inside one atomic honest pass. -/
theorem advance_honest (limit : ℕ) (keys : Set HashOutput)
    (P : OracleComp (PartySpec C E RealSpec) (Option α))
    (disc : CheckDisc limit 1 keys P) (s : TreeSimState C)
    (known : KeysInCache limit keys s.1.1) (honest : HonestCheckLog limit s.1.1 s.2)
    (r : Step C E RealSpec α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free (advance P))).run s)) :
    HonestCheckLog limit r.2.1.1 r.2.2 := by
  induction P using OracleComp.inductionOn generalizing keys s r with
  | pure a =>
    simp only [advance_pure, free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact honest
  | query_bind t k ih =>
    rcases t with (q | out) | impossible
    · rw [advance_query_bind, free_bind] at run
      simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
      obtain ⟨mid, hmid, hrun⟩ := run
      have hquery : mid ∈ support ((treeSimLoggedWorld prims D (.inr q)).run s) := by
        change mid ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr q)))).run s) at hmid
        simpa only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map] using hmid
      obtain ⟨honest', known'⟩ := free_query prims D limit keys q s mid disc.local_inv.1 known honest hquery
      exact ih mid.1 (localKeys keys q mid.1) (disc.local_inv.2 mid.1) mid.2 known' honest' r hrun
    · change r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (free (pure (.wait out k) : OracleComp (LocalSpec C) _))).run s) at run
      simp only [free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      subst r
      exact honest
    · exact impossible.elim

/-- A predicate on WorldSpec selecting only the free check domains. -/
def FreeCheckQuery : (WorldSpec C).Domain → Prop
  | .inr q => CheckQuery q
  | _ => False

theorem quiet_query (limit : ℕ) (t : (WorldSpec C).Domain)
    (quiet : ¬ FreeCheckQuery t) (s : TreeSimState C)
    (r : (WorldSpec C).Range t × TreeSimState C) (honest : HonestCheckLog limit s.1.1 s.2)
    (run : r ∈ support ((treeSimLoggedWorld prims D t).run s)) :
    HonestCheckLog limit r.2.1.1 r.2.2 := by
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map] at run
  obtain ⟨p, hp, rfl⟩ := run
  apply honest.append (treeSim_streamWorld_grows prims D t s.1 p hp)
  rcases t with counted | (noise | (q | prg))
  · trivial
  · trivial
  · cases q <;> simp_all [FreeCheckQuery, CheckQuery, EntryDisc]
  · trivial

theorem run_quiet (limit : ℕ) (p : OracleComp (WorldSpec C) α)
    (quiet : IsQueryBoundP p FreeCheckQuery 0) (s : TreeSimState C)
    (honest : HonestCheckLog limit s.1.1 s.2) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    HonestCheckLog limit r.2.1.1 r.2.2 := by
  induction p using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact honest
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at quiet
    have ht : ¬ FreeCheckQuery t := quiet.1.resolve_right (by omega)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at run
    obtain ⟨mid, hmid, hrun⟩ := run
    exact ih mid.1 (by simpa only [if_neg ht] using quiet.2 mid.1) mid.2
      (quiet_query prims D limit t ht s mid honest hmid) r hrun

theorem counted_zero (p : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (worldRoles.adversary p) FreeCheckQuery 0 := by
  change IsQueryBoundP (counted (liftComp p _)) FreeCheckQuery 0
  apply ProgramQuiet.qb0_simulateQ
  intro t
  apply (isQueryBoundP_query_iff _ _ _).2
  simp [FreeCheckQuery]

theorem free_zero (p : OracleComp (LocalSpec C) α) (quiet : IsQueryBoundP p CheckQuery 0) :
    IsQueryBoundP (free p) FreeCheckQuery 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at quiet
    rw [free_bind]
    have ht : ¬ CheckQuery t := quiet.1.resolve_right (by omega)
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr t)) >>=
      fun r => free (k r)) FreeCheckQuery 0
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨Or.inl ht, fun r => ?_⟩
    simpa only [FreeCheckQuery, if_neg ht] using ih r (by simpa only [if_neg ht] using quiet.2 r)

-- Port of the private treeSim_sequenceFin_preserves_prop in TreeSim.lean.
theorem sequenceFin_preserves {σ : Type} {n : ℕ} (P : σ → Prop)
    (f : Fin n → StateT σ ProbComp α)
    (preserve : ∀ i, StateT.PreservesInv (f i) P) :
    StateT.PreservesInv (Concrete.sequenceFin f) P := by
  intro s hs r hr
  induction n generalizing s with
  | zero =>
    have eq : r = (Fin.elim0, s) := by simpa [Concrete.sequenceFin] using hr
    subst r
    exact hs
  | succ n ih =>
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr
    exact ih (fun i => f i.succ) (fun i => preserve i.succ) u.2
      (preserve 0 s hs u hu) v hv

theorem start_honest (limit : ℕ) (program : C.Party → PartyM C E RealSpec α)
    (disc : ∀ i, i ∉ D.1 → CheckDisc limit 1 ∅ (program i).run)
    (s : TreeSimState C) (honest : HonestCheckLog limit s.1.1 s.2)
    (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D program)).run s)) :
    HonestCheckLog limit r.2.1.1 r.2.2 := by
  unfold startSteps at run
  rw [simulateQ_sequenceFin] at run
  apply sequenceFin_preserves (fun s : TreeSimState C => HonestCheckLog limit s.1.1 s.2) _ _ s honest r run
  intro i s hs r hr
  split_ifs at hr with hi
  · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact hs
  · exact advance_honest prims D limit ∅ (program i).run (disc i hi) s
      (fun _ mem => mem.elim) hs r hr

variable {A : Adversary C E (Keys C) PEmpty PEmpty}

theorem next_honest (limit : ℕ) (Z : Distinguisher C A.State TreeOutput)
    (fuel : ℕ) (p q : TreeCheckWalkDef.Pending A)
    (honest : HonestCheckLog limit p.world.1.1 p.world.2)
    (disc : ∀ i, i ∉ D.1 → CheckDisc limit 1 ∅ (p.program i).run)
    (run : .inl q ∈ support (TreeCheckWalkDef.next prims D Z fuel p)) :
    HonestCheckLog limit q.world.1.1 q.world.2 := by
  unfold TreeCheckWalkDef.next at run
  simp only [mem_support_bind_iff] at run
  obtain ⟨started, hs, run⟩ := run
  have honest' := start_honest prims D limit p.program disc p.world honest started hs
  split_ifs at run
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at run
    obtain ⟨_, _, impossible⟩ := run
    cases impossible
  · simp only [mem_support_bind_iff, mem_support_pure_iff, Sum.inl.injEq] at run
    obtain ⟨reply, hr, rfl⟩ := run
    exact run_quiet prims D limit _ (counted_zero _) _ honest' reply hr

section QuietNetwork

variable [Field E] [Algebra Bit E]

/-- Every honest continuation of a quiet step remains quiet after delivery. -/
theorem round_quiet (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, StepBudget CheckQuery (steps i) 0) :
    IsQueryBoundP (stepRound worldRoles D A noFunctionality state steps) FreeCheckQuery 0 := by
  rw [stepRound_real]
  refine ProgramQuiet.qb0_bind' (counted_zero _) fun reply => ?_
  refine ProgramQuiet.qb0_bind' (free_zero _ ?_) fun _ => isQueryBoundP_pure _ _ _
  apply isQueryBoundP_sequenceFin
  intro i
  unfold roundLocal
  cases h : steps i with
  | done out => exact isQueryBoundP_pure _ _ _
  | wait out resume =>
    have hb := hsteps i
    rw [h] at hb
    dsimp only
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · exact advance_zero CheckQuery _ (hb _)
  | call input _ => exact input.elim

theorem round_steps_quiet (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, StepBudget CheckQuery (steps i) 0)
    (r : A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E))
    (run : r ∈ support (stepRound worldRoles D A noFunctionality state steps)) :
    ∀ i, StepBudget CheckQuery (r.2.1 i) 0 := by
  rw [stepRound_real] at run
  simp only [mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨reply, _, locals, hl, rfl⟩ := run
  have each := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _ hl)
  intro i
  change StepBudget CheckQuery (locals i) 0
  have localRun := each i
  unfold roundLocal at localRun
  cases h : steps i with
  | done out =>
    simp only [h, mem_support_pure_iff] at localRun
    rw [localRun]
    trivial
  | wait out resume =>
    have hb := hsteps i
    rw [h] at hb
    simp only [h] at localRun
    split_ifs at localRun
    · simp only [mem_support_pure_iff] at localRun
      rw [localRun]
      trivial
    · exact advance_stepBudget CheckQuery _ (hb _) _ localRun
  | call input _ => exact input.elim

theorem rounds_honest (limit : ℕ) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (hsteps : ∀ i, StepBudget CheckQuery (steps i) 0)
    (s : TreeSimState C) (honest : HonestCheckLog limit s.1.1 s.2)
    (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executeRounds worldRoles D A noFunctionality fuel state steps)).run s)) :
    HonestCheckLog limit r.2.1.1 r.2.2 := by
  induction fuel generalizing state steps s with
  | zero =>
    simp only [executeRounds, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact honest
  | succ fuel ih =>
    rw [executeRounds] at run
    split_ifs at run
    · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      subst r
      exact honest
    · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
      obtain ⟨mid, hmid, hrun⟩ := run
      exact ih mid.1.1 mid.1.2.1
        (round_steps_quiet D state steps hsteps mid.1 (treeCheck_logged_support prims D _ _ hmid))
        mid.2 (run_quiet prims D limit _ (round_quiet D state steps hsteps) s honest mid hmid) hrun

theorem phase_honest_quiet (limit : ℕ) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α)
    (quiet : ∀ i, PartyBudget CheckQuery (program i) 0)
    (s : TreeSimState C) (honest : HonestCheckLog limit s.1.1 s.2)
    (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state program)).run s)) :
    HonestCheckLog limit r.2.1.1 r.2.2 := by
  unfold executePhase at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨started, hs, hrun⟩ := run
  have honest' := start_honest prims D limit program
    (fun i _ => Disc.of_quiet (quiet i) 1) s honest started hs
  apply rounds_honest prims D limit fuel state started.1 _ started.2 honest' r hrun
  intro i
  have each := mem_support_sequenceFin_oc _ _ (treeCheck_logged_support prims D _ _ hs) i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, mem_support_pure_iff] at each
    rw [each]
    trivial
  · simp only [if_neg hi, worldRoles] at each
    exact advance_stepBudget CheckQuery _ (quiet i) _ (treeSimCheck_support_free _ each)

-- Port of TreeSimHashCount.derive_zero and setup_bound, with CheckQuery
-- excluding both coinKey and expand throughout the setup.
theorem derive_check_zero (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    IsQueryBoundP (deriveKeys phase i view) (fun t => CheckQuery (C := C) (.inr t)) 0 := by
  unfold deriveKeys
  dsimp only
  rw [← ite_bind]
  refine isQueryBoundP_bind (p := fun t => CheckQuery (.inr t))
    (n := 0) (m := 0) ?_ (fun parameter _ => ?_)
  · split_ifs
    · exact hash_zero _ (by simp [CheckQuery])
    · exact isQueryBoundP_pure _ _ _
  · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun terms _ => ?_)
    · simpa using queryBound_mapM (fun t => CheckQuery (C := C) (.inr t)) _ 0 C.terms
        (fun T _ => by
          split_ifs
          · exact hash_zero _ (by simp [CheckQuery])
          · exact isQueryBoundP_pure _ _ _)
    · refine isQueryBoundP_bind (n := 0) (m := 0) ?_ (fun pairs _ => isQueryBoundP_pure _ _ _)
      simpa using queryBound_mapM (fun t => CheckQuery (C := C) (.inr t)) _ 0 C.parties
        (fun j _ => by
          split_ifs
          · exact isQueryBoundP_pure _ _ _
          · exact hash_zero _ (by simp [CheckQuery]))

theorem sample_check_zero (p : ProbComp α) :
    IsQueryBoundP (liftComp p (LocalSpec C)) CheckQuery 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, liftComp_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (.inl t)) >>= fun u =>
      liftComp (k u) (LocalSpec C)) CheckQuery 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [CheckQuery]), fun u => by simpa [CheckQuery] using ih u⟩

theorem setup_check_zero (i : C.Party) :
    PartyBudget CheckQuery (prssSetup i : PartyM C E RealSpec _) 0 := by
  have hm (f : C.Party → Query C) (hf : ∀ j, ¬ CheckQuery (.inr (.inl (f j)))) :
      PartyBudget CheckQuery (oracleStep (C.parties.mapM fun j => hashQuery (f j)) :
        PartyM C E RealSpec _) 0 := by
    apply oracle_bound (E := E)
    simpa using queryBound_mapM (fun t => CheckQuery (C := C) (.inr t))
      (fun j => hashQuery (f j)) 0 C.parties (fun j _ => TreeCheckHonestDisc.hash_zero _ (hf j))
  unfold prssSetup
  refine (localStep_bound (E := E) (G := RealSpec) (sample_check_zero (sampleParts (C := C)))).bind (m := 0) fun own => ?_
  unfold commitRevealEcho
  simp only [bind_assoc]
  exact (hm _ (fun _ => by simp [CheckQuery])).bind fun commits =>
    (party_quiet_of_zero (PartyBound.exchange _)).bind fun committed =>
      (party_quiet_of_zero (PartyBound.exchange _)).bind fun revealed =>
        (hm _ (fun _ => by simp [CheckQuery])).bind fun opens =>
          (party_quiet_of_zero (PartyBound.require _)).bind fun _ =>
            (oracle_bound (derive_check_zero _ _ _)).bind fun keys =>
              (hm _ (fun _ => by simp [CheckQuery])).bind fun shared =>
                (party_quiet_of_zero (PartyBound.exchange _)).bind fun received =>
                  (party_quiet_of_zero (PartyBound.require _)).bind fun _ =>
                    (PartyBudget.pure _).bind fun result => PartyBudget.pure _

theorem setup_honest (limit : ℕ) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : p ∈ support (treeSaltSetup prims D A x z)) :
    HonestCheckLog limit p.2.1.1 p.2.2 := by
  unfold treeSaltSetup at run
  rw [mem_support_bind_iff] at run
  obtain ⟨start, hs, run⟩ := run
  have honest : HonestCheckLog limit start.2.1.1 start.2.2 :=
    run_quiet prims D limit _ (counted_zero _) _ ⟨by simp, by simp⟩ start hs
  apply phase_honest_quiet prims D limit _ _ _ (fun i => setup_check_zero i) _ honest p
  simpa only [simulateQ_executePhase, treeSimRealRoles] using run


/-- The local tail is consumed before the first exchange; every retained
continuation then belongs to the quiet batch prefix. -/
theorem prelude_advance_quiet (gate : OracleComp (LocalSpec C) (Option Unit))
    (p : PartyM C E RealSpec α) (quiet : PartyBudget CheckQuery p 0)
    (step : Step C E RealSpec α)
    (run : step ∈ support (advance (treeLockstepLocalPrelude gate >>= fun _ => p).run)) :
    StepBudget CheckQuery step 0 := by
  unfold treeLockstepLocalPrelude at run
  rw [bind_assoc, advance_localStep_bind] at run
  rw [mem_support_bind_iff] at run
  obtain ⟨out, _, run⟩ := run
  cases out with
  | none =>
    simp only [failure_bind] at run
    subst step
    trivial
  | some u =>
    simp only [pure_bind] at run
    exact advance_stepBudget CheckQuery _ quiet step run

end QuietNetwork

section Boundary
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Transfer the literal first-pass world through the decoder's complete
start equality, then execute only quiet retained prefix continuations. -/
theorem boundary_pre_honest (limit : ℕ) (b : TreeCheckTailBoundary A)
    (parameter : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (first : ∀ r, r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (b.program K circuits settings))).run b.batch.world) →
        HonestCheckLog limit r.2.1.1 r.2.2)
    (o : TreeCheckTailCheckpoint A)
    (run : o ∈ support (b.pre prims K circuits settings D)) :
    HonestCheckLog limit o.2.1.1 o.2.2 := by
  let p := fun i => treeLockstepLocalPrelude (b.tail i) >>= fun _ =>
    treeSimCheckBatchPrefix K circuits settings (b.batch.ctx i) b.batch.jobs b.batch.initial
  let k := fun i data => treeSimCheckBatchFinish K circuits (b.batch.ctx i) b.batch.jobs
    b.batch.initial data >>= b.batch.k i
  have timed := treeSimCheckTimed_start D
    (depth (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) * settings.mode.rounds)
    p k (fun i => treeLockstep_localPrelude_timed _ _ _ (by
      simpa only [parameter i] using treeSimCheckBatchPrefix_timed K circuits settings
        (b.batch.ctx i) b.batch.jobs b.batch.initial))
  have same : (b.program K circuits settings) = fun i => p i >>= k i := by
    funext i
    simp only [TreeCheckTailBoundary.program, treeSimCheckBatchAudit_run_prefix, bind_assoc, p, k]
  unfold TreeCheckTailBoundary.pre executePhase at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨started, hs, run⟩ := run
  have firstRun : ((fun i => suspendStep (k i) (started.1 i)), started.2) ∈
      support ((simulateQ (treeSimLoggedWorld prims D)
        (startSteps worldRoles D (b.program K circuits settings))).run b.batch.world) := by
    rw [same, timed, simulateQ_map, StateT.run_map, support_map]
    exact ⟨started, hs, rfl⟩
  have honest := first _ firstRun
  apply rounds_honest prims D limit _ _ started.1 _ started.2 honest o run
  intro i
  have each := mem_support_sequenceFin_oc _ _ (treeCheck_logged_support prims D _ _ hs) i
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, mem_support_pure_iff] at each
    rw [each]
    trivial
  · simp only [if_neg hi, worldRoles] at each
    exact prelude_advance_quiet _ _ (batchPrefix_quiet K circuits settings _ _ _) _
      (treeSimCheck_support_free _ each)

end Boundary

theorem reached_honest (limit N : ℕ) (Z : Distinguisher C A.State TreeOutput)
    (start : TreeCheckWalkDef.Pending A)
    (honest : HonestCheckLog limit start.world.1.1 start.world.2)
    (disc : ∀ i, i ∉ D.1 → CheckDisc limit (N + 1) ∅ (start.program i).run)
    {m : ℕ} {q : TreeCheckWalkDef.Pending A}
    (reached : Reached prims D Z start m q) (below : m ≤ N) :
    HonestCheckLog limit q.world.1.1 q.world.2 := by
  induction reached with
  | start => exact honest
  | @next n fuel p q reached fuelLeft run ih =>
    apply next_honest prims D limit Z fuel p q (ih (by omega)) _ run
    intro i hi
    exact ((disc i hi).residual (Reached.residual prims D Z reached i hi) (by omega)).antitone (by omega)

section Actual
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (Z : Distinguisher C A.State TreeOutput)

/-- A decoded first-run hit occurs no later than the certified batch boundary. -/
theorem walk_hit_before (setup : C.Party → Option (PrssKeys C)) (j : ℕ)
    (first : j ≠ (firstChunks settings tree).length) (start : TreeCheckWalkDef.Pending A) (N : ℕ)
    (hits : ∀ q, Reached prims D Z start N q →
      (decode prims K D A circuits settings top tree x setup j q).isSome) :
    ∀ (fuel n : ℕ) (p : TreeCheckWalkDef.Pending A), Reached prims D Z start n p → p.fuel = fuel → n ≤ N →
      ∀ c, .inl c ∈ support (walk prims K D A circuits settings top tree x setup j Z fuel p) →
        ∃ m, m ≤ N ∧ Reached prims D Z start m c.1.1
  | fuel, n, p, reached, fuelLeft, below, c, run => by
    have same : ({p with fuel := fuel} : TreeCheckWalkDef.Pending A) = p := by
      cases p
      simp_all
    have missed : ¬ (decode prims K D A circuits settings top tree x setup j p).isSome → n < N := by
      intro miss
      rcases Nat.lt_or_eq_of_le below with lt | eq
      · exact lt
      · exact (miss (hits p (eq ▸ reached))).elim
    cases fuel with
    | zero =>
      simp only [walk, prepare_first prims K D A circuits settings top tree x setup j first, same,
        pure_bind] at run
      split_ifs at run with hit
      · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
        subst run
        exact ⟨n, below, reached⟩
      · simp only [support_map, Set.mem_image] at run
        obtain ⟨_, _, impossible⟩ := run
        cases impossible
    | succ fuel =>
      simp only [walk, prepare_first prims K D A circuits settings top tree x setup j first, same,
        pure_bind] at run
      split_ifs at run with hit
      · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
        subst run
        exact ⟨n, below, reached⟩
      · rw [mem_support_bind_iff] at run
        obtain ⟨outcome, nextRun, run⟩ := run
        cases outcome with
        | inr terminal => simp only [mem_support_pure_iff] at run; cases run
        | inl pending =>
          exact walk_hit_before setup j first start N hits fuel (n + 1) pending
            (.next reached fuelLeft nextRun) (next_fuel prims D A Z fuel p pending nextRun)
            (Nat.succ_le_of_lt (missed hit)) c run

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 8000 in
theorem walk_first_hit (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (dealt : DealtInputs D x) (j : ℕ) (first : j < (firstChunks settings tree).length)
    (c : Decoded (decode prims K D A circuits settings top tree x setup.1.2 j))
    (run : .inl c ∈ support (walk prims K D A circuits settings top tree x setup.1.2 j Z
      (TreeCheckWalkDef.initial K circuits settings top tree x setup).fuel
      (TreeCheckWalkDef.initial K circuits settings top tree x setup))) :
    ∃ m, m ≤ batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j ∧
      Reached prims D Z (TreeCheckWalkDef.initial K circuits settings top tree x setup) m c.1.1 := by
  have hits : ∀ q, Reached prims D Z (initial K circuits settings top tree x setup)
      (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j) q →
      (decode prims K D A circuits settings top tree x setup.1.2 j q).isSome := fun q reached =>
    walkState_first_decode prims K D A circuits settings top tree x Z setup dealt j first reached
  have bridge := walk_hit_before prims D K A circuits settings top tree x Z setup.1.2 j (Nat.ne_of_lt first)
    (initial K circuits settings top tree x setup)
    (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j) hits
    (initial K circuits settings top tree x setup).fuel 0
    (initial K circuits settings top tree x setup) .start rfl (Nat.zero_le _) c
  with_reducible exact bridge run


set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 8000 in
/-- The exact classifier at every supported first-run checkpoint of the
unchanged source walk, including checkpoints whose honest rows have aborted. -/
theorem sourceWalk_honest (z : Aux) (j : ℕ) (step : ℕ)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (dealt : DealtInputs D x) (first : j < (firstChunks settings tree).length)
    (hp : p ∈ support (treeSaltSetup prims D A x z))
    (c : Decoded (decode prims K D A circuits settings top tree x p.1.2 j))
    (o : TreeCheckTailCheckpoint A)
    (run : (.inl (c, o) : (Decoded (decode prims K D A circuits settings top tree x p.1.2 j) ×
        TreeCheckTailCheckpoint A) ⊕ TreeCheckTailResult A) ∈ support
      ((sourceWalk prims K D A circuits settings top tree x j Z step p).cut prims K circuits settings D Z).pre) :
    HonestCheckLog
      (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) j)
      o.2.1.1 o.2.2 := by
  let W := sourceWalk prims K D A circuits settings top tree x j Z step p
  let limit := lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) j
  have hc : .inl c ∈ support W.pre := by
    with_reducible exact index_support prims D Z K circuits settings W c o run
  have ho : o ∈ support ((W.boundary c).pre prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre
      (W := W) (prims := prims) (K := K) (circuits := circuits) (settings := settings)
      (D := D) (Z := Z) (c := c) (o := o) run)
  have hit : ∃ m, m ≤ batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j ∧
      Reached prims D Z (initial K circuits settings top tree x p) m c.1.1 := by
    with_reducible exact walk_first_hit prims D K A circuits settings top tree x Z p dealt j first c hc
  obtain ⟨m, below, reached⟩ := hit
  have initialDisc := initial_program_checkDisc K D circuits settings top tree x A p dealt
  have initialHonest : HonestCheckLog limit (initial K circuits settings top tree x p).world.1.1
      (initial K circuits settings top tree x p).world.2 := setup_honest prims D limit A x z p hp
  have honest := reached_honest prims D limit
    (batchStart circuits settings tree (x (refHolder D K.publicTerm)).parameter j) Z
    (initial K circuits settings top tree x p) initialHonest
    (fun i _ => initialDisc i j first) reached below
  have disc : ∀ i, i ∉ D.1 → CheckDisc limit 1 ∅ (c.1.1.program i).run := by
    intro i hi
    exact ((initialDisc i j first).residual (Reached.residual prims D Z reached i hi)
      (by omega)).antitone (by omega)
  have fits := decode_sound prims K D A circuits settings top tree x p.1.2 j c
  apply boundary_pre_honest prims D K circuits settings limit (W.boundary c) _ _ o ho
  · intro i
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    change (x i).parameter = (x (refHolder D K.publicTerm)).parameter
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl
  · intro r hr
    apply start_honest prims D limit c.1.1.program disc c.1.1.world honest r
    rw [fits.2.2]
    exact hr

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 8000 in
/-- The first-run classifier on the actual walk family. All source assumptions
come from `AtWalk`; the only checkpoint restriction is its first-run index. -/
theorem walkCheckpoint_honest (K : Constants C E) (circuits : Circuits) (settings : Settings) :
    AtWalk prims K circuits settings fun _ tree D _ x _ Z _ _ j _ W =>
      j.val < (firstChunks settings tree).length →
      ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
          HonestCheckLog
            (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter (firstChunks settings tree) j)
            o.2.1.1 o.2.2 := by
  intro _ top tree D A x z Z q dealt bounded small j p hp first c o run
  with_reducible exact (sourceWalk_honest prims D K A circuits settings top tree x Z
    z j _ p dealt first hp c o run)

end Actual

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckHonestLog.advance_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms advance_honest

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckHonestLog.walk_first_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms walk_first_hit

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckHonestLog.sourceWalk_honest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms sourceWalk_honest

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckHonestLog.walkCheckpoint_honest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms walkCheckpoint_honest


end TreeCheckHonestLog
end ThresholdLeanXmssSecurity
