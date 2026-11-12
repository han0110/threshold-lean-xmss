import ThresholdLeanXmssSecurity.Proof.TreeHashBudget
import ThresholdLeanXmssSecurity.Proof.TreeLockstepSegments
import ThresholdLeanXmssSecurity.Proof.KeygenKnown

/-!
# Honest hash covers across aborted batches

The actual digest round has two cases. With an accepting receiver, its query
pass costs at most two points per term. With no accepting receiver, its entire
round costs at most `(n + 1)` points per term and every continuation is stopped.
The saved opening is never invoked; the remaining network and distinguisher
add no honest points. Both cases fit the original per-batch allowance.

Region covers compose through retained-log cuts, excluding input PRF and
PRSS derivation queries that the model pays separately. The number of distinct
reached indices is bounded by `treeBatches`, independently of the selected
encoding. `treeHashBudget_from_cuts` gives exactly `treeSecrets - 2*prssKeyCount`
from a setup cover and covers of successive reached batches.

The setup cover applies to the actual logged phase from any incoming state,
including aborts: at most `n²` commitment inputs and `2*n²` opening/echo inputs.
Derivation queries are outside the region. The final echo adds no honest hash
entry. This fits the existing setup allowance and gives a cover from the empty
honest transcript after the actual common prefix, including unlogged padding.

`treeSimHashHonestBudget` in `TreeHashBudgetRun` connects these setup and batch
covers to the whole ceremony, with aligned coin tags and labels, zero
nonholder copies, and reached-index provenance. It establishes the exact
`TreeSimHashHonestBudget`, including retained queries from aborted prefixes,
without a final-output premise.

The pinned and working leanVM libraries were searched for query-budget and
abort laws. Synchronous check and opening boundaries are specific to this
protocol; the existing actual round factorization and covers are reused.
The setup uses `keygenIsQueryBoundP_sequenceFin_sum`, the exact setup expansion,
and `finish_facts` instead of duplicating the private echo proof.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- Only inputs in the budget domain are charged. Input PRF calls and PRSS
key derivation in the gaps between covered phases are excluded by the model. -/
def TreeHashBudgetRegionCover (S : Finset (Query C)) (before after : TreeSimLog C) : Prop :=
  ∀ q h, TreeSimHashBudgetDomain q → freeEntry q h ∈ after →
    freeEntry q h ∈ before ∨ q ∈ S

theorem TreeHashCover.region {S : Finset (Query C)} {before after : TreeSimLog C}
    (h : TreeHashCover S before after) : TreeHashBudgetRegionCover S before after :=
  fun q v _ hv => h q v hv

theorem TreeHashBudgetRegionCover.refl (S : Finset (Query C)) (log : TreeSimLog C) :
    TreeHashBudgetRegionCover S log log := fun _ _ _ h => Or.inl h

theorem TreeHashBudgetRegionCover.trans {S : Finset (Query C)} {a b c : TreeSimLog C}
    (first : TreeHashBudgetRegionCover S a b) (second : TreeHashBudgetRegionCover S b c) :
    TreeHashBudgetRegionCover S a c :=
  fun q h domain mem => (second q h domain mem).elim (first q h domain) Or.inr

theorem TreeHashBudgetRegionCover.union_trans {S T : Finset (Query C)} {a b c : TreeSimLog C}
    (first : TreeHashBudgetRegionCover S a b) (second : TreeHashBudgetRegionCover T b c) :
    TreeHashBudgetRegionCover (S ∪ T) a c := by
  intro q h domain mem
  rcases second q h domain mem with old | added
  · exact (first q h domain old).imp id (Finset.mem_union_left T)
  · exact Or.inr (Finset.mem_union_right S added)

theorem TreeHashBudgetRegionCover.from_empty {S : Finset (Query C)} {log : TreeSimLog C}
    (h : TreeHashBudgetRegionCover S [] log) (q : Query C) (v : HashOutput)
    (domain : TreeSimHashBudgetDomain q) (mem : freeEntry q v ∈ log) : q ∈ S := by
  rcases h q v domain mem with impossible | hs
  · cases impossible
  · exact hs

/-- Rejecting every saved result invokes no continuation and makes no query. -/
theorem treeHashBudget_resume_none {α β : Type}
    (k : C.Party → β → PartyM C E RealSpec α) :
    treeSimResumeAll k (fun _ => none) = pure (fun _ => .done none) := by
  simp only [treeSimResumeAll, treeSimResume, sequenceFin_pure, free_pure]

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (D : C.Coalition) (K : Constants C E)

/-- A syntactic zero bound outside the cover proves an actual log cover,
while allowing the PRF and derivation queries outside the budget domain. -/
theorem treeHashBudget_free_region_cover {α : Type} (S : Finset (Query C))
    (p : OracleComp (LocalSpec C) α)
    (bound : IsQueryBoundP p (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S)) 0)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run s)) :
    TreeHashBudgetRegionCover S s.2 r.2.2 := by
  apply logged_free_inv prims D (FreeHashIn (fun q => TreeSimHashBudgetDomain q ∧ q ∉ S))
    (fun t => TreeHashBudgetRegionCover S s.2 t.2) ?_ p bound s (.refl S s.2) r run
  intro t ht a ha b hb q h domain mem
  rw [logged_step_log prims D _ a b hb, List.mem_append, List.mem_singleton] at mem
  rcases mem with old | added
  · exact ha q h domain old
  · apply Or.inr
    by_contra outside
    apply ht ⟨q, ⟨domain, outside⟩, ?_⟩
    have he := congrArg Sigma.fst added
    simp only [Sum.inr.injEq] at he
    exact he.symm

/-- After an all-rejected check, every remaining network round is inert.
The pending opening continuation is never invoked. -/
theorem treeHashBudget_rejected_suffix {α : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (kind : TreeSimCheckKind C E)
    (sent : C.Party → Mail C E) (k : C.Party → PartyM C E RealSpec α)
    (reject : ∀ i, treeSimCheckResult K D live kind sent i = none) (fuel : ℕ) :
    (do
      let steps ← treeSimResumeAll (fun i (_ : Unit) => k i)
        (treeSimCheckResult K D live kind sent)
      executeRounds worldRoles D A noFunctionality fuel state steps) =
      pure (state, fun _ => none) := by
  rw [show treeSimCheckResult K D live kind sent = (fun _ => none) from funext reject,
    treeHashBudget_resume_none, pure_bind]
  exact executeRounds_all_done worldRoles D A noFunctionality fuel state _ (fun _ _ => trivial)

/-- A stopped network followed by its real distinguisher adds no honest
hash points. The distinguisher's calls retain their adversarial designation. -/
theorem treeHashBudget_stopped_finish {α β : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (fuel : ℕ)
    (Z : (A.State × (C.Party → Option α)) → OracleComp (LocalSpec C) β)
    (s : TreeSimState C) (r : β × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (do
      let out ← executeRounds worldRoles D A noFunctionality fuel state
        (fun _ => (Step.done none : Step C E RealSpec α))
      worldRoles.adversary (Z out))).run s)) :
    TreeHashCover ∅ s.2 r.2.2 := by
  rw [executeRounds_all_done worldRoles D A noFunctionality fuel state
    (fun _ => (Step.done none : Step C E RealSpec α)) (fun _ _ => trivial), pure_bind] at run
  exact treeHashBudget_adversary_cover prims D ∅ _ s r run

include K in
/-- On the actual digest round, either its query pass has the cheap surviving
cover, or the complete round has the terminal cover and all continuations have
stopped. The adversarial reply and both caches remain those of the same run. -/
theorem treeHashBudget_digest_dichotomy {α : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (live : C.Party → Bool) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (salts : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C) (before : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (run : before ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
      (fun i (_ : Unit) => (compareDigests (ctx i) (salts i)).run (st i) >>= k i)
      (fun i => if i ∈ D.1 then none else if live i then some () else none))).run s))
    (r : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) × TreeSimState C)
    (round : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (stepRound worldRoles D A noFunctionality state before.1)).run before.2))
    (final : r.2.2 ⊆ log) :
    (∃ S : Finset (Query C), S.card ≤ 2 * termCount C ∧ TreeHashCover S s.2 before.2.2) ∨
    (r.1.2.1 = (fun _ => .done none) ∧ ∃ S : Finset (Query C),
      S.card ≤ (C.n + 1) * termCount C ∧ TreeHashCover S s.2 r.2.2) := by
  have future : before.2.2 ⊆ log :=
    (treeSimLoggedWorld_prefix prims D _ before.2 r round).subset.trans final
  obtain ⟨ds, waiting, survives⟩ := treeHashBudget_digest_surviving prims D K log cache coherent good
    live ctx self salts st k s before run future
  rw [waiting, treeSim_check_round_factor] at round
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at round
  obtain ⟨adv, hadv, next, hnext, rfl⟩ := round
  by_cases accepted : ∃ i, treeSimCheckResult K D live (.digests ds) adv.1.2 i = some ()
  · obtain ⟨i, hi⟩ := accepted
    exact Or.inl (survives adv.1.2 i hi)
  · have reject : treeSimCheckResult K D live (.digests ds) adv.1.2 = (fun _ => none) := by
      funext i
      cases h : treeSimCheckResult K D live (.digests ds) adv.1.2 i with
      | none => rfl
      | some u => cases u; exact (accepted ⟨i, h⟩).elim
    rw [reject, treeHashBudget_resume_none] at hnext
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hnext
    subst next
    obtain ⟨S, size, cover⟩ := treeHashBudget_digest_terminal prims D K log cache coherent
      live ctx self salts st k s before run future
    refine Or.inr ⟨rfl, S, size, ?_⟩
    exact cover.trans (treeHashBudget_adversary_cover prims D S _ before.2 adv hadv)


/-- Coin, surviving-digest, and opening covers fit the existing per-batch
allowance. A term pays for the one zero-copy input shared by all nonholders. -/
theorem treeHashBudget_surviving_batch
    (coins : ℕ) (coinSet digestSet openSet : Finset (Query C))
    (a b c d : TreeSimLog C)
    (coinSize : coinSet.card ≤ coins) (digestSize : digestSet.card ≤ 2 * termCount C)
    (openSize : openSet.card ≤ C.n * termCount C + 1)
    (coinCover : TreeHashCover coinSet a b) (digestCover : TreeHashCover digestSet b c)
    (openCover : TreeHashCover openSet c d) :
    ∃ S : Finset (Query C), S.card ≤ 3 * termCount C + C.n * termCount C + coins ∧
      TreeHashCover S a d := by
  refine ⟨(coinSet ∪ digestSet) ∪ openSet, ?_,
    (coinCover.union_trans digestCover).union_trans openCover⟩
  have first := Finset.card_union_le coinSet digestSet
  have second := Finset.card_union_le (coinSet ∪ digestSet) openSet
  have nonempty := treeSimHash_parties_le_terms (C := C)
  have positive := C.one_le_t
  unfold Committee.n at nonempty
  omega

/-- A terminal digest uses the same per-batch allowance with no opening charge. -/
theorem treeHashBudget_terminal_batch
    (coins : ℕ) (coinSet digestSet : Finset (Query C)) (a b c : TreeSimLog C)
    (coinSize : coinSet.card ≤ coins)
    (digestSize : digestSet.card ≤ (C.n + 1) * termCount C)
    (coinCover : TreeHashCover coinSet a b) (digestCover : TreeHashCover digestSet b c) :
    ∃ S : Finset (Query C), S.card ≤ 3 * termCount C + C.n * termCount C + coins ∧
      TreeHashCover S a c := by
  refine ⟨coinSet ∪ digestSet, ?_, coinCover.union_trans digestCover⟩
  have hc := Finset.card_union_le coinSet digestSet
  rw [Nat.add_mul, one_mul] at digestSize
  omega

/-- The number of distinct reached batch indices is independent of the
selected encoding. The premise must come from the actual prefix schedule. -/
theorem treeHashBudget_reached_count (settings : Settings) (enc : Encoding) (tree : Tree)
    (reached : Finset ℕ)
    (indices : ∀ k ∈ reached, k < (lockstepChunks settings enc tree).length) :
    reached.card ≤ treeBatches settings tree := by
  rw [← lockstepChunks_length settings enc tree]
  have sub : reached ⊆ Finset.range (lockstepChunks settings enc tree).length :=
    fun k hk => Finset.mem_range.mpr (indices k hk)
  exact (Finset.card_le_card sub).trans_eq (Finset.card_range _)

/-- Covers compose over retained-log cuts; no final output or non-abort
premise is used. Repeated points across cuts count only once. -/
theorem treeHashBudget_cover_chain (logs : ℕ → TreeSimLog C)
    (sets : ℕ → Finset (Query C)) (m : ℕ)
    (covers : ∀ k < m, TreeHashBudgetRegionCover (sets k) (logs k) (logs (k + 1))) :
    TreeHashBudgetRegionCover ((Finset.range m).biUnion sets) (logs 0) (logs m) := by
  induction m with
  | zero => exact .refl _ _
  | succ m ih =>
    have h := (ih (fun k hk => covers k (by omega))).union_trans (covers m (by omega))
    simpa only [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm] using h

/-- The original honest allowance is precisely setup plus one fixed allowance
for every possible batch; the derived/stream-key points remain paid elsewhere. -/
theorem treeHashBudget_capacity (circuits : Circuits) (settings : Settings) (tree : Tree) :
    treeSecrets circuits settings C tree - 2 * prssKeyCount C =
      C.n * (termCount C + C.n) + C.n ^ 2 + treeBatches settings tree *
        (3 * termCount C + C.n * termCount C +
          maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2) := by
  simp only [treeSecrets, prssKeyCount]
  omega

/-- Once setup and the actual successive batch cuts have covers, their union
meets the original numerical target. The last cut may be a terminal digest. -/
theorem treeHashBudget_from_cuts (circuits : Circuits) (settings : Settings) (tree : Tree)
    (logs : ℕ → TreeSimLog C) (setup : Finset (Query C))
    (sets : ℕ → Finset (Query C)) (m : ℕ)
    (first : TreeHashBudgetRegionCover setup [] (logs 0))
    (setupSize : setup.card ≤ C.n * (termCount C + C.n) + C.n ^ 2)
    (reached : m ≤ treeBatches settings tree)
    (sizes : ∀ k < m, (sets k).card ≤
      3 * termCount C + C.n * termCount C +
        maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2)
    (covers : ∀ k < m, TreeHashBudgetRegionCover (sets k) (logs k) (logs (k + 1))) :
    ∃ S : Finset (Query C), S.card ≤ treeSecrets circuits settings C tree - 2 * prssKeyCount C ∧
      TreeHashBudgetRegionCover S [] (logs m) := by
  refine ⟨setup ∪ (Finset.range m).biUnion sets, ?_,
    first.union_trans (treeHashBudget_cover_chain logs sets m covers)⟩
  rw [treeHashBudget_capacity]
  have hc := Finset.card_union_le setup ((Finset.range m).biUnion sets)
  have hb := Finset.card_biUnion_le (s := Finset.range m) (t := sets)
  have hs := Finset.sum_le_sum (s := Finset.range m)
    (fun k hk => sizes k (Finset.mem_range.mp hk))
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hs
  have hm := Nat.mul_le_mul_right
    (3 * termCount C + C.n * termCount C +
      maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2) reached
  omega

/-! ## The actual setup -/

/-- A bound on the local honest queries gives a finite cover of the newly
logged budget-region inputs, retaining any incoming transcript. -/
theorem treeHashBudget_free_count_cover {α : Type}
    (p : OracleComp (LocalSpec C) α) (n : ℕ)
    (bound : IsQueryBoundP p (FreeHashIn TreeSimHashBudgetDomain) n)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run s)) :
    ∃ S : Finset (Query C), S.card ≤ n ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  let I : QueryImpl (SimulatorSpec C) (StateT (TreeSimState C) ProbComp) :=
    fun t => treeSimLoggedWorld prims D (.inl t)
  let impl : QueryImpl (LocalSpec C) (StateT (TreeSimState C) ProbComp) :=
    fun t => treeSimLoggedWorld prims D (.inr t)
  have split : treeSimLoggedWorld prims D = I + impl := by
    funext t
    cases t <;> rfl
  rw [split, simulateQ_free] at run
  induction p using OracleComp.inductionOn generalizing n s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact ⟨∅, by simp, .refl _ _⟩
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at bound
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at run
    obtain ⟨mid, hmid, run⟩ := run
    obtain ⟨S, size, cover⟩ := ih mid.1 _ (bound.2 mid.1) mid.2 r run
    change mid ∈ support ((treeSimLoggedWorld prims D (.inr t)).run s) at hmid
    by_cases counted : FreeHashIn TreeSimHashBudgetDomain t
    · have positive := bound.1.resolve_left (not_not.mpr counted)
      simp only [if_pos counted] at size
      obtain ⟨q, domain, rfl⟩ := counted
      have step : TreeHashBudgetRegionCover {q} s.2 mid.2.2 := by
        intro a h ha mem
        rw [logged_step_log prims D (.inr (.inr (.inl q))) s mid hmid,
          List.mem_append, List.mem_singleton] at mem
        rcases mem with old | added
        · exact Or.inl old
        · have eq := congrArg Sigma.fst added
          simp only [Sum.inr.injEq, Sum.inl.injEq] at eq
          exact Or.inr (Finset.mem_singleton.mpr eq)
      refine ⟨{q} ∪ S, ?_, step.union_trans cover⟩
      have card := Finset.card_union_le ({q} : Finset (Query C)) S
      simp only [Finset.card_singleton] at card
      omega
    · simp only [if_neg counted] at size
      refine ⟨S, size, ?_⟩
      intro q h domain mem
      rcases cover q h domain mem with old | added
      · rw [logged_step_log prims D (.inr t) s mid hmid,
          List.mem_append, List.mem_singleton] at old
        rcases old with old | new
        · exact Or.inl old
        · have eq := congrArg Sigma.fst new
          simp only [Sum.inr.injEq] at eq
          exact (counted ⟨q, domain, eq.symm⟩).elim
      · exact Or.inr added

private theorem setup_hash_pass (f : C.Party → Query C) :
    IsQueryBoundP (liftComp (C.parties.mapM fun j => hashQuery (f j)) (LocalSpec C))
      (FreeHashIn TreeSimHashBudgetDomain) C.n := by
  apply TreeSimHashCount.ro_bound
  simpa only [Committee.parties, List.length_finRange, Nat.mul_one] using
    queryBound_mapM (fun t => FreeHashIn TreeSimHashBudgetDomain (.inr t))
      (fun j => hashQuery (f j)) 1 C.parties (fun j _ =>
        IsQueryBoundP.of_imp (fun _ _ => trivial) (hashQuery_queryBound (f j)))

/-- The commitment pass makes at most `n²` honest budget-region queries. -/
theorem treeHashBudget_setup_initial_count :
    IsQueryBoundP (prssInitialData D) (FreeHashIn TreeSimHashBudgetDomain) (C.n ^ 2) := by
  unfold prssInitialData
  have h := keygenIsQueryBoundP_sequenceFin_sum (p := FreeHashIn TreeSimHashBudgetDomain)
    (fun i : C.Party => if i ∈ D.1 then pure (⟨0, fun _ => 0, fun _ => 0⟩, []) else do
      let own ← liftComp (sampleParts : ProbComp (Parts C)) (LocalSpec C)
      let commitments ← liftComp (C.parties.mapM fun j =>
        hashQuery (.commit .prss i j (revealTo .prss own i j))) (LocalSpec C)
      pure (own, commitments)) (fun _ => C.n) (fun i => by
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · refine (isQueryBoundP_bind (prob_freeHashIn_zero _ _) (m := C.n)
            fun own _ => ?_).mono (by omega)
          exact (isQueryBoundP_bind (setup_hash_pass _) fun _ _ =>
            isQueryBoundP_pure _ _ 0).mono (by omega))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, pow_two] using h

/-- Opening checks and echo hashes make at most `2*n²` region queries. PRSS
derivations are outside this domain, including on partially aborted setup runs. -/
theorem treeHashBudget_setup_reveal_count (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) :
    IsQueryBoundP (prssRevealRows D active parts committed sent)
      (FreeHashIn TreeSimHashBudgetDomain) (2 * C.n ^ 2) := by
  unfold prssRevealRows
  have localBound (i : C.Party) :
      IsQueryBoundP (prssRevealData i (parts i) (committed i)
        (prssRevealInbox D active parts sent i)) (FreeHashIn TreeSimHashBudgetDomain) (2 * C.n) := by
    unfold prssRevealData
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · unfold prssPostRevealData
      refine (isQueryBoundP_bind (setup_hash_pass _) (m := C.n) fun opens _ => ?_).mono (by omega)
      split_ifs
      · refine (isQueryBoundP_bind (derive_freeHashIn_zero _
          (fun q hq => ⟨hq, treeSimHashBudgetDomain_not_fixed q hq⟩) _ _ _) (m := C.n)
          fun keys _ => ?_).mono
          (by omega)
        exact (isQueryBoundP_bind (setup_hash_pass _) fun _ _ =>
          isQueryBoundP_pure _ _ 0).mono (by omega)
      · exact isQueryBoundP_pure _ _ _
  have h := keygenIsQueryBoundP_sequenceFin_sum (p := FreeHashIn TreeSimHashBudgetDomain)
    (fun i : C.Party => if i ∈ D.1 then pure none else if active i then
      prssRevealData i (parts i) (committed i) (prssRevealInbox D active parts sent i)
      else pure none) (fun _ => 2 * C.n) (fun i => by
        split_ifs
        · exact isQueryBoundP_pure _ _ _
        · exact localBound i
        · exact isQueryBoundP_pure _ _ _)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, pow_two,
    ← Nat.mul_assoc, Nat.mul_comm C.n 2] using h

/-- The complete actual setup, including both abort branches, adds at most
three `n²` passes of honest region inputs. Adversarial queries do not enter the
cover, derivations are outside the region, and the echo pass makes no new hash
call. No collision or successful-output hypothesis is needed. -/
theorem treeHashBudget_setup_cover
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : r ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality
      setupRounds state (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ 3 * C.n ^ 2 ∧ TreeHashBudgetRegionCover S s.2 r.2.2 := by
  rw [treeSimRealRoles, ← simulateQ_executePhase] at run
  change r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (executePhase worldRoles D A noFunctionality (1 + 2) state
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))))).run s) at run
  rw [executePhase_prssSetup_prefix] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨data, hdata, adv, hadv, run⟩ := run
  obtain ⟨initial, initialSize, initialCover⟩ := treeHashBudget_free_count_cover prims D
    (prssInitialData D) _ (treeHashBudget_setup_initial_count D) s data hdata
  have committed : TreeHashBudgetRegionCover initial s.2 adv.2.2 :=
    initialCover.trans (treeHashBudget_adversary_cover prims D initial _ data.2 adv hadv).region
  split_ifs at run with aborted
  · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact ⟨initial, by omega, committed⟩
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
    obtain ⟨adv', hadv', rows, hrows, finish⟩ := run
    have revealed : TreeHashBudgetRegionCover initial s.2 adv'.2.2 :=
      committed.trans (treeHashBudget_adversary_cover prims D initial _ adv.2 adv' hadv').region
    obtain ⟨checked, checkedSize, checkedCover⟩ := treeHashBudget_free_count_cover prims D
      _ _ (treeHashBudget_setup_reveal_count D _ _ _ _) adv'.2 rows hrows
    refine ⟨initial ∪ checked, ?_, ?_⟩
    · have card := Finset.card_union_le initial checked
      omega
    · intro q h domain mem
      exact (revealed.union_trans checkedCover) q h domain
        ((finish_facts D prims A adv'.1.1 rows.1 rows.2 r finish).2 q h mem)

/-- The proved setup cover fits the existing setup allowance. -/
theorem treeHashBudget_setup_capacity
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : r ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality
      setupRounds state (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ C.n * (termCount C + C.n) + C.n ^ 2 ∧
      TreeHashBudgetRegionCover S s.2 r.2.2 := by
  obtain ⟨S, size, cover⟩ := treeHashBudget_setup_cover prims D A state s r run
  exact ⟨S, size.trans treeSimHash_setup_capacity, cover⟩

/-- The setup cover starts at the empty honest transcript after the actual
common prefix. An unlogged padding may change the incoming hash cache; it
does not add honest entries to the retained transcript. -/
theorem treeHashBudget_setup_from_prefix (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (z : Aux) (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (hp : p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z))
    (hash : HashCache C)
    (r : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (run : r ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality
      setupRounds p.2.1 (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run
        ((hash, p.2.2.1.2), p.2.2.2))) :
    ∃ S : Finset (Query C), S.card ≤ C.n * (termCount C + C.n) + C.n ^ 2 ∧
      TreeHashBudgetRegionCover S [] r.2.2 := by
  obtain ⟨S, size, cover⟩ := treeHashBudget_setup_capacity prims D A p.2.1 _ r run
  refine ⟨S, size, ?_⟩
  apply TreeHashBudgetRegionCover.trans (b := p.2.2.2) _ cover
  unfold treeSimCommonPrefix at hp
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hp
  obtain ⟨dealt, _, start, hstart, rfl⟩ := hp
  exact (treeHashBudget_adversary_cover prims D S _ ((dealt.2, ∅), []) start hstart).region

/-- The exact whole-ceremony target, unchanged. The setup cover is proved;
its connection to the whole-run batch cuts, synchronized Coin labels,
nonholder zero copies and batch covers still has to instantiate the assembly. -/
def TreeHashBudgetFinalRemaining (circuits : Circuits) (settings : Settings) : Prop :=
  TreeSimHashHonestBudget prims K circuits settings


/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_digest_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_digest_dichotomy

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_rejected_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_rejected_suffix

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_stopped_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_stopped_finish

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_free_region_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_free_region_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_reached_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_reached_count

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_from_cuts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_from_cuts

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_free_count_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_free_count_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_setup_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_setup_cover

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_setup_capacity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_setup_capacity

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_setup_from_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_setup_from_prefix

end ThresholdLeanXmssSecurity
