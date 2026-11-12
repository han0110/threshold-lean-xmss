import ThresholdLeanXmssSecurity.Proof.TreeSimHashFinish
import ThresholdLeanXmssSecurity.Proof.TreeCheckGuess
import ThresholdLeanXmssSecurity.Proof.TreeLockstepOpened

/-!
# Honest hash points in the retained tree transcript

The local covers in `TreeSimHash` must cover the actual query log, including
queries issued before an abort. This file transfers those covers through the
logged world. Both passes of a synchronized replicated opening together use
at most `n * termCount + 1` points, even if it fails. A terminal digest phase
uses at most `(n + 1) * termCount`; a phase with an accepting receiver uses at
most `2 * termCount`. Accepted Coin values at one tag and label share one key.

The whole-ceremony interface is `TreeSimHashHonestBudget`.
A whole-run assembly must split the actual retained log at synchronized
setup and batch boundaries, bound the number of reached batches, and supply
common Coin tags/labels and zero nonholder copies there. In particular, a
terminal digest batch must not also be charged for a later opening.
Completed output records alone cannot establish
this obligation, since an aborted execution retains its earlier queries.

The pinned and current leanVM query-log and `OnlyQueries` lemmas were searched.
The dependent world interface here uses the existing `logged_free_inv` and
`logged_adversary_inv`, and the threshold-specific covers of `TreeSimHash`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- Every newly logged honest hash input belongs to the indicated finite set.
The incoming transcript is kept, so this composes across aborted phases. -/
def TreeHashCover (S : Finset (Query C)) (before after : TreeSimLog C) : Prop :=
  ∀ q h, freeEntry q h ∈ after → freeEntry q h ∈ before ∨ q ∈ S

theorem TreeHashCover.refl (S : Finset (Query C)) (log : TreeSimLog C) :
    TreeHashCover S log log := fun _ _ h => Or.inl h

theorem TreeHashCover.trans {S : Finset (Query C)} {a b c : TreeSimLog C}
    (hab : TreeHashCover S a b) (hbc : TreeHashCover S b c) : TreeHashCover S a c := by
  intro q h hc
  exact (hbc q h hc).elim (hab q h) Or.inr

theorem TreeHashCover.mono {S T : Finset (Query C)} {a b : TreeSimLog C}
    (h : TreeHashCover S a b) (hst : S ⊆ T) : TreeHashCover T a b :=
  fun q v hv => (h q v hv).imp id (fun hq => hst hq)

theorem TreeHashCover.union_trans {S T : Finset (Query C)} {a b c : TreeSimLog C}
    (hab : TreeHashCover S a b) (hbc : TreeHashCover T b c) :
    TreeHashCover (S ∪ T) a c :=
  (hab.mono Finset.subset_union_left).trans (hbc.mono Finset.subset_union_right)

variable (prims : Primitives) (D : C.Coalition)

/-- A zero bound outside a finite cover controls the actual retained log. -/
theorem treeHashBudget_free_cover {α : Type} (S : Finset (Query C))
    (p : OracleComp (LocalSpec C) α)
    (bound : IsQueryBoundP p (FreeHashIn (fun q => q ∉ S)) 0)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free p)).run s)) :
    TreeHashCover S s.2 r.2.2 := by
  apply logged_free_inv prims D (FreeHashIn (fun q => q ∉ S))
    (fun t => TreeHashCover S s.2 t.2) ?_ p bound s (.refl S s.2) r run
  intro t ht a ha b hb q h hmem
  rw [logged_step_log prims D _ a b hb, List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | hmem
  · exact ha q h hmem
  · apply Or.inr
    by_contra hn
    apply ht ⟨q, hn, ?_⟩
    have he := congrArg Sigma.fst hmem
    simp only [Sum.inr.injEq] at he
    exact he.symm

/-- Adversarial calls cannot add an honest query-log entry. -/
theorem treeHashBudget_adversary_cover {α : Type} (S : Finset (Query C))
    (p : OracleComp (LocalSpec C) α) (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (worldRoles.adversary p)).run s)) : TreeHashCover S s.2 r.2.2 := by
  apply logged_adversary_inv prims D (fun t => TreeHashCover S s.2 t.2)
    ?_ p s (.refl S s.2) r run
  intro t a ha b hb q h hmem
  rw [logged_step_log prims D _ a b hb, List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hmem | hmem
  · exact ha q h hmem
  · cases hmem

/-- A cover can be checked against a later transcript while traversing the
actual joint execution, rather than arbitrary independent party replays. -/
theorem treeHashBudget_sequence_cover {α : Type} (S : Finset (Query C)) (log : TreeSimLog C) :
    ∀ {n : ℕ} (f : Fin n → OracleComp (WorldSpec C) α),
      (∀ i s r, r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (f i)).run s) →
        r.2.2 ⊆ log → TreeHashCover S s.2 r.2.2) →
      ∀ s r, r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (Concrete.sequenceFin f)).run s) → r.2.2 ⊆ log → TreeHashCover S s.2 r.2.2
  | 0, f, step, s, r, run, final => by
    simp only [Concrete.sequenceFin, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at run
    subst r
    exact .refl S s.2
  | n + 1, f, step, s, r, run, final => by
    simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at run
    obtain ⟨a, ha, tail, ht, rfl⟩ := run
    have grows := (treeSimLoggedWorld_prefix prims D _ a.2 tail ht).subset
    exact (step 0 s a ha (grows.trans final)).trans
      (treeHashBudget_sequence_cover S log (fun i : Fin n => f i.succ)
        (fun i => step i.succ) a.2 tail ht final)

theorem treeHashBudget_hash_cover (S : Finset (Query C)) (q : Query C) (hq : q ∈ S)
    (s : TreeSimState C) (r : HashOutput × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (hashQuery q) (LocalSpec C)))).run s)) :
    TreeHashCover S s.2 r.2.2 := by
  apply treeHashBudget_free_cover prims D S _ ?_ s r run
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query
    (spec := LocalSpec C) (.inr (.inl q)))) _ 0
  rw [isQueryBoundP_query_iff]
  rintro ⟨q', hq', he⟩
  simp only [Sum.inr.injEq, Sum.inl.injEq] at he
  exact (hq' (he ▸ hq)).elim

/-- Cover one digest using its actual history answer in the later transcript. -/
theorem treeHashBudget_oneDigest_cover (S : Finset (Query C)) (log : TreeSimLog C)
    (salt history : List Bit) (inner : HashOutput)
    (historyAnswer : ∀ h, TreeSimHashAnswer log (.history history) h → h = inner)
    (points : Query.history (C := C) history ∈ S ∧ Query.digest salt inner ∈ S)
    (s : TreeSimState C) (r : HashOutput × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (oneDigestQuery (C := C) salt history) (LocalSpec C)))).run s))
    (final : r.2.2 ⊆ log) : TreeHashCover S s.2 r.2.2 := by
  simp only [oneDigestQuery, liftComp_bind, free_bind, simulateQ_bind,
    StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨a, ha, hr⟩ := run
  have grows := (treeSimLoggedWorld_prefix prims D _ a.2 r hr).subset
  have answer := treeSetup_hash_logged prims D (.history history) s a ha
  have eq := historyAnswer a.1 (answer.imp
    (fun h => final (grows h)) (fun h => final (grows h)))
  exact (treeHashBudget_hash_cover prims D S _ points.1 s a ha).trans
    (treeHashBudget_hash_cover prims D S _ (eq ▸ points.2) a.2 r hr)

/-- Cover every query issued by a digest traversal, including before failure. -/
theorem treeHashBudget_digestQueries_cover (S : Finset (Query C)) (log : TreeSimLog C)
    (i : C.Party) (salts : Shares C Bit) (history : C.Term → List Bit)
    (inner : C.Term → HashOutput)
    (historyAnswer : ∀ T h, TreeSimHashAnswer log (.history (history T)) h → h = inner T)
    (points : ∀ T, i ∈ C.holders T → Query.history (C := C) (history T) ∈ S ∧
      Query.digest (vector 256 (salts T)) (inner T) ∈ S)
    (terms : List C.Term) (s : TreeSimState C) (r : List HashOutput × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free (liftComp
      (terms.mapM fun T => if i ∈ C.holders T then
        oneDigestQuery (C := C) (vector 256 (salts T)) (history T) else pure 0)
      (LocalSpec C)))).run s))
    (final : r.2.2 ⊆ log) : TreeHashCover S s.2 r.2.2 := by
  induction terms generalizing s r with
  | nil =>
    simp only [List.mapM_nil, liftComp_pure, free_pure, simulateQ_pure,
      StateT.run_pure, mem_support_pure_iff] at run
    subst r
    exact .refl S s.2
  | cons T terms ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, free_bind, free_pure,
      simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, mem_support_pure_iff] at run
    obtain ⟨a, ha, tail, ht, rfl⟩ := run
    have grows := (treeSimLoggedWorld_prefix prims D _ a.2 tail ht).subset
    have first : TreeHashCover S s.2 a.2.2 := by
      by_cases held : i ∈ C.holders T
      · simp only [if_pos held] at ha
        exact treeHashBudget_oneDigest_cover prims D S log _ _ (inner T)
          (historyAnswer T) (points T held) s a ha (grows.trans final)
      · simp only [if_neg held, liftComp_pure, free_pure, simulateQ_pure,
          StateT.run_pure, mem_support_pure_iff] at ha
        subst a
        exact .refl S s.2
    exact first.trans (ih a.2 tail ht final)

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

include K in
/-- The cover includes every issued digest input, even when no operator ever
returns a completed batch record. The cache and log are from one later state. -/
theorem treeHashBudget_digest_partial_cover {α : Type} (S : Finset (Query C))
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (live : C.Party → Bool) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (salts : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (points : ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T →
      Query.history (C := C) ((st i).history T) ∈ S ∧
      Query.digest (vector 256 (salts i T))
        ((cache (.history ((st i).history T))).getD 0) ∈ S)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
      (fun i (_ : Unit) => (compareDigests (ctx i) (salts i)).run (st i) >>= k i)
      (fun i => if i ∈ D.1 then none else if live i then some () else none))).run s))
    (final : r.2.2 ⊆ log) : TreeHashCover S s.2 r.2.2 := by
  unfold treeSimResumeAll at run
  rw [free_sequenceFin] at run
  apply treeHashBudget_sequence_cover prims D S log _ ?_ s r run final
  intro i a b hb future
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure,
      StateT.run_pure, mem_support_pure_iff] at hb
    subst b
    exact .refl S a.2
  · simp only [if_neg hi] at hb
    by_cases hl : live i = true
    · simp only [if_pos hl, treeSimResume] at hb
      change b ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.honest (advance (((compareDigests (ctx i) (salts i)).run (st i)
          >>= k i).run)))).run a) at hb
      rw [treeSim_digest_entry (K := K), self i hi] at hb
      simp only [simulateQ_map, StateT.run_map, support_map] at hb
      obtain ⟨v, hv, rfl⟩ := hb
      apply treeHashBudget_digestQueries_cover prims D S log i (salts i) (st i).history
        (fun T => (cache (.history ((st i).history T))).getD 0) ?_
        (points i hi hl) C.terms a v hv future
      intro T h hh
      rw [coherent (.history ((st i).history T)) h trivial hh]
      rfl
    · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure,
        StateT.run_pure, mem_support_pure_iff] at hb
      subst b
      exact .refl S a.2

include K in
/-- A possibly terminal digest phase has at most two points per holder. -/
theorem treeHashBudget_digest_terminal {α : Type}
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (live : C.Party → Bool) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (salts : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
      (fun i (_ : Unit) => (compareDigests (ctx i) (salts i)).run (st i) >>= k i)
      (fun i => if i ∈ D.1 then none else if live i then some () else none))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ S : Finset (Query C), S.card ≤ (C.n + 1) * termCount C ∧
      TreeHashCover S s.2 r.2.2 := by
  obtain ⟨S, size, points⟩ := treeSimHash_digest_terminal_points
    (fun i T => vector 256 (salts i T)) (fun i => (st i).history)
    (fun i T => (cache (.history ((st i).history T))).getD 0)
  exact ⟨S, size, treeHashBudget_digest_partial_cover prims D K S log cache coherent
    live ctx self salts st (fun i _ _ => points i) k s r run final⟩

/-- Ported from TreeSimStages.treeStages_digest_partial_log, with the output
type generalized so audited records use the same exact joint transcript. -/
theorem treeHashBudget_digest_partial_log {α : Type} (live : C.Party → Bool)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (salts : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
      (fun i (_ : Unit) => (compareDigests (ctx i) (salts i)).run (st i) >>= k i)
      (fun i => if i ∈ D.1 then none else if live i then some () else none))).run s)) :
    ∃ ds, r.1 = treeSimCheckWaiting K D live (.digests ds) (fun i => k i ((), st i)) ∧
      ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T → ∃ h d,
        TreeSimHashAnswer r.2.2 (.history ((st i).history T)) h ∧
        TreeSimHashAnswer r.2.2 (.digest (vector 256 (salts i T)) h) d ∧
        (ds i)[C.terms.idxOf T]? = some d := by
  let P := fun i (v : Step C E RealSpec α) (log : TreeSimLog C) => ∃ ds,
    v = treeSimCheckWaiting K D live (.digests (fun _ => ds)) (fun j => k j ((), st j)) i ∧
    (i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T → ∃ h d,
      TreeSimHashAnswer log (.history ((st i).history T)) h ∧
      TreeSimHashAnswer log (.digest (vector 256 (salts i T)) h) d ∧
      ds[C.terms.idxOf T]? = some d)
  have certificates : ∀ i, P i (r.1 i) r.2.2 := by
    apply treeStages_resumeAll_log prims D _ _ P _ _ s r hr
    · intro i v l l' hpref hp
      obtain ⟨ds, hv, hc⟩ := hp
      refine ⟨ds, hv, ?_⟩
      intro hi hl T held
      obtain ⟨h, d, hh, hd, idx⟩ := hc hi hl T held
      exact ⟨h, d, treeStages_hashAnswer_mono hpref _ _ hh,
        treeStages_hashAnswer_mono hpref _ _ hd, idx⟩
    · intro i a u hu
      by_cases hi : i ∈ D.1
      · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hu
        subst u
        exact ⟨[], by simp [treeSimCheckWaiting, hi], fun hn => (hn hi).elim⟩
      · simp only [if_neg hi] at hu
        by_cases hl : live i = true
        · simp only [if_pos hl, treeSimResume] at hu
          change u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
            (worldRoles.honest (advance (((compareDigests (ctx i) (salts i)).run (st i) >>= k i).run)))).run a) at hu
          rw [treeSim_digest_entry (K := K), self i hi] at hu
          simp only [simulateQ_map, StateT.run_map, support_map] at hu
          obtain ⟨v, hv, rfl⟩ := hu
          exact ⟨v.1, by simp [treeSimCheckWaiting, hi, hl],
            fun _ _ => treeStages_digestQuery_log prims D i (salts i) (st i).history a v hv⟩
        · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hu
          subst u
          exact ⟨[], by simp [treeSimCheckWaiting, hi, hl], fun _ hh => (hl hh).elim⟩
  choose ds steps cert using certificates
  exact ⟨ds, funext steps, cert⟩


/-- One accepting receiver reduces the actual digest transcript to two points
per term. The acceptance is for the same jointly produced digest rows. -/
theorem treeHashBudget_digest_surviving {α : Type}
    (log : TreeSimLog C) (cache : HashCache C) (coherent : TreeSimHashCoherent cache log)
    (good : ¬ TreeSimHashBudgetCollision log)
    (live : C.Party → Bool) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (salts : C.Party → Shares C Bit) (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
      (fun i (_ : Unit) => (compareDigests (ctx i) (salts i)).run (st i) >>= k i)
      (fun i => if i ∈ D.1 then none else if live i then some () else none))).run s))
    (final : r.2.2 ⊆ log) :
    ∃ ds, r.1 = treeSimCheckWaiting K D live (.digests ds) (fun i => k i ((), st i)) ∧
      ∀ sent receiver, treeSimCheckResult K D live (.digests ds) sent receiver = some () →
        ∃ S : Finset (Query C), S.card ≤ 2 * termCount C ∧ TreeHashCover S s.2 r.2.2 := by
  obtain ⟨ds, waiting, recorded⟩ :=
    treeHashBudget_digest_partial_log prims D K live ctx self salts st k s r run
  refine ⟨ds, waiting, ?_⟩
  intro sent receiver accepted
  have all : ∀ i, i ∉ D.1 → live i = true := by
    intro i hi
    by_contra hn
    rw [treeStages_check_inactive K D live (.digests ds) ⟨i, hi, hn⟩] at accepted
    cases accepted
  have inbox : treeSimCheckInbox D live (.digests ds) sent receiver =
      digestInbox D ds sent receiver := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [treeSimCheckInbox, digestInbox, hi]
    · simp [treeSimCheckInbox, digestInbox, hi, all i hi, treeSimCheckOut]
  have passed : digestLive D ds sent receiver := by
    unfold treeSimCheckResult at accepted
    split_ifs at accepted with hi hl ha hc
    exact ⟨by simpa only [inbox, anyAbort] using ha,
      by simpa only [TreeSimCheckAccept, inbox] using hc⟩
  let inner : C.Party → C.Term → HashOutput := fun i T =>
    (cache (.history ((st i).history T))).getD 0
  let outer : C.Party → C.Term → HashOutput := fun i T =>
    (cache (.digest (vector 256 (salts i T)) (inner i T))).getD 0
  have answers : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T →
      TreeSimHashAnswer log (.history ((st i).history T)) (inner i T) ∧
      TreeSimHashAnswer log (.digest (vector 256 (salts i T)) (inner i T)) (outer i T) ∧
      (ds i)[C.terms.idxOf T]? = some (outer i T) := by
    intro i hi T held
    obtain ⟨h, d, hh, hd, idx⟩ := recorded i hi (all i hi) T held
    have hh' := hh.imp (fun h => final h) (fun h => final h)
    have hd' := hd.imp (fun h => final h) (fun h => final h)
    have hin : inner i T = h := by
      dsimp only [inner]
      rw [coherent (.history ((st i).history T)) h trivial hh']
      rfl
    have hout : outer i T = d := by
      dsimp only [outer]
      rw [hin, coherent (.digest (vector 256 (salts i T)) h) d trivial hd']
      rfl
    rw [hout, hin]
    exact ⟨hh', hd', idx⟩
  have noCollision : ¬ TreeSimHashCollision log := by
    rintro ⟨q, t, h, hq, ht, ne, aq, ah⟩
    exact good ⟨q, t, h, treeSimHash_domain_budget q hq,
      treeSimHash_domain_budget t ht, ne, aq, ah⟩
  obtain ⟨S, size, points⟩ := treeSimHash_digest_points D log noCollision
    (fun i T => vector 256 (salts i T)) (fun i => (st i).history)
    inner outer ds answers sent receiver passed
  exact ⟨S, size, treeHashBudget_digest_partial_cover prims D K S log cache coherent
    live ctx self salts st (fun i hi _ => points i hi) k s r run final⟩

/-- The whole opening, including both copy passes, one shared malicious reply,
and rejection, has the paper's distinct-point cover. No agreement is assumed. -/
theorem treeHashBudget_open_phase
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (count : ℕ) (v : C.Party → Shares C Bit)
    (zero : ∀ i T, i ∉ C.holders T → ∀ g, v i T g = 0)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Option (ℕ → Bit))) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (fuel + 1) state
        (fun i => openRep K (localContext i) (v i) count))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ C.n * termCount C + 1 ∧
      TreeHashCover S s.2 r.2.2 := by
  rw [treeLockstep_open_phase K D A fuel state count v] at run
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨ds, hds, adv, hadv, out, hout, rfl⟩ := run
  obtain ⟨S, size, cover⟩ := treeSimHash_open_points K count v
    (treeSimOpenInbox K D (fun _ => true) count v ds.1 adv.1.2) zero
  refine ⟨S, size, ?_⟩
  have first : TreeHashCover S s.2 ds.2.2 := by
    apply treeHashBudget_free_cover prims D S _ ?_ s ds hds
    unfold treeLockstepOpenHashes
    apply isQueryBoundP_sequenceFin
    intro i
    split_ifs
    · exact hashes_freeHashIn_zero _ _ _ (fun T _ hn => hn (cover i T).1)
    · exact isQueryBoundP_pure _ _ _
  have middle := treeHashBudget_adversary_cover prims D S _ ds.2 adv hadv
  have last : TreeHashCover S adv.2.2 out.2.2 := by
    apply treeHashBudget_free_cover prims D S _ ?_ adv.2 out hout
    apply isQueryBoundP_sequenceFin
    intro i
    simp only [treeSimOpenHead, if_true]
    split_ifs with hi
    · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_pure _ _ _
    · simp only [liftComp_bind, liftComp_pure]
      refine isQueryBoundP_bind (n := 0) (m := 0)
        (hashes_freeHashIn_zero (fun q => q ∉ S) _ _
          (fun T _ hn => hn (cover i T).2))
        (fun _ _ => isQueryBoundP_pure _ _ _)
  exact first.trans (middle.trans last)

/-- The actual accepted Coin values share one coin-key point at a common
tag and label. Rejecting operators issue no coin-key query. -/
theorem treeHashBudget_coin_hashes (count tag label : ℕ)
    (rnd : C.Party → PrssOutput C E) (sent : C.Party → Mail C E)
    (s : TreeSimState C) (r : (C.Party → Option HashOutput) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free
      (Concrete.sequenceFin fun i => match treeSimCoinOutput K D count rnd sent i with
        | none => pure none
        | some values => some <$> liftComp
            (hashQuery (C := C) (.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v))))
            (LocalSpec C)))).run s)) :
    ∃ S : Finset (Query C), S.card ≤ 1 ∧ TreeHashCover S s.2 r.2.2 := by
  obtain ⟨S, size, points⟩ := treeSimHash_coin_points K D count tag label rnd sent
  refine ⟨S, size, treeHashBudget_free_cover prims D S _ ?_ s r run⟩
  apply isQueryBoundP_sequenceFin
  intro i
  cases hi : treeSimCoinOutput K D count rnd sent i with
  | none => exact isQueryBoundP_pure _ _ _
  | some values =>
    rw [isQueryBoundP_map_iff]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := LocalSpec C)
      (.inr (.inl (.coinKey tag label (values.flatMap fun v => List.ofFn (K.encode v))))))) _ 0
    rw [isQueryBoundP_query_iff]
    rintro ⟨q, hq, he⟩
    simp only [Sum.inr.injEq, Sum.inl.injEq] at he
    exact (hq (he ▸ points i values hi)).elim

/-- The original target, with all inputs and guards unchanged. -/
def TreeHashBudgetRemaining (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) : Prop :=
  TreeSimHashHonestBudget prims K circuits settings

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_open_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_open_phase

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_digest_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_digest_terminal

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_digest_surviving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_digest_surviving

/-- info: 'ThresholdLeanXmssSecurity.treeHashBudget_coin_hashes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashBudget_coin_hashes

end ThresholdLeanXmssSecurity
