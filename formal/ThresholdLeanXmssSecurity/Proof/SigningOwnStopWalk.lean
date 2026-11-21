import ThresholdLeanXmssSecurity.Proof.SigningOwnStop

/-!
# The walk of the ledger run

The lemmas bound the ledger of a run of the ledger world by the own keyed calls of the new log.

* `Paid x n p r` states that each new unit of the ledger from `p` to `r` is an own keyed call of
  the new log, apart from `n` free units.
* `ledger_run_bound` gives `n` free units for a program with at most `n` calls of the free copy on
  a bottom digest input. `ledger_run_except` gives one free unit when all these calls are on one
  input.
* `ledger_run_alt` states that the ledger does not move after a second opening of a commitment.
  `ledger_run_rerun` states that it does not move in a rerun of a hash program.
* `TreeAgrees` is the agreement of a stored tree with the cache at one key.
  `world_check_alternative` and `world_base_witness` are the two handler facts of a signer.
  `ledger_signCodeword` joins them.
* `freeKeyed_of_atKey`, `freeKeyed_except_of_atKey` and `dealer_freeKeyed` move the static lemmas
  of `SigningSelection` to the form of the walk.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningOwnStop

open HashSig LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof SigningJointEagerProof
  SigningPartnerBoundProof SigningReleasedLinkProof SigningReleasedAlignProof SigningOwnForger

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- A bottom digest input of the parameter `P`, at each key. -/
def Keyed (P : PublicParameter) (input : HashInput) : Prop :=
  (XmssSecurity.encodingInputLeafIndex? P input).isSome

theorem keyed_iff (P : PublicParameter) (input : HashInput) :
    Keyed P input ↔ ∃ e, SigningSelectionProof.AtKey P e input := by
  unfold Keyed SigningSelectionProof.AtKey
  exact Option.isSome_iff_exists

/-- The ledger of `r` is paid from `p`. Each new unit of the ledger is an own keyed call of the new
log, apart from `n` free units. -/
def Paid (x : SigningSecurityProof.Keys3 C) (n : ℕ) (p r : LedgerState C) : Prop :=
  r.1.2 + SigningGuessLaneProof.logCost (ownKeyedCost x) p.1.1.1.1.2 ≤
    p.1.2 + SigningGuessLaneProof.logCost (ownKeyedCost x) r.1.1.1.1.2 + n

theorem Paid.refl (x : SigningSecurityProof.Keys3 C) (p : LedgerState C) : Paid x 0 p p :=
  le_rfl

theorem Paid.trans {x : SigningSecurityProof.Keys3 C} {n m : ℕ} {p q r : LedgerState C}
    (h : Paid x n p q) (h' : Paid x m q r) : Paid x (n + m) p r := by
  unfold Paid at *
  omega

theorem Paid.mono {x : SigningSecurityProof.Keys3 C} {n m : ℕ} {p r : LedgerState C}
    (h : Paid x n p r) (hle : n ≤ m) : Paid x m p r := by
  unfold Paid at *
  omega

set_option linter.constructorNameAsVariable false in
/-- A call of the split world logs the call. -/
theorem world_log (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain) (s : SplitState C)
    (r : (WorldSpec C).Range t × SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s)) :
    r.2.1.1.1.2 = s.1.1.1.2.logQuery t r.1 := by
  simp only [SigningReleasedLinkProof.world, SigningOneRunProof.keyedSplitWorld, carry, StateT.run_mk,
    bind_map_left, mem_support_bind_iff, support_map, Set.mem_image] at hr
  obtain ⟨z, hz, y, hy, rfl⟩ := hr
  exact SigningHitLaneProof.loggedImpl_log prims t s.1.1.1 z hz

/-- The charge of a call is at most its own keyed unit and one unit for a call of the free copy on
a bottom digest input. -/
theorem stopCharge_le (x : SigningSecurityProof.Keys3 C) (cache : HashCache C) (t : (WorldSpec C).Domain) :
    stopCharge x cache t ≤
      ownKeyedCost x t + if SigningSelectionProof.FreeQ (Keyed x.1) t then 1 else 0 := by
  unfold stopCharge
  by_cases halt : SigningGuessProof.AlternativeCommitment x.2.1 x.1 cache
  · rw [ite_eq_left halt]
    exact Nat.zero_le _
  rw [ite_eq_right halt]
  rcases t with ((n | (q | q)) | prog) | (n | (q | q))
  · simp [SigningOwnR1.freshKeyedCost]
  · refine le_trans ?_ (Nat.le_add_right _ _)
    cases q with
    | hash input =>
      simp only [SigningOwnR1.freshKeyedCost, ownKeyedCost]
      split_ifs <;> simp_all
    | _ => simp [SigningOwnR1.freshKeyedCost]
  · simp [SigningOwnR1.freshKeyedCost]
  · simp [SigningOwnR1.freshKeyedCost]
  · simp [SigningOwnR1.freshKeyedCost]
  · refine le_trans ?_ (Nat.le_add_left _ _)
    cases q with
    | hash input =>
      by_cases hk : Keyed x.1 input
      · have hf : SigningSelectionProof.FreeQ (C := C) (Keyed x.1) (.inr (.inr (.inl (.hash input)))) :=
          ⟨input, rfl, hk⟩
        rw [ite_eq_left hf]
        simp only [SigningOwnR1.freshKeyedCost]
        split_ifs <;> simp
      · have hk' : ¬(XmssSecurity.encodingInputLeafIndex? x.1 input).isSome := hk
        simp [SigningOwnR1.freshKeyedCost, hk']
    | _ => simp [SigningOwnR1.freshKeyedCost]
  · simp [SigningOwnR1.freshKeyedCost]

/-- One call of the ledger world is paid with its unit of the free copy. -/
theorem ledgerWorld_paid (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain) (p : LedgerState C)
    (r : (WorldSpec C).Range t × LedgerState C) (hr : r ∈ support ((ledgerWorld prims x t).run p)) :
    Paid x (if SigningSelectionProof.FreeQ (Keyed x.1) t then 1 else 0) p r.2 := by
  obtain ⟨hw, hledger⟩ := ledgerWorld_support prims x t p r hr
  have hlog : r.2.1.1.1.1.2 = p.1.1.1.1.2.logQuery t r.1 := world_log prims x t (p.1.1, p.2) _ hw
  have hc := stopCharge_le x p.1.1.1.1.1.1 t
  unfold Paid
  rw [hledger, hlog, logCost_logQuery]
  omega

/-- A world program with at most `n` calls of the free copy on a bottom digest input adds at
most `n` free units to the ledger. -/
theorem ledger_run_bound {α : Type} (x : SigningSecurityProof.Keys3 C) (oa : OracleComp (WorldSpec C) α)
    (n : ℕ) (hbound : oa.IsQueryBoundP (SigningSelectionProof.FreeQ (Keyed x.1)) n)
    (p : LedgerState C) (r : α × LedgerState C)
    (hr : r ∈ support ((simulateQ (ledgerWorld prims x) oa).run p)) : Paid x n p r.2 := by
  induction oa using OracleComp.inductionOn generalizing p n with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
    exact (Paid.refl x p).mono (Nat.zero_le n)
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at hbound
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    have hstep := ledgerWorld_paid prims x t p mid hmid
    have hrest := ih mid.1 _ (hbound.2 mid.1) mid.2 hr
    refine (hstep.trans hrest).mono ?_
    split_ifs with hf
    · have := hbound.1.resolve_left (not_not.mpr hf)
      omega
    · omega

/-- After a second opening of a commitment, the ledger does not move. -/
theorem ledger_run_alt {α : Type} (x : SigningSecurityProof.Keys3 C) (oa : OracleComp (WorldSpec C) α)
    (p : LedgerState C) (halt : SigningGuessProof.AlternativeCommitment x.2.1 x.1 p.1.1.1.1.1.1)
    (r : α × LedgerState C) (hr : r ∈ support ((simulateQ (ledgerWorld prims x) oa).run p)) :
    r.2.1.2 = p.1.2 := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    obtain ⟨hsplit, hledger⟩ := ledgerWorld_support prims x t p mid hmid
    have hgrow := world_cache_le prims x t (p.1.1, p.2) _ hsplit
    have halt' : SigningGuessProof.AlternativeCommitment x.2.1 x.1 mid.2.1.1.1.1.1.1 :=
      SigningGuessProof.alternativeCommitment_mono x.2.1 x.1 _ _ hgrow halt
    rw [ih mid.1 mid.2 halt' hr, hledger, stopCharge, ite_eq_left halt, Nat.add_zero]

/-- A call of `H` on the free copy caches its answer. -/
theorem countImpl_free_hash_answer (input : HashInput) (s : HashCache C × ℕ)
    (w : HashOutput × HashCache C × ℕ)
    (hw : w ∈ support ((SigningCacheProof.countImpl prims (.inr (.inr (.inl (.hash input))))).run s)) :
    w.2.1 (.hash input) = some w.1 := by
  simp only [SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk, support_map] at hw
  obtain ⟨r, hr, rfl⟩ := hw
  exact (randomOracle_support _ s.1 r hr).2.1

/-- A call of `H` on the free copy of the split world caches its answer. -/
theorem world_free_hash_cached (x : SigningSecurityProof.Keys3 C) (input : HashInput) (s : SplitState C)
    (r : HashOutput × SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x (.inr (.inr (.inl (.hash input))))).run s)) :
    r.2.1.1.1.1.1 (.hash input) = some r.1 := by
  obtain ⟨counted, hcounted, hv, hle⟩ := world_counted_step prims x (.inr (.inr (.inl (.hash input)))) s r hr
  rw [← hv]
  exact hle (countImpl_free_hash_answer prims input _ counted hcounted)

/-- A call of `H` on a cached input has no charge. -/
theorem stopCharge_cached (x : SigningSecurityProof.Keys3 C) (cache : HashCache C) (input : HashInput)
    (output : HashOutput) (hcache : cache (.hash input) = some output) :
    stopCharge x cache (.inr (.inr (.inl (.hash input)))) = 0 := by
  unfold stopCharge
  split_ifs
  · rfl
  · simp [SigningOwnR1.freshKeyedCost, hcache]

/-- A rerun of a hash program on the free copy does not move the ledger. The cache of the
state holds the cache of a first run. -/
theorem ledger_run_rerun {α : Type} (x : SigningSecurityProof.Keys3 C)
    (oa : OracleComp LeanXmss.HashSpec α) (initial first : HashCache C) (a : α)
    (hfirst : (a, first) ∈ support ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput))
      (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input)) oa)).run initial))
    (p : LedgerState C) (hle : first ≤ p.1.1.1.1.1.1) (r : α × LedgerState C)
    (hr : r ∈ support ((simulateQ (ledgerWorld prims x)
      (SigningSecurityProof.liftFree (tweakable oa))).run p)) :
    r.2.1.2 = p.1.2 := by
  induction oa using OracleComp.inductionOn generalizing initial p r with
  | pure value =>
    change r ∈ support ((simulateQ (ledgerWorld prims x)
      (SigningSecurityProof.liftFree (tweakable (pure value : OracleComp LeanXmss.HashSpec α)))).run p) at hr
    rw [tweakable_pure] at hr
    simp [SigningSecurityProof.liftFree, free] at hr
    rw [hr]
  | query_bind t next ih =>
    rw [simulateQ_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hfirst
    obtain ⟨⟨output, middle⟩, hquery, hrest⟩ := hfirst
    simp only [simulateQ_spec_query] at hquery
    have hmid : middle (.hash t) = some output :=
      (randomOracle_support (.hash t) initial (output, middle) (by simpa using hquery)).2.1
    have hmiddleLe : middle ≤ first :=
      SeedHitProof.support_simulateQ_inv (randomOracle (spec := Query C →ₒ HashOutput))
        (fun cache => middle ≤ cache)
        (fun q cache hcache r hr => hcache.trans (randomOracle_support q cache r hr).1)
        _ middle le_rfl _ hrest
    have hcached : p.1.1.1.1.1.1 (.hash t) = some output := hle (hmiddleLe hmid)
    change r ∈ support ((simulateQ (ledgerWorld prims x)
      (SigningCacheProof.freeHom (tweakable (Verification.oracleHashWithHash t >>= next)))).run p) at hr
    rw [tweakable_bind, tweakable_oracleHash, MonadHom.mmap_bind] at hr
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨step, hstep, hr⟩ := hr
    have hstep' : step ∈ support ((ledgerWorld prims x (.inr (.inr (.inl (.hash t))))).run p) := by
      change step ∈ support ((simulateQ (ledgerWorld prims x)
        (SigningSecurityProof.liftFree (hashQuery (.hash t)))).run p) at hstep
      rw [SigningSecurityProof.liftFree, hashQuery, free] at hstep
      erw [liftComp_query, simulateQ_query] at hstep
      erw [id_map] at hstep
      exact hstep
    obtain ⟨hsplit, hledger⟩ := ledgerWorld_support prims x (.inr (.inr (.inl (.hash t)))) p step hstep'
    rw [stopCharge_cached x _ t output hcached, Nat.add_zero] at hledger
    have hgrow := world_cache_le prims x (.inr (.inr (.inl (.hash t)))) (p.1.1, p.2) _ hsplit
    have hanswer : step.1 = output := Option.some.inj
      ((world_free_hash_cached prims x t (p.1.1, p.2) _ hsplit).symm.trans (hgrow hcached))
    rw [hanswer] at hr
    rw [ih output middle hrest step.2 (hle.trans hgrow) r hr, hledger]

/-- One call of the ledger world with no call of the free copy on a bottom digest input other
than `X` is paid with the drop of the free unit of `X`. The free unit of `X` is one while `X` is not
in the cache, and it does not rise. -/
theorem ledgerWorld_except (x : SigningSecurityProof.Keys3 C) (X : HashInput) (t : (WorldSpec C).Domain)
    (ht : ¬SigningSelectionProof.FreeQ (C := C) (fun input => Keyed x.1 input ∧ input ≠ X) t)
    (p : LedgerState C) (r : (WorldSpec C).Range t × LedgerState C)
    (hr : r ∈ support ((ledgerWorld prims x t).run p)) :
    Paid x ((if p.1.1.1.1.1.1 (.hash X) = none then 1 else 0) -
        (if r.2.1.1.1.1.1.1 (.hash X) = none then 1 else 0)) p r.2 ∧
      (if r.2.1.1.1.1.1.1 (.hash X) = none then 1 else 0) ≤
        (if p.1.1.1.1.1.1 (.hash X) = none then 1 else 0) := by
  obtain ⟨hw, hledger⟩ := ledgerWorld_support prims x t p r hr
  have hlog : r.2.1.1.1.1.2 = p.1.1.1.1.2.logQuery t r.1 := world_log prims x t (p.1.1, p.2) _ hw
  have hgrow := world_cache_le prims x t (p.1.1, p.2) _ hw
  have hmono : (if r.2.1.1.1.1.1.1 (.hash X) = none then 1 else 0) ≤
      (if p.1.1.1.1.1.1 (.hash X) = none then 1 else 0) := by
    cases hp : p.1.1.1.1.1.1 (.hash X) with
    | none =>
      rw [ite_eq_left rfl]
      split_ifs <;> omega
    | some v =>
      have hr' : r.2.1.1.1.1.1.1 (.hash X) = some v := hgrow hp
      rw [hr']
  refine ⟨?_, hmono⟩
  have hc : stopCharge x p.1.1.1.1.1.1 t ≤ ownKeyedCost x t +
      ((if p.1.1.1.1.1.1 (.hash X) = none then 1 else 0) -
        (if r.2.1.1.1.1.1.1 (.hash X) = none then 1 else 0)) := by
    by_cases hX : t = .inr (.inr (.inl (.hash X)))
    · subst hX
      have hcached := world_free_hash_cached prims x X (p.1.1, p.2) (r.1, (r.2.1.1, r.2.2)) hw
      have hne : r.2.1.1.1.1.1.1 (.hash X) ≠ none := by
        change (r.1, (r.2.1.1, r.2.2)).2.1.1.1.1.1 (.hash X) ≠ none
        rw [hcached]
        exact Option.some_ne_none _
      rw [ite_eq_right hne, Nat.sub_zero]
      unfold stopCharge
      by_cases halt : SigningGuessProof.AlternativeCommitment x.2.1 x.1 p.1.1.1.1.1.1
      · rw [ite_eq_left halt]
        exact Nat.zero_le _
      rw [ite_eq_right halt]
      by_cases hn : p.1.1.1.1.1.1 (.hash X) = none
      · rw [ite_eq_left hn]
        simp only [SigningOwnR1.freshKeyedCost]
        split_ifs <;> simp
      · rw [ite_eq_right hn]
        simp only [SigningOwnR1.freshKeyedCost]
        rw [ite_eq_right (fun h => hn h.2)]
        exact Nat.zero_le _
    · have hfree : ¬SigningSelectionProof.FreeQ (C := C) (Keyed x.1) t := by
        rintro ⟨input, rfl, hk⟩
        exact ht ⟨input, rfl, hk, fun h => hX (h ▸ rfl)⟩
      have h := stopCharge_le x p.1.1.1.1.1.1 t
      rw [ite_eq_right hfree, Nat.add_zero] at h
      exact h.trans (Nat.le_add_right _ _)
  unfold Paid
  rw [hledger, hlog, logCost_logQuery]
  omega

/-- `ledger_run_except` with the free unit of `X` at the cache of the start. -/
theorem ledger_run_except_cached {α : Type} (x : SigningSecurityProof.Keys3 C) (X : HashInput)
    (oa : OracleComp (WorldSpec C) α)
    (hcall : SigningSelectionProof.NoCall
      (SigningSelectionProof.FreeQ (C := C) fun input => Keyed x.1 input ∧ input ≠ X) oa)
    (p : LedgerState C) (r : α × LedgerState C)
    (hr : r ∈ support ((simulateQ (ledgerWorld prims x) oa).run p)) :
    Paid x (if p.1.1.1.1.1.1 (.hash X) = none then 1 else 0) p r.2 := by
  rw [SigningSelectionProof.noCall_iff] at hcall
  induction oa using OracleComp.inductionOn generalizing p with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
    exact (Paid.refl x p).mono (Nat.zero_le _)
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff] at hcall
    have ht : ¬SigningSelectionProof.FreeQ (C := C) (fun input => Keyed x.1 input ∧ input ≠ X) t :=
      hcall.1.resolve_right (by omega)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    obtain ⟨hstep, hmono⟩ := ledgerWorld_except prims x X t ht p mid hmid
    have hrest := ih mid.1 (by simpa [ht] using hcall.2 mid.1) mid.2 hr
    refine (hstep.trans hrest).mono ?_
    omega

/-- A world program whose calls of the free copy on a bottom digest input are all on one
input `X` adds at most one free unit to the ledger. The second call on `X` is on a cached input. -/
theorem ledger_run_except {α : Type} (x : SigningSecurityProof.Keys3 C) (X : HashInput)
    (oa : OracleComp (WorldSpec C) α)
    (hcall : SigningSelectionProof.NoCall
      (SigningSelectionProof.FreeQ (C := C) fun input => Keyed x.1 input ∧ input ≠ X) oa)
    (p : LedgerState C) (r : α × LedgerState C)
    (hr : r ∈ support ((simulateQ (ledgerWorld prims x) oa).run p)) : Paid x 1 p r.2 := by
  refine (ledger_run_except_cached prims x X oa hcall p r hr).mono ?_
  split_ifs <;> omega

/-! ## The two handler facts -/

/-- The stored commitment of key `e` agrees with the cache. The terms of the randomizer of `e` are
in the cache, and the commitment of the tree is the cached answer at the cached randomizer. -/
def TreeAgrees (x : SigningSecurityProof.Keys3 C) (cache : HashCache C) (tree : BottomTree)
    (e : KeyIndex) : Prop :=
  SigningGuessProof.RandomizerCached x.2.1 cache e ∧
    ∃ v, cache (.hash (commitmentInput x.1 e (SigningGuessProof.cachedRandomizer x.2.1 cache e))) = some v ∧
      tree.commitment e = truncateHash v

theorem TreeAgrees.mono {x : SigningSecurityProof.Keys3 C} {cache cache' : HashCache C}
    {tree : BottomTree} {e : KeyIndex} (hle : cache ≤ cache') (h : TreeAgrees x cache tree e) :
    TreeAgrees x cache' tree e := by
  obtain ⟨hprf, v, hv, hc⟩ := h
  have hs := SigningGuessProof.cachedRandomizer_stable x.2.1 cache cache' e hle hprf
  refine ⟨SigningR1FixedProof.randomizerCached_mono hle hprf, v, ?_, hc⟩
  rw [← hs]
  exact hle hv

/-- The invariant of the walk. The cache holds a run of the top tree and a run of each stored
bottom tree. -/
def StopInv (x : SigningSecurityProof.Keys3 C) (top : TopTree) (s : SplitState C) : Prop :=
  TopRun prims x top s.1.1.1.1.1 ∧ SigningGuessProof.StoredTreeRuns prims x top s.1.1.1.1.1 s.2.1.1

set_option linter.constructorNameAsVariable false in
/-- The transport of the invariant. A bottom tree with a run below the cache agrees with the cache
at each of its keys. -/
theorem treeAgrees_of_run (x : SigningSecurityProof.Keys3 C) (top : TopTree) (e : KeyIndex)
    (cache : HashCache C) (htop : TopRun prims x top cache) (tree : BottomTree)
    (initial : HashCache C × ℕ) (built : Option TreeOutput × HashCache C × ℕ)
    (hbuilt : built ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 top
        (.bottom (treeOf e))))).run initial))
    (htree : built.1 = some (.bottom tree)) (hle : built.2.1 ≤ cache) : TreeAgrees x cache tree e := by
  obtain ⟨hterms, canonicalOutput, hcanonical⟩ := SigningGuessProof.run_bottom_commitment_cached
    prims x.2.1 x.1 top e initial built (by with_reducible exact hbuilt)
    (SigningCacheProof.answersOf cache) (SigningCacheProof.agrees_answersOf hle)
  have ht := SigningGuessProof.run_bottom_commitment_eq prims x.2.1 x.1 top e initial built
    (by with_reducible exact hbuilt) (SigningCacheProof.answersOf cache)
    (SigningCacheProof.agrees_answersOf hle) htop.facts tree htree
  have hcanonical' := hle hcanonical
  rw [SigningGuessProof.cachedRandomizer_eq] at hcanonical' ht
  refine ⟨fun T => ?_, canonicalOutput, hcanonical', ?_⟩
  · obtain ⟨answer, ha⟩ := hterms T
    exact ⟨answer, hle ha⟩
  · simpa only [SigningCacheProof.answersOf, hcanonical', Option.getD_some] using ht

/-- The second handler fact on a cache. A check of `c_e` that passes at a value other than the
cached randomizer gives a second opening of the commitment. -/
theorem alternativeCommitment_of_check (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (tree : BottomTree) (e : KeyIndex) (hagree : TreeAgrees x cache tree e) (candidate : Digest)
    (output : HashOutput) (hcall : cache (.hash (commitmentInput x.1 e candidate)) = some output)
    (hpass : truncateHash output = tree.commitment e)
    (hne : candidate ≠ SigningGuessProof.cachedRandomizer x.2.1 cache e) :
    SigningGuessProof.AlternativeCommitment x.2.1 x.1 cache := by
  obtain ⟨hprf, v, hv, hc⟩ := hagree
  exact ⟨e, candidate, v, output, hprf, hv, hcall, hne, hpass.trans hc⟩

/-- The second handler fact as a step of the split world. The check of `c_e` of a signer
is one call of the free copy on `commitmentInput`. If its answer passes at a value other than the
cached randomizer, the cache after the call has a second opening. -/
theorem world_check_alternative (x : SigningSecurityProof.Keys3 C) (e : KeyIndex) (candidate : Digest)
    (tree : BottomTree) (s : SplitState C) (hagree : TreeAgrees x s.1.1.1.1.1 tree e)
    (r : HashOutput × SplitState C)
    (hr : r ∈ support ((world prims x
      (.inr (.inr (.inl (.hash (commitmentInput x.1 e candidate)))))).run s))
    (hpass : truncateHash r.1 = tree.commitment e)
    (hne : candidate ≠ SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) :
    SigningGuessProof.AlternativeCommitment x.2.1 x.1 r.2.1.1.1.1.1 := by
  have hgrow := world_cache_le prims x (.inr (.inr (.inl (.hash (commitmentInput x.1 e candidate))))) s r hr
  have hcall := world_free_hash_cached prims x _ s r hr
  have hne' : candidate ≠ SigningGuessProof.cachedRandomizer x.2.1 r.2.1.1.1.1.1 e := fun h =>
    hne (h.trans (SigningGuessProof.cachedRandomizer_stable x.2.1 _ _ e hgrow hagree.1).symm)
  exact alternativeCommitment_of_check x _ tree e (hagree.mono hgrow) candidate r.1 hcall hpass hne'

set_option linter.constructorNameAsVariable false in
/-- A canonical base call of the split world runs the search on the answer of the base input. The
cache after the call holds the run of the search and the answer. -/
theorem world_base_grind (x : SigningSecurityProof.Keys3 C) (t : (WorldSpec C).Domain) (s : SplitState C)
    (r : (WorldSpec C).Range t × SplitState C)
    (hr : r ∈ support ((SigningReleasedLinkProof.world prims x t).run s)) (e : KeyIndex) (message : Message)
    (hprf : SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 e)
    (hbase : BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) s.2.1.1 t)
    (hb : s.2.1.1.bound e = some message) :
    ∃ (initial first : HashCache C) (found : Option (Randomizer × Encoding)) (answer : HashOutput),
      (found, first) ∈ support ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput))
        (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
          (grind x.1 bottomLayer e (littleEndianBytes 32 message) (truncateHash answer)
            randomizerAttemptLimit 0))).run initial) ∧
      first ≤ r.2.1.1.1.1.1 ∧
      r.2.1.1.1.1.1 (.hash (randomizerInput x.1 bottomLayer e
        (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (littleEndianBytes 32 message))) = some answer := by
  have hcall : HashCallAt (randomizerInput x.1 bottomLayer e
      (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (littleEndianBytes 32 message)) t := by
    obtain ⟨input, hi, hc⟩ := hbase
    have hi' : randomizerInput x.1 bottomLayer e
        (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (littleEndianBytes 32 message) = input := by
      unfold baseInput at hi
      rw [hb] at hi
      exact Option.some.inj hi
    exact hi'.symm ▸ hc
  simp only [SigningReleasedLinkProof.world, SigningOneRunProof.keyedSplitWorld, StateT.run_mk,
    mem_support_bind_iff, support_map, Set.mem_image] at hr
  obtain ⟨called, hc, ground, hg, rfl⟩ := hr
  have hc' := hc
  simp only [carry, SigningCostProof.loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hc'
  obtain ⟨outer, ⟨counted, hcounted, rfl⟩, heq⟩ := hc'
  obtain ⟨baseAnswer, hanswer⟩ := countImpl_hash_cached prims _ t hcall _ counted hcounted
  have ha : called.2.1.1.1 (.hash (randomizerInput x.1 bottomLayer e
      (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (littleEndianBytes 32 message))) = some baseAnswer := by
    rw [← heq]
    exact hanswer
  rw [SigningReleasedLinkProof.jointCachedExtra_base x (s.1.1.1, s.2) called.2 t e message baseAnswer
    hprf hbase hb ha] at hg
  obtain ⟨g, hgrind, hgstate⟩ := baseGrind_subrun x.1 e message baseAnswer _ ground hg
  have hgrow := keyed_run_cache_le (XmssSecurity.encodingInputLeafIndex? x.1) _ _ ground hg
  have hraw := keyed_run_support (XmssSecurity.encodingInputLeafIndex? x.1) _ _ g hgrind
  refine ⟨_, g.2.1.1, g.1, baseAnswer, hraw, ?_, ?_⟩
  · change g.2.1.1 ≤ ground.2.1.1
    rw [hgstate]
  · change ground.2.1.1 _ = _
    exact hgrow ha

/-- The first handler fact as a step of the split world. The base call of a signer at the
cached randomizer of a bound key leaves a complete run of the search in the cache. The fact does
not read the signed keys of the monitor. -/
theorem world_base_witness (x : SigningSecurityProof.Keys3 C) (e : KeyIndex) (message : Message)
    (s : SplitState C) (hprf : SigningGuessProof.RandomizerCached x.2.1 s.1.1.1.1.1 e)
    (hb : s.2.1.1.bound e = some message) (r : HashOutput × SplitState C)
    (hr : r ∈ support ((world prims x (.inr (.inr (.inl (.hash (randomizerInput x.1 bottomLayer e
      (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (littleEndianBytes 32 message))))))).run s)) :
    ∃ (initial first : HashCache C) (found : Option (Randomizer × Encoding)),
      (found, first) ∈ support ((simulateQ (randomOracle (spec := Query C →ₒ HashOutput))
        (simulateQ (fun input => query (spec := Query C →ₒ HashOutput) (.hash input))
          (grind x.1 bottomLayer e (littleEndianBytes 32 message) (truncateHash r.1)
            randomizerAttemptLimit 0))).run initial) ∧
      first ≤ r.2.1.1.1.1.1 := by
  have hbase : BaseCall x.1 e (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) s.2.1.1
      (.inr (.inr (.inl (.hash (randomizerInput x.1 bottomLayer e
        (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (littleEndianBytes 32 message)))))) :=
    ⟨_, by rw [baseInput, hb]; rfl, Or.inr rfl⟩
  obtain ⟨initial, first, found, answer, hrun, hle, hcache⟩ := world_base_grind prims x
    (.inr (.inr (.inl (.hash (randomizerInput x.1 bottomLayer e
      (SigningGuessProof.cachedRandomizer x.2.1 s.1.1.1.1.1 e) (littleEndianBytes 32 message)))))) s r hr e message
    hprf hbase hb
  have hanswer : answer = r.1 :=
    Option.some.inj (hcache.symm.trans (world_free_hash_cached prims x _ s r hr))
  subst hanswer
  exact ⟨initial, first, found, hrun, hle⟩

/-- A call of the free copy on an input that is no bottom digest input has no charge. -/
theorem stopCharge_free_of_not_keyed (x : SigningSecurityProof.Keys3 C) (cache : HashCache C)
    (input : HashInput) (h : ¬Keyed x.1 input) :
    stopCharge x cache (.inr (.inr (.inl (.hash input)))) = 0 := by
  unfold stopCharge
  split_ifs
  · rfl
  · have h' : ¬(XmssSecurity.encodingInputLeafIndex? x.1 input).isSome := h
    simp [SigningOwnR1.freshKeyedCost, h']

/-- One hash call of the free copy in the ledger world. -/
theorem ledger_hashQuery (x : SigningSecurityProof.Keys3 C) (input : HashInput) (p : LedgerState C)
    (r : HashOutput × LedgerState C)
    (hr : r ∈ support ((simulateQ (ledgerWorld prims x)
      (SigningCacheProof.freeHom (hashQuery (C := C) (.hash input)))).run p)) :
    r ∈ support ((ledgerWorld prims x (.inr (.inr (.inl (.hash input))))).run p) := by
  change r ∈ support ((simulateQ (ledgerWorld prims x)
    (SigningSecurityProof.liftFree (hashQuery (.hash input)))).run p) at hr
  rw [SigningSecurityProof.liftFree, hashQuery, free] at hr
  erw [liftComp_query, simulateQ_query] at hr
  erw [id_map] at hr
  exact hr

/-- Both handler facts for one signer. The search of a signer at a bound key does not move the
ledger, for each opened value. At the cached randomizer the search is a rerun. At another value that
passes the check the run is after the stop. -/
theorem ledger_signCodeword (x : SigningSecurityProof.Keys3 C) (e : KeyIndex) (message : Message)
    (candidate : Digest) (tree : BottomTree) (p : LedgerState C)
    (hagree : TreeAgrees x p.1.1.1.1.1.1 tree e) (hb : p.2.1.1.bound e = some message)
    (r : Option (Randomizer × Encoding) × LedgerState C)
    (hr : r ∈ support ((simulateQ (ledgerWorld prims x)
      (SigningSecurityProof.liftFree (signCodeword x.1 (tree.commitment e) e message candidate))).run p)) :
    r.2.1.2 = p.1.2 := by
  change r ∈ support ((simulateQ (ledgerWorld prims x)
    (SigningCacheProof.freeHom (signCodeword x.1 (tree.commitment e) e message candidate))).run p) at hr
  rw [signCodeword, tweakable_bind, tweakable_oracleHash, MonadHom.mmap_bind] at hr
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨opened, hopened, hr⟩ := hr
  obtain ⟨hsplit1, hledger1⟩ := ledgerWorld_support prims x
    (.inr (.inr (.inl (.hash (commitmentInput x.1 e candidate))))) p opened
    (ledger_hashQuery prims x _ p opened hopened)
  rw [stopCharge_free_of_not_keyed x _ _ (fun h => by
    obtain ⟨e', he'⟩ := (keyed_iff _ _).mp h
    exact SigningSelectionProof.not_atKey_commitment x.1 e' e candidate he'), Nat.add_zero] at hledger1
  have hgrow1 := world_cache_le prims x _ (p.1.1, p.2) _ hsplit1
  have hcar1 : opened.2.2 = p.2 := world_carried prims x _ (p.1.1, p.2) _ hsplit1
  have hagree1 : TreeAgrees x opened.2.1.1.1.1.1.1 tree e := hagree.mono hgrow1
  by_cases hbad : truncateHash opened.1 ≠ tree.commitment e
  · rw [ite_eq_left hbad] at hr
    simp only [tweakable_pure, MonadHom.mmap_pure, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at hr
    rw [hr]
    exact hledger1
  · have hpass : truncateHash opened.1 = tree.commitment e := not_not.mp hbad
    by_cases hcan : candidate = SigningGuessProof.cachedRandomizer x.2.1 opened.2.1.1.1.1.1.1 e
    · simp only [hbad, ↓reduceIte, tweakable_bind, tweakable_oracleHash, MonadHom.mmap_bind,
        simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨base, hbase, htail⟩ := hr
      obtain ⟨hsplit2, hledger2⟩ := ledgerWorld_support prims x
        (.inr (.inr (.inl (.hash (randomizerInput x.1 bottomLayer e candidate (littleEndianBytes 32 message))))))
        opened.2 base (ledger_hashQuery prims x _ opened.2 base hbase)
      rw [stopCharge_free_of_not_keyed x _ _ (fun h => by
        obtain ⟨e', he'⟩ := (keyed_iff _ _).mp h
        exact SigningSelectionProof.not_atKey_randomizer x.1 e' e bottomLayer candidate _ he'),
        Nat.add_zero] at hledger2
      have hb2 : opened.2.2.1.1.bound e = some message := by
        rw [hcar1]
        exact hb
      rw [hcan] at hsplit2
      obtain ⟨initial, first, found, hfirst, hle⟩ := world_base_witness prims x e message
        (opened.2.1.1, opened.2.2) hagree1.1 hb2 (base.1, (base.2.1.1, base.2.2)) hsplit2
      rw [ledger_run_rerun prims x _ initial first found hfirst base.2 hle r htail, hledger2, hledger1]
    · have hne : candidate ≠ SigningGuessProof.cachedRandomizer x.2.1 p.1.1.1.1.1.1 e := fun h =>
        hcan (h.trans (SigningGuessProof.cachedRandomizer_stable x.2.1 _ _ e hgrow1 hagree.1))
      have halt := world_check_alternative prims x e candidate tree (p.1.1, p.2) hagree
        (opened.1, (opened.2.1.1, opened.2.2)) hsplit1 hpass hne
      rw [ledger_run_alt prims x _ opened.2 halt r hr, hledger1]


/-- A program with no call of the free copy in each of a family of sets has no such call in their
union. -/
theorem noCall_freeQ_exists {κ α : Type} (Q : κ → HashInput → Prop) (oa : OracleComp (WorldSpec C) α)
    (h : ∀ k, SigningSelectionProof.NoCall (SigningSelectionProof.FreeQ (C := C) (Q k)) oa) :
    SigningSelectionProof.NoCall (SigningSelectionProof.FreeQ (C := C) fun input => ∃ k, Q k input) oa := by
  simp only [SigningSelectionProof.noCall_iff] at h ⊢
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t next ih =>
    rw [isQueryBoundP_query_bind_iff]
    have h' := fun k => (isQueryBoundP_query_bind_iff _ t next 0).mp (h k)
    have ht : ¬SigningSelectionProof.FreeQ (C := C) (fun input => ∃ k, Q k input) t := by
      rintro ⟨input, rfl, k, hk⟩
      exact ((h' k).1.resolve_right (by omega)) ⟨input, rfl, hk⟩
    refine ⟨Or.inl ht, fun u => ?_⟩
    rw [ite_eq_right ht]
    refine ih u fun k => ?_
    have hu := (h' k).2 u
    have hk : ¬SigningSelectionProof.FreeQ (C := C) (Q k) t := (h' k).1.resolve_right (by omega)
    rwa [ite_eq_right hk] at hu

/-- A program with no call of the free copy at each key has no call of the free copy on a bottom
digest input. This form feeds `ledger_run_bound` from the lemmas of `SigningSelection`. -/
theorem freeKeyed_of_atKey {α : Type} (P : PublicParameter) (oa : OracleComp (WorldSpec C) α)
    (h : ∀ e, SigningSelectionProof.NoCall
      (SigningSelectionProof.FreeQ (C := C) (SigningSelectionProof.AtKey P e)) oa) :
    oa.IsQueryBoundP (SigningSelectionProof.FreeQ (Keyed P)) 0 := by
  have hall := noCall_freeQ_exists (C := C) (fun e input => SigningSelectionProof.AtKey P e input) oa h
  rw [SigningSelectionProof.noCall_iff] at hall
  have hpred : (SigningSelectionProof.FreeQ (C := C) fun input => ∃ e, SigningSelectionProof.AtKey P e input) =
      SigningSelectionProof.FreeQ (Keyed P) := by
    congr 1
    funext input
    exact propext (keyed_iff P input).symm
  rw [← hpred]
  exact hall

/-- The same with one input `X` left out. This form feeds `ledger_run_except` from
`SigningSelectionProof.verify_bound`. -/
theorem freeKeyed_except_of_atKey {α : Type} (P : PublicParameter) (X : HashInput)
    (oa : OracleComp (WorldSpec C) α)
    (h : ∀ e, SigningSelectionProof.NoCall
      (SigningSelectionProof.FreeQ (C := C) fun input => SigningSelectionProof.AtKey P e input ∧ input ≠ X) oa) :
    SigningSelectionProof.NoCall
      (SigningSelectionProof.FreeQ (C := C) fun input => Keyed P input ∧ input ≠ X) oa := by
  have hall := noCall_freeQ_exists (C := C)
    (fun e input => SigningSelectionProof.AtKey P e input ∧ input ≠ X) oa h
  have hpred : (SigningSelectionProof.FreeQ (C := C) fun input =>
      ∃ e, SigningSelectionProof.AtKey P e input ∧ input ≠ X) =
      SigningSelectionProof.FreeQ (fun input => Keyed P input ∧ input ≠ X) := by
    congr 1
    funext input
    refine propext ⟨fun ⟨e, he, hne⟩ => ⟨(keyed_iff P input).mpr ⟨e, he⟩, hne⟩, fun ⟨hk, hne⟩ => ?_⟩
    obtain ⟨e, he⟩ := (keyed_iff P input).mp hk
    exact ⟨e, he, hne⟩
  rw [← hpred]
  exact hall

set_option maxRecDepth 100000 in
/-- The dealer makes no call of the free copy on a bottom digest input. -/
theorem dealer_freeKeyed (x : SigningSecurityProof.Keys3 C) :
    (referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top :
        OracleComp (WorldSpec C) (Option TreeOutput)).IsQueryBoundP
      (SigningSelectionProof.FreeQ (Keyed x.1)) 0 := by
  rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
    referenceTree_φ _ _ _ _]
  exact freeKeyed_of_atKey x.1 _ fun e => SigningSelectionProof.noCall_liftFree _ _
    (SigningSelectionProof.referenceTree_bound x.1 e x.2.1 emptyTop .top)

end SigningOwnStop

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.keyed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.keyed_iff

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.Paid.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.Paid.refl

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.Paid.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.Paid.trans

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.Paid.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.Paid.mono

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.world_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.world_log

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.stopCharge_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.stopCharge_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerWorld_paid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerWorld_paid

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_bound

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_alt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_alt

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.countImpl_free_hash_answer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.countImpl_free_hash_answer

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.world_free_hash_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.world_free_hash_cached

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.stopCharge_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.stopCharge_cached

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_rerun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_rerun

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerWorld_except' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerWorld_except

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_except_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_except_cached

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_except' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_except

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.TreeAgrees.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.TreeAgrees.mono

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.treeAgrees_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.treeAgrees_of_run

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.alternativeCommitment_of_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.alternativeCommitment_of_check

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.world_check_alternative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.world_check_alternative

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.world_base_grind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.world_base_grind

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.world_base_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.world_base_witness

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.stopCharge_free_of_not_keyed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.stopCharge_free_of_not_keyed

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_hashQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_hashQuery

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_signCodeword' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_signCodeword

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.noCall_freeQ_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.noCall_freeQ_exists

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.freeKeyed_of_atKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.freeKeyed_of_atKey

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.freeKeyed_except_of_atKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.freeKeyed_except_of_atKey

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.dealer_freeKeyed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.dealer_freeKeyed
