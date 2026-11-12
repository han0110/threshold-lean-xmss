import ThresholdLeanXmssSecurity.Proof.TreeSimHash

/-!
The raw salt estimate for the real ceremony.

Complete hidden blocks implement lazy block reads jointly with the original
hidden cache and call log. Repeated addresses retain the same block.

1. Retain the entire state in the real hidden-block/random-oracle law.
2. Compose that law with any continuation.
3. Apply the existing adaptive address bound with the exact raw coefficient.
4. Derive the original target from `TreeRawSaltCeremonyRepresentation`.

That representation requires normalization of the complete real ceremony into
the opaque address program, preserving its full log distribution, the counted
salt event, and both query budgets. No bound on probabilities is assumed by the
representation. Addresses are discovered during the run and share one hash
cache.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- Installing a block already present in the hidden cache leaves it unchanged. -/
theorem treeRawSalt_install_cached (b : TreeSimHashSaltBlock C)
    (vals : Fin 256 → Bit) (streams : HiddenCache C)
    (cached : ∀ g, streams (treeSimHashSaltAddress b g) = some (vals g)) :
    cacheFin (treeSimHashSaltAddress b) vals streams = streams := by
  funext x
  by_cases hx : ∃ g, x = treeSimHashSaltAddress b g
  · obtain ⟨g, rfl⟩ := hx
    rw [cacheFin_at _ (treeSimHash_salt_address_injective b), cached]
  · exact cacheFin_of_not_mem _ _ _ _ (by simpa only [not_exists] using hx)

/-- The block law retains all state required to compose real salt reads.
Unlike the projected lookup law, it retains the bit cache and complete log. -/
theorem treeRawSalt_block_joint (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (hidden : ¬ KnownTo D.1 b.1)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams) :
    𝒟[(simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prgBits (.term b.1) b.2.1 b.2.2 2 256) (LocalSpec C)))).run
        ((cache, streams), log)] =
      𝒟[(fun r => ((fun g => (List.ofFn r.1).getD g 0),
        (cache, cacheFin (treeSimHashSaltAddress b) r.1 streams),
        log ++ treeSimHiddenLog (treeSimHashSaltAddress b) r.1)) <$>
        (((TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle b).run
          (treeSimHashSaltLookup streams))] := by
  rcases complete b with fresh | ⟨vals, cached⟩
  · rw [treeSimHash_salt_block_fresh prims D b hidden cache streams log fresh]
    rw [QueryImpl.withCaching_run_none _ (treeSimHash_salt_lookup_none streams b fresh)]
    simp only [Functor.map_map]
    rfl
  · rw [treeSim_prgBits_cached_logged prims D (.term b.1) hidden b.2.1 b.2.2 2 256 vals
      cache streams log cached]
    rw [QueryImpl.withCaching_run_some _ (treeSimHash_salt_lookup_some streams b vals cached)]
    rw [map_pure, treeRawSalt_install_cached b vals streams cached]
    rfl

/-- Any continuation of an actual hidden block can instead read the lazy block
oracle and reconstruct its exact state. The continuation may use that state. -/
theorem treeRawSalt_block_bind {α : Type} (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (hidden : ¬ KnownTo D.1 b.1)
    (cache : HashCache C) (streams : HiddenCache C) (log : TreeSimLog C)
    (complete : TreeSimHashSaltBlocksComplete streams)
    (k : (ℕ → Bit) × TreeSimState C → ProbComp α) :
    𝒟[((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prgBits (.term b.1) b.2.1 b.2.2 2 256) (LocalSpec C)))).run
        ((cache, streams), log)) >>= k] =
      𝒟[(((TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle b).run
          (treeSimHashSaltLookup streams)) >>= fun r =>
        k ((fun g => (List.ofFn r.1).getD g 0),
          (cache, cacheFin (treeSimHashSaltAddress b) r.1 streams),
          log ++ treeSimHiddenLog (treeSimHashSaltAddress b) r.1)] := by
  rw [evalDist_bind, treeRawSalt_block_joint prims D b hidden cache streams log complete]
  simp only [← evalDist_bind, bind_map_left]

/-- A nonempty job list contributes at least one batch. -/
theorem treeRawSalt_chunks_pos {α : Type} (size : ℕ) (hsize : 0 < size)
    (jobs : List α) (hne : jobs ≠ []) : 0 < (chunks size jobs).length := by
  by_contra h
  have he : chunks size jobs = [] := List.length_eq_zero_iff.mp (by omega)
  have hf := chunks_flatten size hsize jobs
  rw [he, List.flatten_nil] at hf
  exact hne hf.symm

/-- Every tree has jobs, so the finite salt allocation has positive capacity. -/
theorem treeRawSalt_capacity_pos (settings : Settings) (hb : 0 < settings.batchSize)
    (tree : Tree) : 0 < treeBatches settings tree * (C.t * termCount C) := by
  have ht : 0 < C.t := C.one_le_t
  have hn : 0 < C.n := by simp only [Committee.n]; omega
  have hterms : 0 < termCount C := hn.trans_le treeSimHash_parties_le_terms
  apply Nat.mul_pos _ (Nat.mul_pos ht hterms)
  cases tree with
  | top =>
    apply treeRawSalt_chunks_pos _ hb
    intro he
    let l : ChainIndex := ⟨0, by decide⟩
    have hm : (⟨.chainEnd (topKey 0) l,
        [.chain topLayer (topKey 0) l (digit 0)]⟩ : Job) ∈ topJobs := by
      apply List.mem_flatMap.mpr
      refine ⟨0, List.mem_finRange _, ?_⟩
      exact List.mem_map.mpr ⟨l, List.mem_finRange _, rfl⟩
    simp only [he, List.not_mem_nil] at hm
  | bottom b =>
    have hp := treeRawSalt_chunks_pos _ hb (bottomJobs b) (by simp [bottomJobs])
    exact hp.trans_le (Nat.le_add_right _ _)

abbrev TreeRawSaltOutcome (C : Committee) (H : ℕ) (α : Type) :=
  ((α × List (TreeSimHashSaltBlock C)) × List (List Bit) × List (List Bit)) ×
    HashCache C × (Fin (H + 1) →ₒ (Fin 256 → Bit)).QueryCache

/-- The normalized experiment retains address allocation, used salts, public
salt guesses and both caches. -/
def treeRawSaltRun {α : Type} (prims : Primitives) (H : ℕ)
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α) :
    ProbComp (TreeRawSaltOutcome C H α) :=
  (simulateQ (treeSimHashBlockCacheAnswer (localAnswer prims))
    ((simulateQ treeSimHashSaltRead
      ((simulateQ (treeSimHashSaltAllocate H) p).run [])).run ([], []))).run (∅, ∅)

def TreeRawSaltHit {H : ℕ} {α : Type} (r : TreeRawSaltOutcome C H α) : Prop :=
  ∃ salt, salt ∈ r.1.2.1 ∧ salt ∈ r.1.2.2

set_option backward.isDefEq.respectTransparency false in
/-- The existing lazy address theorem has exactly the real coefficient of A13. -/
theorem treeRawSalt_run_bound {α : Type} (prims : Primitives) (H q : ℕ) (hH : 0 < H)
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (hcount : IsQueryBoundP p treeSimHashSaltTableCharged (q + H)) :
    (Pr[TreeRawSaltHit | treeRawSaltRun prims H p]).toReal ≤
      2 * (H : ℝ) * ((q + H : ℕ) : ℝ) / 2 ^ 256 := by
  have h := treeSimHash_lazy_address_bound prims H (q + H) hH p hcount
  have hr := ENNReal.toReal_mono (by finiteness) h
  unfold TreeRawSaltHit treeRawSaltRun
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, Nat.cast_mul, Nat.cast_ofNat,
    ENNReal.toReal_mul] using hr

variable {E : Type} [Field E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Remaining ceremony normalization, with no probability estimate assumed.
The decoder must reconstruct the distribution of the actual complete log,
and its bad event must imply the salt intersection in that same execution.
The private budget prevents the address allocator from merging distinct blocks.
-/
def TreeRawSaltCeremonyRepresentation : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    let H := treeBatches settings tree * (C.t * termCount C)
    ∃ (α : Type) (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
      (decode : TreeRawSaltOutcome C H α → Bool × TreeSimLog C),
      IsQueryBoundP p TreeSimHashSaltPrivate H ∧
      IsQueryBoundP p treeSimHashSaltTableCharged (q + H) ∧
      𝒟[treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] =
        𝒟[decode <$> treeRawSaltRun prims H p] ∧
      ∀ r ∈ support (treeRawSaltRun prims H p),
        ¬ TreeSimHashCollision (decode r).2 → TreeSimSaltGuess D (decode r).2 →
          TreeRawSaltHit r

set_option backward.isDefEq.respectTransparency false in
/-- Exact A13 target from the remaining semantic representation. -/
theorem treeSimHashRawSaltEstimate_of_representation
    (representation : TreeRawSaltCeremonyRepresentation prims K circuits settings) :
    TreeSimHashRawSaltEstimate prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  obtain ⟨α, p, decode, _hprivate, hcount, hlaw, hevent⟩ :=
    representation hb top tree D A x z Z q hx hq hsmall
  have he := OracleComp.probEvent_congr'
    (p := fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)
    (q := fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)
    (fun _ _ => Iff.rfl) hlaw
  rw [he, probEvent_map]
  refine (ENNReal.toReal_mono (by exact probEvent_ne_top) ?_).trans
    (treeRawSalt_run_bound prims _ q (treeRawSalt_capacity_pos settings hb tree) p hcount)
  apply probEvent_mono
  intro r hr h
  exact hevent r hr h.1 h.2

/-- info: 'ThresholdLeanXmssSecurity.treeRawSalt_install_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeRawSalt_install_cached

/-- info: 'ThresholdLeanXmssSecurity.treeRawSalt_block_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeRawSalt_block_joint

/-- info: 'ThresholdLeanXmssSecurity.treeRawSalt_block_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeRawSalt_block_bind

/-- info: 'ThresholdLeanXmssSecurity.treeRawSalt_capacity_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeRawSalt_capacity_pos

/-- info: 'ThresholdLeanXmssSecurity.treeRawSalt_run_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeRawSalt_run_bound

/-- info: 'ThresholdLeanXmssSecurity.treeSimHashRawSaltEstimate_of_representation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHashRawSaltEstimate_of_representation

end ThresholdLeanXmssSecurity
