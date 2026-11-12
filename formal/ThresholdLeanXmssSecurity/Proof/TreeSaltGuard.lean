import ThresholdLeanXmssSecurity.Proof.TreeSaltReuse

/-!
# The guarded salt reuse estimate of the tree simulation hop

`TreeSaltReuse.lean` names three problems of `TreeSimSaltReuseEstimate`. This module fixes the
statement and shows that the fixed statement still gives the hash goal.

* `TreeSimHashBudgetCollision` is the collision over `TreeSimHashBudgetDomain`. This region also
  has the `.commit` and `.sharedKeys` inputs of the setups.
* `treeSimHash_logged_budget_birthday` bounds it with the certificate that already bounds
  `TreeSimHashCollision`. The certificate counts the fresh points of `TreeSimHashBudgetDomain`,
  so the bound stays `N (N - 1) / 2^257`.
* `TreeSimSaltReuseGuarded` bounds the salt reuse only outside the budget collision.
* `treeSimHashBoundGoal2_of_guarded` gives the hash goal from the guarded estimate. The budget
  collision replaces the old collision in the union, so the sum is the sum of
  `treeSimHashBoundGoal2_of_estimates`.

A separate budget collision term next to the old collision term does not fit. With
`N = q + S'`, each of the two terms is `N² / 2^257`, and the two terms together are the whole
budget `N² / 2^256`.

The guarded estimate conditions the run on the end of the PRSS setup.

* `treeSaltSetup_split` writes the logged real run as `treeSaltSetup` and then
  `treeSaltAfterSetup`. The split is the split of `treeSim_prssSetup_split`.
* `TreeSaltSetupAddresses` states that the setup fixes at most `treeBatches * termCount`
  addresses, and that each run with no budget collision reads salts only there. This needs the
  agreement of the honest holders on the key of each term and on the label of each batch.
* `TreeSaltSetupEager` states that the reuse after the setup is at most the eager bad event on
  these addresses.
* `treeSimSaltReuseGuarded_of_setup` averages over the setup and applies `treeSaltEager_bound`.

The two named statements require the same bridge from the ceremony to the salt
address program as `TreeSimHashRawSaltEstimate`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- One collision union over `TreeSimHashBudgetDomain`, which adds the setup commitments and the
setup echoes to `TreeSimHashDomain`. -/
def TreeSimHashBudgetCollision (log : TreeSimLog C) : Prop :=
  ∃ q r h, TreeSimHashBudgetDomain q ∧ TreeSimHashBudgetDomain r ∧ q ≠ r ∧
    TreeSimHashAnswer log q h ∧ TreeSimHashAnswer log r h

theorem treeSimHashBudgetCollision_of_collision (log : TreeSimLog C)
    (h : TreeSimHashCollision log) : TreeSimHashBudgetCollision log := by
  obtain ⟨q, r, u, hq, hr, hne, hqu, hru⟩ := h
  exact ⟨q, r, u, treeSimHash_domain_budget q hq, treeSimHash_domain_budget r hr, hne, hqu, hru⟩

theorem treeSimHashBudgetDomain_not_fixed (q : Query C) (h : TreeSimHashBudgetDomain q) :
    ¬ IsFixed q := by
  rintro ⟨input, rfl, _⟩
  simp [TreeSimHashBudgetDomain, TreeSimHashDomain] at h

/-- `TreeSimHashCoherent` on a region of queries with random answers. -/
def TreeSimHashRegionCoherent (P : Query C → Prop) (cache : HashCache C) (log : TreeSimLog C) :
    Prop :=
  ∀ q h, P q → TreeSimHashAnswer log q h → cache q = some h

theorem TreeSimHashRegionCoherent.mono {P : Query C → Prop} {cache next : HashCache C}
    {log : TreeSimLog C} (h : TreeSimHashRegionCoherent P cache log) (hle : cache ≤ next) :
    TreeSimHashRegionCoherent P next log := fun q u hq hu => hle (h q u hq hu)

theorem TreeSimHashRegionCoherent.append {P : Query C → Prop} {cache : HashCache C}
    {a b : TreeSimLog C} (ha : TreeSimHashRegionCoherent P cache a)
    (hb : TreeSimHashRegionCoherent P cache b) :
    TreeSimHashRegionCoherent P cache (a ++ b) := by
  intro q u hq hu
  rcases hu with hu | hu <;> rcases List.mem_append.mp hu with hu | hu
  · exact ha q u hq (Or.inl hu)
  · exact hb q u hq (Or.inl hu)
  · exact ha q u hq (Or.inr hu)
  · exact hb q u hq (Or.inr hu)

/-- `treeSimHash_local_log` on a region with no fixed query. -/
theorem treeSimHash_region_local_log (P : Query C → Prop) (hP : ∀ q, P q → ¬ IsFixed q)
    (D : C.Coalition)
    (t : (LocalSpec C + LocalSpec C).Domain) (cache : HashCache C × HiddenCache C)
    (r : (LocalSpec C + LocalSpec C).Range t × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (treeSimLocalWorld t)).run cache)) :
    cache.1 ≤ r.2.1 ∧ TreeSimHashRegionCoherent P r.2.1 (treeSimLocalLog t r.1) := by
  rcases t with (t | q | x) | (t | q | x)
  case inr.inr.inr =>
    by_cases hx : Hidden D x.1
    · simp [treeSimLocalWorld, streamWorld, onHash, hx] at hr
      obtain ⟨u, hu, rfl⟩ := hr
      refine ⟨le_refl _, ?_⟩
      intro q h hq ha
      simp [TreeSimHashAnswer, treeSimLocalLog] at ha
    · simp [treeSimLocalWorld, streamWorld, onHash, hx] at hr
      obtain ⟨u, hu, rfl⟩ := hr
      refine ⟨treeSimHash_local_mono prims (.inr (.inr x)) cache.1 _ hu, ?_⟩
      intro q h hq ha
      simp [TreeSimHashAnswer, treeSimLocalLog] at ha
  all_goals
    simp [treeSimLocalWorld, streamWorld, onHash] at hr
    obtain ⟨u, hu, rfl⟩ := hr
    refine ⟨?_, ?_⟩
    · first
      | exact treeSimHash_local_mono prims (.inl t) cache.1 _ hu
      | exact treeSimHash_local_mono prims (.inr (.inl q)) cache.1 _ hu
      | exact treeSimHash_local_mono prims (.inr (.inr x)) cache.1 _ hu
    intro q' h hq' ha
    simp only [TreeSimHashAnswer, treeSimLocalLog, List.mem_singleton] at ha
    rcases ha with he | he <;> cases he
  all_goals
    exact hashAnswer_cached prims (hP _ hq') cache.1 u hu

/-- `treeSimHash_local_coherent` on a region with no fixed query. -/
theorem treeSimHash_region_local_coherent (P : Query C → Prop) (hP : ∀ q, P q → ¬ IsFixed q)
    (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (hc : TreeSimHashRegionCoherent P s.1.1 s.2)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (simulateQ treeSimLocalWorld p)).run s)) :
    TreeSimHashRegionCoherent P r.2.1.1 r.2.2 := by
  induction p using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact hc
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    apply ih mid.1 mid.2 r _ hr
    rw [treeSimHash_logged_step, support_map] at hmid
    obtain ⟨u, hu, rfl⟩ := hmid
    have hs := treeSimHash_region_local_log prims P hP D t s.1 u hu
    exact (hc.mono hs.1).append hs.2

/-- `treeSimHash_normalized_coherent` on a region with no fixed query. -/
theorem treeSimHash_region_normalized_coherent (P : Query C → Prop)
    (hP : ∀ q, P q → ¬ IsFixed q) (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α)
    (hash : HashCache C) (hidden : HiddenCache C)
    (r : ((α × TreeSimLog C) × HiddenCache C) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      ((simulateQ (treeSimHashLocal D) (treeSimLocalLogged p)).run hidden)).run hash)) :
    TreeSimHashRegionCoherent P r.2 r.1.1.2 := by
  apply treeSimHash_region_local_coherent prims P hP D p ((hash, hidden), [])
    (r.1.1.1, (r.2, r.1.2), r.1.1.2)
  · intro q h hq hh
    simpa [TreeSimHashAnswer] using hh
  · rw [treeSimHash_state_normalize, support_map]
    exact ⟨r, hr, rfl⟩

/-- The certificate of `treeSimHash_logged_birthday_region` with the region
`TreeSimHashBudgetDomain` also bounds the collision over that region. -/
theorem treeSimHash_logged_budget_birthday (D : C.Coalition)
    {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α) (n : ℕ)
    (budget : TreeSimHashFreshBudget prims TreeSimHashBudgetDomain
      ((simulateQ (treeSimHashLocal D) (treeSimLocalLogged p)).run ∅) ∅ n) :
    Pr[fun r => TreeSimHashBudgetCollision r.2 |
      treeSimLoggedRun prims D (simulateQ treeSimLocalWorld p)] ≤
      ((n * (n - 1) : ℕ) : ℝ≥0∞) / (2 * 2 ^ 256) := by
  rw [treeSimHash_logged, probEvent_map, StateT.run'_eq, probEvent_map]
  refine le_trans ?_ (treeSimHash_fresh_birthday prims TreeSimHashBudgetDomain _ n budget)
  apply probEvent_mono
  intro r hr hbad
  have hc := treeSimHash_region_normalized_coherent prims TreeSimHashBudgetDomain
    treeSimHashBudgetDomain_not_fixed D p ∅ ∅ r hr
  obtain ⟨a, b, h, ha, hb, hne, hah, hbh⟩ := hbad
  exact ⟨a, b, h, h, hne,
    by simpa only [splitRegionCache, if_pos ha] using hc a h ha hah,
    by simpa only [splitRegionCache, if_pos hb] using hc b h hb hbh, HEq.rfl⟩

/-- The salt reuse outside the budget collision, as a birthday bound on the
`treeBatches * termCount` salt addresses. -/
def TreeSimSaltReuseGuarded : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    (Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)]).toReal ≤
      (((treeBatches settings tree * termCount C) ^ 2 : ℕ) : ℝ) / 2 ^ 257

/-- The union of `treeSimHash_union2` with the budget collision in place of the collision. -/
theorem treeSimHash_union_guarded {α : Type} (D : C.Coalition) (p : ProbComp (α × TreeSimLog C)) :
    (Pr[fun r => TreeSimHashBad2 D r.2 | p]).toReal ≤
      (Pr[fun r => TreeSimHashBudgetCollision r.2 | p]).toReal +
      (Pr[fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 | p]).toReal +
      (Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 | p]).toReal := by
  have h1 := probEvent_or_le p (fun r => TreeSimHashBudgetCollision r.2)
    (fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)
  have h2 := probEvent_or_le p
    (fun r => TreeSimHashBudgetCollision r.2 ∨ (¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2))
    (fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2)
  have hle : Pr[fun r => TreeSimHashBad2 D r.2 | p] ≤
      Pr[fun r => TreeSimHashBudgetCollision r.2 | p] +
      Pr[fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 | p] +
      Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 | p] := by
    refine le_trans (probEvent_mono ?_) (h2.trans (add_le_add h1 le_rfl))
    intro r _ h
    by_cases hb : TreeSimHashBudgetCollision r.2
    · exact Or.inl (Or.inl hb)
    rcases h with (hc | hg) | hu
    · exact (hb (treeSimHashBudgetCollision_of_collision _ hc)).elim
    · exact Or.inl (Or.inr ⟨fun hc => hb (treeSimHashBudgetCollision_of_collision _ hc), hg⟩)
    · exact Or.inr ⟨hb, hu⟩
  have hab := ENNReal.add_ne_top.mpr ⟨probEvent_ne_top (mx := p)
    (p := fun r => TreeSimHashBudgetCollision r.2), probEvent_ne_top (mx := p)
    (p := fun r => ¬ TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)⟩
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hab, probEvent_ne_top⟩) hle
  rwa [ENNReal.toReal_add hab probEvent_ne_top,
    ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at h

/-- The new hash goal from the honest count, the salt estimate and the guarded salt reuse
estimate. The sum is the sum of `treeSimHashBoundGoal2_of_estimates`. -/
theorem treeSimHashBoundGoal2_of_guarded
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseGuarded prims K circuits settings) :
    TreeSimHashBoundGoal2 prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  let N := q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)
  by_cases hlarge : 2 ^ 128 ≤ N
  · apply le_trans _ (treeSimHash_unit_budget _ hlarge)
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
      (probEvent_le_one (mx := treeSimTrace prims K circuits settings
        (treeSimEvents2 prims K circuits settings) top tree D A x z Z) (p := fun r => r.2.1 = true))
  have hn : N < 2 ^ 128 := Nat.lt_of_not_ge hlarge
  have cert := treeSimHash_terminal_fresh prims K circuits settings top tree D A x z Z q hq hn
    (treeSimHash_terminal_of_honest prims K circuits settings honest hb top tree D A x z Z q hx hq hn)
  have h := treeSimHash_logged_budget_birthday prims D
    (treeSimLocalRealGame K circuits settings top tree D A x z Z) N cert
  rw [treeSim_localReal_eq K circuits settings top tree D A x z Z] at h
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat, ENNReal.toReal_pow] at hreal
  have hc : (Pr[fun r => TreeSimHashBudgetCollision r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)]).toReal ≤
        ((N ^ 2 : ℕ) : ℝ) / (2 * 2 ^ 256) := by
    refine hreal.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    have hN : N * (N - 1) ≤ N ^ 2 := by
      simpa only [pow_two] using Nat.mul_le_mul_left N (Nat.sub_le N 1)
    exact_mod_cast hN
  rw [treeSimHash_flag2]
  refine (treeSimHash_union_guarded D _).trans ((add_le_add (add_le_add hc
    (salt hb top tree D A x z Z q hx hq hsmall)) (reuse hb top tree D A x z Z q hx hq hsmall)).trans ?_)
  simp only [N, Nat.cast_pow, Nat.cast_add]
  apply treeSimHash_union2_arith _ _ _ _ (by positivity) (by positivity) (by positivity)
  have hs : 2 * ((treeBatches settings tree * (C.t * termCount C) : ℕ) : ℝ) +
      2 * ((treeBatches settings tree * termCount C : ℕ) : ℝ) ≤
      ((treeSecrets circuits settings C tree - 2 * prssKeyCount C : ℕ) : ℝ) := by
    exact_mod_cast treeSimHash_reuse_capacity (C := C) circuits settings tree
  linarith

/-- The full hop from the old check goal, the two hash estimates and the guarded estimate. -/
theorem treeSimulationHop_of_guarded
    (stages : TreeSimStagesGoal2 prims K circuits settings)
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (reuse : TreeSimSaltReuseGuarded prims K circuits settings)
    (checkBound : TreeSimCheckBoundGoal prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHopClosed2 prims K circuits settings stages
    (treeSimHashBoundGoal2_of_guarded prims K circuits settings honest salt reuse)
    (treeSimCheckBoundGoal2_of_goal prims K circuits settings checkBound)

/-- The logged run from the start of the adversary to the end of the PRSS setup. -/
def treeSaltSetup (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) :
    ProbComp ((A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) := do
  let start ← (simulateQ (treeSimLoggedWorld prims D)
    (worldRoles.adversary (A.start (corruptInputs D x) z))).run ((∅, ∅), [])
  (executePhase (treeSimRealRoles prims D) D A noFunctionality setupRounds start.1
    (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run start.2

/-- The logged run after the PRSS setup, with the batches and the distinguisher. -/
def treeSaltAfterSetup (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    ProbComp (Bool × TreeSimLog C) := do
  let next ← (simulateQ (treeSimLoggedWorld prims D)
    (treeSimContinue (treeSimRealCont K circuits settings top tree x) p.1.2)).run p.2
  let out ← (executeRounds (treeSimRealRoles prims D) D A noFunctionality
    (ceremonyFuel circuits settings - setupRounds) p.1.1 next.1).run next.2
  treeSimRealObserve prims D A Z out

theorem treeSimLoggedRun_eq_run {α : Type} (D : C.Coalition) (p : OracleComp (WorldSpec C) α) :
    treeSimLoggedRun prims D p =
      (fun r => (r.1, r.2.2)) <$> (simulateQ (treeSimLoggedWorld prims D) p).run ((∅, ∅), []) := by
  rw [treeSimLoggedWorld_run]
  simp [treeSimLoggedRun, StateT.run'_eq, Functor.map_map]

/-- The logged real run is the PRSS setup followed by the rest of the run. -/
theorem treeSaltSetup_split (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z) =
      treeSaltSetup prims D A x z >>= treeSaltAfterSetup prims K circuits settings top tree D A x Z := by
  obtain ⟨fuel, hf⟩ : ∃ fuel, ceremonyFuel circuits settings = fuel + 3 :=
    ⟨ceremonyFuel circuits settings - 3, by simp only [ceremonyFuel, setupRounds]; omega⟩
  have hs : ceremonyFuel circuits settings - setupRounds = fuel := by
    simp only [hf, setupRounds]; omega
  have hc : (fun i => ceremony K circuits settings i (x i) top tree) =
      fun i => prssSetup i >>= treeSimRealCont K circuits settings top tree x i := rfl
  rw [treeSimLoggedRun_eq_run]
  unfold treeRealGame distinguish realExecution treeSaltSetup treeSaltAfterSetup
  simp only [simulateQ_bind, StateT.run_bind, map_bind, bind_assoc, hs]
  apply bind_congr
  intro start
  rw [simulateQ_executePhase, hf, hc, treeSim_prssSetup_split]
  simp only [treeSimRealRoles, treeSimRealObserve, StateT.run_bind, bind_assoc]
  rfl

/-- The eager birthday bound with at most `N` addresses. -/
theorem treeSaltEager_le {n N : ℕ} (hn : n ≤ N) (hidden : Fin n → Prop)
    (known : Fin n → Fin 256 → Bit) :
    Pr[TreeSaltEagerBad hidden known | $ᵗ (Fin n → Fin 256 → Bit)] ≤
      ((N ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
  refine (treeSaltEager_bound hidden known).trans ?_
  have hN : 2 * ({x | x.1 < x.2} : Finset (Fin n × Fin n)).card ≤ N ^ 2 :=
    (treeSaltPairs_card n).trans (Nat.pow_le_pow_left hn 2)
  rw [ENNReal.le_div_iff_mul_le (by simp) (by simp),
    show (2 : ℝ≥0∞) ^ 257 = 2 * 2 ^ 256 from pow_succ' 2 256, ← mul_assoc,
    mul_comm _ (2 : ℝ≥0∞), mul_assoc, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
  exact_mod_cast hN

/-- The salt addresses of the honest index-2 term reads in a log lie in the range of `addr`. -/
def TreeSaltAddressesCover {n : ℕ} (addr : Fin n → C.Term × HashOutput × ℕ)
    (log : TreeSimLog C) : Prop :=
  ∀ (T : C.Term) (key : HashOutput) (label g : ℕ) (b : Bit),
    (⟨.inr (.inr (.inr (.term T, key, label, 2, g))), b⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log → ∃ i, addr i = (T, key, label)

/-- The end of the PRSS setup fixes at most `treeBatches * termCount` salt addresses. Each run
after the setup with no budget collision reads salts only at these addresses. The honest holders
of a term agree on its key by the echo, and on its label in each batch. -/
def TreeSaltSetupAddresses : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput), DealtInputs D x →
    ∀ p ∈ support (treeSaltSetup prims D A x z),
    ∃ (n : ℕ) (addr : Fin n → C.Term × HashOutput × ℕ),
      Function.Injective addr ∧ n ≤ treeBatches settings tree * termCount C ∧
      ∀ r ∈ support (treeSaltAfterSetup prims K circuits settings top tree D A x Z p),
        ¬ TreeSimHashBudgetCollision r.2 → TreeSaltAddressesCover addr r.2

/-- After the PRSS setup, the salts at a fixed set of addresses are as in the eager model. The
hidden salts are uniform and independent. The known salts come from the lazy `.streamKey` points,
which the first batch reads before any hidden salt, so they are independent of the hidden salts. -/
def TreeSaltSetupEager : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSaltSetup prims D A x z),
    ∀ (n : ℕ) (addr : Fin n → C.Term × HashOutput × ℕ), Function.Injective addr →
      (∀ r ∈ support (treeSaltAfterSetup prims K circuits settings top tree D A x Z p),
        ¬ TreeSimHashBudgetCollision r.2 → TreeSaltAddressesCover addr r.2) →
      ∃ known : Fin n → Fin 256 → Bit,
        Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 |
          treeSaltAfterSetup prims K circuits settings top tree D A x Z p] ≤
          Pr[TreeSaltEagerBad (fun i => ¬ KnownTo D.1 (addr i).1) known |
            $ᵗ (Fin n → Fin 256 → Bit)]

/-- The guarded estimate from the setup addresses and the eager model after the setup. -/
theorem treeSimSaltReuseGuarded_of_setup
    (addresses : TreeSaltSetupAddresses prims K circuits settings)
    (eager : TreeSaltSetupEager prims K circuits settings) :
    TreeSimSaltReuseGuarded prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  have hle : Pr[fun r => ¬ TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 |
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] ≤
      (((treeBatches settings tree * termCount C) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
    rw [treeSaltSetup_split]
    apply probEvent_bind_le_of_forall_le
    intro p hp
    obtain ⟨n, addr, hinj, hn, hcover⟩ := addresses hb top tree D A x z Z hx p hp
    obtain ⟨known, hk⟩ := eager hb top tree D A x z Z q hx hq hsmall p hp n addr hinj hcover
    exact hk.trans (treeSaltEager_le hn _ known)
  refine (ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)) hle).trans_eq ?_
  simp [ENNReal.toReal_div]

/-- The full hop from the old check goal, the two hash estimates, the setup addresses and the
eager model after the setup. -/
theorem treeSimulationHop_of_setup
    (stages : TreeSimStagesGoal2 prims K circuits settings)
    (honest : TreeSimHashHonestBudget prims K circuits settings)
    (salt : TreeSimHashRawSaltEstimate prims K circuits settings)
    (addresses : TreeSaltSetupAddresses prims K circuits settings)
    (eager : TreeSaltSetupEager prims K circuits settings)
    (checkBound : TreeSimCheckBoundGoal prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) :=
  treeSimulationHop_of_guarded prims K circuits settings stages honest salt
    (treeSimSaltReuseGuarded_of_setup prims K circuits settings addresses eager) checkBound

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_logged_budget_birthday' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_logged_budget_birthday

/-- info: 'ThresholdLeanXmssSecurity.treeSimHash_union_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHash_union_guarded

/-- info: 'ThresholdLeanXmssSecurity.treeSimHashBoundGoal2_of_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimHashBoundGoal2_of_guarded

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHop_of_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_guarded

/-- info: 'ThresholdLeanXmssSecurity.treeSaltSetup_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSaltSetup_split

/-- info: 'ThresholdLeanXmssSecurity.treeSaltEager_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSaltEager_le

/-- info: 'ThresholdLeanXmssSecurity.treeSimSaltReuseGuarded_of_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimSaltReuseGuarded_of_setup

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHop_of_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimulationHop_of_setup

end ThresholdLeanXmssSecurity
