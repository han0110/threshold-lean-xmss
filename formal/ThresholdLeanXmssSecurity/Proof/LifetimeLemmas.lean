import ThresholdLeanXmssSecurity.Proof.TreeKeyFromCache
import ThresholdLeanXmssSecurity.Proof.Signing

/-!
# Lemmas of the lifetime claim

These are the lemmas of Stage A2 of `FIX.md` that need neither the Stage A1 draft nor an open gap.
They use only the definitions of `Scheme.lean`, `Ideal.lean` and `Statement.lean`.

* A2 item 3, averaging over `Th`.
  * `mpcInput_finite` shows that the inputs that the MPC evaluates are finite (A0 item 4).
  * `probEvent_bind_toReal_eq_sum` writes a run with a sampled `Th` as the average of the runs with
    a fixed `Th`. `probEvent_bind_toReal_le_sum` and `abs_probEvent_bind_sub_le_sum` average a
    bound, and `abs_probEvent_bind_sub_le_of_forall_th` applies it to every `Th` that the circuits
    compute. `abs_probEvent_bind_sub_le_of_forall_th_const` gives a constant bound.
* A2 item 5, retries.
  * `roRun_rerun` and `dealerCeremony_rerun` show that a run of `F_tree` from a larger cache gives the
    same tree and the same openings. So retries give one output and abort together (D7).
  * `abs_sub_le_sum_of_hybrid` adds the losses of a sequence of hybrids, and
    `sum_runs_le_attempts` groups them by tree with at most `attempts` runs each.
* A2 item 4, local programming.
  * `localTableWorld` answers `H` and the programming at the `.derive .keygen` points from a local
    lazy table, and sends every other call to the game.
  * `localTableWorld_run` shows that it gives the same outputs and the same merged cache as the world
    on one cache, for `localAnswer` and for `signingLocalAnswer` (`localTable_hashAnswer`,
    `localTable_randomOracle`). The costs are not part of the statement.
  * The reduction can run it in `tsigGame` when two facts hold. The simulators program only keygen
    points (A0 item 3), and the signing game makes no call at a keygen point.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## Averaging over `Th` -/

/-- The inputs that the MPC evaluates are finite. The proof is the one of the `Fintype MpcDomain`
instance of the Stage A1 draft (`formal/LifetimeDraft.lean`). -/
theorem mpcInput_finite : {input | MpcInput input}.Finite := by
  have : {input | MpcInput input} =
      Set.range (fun a : PublicParameter × Layer × KeyIndex × ChainStep × ChainIndex × Digest =>
        tweakableHashInput a.1 (.chain a.2.1 a.2.2.1 a.2.2.2.1) (Concrete.chainPayload a.2.2.2.2.1 a.2.2.2.2.2)) ∪
      Set.range (fun a : PublicParameter × KeyIndex × Digest => commitmentInput a.1 a.2.1 a.2.2) := by
    ext input
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_range, Prod.exists, MpcInput]
    constructor
    · rintro (⟨p, lay, key, step, l, value, rfl⟩ | ⟨p, e, ρ, rfl⟩)
      · exact .inl ⟨p, lay, key, step, l, value, rfl⟩
      · exact .inr ⟨p, e, ρ, rfl⟩
    · rintro (⟨p, lay, key, step, l, value, rfl⟩ | ⟨p, e, ρ, rfl⟩)
      · exact .inl ⟨p, lay, key, step, l, value, rfl⟩
      · exact .inr ⟨p, e, ρ, rfl⟩
  rw [this]
  exact (Set.finite_range _).union (Set.finite_range _)

section Average

variable {V β : Type}

/-- The probability of an event after a sample `v` is the average over `v` of its probability. -/
theorem probEvent_bind_toReal_eq_sum [Fintype V] (mx : ProbComp V) (g : V → ProbComp β) (p : β → Prop) :
    (Pr[p | mx >>= g]).toReal = ∑ v, (Pr[= v | mx]).toReal * (Pr[p | g v]).toReal := by
  rw [probEvent_bind_eq_sum_fintype, ENNReal.toReal_sum fun v _ => ENNReal.mul_ne_top probOutput_ne_top probEvent_ne_top]
  simp only [ENNReal.toReal_mul]

/-- If a bound holds for each sample, the average of the bounds holds for the sampled run. -/
theorem probEvent_bind_toReal_le_sum [Fintype V] (mx : ProbComp V) (g : V → ProbComp β) (p : β → Prop)
    (ε : V → ℝ) (h : ∀ v, (Pr[p | g v]).toReal ≤ ε v) :
    (Pr[p | mx >>= g]).toReal ≤ ∑ v, (Pr[= v | mx]).toReal * ε v := by
  rw [probEvent_bind_toReal_eq_sum]
  exact Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (h v) ENNReal.toReal_nonneg

/-- If a distance bound holds for each sample, the average of the bounds holds for the sampled
runs. -/
theorem abs_probEvent_bind_sub_le_sum [Fintype V] (mx : ProbComp V) (f g : V → ProbComp β) (p : β → Prop)
    (ε : V → ℝ) (h : ∀ v, |(Pr[p | f v]).toReal - (Pr[p | g v]).toReal| ≤ ε v) :
    |(Pr[p | mx >>= f]).toReal - (Pr[p | mx >>= g]).toReal| ≤ ∑ v, (Pr[= v | mx]).toReal * ε v := by
  rw [probEvent_bind_toReal_eq_sum, probEvent_bind_toReal_eq_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (h v) ENNReal.toReal_nonneg

/-- The average of a constant bound is at most the bound. -/
theorem sum_probOutput_mul_const_le [Fintype V] (mx : ProbComp V) {ε : ℝ} (hε : 0 ≤ ε) :
    ∑ v, (Pr[= v | mx]).toReal * ε ≤ ε := by
  rw [← Finset.sum_mul]
  refine mul_le_of_le_one_left hε ?_
  rw [← ENNReal.toReal_sum fun v _ => probOutput_ne_top, ← tsum_fintype (L := SummationFilter.unconditional V)]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simp)

/-- A distance bound that holds for every fixed `Th` that the circuits compute holds for a sampled
`Th`, with the average of the bounds. The sample `v` gives `Th` as `mk v`, as `thOf` of the Stage A1
draft does. -/
theorem abs_probEvent_bind_sub_le_of_forall_th [Fintype V] (circuitsOf : (HashInput → HashOutput) → Circuits)
    (mk : V → HashInput → HashOutput) (mx : ProbComp V) (f g : (HashInput → HashOutput) → ProbComp β)
    (p : β → Prop) (ε : (HashInput → HashOutput) → ℝ) (hcomp : ∀ Th, CircuitsCompute (circuitsOf Th) Th)
    (h : ∀ Th, CircuitsCompute (circuitsOf Th) Th → |(Pr[p | f Th]).toReal - (Pr[p | g Th]).toReal| ≤ ε Th) :
    |(Pr[p | mx >>= fun v => f (mk v)]).toReal - (Pr[p | mx >>= fun v => g (mk v)]).toReal| ≤
      ∑ v, (Pr[= v | mx]).toReal * ε (mk v) :=
  abs_probEvent_bind_sub_le_sum mx _ _ p _ fun v => h (mk v) (hcomp (mk v))

/-- A distance bound with a constant error that holds for every fixed `Th` that the circuits compute
holds for a sampled `Th`. -/
theorem abs_probEvent_bind_sub_le_of_forall_th_const [Fintype V] (circuitsOf : (HashInput → HashOutput) → Circuits)
    (mk : V → HashInput → HashOutput) (mx : ProbComp V) (f g : (HashInput → HashOutput) → ProbComp β)
    (p : β → Prop) {ε : ℝ} (hε : 0 ≤ ε) (hcomp : ∀ Th, CircuitsCompute (circuitsOf Th) Th)
    (h : ∀ Th, CircuitsCompute (circuitsOf Th) Th → |(Pr[p | f Th]).toReal - (Pr[p | g Th]).toReal| ≤ ε) :
    |(Pr[p | mx >>= fun v => f (mk v)]).toReal - (Pr[p | mx >>= fun v => g (mk v)]).toReal| ≤ ε :=
  (abs_probEvent_bind_sub_le_of_forall_th circuitsOf mk mx f g p (fun _ => ε) hcomp h).trans
    (sum_probOutput_mul_const_le mx hε)

end Average

/-! ## Retries -/

section Retries

variable (prims : Primitives)

/-- A random-oracle computation that runs again from a larger cache gives the same output. The
second start cache `s'` contains the final cache of the first run. Anything that only adds entries
can run between the two runs. -/
theorem roRun_rerun {α : Type} (oa : OracleComp (RoSpec C) α) {s s' : HashCache C}
    {z₁ z₂ : α × HashCache C} (h₁ : z₁ ∈ support (roRun prims oa s)) (hle : z₁.2 ≤ s') (hs' : NoMpc s')
    (h₂ : z₂ ∈ support (roRun prims oa s')) : z₂.1 = z₁.1 := by
  obtain ⟨hle₂, hn₂, hd₂⟩ := roRun_support prims oa s' z₂ h₂
  obtain ⟨-, -, hd₁⟩ := roRun_support prims oa s z₁ h₁
  have hagree := agrees_hashOf prims (hn₂ hs')
  rw [hd₂ _ (good_hashOf prims _) hagree,
    hd₁ _ (good_hashOf prims _) fun q v hq => hagree q v (hle₂ (hle hq))]

/-- All runs of `F_tree` for one tree on the same keys give the same tree and the same openings,
from any larger cache. So the adversary cannot choose between the outputs of retries, and the
retries abort together. Only the receivers of each run can differ. -/
theorem dealerCeremony_rerun (circuits : Circuits) (settings : Settings) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) {s s' : HashCache C}
    {z₁ z₂ : (Option TreeOutput × List (List (List Bit))) × HashCache C}
    (h₁ : z₁ ∈ support (roRun prims (dealerCeremony circuits settings parameter seeds top tree) s))
    (hle : z₁.2 ≤ s') (hs' : NoMpc s')
    (h₂ : z₂ ∈ support (roRun prims (dealerCeremony circuits settings parameter seeds top tree) s')) :
    z₂.1 = z₁.1 :=
  roRun_rerun prims _ h₁ hle hs' h₂

end Retries

/-- The hybrid argument. The distance between the first and the last of a sequence of games is at
most the sum of the distances of neighbors. -/
theorem abs_sub_le_sum_of_hybrid (p : ℕ → ℝ) (n : ℕ) (ε : ℕ → ℝ) (h : ∀ k < n, |p k - p (k + 1)| ≤ ε k) :
    |p 0 - p n| ≤ ∑ k ∈ Finset.range n, ε k := by
  have := dist_le_range_sum_of_dist_le (f := p) n (d := ε) fun hk => by rw [Real.dist_eq]; exact h _ hk
  rwa [Real.dist_eq] at this

/-- The losses of the runs add up by tree. If run `k` is a run of tree `treeOf k` with loss at most
`e (treeOf k)`, and each tree has at most `attempts` runs, the sum is at most `attempts * e` over
the trees. -/
theorem sum_runs_le_attempts {τ : Type} [Fintype τ] [DecidableEq τ] (treeOf : ℕ → τ) (n attempts : ℕ)
    (e : τ → ℝ) (he : ∀ b, 0 ≤ e b)
    (hruns : ∀ b, ((Finset.range n).filter fun k => treeOf k = b).card ≤ attempts) :
    ∑ k ∈ Finset.range n, e (treeOf k) ≤ ∑ b, (attempts : ℝ) * e b := by
  rw [← Finset.sum_fiberwise (Finset.range n) treeOf]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [Finset.sum_congr rfl fun k hk => by rw [(Finset.mem_filter.mp hk).2], Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hruns b) (he b)

/-! ## Local programming -/

section LocalTable

/-- The points that `keygenSimulator` programs. -/
def KeygenPoint : Query C → Prop
  | .derive .keygen _ _ => True
  | _ => False

/-- The cache with the points of `P` from `a` and every other point from `b`. -/
def mergeOn (P : Query C → Prop) (a b : HashCache C) : HashCache C := fun q => if P q then a q else b q

/-- A step on the cache reads and writes only the points of `P`. It then runs the same on the part
of `P` alone and on a merged cache. -/
def Frames (P : Query C → Prop) {α : Type} (m : StateT (HashCache C) ProbComp α) : Prop :=
  ∀ a b, (fun r => (r.1, mergeOn P r.2 b)) <$> m.run a = m.run (mergeOn P a b)

theorem mergeOn_not (P : Query C → Prop) (a b : HashCache C) :
    mergeOn (fun q => ¬ P q) b a = mergeOn P a b := by
  funext q
  by_cases h : P q <;> simp [mergeOn, h]

theorem mergeOn_cacheQuery {P : Query C → Prop} {q : Query C} (hq : P q) (a b : HashCache C) (u : HashOutput) :
    mergeOn P (a.cacheQuery q u) b = (mergeOn P a b).cacheQuery q u := by
  funext q'
  by_cases h : q' = q
  · subst h; simp [mergeOn, hq]
  · by_cases hp : P q' <;> simp [mergeOn, hp, h]

theorem frames_pure (P : Query C → Prop) {α : Type} (x : α) : Frames P (pure x : StateT (HashCache C) ProbComp α) := by
  intro a b; simp

theorem frames_lift (P : Query C → Prop) {α : Type} (p : ProbComp α) :
    Frames P (StateT.lift p : StateT (HashCache C) ProbComp α) := by
  intro a b; simp

theorem frames_bind (P : Query C → Prop) {α β : Type} {m : StateT (HashCache C) ProbComp α}
    {f : α → StateT (HashCache C) ProbComp β} (hm : Frames P m) (hf : ∀ x, Frames P (f x)) : Frames P (m >>= f) := by
  intro a b
  rw [StateT.run_bind, StateT.run_bind, ← hm, map_bind, bind_map_left]
  exact bind_congr fun r => hf r.1 r.2 b

theorem frames_randomOracle {P : Query C → Prop} {q : Query C} (hq : P q) :
    Frames P ((Query C →ₒ HashOutput).randomOracle q) := by
  intro a b
  have hmerge : mergeOn P a b q = a q := by simp [mergeOn, hq]
  cases h : a q with
  | some u =>
    rw [QueryImpl.withCaching_run_some _ h, QueryImpl.withCaching_run_some _ (hmerge.trans h)]
    simp
  | none =>
    rw [QueryImpl.withCaching_run_none _ h, QueryImpl.withCaching_run_none _ (hmerge.trans h), Functor.map_map]
    simp only [mergeOn_cacheQuery hq]

theorem frames_programAnswer {P : Query C → Prop} (x : Query C × HashOutput) (hx : P x.1) :
    Frames P (programAnswer (C := C) x) := by
  intro a b
  have hmerge : mergeOn P a b x.1 = a x.1 := by simp [mergeOn, hx]
  simp only [programAnswer, StateT.run_bind, StateT.run_get, pure_bind, hmerge]
  split_ifs <;> simp [mergeOn_cacheQuery hx]

/-- A step on the local table of the reduction. -/
def onKeygenTable {α : Type} (m : StateT (HashCache C) ProbComp α) : StateT (HashCache C × HashCache C) ProbComp α :=
  StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$> m.run s.1

/-- A step on the cache of the game. -/
def onGameCache {α : Type} (m : StateT (HashCache C) ProbComp α) : StateT (HashCache C × HashCache C) ProbComp α :=
  StateT.mk fun s => (fun r => (r.1, (s.1, r.2))) <$> m.run s.2

/-- The state of the reduction and of the game as one cache. -/
def mergedCache (s : HashCache C × HashCache C) : HashCache C := mergeOn KeygenPoint s.1 s.2

theorem onKeygenTable_run {α : Type} {m : StateT (HashCache C) ProbComp α} (hm : Frames KeygenPoint m)
    (s : HashCache C × HashCache C) :
    Prod.map id mergedCache <$> (onKeygenTable m).run s = m.run (mergedCache s) := by
  rw [mergedCache, ← hm]
  simp [onKeygenTable, mergedCache, Functor.map_map]

theorem onGameCache_run {α : Type} {m : StateT (HashCache C) ProbComp α} (hm : Frames (fun q => ¬ KeygenPoint q) m)
    (s : HashCache C × HashCache C) :
    Prod.map id mergedCache <$> (onGameCache m).run s = m.run (mergedCache s) := by
  rw [mergedCache, ← mergeOn_not, ← hm]
  simp [onGameCache, mergedCache, Functor.map_map, mergeOn_not]

variable (prims : Primitives)

/-- The local oracles with the implementation `hash` of `H`. `localAnswer` takes `hashAnswer`, and
`signingLocalAnswer` takes the lazy random oracle. -/
def localWith (hash : QueryImpl (Query C →ₒ HashOutput) (StateT (HashCache C) ProbComp)) :
    QueryImpl (LocalSpec C) (StateT (HashCache C) ProbComp) :=
  unifFwdImpl (Query C →ₒ HashOutput) + (hash + prgAnswer (C := C) prims)

/-- The world on one cache, without the costs. `world` and `signingWorld` add costs to it. -/
def worldWith (hash : QueryImpl (Query C →ₒ HashOutput) (StateT (HashCache C) ProbComp)) :
    QueryImpl (WorldSpec C) (StateT (HashCache C) ProbComp) :=
  localWith prims hash + programAnswer (C := C) + localWith prims hash

/-- The reduction answers `H` and the programming at the keygen points from its local lazy table.
Every other call goes to the game. -/
def localTableLocal (hash : QueryImpl (Query C →ₒ HashOutput) (StateT (HashCache C) ProbComp)) :
    QueryImpl (LocalSpec C) (StateT (HashCache C × HashCache C) ProbComp) :=
  (fun t => onGameCache (unifFwdImpl (Query C →ₒ HashOutput) t)) +
    ((fun q => if KeygenPoint q then onKeygenTable ((Query C →ₒ HashOutput).randomOracle q) else onGameCache (hash q)) +
      fun x => onGameCache (prgAnswer (C := C) prims x))

/-- The world of the reduction with its local table. -/
def localTableWorld (hash : QueryImpl (Query C →ₒ HashOutput) (StateT (HashCache C) ProbComp)) :
    QueryImpl (WorldSpec C) (StateT (HashCache C × HashCache C) ProbComp) :=
  localTableLocal prims hash +
    (fun x => if KeygenPoint x.1 then onKeygenTable (programAnswer (C := C) x) else onGameCache (programAnswer (C := C) x)) +
    localTableLocal prims hash

theorem frames_hashAnswer {q : Query C} (hq : ¬ KeygenPoint q) :
    Frames (fun q => ¬ KeygenPoint q) (hashAnswer (C := C) prims q) := by
  cases q with
  | hash input =>
    change Frames _ (if MpcInput input then pure (prims.Th input) else _)
    split_ifs
    · exact frames_pure _ _
    · exact frames_randomOracle (P := fun q => ¬ KeygenPoint q) hq
  | _ => exact frames_randomOracle (P := fun q => ¬ KeygenPoint q) hq

theorem frames_prgAnswer (x : PrgInput C) : Frames (fun q => ¬ KeygenPoint q) (prgAnswer (C := C) prims x) :=
  frames_bind _ (frames_hashAnswer prims (q := .streamKey x.2.1) id) fun _ => frames_pure _ _

theorem localTableLocal_run (hash : QueryImpl (Query C →ₒ HashOutput) (StateT (HashCache C) ProbComp))
    (hkeygen : ∀ q, KeygenPoint q → hash q = (Query C →ₒ HashOutput).randomOracle q)
    (hother : ∀ q, ¬ KeygenPoint q → Frames (fun q => ¬ KeygenPoint q) (hash q))
    (t : (LocalSpec C).Domain) (s : HashCache C × HashCache C) :
    Prod.map id mergedCache <$> (localTableLocal prims hash t).run s = (localWith prims hash t).run (mergedCache s) := by
  rcases t with u | q | x
  · exact onGameCache_run (frames_lift _ _) s
  · change Prod.map id mergedCache <$> (if KeygenPoint q then onKeygenTable _ else onGameCache (hash q)).run s = (hash q).run _
    split_ifs with hq
    · rw [hkeygen q hq]; exact onKeygenTable_run (frames_randomOracle hq) s
    · exact onGameCache_run (hother q hq) s
  · exact onGameCache_run (frames_prgAnswer prims x) s

/-- The view equality of the local table. The world of the reduction, which answers `H` and the
programming at the keygen points from its local table, gives the same outputs and the same merged
cache as the world on one cache. -/
theorem localTableWorld_run (hash : QueryImpl (Query C →ₒ HashOutput) (StateT (HashCache C) ProbComp))
    (hkeygen : ∀ q, KeygenPoint q → hash q = (Query C →ₒ HashOutput).randomOracle q)
    (hother : ∀ q, ¬ KeygenPoint q → Frames (fun q => ¬ KeygenPoint q) (hash q))
    {α : Type} (oa : OracleComp (WorldSpec C) α) (s : HashCache C × HashCache C) :
    Prod.map id mergedCache <$> (simulateQ (localTableWorld prims hash) oa).run s =
      (simulateQ (worldWith prims hash) oa).run (mergedCache s) := by
  refine map_run_simulateQ_eq_of_query_map_eq _ _ mergedCache (fun t s => ?_) oa s
  rcases t with (t | x) | t
  · exact localTableLocal_run prims hash hkeygen hother t s
  · change Prod.map id mergedCache <$> (if KeygenPoint x.1 then onKeygenTable _ else onGameCache _).run s = _
    split_ifs with hx
    · exact onKeygenTable_run (frames_programAnswer x hx) s
    · exact onGameCache_run (frames_programAnswer (P := fun q => ¬ KeygenPoint q) x hx) s
  · exact localTableLocal_run prims hash hkeygen hother t s

/-- From empty caches, the reduction with its local table gives the outputs of the world on one
cache. -/
theorem localTableWorld_run'_empty (hash : QueryImpl (Query C →ₒ HashOutput) (StateT (HashCache C) ProbComp))
    (hkeygen : ∀ q, KeygenPoint q → hash q = (Query C →ₒ HashOutput).randomOracle q)
    (hother : ∀ q, ¬ KeygenPoint q → Frames (fun q => ¬ KeygenPoint q) (hash q))
    {α : Type} (oa : OracleComp (WorldSpec C) α) :
    (simulateQ (localTableWorld prims hash) oa).run' (∅, ∅) = (simulateQ (worldWith prims hash) oa).run' ∅ := by
  have hempty : mergedCache ((∅, ∅) : HashCache C × HashCache C) = ∅ := by
    funext q; simp [mergedCache, mergeOn]
  have h := congrArg (Prod.fst <$> ·) (localTableWorld_run prims hash hkeygen hother oa (∅, ∅))
  simp only [Functor.map_map, Prod.map_fst, id_eq, hempty] at h
  simpa [StateT.run'_eq] using h

/-- The world of the ceremony claims, `localAnswer` with the programming, satisfies the hypotheses of
`localTableWorld_run`. -/
theorem localTable_hashAnswer :
    (∀ q, KeygenPoint q → hashAnswer (C := C) prims q = (Query C →ₒ HashOutput).randomOracle q) ∧
      ∀ q, ¬ KeygenPoint q → Frames (fun q => ¬ KeygenPoint q) (hashAnswer (C := C) prims q) := by
  refine ⟨fun q hq => ?_, fun q hq => frames_hashAnswer prims hq⟩
  cases q with
  | hash input => exact hq.elim
  | _ => rfl

/-- The world of the signing claim, `signingLocalAnswer` with the programming, satisfies the
hypotheses of `localTableWorld_run`. -/
theorem localTable_randomOracle :
    (∀ q, KeygenPoint q → (Query C →ₒ HashOutput).randomOracle q = (Query C →ₒ HashOutput).randomOracle q) ∧
      ∀ q, ¬ KeygenPoint q → Frames (fun q => ¬ KeygenPoint q) ((Query C →ₒ HashOutput).randomOracle q) :=
  ⟨fun _ _ => rfl, fun _ hq => frames_randomOracle (P := fun q => ¬ KeygenPoint q) hq⟩

theorem localWith_hashAnswer : localWith (C := C) prims (hashAnswer prims) = localAnswer prims := rfl

theorem localWith_randomOracle :
    localWith (C := C) prims (Query C →ₒ HashOutput).randomOracle = signingLocalAnswer prims := rfl

end LocalTable

/-- info: 'ThresholdLeanXmssSecurity.mpcInput_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mpcInput_finite

/-- info: 'ThresholdLeanXmssSecurity.probEvent_bind_toReal_le_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms probEvent_bind_toReal_le_sum

/-- info: 'ThresholdLeanXmssSecurity.abs_probEvent_bind_sub_le_of_forall_th' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_probEvent_bind_sub_le_of_forall_th

/-- info: 'ThresholdLeanXmssSecurity.abs_probEvent_bind_sub_le_of_forall_th_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_probEvent_bind_sub_le_of_forall_th_const

/-- info: 'ThresholdLeanXmssSecurity.sum_probOutput_mul_const_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_probOutput_mul_const_le

/-- info: 'ThresholdLeanXmssSecurity.dealerCeremony_rerun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dealerCeremony_rerun

/-- info: 'ThresholdLeanXmssSecurity.abs_sub_le_sum_of_hybrid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms abs_sub_le_sum_of_hybrid

/-- info: 'ThresholdLeanXmssSecurity.sum_runs_le_attempts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sum_runs_le_attempts

/-- info: 'ThresholdLeanXmssSecurity.localTableWorld_run'_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms localTableWorld_run'_empty

/-- info: 'ThresholdLeanXmssSecurity.localTable_hashAnswer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms localTable_hashAnswer

/-- info: 'ThresholdLeanXmssSecurity.localTable_randomOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms localTable_randomOracle

end ThresholdLeanXmssSecurity
