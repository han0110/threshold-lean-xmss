import ThresholdLeanXmssSecurity.Proof.LifetimeIdealKeyLink
import ThresholdLeanXmssSecurity.Proof.LifetimeRunBoundary
import ThresholdLeanXmssSecurity.Proof.TreeKeyStages

/-!
# The fresh-answer part of the key overlap in the left world

This module cuts the left world `(simulateQ (leftImpl …) (program4 … n)).run idealStart` of hop
`n` right after run `n` samples its parts, and it bounds the key overlap at one hidden name.

* `setupCut` runs `program4` up to the admitted start of run `n` (`runTo` with `StartStop`) and
  then samples the first setup data of run `n` by `prssInitialData` on the target copy. `tailCut`
  runs the rest and the win test. `program4_cut` states that `program4` is `setupCut` followed by
  `tailCut`.
* `setupCut_inv` gives the key-link invariant at each supported cut. When run `n` has started,
  the parts of run `n` in the history are the sampled parts. When run `n` has not started, the
  second table stays empty (`tail_none`).
* `tail_overlap` uses the frozen first table (`loop_frozen`) and the final tables. A key overlap
  at the end is a collision of the final answer at the run-`n` input with the final answer at the
  input of an earlier run `m < n`. The cut already caches that earlier input.
* `prob_collision_left` is `prob_collision_le` in the left world. The tables do not change the hash
  cache, so `collisionPotential` does not grow over one call (`leftImpl_potential`).
* `tail_fresh` gives at most `n / 2 ^ 256` from a cut where the run-`n` input is not cached.
  `keyOverlap_le_early` adds the chance `RunEarlyCached` that the cut caches it.
* `RunEarlyCachedBound` is the early-cache estimate `Q / 2 ^ 256` on the cut, with the premises of
  `HiddenKeyOverlapBound`. `hiddenKeyOverlapBound_of_early` gives `HiddenKeyOverlapBound` from
  it, since `n ≤ lifetimeRuns attempts - 1`.

`prssInitialData` makes only `.commit` queries, so the sample adds no `.derive` input to the cache.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

namespace ThresholdLeanXmssSecurity.LifetimeIdealOverlapFinal

open LifetimePrfTransportProof LifetimeIdealBad LifetimeEmulatedBudget LifetimeIdealKeyLink

attribute [local instance] Classical.propDecidable

section Potential

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

theorem onCache_potential {x y : Query C} (hx : ∃ ph k v, x = .derive ph k v)
    (hy : ∃ ph k v, y = .derive ph k v) (hxy : x ≠ y) (t : (LocalSpec C).Domain) (s : IdealState C) :
    ∑' r, Pr[= r | (onCache (localAnswer prims t)).run s] * collisionPotential x y r.2.1 ≤
      collisionPotential x y s.1 := by
  change ∑' r, Pr[= r | (fun r => (r.1, (r.2, s.2))) <$> (localAnswer prims t).run s.1] *
    collisionPotential x y r.2.1 ≤ _
  rw [tsum_probOutput_map_mul]
  exact collisionPotential_step prims hx hy hxy t s.1

theorem table_potential (x y : Query C) (m : StateT (IdealState C) ProbComp Bit) (s : IdealState C)
    (hm : ∀ r ∈ support (m.run s), r.2.1 = s.1) :
    ∑' r, Pr[= r | m.run s] * collisionPotential x y r.2.1 ≤ collisionPotential x y s.1 :=
  tsum_probOutput_mul_le_of_eq _ _ _ fun r hr => by rw [hm r hr]

theorem firstTable_cache (a : Address C) (s : IdealState C) :
    ∀ r ∈ support ((firstTable a).run s), r.2.1 = s.1 := by
  intro r hr
  change r ∈ support ((fun r => (r.1, (s.1, r.2, s.2.2))) <$> tableDraw s.2.1 a) at hr
  rw [support_map] at hr
  obtain ⟨u, -, rfl⟩ := hr
  rfl

theorem secondTable_cache (a : Address C) (s : IdealState C) :
    ∀ r ∈ support ((secondTable a).run s), r.2.1 = s.1 := by
  intro r hr
  change r ∈ support ((fun r => (r.1, (s.1, s.2.1, r.2, s.2.2.2))) <$> tableDraw s.2.2.1 a) at hr
  rw [support_map] at hr
  obtain ⟨u, -, rfl⟩ := hr
  rfl

theorem flagged_cache (m : StateT (IdealState C) ProbComp Bit) (s : IdealState C)
    (hm : ∀ r ∈ support (m.run s), r.2.1 = s.1) :
    ∀ r ∈ support ((flagged m).run s), r.2.1 = s.1 := by
  intro r hr
  change r ∈ support ((fun r => (r.1, (r.2.1, r.2.2.1, r.2.2.2.1, true))) <$> m.run s) at hr
  rw [support_map] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  exact hm u hu

theorem withHidden_potential {x y : Query C} (hx : ∃ ph k v, x = .derive ph k v)
    (hy : ∃ ph k v, y = .derive ph k v) (hxy : x ≠ y)
    (hidden : PrgInput C → StateT (IdealState C) ProbComp Bit)
    (hh : ∀ z s, ∀ r ∈ support ((hidden z).run s), r.2.1 = s.1)
    (t : (LocalSpec C).Domain) (s : IdealState C) :
    ∑' r, Pr[= r | (withHidden prims D hidden t).run s] * collisionPotential x y r.2.1 ≤
      collisionPotential x y s.1 := by
  rcases t with u | q | z
  · exact onCache_potential prims hx hy hxy _ s
  · exact onCache_potential prims hx hy hxy _ s
  · change ∑' r, Pr[= r | (if Hidden D z.1 then hidden z else
      onCache (localAnswer prims (.inr (.inr z)))).run s] * _ ≤ _
    split_ifs
    · exact table_potential x y _ s (hh z s)
    · exact onCache_potential prims hx hy hxy (.inr (.inr z)) s

/-- One call of the left world does not raise the collision potential of two distinct derivation
inputs. Only the hash cache holds them, and the tables do not change it. -/
theorem leftImpl_potential {x y : Query C} (hx : ∃ ph k v, x = .derive ph k v)
    (hy : ∃ ph k v, y = .derive ph k v) (hxy : x ≠ y) (t : (Spec4 C).Domain) (s : IdealState C) :
    ∑' r, Pr[= r | (leftImpl prims D t).run s] * collisionPotential x y r.2.1 ≤
      collisionPotential x y s.1 := by
  rcases t with ((t | t) | t) | t
  · exact onCache_potential prims hx hy hxy t s
  · exact withHidden_potential prims D hx hy hxy _ (fun z s => firstTable_cache _ s) t s
  · exact withHidden_potential prims D hx hy hxy _
      (fun z s => flagged_cache _ s (secondTable_cache _ s)) t s
  · exact withHidden_potential prims D hx hy hxy _ (fun z s => secondTable_cache _ s) t s

/-- In the left world, the answer at a derivation input that is not cached equals the answer at
another derivation input with probability at most `1 / 2 ^ 256`. -/
theorem prob_collision_left {β : Type} (oa : OracleComp (Spec4 C) β) {x y : Query C}
    (hx : ∃ ph k v, x = .derive ph k v) (hy : ∃ ph k v, y = .derive ph k v) (hxy : x ≠ y)
    (s : IdealState C) (hs : s.1 x = none) :
    Pr[fun r => r.2.1 x ≠ none ∧ r.2.1 x = r.2.1 y | (simulateQ (leftImpl prims D) oa).run s] ≤
      (2 ^ 256)⁻¹ := by
  have h := probEvent_run_le_potential (leftImpl prims D)
    (fun s' : IdealState C => s'.1 x ≠ none ∧ s'.1 x = s'.1 y)
    (fun s' => collisionPotential x y s'.1) (fun s' hs' => ?_)
    (leftImpl_potential prims D hx hy hxy) oa s
  · refine h.trans (le_of_eq ?_)
    simp [collisionPotential, hs]
  · obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.mp hs'.1
    have hv := hs'.2
    rw [hu] at hv
    simp [collisionPotential, hu, ← hv]

end Potential

section Cut

open LifetimeRunBoundary (Program Pause runTo StartStop CountIs cont oracles4 finish4)

variable {C : Committee} {E : Type}

/-- The lifetime right after run `n` samples its parts. It holds the keys and the operator `h` of
the keygen, the setup data of run `n` (`none` when run `n` does not start), the rest of the
adversary and the state of the lifetime oracles. -/
structure Cut (C : Committee) (E : Type) where
  keys : C.Party → Keys C
  h : C.Party
  data : Option (C.Party → Parts C × List HashOutput)
  rest : Program C E
  state : LifetimeState C E

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (n : ℕ) (A : LifetimeAdversary C E)

/-- `program4` up to the admitted start of run `n` and the sample of its first setup data by
`prssInitialData`. It is `none` when the lifetime ends after the keygen. -/
def setupCut : OracleComp (Spec4 C) (Option (Cut C E)) := do
  let state ← (base4 (C := C)).adversary (A.keygen.start (corruptInputs D fun _ => ()) [])
  let (state, outputs) ← executePhase base4 D A.keygen noFunctionality setupRounds state
    fun i => (keygen i : PartyM C E RealSpec (Keys C))
  let some h := C.parties.find? (· ∉ D.1) | pure none
  if ¬ ∀ i, i ∉ D.1 → (outputs i).isSome then pure none else do
  let keys := fun i => (outputs i).getD default
  let r ← (runTo (oracles4 K circuits settings attempts D n keys h) (StartStop attempts D n)
    (A.run state (keys h).parameter)).run (LifetimeProof.initial D)
  r.1.atStart (pure (some ⟨keys, h, none, r.1.rest, r.2⟩)) fun tree k' =>
    if LifetimeProof.canStart attempts D r.2 tree ∧ CountIs n r.2 then do
      let data ← targetCopy4 (prssInitialData D)
      let next := fun i =>
        suspendStep (cont K circuits settings keys r.2 tree i) (prssInitialSteps D data i)
      pure (some ⟨keys, h, some data, k' (some (toCoalition D next)),
        ({ LifetimeProof.increment r.2 tree with
          running := some (tree, ceremonyFuel circuits settings, next) }).settle D⟩)
    else pure (some ⟨keys, h, none, r.1.rest, r.2⟩)

/-- `program4` after the sample of the parts of run `n`. -/
def tailCut : Option (Cut C E) → OracleComp (Spec4 C) Bool
  | none => pure false
  | some c => (simulateQ (oracles4 K circuits settings attempts D n c.keys c.h) c.rest).run c.state >>=
      finish4 D c.keys c.h

set_option maxRecDepth 200000 in
/-- `program4` is its run up to the sample of the parts of run `n`, then the rest. -/
theorem program4_cut :
    program4 D K circuits settings attempts A n =
      setupCut K circuits settings attempts D n A >>= tailCut K circuits settings attempts D n := by
  unfold program4 lifetimeGameWith setupCut
  simp only [bind_assoc]
  refine bind_congr fun state => ?_
  refine bind_congr fun r => ?_
  rcases r with ⟨state', outputs⟩
  cases hh : C.parties.find? (· ∉ D.1) with
  | none => simp [tailCut]
  | some h =>
    dsimp only
    by_cases hall : ∀ i, i ∉ D.1 → (outputs i).isSome
    · rw [if_neg (not_not.mpr hall), if_neg (not_not.mpr hall)]
      change (simulateQ (oracles4 K circuits settings attempts D n (fun i => (outputs i).getD default) h)
        (A.run state' ((outputs h).getD default).parameter)).run (LifetimeProof.initial D) >>=
          finish4 D (fun i => (outputs i).getD default) h = _
      rw [LifetimeRunBoundary.simulateQ_eq_runTo _ (StartStop attempts D n), StateT.run_bind,
        bind_assoc, bind_assoc]
      refine bind_congr fun r => ?_
      rcases r with ⟨p, st'⟩
      cases p with
      | done f => simp only [Pause.atStart, pure_bind, tailCut]
      | wait q k' =>
        cases q with
        | start tree =>
          simp only [Pause.atStart]
          split_ifs with hg
          · obtain ⟨hc, hn⟩ := hg
            simp only [Pause.rest, LifetimeRunBoundary.simulateQ_queryBind, StateT.run_bind,
              LifetimeRunBoundary.oracles4_inr]
            rw [LifetimeProof.run_start, if_neg (not_not.mpr hc), show st'.runCount = n from hn]
            simp only [ceremony_eq_prssSetup_bind, bind_assoc]
            change ((startSteps (roles4 n n) D fun i =>
              prssSetup i >>= cont K circuits settings (fun i => (outputs i).getD default) st' tree i) >>=
                _) = _
            rw [LifetimeRunBoundary.startSteps_run4, bind_map_left]
            refine bind_congr fun data => ?_
            simp only [pure_bind, tailCut]
          · simp only [pure_bind, tailCut]
        | _ => simp only [Pause.atStart, pure_bind, tailCut]
    · simp [hall, tailCut]

end Cut

section Support

open LifetimeRunBoundary (Program Pause runTo StartStop CountIs cont oracles4 finish4)

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (attempts : ℕ) (D : C.Coalition) (n : ℕ) (A : LifetimeAdversary C E)

theorem oracles4_eq (keys : C.Party → Keys C) (h : C.Party) :
    oracles4 K circuits settings attempts D n keys h =
      lifeImpl D K circuits settings attempts n keys h := rfl

/-- One call of the left world keeps every cached hash answer. -/
theorem leftImpl_cache (t : (Spec4 C).Domain) (s : IdealState C) (r : _ × IdealState C)
    (hr : r ∈ support ((leftImpl prims D t).run s)) : s.1 ≤ r.2.1 := by
  have hw : ∀ (hidden : PrgInput C → StateT (IdealState C) ProbComp Bit)
      (hh : ∀ z s, ∀ r ∈ support ((hidden z).run s), r.2.1 = s.1) (t : (LocalSpec C).Domain)
      (r : _ × IdealState C), r ∈ support ((withHidden prims D hidden t).run s) → s.1 ≤ r.2.1 := by
    intro hidden hh t r hr
    rcases t with u | q | z
    · exact (onCache_within prims _ (fun _ => True) (fun _ => True) s r hr).1
    · exact (onCache_within prims _ (fun _ => True) (fun _ => True) s r hr).1
    · change r ∈ support ((if Hidden D z.1 then hidden z else
        onCache (localAnswer prims (.inr (.inr z)))).run s) at hr
      split_ifs at hr
      · exact le_of_eq (hh z s r hr).symm
      · exact (onCache_within prims _ (fun _ => True) (fun _ => True) s r hr).1
  rcases t with ((t | t) | t) | t
  · exact (onCache_within prims _ (fun _ => True) (fun _ => True) s r hr).1
  · exact hw _ (fun z s => firstTable_cache _ s) t r hr
  · exact hw _ (fun z s => flagged_cache _ s (secondTable_cache _ s)) t r hr
  · exact hw _ (fun z s => secondTable_cache _ s) t r hr

/-- A run of the left world keeps every cached hash answer. -/
theorem simulate_cache {α : Type} (p : OracleComp (Spec4 C) α) (s : IdealState C)
    (r : α × IdealState C) (hr : r ∈ support ((simulateQ (leftImpl prims D) p).run s)) :
    s.1 ≤ r.2.1 := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a =>
    have he : r = (a, s) := by simpa using hr
    rw [he]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    exact le_trans (leftImpl_cache prims D t s u hu) (ih u.1 u.2 hr)

/-- Up to a pause before the admitted start of run `n`, the left world keeps the key-link
invariant and a run count of at most `n`. A pause is at that start. -/
theorem runTo_inv (keys : C.Party → Keys C) (h : C.Party) (prog : Program C E)
    (st : LifetimeState C E) (partsOf : ℕ → C.Party → Parts C) (s : IdealState C)
    (hinv : KeyLinkInv D keys n partsOf st s) (hc : st.runCount ≤ n)
    (r : (Pause C E × LifetimeState C E) × IdealState C)
    (hr : r ∈ support ((simulateQ (leftImpl prims D)
      ((runTo (oracles4 K circuits settings attempts D n keys h) (StartStop attempts D n) prog).run
        st)).run s)) :
    (∃ partsOf', KeyLinkInv D keys n partsOf' r.1.2 r.2) ∧ r.1.2.runCount ≤ n ∧
      ∀ q k, r.1.1 = .wait q k → StartStop attempts D n r.1.2 q := by
  have step : ∀ (t : (LocalSpec C + LifetimeSpec C E).Domain) (st : LifetimeState C E)
      (partsOf : ℕ → C.Party → Parts C) (s : IdealState C), KeyLinkInv D keys n partsOf st s →
      st.runCount ≤ n → (∀ q, t = .inr q → ¬ StartStop attempts D n st q) →
      ∀ u ∈ support ((simulateQ (leftImpl prims D)
        ((oracles4 K circuits settings attempts D n keys h t).run st)).run s),
        (∃ partsOf', KeyLinkInv D keys n partsOf' u.1.2 u.2) ∧ u.1.2.runCount ≤ n := by
    intro t st partsOf s hinv hc ht u hu
    obtain ⟨⟨p, hp, -⟩, -⟩ := step_inv prims D K circuits settings attempts n keys h t st partsOf s
      hinv u hu
    refine ⟨⟨p, hp⟩, ?_⟩
    rcases LifetimeRunBoundary.oracles4_runCount K circuits settings attempts D n keys h t st u.1
      (simulate_fst prims D _ s u hu) with he | ⟨tree, he, hcan, he'⟩
    · omega
    · have h' := ht _ he
      simp only [StartStop, CountIs, not_and] at h'
      have := h' hcan
      omega
  induction prog using OracleComp.recOn generalizing st partsOf s with
  | pure f =>
    change r ∈ support ((simulateQ (leftImpl prims D)
      (pure (Pause.done f, st) : OracleComp (Spec4 C) _)).run s) at hr
    rw [mem_left_pure prims D hr]
    exact ⟨⟨partsOf, hinv⟩, hc, fun q k h => by cases h⟩
  | queryBind t k ih =>
    rcases t with t | q
    · simp only [runTo, StateT.run_bind] at hr
      obtain ⟨u, hu, hr⟩ := mem_left_bind prims D hr
      obtain ⟨⟨p, hp⟩, hc'⟩ := step (.inl t) st partsOf s hinv hc (fun q h => by cases h) u hu
      exact ih u.1.1 u.1.2 p u.2 hp hc' hr
    · by_cases hq : StartStop attempts D n st q
      · simp only [runTo, StateT.run_bind, StateT.run_get, pure_bind, hq, if_true,
          StateT.run_pure] at hr
        rw [mem_left_pure prims D hr]
        refine ⟨⟨partsOf, hinv⟩, hc, fun q' k' h => ?_⟩
        cases h
        exact hq
      · simp only [runTo, StateT.run_bind, StateT.run_get, pure_bind, hq, if_false] at hr
        obtain ⟨u, hu, hr⟩ := mem_left_bind prims D hr
        obtain ⟨⟨p, hp⟩, hc'⟩ := step (.inr q) st partsOf s hinv hc
          (fun q' h => by cases h; exact hq) u hu
        exact ih u.1.1 u.1.2 p u.2 hp hc' hr

/-- After run `n` starts, the adversary program adds no first-table address. -/
theorem loop_frozen (keys : C.Party → Keys C) (h : C.Party) {β : Type}
    (prog : OracleComp (LocalSpec C + LifetimeSpec C E) β)
    (st : LifetimeState C E) (partsOf : ℕ → C.Party → Parts C) (s : IdealState C)
    (hinv : KeyLinkInv D keys n partsOf st s) (hn : n < st.runCount)
    (res : (β × LifetimeState C E) × IdealState C)
    (hres : res ∈ support ((simulateQ (leftImpl prims D)
      ((simulateQ (lifeImpl D K circuits settings attempts n keys h) prog).run st)).run s)) :
    ∀ y, (res.2.2.1 y).isSome → (s.2.1 y).isSome := by
  induction prog using OracleComp.inductionOn generalizing st partsOf s with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure] at hres
    rw [mem_left_pure prims D hres]
    exact fun _ h => h
  | query_bind q k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hres
    obtain ⟨u, hu, hres⟩ := mem_left_bind prims D hres
    obtain ⟨⟨partsOf', hinv', -⟩, hfrozen⟩ := step_inv prims D K circuits settings attempts n keys h q
      st partsOf s hinv u hu
    have hle := lifeImpl_runCount prims D K circuits settings attempts n keys h q st s u hu
    exact fun y hy => hfrozen hn y (ih u.1.1 u.1.2 partsOf' u.2 hinv' (by omega) hres y hy)

/-- The win test adds no table address. -/
theorem finish4_within (keys : C.Party → Keys C) (h : C.Party) (w : Forgery × LifetimeState C E)
    (s : IdealState C) (r : Bool × IdealState C)
    (hr : r ∈ support ((simulateQ (leftImpl prims D) (finish4 D keys h w)).run s)) :
    Within (fun _ => False) (fun _ => False) s r.2 := by
  refine simulate_within prims D _ _ _ ?_ s r hr
  have hlift : ∀ {α : Type} (p : OracleComp (RoSpec C) α), IsQueryBoundP p RoPrgCall 0 →
      IsQueryBoundP (roFree p) (Bad4 D (fun _ => False) (fun _ => False)) 0 :=
    fun p hp => free_bad D _ _ _ (ro_local_quiet p hp)
  unfold finish4
  dsimp only
  split_ifs
  · split
    · exact forgeryWins_quiet _ roFree hlift _
        (dealtWith_quiet _ roFree hlift _ _ _ _ (fun x => hlift _ (prfValue_quiet _ x))) _ _
    · exact trivial
  · exact trivial

end Support

section CutSupport

open LifetimeRunBoundary (Program Pause runTo StartStop CountIs cont oracles4 finish4)

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (attempts : ℕ) (D : C.Coalition) (n : ℕ) (A : LifetimeAdversary C E)

set_option maxRecDepth 200000 in
/-- Each supported cut has an empty second table, or it keeps the key-link invariant. Run `n`
then has not started and the rest is a final forgery, or run `n` has started and the parts of
run `n` in the history are the sampled parts. -/
theorem setupCut_inv (c : Option (Cut C E) × IdealState C)
    (hc : c ∈ support ((simulateQ (leftImpl prims D)
      (setupCut K circuits settings attempts D n A)).run idealStart)) :
    (c.1 = none → ∀ y, (c.2.2.2.1 y).isSome → False) ∧
    ∀ cut, c.1 = some cut → ∃ partsOf, KeyLinkInv D cut.keys n partsOf cut.state c.2 ∧
      ((cut.data = none ∧
        (∃ f, cut.rest = (pure f : OracleComp (LocalSpec C + LifetimeSpec C E) Forgery)) ∧ cut.state.runCount ≤ n) ∨
        (∃ data, cut.data = some data ∧ n < cut.state.runCount ∧
          partsOf n = fun i => (data i).1)) := by
  unfold setupCut at hc
  obtain ⟨u, hu, hc⟩ := mem_left_bind prims D hc
  have hw₀ := simulate_within prims D (fun _ => False) (fun _ => False) _ (adv_bad D _ _ _)
    idealStart u hu
  obtain ⟨v, hv, hc⟩ := mem_left_bind prims D hc
  have hw₁ := within_trans hw₀ (simulate_within prims D (fun _ => False) (fun _ => False) _
    (keygen_bad D _ _ A.keygen u.1) u.2 v hv)
  have hempty : ∀ y, (v.2.2.2.1 y).isSome → False := fun y hy => by
    rcases hw₁.2.2.2 y hy with h | h
    · simp [idealStart] at h
    · exact h
  let zero : ℕ → C.Party → Parts C := fun _ _ => ⟨0, fun _ => 0, fun _ => 0⟩
  rcases v with ⟨⟨state, outputs⟩, s₁⟩
  dsimp only at hc hempty hw₁
  split at hc
  swap
  · obtain rfl := mem_left_pure prims D hc
    exact ⟨fun _ => hempty, fun cut h => by cases h⟩
  rename_i h _
  by_cases hout : ∀ i, i ∉ D.1 → (outputs i).isSome
  swap
  · rw [if_pos hout] at hc
    obtain rfl := mem_left_pure prims D hc
    exact ⟨fun _ => hempty, fun cut h => by cases h⟩
  rw [if_neg (not_not.mpr hout)] at hc
  obtain ⟨w, hw, hc⟩ := mem_left_bind prims D hc
  obtain ⟨⟨partsOf, hinv⟩, hcount, hstop⟩ := runTo_inv prims K circuits settings attempts D n _ h _ _
    zero s₁ ⟨tablesOk_start D n _ _ s₁ hw₁, fun tree fuel steps hs => by cases hs⟩
    (by simp [LifetimeProof.initial, LifetimeState.runCount]) w hw
  rcases w with ⟨⟨p, st⟩, s₂⟩
  dsimp only at hc hinv hcount hstop
  cases p with
  | done f =>
    simp only [Pause.atStart] at hc
    obtain rfl := mem_left_pure prims D hc
    refine ⟨fun h => (by cases h), fun cut hcut => ?_⟩
    cases hcut
    exact ⟨partsOf, hinv, Or.inl ⟨rfl, ⟨f, rfl⟩, hcount⟩⟩
  | wait q k' =>
    have hq := hstop q k' rfl
    cases q with
    | start tree =>
      obtain ⟨hcan, hn⟩ := hq
      have hn' : st.runCount = n := hn
      simp only [Pause.atStart] at hc
      rw [if_pos ⟨hcan, hn⟩] at hc
      obtain ⟨v, hv, hc⟩ := mem_left_bind prims D hc
      obtain rfl := mem_left_pure prims D hc
      refine ⟨fun h => (by cases h), fun cut hcut => ?_⟩
      cases hcut
      dsimp only
      have hw := simulate_within prims D _ _ _ (runQ_noStream D n n _ (qb0_prssInitialData D)) s₂ v
        (by rw [runQ_self]; exact hv)
      have hc' : ({ LifetimeProof.increment st tree with running := some (tree,
          ceremonyFuel circuits settings, fun i =>
            suspendStep (cont K circuits settings (fun i => (outputs i).getD default) st tree i)
              (prssInitialSteps D v.1 i)) } : LifetimeState C E).runCount = st.runCount + 1 :=
        LifetimeProof.increment_runCount st tree
      refine ⟨Function.update partsOf st.runCount (fun i => (v.1 i).1), ?_,
        Or.inr ⟨v.1, rfl, ?_, by rw [← hn']; exact Function.update_self _ _ _⟩⟩
      · refine settle_inv D n _ _ tree _ _ rfl _ _ ?_ ?_ fun _ => ?_
        · rw [hc']
          exact tablesOk_quiet D n (tablesOk_update D n hinv.1 _) hw (by omega)
        · rw [hc']
          omega
        · rw [hc', Nat.add_sub_cancel]
          refine Or.inl ⟨cont K circuits settings (fun i => (outputs i).getD default) st tree, v.1,
            fun i prss => POk.ceremonyAfterSetup K circuits settings _ tree, ?_, rfl⟩
          exact Function.update_self _ _ _
      · rw [LifetimeRunBoundary.runCount_start]
        omega
    | _ => exact (hq : False).elim

/-- A cut where run `n` has not started gives no key overlap. -/
theorem tail_none (cut : Cut C E) (partsOf : ℕ → C.Party → Parts C) (s : IdealState C)
    (hinv : KeyLinkInv D cut.keys n partsOf cut.state s) (f : Forgery)
    (hrest : cut.rest = (pure f : OracleComp (LocalSpec C + LifetimeSpec C E) Forgery))
    (hcount : cut.state.runCount ≤ n) (name : KeyName C) (r : Bool × IdealState C)
    (hr : r ∈ support ((simulateQ (leftImpl prims D)
      (tailCut K circuits settings attempts D n (some cut))).run s)) :
    ¬ KeyOverlap name r.2 := by
  change r ∈ support ((simulateQ (leftImpl prims D)
    ((simulateQ (oracles4 K circuits settings attempts D n cut.keys cut.h) cut.rest).run cut.state >>=
      finish4 D cut.keys cut.h)).run s) at hr
  rw [hrest, simulateQ_pure, StateT.run_pure, pure_bind] at hr
  have hw := finish4_within prims D cut.keys cut.h _ s r hr
  rintro ⟨key, a, b, -, hb⟩
  rcases hw.2.2.2 _ hb with h | h
  · have := (hinv.1.2.2 _ h).2.1
    omega
  · exact h

/-- At a cut where run `n` has started with the parts `partsOf n`, a key overlap at the end is a
collision of the final answer at the run-`n` input with the final answer at the input of an
earlier run `m < n` that the cut has already cached. -/
theorem tail_overlap (cut : Cut C E) (partsOf : ℕ → C.Party → Parts C) (s : IdealState C)
    (hinv : KeyLinkInv D cut.keys n partsOf cut.state s) (hn : n < cut.state.runCount)
    (name : KeyName C) (r : Bool × IdealState C)
    (hr : r ∈ support ((simulateQ (leftImpl prims D)
      (tailCut K circuits settings attempts D n (some cut))).run s))
    (ho : KeyOverlap name r.2) :
    ∃ m ∈ (Finset.range n).filter fun m => (s.1 (LifetimeIdealKeyLink.hiddenInput (partsOf m) name)).isSome,
      r.2.1 (LifetimeIdealKeyLink.hiddenInput (partsOf n) name) ≠ none ∧
        r.2.1 (LifetimeIdealKeyLink.hiddenInput (partsOf n) name) = r.2.1 (LifetimeIdealKeyLink.hiddenInput (partsOf m) name) := by
  change r ∈ support ((simulateQ (leftImpl prims D)
    ((simulateQ (oracles4 K circuits settings attempts D n cut.keys cut.h) cut.rest).run cut.state >>=
      finish4 D cut.keys cut.h)).run s) at hr
  obtain ⟨w, hw, hr⟩ := mem_left_bind prims D hr
  obtain ⟨partsOf', hinv', hagree⟩ := loop_inv prims D K circuits settings attempts n cut.keys cut.h
    _ _ partsOf s hinv w hw
  have hfrozen := loop_frozen prims K circuits settings attempts D n cut.keys cut.h _ _ partsOf s
    hinv hn w hw
  have hcache := simulate_cache prims D _ s w hw
  have hfin := finish4_within prims D cut.keys cut.h _ _ r hr
  obtain ⟨key, a, b, ha, hb⟩ := ho
  have ha' : (w.2.2.1 ((name, key), a)).isSome := (hfin.2.2.1 _ ha).resolve_right id
  have hb' : (w.2.2.2.1 ((name, key), b)).isSome := (hfin.2.2.2 _ hb).resolve_right id
  obtain ⟨-, m, hm, -, hkey⟩ := hinv.1.2.1 _ (hfrozen _ ha')
  have hsecond := (hinv'.1.2.2 _ hb').2.2
  rw [hagree n hn] at hsecond
  have hx : r.2.1 (LifetimeIdealKeyLink.hiddenInput (partsOf n) name) = some key := hfin.1 hsecond
  have hy : r.2.1 (LifetimeIdealKeyLink.hiddenInput (partsOf m) name) = some key := hfin.1 (hcache hkey)
  refine ⟨m, Finset.mem_filter.2 ⟨Finset.mem_range.2 hm, by simp [hkey]⟩, by simp [hx], ?_⟩
  rw [hx, hy]

end CutSupport

section Bound

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (attempts : ℕ) (D : C.Coalition) (n : ℕ) (A : LifetimeAdversary C E)

/-- At the cut, run `n` has sampled its parts, and the hash cache already holds the `.derive`
input of `name` from these parts. -/
def RunEarlyCached (name : KeyName C) (c : Option (Cut C E) × IdealState C) : Prop :=
  ∃ cut data, c.1 = some cut ∧ cut.data = some data ∧
    (c.2.1 (LifetimeIdealKeyLink.hiddenInput (fun i => (data i).1) name)).isSome

theorem hiddenInput_derive (parts : C.Party → Parts C) (name : KeyName C) :
    ∃ ph k v, LifetimeIdealKeyLink.hiddenInput parts name = .derive ph k v := by
  cases name <;> exact ⟨_, _, _, rfl⟩

/-- From a supported cut where the run-`n` input of `name` is not cached, the rest of the left
world gives a key overlap at `name` with probability at most `n / 2 ^ 256`. -/
theorem tail_fresh (c : Option (Cut C E) × IdealState C)
    (hc : c ∈ support ((simulateQ (leftImpl prims D)
      (setupCut K circuits settings attempts D n A)).run idealStart))
    (name : KeyName C) (hearly : ¬ RunEarlyCached name c) :
    Pr[KeyOverlap name ∘ Prod.snd | (simulateQ (leftImpl prims D)
      (tailCut K circuits settings attempts D n c.1)).run c.2] ≤ (n : ℝ≥0∞) / 2 ^ 256 := by
  obtain ⟨hnone, hsome⟩ := setupCut_inv prims K circuits settings attempts D n A c hc
  rcases hc1 : c.1 with _ | cut
  · refine le_of_eq_of_le (probEvent_eq_zero_iff.2 fun r hr => ?_) zero_le
    change r ∈ support ((simulateQ (leftImpl prims D) (pure false : OracleComp (Spec4 C) Bool)).run
      c.2) at hr
    obtain rfl := mem_left_pure prims D hr
    rintro ⟨key, a, b, -, hb⟩
    exact hnone hc1 _ hb
  obtain ⟨partsOf, hinv, hcase⟩ := hsome cut hc1
  rcases hcase with ⟨-, ⟨f, hf⟩, hcount⟩ | ⟨data, hd, hn, hp⟩
  · refine le_of_eq_of_le (probEvent_eq_zero_iff.2 fun r hr => ?_) zero_le
    exact tail_none prims K circuits settings attempts D n cut partsOf c.2 hinv f hf hcount name r hr
  let x := LifetimeIdealKeyLink.hiddenInput (partsOf n) name
  have hx : c.2.1 x = none := by
    by_contra hne
    exact hearly ⟨cut, data, hc1, hd, by
      rw [← hp]
      exact Option.ne_none_iff_isSome.mp hne⟩
  let R := (Finset.range n).filter fun m =>
    (c.2.1 (LifetimeIdealKeyLink.hiddenInput (partsOf m) name)).isSome
  calc Pr[KeyOverlap name ∘ Prod.snd | (simulateQ (leftImpl prims D)
        (tailCut K circuits settings attempts D n (some cut))).run c.2]
      ≤ Pr[fun r => ∃ m ∈ R, r.2.1 x ≠ none ∧
          r.2.1 x = r.2.1 (LifetimeIdealKeyLink.hiddenInput (partsOf m) name) |
          (simulateQ (leftImpl prims D) (tailCut K circuits settings attempts D n (some cut))).run
            c.2] :=
        probEvent_mono fun r hr ho =>
          tail_overlap prims K circuits settings attempts D n cut partsOf c.2 hinv hn name r hr ho
    _ ≤ ∑ m ∈ R, Pr[fun r => r.2.1 x ≠ none ∧
          r.2.1 x = r.2.1 (LifetimeIdealKeyLink.hiddenInput (partsOf m) name) |
          (simulateQ (leftImpl prims D) (tailCut K circuits settings attempts D n (some cut))).run
            c.2] := probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _m ∈ R, ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hy := (Finset.mem_filter.1 hm).2
        refine prob_collision_left prims D _ (hiddenInput_derive _ _) (hiddenInput_derive _ _)
          (fun he => ?_) c.2 hx
        rw [← he, hx] at hy
        exact absurd hy (by simp)
    _ = (R.card : ℝ≥0∞) / 2 ^ 256 := by simp [div_eq_mul_inv]
    _ ≤ (n : ℝ≥0∞) / 2 ^ 256 := ENNReal.div_le_div_right (by
        exact_mod_cast (Finset.card_filter_le _ _).trans (Finset.card_range n).le) _

/-- The key overlap at `name` in the left world of hop `n` has probability at most the chance that
the cut has already cached the run-`n` input of `name`, plus `n / 2 ^ 256`. -/
theorem keyOverlap_le_early (name : KeyName C) :
    Pr[KeyOverlap name ∘ Prod.snd | (simulateQ (leftImpl prims D)
      (program4 D K circuits settings attempts A n)).run idealStart] ≤
      Pr[RunEarlyCached name | (simulateQ (leftImpl prims D)
        (setupCut K circuits settings attempts D n A)).run idealStart] + (n : ℝ≥0∞) / 2 ^ 256 := by
  let P := (simulateQ (leftImpl prims D) (setupCut K circuits settings attempts D n A)).run idealStart
  rw [program4_cut, simulateQ_bind, StateT.run_bind, probEvent_bind_eq_tsum]
  calc ∑' c, Pr[= c | P] * Pr[KeyOverlap name ∘ Prod.snd | (simulateQ (leftImpl prims D)
        (tailCut K circuits settings attempts D n c.1)).run c.2]
      ≤ ∑' c, Pr[= c | P] * ((if RunEarlyCached name c then 1 else 0) + (n : ℝ≥0∞) / 2 ^ 256) := by
        refine ENNReal.tsum_le_tsum fun c => ?_
        by_cases hc : c ∈ support P
        · gcongr
          by_cases he : RunEarlyCached name c
          · simp only [he, if_true]
            exact probEvent_le_one.trans le_self_add
          · simp only [he, if_false, zero_add]
            exact tail_fresh prims K circuits settings attempts D n A c hc name he
        · simp [probOutput_eq_zero_of_not_mem_support hc]
    _ = (∑' c, if RunEarlyCached name c then Pr[= c | P] else 0) +
          (∑' c, Pr[= c | P]) * ((n : ℝ≥0∞) / 2 ^ 256) := by
        simp only [mul_add, mul_ite, mul_one, mul_zero]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ Pr[RunEarlyCached name | P] + 1 * ((n : ℝ≥0∞) / 2 ^ 256) := by
        rw [probEvent_eq_tsum_ite]
        gcongr
        exact tsum_probOutput_le_one
    _ = _ := by rw [one_mul]

end Bound

section Assembly

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ) (D : C.Coalition)
variable (A : LifetimeAdversary C E) (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)

/-- The early-cache estimate on the cut of the actual left world. Under the lifetime
budget, the hash cache holds the run-`n` input of a hidden name right after run `n` samples its
parts with probability at most `Q / 2 ^ 256`. -/
def RunEarlyCachedBound (Q : ℕ) : Prop :=
  let F := ceremonyFuel (circuitsOf fun _ => 0) settings
  HasLifetimeQueryBound K settings attempts circuitsOf D A Q →
  keySplit C (Q + lifetimeOverhead C attempts Q + (F + 2) * Q) < 2 →
  ∀ (n : Fin (lifetimeRuns attempts)) (values : MpcDomain → HashOutput)
      (name : {name : KeyName C // Hidden D name}),
    Pr[RunEarlyCached name.1 | (simulateQ (leftImpl ⟨thOf values, aes⟩ D)
      (setupCut K (circuitsOf (thOf values)) settings attempts D n A)).run idealStart] ≤
        (Q : ℝ≥0∞) / 2 ^ 256

/-- The early-cache estimate gives the U4 estimate `HiddenKeyOverlapBound`. The fresh run-`n`
answer pays `n ≤ lifetimeRuns attempts - 1` of the `2 * (lifetimeRuns attempts - 1)` part. -/
theorem hiddenKeyOverlapBound_of_early (Q : ℕ)
    (early : RunEarlyCachedBound K settings attempts D A aes circuitsOf Q) :
    HiddenKeyOverlapBound K settings attempts D A aes circuitsOf Q := by
  intro hQ hsplit n values name
  refine (keyOverlap_le_early ⟨thOf values, aes⟩ K (circuitsOf (thOf values)) settings attempts D n A
    name.1).trans ?_
  have hn : (n : ℕ) ≤ 2 * (lifetimeRuns attempts - 1) := by
    have := n.isLt
    omega
  calc _ ≤ (Q : ℝ≥0∞) / 2 ^ 256 + (n : ℝ≥0∞) / 2 ^ 256 :=
        add_le_add (early hQ hsplit n values name) le_rfl
    _ = ((Q + n : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
        rw [ENNReal.div_add_div_same]
        push_cast
        rfl
    _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast (by omega : Q + n ≤
        2 * (lifetimeRuns attempts - 1) + Q)) _

end Assembly

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealOverlapFinal.prob_collision_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prob_collision_left

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealOverlapFinal.program4_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms program4_cut

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealOverlapFinal.setupCut_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms setupCut_inv

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealOverlapFinal.tail_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tail_fresh

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealOverlapFinal.keyOverlap_le_early' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms keyOverlap_le_early

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealOverlapFinal.hiddenKeyOverlapBound_of_early' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hiddenKeyOverlapBound_of_early

end ThresholdLeanXmssSecurity.LifetimeIdealOverlapFinal
