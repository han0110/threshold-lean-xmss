import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Games
import ThresholdLeanXmssSecurity.Proof.Dealer
import ThresholdLeanXmssSecurity.Proof.Execution
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Partition
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Start
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.End
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Readiness
import ThresholdLeanXmssSecurity.Proof.DkgCompleteness.SeedGen
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Game
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Hops
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# No run after a failed search of the dealer

`dealtProb_search` states that, for each event on the result of `sharedDealt`, the real mode and the mode
that skips a bottom tree after a failed search of the dealer differ by at most `2 ^ layerHeight` times
`searchFailure`. `sharedSearch` is the hop `SharedSearch`.

* `pot S p c` is the probability that the random-oracle computation `S` gives a result with `p` from the
  cache `c`. A local call of the world keeps it in the mean, by lazy sampling (`sameRun_swap`). A
  programming call on a cell that `S` never asks keeps it. From the empty cache the potential of the
  search of the dealer is at most the bound of `refSuccess_fail`.
* `wp_simulateQ_untilBad` compares two handlers that agree until a bad state. A potential that is at
  least one on a bad state and does not grow in the mean bounds the difference.
* In the signing layer the bad state is a failed search (`TreesBad`), and `treePot` is the potential of
  one bottom tree. The seed generation draws the seeds after the first calls of the adversary, so the
  bound takes the mean of the potential over `prawnsKeyGen` (`wp_worldSeedGen_pot`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgCorrectnessProof.GameCount (OnlySign onlySign_iff onlySign_bind onlySign_map
  onlySign_referenceTree SignCall)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_bind noCall_pure noCall_map
  noCall_query noCall_mapM noCall_sequenceFin)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee} (prims : Primitives)

/-! ## Expectations of events -/

theorem prEvent_bind_wp {α β : Type} (mx : ProbComp α) (f : α → ProbComp β) (q : β → Prop) :
    Pr{let z ← mx >>= f}[q z] = wp mx (fun x => Pr{let z ← f x}[q z]) := by
  rw [prEvent_eq_wp_indicator, wp_bind]
  congr 1
  funext x
  rw [prEvent_eq_wp_indicator]

/-! ## The potential -/

/-- The probability that `S` gives a result with `p` from the cache `c`. -/
def pot {β : Type} (S : OracleComp (RoSpec C) β) (p : β → Prop) (c : HashCache C) : ℝ≥0∞ :=
  Pr{let z ← roRun prims S c}[p z.1]

/-- A local call keeps the potential in expectation. -/
theorem wp_pot_local {β : Type} (S : OracleComp (RoSpec C) β) (p : β → Prop) (t : (LocalSpec C).Domain)
    (c : HashCache C) :
    wp ((localAnswer prims t).run c) (fun z => pot prims S p z.2) = pot prims S p c := by
  have h := sameRun_swap prims (liftM (OracleSpec.query (spec := LocalSpec C) t))
    (liftComp S (LocalSpec C)) (fun _ b => pure b) c
  have e := h.prEvent_eq (fun z => p z.1)
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, simulateQ_spec_query,
    bind_pure] at e
  rw [prEvent_bind_wp] at e
  simp only [pot, ← localRun_liftComp prims S]
  rw [e, prEvent_bind_wp, prEvent_eq_wp_indicator]
  congr 1
  funext x
  simp only [bind_pure_comp]
  rw [prEvent_map]
  by_cases hx : p x.1
  · simp [hx]
  · simp [hx]

/-! ## A write on a cell that a computation never asks -/

theorem cacheQuery_comm {q q' : Query C} (hne : q' ≠ q) (u v : HashOutput) (c : HashCache C) :
    (c.cacheQuery q' u).cacheQuery q v = (c.cacheQuery q v).cacheQuery q' u := by
  refine QueryCache.ext fun r => ?_
  by_cases h1 : r = q
  · subst h1
    rw [QueryCache.cacheQuery_self, QueryCache.cacheQuery_of_ne _ _ hne.symm, QueryCache.cacheQuery_self]
  · by_cases h2 : r = q'
    · subst h2
      rw [QueryCache.cacheQuery_of_ne _ _ h1, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
    · rw [QueryCache.cacheQuery_of_ne _ _ h1, QueryCache.cacheQuery_of_ne _ _ h2,
        QueryCache.cacheQuery_of_ne _ _ h2, QueryCache.cacheQuery_of_ne _ _ h1]

/-- A computation that asks only cells of `H` other than `q` moves along a write on `q`. -/
theorem roRun_cacheQuery (q : Query C) (v : HashOutput) {β : Type} (S : OracleComp (RoSpec C) β)
    (hS : AllQueriesSatisfy S fun t => ∃ q', t = .inl q' ∧ q' ≠ q) (c : HashCache C) :
    roRun prims S (c.cacheQuery q v) = (fun z => (z.1, z.2.cacheQuery q v)) <$> roRun prims S c := by
  induction S using OracleComp.inductionOn generalizing c with
  | pure a => simp [roRun_pure]
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hS
    obtain ⟨⟨q', rfl, hne⟩, hk⟩ := hS
    have e : ∀ s, roRun prims (liftM (OracleSpec.query (spec := RoSpec C) (.inl q')) >>= k) s =
        (hashAnswer prims q').run s >>= fun z => roRun prims (k z.1) z.2 := fun s => by
      rw [roRun_bind, ← roRun_hashQuery]
      rfl
    rw [e, e, DkgCorrectnessProof.UsedHit.hashAnswer_map prims q' (fun c => c.cacheQuery q v) c
      (QueryCache.cacheQuery_of_ne _ _ hne) (fun u => cacheQuery_comm hne u v c), bind_map_left, map_bind]
    exact bind_congr fun z => ih z.1 (hk z.1) z.2

/-- A cell of `Th` or of the PRF of a term. The searches of the dealer ask only such cells. -/
def HashPrf : Query C → Prop
  | .hash _ => True
  | .prf _ _ => True
  | _ => False

theorem pot_cacheQuery {β : Type} (S : OracleComp (RoSpec C) β) (p : β → Prop) (hS : OnlySign S)
    {q : Query C} (hq : ¬ HashPrf q) (v : HashOutput) (c : HashCache C) :
    pot prims S p (c.cacheQuery q v) = pot prims S p c := by
  have hS' : AllQueriesSatisfy S fun t => ∃ q', t = .inl q' ∧ q' ≠ q := ((onlySign_iff S).1 hS).mono fun t ht => by
    rcases t with q' | x
    · refine ⟨q', rfl, fun e => hq (e ▸ ?_)⟩
      cases q' <;> simp_all [SignCall, HashPrf]
    · exact absurd ht (by simp [SignCall])
  unfold pot
  rw [roRun_cacheQuery prims q v S hS' c, prEvent_map]

/-! ## The calls of `streamWorld` -/

/-- A call of the world that is no programming call on a cell of `Th` or of the PRF of a term. -/
def SearchSafe : (WorldSpec C).Domain → Prop
  | .inl (.inr x) => ¬ HashPrf x.1
  | _ => True

theorem wp_onHash {α : Type} (m : StateT (HashCache C) ProbComp α) (w : StreamState C)
    (f : HashCache C → ℝ≥0∞) :
    wp ((onHash m).run w) (fun z => f z.2.1) = wp (m.run w.1) (fun z => f z.2) := by
  simp only [onHash, StateT.run_mk, wp_map]
  rfl

/-- A safe call of `streamWorld` keeps the potential of a search in expectation. -/
theorem wp_pot_streamWorld (D : C.Coalition) {β : Type} (S : OracleComp (RoSpec C) β) (p : β → Prop)
    (hS : OnlySign S) (t : (WorldSpec C).Domain) (ht : SearchSafe t) (w : StreamState C) :
    wp ((streamWorld prims D t).run w) (fun z => pot prims S p z.2.1) = pot prims S p w.1 := by
  rcases t with (t | x) | t
  · exact (wp_onHash _ w _).trans (wp_pot_local prims S p t w.1)
  · simp only [streamWorld]
    rw [wp_onHash]
    change wp ((programAnswer x).run w.1) _ = _
    unfold programAnswer
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs
    · simp
    · simp only [StateT.run_bind, StateT.run_set, pure_bind, StateT.run_pure, wp_pure]
      exact pot_cacheQuery prims S p hS ht x.2 w.1
  · rcases t with n | q | x
    · exact (wp_onHash _ w _).trans (wp_pot_local prims S p _ w.1)
    · exact (wp_onHash _ w _).trans (wp_pot_local prims S p _ w.1)
    · simp only [streamWorld]
      split_ifs
      · simp only [StateT.run_mk, wp_map]
        simp [Function.comp_def]
      · exact (wp_onHash _ w _).trans (wp_pot_local prims S p _ w.1)

/-! ## The potential along a world computation -/

/-- A handler keeps `f` of the state when each call with `ok` keeps it in expectation. -/
theorem wp_simulateQ_le {ι W α : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (StateT W ProbComp))
    (ok : ι → Prop) (f : W → ℝ≥0∞) (hstep : ∀ t, ok t → ∀ w, wp ((impl t).run w) (fun z => f z.2) ≤ f w)
    (oa : OracleComp spec α) (hoa : AllQueriesSatisfy oa ok) (w : W) :
    wp ((simulateQ impl oa).run w) (fun z => f z.2) ≤ f w := by
  induction oa using OracleComp.inductionOn generalizing w with
  | pure a => simp
  | query_bind t k ih =>
    rw [allQueriesSatisfy_query_bind_iff] at hoa
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, wp_bind]
    exact (wp_mono _ fun (z : spec.Range t × W) => ih z.1 (hoa.2 z.1) z.2).trans (hstep t hoa.1 w)

/-- A safe call of `loggedWorld` keeps the potential of a search in expectation. -/
theorem wp_pot_loggedWorld (D : C.Coalition) {β : Type} (S : OracleComp (RoSpec C) β) (p : β → Prop)
    (hS : OnlySign S) (t : (WorldSpec C).Domain) (ht : SearchSafe t) (w : StreamState C × List (Query C)) :
    wp ((loggedWorld prims D t).run w) (fun z => pot prims S p z.2.1.1) = pot prims S p w.1.1 := by
  simp only [loggedWorld, StateT.run_mk, wp_map]
  exact wp_pot_streamWorld prims D S p hS t ht w.1

/-- A world computation with safe calls keeps the potential of a search in `loggedWorld`. -/
theorem wp_pot_simulateQ (D : C.Coalition) {β : Type} (S : OracleComp (RoSpec C) β) (p : β → Prop)
    (hS : OnlySign S) {α : Type} (oa : OracleComp (WorldSpec C) α) (hoa : AllQueriesSatisfy oa SearchSafe)
    (w : StreamState C × List (Query C)) :
    wp ((simulateQ (loggedWorld prims D) oa).run w) (fun z => pot prims S p z.2.1.1) ≤ pot prims S p w.1.1 :=
  wp_simulateQ_le (loggedWorld prims D) SearchSafe (fun w => pot prims S p w.1.1)
    (fun t ht w => (wp_pot_loggedWorld prims D S p hS t ht w).le) oa hoa w

theorem searchSafe_of_noCall {α : Type} {oa : OracleComp (WorldSpec C) α} (h : NoCall WorldProgramQuery oa) :
    AllQueriesSatisfy oa SearchSafe :=
  (UsedHit.allQueries_of_noCall h).mono fun t ht => by
    rcases t with (t | x) | t
    · trivial
    · exact absurd trivial ht
    · trivial

/-- A computation on `.hash` and `.prf` on the free copy is its run on the hash cache. -/
theorem freeRun_onlySign (D : C.Coalition) {α : Type} (oa : OracleComp (RoSpec C) α) (h : OnlySign oa)
    (w : StreamState C) :
    Ready.freeRun prims D oa w = (fun z => (z.1, (z.2, w.2))) <$> roRun prims oa w.1 := by
  induction oa using OracleComp.inductionOn generalizing w with
  | pure a => simp [Ready.freeRun, roRun_pure]
  | query_bind t k ih =>
    rw [onlySign_iff, allQueriesSatisfy_query_bind_iff] at h
    obtain ⟨ht, hk⟩ := h
    rcases t with q | x
    · have hq : (liftM (OracleSpec.query (spec := RoSpec C) (.inl q)) : OracleComp (RoSpec C) _) = hashQuery q := rfl
      rw [Ready.freeRun_bind, roRun_bind, hq, roRun_hashQuery, hashQuery, Ready.freeRun_query]
      simp only [streamWorld, onHash, StateT.run_mk, map_bind, bind_map_left]
      refine bind_congr fun r => ?_
      rw [ih r.1 ((onlySign_iff _).2 (hk r.1))]
    · exact absurd ht (by simp [SignCall])

/-- A computation on `.hash` and `.prf` on the free copy in `loggedWorld` is its run on the hash cache,
for each function of the result and of the hash cache. -/
theorem wp_logged_free (D : C.Coalition) {α : Type} (T : OracleComp (RoSpec C) α) (hT : OnlySign T)
    (w : StreamState C × List (Query C)) (G : α → HashCache C → ℝ≥0∞) :
    wp ((simulateQ (loggedWorld prims D) (free (liftComp T (LocalSpec C)))).run w) (fun z => G z.1 z.2.1.1) =
      wp (roRun prims T w.1.1) (fun z => G z.1 z.2) := by
  have hw := withLog_run (streamWorld prims D) countedCells (free (liftComp T (LocalSpec C))) w.1 w.2
  rw [← loggedWorld_eq] at hw
  have e : wp ((simulateQ (loggedWorld prims D) (free (liftComp T (LocalSpec C)))).run w) (fun z => G z.1 z.2.1.1) =
      wp ((fun r => (r.1, r.2.1)) <$> (simulateQ (loggedWorld prims D) (free (liftComp T (LocalSpec C)))).run
        (w.1, w.2)) (fun z => G z.1 z.2.1) := by
    rw [wp_map]
    rfl
  rw [e, hw]
  change wp (Ready.freeRun prims D T w.1) _ = _
  rw [freeRun_onlySign prims D T hT, wp_map]
  rfl

/-! ## The search of the dealer for one bottom tree -/

/-- The dealer on the random oracles. It builds its top tree, and then bottom tree `b` on it. -/
def dealerSearch (parameter : PublicParameter) (seeds : C.Term → HashOutput) (b : Fin (2 ^ layerHeight)) :
    OracleComp (RoSpec C) (Option BottomTree) := do
  let output ← referenceTree tweakable (prfValue seeds) parameter emptyTop .top
  bottomOf <$> referenceTree tweakable (prfValue seeds) parameter
    ((TreeOutput.topTree output).getD emptyTop) (.bottom b)

theorem bottomOf_rest (seeds : C.Term → HashOutput) (parameter : PublicParameter) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) :
    ∀ o ∈ support (referenceBottomRest seeds parameter top b outputs), bottomOf o = none → o = none := by
  intro o ho
  unfold referenceBottomRest at ho
  simp only [mem_support_bind_iff] at ho
  obtain ⟨root, -, base, -, g, -, ho⟩ := ho
  rcases g with _ | ⟨r, enc⟩
  · simp at ho; simp [ho]
  simp only [mem_support_bind_iff] at ho
  obtain ⟨v, -, ho⟩ := ho
  rcases v with _ | vals
  · simp at ho; simp [ho]
  simp only [mem_support_bind_iff] at ho
  obtain ⟨path, -, topRoot, -, ho⟩ := ho
  split_ifs at ho <;> simp at ho <;> simp [ho, bottomOf]

theorem bottomOf_bottom (seeds : C.Term → HashOutput) (parameter : PublicParameter) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) :
    ∀ o ∈ support (referenceTree tweakable (prfValue seeds) parameter top (.bottom b)),
      bottomOf o = none → o = none := by
  intro o ho
  rw [refBottom_eq, mem_support_bind_iff] at ho
  obtain ⟨outputs, -, ho⟩ := ho
  exact bottomOf_rest seeds parameter top b outputs o ho

theorem fst_mem_support_roRun {β : Type} (S : OracleComp (RoSpec C) β) (c : HashCache C) (z : β × HashCache C)
    (hz : z ∈ support (roRun prims S c)) : z.1 ∈ support S := by
  refine OracleComp.support_simulateQ_run'_subset (roImpl prims) S c ?_
  rw [StateT.run'_eq, support_map]
  exact ⟨z, hz, rfl⟩

/-- From the empty cache the search of the dealer fails at most with the chance that its randomizer
search fails. -/
theorem pot_dealerSearch_empty (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (b : Fin (2 ^ layerHeight)) :
    pot prims (dealerSearch parameter seeds b) (· = none) ∅ ≤ (1 - codewordP) ^ randomizerAttemptLimit := by
  refine le_trans ?_ (refSuccess_fail prims parameter seeds b)
  unfold pot dealerSearch refSuccessRun
  rw [roRun_bind, roRun_bind, prEvent_bind_wp, prEvent_bind_wp]
  refine wp_mono _ fun z => ?_
  rcases z with ⟨out, s1⟩
  dsimp only
  cases h : TreeOutput.topTree out with
  | none =>
    simp only [roRun_pure]
    simp
  | some top =>
    simp only [Option.getD_some]
    rw [roRun_map]
    rw [prEvent_map]
    refine prEvent_mono_of_support _ _ _ fun y hy hn => ?_
    exact bottomOf_bottom seeds parameter top b y.1 (fst_mem_support_roRun prims _ s1 y hy) hn

/-! ## Identical until bad with a potential -/

section UntilBad

variable {T R W ι : Type} {spec : OracleSpec ι}

theorem wp_bind_le_add {α β : Type} (mx : ProbComp α) (f₁ f₂ : α → ProbComp β) (F : β → ℝ≥0∞) (g : α → ℝ≥0∞)
    (h : ∀ a, wp (f₁ a) F ≤ wp (f₂ a) F + g a) : wp (mx >>= f₁) F ≤ wp (mx >>= f₂) F + wp mx g := by
  rw [wp_bind, wp_bind, ← wp_add]
  exact wp_mono _ h

theorem wp_stateBind_le_add {S W α β : Type} (x : StateT S (StateT W ProbComp) α)
    (G₁ G₂ : α → StateT S (StateT W ProbComp) β) (F : (β × S) × W → ℝ≥0∞) (g : α → S → W → ℝ≥0∞)
    (h : ∀ a s w, wp (((G₁ a).run s).run w) F ≤ wp (((G₂ a).run s).run w) F + g a s w) (s : S) (w : W) :
    wp (((x >>= G₁).run s).run w) F ≤ wp (((x >>= G₂).run s).run w) F + wp ((x.run s).run w) fun z => g z.1.1 z.1.2 z.2 := by
  simp only [StateT.run_bind]
  exact wp_bind_le_add _ _ _ F _ fun z => h z.1.1 z.1.2 z.2

theorem wp_run_bind {W α γ : Type} (x : StateT W ProbComp α) (K : α → StateT W ProbComp γ) (F : γ × W → ℝ≥0∞)
    (w : W) : wp ((x >>= K).run w) F = wp (x.run w) fun z => wp ((K z.1).run z.2) F := by
  rw [StateT.run_bind, wp_bind]

/-- A common prefix that keeps `g` in the mean and two continuations within `g` give two programs within
`g`, before a common tail `K`. -/
theorem wp_prefix_le {S W α β γ : Type} (X : StateT S (StateT W ProbComp) α)
    (G₁ G₂ : α → StateT S (StateT W ProbComp) β) (K : β × S → StateT W ProbComp γ) (F : γ × W → ℝ≥0∞)
    (g : W → ℝ≥0∞) (hG : ∀ a s w, wp ((((G₁ a).run s) >>= K).run w) F ≤ wp ((((G₂ a).run s) >>= K).run w) F + g w)
    (hX : ∀ s w, wp ((X.run s).run w) (fun z => g z.2) ≤ g w) (s : S) (w : W) :
    wp ((((X >>= G₁).run s) >>= K).run w) F ≤ wp ((((X >>= G₂).run s) >>= K).run w) F + g w := by
  simp only [StateT.run_bind, bind_assoc, wp_bind]
  calc _ ≤ wp ((X.run s).run w) (fun z => wp (((G₂ z.1.1).run z.1.2).run z.2) (fun x => wp ((K x.1).run x.2) F) +
        g z.2) := by
        refine wp_mono _ fun z => ?_
        have h := hG z.1.1 z.1.2 z.2
        simp only [StateT.run_bind, wp_bind] at h
        exact h
    _ ≤ _ := by
        rw [wp_add]
        exact add_le_add le_rfl (hX s w)

theorem wp_stateT_bind_le {W α β : Type} (x : StateT W ProbComp α) (G₁ G₂ : α → StateT W ProbComp β)
    (F : β × W → ℝ≥0∞) (g : α → W → ℝ≥0∞) (c : ℝ≥0∞) (h : ∀ a w, wp ((G₁ a).run w) F ≤ wp ((G₂ a).run w) F + g a w)
    {w : W} (hx : wp (x.run w) (fun z => g z.1 z.2) ≤ c) :
    wp ((x >>= G₁).run w) F ≤ wp ((x >>= G₂).run w) F + c := by
  rw [StateT.run_bind, StateT.run_bind]
  exact (wp_bind_le_add _ _ _ F _ fun (z : α × W) => h z.1 z.2).trans (add_le_add le_rfl hx)

/-- The run of a program on three nested states. -/
def runAll {α : Type} (x : StateT T (StateT R (StateT W ProbComp)) α) (ts : T) (s : R) (w : W) :
    ProbComp (((α × T) × R) × W) :=
  ((x.run ts).run s).run w

theorem runAll_bind {α β : Type} (x : StateT T (StateT R (StateT W ProbComp)) α)
    (f : α → StateT T (StateT R (StateT W ProbComp)) β) (ts : T) (s : R) (w : W) :
    runAll (x >>= f) ts s w = runAll x ts s w >>= fun z => runAll (f z.1.1.1) z.1.1.2 z.1.2 z.2 := by
  simp only [runAll, StateT.run_bind]

theorem runAll_pure {α : Type} (a : α) (ts : T) (s : R) (w : W) :
    runAll (pure a : StateT T (StateT R (StateT W ProbComp)) α) ts s w = pure (((a, ts), s), w) := by
  simp [runAll]

theorem wp_runAll_bind_le {α β : Type} (x : StateT T (StateT R (StateT W ProbComp)) α)
    (f₁ f₂ : α → StateT T (StateT R (StateT W ProbComp)) β) (G₁ G₂ : ((β × T) × R) × W → ℝ≥0∞) (ts : T) (s : R)
    (w : W) (h : ∀ z ∈ support (runAll x ts s w),
      wp (runAll (f₁ z.1.1.1) z.1.1.2 z.1.2 z.2) G₁ ≤ wp (runAll (f₂ z.1.1.1) z.1.1.2 z.1.2 z.2) G₂) :
    wp (runAll (x >>= f₁) ts s w) G₁ ≤ wp (runAll (x >>= f₂) ts s w) G₂ := by
  rw [runAll_bind, runAll_bind, wp_bind, wp_bind]
  exact wp_mono_of_support _ h

theorem wp_le_one {α : Type} (mx : ProbComp α) (f : α → ℝ≥0∞) (hf : ∀ z, f z ≤ 1) : wp mx f ≤ 1 :=
  (wp_mono mx hf).trans_eq (wp_const mx 1)

/-- Two handlers that agree on the steps that stay good give expectations of a function below one that
differ by at most a potential `V`. `V` is at least one on a bad state and does not grow in the mean
along a step of the first handler from a good state. -/
theorem wp_simulateQ_untilBad (I₁ I₂ : QueryImpl spec (StateT T (StateT R (StateT W ProbComp))))
    (bad : T → Prop) (V : T → W → ℝ≥0∞)
    (agree : ∀ t ts s w, ¬ bad ts → ∀ g : ((spec.Range t × T) × R) × W → ℝ≥0∞,
      wp (runAll (I₁ t) ts s w) (fun z => if bad z.1.1.2 then 0 else g z) ≤ wp (runAll (I₂ t) ts s w) g)
    (step : ∀ t ts s w, ¬ bad ts → wp (runAll (I₁ t) ts s w) (fun z => V z.1.1.2 z.2) ≤ V ts w)
    (one : ∀ ts w, bad ts → 1 ≤ V ts w) {α : Type} (oa : OracleComp spec α)
    (f : ((α × T) × R) × W → ℝ≥0∞) (hf : ∀ z, f z ≤ 1) (ts : T) (s : R) (w : W) :
    wp (runAll (simulateQ I₁ oa) ts s w) f ≤ wp (runAll (simulateQ I₂ oa) ts s w) f + V ts w := by
  induction oa using OracleComp.inductionOn generalizing ts s w with
  | pure a =>
    simp only [simulateQ_pure]
    exact le_self_add
  | query_bind t k ih =>
    by_cases hb : bad ts
    · exact ((wp_le_one _ f hf).trans (one ts w hb)).trans le_add_self
    simp only [simulateQ_query_bind, OracleQuery.input_query, OracleQuery.cont_query, liftM, monadLift_self]
    rw [runAll_bind, runAll_bind, wp_bind, wp_bind]
    have hz : ∀ z : ((spec.Range t × T) × R) × W,
        wp (runAll (simulateQ I₁ (k z.1.1.1)) z.1.1.2 z.1.2 z.2) f ≤
          (if bad z.1.1.2 then 0 else wp (runAll (simulateQ I₂ (k z.1.1.1)) z.1.1.2 z.1.2 z.2) f) +
            V z.1.1.2 z.2 := by
      intro z
      by_cases hz : bad z.1.1.2
      · rw [ite_eq_left hz, zero_add]
        exact (wp_le_one _ f hf).trans (one _ _ hz)
      · rw [ite_eq_right hz]
        exact ih _ _ _ _
    refine (wp_mono _ hz).trans ?_
    rw [wp_add]
    exact add_le_add (agree t ts s w hb _) (step t ts s w hb)

/-- `wp_simulateQ_untilBad` with a common continuation on the inner two states. -/
theorem wp_simulateQ_cont_le (I₁ I₂ : QueryImpl spec (StateT T (StateT R (StateT W ProbComp))))
    (bad : T → Prop) (V : T → W → ℝ≥0∞)
    (agree : ∀ t ts s w, ¬ bad ts → ∀ g : ((spec.Range t × T) × R) × W → ℝ≥0∞,
      wp (runAll (I₁ t) ts s w) (fun z => if bad z.1.1.2 then 0 else g z) ≤ wp (runAll (I₂ t) ts s w) g)
    (step : ∀ t ts s w, ¬ bad ts → wp (runAll (I₁ t) ts s w) (fun z => V z.1.1.2 z.2) ≤ V ts w)
    (one : ∀ ts w, bad ts → 1 ≤ V ts w) {α β : Type} (oa : OracleComp spec α) (ts : T)
    (K : α × T → StateT R (StateT W ProbComp) β) (f : (β × R) × W → ℝ≥0∞) (hf : ∀ z, f z ≤ 1) (s : R) (w : W)
    (c : ℝ≥0∞) (hc : V ts w ≤ c) :
    wp (((((simulateQ I₁ oa).run ts) >>= K).run s).run w) f ≤
      wp (((((simulateQ I₂ oa).run ts) >>= K).run s).run w) f + c := by
  simp only [StateT.run_bind, wp_bind]
  exact (wp_simulateQ_untilBad I₁ I₂ bad V agree step one oa _ (fun _ => wp_le_one _ _ hf) ts s w).trans
    (add_le_add le_rfl hc)

end UntilBad

/-! ## The seed generation -/

section SeedGen

/-- The expectations of two independent draws commute. -/
theorem wp_swap {α β : Type} (mx : ProbComp α) (my : ProbComp β) (F : α → β → ℝ≥0∞) :
    wp mx (fun a => wp my (F a)) = wp my (fun b => wp mx (fun a => F a b)) := by
  have h₁ : wp mx (fun a => wp my (F a)) =
      wp (mx >>= fun a => my >>= fun b => pure (a, b)) (fun p => F p.1 p.2) := by
    simp only [wp_bind, wp_pure]
  have h₂ : wp my (fun b => wp mx (fun a => F a b)) =
      wp (my >>= fun b => mx >>= fun a => pure (a, b)) (fun p => F p.1 p.2) := by
    simp only [wp_bind, wp_pure]
  rw [h₁, h₂]
  refine wp_congr_evalDist_map _ ?_
  simp only [map_bind, map_pure]
  exact OracleComp.evalDist_bind_bind_swap mx my (fun a b => pure (F a b))

/-- A call that is a programming call on a cell of `Th` or of the PRF of a term. -/
def BadProgram (t : (WorldSpec C).Domain) : Prop := ¬ SearchSafe t

theorem searchSafe_of_noBad {α : Type} {oa : OracleComp (WorldSpec C) α} (h : NoCall BadProgram oa) :
    AllQueriesSatisfy oa SearchSafe :=
  ((isQueryBoundP_zero_iff _ _).1 ((isQueryBoundP_congr_pred fun _ => not_not).2 ((noCall_iff _ _).1 h))).mono
    fun t ht => by simpa [BadProgram] using ht

theorem noBad_of_noProgram {α : Type} {oa : OracleComp (WorldSpec C) α} (h : NoCall WorldProgramQuery oa) :
    NoCall BadProgram oa :=
  SigningSelectionProof.noCall_mono _ (fun t ht => by
    rcases t with (t | x) | t
    · exact absurd trivial ht
    · trivial
    · exact absurd trivial ht) h

theorem noCall_simulateQ_writer {ω : Type} [EmptyCollection ω] [Append ω] [LawfulAppend ω]
    (p : (WorldSpec C).Domain → Prop) (impl : QueryImpl (LocalSpec C) (WriterT ω (OracleComp (WorldSpec C))))
    (himpl : ∀ t, NoCall p (impl t).run) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    NoCall p (simulateQ impl oa).run := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact noCall_pure _ _
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_query, WriterT.run_bind]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    exact noCall_bind _ (himpl t) fun r => noCall_map _ _ (ih r.1)

theorem noCall_writer_bind (p : (WorldSpec C).Domain → Prop) {α β : Type}
    (x : WriterT (CallLog C) (OracleComp (WorldSpec C)) α) (f : α → WriterT (CallLog C) (OracleComp (WorldSpec C)) β)
    (hx : NoCall p x.run) (hf : ∀ a, NoCall p (f a).run) : NoCall p (x >>= f).run := by
  rw [WriterT.run_bind]
  exact noCall_bind _ hx fun r => by
    rcases r with ⟨a, w₁⟩
    exact noCall_map _ _ (hf a)

theorem noProgram_observe {α : Type} (oa : OracleComp (LocalSpec C) α) :
    NoCall WorldProgramQuery (ThresholdLeanXmss.observe oa) := by
  unfold ThresholdLeanXmss.observe
  refine noCall_simulateQ_writer _ _ (fun t => ?_) oa
  rcases t with u | q | x
  · exact noCall_map _ _ (Collision.noProgram_adversary _)
  · dsimp only
    refine noCall_writer_bind _ _ _ (noCall_map _ _ (Collision.noProgram_adversary _)) fun y => ?_
    exact noCall_writer_bind _ _ _ (noCall_pure _ _) fun _ => noCall_pure _ _
  · exact noCall_map _ _ (Collision.noProgram_adversary _)

theorem noCall_writer_sequenceFin (p : (WorldSpec C).Domain → Prop) {α : Type} :
    ∀ {n : ℕ} (f : Fin n → WriterT (CallLog C) (OracleComp (WorldSpec C)) α),
      (∀ i, NoCall p (f i).run) → NoCall p (OverPermutation.sequenceFin f).run
  | 0, f, _ => noCall_pure _ _
  | n + 1, f, h => by
    simp only [OverPermutation.sequenceFin]
    exact noCall_writer_bind _ _ _ (h 0) fun a => noCall_writer_bind _ _ _
      (noCall_writer_sequenceFin p (fun i : Fin n => f i.succ) fun i => h i.succ) fun rest => noCall_pure _ _

theorem noProgram_stepRound_observed {E Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec α) :
    NoCall WorldProgramQuery (stepRound observedRoles D A noFunctionality state steps).run := by
  unfold stepRound
  rw [ite_eq_right (by simp [callInput_real])]
  refine noCall_writer_bind _ _ _ (noProgram_observe _) fun p => ?_
  refine noCall_writer_bind _ _ _ (noCall_writer_sequenceFin _ _ fun j => ?_) fun steps' => noCall_pure _ _
  split
  · exact noCall_pure _ _
  · split_ifs
    · exact noCall_pure _ _
    · exact noCall_map _ _ (Collision.noProgram_free _)
  · exact noCall_pure _ _

theorem noProgram_executeRounds_observed {E Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α),
      NoCall WorldProgramQuery (executeRounds observedRoles D A noFunctionality fuel state steps).run
  | 0, state, steps => noCall_pure _ _
  | fuel + 1, state, steps => by
    unfold executeRounds
    split_ifs
    · exact noCall_pure _ _
    · exact noCall_writer_bind _ _ _ (noProgram_stepRound_observed D A state steps) fun p =>
        noProgram_executeRounds_observed D A fuel _ _

/-- A draw of the free copy in `loggedWorld` keeps the world. -/
theorem loggedWorld_free_liftComp (D : C.Coalition) {α : Type} (p : ProbComp α) (w : StreamState C × List (Query C)) :
    (simulateQ (loggedWorld prims D) (free (liftComp p (LocalSpec C)))).run w = (fun a => (a, w)) <$> p := by
  induction p using OracleComp.inductionOn generalizing w with
  | pure x => rfl
  | query_bind t oa ih =>
    rw [liftComp_bind, free_bind, simulateQ_bind, free_liftComp_query, StateT.run_bind]
    simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, loggedWorld, streamWorld,
      onHash, StateT.run_mk, localAnswer, QueryImpl.add_apply_inl, unifFwdImpl, countedCells, List.append_nil]
    simp [QueryImpl.liftTarget, map_bind, bind_map_left, Functor.map_map]
    exact bind_congr fun a => ih a w

theorem noBad_program (q : Query C) (hq : ¬ HashPrf q) (value : HashOutput) :
    NoCall BadProgram (ThresholdLeanXmss.program q value) := by
  unfold ThresholdLeanXmss.program counted
  erw [simulateQ_query]
  rw [noCall_iff]
  simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
  exact (noCall_iff _ _).1 (noCall_query _ _ (by simpa [BadProgram, SearchSafe] using hq))

theorem noProgram_startSteps {E α : Type} (D : C.Coalition) (program : C.Party → PartyM C E RealSpec α) :
    NoCall WorldProgramQuery (startSteps worldRoles D program) := by
  unfold startSteps
  refine noCall_sequenceFin _ _ fun i => ?_
  split_ifs
  · exact noCall_pure _ _
  · exact Collision.noProgram_free _

end SeedGen

/-! ## The game -/

section Game

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The mode with no emulated run, where a bottom tree runs only after a search that succeeds. -/
abbrev skipMode : Mode := ⟨true, fun _ => 0⟩

/-- The search of the dealer for bottom tree `b` on the top tree `top`. -/
def bottomSearch (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) : OracleComp (RoSpec C) (Option BottomTree) :=
  bottomOf <$> referenceTree tweakable (prfValue seeds) parameter top (.bottom b)

/-- The potential of the search for `b` in the signing layer. It is the failure of the search when the
oracle answered `tree b`, and the probability of a failure from the cache before. -/
def treePot (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (ts : TsigState C) (w : LogState C) : ℝ≥0∞ :=
  match ts.trees b with
  | some x => if x = none then 1 else 0
  | none => pot prims (bottomSearch parameter seeds top b) (· = none) w.1.1

/-- A search of the dealer failed. -/
def TreesBad (ts : TsigState C) : Prop := ∃ b, ts.trees b = some none

/-- The dealer of the signing layer on the top tree `top`. -/
abbrev gameDealer (D : C.Coalition) (σ : Type) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (dealt : C.Party → Keys C) (top : TopTree) : Dealt C (SharedM C ProbComp (LogState C) σ) :=
  dealtWith (sharedLift (loggedWorld prims D)) parameter dealt top fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)

/-- The signing game of `forge` with the answers of the dealer `dealer`, and the win test. -/
def signCore (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (dealer : Dealt C (SharedM C ProbComp (LogState C) A.net.State)) : SharedM C ProbComp (LogState C) A.net.State Bool := do
  let (forgery, st) ← (simulateQ
    (sharedDealerForge K circuits settings runLimit (loggedWorld prims D) Prod.fst D m A parameter seeds dealt emu dealer)
    (A.forge ⟨dealer.top.root, dealer.parameter⟩ dealer.top)).run ⟨D.1, fun _ => none, [], fun _ => none⟩
  forgeryWins (sharedLift (loggedWorld prims D)) dealer st forgery

omit [Fintype E] [DecidableEq E] in
theorem sharedSigning_false (m : Mode) (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) :
    sharedSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst false m D A parameter seeds dealt emu =
      get >>= fun s => match topHolder D s.operators with
        | none => pure false
        | some (_, _) => referenceTree (fun oa => sharedLift (loggedWorld prims D) (tweakable oa))
            (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) parameter emptyTop .top >>= fun out =>
              signCore prims K circuits settings runLimit m D A parameter seeds dealt emu
                (gameDealer prims D A.net.State parameter seeds dealt ((TreeOutput.topTree out).getD emptyTop)) := by
  unfold sharedSigning signCore sharedDealer
  simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- The runs read only the emulated count of the mode. -/
theorem sharedRuns_skipMode (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (tree : Tree)
    (count : ℕ) :
    sharedRuns K circuits settings runLimit (loggedWorld prims D) Prod.fst skipMode D net parameter seeds dealt emu tree
        count =
      sharedRuns K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net parameter seeds dealt emu tree
        count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [sharedRuns, ih]
    rfl

omit [Fintype E] [DecidableEq E] in
theorem noProg_treeRun (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    UsedHit.NoProg (treeRun K circuits settings noMonitor D net tree) := by
  unfold treeRun
  exact UsedHit.NoProg.get.bind fun s => (UsedHit.NoProg.lift (Collision.noProgram_executePhase D net _ _ _)).bind
    fun r => (UsedHit.NoProg.lift (noCall_pure _ _)).bind fun _ => UsedHit.NoProg.set _

omit [Fintype E] [DecidableEq E] in
theorem noProg_treeRuns (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    ∀ count, UsedHit.NoProg (treeRuns K circuits settings runLimit noMonitor D net tree count)
  | 0 => UsedHit.NoProg.pure _
  | count + 1 => by
    unfold treeRuns
    refine UsedHit.NoProg.get.bind fun s => ?_
    split_ifs
    · exact (noProg_treeRun K circuits settings D net tree).bind fun _ => noProg_treeRuns D net tree count
    · exact UsedHit.NoProg.pure _

/-- A program that erases its flag to a program of the world has the law of the state of the world of
that program. -/
theorem wp_of_flagErases {W σ α : Type} {impl : QueryImpl (WorldSpec C) (StateT W ProbComp)}
    {x : StateT (RealState C σ) (StateT W ProbComp) α} {y : RealM C σ α} (h : FlagErases impl x y)
    (s : RealState C σ) (w : W) (G : W → ℝ≥0∞) :
    wp ((x.run s).run w) (fun z => G z.2) = wp ((simulateQ impl (y.run s)).run w) (fun z => G z.2) := by
  have e := congrArg (fun m => wp (m.run w) (fun z => G z.2)) (h s s rfl)
  simp only [StateT.run_map, wp_map] at e
  exact e

omit [Fintype E] [DecidableEq E] in
/-- The runs keep the potential of each search of the dealer. -/
theorem wp_sharedRuns_pot (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (tree : Tree)
    (count : ℕ) {β : Type} (S : OracleComp (RoSpec C) β) (p : β → Prop) (hS : OnlySign S)
    (s : RealState C net.State) (w : LogState C) :
    wp (((sharedRuns K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net parameter seeds dealt
        emu tree count).run s).run w) (fun z => pot prims S p z.2.1.1) ≤ pot prims S p w.1.1 := by
  rw [wp_of_flagErases (flagErases_sharedRuns_real K circuits settings runLimit (loggedWorld prims D) Prod.fst D net
    parameter seeds dealt emu tree count) s w (fun w => pot prims S p w.1.1)]
  exact wp_pot_simulateQ prims D S p hS _ (searchSafe_of_noCall (noProg_treeRuns K circuits settings runLimit D net tree
    count s)) w

theorem onlySign_dealerSearch (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (b : Fin (2 ^ layerHeight)) : OnlySign (C := C) (dealerSearch parameter seeds b) :=
  onlySign_bind (onlySign_referenceTree seeds parameter emptyTop .top) fun _ =>
    onlySign_map _ (onlySign_referenceTree seeds parameter _ _)

/-! ### The potential along the signing oracles on the world -/

section Keeps

variable (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
  (b : Fin (2 ^ layerHeight))

theorem treePot_congr {ts ts' : TsigState C} (h : ts'.trees b = ts.trees b) (w : LogState C) :
    treePot prims parameter seeds top b ts' w = treePot prims parameter seeds top b ts w := by
  unfold treePot
  rw [h]

/-- A program of the signing layer on the world keeps the potential of the search for `b` in the mean,
from the signing state `ts`. -/
def TreeKeepsAt {α : Type} (x : StateT (TsigState C) (OracleComp (WorldSpec C)) α) (ts : TsigState C) : Prop :=
  ∀ w, wp ((simulateQ (loggedWorld prims D) (x.run ts)).run w)
    (fun z => treePot prims parameter seeds top b z.1.2 z.2) ≤ treePot prims parameter seeds top b ts w

variable {prims D parameter seeds top b}

theorem TreeKeepsAt.bind {α β : Type} {x : StateT (TsigState C) (OracleComp (WorldSpec C)) α}
    {f : α → StateT (TsigState C) (OracleComp (WorldSpec C)) β} {ts : TsigState C}
    (hx : TreeKeepsAt prims D parameter seeds top b x ts) (hf : ∀ a ts', TreeKeepsAt prims D parameter seeds top b (f a) ts') :
    TreeKeepsAt prims D parameter seeds top b (x >>= f) ts := fun w => by
  rw [StateT.run_bind, simulateQ_bind, StateT.run_bind, wp_bind]
  exact (wp_mono _ fun (z : (α × TsigState C) × LogState C) => hf z.1.1 z.1.2 z.2).trans (hx w)

theorem treeKeepsAt_pure {α : Type} (a : α) (ts : TsigState C) :
    TreeKeepsAt prims D parameter seeds top b (pure a : StateT (TsigState C) (OracleComp (WorldSpec C)) α) ts := fun w => by
  simp

theorem treeKeepsAt_get_bind {α : Type} {f : TsigState C → StateT (TsigState C) (OracleComp (WorldSpec C)) α}
    {ts : TsigState C} (h : TreeKeepsAt prims D parameter seeds top b (f ts) ts) :
    TreeKeepsAt prims D parameter seeds top b (get >>= f) ts := by
  intro w
  rw [run_get_bind]
  exact h w

theorem treeKeepsAt_set {ts ts' : TsigState C} (h : ts'.trees b = ts.trees b) :
    TreeKeepsAt prims D parameter seeds top b (set ts' : StateT (TsigState C) (OracleComp (WorldSpec C)) PUnit) ts :=
  fun w => by
  simp only [StateT.run_set, simulateQ_pure, StateT.run_pure, wp_pure]
  exact (treePot_congr prims parameter seeds top b h w).le

theorem treeKeepsAt_modify {f : TsigState C → TsigState C} {ts : TsigState C} (h : (f ts).trees b = ts.trees b) :
    TreeKeepsAt prims D parameter seeds top b (modify f : StateT (TsigState C) (OracleComp (WorldSpec C)) PUnit) ts :=
  fun w => by
  simp only [StateT.run_modify, simulateQ_pure, StateT.run_pure, wp_pure]
  exact (treePot_congr prims parameter seeds top b h w).le

theorem treeKeepsAt_liftM {α : Type} {oa : OracleComp (WorldSpec C) α} (h : NoCall WorldProgramQuery oa)
    (ts : TsigState C) :
    TreeKeepsAt prims D parameter seeds top b (StateT.lift oa : StateT (TsigState C) (OracleComp (WorldSpec C)) α) ts :=
  fun w => by
  change wp ((simulateQ (loggedWorld prims D) (oa >>= fun a => pure (a, ts))).run w) _ ≤ _
  rw [simulateQ_bind, StateT.run_bind, wp_bind]
  simp only [simulateQ_pure, StateT.run_pure, wp_pure]
  unfold treePot
  cases ts.trees b with
  | some x => exact (wp_const _ _).le
  | none =>
    exact wp_pot_simulateQ prims D _ _ (onlySign_map _ (onlySign_referenceTree seeds parameter top _)) oa
      (searchSafe_of_noCall h) w

omit [Fintype E] [DecidableEq E] in
theorem worldDealt₀_bottom (dealt : C.Party → Keys C) (b' : Fin (2 ^ layerHeight)) :
    (worldDealt₀ parameter seeds dealt top).bottom b' =
      free (liftComp (bottomSearch parameter seeds top b') (LocalSpec C)) := by
  unfold worldDealt₀
  rw [DkgCompletenessProof.dealtWith_bottom, ← DkgCompletenessProof.freeHom_referenceTree]
  simp only [bottomSearch, liftComp_map, free, simulateQ_map]

omit [Fintype E] [DecidableEq E] in
theorem treeKeepsAt_bottomOnce (dealt : C.Party → Keys C) (b' : Fin (2 ^ layerHeight)) (ts : TsigState C) :
    TreeKeepsAt prims D parameter seeds top b (bottomOnce (worldDealt₀ parameter seeds dealt top) b') ts := by
  unfold bottomOnce
  refine treeKeepsAt_get_bind ?_
  cases h : ts.trees b' with
  | some x => exact treeKeepsAt_pure _ _
  | none =>
    by_cases hb : b' = b
    · subst hb
      intro w
      simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, simulateQ_bind, simulateQ_pure]
      simp only [liftM, monadLift, MonadLift.monadLift, StateT.run_lift, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure, pure_bind, wp_bind, wp_pure]
      have e : ∀ (x : Option BottomTree) (w' : LogState C), treePot prims parameter seeds top b'
          { ts with trees := Function.update ts.trees b' (some x) } w' = if x = none then 1 else 0 :=
        fun x w' => by simp [treePot]
      have e' : treePot prims parameter seeds top b' ts w =
          pot prims (bottomSearch parameter seeds top b') (· = none) w.1.1 := by
        simp [treePot, h]
      simp only [e, e', worldDealt₀_bottom]
      refine le_of_eq ((wp_logged_free prims D _ (onlySign_map _ (onlySign_referenceTree seeds parameter top _)) w
        (fun a _ => if a = none then 1 else 0)).trans ?_)
      rw [pot, prEvent_eq_wp_indicator]
      rfl
    · simp only
      refine TreeKeepsAt.bind (treeKeepsAt_liftM ?_ ts) fun tree ts' => TreeKeepsAt.bind (treeKeepsAt_modify ?_) fun _ _ => treeKeepsAt_pure _ _
      · rw [worldDealt₀_bottom]
        exact Collision.noProgram_free _
      · exact Function.update_of_ne (Ne.symm hb) _ _

theorem treeKeepsAt_map {α β : Type} {x : StateT (TsigState C) (OracleComp (WorldSpec C)) α} (f : α → β) {ts : TsigState C}
    (hx : TreeKeepsAt prims D parameter seeds top b x ts) : TreeKeepsAt prims D parameter seeds top b (f <$> x) ts := by
  rw [map_eq_bind_pure_comp]
  exact hx.bind fun _ _ => treeKeepsAt_pure _ _

omit [Fintype E] [DecidableEq E] in
theorem noProgram_signRound2 (dealt : C.Party → Keys C) (i : C.Party) (J : C.Quorum) (commitment : Digest)
    (e : KeyIndex) (message : Message) (parts : C.Party → Digest) :
    NoCall WorldProgramQuery (signRound2With (fun oa => free (liftComp oa (LocalSpec C)))
      (fun x => (worldDealt₀ parameter seeds dealt top).part i J x message) parameter J commitment e message parts) := by
  have e₁ := SeedHitProof.hom_signRound2With (DkgCompletenessProof.freeHom (C := C)) (fun oa => oa)
    (fun x => eval (dealt i) i J x message) parameter J commitment e message parts
  have e₂ : signRound2With (fun oa => free (liftComp oa (LocalSpec C)))
      (fun x => (worldDealt₀ parameter seeds dealt top).part i J x message) parameter J commitment e message parts =
      DkgCompletenessProof.freeHom (signRound2With (fun oa => oa) (fun x => eval (dealt i) i J x message) parameter J
        commitment e message parts) := e₁.symm
  rw [e₂]
  exact Collision.noProgram_free _

omit [Fintype E] [DecidableEq E] in
theorem noProgram_part (dealt : C.Party → Keys C) (i : C.Party) (J : C.Quorum) (x : Point) (message : Message) :
    NoCall WorldProgramQuery ((worldDealt₀ parameter seeds dealt top).part i J x message) :=
  Collision.noProgram_free (liftComp (eval (dealt i) i J x message) (LocalSpec C))

omit [Fintype E] [DecidableEq E] in
theorem treeKeepsAt_tsig_corrupt (dealt : C.Party → Keys C) (i : C.Party) (ts : TsigState C) :
    TreeKeepsAt prims D parameter seeds top b
      (tsigOracles (fun oa => free (liftComp oa (LocalSpec C))) (worldDealt₀ parameter seeds dealt top) (.corrupt i))
      ts := by
  unfold tsigOracles
  refine treeKeepsAt_get_bind ?_
  split_ifs
  · exact treeKeepsAt_pure _ _
  · exact (treeKeepsAt_set rfl).bind fun _ _ => treeKeepsAt_pure _ _

omit [Fintype E] [DecidableEq E] in
theorem treeKeepsAt_tsig_tree (dealt : C.Party → Keys C) (b' : Fin (2 ^ layerHeight)) (ts : TsigState C) :
    TreeKeepsAt prims D parameter seeds top b
      (tsigOracles (fun oa => free (liftComp oa (LocalSpec C))) (worldDealt₀ parameter seeds dealt top) (.tree b'))
      ts := by
  unfold tsigOracles
  refine (treeKeepsAt_bottomOnce dealt b' ts).bind fun o ts₁ => ?_
  rcases o with _ | tree
  · exact treeKeepsAt_pure _ _
  · exact (treeKeepsAt_liftM (Collision.noProgram_free _) ts₁).bind fun _ _ => treeKeepsAt_pure _ _

omit [Fintype E] [DecidableEq E] in
theorem treeKeepsAt_tsig_round1 (dealt : C.Party → Keys C) (i : C.Party) (J : C.Quorum) (e : KeyIndex)
    (message : Message) (ts : TsigState C) :
    TreeKeepsAt prims D parameter seeds top b
      (tsigOracles (fun oa => free (liftComp oa (LocalSpec C))) (worldDealt₀ parameter seeds dealt top)
        (.round1 i J e message)) ts := by
  unfold tsigOracles
  refine treeKeepsAt_get_bind ?_
  split_ifs
  · exact treeKeepsAt_pure _ _
  · refine TreeKeepsAt.bind (x := set _) ?_ fun _ ts₁ => ?_
    · exact treeKeepsAt_set rfl
    · exact treeKeepsAt_map _ (treeKeepsAt_liftM (noProgram_part dealt i J _ message) ts₁)

omit [Fintype E] [DecidableEq E] in
theorem treeKeepsAt_tsig_round2 (dealt : C.Party → Keys C) (i : C.Party) (J : C.Quorum) (e : KeyIndex)
    (message : Message) (parts : C.Party → Digest) (ts : TsigState C) :
    TreeKeepsAt prims D parameter seeds top b
      (tsigOracles (fun oa => free (liftComp oa (LocalSpec C))) (worldDealt₀ parameter seeds dealt top)
        (.round2 i J e message parts)) ts := by
  unfold tsigOracles
  refine treeKeepsAt_get_bind ?_
  split_ifs
  · exact treeKeepsAt_pure _ _
  · refine (treeKeepsAt_bottomOnce dealt _ ts).bind fun o ts₁ => ?_
    rcases o with _ | tree
    · exact treeKeepsAt_pure _ _
    refine (treeKeepsAt_liftM (noProgram_part dealt i J _ message) ts₁).bind fun own ts₂ => ?_
    refine (treeKeepsAt_liftM (noProgram_signRound2 dealt i J _ e message _) ts₂).bind fun r ts₃ => ?_
    rcases r with _ | values
    · exact treeKeepsAt_pure _ _
    · exact (treeKeepsAt_modify rfl).bind fun _ _ => treeKeepsAt_pure _ _

omit [Fintype E] [DecidableEq E] in
/-- The signing oracles of the dealer on the world keep the potential of the search for `b` in the mean. -/
theorem treeKeepsAt_tsigOracles (dealt : C.Party → Keys C) (q : (TsigSpec C).Domain) (ts : TsigState C) :
    TreeKeepsAt prims D parameter seeds top b
      (tsigOracles (fun oa => free (liftComp oa (LocalSpec C))) (worldDealt₀ parameter seeds dealt top) q) ts := by
  rcases q with i | b' | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact treeKeepsAt_tsig_corrupt dealt i ts
  · exact treeKeepsAt_tsig_tree dealt b' ts
  · exact treeKeepsAt_tsig_round1 dealt i J e message ts
  · exact treeKeepsAt_tsig_round2 dealt i J e message parts ts

end Keeps

/-! ### The potential along the signing oracles of the game -/

section KeepsShared

variable (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
  (b : Fin (2 ^ layerHeight)) {σ : Type}

/-- A program of the signing layer of the game keeps the potential of the search for `b` in the mean. -/
def TreeKeeps {α : Type} (x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) : Prop :=
  ∀ ts s w, wp (runAll x ts s w) (fun z => treePot prims parameter seeds top b z.1.1.2 z.2) ≤
    treePot prims parameter seeds top b ts w

/-- A program of the game keeps the potential of each search in the mean. -/
def KeepsPot {α : Type} (y : SharedM C ProbComp (LogState C) σ α) : Prop :=
  ∀ {β : Type} (S : OracleComp (RoSpec C) β) (p : β → Prop), OnlySign S → ∀ s w,
    wp ((y.run s).run w) (fun z => pot prims S p z.2.1.1) ≤ pot prims S p w.1.1

variable {prims D parameter seeds top b}

theorem TreeKeeps.bind {α β : Type} {x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α}
    {f : α → StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) β}
    (hx : TreeKeeps prims parameter seeds top b x) (hf : ∀ a, TreeKeeps prims parameter seeds top b (f a)) :
    TreeKeeps prims parameter seeds top b (x >>= f) := fun ts s w => by
  rw [runAll_bind, wp_bind]
  exact (wp_mono _ fun (z : ((α × TsigState C) × RealState C σ) × LogState C) => hf z.1.1.1 z.1.1.2 z.1.2 z.2).trans
    (hx ts s w)

theorem treeKeeps_pure {α : Type} (a : α) :
    TreeKeeps prims parameter seeds top b (pure a : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) :=
  fun ts s w => by simp [runAll_pure]

theorem treeKeeps_lift {α : Type} {y : SharedM C ProbComp (LogState C) σ α} (hy : KeepsPot prims y) :
    TreeKeeps prims parameter seeds top b
      (StateT.lift y : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) := fun ts s w => by
  simp only [runAll, StateT.run_lift, StateT.run_bind, StateT.run_pure, wp_bind, wp_pure]
  unfold treePot
  cases ts.trees b with
  | some x => exact (wp_const _ _).le
  | none => exact hy _ _ (onlySign_map _ (onlySign_referenceTree seeds parameter top _)) s w

theorem keepsPot_world {α : Type} {oa : OracleComp (WorldSpec C) α} (h : NoCall WorldProgramQuery oa) :
    KeepsPot prims (inWorld (σ := σ) (loggedWorld prims D) oa) := fun S p hS s w => by
  simp only [inWorld, StateT.run_lift, StateT.run_bind, StateT.run_pure, wp_bind, wp_pure]
  exact wp_pot_simulateQ prims D S p hS oa (searchSafe_of_noCall h) w

theorem keepsPot_get_map {α : Type} (f : RealState C σ → α) :
    KeepsPot prims (f <$> (get : SharedM C ProbComp (LogState C) σ _)) := fun S p hS s w => by
  simp

theorem keepsPot_modify (f : RealState C σ → RealState C σ) :
    KeepsPot prims (modify f : SharedM C ProbComp (LogState C) σ PUnit) := fun S p hS s w => by
  simp

/-- The signing oracles of the dealer of the game keep the potential, through the world. -/
theorem treeKeeps_tsig (dealt : C.Party → Keys C) (q : (TsigSpec C).Domain) :
    TreeKeeps prims parameter seeds top b
      (tsigOracles (sharedLift (σ := σ) (loggedWorld prims D))
        (SeedHitProof.Dealt.hmap (worldHom (loggedWorld prims D) σ) (worldDealt₀ parameter seeds dealt top)) q) :=
  fun ts s w => by
  have e : (tsigOracles (sharedLift (σ := σ) (loggedWorld prims D))
      (SeedHitProof.Dealt.hmap (worldHom (loggedWorld prims D) σ) (worldDealt₀ parameter seeds dealt top)) q).run ts =
      StateT.lift (simulateQ (loggedWorld prims D)
        ((tsigOracles (fun oa => free (liftComp oa _)) (worldDealt₀ parameter seeds dealt top) q).run ts)) :=
    (SeedHitProof.hom_tsigOracles (worldHom (loggedWorld prims D) σ) (fun oa => free (liftComp oa _))
      (worldDealt₀ parameter seeds dealt top) q ts).symm
  unfold runAll
  rw [e]
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, wp_bind, wp_pure]
  exact treeKeepsAt_tsigOracles dealt q ts w

theorem keepsPot_get : KeepsPot prims (get : SharedM C ProbComp (LogState C) σ _) := fun S p hS s w => by
  simp

theorem treeKeeps_get_bind {α : Type} {f : RealState C σ → StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α}
    (hf : ∀ s, TreeKeeps prims parameter seeds top b (f s)) :
    TreeKeeps prims parameter seeds top b (StateT.lift get >>= f) :=
  (treeKeeps_lift keepsPot_get).bind hf

end KeepsShared

section KeepsHandler

variable (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
  (b : Fin (2 ^ layerHeight))

omit [Fintype E] [DecidableEq E] in
theorem keepsPot_sharedRuns (net : Adversary C E Unit PEmpty PEmpty) (dealt : C.Party → Keys C)
    (emu : C.Party → Option (Keys C)) (tree : Tree) (count : ℕ) :
    KeepsPot prims (sharedRuns K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D net parameter
      seeds dealt emu tree count) := fun S p hS s w =>
  wp_sharedRuns_pot prims K circuits settings runLimit D net parameter seeds dealt emu tree count S p hS s w

/-- The dealer of the signing layer on the computations of the world. -/
abbrev hDealer (σ : Type) (dealt : C.Party → Keys C) : Dealt C (SharedM C ProbComp (LogState C) σ) :=
  SeedHitProof.Dealt.hmap (worldHom (loggedWorld prims D) σ) (worldDealt₀ parameter seeds dealt top)

omit [Fintype E] [DecidableEq E] in
theorem treeKeeps_sign {σ : Type} (dealt : C.Party → Keys C) (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    TreeKeeps prims parameter seeds top b
      ((do
        StateT.lift (modify fun s : RealState C σ => { s with closed := Function.update s.closed (treeOf e) true })
        let s ← StateT.lift get
        match (s.operators i).keys, (s.operators i).top, (s.operators i).bottom (treeOf e) with
        | some _, some _, some _ => tsigOracles (sharedLift (loggedWorld prims D)) (hDealer prims D parameter seeds top σ dealt) q
        | _, _, _ => pure (noAnswer q)) : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) (TsigSpec C q)) := by
  refine (treeKeeps_lift (keepsPot_modify _)).bind fun _ => treeKeeps_get_bind fun s => ?_
  split
  · exact treeKeeps_tsig dealt q
  · exact treeKeeps_pure _

omit [Fintype E] [DecidableEq E] in
theorem treeKeeps_treeRequest (A : DkgTsigAdversary C E) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (b' : Fin (2 ^ layerHeight)) :
    TreeKeeps prims parameter seeds top b
      (sharedDealerOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D A.net parameter seeds
        dealt emu (hDealer prims D parameter seeds top A.net.State dealt) (.tree b')) := by
  unfold sharedDealerOracles
  dsimp only
  refine (treeKeeps_tsig dealt _).bind fun answer => ?_
  refine TreeKeeps.bind ?_ fun _ => treeKeeps_get_bind fun s => ?_
  · exact treeKeeps_lift (keepsPot_sharedRuns prims K circuits settings runLimit D parameter seeds A.net dealt emu _ 1)
  · split <;> exact treeKeeps_pure _

omit [Fintype E] [DecidableEq E] in
/-- Each call of the oracles of `forge` in the real mode keeps the potential of the search for `b`. -/
theorem treeKeeps_dealerForge (A : DkgTsigAdversary C E) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain) :
    TreeKeeps prims parameter seeds top b
      (sharedDealerForge K circuits settings runLimit (loggedWorld prims D) Prod.fst D Mode.real A parameter seeds dealt
        emu (hDealer prims D parameter seeds top A.net.State dealt) t) := by
  rcases t with t | q | q
  · exact treeKeeps_lift (keepsPot_world (Collision.noProgram_adversary _))
  · rcases q with i | b' | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
    · exact treeKeeps_pure _
    · exact treeKeeps_treeRequest prims K circuits settings runLimit D parameter seeds top b A dealt emu b'
    · exact treeKeeps_sign prims D parameter seeds top b dealt i e _
    · exact treeKeeps_sign prims D parameter seeds top b dealt i e _
  · rcases q with _ | state
    · exact treeKeeps_lift (keepsPot_get_map _)
    · exact treeKeeps_lift (keepsPot_modify _)

end KeepsHandler

/-! ### The two modes agree until a search fails -/

section Agree

/-- A failed search of the dealer for `b` gives the answer `none` and the mark `trees b = some none`. -/
theorem tree_none_bad (d : Dealt C (OracleComp (WorldSpec C))) (b' : Fin (2 ^ layerHeight)) (ts : TsigState C)
    (hb : ¬ TreesBad ts) (p : (TsigSpec C).Range (.tree b') × TsigState C)
    (hp : p ∈ support ((tsigOracles (fun oa => free (liftComp oa (LocalSpec C))) d (.tree b')).run ts))
    (hn : p.1 = none) : TreesBad p.2 := by
  unfold tsigOracles bottomOnce at hp
  simp only [liftM, monadLift, MonadLift.monadLift, StateT.run_bind, StateT.run_get, pure_bind, bind_assoc] at hp
  cases h : ts.trees b' with
  | some x =>
    cases x with
    | none => exact absurd ⟨b', h⟩ hb
    | some tree =>
      simp [h] at hp
      obtain ⟨v, -, rfl⟩ := hp
      simp at hn
  | none =>
    simp [h] at hp
    obtain ⟨i, -, hp⟩ := hp
    cases i with
    | none =>
      simp at hp
      subst hp
      exact ⟨b', by simp⟩
    | some tree =>
      simp at hp
      obtain ⟨v, -, rfl⟩ := hp
      simp at hn

variable {σ : Type}

/-- A program of the signing layer that never changes the signing state. -/
def Fixed {α : Type} (x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) : Prop :=
  ∀ ts s w, ∀ z ∈ support (runAll x ts s w), z.1.1.2 = ts

theorem Fixed.bind {α β : Type} {x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α}
    {f : α → StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) β} (hx : Fixed x) (hf : ∀ a, Fixed (f a)) :
    Fixed (x >>= f) := fun ts s w z hz => by
  rw [runAll_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  rw [hf _ _ _ _ z hz, hx ts s w y hy]

theorem fixed_pure {α : Type} (a : α) :
    Fixed (pure a : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) := fun ts s w z hz => by
  simp only [runAll_pure, support_pure, Set.mem_singleton_iff] at hz
  rw [hz]

theorem fixed_lift {α : Type} (y : SharedM C ProbComp (LogState C) σ α) :
    Fixed (StateT.lift y : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α) := fun ts s w z hz => by
  simp only [runAll, StateT.run_lift, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨y', -, rfl⟩ := hz
  rfl

/-- A fixed program from a bad state gives a bad state, so the expectation of a function that is zero on
the bad states is zero. -/
theorem wp_fixed_bad {α : Type} {x : StateT (TsigState C) (SharedM C ProbComp (LogState C) σ) α} (hx : Fixed x)
    {ts : TsigState C} (hb : TreesBad ts) (s : RealState C σ) (w : LogState C)
    (g : ((α × TsigState C) × RealState C σ) × LogState C → ℝ≥0∞) :
    wp (runAll x ts s w) (fun z => if TreesBad z.1.1.2 then 0 else g z) = 0 :=
  le_antisymm (wp_le_const_of_support _ fun z hz => by rw [hx ts s w z hz, ite_eq_left hb]) (zero_le)

theorem tsig_run_eq (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (dealt : C.Party → Keys C) (q : (TsigSpec C).Domain) (ts : TsigState C) :
    (tsigOracles (sharedLift (σ := σ) (loggedWorld prims D))
      (SeedHitProof.Dealt.hmap (worldHom (loggedWorld prims D) σ) (worldDealt₀ parameter seeds dealt top)) q).run ts =
      StateT.lift (simulateQ (loggedWorld prims D)
        ((tsigOracles (fun oa => free (liftComp oa _)) (worldDealt₀ parameter seeds dealt top) q).run ts)) :=
  (SeedHitProof.hom_tsigOracles (worldHom (loggedWorld prims D) σ) (fun oa => free (liftComp oa _))
    (worldDealt₀ parameter seeds dealt top) q ts).symm

/-- The answer `none` to `tree b'` marks a failed search in the game. -/
theorem tsig_tree_none_bad (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (dealt : C.Party → Keys C) (b' : Fin (2 ^ layerHeight)) (ts : TsigState C) (s : RealState C σ)
    (w : LogState C) (hb : ¬ TreesBad ts)
    (z : (((TsigSpec C).Range (.tree b') × TsigState C) × RealState C σ) × LogState C)
    (hz : z ∈ support (runAll (tsigOracles (sharedLift (σ := σ) (loggedWorld prims D))
      (SeedHitProof.Dealt.hmap (worldHom (loggedWorld prims D) σ) (worldDealt₀ parameter seeds dealt top)) (.tree b'))
        ts s w))
    (hn : z.1.1.1 = none) : TreesBad z.1.1.2 := by
  unfold runAll at hz
  rw [tsig_run_eq prims D parameter seeds top dealt] at hz
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have hy' : y.1 ∈ support ((tsigOracles (fun oa => free (liftComp oa _)) (worldDealt₀ parameter seeds dealt top)
      (.tree b')).run ts) := by
    refine OracleComp.support_simulateQ_run'_subset (loggedWorld prims D) _ w ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨y, hy, rfl⟩
  exact tree_none_bad _ b' ts hb y.1 hy' hn

end Agree

section AgreeHandler

variable (D : C.Coalition) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)

omit [Fintype E] [DecidableEq E] in
theorem agree_treeRequest (A : DkgTsigAdversary C E) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (b' : Fin (2 ^ layerHeight)) (ts : TsigState C) (s : RealState C A.net.State) (w : LogState C)
    (hb : ¬ TreesBad ts) (g : (((TsigSpec C).Range (.tree b') × TsigState C) × RealState C A.net.State) × LogState C → ℝ≥0∞) :
    wp (runAll (sharedDealerOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst Mode.real D A.net parameter
        seeds dealt emu (hDealer prims D parameter seeds top A.net.State dealt) (.tree b')) ts s w)
        (fun z => if TreesBad z.1.1.2 then 0 else g z) ≤
      wp (runAll (sharedDealerOracles K circuits settings runLimit (loggedWorld prims D) Prod.fst skipMode D A.net
        parameter seeds dealt emu (hDealer prims D parameter seeds top A.net.State dealt) (.tree b')) ts s w) g := by
  unfold sharedDealerOracles
  dsimp only
  refine wp_runAll_bind_le _ _ _ _ _ _ _ _ fun z hz => ?_
  rw [ite_eq_left (Or.inl rfl : Mode.real.skip = false ∨ z.1.1.1.isSome = true)]
  by_cases ha : z.1.1.1.isSome = true
  · rw [ite_eq_left (Or.inr ha : true = false ∨ z.1.1.1.isSome = true), sharedRuns_skipMode]
    exact wp_mono _ fun z => by split_ifs <;> simp
  · have hn : z.1.1.1 = none := Option.not_isSome_iff_eq_none.mp (by simpa using ha)
    have hbad := tsig_tree_none_bad prims D parameter seeds top dealt b' ts s w hb z hz hn
    rw [wp_fixed_bad ((fixed_lift _).bind fun _ => (fixed_lift _).bind fun s => by split <;> exact fixed_pure _) hbad]
    exact zero_le

omit [Fintype E] [DecidableEq E] in
/-- The two modes agree on each call of `forge` from a state with no failed search, up to the steps that
end in a failed search. -/
theorem agree_dealerForge (A : DkgTsigAdversary C E) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain) (ts : TsigState C) (s : RealState C A.net.State)
    (w : LogState C) (hb : ¬ TreesBad ts)
    (g : ((((LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Range t) × TsigState C) × RealState C A.net.State) ×
      LogState C → ℝ≥0∞) :
    wp (runAll (sharedDealerForge K circuits settings runLimit (loggedWorld prims D) Prod.fst D Mode.real A parameter
        seeds dealt emu (hDealer prims D parameter seeds top A.net.State dealt) t) ts s w)
        (fun z => if TreesBad z.1.1.2 then 0 else g z) ≤
      wp (runAll (sharedDealerForge K circuits settings runLimit (loggedWorld prims D) Prod.fst D skipMode A parameter
        seeds dealt emu (hDealer prims D parameter seeds top A.net.State dealt) t) ts s w) g := by
  have hle : ∀ x : ProbComp ((((LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Range t × TsigState C) ×
      RealState C A.net.State) × LogState C), wp x (fun z => if TreesBad z.1.1.2 then 0 else g z) ≤ wp x g :=
    fun x => wp_mono _ fun z => by split_ifs <;> simp
  rcases t with t | q | q
  · exact hle _
  · rcases q with i | b' | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
    · exact hle _
    · exact agree_treeRequest prims K circuits settings runLimit D parameter seeds top A dealt emu b' ts s w hb g
    · exact hle _
    · exact hle _
  · exact hle _

end AgreeHandler

omit [Fintype E] [DecidableEq E] in
/-- The signing game with the dealer on a fixed top tree, in the two modes. -/
theorem wp_signCore_le (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C)) (top : TopTree)
    (s : RealState C A.net.State) (w : LogState C) (f : (Bool × RealState C A.net.State) × LogState C → ℝ≥0∞)
    (hf : ∀ z, f z ≤ 1) :
    wp (((signCore prims K circuits settings runLimit Mode.real D A parameter seeds dealt emu
        (gameDealer prims D A.net.State parameter seeds dealt top)).run s).run w) f ≤
      wp (((signCore prims K circuits settings runLimit skipMode D A parameter seeds dealt emu
        (gameDealer prims D A.net.State parameter seeds dealt top)).run s).run w) f +
        ∑ b, pot prims (bottomSearch parameter seeds top b) (· = none) w.1.1 := by
  have hd : gameDealer prims D A.net.State parameter seeds dealt top = hDealer prims D parameter seeds top A.net.State dealt :=
    (hmap_dealtWith_hom (worldHom (loggedWorld prims D) A.net.State) (fun oa => free (liftComp oa _)) parameter dealt top
      fun x => free (liftComp (prfValue seeds x) _)).symm
  rw [hd]
  unfold signCore
  refine wp_simulateQ_cont_le _ _ TreesBad (fun ts w => ∑ b, treePot prims parameter seeds top b ts w)
    (fun t ts s w hb g => agree_dealerForge prims K circuits settings runLimit D parameter seeds top A dealt emu t ts s w hb g)
    (fun t ts s w _ => ?_) (fun ts w hb => ?_) _ _ _ f hf s w _ ?_
  · rw [wp_finsetSum]
    exact Finset.sum_le_sum fun b _ => treeKeeps_dealerForge prims K circuits settings runLimit D parameter seeds top b A
      dealt emu t ts s w
  · obtain ⟨b, hb⟩ := hb
    refine le_trans ?_ (Finset.single_le_sum (f := fun b => treePot prims parameter seeds top b ts w)
      (fun _ _ => zero_le) (Finset.mem_univ b))
    simp [treePot, hb]
  · simp [treePot]

/-- The top tree of the dealer keeps the potential of the searches. -/
theorem wp_dealerTop (D : C.Coalition) {σ : Type} (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (s : RealState C σ) (w : LogState C) :
    wp (((referenceTree (fun oa => sharedLift (loggedWorld prims D) (tweakable oa))
        (fun x => sharedLift (loggedWorld prims D) (prfValue seeds x)) parameter emptyTop .top :
          SharedM C ProbComp (LogState C) σ _).run s).run w)
        (fun z => ∑ b, pot prims (bottomSearch parameter seeds ((TreeOutput.topTree z.1.1).getD emptyTop) b) (· = none)
          z.2.1.1) =
      ∑ b, pot prims (dealerSearch parameter seeds b) (· = none) w.1.1 := by
  have e₁ : referenceTree (fun oa => sharedLift (σ := σ) (loggedWorld prims D) (tweakable oa))
      (fun x => sharedLift (σ := σ) (loggedWorld prims D) (prfValue seeds x)) parameter emptyTop .top =
      StateT.lift (simulateQ (loggedWorld prims D)
        (free (liftComp (referenceTree tweakable (prfValue seeds) parameter emptyTop .top) (LocalSpec C)))) := by
    rw [DkgCompletenessProof.freeHom_referenceTree]
    exact (SeedHitProof.hom_referenceTree (worldHom (loggedWorld prims D) σ) (fun oa => free (liftComp (tweakable oa) _))
      (fun x => free (liftComp (prfValue seeds x) _)) parameter emptyTop .top).symm
  rw [e₁]
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, wp_bind, wp_pure]
  rw [wp_finsetSum]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine (wp_logged_free prims D _ (onlySign_referenceTree seeds parameter emptyTop .top) w
    (fun a c => pot prims (bottomSearch parameter seeds ((TreeOutput.topTree a).getD emptyTop) b) (· = none) c)).trans ?_
  unfold pot dealerSearch bottomSearch
  rw [roRun_bind, prEvent_bind_wp]

omit [Fintype E] [DecidableEq E] in
theorem wp_sharedSigning_le (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (s : RealState C A.net.State) (w : LogState C) (f : (Bool × RealState C A.net.State) × LogState C → ℝ≥0∞)
    (hf : ∀ z, f z ≤ 1) :
    wp (((sharedSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst false Mode.real D A parameter
        seeds dealt emu).run s).run w) f ≤
      wp (((sharedSigning K circuits settings runLimit (loggedWorld prims D) Prod.fst false skipMode D A parameter
        seeds dealt emu).run s).run w) f +
        ∑ b, pot prims (dealerSearch parameter seeds b) (· = none) w.1.1 := by
  rw [sharedSigning_false, sharedSigning_false]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases topHolder D s.operators with
  | none => exact le_self_add
  | some kt =>
    simp only
    rw [← wp_dealerTop prims D parameter seeds s w]
    exact wp_stateBind_le_add _ _ _ f _ (fun out s' w' =>
      wp_signCore_le prims K circuits settings runLimit D A parameter seeds dealt emu _ s' w' f hf) s w

omit [Fintype E] [DecidableEq E] in
theorem wp_sharedRest_le (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (start : RealState C A.net.State) (w : LogState C) (f : (Bool × Bool) × LogState C → ℝ≥0∞) (hf : ∀ z, f z ≤ 1) :
    wp ((sharedRest K circuits settings runLimit (loggedWorld prims D) Prod.fst false Mode.real D A parameter seeds
        dealt emu start).run w) f ≤
      wp ((sharedRest K circuits settings runLimit (loggedWorld prims D) Prod.fst false skipMode D A parameter seeds
        dealt emu start).run w) f +
        ∑ b, pot prims (dealerSearch parameter seeds b) (· = none) w.1.1 := by
  unfold sharedRest
  rw [sharedRuns_skipMode]
  refine wp_prefix_le _ _ _ _ f (fun w => ∑ b, pot prims (dealerSearch parameter seeds b) (· = none) w.1.1)
    (fun _ s' w' => ?_) (fun s' w' => ?_) start w
  · rw [wp_run_bind, wp_run_bind]
    exact wp_sharedSigning_le prims K circuits settings runLimit D A parameter seeds dealt emu s' w' _
      fun z => wp_le_one _ _ hf
  · rw [wp_finsetSum]
    exact Finset.sum_le_sum fun b _ => wp_sharedRuns_pot prims K circuits settings runLimit D A.net parameter seeds
      dealt emu .top runLimit _ _ (onlySign_dealerSearch parameter seeds b) s' w'

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The seed generation keeps the mean of the potential of each search of the dealer, from the empty
caches. -/
theorem wp_worldSeedGen_pot (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) :
    wp ((simulateQ (loggedWorld prims D) (worldSeedGen D net)).run ((∅, ∅), []))
        (fun z => ∑ b, pot prims (dealerSearch z.1.2.1 z.1.2.2.1 b) (· = none) z.2.1.1) ≤
      ∑ _b : Fin (2 ^ layerHeight), (1 - codewordP) ^ randomizerAttemptLimit := by
  rw [wp_finsetSum]
  refine Finset.sum_le_sum fun b _ => ?_
  unfold worldSeedGen
  rw [simulateQ_bind, StateT.run_bind, wp_bind]
  refine (wp_mono (post' := fun a => wp prawnsKeyGen (fun x => pot prims (dealerSearch x.1 x.2.1 b) (· = none)
    a.2.1.1)) _ fun a => ?_).trans ?_
  · rcases a with ⟨⟨state, early⟩, w₁⟩
    dsimp only
    rw [simulateQ_bind, StateT.run_bind, wp_bind, loggedWorld_free_liftComp, wp_map]
    refine wp_mono _ fun x => ?_
    rcases x with ⟨parameter, seeds, dealt⟩
    simp only [Function.comp_apply]
    refine (le_of_eq (wp_congr_of_support _ fun z hz => ?_)).trans
      (wp_pot_simulateQ prims D _ _ (onlySign_dealerSearch parameter seeds b) _ (searchSafe_of_noBad ?_) w₁)
    · have hz' := OracleComp.support_simulateQ_run'_subset (loggedWorld prims D) _ w₁
        (by rw [StateT.run'_eq, support_map]; exact ⟨z, hz, rfl⟩)
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz'
      obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, h⟩ := hz'
      rw [h]
    · refine noCall_bind _ (noBad_of_noProgram (Collision.noProgram_free _)) fun parts => ?_
      refine noCall_bind _ (noBad_of_noProgram (noProgram_startSteps D _)) fun steps => ?_
      refine noCall_bind _ (noBad_of_noProgram (noProgram_stepRound_observed D net _ _)) fun r => ?_
      refine noCall_bind _ (noBad_of_noProgram (Collision.noProgram_free _)) fun high => ?_
      refine noCall_bind _ (noBad_program _ (by simp [HashPrf]) _) fun _ => ?_
      refine noCall_bind _ (noCall_mapM _ _ _ fun T => ?_) fun _ => ?_
      · split
        · exact noBad_program _ (by simp [HashPrf]) _
        · exact noCall_pure _ _
      refine noCall_bind _ (noCall_mapM _ _ _ fun j => noCall_mapM _ _ _ fun i => ?_) fun _ => ?_
      · split
        · exact noBad_program _ (by simp [HashPrf]) _
        · exact noCall_pure _ _
      exact noCall_bind _ (noBad_of_noProgram (noProgram_executeRounds_observed D net _ _ _)) fun _ => noCall_pure _ _
  · rw [wp_swap]
    refine (wp_mono (post' := fun x : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) =>
      pot prims (dealerSearch x.1 x.2.1 b) (· = none) ∅) _ fun x => ?_).trans ?_
    · exact wp_pot_simulateQ prims D _ _ (onlySign_dealerSearch x.1 x.2.1 b) _
        (searchSafe_of_noCall (noProgram_observe _)) ((∅, ∅), [])
    · exact (wp_mono prawnsKeyGen fun x : PublicParameter × (C.Term → HashOutput) × (C.Party → Keys C) =>
        pot_dealerSearch_empty prims x.1 x.2.1 b).trans (wp_const _ _).le

omit [Fintype E] [DecidableEq E] in
theorem wp_sharedDealt_le (D : C.Coalition) (A : DkgTsigAdversary C E) (F : DealtOut C × LogState C → ℝ≥0∞)
    (hF : ∀ z, F z ≤ 1) :
    wp ((sharedDealt prims K circuits settings runLimit Mode.real D A).run ((∅, ∅), [])) F ≤
      wp ((sharedDealt prims K circuits settings runLimit skipMode D A).run ((∅, ∅), [])) F +
        ∑ _b : Fin (2 ^ layerHeight), (1 - codewordP) ^ randomizerAttemptLimit := by
  unfold sharedDealt
  refine wp_stateT_bind_le _ _ _ F (fun z w => ∑ b, pot prims (dealerSearch z.2.1 z.2.2.1 b) (· = none) w.1.1) _
    (fun ⟨state, parameter, seeds, dealt, emu⟩ w => ?_) ?_
  rotate_left
  · dsimp only
    rw [wp_run_bind, wp_run_bind]
    exact wp_sharedRest_le prims K circuits settings runLimit D A parameter seeds dealt emu _ w _
      fun _ => wp_le_one _ _ hF
  · exact wp_worldSeedGen_pot prims D A.net

omit [Fintype E] [DecidableEq E] in
/-- No run after a failed search of the dealer, for each event on the result of `sharedDealt`. -/
theorem dealtProb_search (D : C.Coalition) (A : DkgTsigAdversary C E) (event : DealtOut C × LogState C → Prop) :
    dealtProb prims K circuits settings runLimit Mode.real D A event ≤
      dealtProb prims K circuits settings runLimit ⟨true, fun _ => 0⟩ D A event + 2 ^ layerHeight * searchFailure := by
  unfold dealtProb
  have h := wp_sharedDealt_le prims K circuits settings runLimit D A (fun r => if event r then 1 else 0)
    fun z => by split_ifs <;> simp
  rw [← prEvent_eq_wp_indicator, ← prEvent_eq_wp_indicator, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  have hne : (2 : ℝ≥0∞) ^ layerHeight * (1 - codewordP) ^ randomizerAttemptLimit ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      (ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self))
  refine (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, hne⟩) h).trans_eq ?_
  rw [ENNReal.toReal_add (prEvent_ne_top _) hne, ENNReal.toReal_mul, toReal_failure]
  simp

omit [Fintype E] [DecidableEq E] in
/-- The hop `SharedSearch`. -/
theorem sharedSearch : SharedSearch prims K circuits settings runLimit := fun D A =>
  dealtProb_search prims K circuits settings runLimit D A _

end Game

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.dealtProb_search' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.dealtProb_search

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSearch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.sharedSearch
