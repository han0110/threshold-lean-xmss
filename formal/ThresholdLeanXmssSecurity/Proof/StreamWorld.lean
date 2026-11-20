import ThresholdLeanXmssSecurity.Proof.Tree
import ThresholdLeanXmssSecurity.Proof.Coupling
import VCVio.ProgramLogic.Relational.Basic
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# The worlds of the hidden streams

`streamWorld` answers each free stream under a hidden key with a random function, and `keyWorld` and
`lazyKeyWorld` give each hidden key name its own AES key. `keyWorld_coupling` bounds the change from
the real hidden keys to these AES keys by the stream-key bad event `probBad_streamKey`. The file also
holds the reduction to the PRF game (`reductionReal`, `reductionIdeal`), the round runner
`executeSteps` with the continuations `continueStep`, and the coupling of two runs up to a bad event.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Reduction
variable {C : Committee} {E : Type} (prims : Primitives) [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The probability that `prgReduction` outputs `1` against the real streams. -/
def reductionReal (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) : ℝ :=
  (Pr{let z ← (hiddenStreams (C := C) prims.aes).prfRealExperiment (prgReduction prims D game)}[z = true]).toReal

/-- The probability that `prgReduction` outputs `1` against a random function. -/
def reductionIdeal (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) : ℝ :=
  (Pr{let z ← PRFScheme.prfIdealExperiment (prgReduction prims D game)}[z = true]).toReal

end Reduction

section Fuse
variable {ι κ : Type} {spec : OracleSpec ι} {spec₂ : OracleSpec κ} {σ τ : Type}

theorem run_simulateQ_fuse (inner : QueryImpl spec (StateT σ (OracleComp spec₂)))
    (outer : QueryImpl spec₂ (StateT τ ProbComp)) {α : Type} (oa : OracleComp spec α) (s : σ) (t : τ) :
    (simulateQ outer ((simulateQ inner oa).run s)).run t =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (fuse inner outer) oa).run (s, t) := by
  induction oa using OracleComp.inductionOn generalizing s t with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, map_bind]
    simp only [fuse, StateT.run_mk, bind_map_left]
    refine bind_congr fun r => ?_
    exact ih r.1.1 r.1.2 r.2

/-- One handler into a state over the oracles of a stateless outer handler. -/
def fuseStateless (inner : QueryImpl spec (StateT σ (OracleComp spec₂))) (outer : QueryImpl spec₂ ProbComp) :
    QueryImpl spec (StateT σ ProbComp) := fun q => StateT.mk fun s => simulateQ outer ((inner q).run s)

theorem simulateQ_run_fuseStateless (inner : QueryImpl spec (StateT σ (OracleComp spec₂)))
    (outer : QueryImpl spec₂ ProbComp) {α : Type} (oa : OracleComp spec α) (s : σ) :
    simulateQ outer ((simulateQ inner oa).run s) = (simulateQ (fuseStateless inner outer) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind]
    simp only [fuseStateless, StateT.run_mk]
    exact bind_congr fun r => ih r.1 r.2

end Fuse

attribute [local instance] Classical.propDecidable

section StreamWorld
variable {C : Committee} (prims : Primitives)

/-- The cache of a random function on the streams under the hidden keys. -/
abbrev HiddenCache (C : Committee) := (((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).QueryCache

/-- A handler of the hash cache on the first component. -/
def onHash {α : Type} (m : StateT (HashCache C) ProbComp α) : StateT (HashCache C × HiddenCache C) ProbComp α :=
  StateT.mk fun st => (fun r => (r.1, (r.2, st.2))) <$> m.run st.1

/-- The world where each free stream under a hidden key is a random function. -/
def streamWorld (D : C.Coalition) : QueryImpl (WorldSpec C) (StateT (HashCache C × HiddenCache C) ProbComp) :=
  fun t => match t with
  | .inl t => onHash ((localAnswer (C := C) prims + programAnswer (C := C)) t)
  | .inr (.inr (.inr x)) => if Hidden D x.1 then StateT.mk fun st =>
        (fun r => (r.1, (st.1, r.2))) <$>
          ((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle ((x.1, x.2.1), x.2.2)).run st.2
      else onHash (localAnswer prims (.inr (.inr x)))
  | .inr t => onHash (localAnswer prims t)

theorem prfIdealExp_prgReduction (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) :
    PRFScheme.prfIdealExperiment (prgReduction prims D game) = (simulateQ (streamWorld prims D) game).run' (∅, ∅) := by
  unfold PRFScheme.prfIdealExperiment prgReduction
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map, run_simulateQ_fuse, Functor.map_map]
  have hl : ∀ {β : Type} (ob : ProbComp β), simulateQ PRFScheme.prfIdealQueryImpl
      (liftM ob : OracleComp (StreamSpec C) β) = liftM ob := fun ob =>
    PRFScheme.simulateQ_prfIdealQueryImpl_liftComp ob
  rw [show fuse _ PRFScheme.prfIdealQueryImpl = streamWorld prims D from ?_]
  funext t
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals simp only [fuse, streamWorld, onHash]
  all_goals try split_ifs
  all_goals congr 1
  all_goals funext st
  case pos h =>
    simp only [QueryImpl.add_apply_inr, if_pos h]
    simp [StateT.run_bind]
  case neg h =>
    simp only [QueryImpl.add_apply_inr]
    rw [if_neg h]
    simp [hl, Functor.map_map]
  all_goals first | (simp [hl, Functor.map_map]; done) | (simp [hl, Functor.map_map]; rfl)

/-- The world where each free stream under a hidden key uses its own AES key. -/
def keyWorld (D : C.Coalition) (keys : KeyName C × HashOutput → Digest) :
    QueryImpl (WorldSpec C) (StateT (HashCache C) ProbComp) :=
  fun t => match t with
  | .inl t => (localAnswer (C := C) prims + programAnswer (C := C)) t
  | .inr (.inr (.inr x)) => if Hidden D x.1 then pure (prims.aes.eval (keys (x.1, x.2.1)) x.2.2)
      else localAnswer prims (.inr (.inr x))
  | .inr t => localAnswer prims t

theorem prfRealExp_prgReduction (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) :
    (hiddenStreams (C := C) prims.aes).prfRealExperiment (prgReduction prims D game) =
      ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys => (simulateQ (keyWorld prims D keys) game).run' ∅ := by
  unfold PRFScheme.prfRealExperiment prgReduction
  refine bind_congr fun keys => ?_
  simp only [StateT.run'_eq, simulateQ_map, simulateQ_run_fuseStateless]
  have hl : ∀ {β : Type} (ob : ProbComp β), simulateQ ((hiddenStreams (C := C) prims.aes).prfRealQueryImpl keys)
      (liftM ob : OracleComp (StreamSpec C) β) = ob := fun ob =>
    PRFScheme.simulateQ_prfRealQueryImpl_liftComp _ _ ob
  rw [show fuseStateless _ (PRFScheme.prfRealQueryImpl _ keys) = keyWorld prims D keys from ?_]
  funext t
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals simp only [fuseStateless, keyWorld]
  all_goals try split_ifs
  case pos h =>
    simp only [QueryImpl.add_apply_inr]
    rw [if_pos h]
    refine StateT.ext fun s => ?_
    simp [StateT.run_lift, hiddenStreams]
  case neg h =>
    simp only [QueryImpl.add_apply_inr]
    rw [if_neg h]
    refine StateT.ext fun s => ?_
    simp [hl]
  all_goals refine StateT.ext fun s => ?_
  all_goals first | (simp [hl]; done) | (simp [hl]; rfl)

/-- The cache of a lazy table of AES keys for the hidden key names. -/
abbrev KeyCache (C : Committee) := ((KeyName C × HashOutput) →ₒ Digest).QueryCache

/-- `keyWorld` with the table of AES keys sampled lazily. -/
def lazyKeyWorld (D : C.Coalition) : QueryImpl (WorldSpec C) (StateT (HashCache C × KeyCache C) ProbComp) :=
  fun t => match t with
  | .inl t => StateT.mk fun st => (fun r => (r.1, (r.2, st.2))) <$>
      ((localAnswer (C := C) prims + programAnswer (C := C)) t).run st.1
  | .inr (.inr (.inr x)) => if Hidden D x.1 then StateT.mk fun st =>
        (fun r => (prims.aes.eval r.1 x.2.2, (st.1, r.2))) <$>
          ((((KeyName C × HashOutput) →ₒ Digest).randomOracle (x.1, x.2.1)).run st.2)
      else StateT.mk fun st => (fun r => (r.1, (r.2, st.2))) <$> (localAnswer prims (.inr (.inr x))).run st.1
  | .inr t => StateT.mk fun st => (fun r => (r.1, (r.2, st.2))) <$> (localAnswer prims t).run st.1

/-- The eager table of AES keys is the lazy one. -/
def KeyTableLazy (D : C.Coalition) : Prop :=
  ∀ game : OracleComp (WorldSpec C) Bool,
    Pr{let z ← ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
        (simulateQ (keyWorld prims D keys) game).run' ∅}[z = true] =
      Pr{let z ← (simulateQ (lazyKeyWorld prims D) game).run' (∅, ∅)}[z = true]

end StreamWorld

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

open OracleComp.DeferredSampling

section KeyTable
variable {C : Committee} (prims : Primitives)

/-- A query that both worlds answer with the same step on the hash cache. -/
theorem evalDist_lazyKeyWorld_common (D : C.Coalition) {α : Type} (t : (WorldSpec C).Domain)
    (k : (WorldSpec C).Range t → OracleComp (WorldSpec C) α) (m : StateT (HashCache C) ProbComp ((WorldSpec C).Range t))
    (hl : lazyKeyWorld prims D t = StateT.mk fun st => (fun r => (r.1, (r.2, st.2))) <$> m.run st.1)
    (hk : ∀ g, keyWorld prims D g t = m)
    (ih : ∀ u (s : HashCache C) (c : KeyCache C),
      (simulateQ (lazyKeyWorld prims D) (k u)).run' (s, c) =ᵈ
        (($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g =>
          (simulateQ (keyWorld prims D (tableExtending c g)) (k u)).run' s))
    (s : HashCache C) (c : KeyCache C) :
    (simulateQ (lazyKeyWorld prims D) ((liftM ((WorldSpec C).query t) : OracleComp (WorldSpec C) _) >>= k)).run' (s, c) =ᵈ
      (($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g =>
        (simulateQ (keyWorld prims D (tableExtending c g)) ((liftM ((WorldSpec C).query t) : OracleComp (WorldSpec C) _) >>= k)).run' s) := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
    StateT.run'_eq, StateT.run_bind, hl, hk, StateT.run_mk, bind_map_left, map_bind]
  refine EvalDistEq.trans ?_ (OracleComp.EvalDistEq.bind_bind_swap _ _ _)
  refine EvalDistEq.bind_right _ fun r => ?_
  have := ih r.1 r.2 c
  simp only [StateT.run'_eq] at this
  exact this

/-- Overwriting one entry of a uniform table with a fresh uniform value keeps the table uniform,
under any continuation. -/
theorem evalDist_update_bind {D R β : Type} [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)] (t : D) (Ψ : (D → R) → ProbComp β) :
    (($ᵗ R) >>= fun u => ($ᵗ (D → R)) >>= fun g => Ψ (Function.update g t u)) =ᵈ
      (($ᵗ (D → R)) >>= Ψ) :=
  evalDistEq_uniformSample_bind_update t Ψ

theorem evalDist_lazyKeyWorld (D : C.Coalition) {α : Type} (game : OracleComp (WorldSpec C) α) :
    ∀ (s : HashCache C) (c : KeyCache C),
    (simulateQ (lazyKeyWorld prims D) game).run' (s, c) =ᵈ
      (($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g =>
        (simulateQ (keyWorld prims D (tableExtending c g)) game).run' s) := by
  induction game using OracleComp.inductionOn with
  | pure a =>
    intro s c
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | query_bind t k ih =>
    intro s c
    rcases t with ((u | q | x) | p) | (u | q | x)
    · exact evalDist_lazyKeyWorld_common prims D _ k _ rfl (fun _ => rfl) ih s c
    · exact evalDist_lazyKeyWorld_common prims D _ k _ rfl (fun _ => rfl) ih s c
    · exact evalDist_lazyKeyWorld_common prims D _ k _ rfl (fun _ => rfl) ih s c
    · exact evalDist_lazyKeyWorld_common prims D _ k _ rfl (fun _ => rfl) ih s c
    · exact evalDist_lazyKeyWorld_common prims D _ k _ rfl (fun _ => rfl) ih s c
    · exact evalDist_lazyKeyWorld_common prims D _ k _ rfl (fun _ => rfl) ih s c
    · by_cases h : Hidden D x.1
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
          StateT.run'_eq, StateT.run_bind]
        simp only [lazyKeyWorld, keyWorld, if_pos h, StateT.run_mk, bind_map_left, StateT.run_pure, pure_bind]
        rcases hc : c (x.1, x.2.1) with _ | u
        · rw [QueryImpl.withCaching_run_none _ hc]
          set y := (x.1, x.2.1) with hy
          let Ψ : (KeyName C × HashOutput → Digest) → ProbComp α := fun g =>
            (fun x => x.1) <$> (simulateQ (keyWorld prims D (tableExtending c g))
              (k (prims.aes.eval (tableExtending c g y) x.2.2))).run s
          have step : ∀ u, ((fun x => x.1) <$> (simulateQ (lazyKeyWorld prims D)
              (k (prims.aes.eval u x.2.2))).run (s, QueryCache.cacheQuery c y u)) =ᵈ
              (($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g => Ψ (Function.update g y u)) := by
            intro u
            have := ih (prims.aes.eval u x.2.2) s (QueryCache.cacheQuery c y u)
            simp only [StateT.run'_eq] at this
            refine this.trans ?_
            refine EvalDistEq.bind_right _ fun g => ?_
            simp only [Ψ]
            rw [tableExtending_cacheQuery, tableExtending_update_of_none c g hc]
            have e : tableExtending c (Function.update g y u) y = u := by simp [tableExtending, hc]
            rw [e]
          rw [bind_map_left, map_bind]
          exact (EvalDistEq.bind_right _ step).trans (evalDist_update_bind y Ψ)
        · rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
          have := ih (prims.aes.eval u x.2.2) s c
          simp only [StateT.run'_eq] at this
          refine this.trans ?_
          have e : ∀ g : KeyName C × HashOutput → Digest, tableExtending c g (x.1, x.2.1) = u := fun g => by
            simp [tableExtending, hc]
          simp only [e, EvalDistEq.refl]
      · exact evalDist_lazyKeyWorld_common prims D _ k (localAnswer prims (.inr (.inr x)))
          (by simp only [lazyKeyWorld, if_neg h]; rfl)
          (fun _ => by simp only [keyWorld, if_neg h]) ih s c

theorem keyTableLazy (D : C.Coalition) : KeyTableLazy prims D := by
  intro game
  have h := evalDist_lazyKeyWorld prims D game ∅ ∅
  simp only [tableExtending_empty] at h
  exact (h.prEvent_eq (· = true)).symm

end KeyTable

end ThresholdLeanXmssSecurity

section FreshStreams
set_option backward.isDefEq.respectTransparency false
namespace ThresholdLeanXmssSecurity
open OracleComp.DeferredSampling
attribute [local instance] Classical.propDecidable

/-- Cache a finite table at the queried addresses, in query order. -/
def cacheFin {D R : Type} [DecidableEq D] : ∀ {n : ℕ},
    (Fin n → D) → (Fin n → R) → (D →ₒ R).QueryCache → (D →ₒ R).QueryCache
  | 0, _, _, c => c
  | _ + 1, addr, vals, c => cacheFin (fun i => addr i.succ) (fun i => vals i.succ)
      (c.cacheQuery (addr 0) (vals 0))

/-- Distinct fresh queries can be sampled first, with their exact final cache retained. -/
theorem randomOracle_sequenceFin_fresh {D R : Type} [DecidableEq D] [SampleableType R] :
    ∀ {n : ℕ} (addr : Fin n → D) (ha : Function.Injective addr) (c : (D →ₒ R).QueryCache)
      (hc : ∀ i, c (addr i) = none),
      (OverPermutation.sequenceFin fun i => (D →ₒ R).randomOracle (addr i)).run c =
        (fun vals => (vals, cacheFin addr vals c)) <$>
          OverPermutation.sequenceFin (fun _ : Fin n => ($ᵗ R))
  | 0, addr, ha, c, hc => by simp [OverPermutation.sequenceFin, cacheFin]
  | n + 1, addr, ha, c, hc => by
    simp only [OverPermutation.sequenceFin, StateT.run_bind]
    rw [QueryImpl.withCaching_run_none _ (hc 0), bind_map_left]
    simp only [map_bind]
    refine bind_congr fun a => ?_
    rw [randomOracle_sequenceFin_fresh (fun i : Fin n => addr i.succ)
      (ha.comp (Fin.succ_injective n)) _ (fun i => ?_)]
    · simp only [bind_map_left, StateT.run_pure, map_pure, cacheFin]
      rfl
    · rw [QueryCache.cacheQuery_of_ne]
      · exact hc i.succ
      · exact fun h => Fin.succ_ne_zero i (ha h)

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

/-- Independent uniform samples at finite coordinates are a uniform function table. -/
theorem evalDist_sequenceFin_uniform {R : Type} [SampleableType R] (n : ℕ) :
    OverPermutation.sequenceFin (fun _ : Fin n => ($ᵗ R)) =ᵈ $ᵗ (Fin n → R) := by
  classical
  let : MeasurableSpace (Fin n → R) := ⊤
  let oa : OracleComp (Fin n →ₒ R) (Fin n → R) :=
    OverPermutation.sequenceFin fun i => (OracleComp.lift (OracleSpec.query (spec := Fin n →ₒ R) i))
  have he : ∀ g : Fin n → R, evalWithAnswerFn (QueryImpl.ofFn g) oa = g := by
    intro g
    simp only [evalWithAnswerFn, oa, simulateQ_sequenceFin, simulateQ_query,
      OracleQuery.cont_query, OracleQuery.input_query, id_map, QueryImpl.ofFn_apply]
    exact congrArg Id.run (sequenceFin_pure g)
  have h := evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable oa
  simp only [he, bind_pure] at h
  rw [show (simulateQ randomOracle oa).run' ∅ =
      OverPermutation.sequenceFin (fun _ : Fin n => ($ᵗ R)) from ?_] at h
  · exact evalDistEq_iff_evalDist_eq.mpr h
  · simp only [oa, simulateQ_sequenceFin, simulateQ_query,
      OracleQuery.cont_query, OracleQuery.input_query, id_map, StateT.run'_eq]
    change Prod.fst <$> (OverPermutation.sequenceFin fun i : Fin n => (Fin n →ₒ R).randomOracle i).run ∅ = _
    erw [randomOracle_sequenceFin_fresh (R := R) (fun i : Fin n => i) Function.injective_id ∅ (fun _ => rfl)]
    simp only [Functor.map_map]
    exact id_map _

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

/-- Inserting a finite table leaves every other coordinate unchanged. -/
theorem cacheFin_of_not_mem {D R : Type} [DecidableEq D] : ∀ {n : ℕ}
    (addr : Fin n → D) (vals : Fin n → R) (c : (D →ₒ R).QueryCache) (x : D)
    (hx : ∀ i, x ≠ addr i), cacheFin addr vals c x = c x
  | 0, addr, vals, c, x, hx => rfl
  | n + 1, addr, vals, c, x, hx => by
    rw [cacheFin, cacheFin_of_not_mem _ _ _ x (fun i => hx i.succ)]
    exact QueryCache.cacheQuery_of_ne c (vals 0) (hx 0)

/-- Every sampled entry is retained in the final cache. -/
theorem cacheFin_at {D R : Type} [DecidableEq D] : ∀ {n : ℕ}
    (addr : Fin n → D) (ha : Function.Injective addr) (vals : Fin n → R)
    (c : (D →ₒ R).QueryCache) (i : Fin n), cacheFin addr vals c (addr i) = some (vals i)
  | 0, addr, ha, vals, c, i => i.elim0
  | n + 1, addr, ha, vals, c, i => by
    cases i using Fin.cases with
    | zero =>
      rw [cacheFin, cacheFin_of_not_mem _ _ _ _ (fun j h => Fin.succ_ne_zero j (ha h).symm)]
      exact QueryCache.cacheQuery_self _ _ _
    | succ i =>
      exact cacheFin_at (fun j : Fin n => addr j.succ) (ha.comp (Fin.succ_injective n)) _ _ i

end ThresholdLeanXmssSecurity

end FreshStreams

section SequentialExecution
set_option backward.isDefEq.respectTransparency false
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

section RoundComposition
variable {C : Committee} {E : Type} {I O L R Ia α : Type}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (Ro : Roles C m) (D : C.Coalition) (A : Adversary C E Ia L R)
variable (F : Functionality C I O L R)

/-- The round runner before projecting its pending programs to outputs. -/
def executeSteps : ℕ → A.State → (C.Party → Step C E (CallSpec I O) α) →
    m (A.State × (C.Party → Step C E (CallSpec I O) α))
  | 0, state, steps => pure (state, steps)
  | fuel + 1, state, steps =>
    if ∀ i, i ∉ D.1 → (steps i).isDone then pure (state, steps) else do
      let (state, steps, _) ← stepRound Ro D A F state steps
      executeSteps fuel state steps

/-- `executeRounds` is the output projection of the runner that retains pending programs. -/
theorem executeRounds_eq_executeSteps (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α) :
    executeRounds Ro D A F fuel state steps =
      (fun p => (p.1, fun i => (p.2 i).output)) <$> executeSteps Ro D A F fuel state steps := by
  induction fuel generalizing state steps with
  | zero => simp [executeRounds, executeSteps]
  | succ fuel ih =>
    simp only [executeRounds, executeSteps]
    split_ifs
    · simp
    · rw [map_bind]
      exact bind_congr fun p => ih p.1 p.2.1

end RoundComposition

section Continuations
variable {C : Committee} {E ι α β : Type} {G : OracleSpec ι}

/-- Continue a suspended program, without running past its next interaction. -/
def continueStep (k : α → PartyM C E G β) : Step C E G α → OracleComp (LocalSpec C) (Step C E G β)
  | .done none => pure (.done none)
  | .done (some a) => advance (k a).run
  | .wait outbox resume => pure (.wait outbox fun inbox =>
      (OptionT.mk (resume inbox) >>= k).run)
  | .call input resume => pure (.call input fun response =>
      (OptionT.mk (resume response) >>= k).run)

/-- Advancing a sequential program first advances its prefix and then attaches the continuation. -/
theorem advance_bind (p : PartyM C E G α) (k : α → PartyM C E G β) :
    advance (p >>= k).run = advance p.run >>= continueStep k := by
  simp only [OptionT.run_bind, Option.elimM]
  change advance (p.run >>= fun a => a.elim (pure none) (fun a => (k a).run)) = _
  generalize p.run = oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    change advance (a.elim (pure none) (fun a => (k a).run)) = pure (.done a) >>= continueStep k
    rw [pure_bind]
    cases a <;> rfl
  | query_bind q f ih =>
    rcases q with (q | mail) | input
    · simp only [bind_assoc]
      change (OracleComp.lift (OracleSpec.query q) >>= fun r =>
        advance (f r >>= fun a => a.elim (pure none) (fun a => (k a).run))) =
        (OracleComp.lift (OracleSpec.query q) >>= fun r => advance (f r)) >>= continueStep k
      simp only [bind_assoc]
      exact bind_congr ih
    · rw [bind_assoc]
      change pure (.wait mail (fun response => f response >>= fun a =>
        a.elim (pure none) (fun a => (k a).run))) = pure (.wait mail f) >>= continueStep k
      simp only [pure_bind, continueStep, OptionT.run_bind, OptionT.run_mk, Option.elimM]
    · rw [bind_assoc]
      change pure (.call input (fun response => f response >>= fun a =>
        a.elim (pure none) (fun a => (k a).run))) = pure (.call input f) >>= continueStep k
      simp only [pure_bind, continueStep, OptionT.run_bind, OptionT.run_mk, Option.elimM]

end Continuations

end ThresholdLeanXmssSecurity

end SequentialExecution

section GoodOutputCoupling
open scoped ENNReal
open OracleComp.ProgramLogic.Relational
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

section BadCoupling
variable {ι σ α : Type} {spec : OracleSpec ι}

/-- Once a monotone bad flag is set, a simulation cannot return to a good state. -/
theorem simulateQ_bad_absorbing (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hmono : ∀ t s, bad s → ∀ r ∈ support ((impl t).run s), bad r.2)
    (game : OracleComp spec α) (s : σ) (hs : bad s) :
    ∀ r ∈ support ((simulateQ impl game).run s), bad r.2 := by
  induction game using OracleComp.inductionOn generalizing s with
  | pure a => simpa using hs
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop]
    rintro r ⟨p, hp, hr⟩
    exact ih p.1 p.2 (hmono t s hs p hp) r hr

/-- A step may first set the flag and return different answers. Only its good outputs must agree. -/
theorem simulateQ_probOutput_good_eq (I J : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hstep : ∀ t s r, ¬ bad r.2 → Pr{let z ← (I t).run s}[z = r] = Pr{let z ← (J t).run s}[z = r])
    (hI : ∀ t s, bad s → ∀ r ∈ support ((I t).run s), bad r.2)
    (hJ : ∀ t s, bad s → ∀ r ∈ support ((J t).run s), bad r.2)
    (game : OracleComp spec α) (s : σ) (r : α × σ) (hr : ¬ bad r.2) :
    Pr{let z ← (simulateQ I game).run s}[z = r] = Pr{let z ← (simulateQ J game).run s}[z = r] := by
  induction game using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, OracleComp.prEvent_bind_eq_tsum]
    refine tsum_congr fun p => ?_
    by_cases hp : bad p.2
    · have hzI : Pr{let z ← (simulateQ I (k p.1)).run p.2}[z = r] = 0 :=
        prEvent_eq_zero_of_not_mem_support _
          fun hm => hr (simulateQ_bad_absorbing I bad hI (k p.1) p.2 hp r hm)
      have hzJ : Pr{let z ← (simulateQ J (k p.1)).run p.2}[z = r] = 0 :=
        prEvent_eq_zero_of_not_mem_support _
          fun hm => hr (simulateQ_bad_absorbing J bad hJ (k p.1) p.2 hp r hm)
      rw [hzI, hzJ, mul_zero, mul_zero]
    · rw [hstep t s p hp, ih]

/-- The two simulations assign the same total mass to the monotone bad event. -/
theorem simulateQ_probBad_eq (I J : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hstep : ∀ t s r, ¬ bad r.2 → Pr{let z ← (I t).run s}[z = r] = Pr{let z ← (J t).run s}[z = r])
    (hI : ∀ t s, bad s → ∀ r ∈ support ((I t).run s), bad r.2)
    (hJ : ∀ t s, bad s → ∀ r ∈ support ((J t).run s), bad r.2)
    (game : OracleComp spec α) (s : σ) :
    Pr{let z ← (simulateQ I game).run s}[(bad ∘ Prod.snd) z] =
      Pr{let z ← (simulateQ J game).run s}[(bad ∘ Prod.snd) z] := by
  have hg : Pr{let r ← (simulateQ I game).run s}[¬ bad r.2] =
      Pr{let r ← (simulateQ J game).run s}[¬ bad r.2] := by
    rw [OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite]
    refine tsum_congr fun r => ?_
    split_ifs with hr
    · rfl
    · exact simulateQ_probOutput_good_eq I J bad hstep hI hJ game s r hr
  have h₁ := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ I game).run s) (fun r => bad r.2)
  have h₂ := prEvent_add_prEvent_not_eq_prEvent_true ((simulateQ J game).run s) (fun r => bad r.2)
  rw [OracleComp.prEvent_true_eq_one] at h₁ h₂
  rw [hg] at h₁
  exact (ENNReal.add_left_inj (prEvent_ne_top _)).mp (h₁.trans h₂.symm)

/-- Identical until bad, allowing the triggering query itself to have different bad outputs. -/
theorem tvDist_simulateQ_le_probBad_of_good_outputs
    (I J : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hstep : ∀ t s r, ¬ bad r.2 → Pr{let z ← (I t).run s}[z = r] = Pr{let z ← (J t).run s}[z = r])
    (hI : ∀ t s, bad s → ∀ r ∈ support ((I t).run s), bad r.2)
    (hJ : ∀ t s, bad s → ∀ r ∈ support ((J t).run s), bad r.2)
    (game : OracleComp spec α) (s : σ) :
    letI : MeasurableSpace α := ⊤
    measureTVDist ((simulateQ I game).run' s) ((simulateQ J game).run' s) ≤
      Pr{let z ← (simulateQ I game).run s}[(bad ∘ Prod.snd) z].toReal := by
  let : MeasurableSpace α := ⊤
  have hgood : ∀ p : α × σ → Prop, Pr{let z ← (simulateQ I game).run s}[p z ∧ ¬ bad z.2] =
      Pr{let z ← (simulateQ J game).run s}[p z ∧ ¬ bad z.2] := by
    intro p
    rw [OracleComp.prEvent_eq_tsum_ite, OracleComp.prEvent_eq_tsum_ite]
    refine tsum_congr fun z => ?_
    by_cases hz : p z ∧ ¬ bad z.2
    · rw [if_pos hz, if_pos hz, simulateQ_probOutput_good_eq I J bad hstep hI hJ game s z hz.2]
    · rw [if_neg hz, if_neg hz]
  have h := measureETVDist_map_le_prEvent_of_agree ((simulateQ I game).run s) ((simulateQ J game).run s)
    Prod.fst (fun z => bad z.2) hgood (simulateQ_probBad_eq I J bad hstep hI hJ game s).ge
  rw [StateT.run'_eq, StateT.run'_eq, measureTVDist_eq_toReal_measureETVDist]
  exact ENNReal.toReal_mono (prEvent_ne_top _) h

end BadCoupling
end ThresholdLeanXmssSecurity
end GoodOutputCoupling

section KeyJointCoupling
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- Full hash outputs for hidden named stream keys. The low half is the AES key. -/
abbrev FullKeyCache (C : Committee) := ((KeyName C × HashOutput) →ₒ HashOutput).QueryCache

/-- A public hash cache and deferred private stream-key answers, with their first owners. -/
structure KeyJointState (C : Committee) where
  hash : HashCache C
  keys : FullKeyCache C
  used : HashOutput → Option (KeyName C)
  bad : Bool

variable {C : Committee}

def KeyJointState.privateHash (s : KeyJointState C) (k : HashOutput) : Option HashOutput :=
  (s.used k).bind fun name => s.keys (name, k)

def onJointHash {α : Type} (m : StateT (HashCache C) ProbComp α) :
    StateT (KeyJointState C) ProbComp α := StateT.mk fun s =>
  (fun r => (r.1, { s with hash := r.2 })) <$> m.run s.hash

/-- A public hash query either exposes a deferred real answer or uses the public cache. -/
def jointHash (prims : Primitives) (real : Bool) (q : Query C) :
    StateT (KeyJointState C) ProbComp HashOutput := StateT.mk fun s =>
  match q with
  | .streamKey k =>
    if real then match s.hash q, s.privateHash k with
      | none, some v => pure (v, { s with hash := s.hash.cacheQuery q v })
      | _, _ => (onJointHash (hashAnswer prims q)).run s
    else (onJointHash (hashAnswer prims q)).run s
  | _ => (onJointHash (hashAnswer prims q)).run s

/-- The named private answer. The real variant reuses an already existing hash of the key. -/
def jointHidden (real : Bool) (x : KeyName C × HashOutput) :
    StateT (KeyJointState C) ProbComp HashOutput := StateT.mk fun s =>
  match s.keys x with
  | some v => pure (v, s)
  | none => do
    let v ← if real then match s.hash (.streamKey x.2) <|> s.privateHash x.2 with
      | some v => pure v
      | none => $ᵗ HashOutput
      else $ᵗ HashOutput
    pure (v, { s with keys := s.keys.cacheQuery x v, used := if (s.used x.2).isSome then s.used else Function.update s.used x.2 (some x.1) })

def jointProgram (real : Bool) (x : Query C × HashOutput) :
    StateT (KeyJointState C) ProbComp Bool := StateT.mk fun s =>
  match x.1 with
  | .streamKey k =>
    if real && (s.privateHash k).isSome then pure (false, s)
    else (onJointHash (programAnswer x)).run s
  | _ => (onJointHash (programAnswer x)).run s

def jointLocal (prims : Primitives) (real : Bool) :
    QueryImpl (LocalSpec C) (StateT (KeyJointState C) ProbComp) :=
  fun q => match q with
  | .inl u => onJointHash ((unifFwdImpl (Query C →ₒ HashOutput)) u)
  | .inr (.inl q) => jointHash prims real q
  | .inr (.inr x) => do
      let h ← jointHash prims real (.streamKey x.2.1)
      pure (prims.aes.eval (truncateHash h) x.2.2)

/-- The three bad events: public use of a private key, an already cached first use, and reuse of
one hidden key under another name. -/
def keyJointRisk (D : C.Coalition) (q : (WorldSpec C).Domain) (s : KeyJointState C) : Bool :=
  let publicHash := fun q : Query C => match q with
    | .streamKey k => (s.used k).isSome
    | _ => false
  match q with
  | .inl (.inr x) => publicHash x.1
  | .inl (.inl (.inr (.inl q))) => publicHash q
  | .inl (.inl (.inr (.inr x))) => (s.used x.2.1).isSome
  | .inr (.inr (.inl q)) => publicHash q
  | .inr (.inr (.inr x)) =>
    if Hidden D x.1 then
      !(s.keys (x.1, x.2.1)).isSome &&
        ((s.hash (.streamKey x.2.1)).isSome || (s.used x.2.1).isSome)
    else (s.used x.2.1).isSome
  | _ => false

/-- The common monitored state representation of the real and independently keyed worlds. -/
def jointKeyWorldCore (prims : Primitives) (D : C.Coalition) (real : Bool) :
    QueryImpl (WorldSpec C) (StateT (KeyJointState C) ProbComp) := fun q =>
  match q with
  | .inl (.inl q) => jointLocal prims real q
  | .inl (.inr x) => jointProgram real x
  | .inr (.inr (.inr x)) =>
    if Hidden D x.1 then do
      let h ← jointHidden real (x.1, x.2.1)
      pure (prims.aes.eval (truncateHash h) x.2.2)
    else jointLocal prims real (.inr (.inr x))
  | .inr q => jointLocal prims real q

def jointKeyWorld (prims : Primitives) (D : C.Coalition) (real : Bool) :
    QueryImpl (WorldSpec C) (StateT (KeyJointState C) ProbComp) := fun q => StateT.mk fun s =>
  (fun r => (r.1, { r.2 with bad := s.bad || keyJointRisk D q s })) <$>
    (jointKeyWorldCore prims D real q).run s

@[simp] theorem privateHash_eq_none (s : KeyJointState C) (k : HashOutput)
    (h : s.used k = none) : s.privateHash k = none := by simp [KeyJointState.privateHash, h]

theorem jointHash_eq_of_unused (prims : Primitives) (q : Query C) (s : KeyJointState C)
    (h : ∀ k, q = .streamKey k → s.used k = none) :
    (jointHash prims true q).run s = (jointHash prims false q).run s := by
  cases q <;> simp only [jointHash, StateT.run_mk, Bool.false_eq_true, if_true, if_false]
  case streamKey k => simp [privateHash_eq_none s k (h k rfl)]

theorem jointHidden_eq_of_fresh (x : KeyName C × HashOutput) (s : KeyJointState C)
    (h : s.keys x = none → s.hash (.streamKey x.2) = none ∧ s.used x.2 = none) :
    (jointHidden true x).run s = (jointHidden false x).run s := by
  cases hk : s.keys x with
  | some v => simp [jointHidden, hk]
  | none => obtain ⟨hh, hu⟩ := h hk; simp [jointHidden, hk, hh, privateHash_eq_none s x.2 hu]

theorem jointProgram_eq_of_unused (x : Query C × HashOutput) (s : KeyJointState C)
    (h : ∀ k, x.1 = .streamKey k → s.used k = none) :
    (jointProgram true x).run s = (jointProgram false x).run s := by
  rcases x with ⟨q, v⟩
  cases q <;> simp only [jointProgram, StateT.run_mk]
  case streamKey k => simp [privateHash_eq_none s k (h k rfl)]

theorem jointKeyWorldCore_eq_of_no_risk (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C) (h : keyJointRisk D q s = false) :
    (jointKeyWorldCore prims D true q).run s = (jointKeyWorldCore prims D false q).run s := by
  rcases q with ((u | q | x) | p) | (u | q | x)
  · rfl
  · exact jointHash_eq_of_unused prims q s (by
      intro k hk; subst q; simpa [keyJointRisk] using h)
  · simp only [jointKeyWorldCore, jointLocal, StateT.run_bind]
    rw [jointHash_eq_of_unused prims (.streamKey x.2.1) s (by
      intro k hk; cases hk; simpa [keyJointRisk] using h)]
  · exact jointProgram_eq_of_unused p s (by
      intro k hk; rcases p with ⟨p, v⟩; dsimp at hk; subst p
      simpa [keyJointRisk] using h)
  · rfl
  · exact jointHash_eq_of_unused prims q s (by
      intro k hk; subst q; simpa [keyJointRisk] using h)
  · by_cases hh : Hidden D x.1
    · simp only [jointKeyWorldCore, if_pos hh, StateT.run_bind]
      rw [jointHidden_eq_of_fresh (x.1, x.2.1) s (by
        intro hk
        simpa [keyJointRisk, hh, hk] using h)]
    · simp only [jointKeyWorldCore, if_neg hh, jointLocal, StateT.run_bind]
      rw [jointHash_eq_of_unused prims (.streamKey x.2.1) s (by
        intro k hk; cases hk; simpa [keyJointRisk, hh] using h)]

/-- The flag is absorbing, and also records a risk at the current query. -/
theorem jointKeyWorld_bad (prims : Primitives) (D : C.Coalition) (real : Bool)
    (q : (WorldSpec C).Domain) (s : KeyJointState C)
    (r : (WorldSpec C).Range q × KeyJointState C)
    (hr : r ∈ support ((jointKeyWorld prims D real q).run s)) :
    r.2.bad = (s.bad || keyJointRisk D q s) := by
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, _, rfl⟩ := hr
  rfl

/-- The monitored worlds assign identical mass to every good answer and successor state. -/
theorem jointKeyWorld_good (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C)
    (r : (WorldSpec C).Range q × KeyJointState C) (hr : r.2.bad ≠ true) :
    Pr{let z ← (jointKeyWorld prims D true q).run s}[z = r] =
      Pr{let z ← (jointKeyWorld prims D false q).run s}[z = r] := by
  by_cases h : keyJointRisk D q s = false
  · simp only [jointKeyWorld, StateT.run_mk, jointKeyWorldCore_eq_of_no_risk prims D q s h]
  · have hz (real : Bool) : Pr{let z ← (jointKeyWorld prims D real q).run s}[z = r] = 0 := by
      refine prEvent_eq_zero_of_not_mem_support _ fun hm => ?_
      have hb := jointKeyWorld_bad prims D real q s r hm
      have ht : keyJointRisk D q s = true := Bool.eq_true_of_not_eq_false h
      exact hr (hb.trans (by simp [ht]))
    rw [hz true, hz false]

/-- The full adaptive computation differs by at most the monitored stream-key bad event.
Application to the original worlds additionally requires cache projection lemmas. -/
theorem jointKeyWorld_coupling (prims : Primitives) (D : C.Coalition) {α : Type}
    (game : OracleComp (WorldSpec C) α) (s : KeyJointState C) :
    letI : MeasurableSpace α := ⊤
    measureTVDist ((simulateQ (jointKeyWorld prims D true) game).run' s)
      ((simulateQ (jointKeyWorld prims D false) game).run' s) ≤
      Pr{let r ← (simulateQ (jointKeyWorld prims D true) game).run s}[r.2.bad = true].toReal := by
  refine tvDist_simulateQ_le_probBad_of_good_outputs _ _ (fun s => s.bad = true) ?_ ?_ ?_ game s
  · exact fun q s r hr => jointKeyWorld_good prims D q s r hr
  · intro q s hs r hr
    rw [jointKeyWorld_bad prims D true q s r hr, hs]
    rfl
  · intro q s hs r hr
    rw [jointKeyWorld_bad prims D false q s r hr, hs]
    rfl

end ThresholdLeanXmssSecurity
end KeyJointCoupling

section KeyIdealProjection
namespace ThresholdLeanXmssSecurity
open OracleComp.DeferredSampling
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {C : Committee}

def truncateKeyCache (c : FullKeyCache C) : KeyCache C := QueryCache.ofFn fun x => (c x).map truncateHash

theorem truncateKeyCache_cacheQuery (c : FullKeyCache C) (x : KeyName C × HashOutput) (v : HashOutput) :
    truncateKeyCache (c.cacheQuery x v) = (truncateKeyCache c).cacheQuery x (truncateHash v) := by
  refine QueryCache.ext fun y => ?_
  by_cases h : y = x
  · subst y; simp [truncateKeyCache]
  · simp [truncateKeyCache, QueryCache.cacheQuery_of_ne, h]

def keyJointIdealProjection (s : KeyJointState C) : HashCache C × KeyCache C :=
  (s.hash, truncateKeyCache s.keys)

theorem jointHash_false (prims : Primitives) (q : Query C) :
    jointHash prims false q = onJointHash (hashAnswer prims q) := by
  apply StateT.ext; intro s; cases q <;> rfl

theorem jointProgram_false (x : Query C × HashOutput) :
    jointProgram false x = onJointHash (programAnswer x) := by
  apply StateT.ext; intro s; rcases x with ⟨q, v⟩; cases q <;> rfl

theorem jointLocal_false (prims : Primitives) (q : (LocalSpec C).Domain) :
    jointLocal prims false q = onJointHash (localAnswer prims q) := by
  rcases q with u | q | x
  · rfl
  · exact jointHash_false prims q
  · apply StateT.ext; intro s
    simp only [jointLocal, jointHash_false, onJointHash, StateT.run_mk, bind_pure_comp, localAnswer, QueryImpl.add_apply_inr,
      prgAnswer, StateT.run_map, Functor.map_map]

theorem onJointHash_idealProjection {α : Type} (m : StateT (HashCache C) ProbComp α)
    (s : KeyJointState C) :
    Prod.map id keyJointIdealProjection <$> (onJointHash m).run s =
      (fun r => (r.1, (r.2, truncateKeyCache s.keys))) <$> m.run s.hash := by
  simp [onJointHash, Functor.map_map, keyJointIdealProjection]

theorem jointHidden_false_projection (x : KeyName C × HashOutput) (s : KeyJointState C) :
    ((fun r => (truncateHash r.1, keyJointIdealProjection r.2)) <$> (jointHidden false x).run s) =ᵈ
      ((fun r => (r.1, (s.hash, r.2))) <$>
        ((((KeyName C × HashOutput) →ₒ Digest).randomOracle x).run (truncateKeyCache s.keys))) := by
  cases hc : s.keys x with
  | some v =>
    rw [QueryImpl.withCaching_run_some _ (show truncateKeyCache s.keys x = some (truncateHash v) by
      simp [truncateKeyCache, hc])]
    simp [jointHidden, hc, keyJointIdealProjection]
  | none =>
    rw [QueryImpl.withCaching_run_none _ (show truncateKeyCache s.keys x = none by
      simp [truncateKeyCache, hc])]
    simp only [jointHidden, StateT.run_mk, hc, Bool.false_eq_true, if_false,
      bind_pure_comp, Functor.map_map]
    simp only [keyJointIdealProjection, truncateKeyCache_cacheQuery]
    have h := evalDist_truncateHash_uniform.map
      (fun v => (v, (s.hash, (truncateKeyCache s.keys).cacheQuery x v)))
    simpa only [Functor.map_map, Function.comp_def, uniformSampleImpl] using h

theorem jointKeyWorld_false_query_projection (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C) :
    (Prod.map id keyJointIdealProjection <$> (jointKeyWorld prims D false q).run s) =ᵈ
      (lazyKeyWorld prims D q).run (keyJointIdealProjection s) := by
  have hf : Prod.map id keyJointIdealProjection <$> (jointKeyWorld prims D false q).run s =
      Prod.map id keyJointIdealProjection <$> (jointKeyWorldCore prims D false q).run s := by
    simp [jointKeyWorld, Functor.map_map, keyJointIdealProjection, Prod.map]
    rfl
  rw [hf]
  rcases q with ((u | q | x) | p) | (u | q | x)
  all_goals simp only [jointKeyWorldCore]
  all_goals try simp only [jointLocal_false, jointProgram_false, onJointHash_idealProjection,
    lazyKeyWorld, StateT.run_mk, keyJointIdealProjection]
  all_goals try rfl
  case inr.inr.inr =>
    by_cases hh : Hidden D x.1
    · simp only [if_pos hh, bind_pure_comp, StateT.run_map,
        Functor.map_map]
      have h := (jointHidden_false_projection (x.1, x.2.1) s).map
        (fun r : Digest × HashCache C × KeyCache C => (prims.aes.eval r.1 x.2.2, r.2))
      simpa only [Functor.map_map, Function.comp_def, Prod.map, id_eq, StateT.run_mk,
        keyJointIdealProjection] using h
    · simp only [if_neg hh, onJointHash_idealProjection, StateT.run_mk]
      rfl

/-- The ideal monitored handler projects to `lazyKeyWorld`. The run of a game under
`jointKeyWorld prims D false` from `s` has the distribution of its run under `lazyKeyWorld` from the
projection `keyJointIdealProjection s` of the state. -/
theorem jointKeyWorld_false_projection (prims : Primitives) (D : C.Coalition) {α : Type}
    (game : OracleComp (WorldSpec C) α) (s : KeyJointState C) :
    (simulateQ (jointKeyWorld prims D false) game).run' s =ᵈ
      (simulateQ (lazyKeyWorld prims D) game).run' (keyJointIdealProjection s) := by
  have h := evalDist_simulateQ_state_projection (jointKeyWorld prims D false) (lazyKeyWorld prims D)
    keyJointIdealProjection (jointKeyWorld_false_query_projection prims D) game s
  have hp := h.map Prod.fst
  simpa only [StateT.run'_eq, Functor.map_map, Function.comp_def, Prod.map, id_eq] using hp

end ThresholdLeanXmssSecurity
end KeyIdealProjection

section KeyRealProjection
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee}

/-- The real hash cache contains both the public and deferred private answers. -/
def KeyJointState.realCache (s : KeyJointState C) : HashCache C := QueryCache.ofFn fun q => match q with
  | .streamKey k => s.hash q <|> s.privateHash k
  | _ => s.hash q

/-- Names for one hidden key agree, and a public copy agrees with its private copy. -/
def KeyJointState.Coherent (s : KeyJointState C) : Prop :=
  (∀ x v, s.keys x = some v → s.privateHash x.2 = some v) ∧
  (∀ k v, s.privateHash k = some v → s.hash (.streamKey k) = none ∨ s.hash (.streamKey k) = some v) ∧
  (∀ k, (s.used k).isSome = (s.privateHash k).isSome)

/-- Register the first name of a key and its full private hash answer. -/
def keyJointInsert (s : KeyJointState C) (x : KeyName C × HashOutput) (v : HashOutput) : KeyJointState C :=
  { s with keys := s.keys.cacheQuery x v,
           used := if (s.used x.2).isSome then s.used else Function.update s.used x.2 (some x.1) }

theorem realCache_private (s : KeyJointState C) (hs : s.Coherent) (k : HashOutput) (v : HashOutput)
    (h : s.privateHash k = some v) : s.realCache (.streamKey k) = some v := by
  rcases hs.2.1 k v h with hh | hh <;> simp [KeyJointState.realCache, h, hh]

theorem realCache_keys (s : KeyJointState C) (hs : s.Coherent) (x : KeyName C × HashOutput) (v : HashOutput)
    (h : s.keys x = some v) : s.realCache (.streamKey x.2) = some v :=
  realCache_private s hs x.2 v (hs.1 x v h)

theorem privateHash_keyJointInsert (s : KeyJointState C) (hs : s.Coherent)
    (x : KeyName C × HashOutput) (v : HashOutput)
    (hv : s.realCache (.streamKey x.2) = none ∨ s.realCache (.streamKey x.2) = some v) :
    (keyJointInsert s x v).privateHash = Function.update s.privateHash x.2 (some v) := by
  have hp : s.privateHash x.2 = none ∨ s.privateHash x.2 = some v := by
    cases hc : s.privateHash x.2 with
    | none => exact Or.inl rfl
    | some w =>
      have hfull := realCache_private s hs x.2 w hc
      rcases hv with hv | hv
      · rw [hfull] at hv; contradiction
      · rw [hfull] at hv; cases hv; exact Or.inr rfl
  funext k
  by_cases hk : k = x.2
  · subst k
    cases hu : s.used x.2 with
    | none => simp [keyJointInsert, KeyJointState.privateHash, hu]
    | some name =>
      have hsome : (s.privateHash x.2).isSome = true := by simpa [hu] using (hs.2.2 x.2).symm
      have hpv : s.privateHash x.2 = some v := by
        rcases hp with hp | hp
        · simp [hp] at hsome
        · exact hp
      have hkey : s.keys (name, x.2) = some v := by
        simpa [KeyJointState.privateHash, hu] using hpv
      by_cases hn : name = x.1
      · subst name; simp [keyJointInsert, KeyJointState.privateHash, hu]
      · have hnx : (name, x.2) ≠ x := fun he => hn (congrArg Prod.fst he)
        simp [keyJointInsert, KeyJointState.privateHash, hu, QueryCache.cacheQuery_of_ne, hnx, hkey]
  · have hn : ∀ name, (name, k) ≠ x := by intro name h; exact hk (congrArg Prod.snd h)
    simp only [keyJointInsert, KeyJointState.privateHash]
    split_ifs
    · cases hu : s.used k <;> simp [Function.update_of_ne hk, QueryCache.cacheQuery_of_ne, hn, KeyJointState.privateHash, hu]
    · simp only [Function.update_of_ne hk]
      cases hu : s.used k <;> simp [QueryCache.cacheQuery_of_ne, hn, KeyJointState.privateHash, hu]

theorem realCache_keyJointInsert (s : KeyJointState C) (hs : s.Coherent)
    (x : KeyName C × HashOutput) (v : HashOutput)
    (hv : s.realCache (.streamKey x.2) = none ∨ s.realCache (.streamKey x.2) = some v) :
    (keyJointInsert s x v).realCache = s.realCache.cacheQuery (.streamKey x.2) v := by
  have hp := privateHash_keyJointInsert s hs x v hv
  have hh : s.hash (.streamKey x.2) = none ∨ s.hash (.streamKey x.2) = some v := by
    cases hc : s.hash (.streamKey x.2) with
    | none => exact Or.inl rfl
    | some w =>
      have hf : s.realCache (.streamKey x.2) = some w := by simp [KeyJointState.realCache, hc]
      rcases hv with hv | hv
      · rw [hf] at hv; contradiction
      · rw [hf] at hv; cases hv; exact Or.inr rfl
  refine QueryCache.ext fun q => ?_
  cases q <;> simp only [KeyJointState.realCache, keyJointInsert, QueryCache.cacheQuery]
  case streamKey k =>
    change (s.hash (.streamKey k) <|> (keyJointInsert s x v).privateHash k) = _
    rw [hp]
    by_cases hk : k = x.2
    · subst k
      rcases hh with hh | hh <;> simp [hh]
    · simp [hk]
  all_goals simp

theorem coherent_keyJointInsert (s : KeyJointState C) (hs : s.Coherent)
    (x : KeyName C × HashOutput) (v : HashOutput)
    (hv : s.realCache (.streamKey x.2) = none ∨ s.realCache (.streamKey x.2) = some v) :
    (keyJointInsert s x v).Coherent := by
  have hp := privateHash_keyJointInsert s hs x v hv
  refine ⟨?_, ?_, ?_⟩
  · intro y w hw
    change (s.keys.cacheQuery x v) y = some w at hw
    rw [hp]
    by_cases hy : y = x
    · subst y; simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hw
      subst w; simp
    · rw [QueryCache.cacheQuery_of_ne _ _ hy] at hw
      by_cases hk : y.2 = x.2
      · have hfull := realCache_keys s hs y w hw
        rw [hk] at hfull
        rcases hv with hv | hv
        · rw [hfull] at hv; contradiction
        · rw [hfull] at hv; cases hv; simp [hk]
      · simpa [Function.update_of_ne hk] using hs.1 y w hw
  · intro k w hw
    rw [hp] at hw
    by_cases hk : k = x.2
    · subst k; simp only [Function.update_self, Option.some.injEq] at hw
      subst w
      change s.hash (.streamKey x.2) = none ∨ s.hash (.streamKey x.2) = some v
      cases hh : s.hash (.streamKey x.2) with
      | none => exact Or.inl rfl
      | some a =>
        have hf : s.realCache (.streamKey x.2) = some a := by simp [KeyJointState.realCache, hh]
        rcases hv with hv | hv
        · rw [hf] at hv; contradiction
        · rw [hf] at hv; cases hv; exact Or.inr rfl
    · rw [Function.update_of_ne hk] at hw
      exact hs.2.1 k w hw
  · intro k
    rw [hp]
    change ((if (s.used x.2).isSome then s.used else Function.update s.used x.2 (some x.1)) k).isSome = _
    by_cases hk : k = x.2
    · subst k
      cases hu : s.used x.2 <;> simp [hu]
    · split_ifs
      · simpa [Function.update_of_ne hk] using hs.2.2 k
      · simpa [Function.update_of_ne hk] using hs.2.2 k

theorem coherent_hashInsert (s : KeyJointState C) (hs : s.Coherent) (q : Query C) (v : HashOutput)
    (hv : s.realCache q = none ∨ s.realCache q = some v) :
    ({ s with hash := s.hash.cacheQuery q v } : KeyJointState C).Coherent := by
  refine ⟨hs.1, ?_, hs.2.2⟩
  intro k w hw
  change s.privateHash k = some w at hw
  change (s.hash.cacheQuery q v) (.streamKey k) = none ∨ (s.hash.cacheQuery q v) (.streamKey k) = some w
  by_cases hk : .streamKey k = q
  · subst q
    have hf := realCache_private s hs k w hw
    rcases hv with hv | hv
    · rw [hf] at hv; contradiction
    · rw [hf] at hv; cases hv; simp
  · rw [QueryCache.cacheQuery_of_ne _ _ hk]
    exact hs.2.1 k w hw

theorem realCache_hashInsert (s : KeyJointState C) (q : Query C) (v : HashOutput) :
    ({ s with hash := s.hash.cacheQuery q v } : KeyJointState C).realCache =
      s.realCache.cacheQuery q v := by
  refine QueryCache.ext fun t => ?_
  by_cases ht : t = q
  · subst t
    cases q <;> simp [KeyJointState.realCache, QueryCache.cacheQuery_self]
  · cases t <;> simp [KeyJointState.realCache, QueryCache.cacheQuery_of_ne, ht, KeyJointState.privateHash]

theorem jointHidden_true_projection (x : KeyName C × HashOutput) (s : KeyJointState C) (hs : s.Coherent) :
    Prod.map id KeyJointState.realCache <$> (jointHidden true x).run s =
      (((Query C →ₒ HashOutput).randomOracle (.streamKey x.2)).run s.realCache) := by
  cases hk : s.keys x with
  | some v =>
    rw [QueryImpl.withCaching_run_some _ (realCache_keys s hs x v hk)]
    simp [jointHidden, hk, Prod.map]
  | none =>
    simp only [jointHidden, StateT.run_mk, hk, if_true, pure_bind]
    change Prod.map id KeyJointState.realCache <$>
      (match s.realCache (.streamKey x.2) with
        | some v => pure (v, keyJointInsert s x v)
        | none => ($ᵗ HashOutput : ProbComp HashOutput) >>= fun v => pure (v, keyJointInsert s x v)) = _
    cases hc : s.realCache (.streamKey x.2) with
    | some v =>
      rw [QueryImpl.withCaching_run_some _ hc]
      simp only [map_pure, Prod.map, id_eq]
      rw [realCache_keyJointInsert s hs x v (Or.inr hc)]
      congr 2
      refine QueryCache.ext fun q => ?_
      by_cases hq : q = .streamKey x.2
      · subst q; simp [hc]
      · simp [QueryCache.cacheQuery_of_ne, hq]
    | none =>
      rw [QueryImpl.withCaching_run_none _ hc]
      simp only [map_bind, map_pure, Prod.map, id_eq]
      rw [map_eq_bind_pure_comp]
      apply bind_congr
      intro v
      rw [realCache_keyJointInsert s hs x v (Or.inl hc)]
      rfl

theorem jointHidden_true_coherent (x : KeyName C × HashOutput) (s : KeyJointState C) (hs : s.Coherent) :
    ∀ r ∈ support ((jointHidden true x).run s), r.2.Coherent := by
  cases hk : s.keys x with
  | some v => simpa [jointHidden, hk] using hs
  | none =>
    simp only [jointHidden, StateT.run_mk, hk, if_true, pure_bind]
    change ∀ r ∈ support (match s.realCache (.streamKey x.2) with
        | some v => pure (v, keyJointInsert s x v)
        | none => ($ᵗ HashOutput : ProbComp HashOutput) >>= fun v => pure (v, keyJointInsert s x v)), r.2.Coherent
    cases hc : s.realCache (.streamKey x.2) with
    | some v => simpa using coherent_keyJointInsert s hs x v (Or.inr hc)
    | none =>
      intro r hr
      simp only [support_bind, Set.mem_iUnion, exists_prop, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨v, _, rfl⟩ := hr
      exact coherent_keyJointInsert s hs x v (Or.inl hc)

theorem onJointHash_randomOracle_projection (q : Query C) (s : KeyJointState C)
    (heq : s.realCache q = s.hash q) :
    Prod.map id KeyJointState.realCache <$>
        (onJointHash ((Query C →ₒ HashOutput).randomOracle q)).run s =
      (((Query C →ₒ HashOutput).randomOracle q).run s.realCache) := by
  cases hc : s.hash q with
  | some v =>
    simp only [onJointHash, StateT.run_mk]
    rw [QueryImpl.withCaching_run_some _ hc, QueryImpl.withCaching_run_some _ (heq.trans hc)]
    simp
  | none =>
    simp only [onJointHash, StateT.run_mk]
    rw [QueryImpl.withCaching_run_none _ hc, QueryImpl.withCaching_run_none _ (heq.trans hc)]
    simp only [Functor.map_map]
    congr 1
    funext v
    simp only [Prod.map, id_eq]
    rw [realCache_hashInsert]

theorem onJointHash_randomOracle_coherent (q : Query C) (s : KeyJointState C) (hs : s.Coherent)
    (heq : s.realCache q = s.hash q) :
    ∀ r ∈ support ((onJointHash ((Query C →ₒ HashOutput).randomOracle q)).run s), r.2.Coherent := by
  cases hc : s.hash q with
  | some v =>
    simp only [onJointHash, StateT.run_mk]
    rw [QueryImpl.withCaching_run_some _ hc]
    simpa using hs
  | none =>
    simp only [onJointHash, StateT.run_mk]
    rw [QueryImpl.withCaching_run_none _ hc]
    intro r hr
    simp only [Functor.map_map, support_map, Set.mem_image] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact coherent_hashInsert s hs q v (Or.inl (heq.trans hc))

theorem jointHash_true_projection (prims : Primitives) (q : Query C) (s : KeyJointState C) :
    Prod.map id KeyJointState.realCache <$> (jointHash prims true q).run s =
      (hashAnswer prims q).run s.realCache := by
  cases q
  case hash input =>
    by_cases hm : MpcInput input
    · simp [jointHash, hashAnswer, hm, onJointHash]
    · simpa [jointHash, hashAnswer, hm] using onJointHash_randomOracle_projection (.hash input) s rfl
  case streamKey k =>
    cases hh : s.hash (.streamKey k) with
    | some v =>
      simp only [jointHash, StateT.run_mk, if_true, hh, hashAnswer, onJointHash]
      rw [QueryImpl.withCaching_run_some _ hh,
        QueryImpl.withCaching_run_some _ (show s.realCache (.streamKey k) = some v by simp [KeyJointState.realCache, hh])]
      simp
    | none =>
      cases hp : s.privateHash k with
      | none =>
        simp only [jointHash, StateT.run_mk, if_true, hh, hp]
        exact onJointHash_randomOracle_projection (.streamKey k) s (by simp [KeyJointState.realCache, hh, hp])
      | some v =>
        simp only [jointHash, StateT.run_mk, if_true, hh, hp, map_pure, Prod.map, id_eq, hashAnswer]
        rw [QueryImpl.withCaching_run_some _ (show s.realCache (.streamKey k) = some v by simp [KeyJointState.realCache, hh, hp])]
        rw [realCache_hashInsert]
        congr 2
        refine QueryCache.ext fun q => ?_
        by_cases hq : q = .streamKey k
        · subst q; simp [KeyJointState.realCache, hh, hp]
        · simp [QueryCache.cacheQuery_of_ne, hq]
  all_goals exact onJointHash_randomOracle_projection _ s rfl

theorem jointHash_true_coherent (prims : Primitives) (q : Query C) (s : KeyJointState C) (hs : s.Coherent) :
    ∀ r ∈ support ((jointHash prims true q).run s), r.2.Coherent := by
  cases q
  case hash input =>
    by_cases hm : MpcInput input
    · simpa [jointHash, hashAnswer, hm, onJointHash] using hs
    · simpa [jointHash, hashAnswer, hm] using onJointHash_randomOracle_coherent (.hash input) s hs rfl
  case streamKey k =>
    cases hh : s.hash (.streamKey k) with
    | some v =>
      simp only [jointHash, StateT.run_mk, if_true, hh, hashAnswer, onJointHash]
      rw [QueryImpl.withCaching_run_some _ hh]
      simpa using hs
    | none =>
      cases hp : s.privateHash k with
      | none =>
        simp only [jointHash, StateT.run_mk, if_true, hh, hp]
        exact onJointHash_randomOracle_coherent (.streamKey k) s hs (by simp [KeyJointState.realCache, hh, hp])
      | some v =>
        simp only [jointHash, StateT.run_mk, if_true, hh, hp, support_pure, Set.mem_singleton_iff]
        intro r hr; subst r
        exact coherent_hashInsert s hs (.streamKey k) v (Or.inr (realCache_private s hs k v hp))
  all_goals exact onJointHash_randomOracle_coherent _ s hs rfl

theorem onJointHash_program_projection (x : Query C × HashOutput) (s : KeyJointState C)
    (heq : s.realCache x.1 = s.hash x.1) :
    Prod.map id KeyJointState.realCache <$> (onJointHash (programAnswer x)).run s =
      (programAnswer x).run s.realCache := by
  simp only [onJointHash, programAnswer, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind,
    heq]
  split_ifs
  · rfl
  · simp [Prod.map, realCache_hashInsert]

theorem onJointHash_program_coherent (x : Query C × HashOutput) (s : KeyJointState C) (hs : s.Coherent)
    (heq : s.realCache x.1 = s.hash x.1) :
    ∀ r ∈ support ((onJointHash (programAnswer x)).run s), r.2.Coherent := by
  simp only [onJointHash, programAnswer, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with h
  · simpa using hs
  · have hc : s.hash x.1 = none := by simpa using (not_or.mp h).2
    simpa using coherent_hashInsert s hs x.1 x.2 (Or.inl (heq.trans hc))

theorem jointProgram_true_projection (x : Query C × HashOutput) (s : KeyJointState C) :
    Prod.map id KeyJointState.realCache <$> (jointProgram true x).run s =
      (programAnswer x).run s.realCache := by
  rcases x with ⟨q, v⟩
  cases q
  case streamKey k =>
    cases hp : s.privateHash k with
    | none =>
      simp only [jointProgram, StateT.run_mk, hp, Option.isSome_none, Bool.and_false, Bool.false_eq_true, if_false]
      exact onJointHash_program_projection (.streamKey k, v) s (by simp [KeyJointState.realCache, hp])
    | some w =>
      have hc : (s.realCache (.streamKey k)).isSome = true := by simp [KeyJointState.realCache, hp]
      simp [jointProgram, hp, programAnswer, hc]
  all_goals exact onJointHash_program_projection _ s rfl

theorem jointProgram_true_coherent (x : Query C × HashOutput) (s : KeyJointState C) (hs : s.Coherent) :
    ∀ r ∈ support ((jointProgram true x).run s), r.2.Coherent := by
  rcases x with ⟨q, v⟩
  cases q
  case streamKey k =>
    cases hp : s.privateHash k with
    | none =>
      simp only [jointProgram, StateT.run_mk, hp, Option.isSome_none, Bool.and_false, Bool.false_eq_true, if_false]
      exact onJointHash_program_coherent (.streamKey k, v) s hs (by simp [KeyJointState.realCache, hp])
    | some w => simpa [jointProgram, hp] using hs
  all_goals exact onJointHash_program_coherent _ s hs rfl

theorem jointLocal_true_projection (prims : Primitives) (q : (LocalSpec C).Domain) (s : KeyJointState C) :
    Prod.map id KeyJointState.realCache <$> (jointLocal prims true q).run s =
      (localAnswer prims q).run s.realCache := by
  rcases q with u | q | x
  · simp [jointLocal, localAnswer, onJointHash, unifFwdImpl,
      Functor.map_map, Prod.map]
  · exact jointHash_true_projection prims q s
  · have h := congrArg (fun p => (fun r : HashOutput × HashCache C => (prims.aes.eval (truncateHash r.1) x.2.2, r.2)) <$> p)
      (jointHash_true_projection prims (.streamKey x.2.1) s)
    simpa [jointLocal, localAnswer, prgAnswer, bind_pure_comp, StateT.run_map,
      Functor.map_map, Function.comp_def, Prod.map] using h

theorem jointLocal_true_coherent (prims : Primitives) (q : (LocalSpec C).Domain)
    (s : KeyJointState C) (hs : s.Coherent) :
    ∀ r ∈ support ((jointLocal prims true q).run s), r.2.Coherent := by
  rcases q with u | q | x
  · simp [jointLocal, onJointHash, unifFwdImpl, Functor.map_map, hs]
  · exact jointHash_true_coherent prims q s hs
  · intro r hr
    simp only [jointLocal, bind_pure_comp, StateT.run_map, support_map, Set.mem_image] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    exact jointHash_true_coherent prims (.streamKey x.2.1) s hs p hp

theorem jointKeyWorldCore_true_projection (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C) (hs : s.Coherent) :
    Prod.map id KeyJointState.realCache <$> (jointKeyWorldCore prims D true q).run s =
      (worldAnswer prims q).run s.realCache := by
  rcases q with ((u | q | x) | p) | (u | q | x)
  · exact jointLocal_true_projection prims (.inl u) s
  · exact jointLocal_true_projection prims (.inr (.inl q)) s
  · exact jointLocal_true_projection prims (.inr (.inr x)) s
  · exact jointProgram_true_projection p s
  · exact jointLocal_true_projection prims (.inl u) s
  · exact jointLocal_true_projection prims (.inr (.inl q)) s
  · by_cases hh : Hidden D x.1
    · simp only [jointKeyWorldCore, if_pos hh, bind_pure_comp, StateT.run_map, Functor.map_map]
      have h := congrArg (fun p => (fun r : HashOutput × HashCache C => (prims.aes.eval (truncateHash r.1) x.2.2, r.2)) <$> p)
        (jointHidden_true_projection (x.1, x.2.1) s hs)
      simpa [worldAnswer, localAnswer, prgAnswer, hashAnswer, bind_pure_comp, StateT.run_map,
        Functor.map_map, Function.comp_def, Prod.map] using h
    · simp only [jointKeyWorldCore, if_neg hh]
      exact jointLocal_true_projection prims (.inr (.inr x)) s

theorem jointKeyWorldCore_true_coherent (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C) (hs : s.Coherent) :
    ∀ r ∈ support ((jointKeyWorldCore prims D true q).run s), r.2.Coherent := by
  rcases q with ((u | q | x) | p) | (u | q | x)
  · exact jointLocal_true_coherent prims (.inl u) s hs
  · exact jointLocal_true_coherent prims (.inr (.inl q)) s hs
  · exact jointLocal_true_coherent prims (.inr (.inr x)) s hs
  · exact jointProgram_true_coherent p s hs
  · exact jointLocal_true_coherent prims (.inl u) s hs
  · exact jointLocal_true_coherent prims (.inr (.inl q)) s hs
  · by_cases hh : Hidden D x.1
    · intro r hr
      simp only [jointKeyWorldCore, if_pos hh, bind_pure_comp, StateT.run_map, support_map, Set.mem_image] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      exact jointHidden_true_coherent (x.1, x.2.1) s hs p hp
    · simp only [jointKeyWorldCore, if_neg hh]
      exact jointLocal_true_coherent prims (.inr (.inr x)) s hs

theorem jointKeyWorld_true_query_projection (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C) (hs : s.Coherent) :
    Prod.map id KeyJointState.realCache <$> (jointKeyWorld prims D true q).run s =
      (worldAnswer prims q).run s.realCache := by
  rw [← jointKeyWorldCore_true_projection prims D q s hs]
  simp only [jointKeyWorld, StateT.run_mk, Functor.map_map]
  rfl

theorem jointKeyWorld_true_coherent (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C) (hs : s.Coherent) :
    ∀ r ∈ support ((jointKeyWorld prims D true q).run s), r.2.Coherent := by
  intro r hr
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  exact jointKeyWorldCore_true_coherent prims D q s hs p hp

/-- Merging the public and private caches gives exactly the real world, including after bad. -/
theorem jointKeyWorld_true_projection (prims : Primitives) (D : C.Coalition) {α : Type}
    (game : OracleComp (WorldSpec C) α) (s : KeyJointState C) (hs : s.Coherent) :
    (simulateQ (jointKeyWorld prims D true) game).run' s =
      (simulateQ (worldAnswer prims) game).run' s.realCache :=
  run'_simulateQ_eq_of_query_map_eq_inv' _ _ KeyJointState.Coherent KeyJointState.realCache
    (jointKeyWorld_true_coherent prims D) (jointKeyWorld_true_query_projection prims D) game s hs

end ThresholdLeanXmssSecurity
end KeyRealProjection

section KeyWorldBound
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee}

/-- No hash queries, no used private keys, and no bad event at the start. -/
def keyJointInitial : KeyJointState C := ⟨∅, ∅, fun _ => none, false⟩

theorem keyJointInitial_coherent : (keyJointInitial (C := C)).Coherent := by
  simp [KeyJointState.Coherent, keyJointInitial, KeyJointState.privateHash]

theorem jointKeyWorld_true_accepts (prims : Primitives) (D : C.Coalition)
    (game : OracleComp (WorldSpec C) Bool) :
    (Pr{let z ← (simulateQ (jointKeyWorld prims D true) game).run' keyJointInitial}[z = true]).toReal =
      accepts prims game := by
  rw [jointKeyWorld_true_projection prims D game keyJointInitial keyJointInitial_coherent]
  have hi : (keyJointInitial (C := C)).realCache = ∅ := by
    refine QueryCache.ext fun q => ?_; cases q <;> rfl
  rw [hi]
  rw [← fst_map_runWorld prims game]
  simp [accepts]

theorem jointKeyWorld_false_probability (prims : Primitives) (D : C.Coalition)
    (game : OracleComp (WorldSpec C) Bool) :
    Pr{let z ← (simulateQ (jointKeyWorld prims D false) game).run' keyJointInitial}[z = true] =
      Pr{let z ← ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
        (simulateQ (keyWorld prims D keys) game).run' ∅}[z = true] := by
  have h := jointKeyWorld_false_projection prims D game (keyJointInitial (C := C))
  have he : keyJointIdealProjection (keyJointInitial (C := C)) = (∅, ∅) := rfl
  rw [he] at h
  exact (h.prEvent_eq (· = true)).trans (keyTableLazy prims D game).symm

/-- The monitored stream-key bad event in the original real world. -/
def probBad_streamKey (prims : Primitives) (D : C.Coalition)
    (game : OracleComp (WorldSpec C) Bool) : ℝ :=
  (Pr{let r ← (simulateQ (jointKeyWorld prims D true) game).run keyJointInitial}[r.2.bad = true]).toReal

/-- The same bad-event probability can be bounded in the independent-key world. -/
theorem probBad_streamKey_eq_ideal (prims : Primitives) (D : C.Coalition)
    (game : OracleComp (WorldSpec C) Bool) :
    probBad_streamKey prims D game =
      (Pr{let r ← (simulateQ (jointKeyWorld prims D false) game).run keyJointInitial}[r.2.bad = true]).toReal := by
  unfold probBad_streamKey
  congr 1
  refine simulateQ_probBad_eq _ _ (fun s => s.bad = true) ?_ ?_ ?_ game keyJointInitial
  · exact fun q s r hr => jointKeyWorld_good prims D q s r hr
  · intro q s hs r hr
    rw [jointKeyWorld_bad prims D true q s r hr, hs]
    rfl
  · intro q s hs r hr
    rw [jointKeyWorld_bad prims D false q s r hr, hs]
    rfl

/-- Replacing the real hidden keys by independently sampled AES keys costs at most the single
stream-key bad event. This applies to arbitrary adaptive games, without secrecy assumptions. -/
theorem keyWorld_coupling (prims : Primitives) (D : C.Coalition)
    (game : OracleComp (WorldSpec C) Bool) :
    |accepts prims game -
      (Pr{let z ← ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
        (simulateQ (keyWorld prims D keys) game).run' ∅}[z = true]).toReal| ≤ probBad_streamKey prims D game := by
  let : MeasurableSpace Bool := ⊤
  have h := (abs_prEvent_toReal_sub_le_measureTVDist
      ((simulateQ (jointKeyWorld prims D true) game).run' keyJointInitial)
      ((simulateQ (jointKeyWorld prims D false) game).run' keyJointInitial) (· = true) measurable_from_top).trans
    (jointKeyWorld_coupling prims D game keyJointInitial)
  rw [jointKeyWorld_true_accepts, jointKeyWorld_false_probability] at h
  exact h

end ThresholdLeanXmssSecurity
end KeyWorldBound
