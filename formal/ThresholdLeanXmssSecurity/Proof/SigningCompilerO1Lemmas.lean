import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Frame
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncHonestRead

/-! # Shared helpers of the O1 coupling

- `relTriple_map_right`, `ne_none_of_le` and `cacheRelation_congr` are small facts of couplings
  and caches.
- `keepsRevealed_virtual` and `keepsRevealed_pending` state that a source call keeps the reveal map.
- `ReadStep` holds the effect of one real read, and `syncFields_observe` carries the
  synchronization fields over a real read.
- `runX_sourcePendingX_some` and `runX_sourcePendingX_fresh` give the source side of a pending call.
- `truncateHash_interpret`, `chainWalk_step` and `tweakable_tweakableHash` unfold one step of a
  chain walk.
- `realWorld_run_carried` and `realWorld_run_stop` state that a run of the real world keeps the
  carried state and the stop of the real side.
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Frame
open SigningCompilerSyncBackend SigningCompilerSyncRealRead SigningCompilerSyncTrigger
open SigningCompilerSyncLocalRead SigningCompilerSyncLocalSlot SigningCompilerSyncHonestRead
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-! ## Couplings and caches -/

/-- A map on the right side of a coupling moves into its post. -/
theorem relTriple_map_right {α β δ : Type} {oa : ProbComp α} {ob : ProbComp β} {g : β → δ}
    {R : α → δ → Prop} (h : RelTriple oa ob (fun a b => R a (g b))) : RelTriple oa (g <$> ob) R := by
  simpa only [id_map] using relTriple_map (f := id) (g := g) (R := R) h

/-- A larger cache holds each entry of a smaller cache. -/
theorem ne_none_of_le {c c' : HashCache C} (hle : c ≤ c') {query : Query C}
    (h : c query ≠ none) : c' query ≠ none := by
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h
  rw [hle hw]
  exact Option.some_ne_none _

/-- The effect of one real read of `input` with the answer `v`. The read observes the answer in the
visible cache, counts once, logs the answer and keeps the private cache, the carried state and the
trace. -/
structure ReadStep (input : Query C) (v : HashOutput) (a a' : RealState C) : Prop where
  visible : visibleOf a' = (visibleOf a).cacheQuery input v
  seen : ∀ w, visibleOf a input = some w → w = v
  priv : a'.2 = a.2
  carried : a'.1.2 = a.1.2
  trace : a'.1.1.2 = a.1.1.2
  count : a'.1.1.1.1.1.1.2 = a.1.1.1.1.1.1.2 + 1
  log : ∃ t value, a'.1.1.1.1.1.2 = a.1.1.1.1.1.2.logQuery t value ∧
    SigningCacheLogProof.hashCall ⟨t, value⟩ = some (input, v)

/-- A cache that holds `v` at `input` or nothing there grows when it observes `v`. -/
theorem le_cacheQuery_of_seen (vis : HashCache C) (input : Query C) (v : HashOutput)
    (h : ∀ w, vis input = some w → w = v) : vis ≤ vis.cacheQuery input v := by
  cases hv : vis input with
  | none => exact QueryCache.le_cacheQuery vis hv
  | some w =>
    rw [h w hv] at hv
    rw [observe_same vis input v hv]

/-- The observed cache is a result of the lazy read. -/
theorem observe_mem_support (vis : HashCache C) (input : Query C) (v : HashOutput)
    (h : ∀ w, vis input = some w → w = v) :
    (v, vis.cacheQuery input v) ∈ support (((Query C →ₒ HashOutput).randomOracle input).run vis) := by
  cases hv : vis input with
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hv]
    simp [uniformSampleImpl]
  | some w =>
    rw [h w hv] at hv
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hv, observe_same vis input v hv]
    simp

/-- One real read grows the log cache. -/
theorem ReadStep.realLog_le {input : Query C} {v : HashOutput} {a a' : RealState C}
    (h : ReadStep input v a a') : realLog a ≤ realLog a' := by
  obtain ⟨t, value, hl, -⟩ := h.log
  intro query w hq
  change SigningCacheLogProof.logCache a'.1.1.1.1.1.2 query = some w
  rw [hl, SigningCacheLogProof.logCache_logQuery]
  rw [show SigningCacheLogProof.logCache a.1.1.1.1.1.2 query = some w from hq]
  rfl

/-- One real read keeps the log agreement. -/
theorem ReadStep.logAgreement (P : PublicParameter) {input : Query C} {v : HashOutput}
    {a a' : RealState C} (h : ReadStep input v a a')
    (hl : SigningPartnerCompareProof.LogAgreement P a.1.1.1.1.1) :
    SigningPartnerCompareProof.LogAgreement P a'.1.1.1.1.1 := by
  obtain ⟨t, value, hlog, hcall⟩ := h.log
  have hw := observe_mem_support (visibleOf a) input v h.seen
  have hagree := SigningPartnerCompareProof.logAgreement_hash P input a.1.1.1.1.1 hl _ hw
    a'.1.1.1.1.1.2 (fun q' => by
      rw [hlog, SigningCacheLogProof.logCache_logQuery, hcall]
      by_cases he : input = q' <;> simp [he]) a'.1.1.1.1.1.1.2
  have hv : a'.1.1.1.1.1.1.1 = (visibleOf a).cacheQuery input v := h.visible
  rw [← hv] at hagree
  exact hagree

/-- A new visible entry after one real read is at the read input. -/
theorem ReadStep.fresh {input : Query C} {v : HashOutput} {a a' : RealState C}
    (h : ReadStep input v a a') (query : Query C) (hq : visibleOf a' query ≠ none) :
    visibleOf a query ≠ none ∨ query = input := by
  by_cases he : query = input
  · exact Or.inr he
  · rw [h.visible, QueryCache.cacheQuery_of_ne _ _ he] at hq
    exact Or.inl hq

/-- The synchronization fields pass to a real state with a larger visible cache, the same carried
state and the same trace. -/
theorem syncFields_observe (x : Keys3 C) (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2)
    (s : HiddenKey → Digest) (pads : Point → Digest) (u : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)
    (a a' : RealState C) (b : SourceState C × CompState C)
    (hs : SyncFields x s pads noise (gOf s pads u) rest a b)
    (hr : RealPrivate x s pads noise (gOf s pads u) rest a'.2 (visibleOf a'))
    (hle : visibleOf a ≤ visibleOf a') (hc : a'.1.2 = a.1.2) (ht : a'.1.1.2 = a.1.1.2) :
    SyncFields x s pads noise (gOf s pads u) rest a' b :=
  { hs with
    corrupt := by rw [hc]; exact hs.corrupt
    bound := by rw [hc]; exact hs.bound
    released := by rw [hc]; exact hs.released
    exposed := by rw [hc]; exact hs.exposed
    candidates := by rw [hc]; exact hs.candidates
    flag := by rw [hc]; exact hs.flag
    opening := ⟨fun e he => realPrivate_actualValue x hkeys s pads noise u rest _ _ hr e he,
      hs.opening.released⟩
    virtualSeen := fun T p hp => ne_none_of_le hle (hs.virtualSeen T p hp)
    trace := ht.trans hs.trace
    realPrivate := hr }

/-! ## The source side of a call -/

/-- A virtual call at a chain point keeps the reveal map of the source. -/
theorem keepsRevealed_virtual (P : PublicParameter) (seeds : C.Term → HashOutput) (T : C.Term)
    (lay : Layer) (e : KeyIndex) (l : ChainIndex) (d : WinternitzDigit) :
    SourceKeepsX (fun src : SourceState C => src.revealed)
      (sourceVirtualX P seeds T (.chain lay e l d)) := by
  unfold sourceVirtualX
  exact (SourceKeepsX.lift _).bind _ fun _ => SourceKeepsX.pure ()

/-- A pending call keeps the reveal map of the source. -/
theorem keepsRevealed_pending (P : PublicParameter) (p : PendingInput) :
    SourceKeepsX (fun src : SourceState C => src.revealed) (sourcePendingX P p) := by
  have tail (prior : Option DeferredOutput) : SourceKeepsX (fun src : SourceState C => src.revealed)
      (do
        let value ← liftM (deferredQueryX (C := C) (.pending p))
        if prior.isNone then
          modify fun (source : SourceState C) => { source with allocated := source.allocated ++ [p] }
        pure value : SourceMX C DeferredOutput) := by
    refine (SourceKeepsX.lift (deferredQueryX (.pending p))).bind _ fun value => ?_
    split
    · exact (SourceKeepsX.modify (fun st => { st with allocated := st.allocated ++ [p] })
        (fun _ => rfl)).bind _ (fun _ => SourceKeepsX.pure value)
    · exact SourceKeepsX.pure value
  unfold sourcePendingX
  refine (SourceKeepsX.lift (deferredQueryX (.inspect p))).bind _ fun prior => ?_
  refine SourceKeepsX.get.bind _ fun source => ?_
  dsimp only
  split
  · refine (SourceKeepsX.lift (deferredQueryX (.hash (.hash _)))).bind _ fun value => ?_
    refine (SourceKeepsX.lift (deferredQueryX (.record p value))).bind _ fun _ => ?_
    exact (SourceKeepsX.modify (fun st => { st with allocated := st.allocated ++ [p] })
      (fun _ => rfl)).bind _ (fun _ => SourceKeepsX.pure _)
  · rename_i original priorCopy known next hmiss
    split
    · exact (SourceKeepsX.modify (fun st => { st with consistent := false }) (fun _ => rfl)).bind _
        (fun _ => tail original)
    · simpa only [pure_bind] using tail original

/-! ## One step of a chain walk -/

/-- The truncation of an answer is the reading of its low half. -/
theorem truncateHash_interpret (s : HiddenKey → Digest) (v : DeferredOutput) :
    truncateHash (v.interpret s) = v.low.interpret s :=
  congrArg Prod.snd (XmssSecurity.Rom.hashOutputEquivDigestPair.apply_symm_apply _)

/-- A walk of `n + 1` steps is the walk of `n` steps and one more step. -/
theorem chainWalk_step {m : Type → Type} [Monad m] [HasQuery HashSpec m] (P : PublicParameter)
    (lay : Layer) (key : KeyIndex) (l : ChainIndex) (start n : ℕ) (v : Digest)
    (h : start + n < chainLength - 1) :
    Verification.chainWalkWithHash (m := m) P lay key l start (n + 1) v =
      Verification.chainWalkWithHash P lay key l start n v >>= fun previous =>
        Verification.tweakableHashWithHash P (.chain lay key ⟨start + n, h⟩) (Verification.chainPayload l previous) := by
  rw [Verification.chainWalk_eq_succ]
  simp only [dif_pos h]

/-- One step of `Th` on the domain of `H` is the truncated answer of one query. -/
theorem tweakable_tweakableHash (P : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    tweakable (C := C) (Verification.tweakableHashWithHash P domain payload : OracleComp HashSpec Digest) =
      truncateHash <$> hashQuery (.hash (tweakableHashInput P domain payload)) := by
  simp [Verification.tweakableHashWithHash, Verification.thWithHash, tweakable_bind,
    tweakable_oracleHash, tweakable_pure, thInput_hashDomainFields, map_eq_bind_pure_comp]

section Runs
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The cache relation reads only the cache, the pending answers and the virtual terms. -/
theorem cacheRelation_congr (P : PublicParameter) (seeds : C.Term → HashOutput)
    (d d' : DeferredState C) (actual : HashCache C) (hc : d'.cache = d.cache)
    (hp : d'.pending = d.pending) (hv : d'.virtual = d.virtual)
    (h : CacheRelation P seeds s d actual) : CacheRelation P seeds s d' actual := by
  refine ⟨fun query hq => ?_, fun p value hpv => h.pending p value (hp ▸ hpv)⟩
  rw [hc]
  apply h.agree query
  intro hs
  apply hq
  unfold SuspendedQuery at hs ⊢
  rw [hc, hp, hv]
  exact hs

/-- A mapped source update runs with no backend call. -/
theorem runX_map_modify {α : Type} (backend : QueryImpl (SpecX C) (StateT (CompState C) ProbComp))
    (f : Unit → α) (g : SourceState C → SourceState C) (src : SourceState C) (st : CompState C) :
    runX backend (f <$> modify g) src st = pure ((f (), g src), st) := by
  rw [map_eq_bind_pure_comp, runX_bind, runX_modify, pure_bind, Function.comp_apply, runX_pure]

/-- The source side of a pending call with a stored answer. -/
theorem runX_sourcePendingX_some (p : PendingInput) (answer : DeferredOutput) (src : SourceState C)
    (st : CompState C) (hf : RestFree x.2.1 st.1.1.1.1.data.cache)
    (hprior : st.1.1.1.1.data.pending p = some answer) :
    runX (compBackend x q s pads u rest noise) (sourcePendingX x.1 p) src st =
      (fun r => ((r.1, src), r.2)) <$>
        (compBackend x q s pads u rest noise (.inl (.inl (.inl (.pending p))))).run st := by
  simp [sourcePendingX, runX_bind, runX_deferred, runX_get,
    backendT_inspect capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest p st hf, hprior]
  exact runX_deferred _ _ _ _

/-- The source side of a fresh pending call with an unrevealed key. -/
theorem runX_sourcePendingX_fresh (p : PendingInput) (src : SourceState C) (st : CompState C)
    (hf : RestFree x.2.1 st.1.1.1.1.data.cache)
    (hprior : st.1.1.1.1.data.pending p = none) (hrev : src.revealed p.key = none) :
    runX (compBackend x q s pads u rest noise) (sourcePendingX x.1 p) src st =
      (fun r => ((r.1, { src with allocated := src.allocated ++ [p] }), r.2)) <$>
        (compBackend x q s pads u rest noise (.inl (.inl (.inl (.pending p))))).run st := by
  simp [sourcePendingX, runX_bind, runX_deferred, runX_get,
    backendT_inspect capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest p st hf, hprior,
    hrev, runX_map_modify]

/-- A world run keeps the carried state. -/
theorem realWorld_run_carried {α : Type} (oa : OracleComp (WorldSpec C) α) (a : RealState C)
    (r : α × RealState C)
    (hr : r ∈ support ((simulateQ (realWorld prims x s pads u rest) oa).run a)) :
    r.2.1.2 = a.1.2 := by
  refine SeedHitProof.support_simulateQ_inv (realWorld prims x s pads u rest)
    (fun st : RealState C => st.1.2 = a.1.2) (fun t st hst z hz => ?_) _ a rfl r hr
  rw [← hst]
  change z ∈ support ((_root_.ThresholdLeanXmssSecurity.fuse (rawTraceWorld prims x)
    (realImpl x (gOf s pads u) rest) t).run st) at hz
  simp only [_root_.ThresholdLeanXmssSecurity.fuse, StateT.run_mk, rawTraceWorld, rawKeyedSplitWorld,
      rawCarriedLogged, simulateQ_map, simulateQ_bind, StateT.run_map, StateT.run_bind,
      support_map, support_bind, Set.mem_image, Set.mem_iUnion] at hz
  obtain ⟨_, ⟨_, ⟨_, ⟨_, -, rfl⟩, ⟨_, -, rfl⟩⟩, rfl⟩, rfl⟩ := hz
  rfl

/-- The stop of the real side persists over a run of the real world. -/
theorem realWorld_run_stop {α : Type} (m : OracleComp (WorldSpec C) α) (a : RealState C)
    (h : RealStop q a) (r : α × RealState C)
    (hr : r ∈ support ((simulateQ (realWorld prims x s pads u rest) m).run a)) : RealStop q r.2 :=
  simulateQ_sticky _ (RealStop q) (fun t st hst r hr => realStop_world prims x (gOf s pads u) rest q
    t st hst r (by with_reducible exact hr)) m a h r hr

end Runs

end ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.relTriple_map_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.relTriple_map_right

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.ne_none_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.ne_none_of_le

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.le_cacheQuery_of_seen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.le_cacheQuery_of_seen

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.observe_mem_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.observe_mem_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.ReadStep.realLog_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.ReadStep.realLog_le

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.ReadStep.logAgreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.ReadStep.logAgreement

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.ReadStep.fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.ReadStep.fresh

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.syncFields_observe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.syncFields_observe

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.keepsRevealed_virtual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.keepsRevealed_virtual

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.keepsRevealed_pending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.keepsRevealed_pending

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.truncateHash_interpret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.truncateHash_interpret

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.chainWalk_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.chainWalk_step

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.tweakable_tweakableHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.tweakable_tweakableHash

/--
info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.cacheRelation_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.cacheRelation_congr

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.runX_map_modify' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.runX_map_modify

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.runX_sourcePendingX_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.runX_sourcePendingX_some

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.runX_sourcePendingX_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.runX_sourcePendingX_fresh

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.realWorld_run_carried' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.realWorld_run_carried

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.realWorld_run_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Lemmas.realWorld_run_stop
