import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkTransport
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkOpenings
import ThresholdLeanXmssSecurity.Proof.TreeSetupKeys
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkUnreached
import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkPositions

/-!
# Setup and stream-key facts for the check coupling

A live checkpoint retains the setup log and has a collision-free continuation.
The setup-key agreement theorem therefore applies to its actual setup rows.
Only stream keys used by honest draws need to be cached: known term keys and
pairs with one honest and one corrupt endpoint. A wrong accepted record forces
a positive output width, whose actual prefix draw supplies those cache entries.

`checkpointFacts` packages present setup rows, term-key agreement, and cached
used keys for the frozen source family. `CheckKernelCoupling` relates the real
check kernel to that family's fixed hybrid adapter. The kernel retains every
pending program, both caches, and the full log; its exact scheduler split and
abort persistence give `walkCheckpointTransport_of_checkKernelCoupling`.
The coupling concerns the check kernel, not the later scheduler rounds or observer.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckWalkCoupling

attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- A live continuation rules out a budget collision already present at its checkpoint. -/
theorem checkpoint_good (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))
    (W : TreeCheckTailWalk A) (c : W.β) (o : TreeCheckTailCheckpoint A)
    (live : (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
      (.inl (c, o))) : ¬ TreeSimHashBudgetCollision o.2.2 := by
  obtain ⟨r, run, bad, _⟩ := live
  have before := treeCheckBatchCont_log_prefix prims K circuits D A Z (W.boundary c).batch o r run
  exact fun collision => bad.1 (treeSimHashBudgetCollision_mono before collision)

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 2000 in
/-- The frozen source walk keeps its setup collision-free at every live checkpoint. -/
theorem setup_good (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree)) (step : ℕ)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (c : (TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x j.val Z step p).β)
    (o : TreeCheckTailCheckpoint A)
    (run : (.inl (c, o) : ((TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x
      j.val Z step p).cut prims K circuits settings D Z).σ) ∈ support
      ((TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x j.val Z step p).cut
        prims K circuits settings D Z).pre)
    (live : ((TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x j.val Z step p).cut
      prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j (.inl (c, o))) :
    ¬ TreeSimHashBudgetCollision p.2.2 := by
  have before : p.2.2 <+: o.2.2 := by
    with_reducible exact (TreeCheckWalkRecipe.sourceWalk_log_prefix prims K D A circuits settings top tree x
      j.val Z step p c o run)
  have good : ¬ TreeSimHashBudgetCollision o.2.2 := by
    with_reducible exact (checkpoint_good prims K circuits settings top tree D A x z Z j
      (TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x j.val Z step p) c o live)
  exact fun collision => good (treeSimHashBudgetCollision_mono before collision)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Actual present setup rows agree at every common term holder. -/
theorem setupKeys_term_agree (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (setup : p ∈ support (treeSaltSetup prims D A x z))
    (good : ¬ TreeSimHashBudgetCollision p.2.2)
    (present : ∀ i, i ∉ D.1 → (p.1.2 i).isSome) :
    ∀ i k, i ∉ D.1 → k ∉ D.1 → ∀ T, i ∈ C.holders T → k ∈ C.holders T →
      (TreeCheckWalkRecipe.setupKeys p.1.2 i).term T =
        (TreeCheckWalkRecipe.setupKeys p.1.2 k).term T := by
  intro i k hi hk T heldI heldK
  obtain ⟨ki, rowI⟩ := Option.isSome_iff_exists.mp (present i hi)
  obtain ⟨kk, rowK⟩ := Option.isSome_iff_exists.mp (present k hk)
  rw [TreeCheckWalkRecipe.setupKeys_some p.1.2 i ki rowI,
    TreeCheckWalkRecipe.setupKeys_some p.1.2 k kk rowK]
  exact treeAgreementSetupKeys prims D A x z p setup good i k ki kk rowI rowK T heldI heldK

/-- A real multiplication reaches an exchange that respects abort frames. -/
theorem mult_exchange (K : Constants C E) (ctx : Context C) (mode : ReshareMode)
    (x y : Shares C Bit) (count : ℕ) (st : RunState C) :
    TreeSimCheckExchange (((realRunGadgets (G := RealSpec) K ctx mode).mult x y count).run st) := by
  change TreeSimCheckExchange
    ((prssRandomness ctx bitCodec 0 count >>= fun rnd =>
      reshareWith K ctx mode rnd (mulRep K ctx x y) count).run st)
  rw [prssRandomness_run]
  cases mode with
  | peer =>
    apply TreeSimCheckExchange.oracle_bind
    intro rnd
    rw [reshareWith, show rnd = (rnd.1, rnd.2) from rfl, reshare_run]
    exact TreeSimCheckExchange.exchange_bind _ _
  | collector =>
    apply TreeSimCheckExchange.oracle_bind
    intro rnd
    rw [reshareWith, show rnd = (rnd.1, rnd.2) from rfl, reshareCollector_run]
    exact TreeSimCheckExchange.exchange_bind _ _

/-- Output rerandomization reaches a peer exchange even for a zero-width output. -/
theorem rerand_exchange (K : Constants C E) (ctx : Context C) (mode : ReshareMode)
    (v : Shares C Bit) (count : ℕ) (st : RunState C) :
    TreeSimCheckExchange (((realRunGadgets (G := RealSpec) K ctx mode).rerand v count).run st) := by
  change TreeSimCheckExchange
    ((prssRandomness ctx bitCodec 0 count >>= fun rnd =>
      reshare K ctx bitCodec rnd (ownerSum K ctx v) count).run st)
  rw [prssRandomness_run]
  apply TreeSimCheckExchange.oracle_bind
  intro rnd
  rw [show rnd = (rnd.1, rnd.2) from rfl, reshare_run]
  exact TreeSimCheckExchange.exchange_bind _ _

/-- Every circuit prefix has a mandatory abort-respecting exchange before its check. -/
theorem beforeVerify_exchange (K : Constants C E) (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) (st : RunState C) :
    TreeSimCheckExchange ((treeSimCheckBeforeVerify K ctx mode jobs inputs).run st) := by
  unfold treeSimCheckBeforeVerify
  cases layers : List.range (depth jobs) with
  | nil =>
    simp only [List.foldlM_nil, pure_bind, StateT.run_bind, StateT.run_pure]
    exact (rerand_exchange K ctx mode _ _ st).bind _
  | cons layer rest =>
    simp only [List.foldlM_cons, StateT.run_bind, bind_assoc]
    apply TreeSimCheckExchange.bind
    unfold layerBody
    simp only [StateT.run_bind, StateT.run_pure]
    exact (mult_exchange K ctx mode _ _ _ st).bind _

/-- The local input queries preceding a mandatory exchange preserve its abort behavior. -/
theorem inputs_exchange {α : Type} (ctx : Context C)
    (jobs : List Job) (k : List (C.Term → List Bit) → PartyM C E RealSpec α)
    (exchange : ∀ inputs, TreeSimCheckExchange (k inputs)) :
    TreeSimCheckExchange (jobs.mapM (inputShares ctx) >>= k) := by
  induction jobs generalizing k with
  | nil => simpa only [List.mapM_nil, pure_bind] using exchange []
  | cons job jobs ih =>
    simp only [List.mapM_cons, bind_assoc, inputShares, pure_bind]
    apply TreeSimCheckExchange.oracle_bind
    intro terms
    exact ih (fun inputs => k ((fun T => terms.getD (C.terms.idxOf T) []) :: inputs))
      (fun _ => exchange _)

/-- Every audited batch starts with a mandatory exchange. -/
theorem batch_exchange (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    TreeSimCheckExchange ((treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx jobs).run.run initial) := by
  rw [treeSimCheckBatchAudit_run_prefix]
  apply TreeSimCheckExchange.bind
  unfold treeSimCheckBatchPrefix
  apply inputs_exchange ctx
  intro inputs
  exact (beforeVerify_exchange K ctx settings.mode _ inputs _).bind _

/-- A ceremony with a batch reaches an abort-respecting exchange after setup. -/
theorem afterSetup_exchange (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (batchSize : 0 < settings.batchSize) (ctx : Context C) (top : TopTree) (tree : Tree)
    (index : Fin (treeBatches settings tree)) :
    TreeSimCheckExchange (treeSimCheckAfterSetupAudit K circuits settings ctx top tree) := by
  have first : TreeCheckWalkRecipe.firstChunks settings tree ≠ [] :=
    TreeCheckWalkUnreached.firstChunks_ne_nil settings tree batchSize
      ⟨0, lt_of_le_of_lt (Nat.zero_le index.val) index.isLt⟩ rfl
  obtain ⟨head, rest, chunked⟩ := List.exists_cons_of_ne_nil first
  change chunks settings.batchSize (treeLockstepFirstJobs tree) = head :: rest at chunked
  rw [treeLockstep_afterSetup_first, TreeCheckWalkRecipe.auditBatched_run, chunked,
    TreeCheckWalkRecipe.auditChunks_cons]
  simp only [bind_assoc, pure_bind]
  exact (batch_exchange K circuits settings ctx head (0, 0)).bind _

set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
/-- One accepted post-setup result forces every honest setup row to be present. -/
theorem auditAfter_setup_live (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (batchSize : 0 < settings.batchSize) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (state : A.State)
    (keys : C.Party → Option (PrssKeys C)) (index : Fin (treeBatches settings tree))
    (world : TreeSimState C)
    (result : (Bool × (A.State × (C.Party → Option (TreeOutput × List (TreeSimCheckBatchRecord C))))) ×
      TreeSimState C)
    (run : result ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (auditAfterProgram K circuits settings top tree D A x Z state keys)).run world))
    (accepted : ∃ i value, result.1.2.2 i = some value) :
    ∀ i, i ∉ D.1 → (keys i).isSome := by
  have raw := treeCheck_logged_support prims D _ _ run
  unfold auditAfterProgram at raw
  rw [mem_support_bind_iff] at raw
  obtain ⟨next, started, raw⟩ := raw
  rw [mem_support_bind_iff] at raw
  obtain ⟨out, finished, raw⟩ := raw
  rw [mem_support_bind_iff] at raw
  obtain ⟨answer, observed, final⟩ := raw
  rw [mem_support_pure_iff] at final
  have output : result.1.2 = out := congrArg Prod.snd final
  rw [output] at accepted
  with_reducible exact (treeSimCheck_exchange_continuations_live D A (ceremonyFuel circuits settings - 3)
    state keys (fun i prss => treeSimCheckAfterSetupAudit K circuits settings ⟨i, x i, prss⟩ top tree)
    (fun i prss => afterSetup_exchange K circuits settings batchSize ⟨i, x i, prss⟩ top tree index)
    next started out finished accepted)

/-- Live cuts of an actual after-setup split retain every honest PRSS row. -/
theorem live_setup_all (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (batchSize : 0 < settings.batchSize) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))
    (W : TreeCheckTailWalk A)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (split : W.Split prims K circuits settings D top tree x Z p)
    (s : (W.cut prims K circuits settings D Z).σ)
    (pre : s ∈ support (W.cut prims K circuits settings D Z).pre)
    (live : (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j s) :
    ∀ i, i ∉ D.1 → (p.1.2 i).isSome := by
  obtain ⟨r, run, bad, _⟩ := live
  have full : r ∈ support (treeCheckAfterSetup prims K circuits settings top tree D A x Z p) := by
    rw [W.cut_split split, mem_support_bind_iff]
    exact ⟨s, pre, run⟩
  rw [treeCheckAfterSetup_eq_audit, support_map] at full
  obtain ⟨out, supported, result⟩ := full
  cases result
  obtain ⟨_, _, _, _, i, value, records, _, _, _, _, _, _, accepted, _⟩ := bad.2
  exact auditAfter_setup_live prims K circuits settings batchSize top tree D A x Z p.1.1 p.1.2
    j p.2 out supported ⟨i, (value, records), accepted⟩

-- The private replay projection from TreeLockstepOpenedFinal, kept with its original proof.
omit [Fintype E] [DecidableEq E] in
private theorem ro_allowed
    {ι α : Type} {G : OracleSpec ι}
    (allowed : (t : (PartySpec C E G).Domain) → (PartySpec C E G).Range t → Prop)
    (p : OracleComp (RoSpec C) α) (a : α)
    (h : TreeSimCheckAllowed allowed (oracleStep p : PartyM C E G α).run (some a)) :
    TreeSimCheckAllowed (fun t u => allowed (.inl (.inl (.inr t))) u) p a := by
  induction p using OracleComp.inductionOn generalizing a with
  | pure b =>
    have he : some a = some b := h.pure_inv
    cases Option.some.inj he
    exact .pure _ b
  | query_bind t k ih =>
    rw [oracleStep_bind] at h
    obtain ⟨v, hv, hk⟩ := h.option_bind_inv _ _ _
    have query_eq : (oracleStep (OracleComp.lift (OracleSpec.query t)) : PartyM C E G _).run =
        ((OracleComp.lift (OracleSpec.query (spec := PartySpec C E G)
          (.inl (.inl (.inr t))))) >>= fun u => pure (some u)) := by
      cases t <;> rfl
    rw [query_eq] at hv
    obtain ⟨u, hu, he⟩ := hv.bind_inv
    have he := Option.some.inj he.pure_inv
    subst v
    exact .query t k u a (hu.query_inv _ _) (ih u a hk)

/-- Every member of an actual replayed list has an actual replay. -/
theorem allowed_mapM_member {ι α β : Type} {S : OracleSpec.{0, 0} ι}
    (allowed : (t : S.Domain) → S.Range t → Prop) (f : α → OracleComp S β)
    (xs : List α) (ys : List β) (run : TreeSimCheckAllowed allowed (xs.mapM f) ys)
    (x : α) (mem : x ∈ xs) : ∃ y, TreeSimCheckAllowed allowed (f x) y := by
  induction xs generalizing ys with
  | nil => simp at mem
  | cons a xs ih =>
      simp only [List.mapM_cons] at run
      obtain ⟨y, first, rest⟩ := run.bind_inv
      obtain ⟨tail, tailRun, _⟩ := rest.bind_inv
      rcases List.mem_cons.mp mem with rfl | later
      · exact ⟨y, first⟩
      · exact ih tail tailRun later

/-- A positive-width visible PRG draw fills its actual derived stream key. -/
theorem prg_cached (prims : Primitives) (D : C.Coalition)
    (cache : HashCache C × HiddenCache C)
    (allowed : (t : (RoSpec C).Domain) → (RoSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr x) u → TreeLockstepStreamAnswer prims D cache x u)
    (name : KeyName C) (key : HashOutput) (label idx count : ℕ) (values : ℕ → Bit)
    (visible : ¬ Hidden D name) (positive : 0 < count)
    (run : TreeSimCheckAllowed allowed (prgBits name key label idx count) values) :
    ∃ derived, cache.1 (.streamKey key) = some derived := by
  have answer := (treeLockstep_prg_stream_answers prims D cache allowed streams name key label idx count values run).1 0 positive
  simp only [TreeLockstepStreamAnswer, if_neg visible] at answer
  obtain ⟨derived, cached, _⟩ := answer
  exact ⟨derived, cached⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Only the visible keys actually used by this honest PRSS draw are cached. -/
theorem prss_cached (prims : Primitives) (D : C.Coalition)
    (cache : HashCache C × HiddenCache C)
    (allowed : (t : (RoSpec C).Domain) → (RoSpec C).Range t → Prop)
    (streams : ∀ x u, allowed (.inr x) u → TreeLockstepStreamAnswer prims D cache x u)
    (ctx : Context C) (label idx count : ℕ) (positive : 0 < count) (rnd : PrssOutput C Bit)
    (run : TreeSimCheckAllowed allowed (prssDraw ctx (bitCodec (E := E)) label idx count) rnd) :
    (∀ T, ctx.self ∈ C.holders T → KnownTo D.1 T →
      ∃ derived, cache.1 (.streamKey (ctx.prss.term T)) = some derived) ∧
    (∀ j, j ≠ ctx.self → j ∈ D.1 →
      ∃ derived, cache.1 (.streamKey (ctx.prss.pair j)) = some derived) := by
  unfold prssDraw at run
  obtain ⟨terms, termRun, rest⟩ := run.bind_inv
  obtain ⟨pairs, pairRun, _⟩ := rest.bind_inv
  constructor
  · intro T held known
    obtain ⟨values, valueRun⟩ := allowed_mapM_member allowed _ C.terms terms termRun T (mem_terms T)
    simp only [if_pos held] at valueRun
    exact prg_cached prims D cache allowed streams (.term T) (ctx.prss.term T) label idx count values
      (TreeCheckWalkTransport.term_visible D T known) positive valueRun
  · intro j ne corrupt
    obtain ⟨values, valueRun⟩ := allowed_mapM_member allowed _ C.parties pairs pairRun j (by simp [Committee.parties])
    simp only [dif_neg ne] at valueRun
    exact prg_cached prims D cache allowed streams (.pair (C.pairOf ctx.self j ne.symm))
      (ctx.prss.pair j) label idx count values
      (TreeCheckWalkTransport.pair_visible D ctx.self j ne.symm corrupt) positive valueRun

omit [Fintype E] [DecidableEq E] in
/-- A positive output width supplies all visible keys used by the prefix's last PRSS draw. -/
theorem beforeVerify_cached (prims : Primitives) (K : Constants C E) (D : C.Coalition)
    (cache : HashCache C × HiddenCache C)
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (streams : ∀ x u, allowed (.inl (.inl (.inr (.inr x)))) u →
      TreeLockstepStreamAnswer prims D cache x u)
    (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) (initial : RunState C)
    (out : Shares C Bit × List (Tuple C)) (final : RunState C)
    (positive : 0 < (outputsOf jobs).length)
    (run : TreeSimCheckAllowed allowed ((treeSimCheckBeforeVerify K ctx mode jobs inputs).run initial).run
      (some (out, final))) :
    (∀ T, ctx.self ∈ C.holders T → KnownTo D.1 T →
      ∃ derived, cache.1 (.streamKey (ctx.prss.term T)) = some derived) ∧
    (∀ j, j ≠ ctx.self → j ∈ D.1 →
      ∃ derived, cache.1 (.streamKey (ctx.prss.pair j)) = some derived) := by
  simp only [treeSimCheckBeforeVerify, StateT.run_bind, StateT.run_pure] at run
  obtain ⟨⟨p, st⟩, _, rest⟩ := run.option_bind_inv _ _ _
  obtain ⟨⟨v, next⟩, rerand, _⟩ := rest.option_bind_inv _ _ _
  change TreeSimCheckAllowed allowed
    (((prssRandomness ctx bitCodec 0 (outputsOf jobs).length >>= fun rnd =>
      reshare K ctx bitCodec rnd (ownerSum K ctx (outputShares K jobs p.1)) (outputsOf jobs).length).run st).run)
    (some (v, next)) at rerand
  rw [prssRandomness_run] at rerand
  obtain ⟨rnd, draw, _⟩ := rerand.option_bind_inv _ _ _
  exact prss_cached prims D cache (fun t u => allowed (.inl (.inl (.inr t))) u)
    (fun x u h => streams x u h) ctx st.label 0 _ positive rnd (ro_allowed allowed _ rnd draw)

/-- An incorrect accepted record must have a positive output width. -/
theorem incorrect_outputs_positive (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    {allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop}
    {r : TreeSimCheckBatchRecord C} (valid : TreeSimCheckRecordValid K circuits settings allowed r)
    (hash : Query C → HashOutput) (seeds : C.Term → HashOutput)
    (wrong : r.outputs ≠ r.jobs.map
      (fun job => ThresholdLeanXmssSecurity.D prims hash (evalJob circuits r.ctx.keys.parameter seeds job))) :
    0 < (outputsOf (r.jobs.map (circuits r.ctx.keys.parameter ·.kind))).length := by
  by_contra zero
  have hz : (outputsOf (r.jobs.map (circuits r.ctx.keys.parameter ·.kind))).length = 0 := by omega
  rw [outputsOf_eq, length_flatIdx, List.map_map] at hz
  have empty : ∀ c ∈ r.jobs.map (circuits r.ctx.keys.parameter ·.kind), c.outputs = [] := by
    intro c hc
    apply List.length_eq_zero_iff.mp
    exact List.sum_eq_zero_iff_forall_eq_nat.mp hz _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  obtain ⟨opened, output⟩ := valid.assembled K circuits settings
  apply wrong
  rw [output, treeSimCheck_assemble_zero _ opened empty, List.map_map]
  apply List.map_congr_left
  intro job hj
  have jobEmpty := empty _ (List.mem_map.mpr ⟨job, hj, rfl⟩)
  simp only [evalJob, D_bind, D_pure, Circuit.eval, jobEmpty, List.map_nil]
  rfl

/-- A successful checkpoint row contains the actual rerandomization draw in its final caches. -/
theorem boundary_cached (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (b : TreeCheckTailBoundary A) (parameters : ∀ i, (b.batch.ctx i).keys.parameter = b.batch.parameter)
    (o : TreeCheckTailCheckpoint A) (run : o ∈ support (b.pre prims K circuits settings D))
    (positive : 0 < (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length)
    (i : C.Party) (honest : i ∉ D.1) (data : MainInput C × (Shares C Bit × List (Tuple C)) × RunState C)
    (present : o.1.2 i = some data) :
    (∀ T, (b.batch.ctx i).self ∈ C.holders T → KnownTo D.1 T →
      ∃ derived, o.2.1.1 (.streamKey ((b.batch.ctx i).prss.term T)) = some derived) ∧
    (∀ j, j ≠ (b.batch.ctx i).self → j ∈ D.1 →
      ∃ derived, o.2.1.1 (.streamKey ((b.batch.ctx i).prss.pair j)) = some derived) := by
  have replay := treeLockstep_logged_run_allowed prims D _ _ o run
  have party := treeSimCheck_phase_replay D A noFunctionality _ _ b.batch.state _ o.1
    replay i honest data present
  obtain ⟨_, _, party⟩ := party.option_bind_inv _ _ _
  unfold treeSimCheckBatchPrefix at party
  obtain ⟨inputs, _, party⟩ := party.option_bind_inv _ _ _
  obtain ⟨p, prefixRun, _⟩ := party.option_bind_inv _ _ _
  apply beforeVerify_cached prims K D o.2.1
    (treeSimCheckPartyAllowed (E := E) (G := RealSpec)
      (fun t u => TreeLockstepWorldStreams prims D o.2.1 (.inr t) u))
    (fun _ _ h => h) (b.batch.ctx i) settings.mode _ inputs _ p.1 p.2
    (by simpa only [parameters i] using positive) prefixRun

set_option maxRecDepth 2000 in
/-- The fixed live source has a positive-width output rerandomization before the checkpoint. -/
theorem source_outputs_positive (prims : Primitives) (K : Constants C E)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (x : C.Party → Keys C) (z : Aux) (j : Fin (treeBatches settings tree))
    (Z : Distinguisher C A.State TreeOutput) (step : ℕ)
    (setup : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (c : (TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x j.val Z step setup).β)
    (o : TreeCheckTailCheckpoint A) (r : TreeCheckTailResult A)
    (run : r ∈ support (((TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x j.val Z step setup).cut
      prims K circuits settings D Z).cont (.inl (c, o))))
    (bad : TreeCheckBranchBad prims K circuits settings top tree D A x z j r) :
    let b := (TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x j.val Z step setup).boundary c
    0 < (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length := by
  obtain ⟨_, parameter, seeds, pairs, i, value, records, hash, before, batch, after,
    dealt, hi, result, _, _, listed, index, _, wrong, reference⟩ := bad.2
  obtain ⟨prss, valid⟩ := reference.records prims K circuits settings top tree D A parameter seeds
    pairs z r.2 hash i hi value records
  obtain ⟨context, valid⟩ := valid batch (by simp [listed])
  have parameterEq : batch.ctx.keys.parameter = parameter := by rw [context]; rfl
  have positive := incorrect_outputs_positive prims K circuits settings valid hash seeds
    (by simpa only [parameterEq] using wrong)
  obtain ⟨fuel, pref, audited, dealer, out, room, hpref, _, replay, accepted, _, _, hashes⟩ := reference
  let record : TreeCheckIndexedRecord prims circuits D A x j.val r :=
    ⟨parameter, seeds, pairs, i, value, records, hash, batch, pref, dealt, hi, result,
      by simp [listed, index], hpref, hashes, wrong⟩
  have metadata := TreeCheckWalkRecipe.sourceWalk_indexed_metadata prims K D A circuits settings top tree x j.val Z step
    setup c o r run record
  dsimp only
  rw [metadata.2.1, metadata.2.2]
  simpa only [record, parameterEq] using positive

/-- Derived keys read by honest draws of known terms and honest-corrupt pairs. -/
def UsedKeysCached (D : C.Coalition) (prss : C.Party → PrssKeys C) (cache : HashCache C) : Prop :=
  (∀ T, KnownTo D.1 T → ∃ derived,
    cache (.streamKey (TreeCheckWalkRecipe.streamKey D prss (.term T))) = some derived) ∧
  (∀ i j, i ∉ D.1 → j ∈ D.1 → ∀ ne : i ≠ j, ∃ derived,
    cache (.streamKey (TreeCheckWalkRecipe.streamKey D prss (.pair (C.pairOf i j ne)))) = some derived)

/-- Setup rows, common held term keys, and the actual cached keys of honest draws. -/
structure CheckpointFacts (D : C.Coalition) (setup : C.Party → Option (PrssKeys C))
    (cache : HashCache C) : Prop where
  present : ∀ i, i ∉ D.1 → (setup i).isSome
  agree : ∀ i k, i ∉ D.1 → k ∉ D.1 → ∀ T, i ∈ C.holders T → k ∈ C.holders T →
    (TreeCheckWalkRecipe.setupKeys setup i).term T = (TreeCheckWalkRecipe.setupKeys setup k).term T
  cached : UsedKeysCached D (TreeCheckWalkRecipe.setupKeys setup) cache

set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
/-- Every live checkpoint of the fixed source has the exact setup and stream-key prerequisites. -/
theorem source_facts (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (batchSize : 0 < settings.batchSize) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))
    (step : ℕ) (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (dealt : DealtInputs D x) (setup : p ∈ support (treeSaltSetup prims D A x z))
    (c : (TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x j.val Z step p).β)
    (o : TreeCheckTailCheckpoint A)
    (pre : (.inl (c, o) : ((TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x
      j.val Z step p).cut prims K circuits settings D Z).σ) ∈ support
      ((TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x j.val Z step p).cut
        prims K circuits settings D Z).pre)
    (live : ((TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x j.val Z step p).cut
      prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j (.inl (c, o))) :
    CheckpointFacts D p.1.2 o.2.1.1 := by
  let W := TreeCheckWalkRecipe.sourceWalk prims K D A circuits settings top tree x j.val Z step p
  let b := W.boundary c
  have split := TreeCheckWalkRecipe.sourceWalk_split prims K D A circuits settings top tree x j.val Z
    step z p dealt setup
  let checkpoint : (W.cut prims K circuits settings D Z).σ := Sum.inl (c, o)
  have rows : ∀ i, i ∉ D.1 → (p.1.2 i).isSome := by
    with_reducible exact (live_setup_all prims K circuits settings batchSize top tree D A x z Z j
      W p split checkpoint pre live)
  have good : ¬ TreeSimHashBudgetCollision p.2.2 := by
    with_reducible exact (setup_good prims K circuits settings top tree D A x z Z j step p c o pre live)
  refine ⟨rows, setupKeys_term_agree prims D A x z p setup good rows, ?_⟩
  obtain ⟨r, run, bad, counted⟩ := live
  have positive : 0 < (outputsOf (b.batch.jobs.map (circuits b.batch.parameter ·.kind))).length := by
    with_reducible exact (source_outputs_positive prims K D A circuits settings top tree x z j Z step p c o r run bad)
  have preRun : o ∈ support (b.pre prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre
      (prims := prims) (K := K) (circuits := circuits) (settings := settings) (D := D) (A := A) (Z := Z)
      (W := W) (c := c) (o := o) pre)
  have parameters i : (b.batch.ctx i).keys.parameter = b.batch.parameter := by
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    change (x i).parameter = (x (refHolder D K.publicTerm)).parameter
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl
  obtain ⟨_, _, _, _, i, value, records, _, _, _, _, _, _, result, _⟩ := bad.2
  change r ∈ support (treeCheckBatchCont prims K circuits D A Z b.batch o) at run
  have present : ∀ i, i ∉ D.1 → (o.1.2 i).isSome := by
    with_reducible exact (treeCheckBatch_live prims K circuits D A Z b.batch o r run
      ⟨i, (value, records), result⟩)
  have keys (i : C.Party) (hi : i ∉ D.1) :
      (∀ T, (b.batch.ctx i).self ∈ C.holders T → KnownTo D.1 T →
        ∃ derived, o.2.1.1 (.streamKey ((b.batch.ctx i).prss.term T)) = some derived) ∧
      (∀ j, j ≠ (b.batch.ctx i).self → j ∈ D.1 →
        ∃ derived, o.2.1.1 (.streamKey ((b.batch.ctx i).prss.pair j)) = some derived) := by
    obtain ⟨data, row⟩ := Option.isSome_iff_exists.mp (present i hi)
    exact boundary_cached prims K circuits settings D A b parameters o preRun positive i hi data row
  constructor
  · intro T known
    have answer := (keys (refHolder D T) (refHolder_spec D T).2).1 T (refHolder_spec D T).1 known
    exact answer
  · intro i j hi hj ne
    rw [TreeCheckWalkTransport.streamKey_pair D (TreeCheckWalkRecipe.setupKeys p.1.2) i j ne hi hj]
    exact (keys i hi).2 j ne.symm hj

set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
/-- The same prerequisites hold at every live checkpoint of A35's frozen family. -/
theorem checkpointFacts (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) :
    TreeCheckWalkRecipe.AtWalk prims K circuits settings fun top tree D A x z Z _ _ j p W =>
      ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
        (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j (.inl (c, o)) →
        CheckpointFacts D p.1.2 o.2.1.1 := by
  intro hb top tree D A x z Z q dealt bounded small j p setup c o pre live
  with_reducible exact (source_facts prims K circuits settings hb top tree D A x z Z j
    (TreeCheckQueryBudget.ofBound bounded).step p dealt setup c o pre live)

/-- The real check kernel retains all suspended continuations and both logged caches. -/
abbrev KernelState (A : Adversary C E (Keys C) PEmpty PEmpty) :=
  (A.State × (C.Party → Step C E RealSpec (TreeOutput × List (TreeSimCheckBatchRecord C)))) × TreeSimState C

def checkKernel (prims : Primitives) (K : Constants C E) (circuits : Circuits) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (rounds : ℕ)
    (b : TreeCheckBatchBoundary A) (o : TreeCheckTailCheckpoint A) : ProbComp (KernelState A) := do
  let next ← (simulateQ (treeSimLoggedWorld prims D)
    (free (Concrete.sequenceFin fun i => continueStep
      (fun p => treeSimCheckBatchFinish K circuits (b.ctx i) b.jobs b.initial p >>= b.k i)
      (.done (o.1.2 i))))).run o.2
  (simulateQ (treeSimLoggedWorld prims D)
    (executeSteps worldRoles D A noFunctionality rounds o.1.1 next.1)).run next.2

/-- The original scheduler and observer resume the retained real kernel verbatim. -/
def kernelTail (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Z : Distinguisher C A.State TreeOutput)
    (fuel : ℕ) (saved : KernelState A) : ProbComp (TreeCheckTailResult A) := do
  let out ← (simulateQ (treeSimLoggedWorld prims D)
    (executeRounds worldRoles D A noFunctionality fuel saved.1.1 saved.1.2)).run saved.2
  treeCheckObserve prims D A Z out

omit [Fintype E] [DecidableEq E] in
/-- Exact composition of the fixed kernel and the unchanged remainder. -/
theorem checkKernel_split (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (rounds : ℕ) (b : TreeCheckBatchBoundary A)
    (room : rounds ≤ b.fuel) (o : TreeCheckTailCheckpoint A) :
    treeCheckBatchCont prims K circuits D A Z b o =
      checkKernel prims K circuits D A rounds b o >>= kernelTail prims D A Z (b.fuel - rounds) := by
  have split (state : A.State) (steps : C.Party → Step C E RealSpec
      (TreeOutput × List (TreeSimCheckBatchRecord C))) :
      executeRounds worldRoles D A noFunctionality b.fuel state steps =
        executeSteps worldRoles D A noFunctionality rounds state steps >>= fun saved =>
          executeRounds worldRoles D A noFunctionality (b.fuel - rounds) saved.1 saved.2 := by
    simpa only [Nat.add_sub_of_le room] using
      executeRounds_add worldRoles D A noFunctionality rounds (b.fuel - rounds) state steps
  simp only [treeCheckBatchCont, checkKernel, split, simulateQ_bind, StateT.run_bind, bind_assoc]
  rfl

-- These two private abort-persistence proofs are from TreeSimCheck.
omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem treeSimCheck_step_done {I O L R Ia α : Type}
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (r : A.State × (C.Party → Step C E (CallSpec I O) α) ×
      (C.Party → C.Party → Option (Msg E)))
    (h : r ∈ support (stepRound worldRoles D A F state steps))
    (i : C.Party) (a : Option α) (hi : steps i = .done a) : r.2.1 i = .done a := by
  classical
  unfold stepRound at h
  split_ifs at h with hc
  all_goals
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at h
    obtain ⟨p, _, next, hn, rfl⟩ := h
    have hh := mem_support_sequenceFin_oc _ next hn i
    simpa only [hi, support_pure, Set.mem_singleton_iff] using hh

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
private theorem treeSimCheck_rounds_done {I O L R Ia α : Type}
    (D : C.Coalition) (A : Adversary C E Ia L R) (F : Functionality C I O L R)
    (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E (CallSpec I O) α)
    (out : A.State × (C.Party → Option α))
    (h : out ∈ support (executeRounds worldRoles D A F fuel state steps))
    (i : C.Party) (a : Option α) (hi : steps i = .done a) : out.2 i = a := by
  classical
  induction fuel generalizing state steps out with
  | zero =>
    simp only [executeRounds, support_pure, Set.mem_singleton_iff] at h
    subst out
    exact congrArg Step.output hi
  | succ fuel ih =>
    simp only [executeRounds] at h
    split_ifs at h with hd
    · cases h
      exact congrArg Step.output hi
    · simp only [support_bind, Set.mem_iUnion] at h
      obtain ⟨r, hr, ho⟩ := h
      exact ih r.1 r.2.1 out ho (treeSimCheck_step_done D A F state steps r hr i a hi)

omit [Fintype E] [DecidableEq E] in
/-- A future indexed bad output requires an honest kernel step that has not aborted. -/
theorem tail_bad_kernel (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))
    (fuel : ℕ) (saved : KernelState A) (r : TreeCheckTailResult A)
    (run : r ∈ support (kernelTail prims D A Z fuel saved))
    (bad : TreeCheckBranchBad prims K circuits settings top tree D A x z j r) :
    ¬ TreeSimHashBudgetCollision saved.2.2 ∧
      ∃ i, i ∉ D.1 ∧ saved.1.2 i ≠ .done none := by
  unfold kernelTail treeCheckObserve at run
  simp only [mem_support_bind_iff, mem_support_pure_iff] at run
  obtain ⟨out, rounds, observed, observation, rfl⟩ := run
  have before := (treeSimLoggedWorld_prefix prims D _ saved.2 out rounds).trans
    (treeSimLoggedWorld_prefix prims D _ out.2 observed observation)
  refine ⟨fun collision => bad.1 (treeSimHashBudgetCollision_mono before collision), ?_⟩
  obtain ⟨_, _, _, _, i, value, records, _, _, _, _, _, honest, accepted, _⟩ := bad.2
  refine ⟨i, honest, ?_⟩
  intro aborted
  have none := treeSimCheck_rounds_done D A noFunctionality fuel saved.1.1 saved.1.2 out.1
    (treeCheck_logged_support prims D _ _ rounds) i none aborted
  rw [none] at accepted
  cases accepted

/-- The exact frozen hybrid computation whose event is `TreeCheckHybrid.event`. -/
def hybridKernel (prims : Primitives) (K : Constants C E) (D : C.Coalition) (h : TreeCheckHybrid C E) :
    ProbComp ((h.adversary.State × (C.Party → Option Unit)) × HashCache C) :=
  letI : SampleableType E := SampleableType.ofFintype E
  (simulateQ (localAnswer prims)
    (executePhase localRoles D h.adversary (checkFunctionalities K) (checkRounds h.counts.sum)
      h.state (fun i => (check K (localContext i) (hybridCheckGadgets K i) (h.tuples i)).run'
        ⟨filledHistory K i (h.tuples i), h.label, h.tag⟩))).run h.cache

/-- A clean real kernel retains each possible future accepter in the fixed hybrid.
The real marginal includes its complete adversary state, pending programs, caches and log. -/
def KernelRelation (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (h : TreeCheckHybrid C E) (saved : KernelState A)
    (out : (h.adversary.State × (C.Party → Option Unit)) × HashCache C) : Prop :=
  ¬ TreeSimHashBudgetCollision saved.2.2 →
    ∀ i, i ∉ D.1 → saved.1.2 i ≠ .done none →
      ¬ CacheHasCollision (splitRegionCache TreeSimHashDomain out.2) ∧ out.1.2 i = some ()

/-- The kernel relation pays for the unchanged complete continuation's indexed bad event. -/
theorem transport_of_kernel (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))
    (rounds : ℕ) (b : TreeCheckBatchBoundary A) (o : TreeCheckTailCheckpoint A)
    (h : TreeCheckHybrid C E) (room : rounds ≤ b.fuel)
    (coupling : RelTriple (checkKernel prims K circuits D A rounds b o) (hybridKernel prims K D h)
      (KernelRelation D A h)) :
    Pr[fun r => TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
        ¬ TreeCheckUncounted D r.2 | treeCheckBatchCont prims K circuits D A Z b o] ≤ h.event prims K D := by
  rw [checkKernel_split prims K circuits D A Z rounds b room o]
  let event := fun saved : KernelState A => ¬ TreeSimHashBudgetCollision saved.2.2 ∧
    ∃ i, i ∉ D.1 ∧ saved.1.2 i ≠ .done none
  have cut : Pr[fun r => TreeCheckBranchBad prims K circuits settings top tree D A x z j r ∧
        ¬ TreeCheckUncounted D r.2 |
      checkKernel prims K circuits D A rounds b o >>= kernelTail prims D A Z (b.fuel - rounds)] ≤
      Pr[event | checkKernel prims K circuits D A rounds b o] := by
    refine probEvent_bind_le_probEvent fun saved _ noEvent => probEvent_eq_zero fun r run bad => noEvent ?_
    exact tail_bad_kernel prims K circuits settings top tree D A x z Z j _ saved r run bad.1
  refine cut.trans ?_
  apply probEvent_le_of_relTriple coupling
  intro saved out related accepted
  obtain ⟨good, i, honest, active⟩ := accepted
  obtain ⟨cacheGood, result⟩ := related good i honest active
  exact ⟨cacheGood, i, honest, result⟩

/-- Coupling of the fixed real check kernel and the fixed GS20 adapter only.
The real kernel stops after the check's mandatory rounds and retains its exact
suspended continuation, adversary state, hash cache, hidden cache, and log.
The scheduler includes local work up to its next suspension. The later rounds,
remaining batches, and distinguisher are outside this obligation. -/
def CheckKernelCoupling (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) : Prop :=
  TreeCheckWalkRecipe.AtWalk prims K circuits settings fun top tree D A x z Z _ _ j p W =>
    ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre →
      (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j (.inl (c, o)) →
      CheckpointFacts D p.1.2 o.2.1.1 →
      let b := (W.boundary c).batch
      RelTriple
        (checkKernel prims K circuits D A (2 * halvings (tupleCount (b.jobs.map (circuits b.parameter ·.kind))) + 5) b o)
        (hybridKernel prims K D (W.hybrid c o)) (KernelRelation D A (W.hybrid c o))

set_option linter.constructorNameAsVariable false in
set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4000 in
/-- The whole checkpoint transport follows from the fixed kernel coupling;
with actual setup and cache facts, exact fuel accounting, and the original continuation. -/
theorem walkCheckpointTransport_of_checkKernelCoupling (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (coupling : CheckKernelCoupling prims K circuits settings) :
    TreeCheckWalkTransport.WalkCheckpointTransport prims K circuits settings := by
  have allFacts := checkpointFacts prims K circuits settings
  dsimp only [TreeCheckWalkRecipe.AtWalk] at allFacts
  dsimp only [CheckKernelCoupling, TreeCheckWalkRecipe.AtWalk] at coupling
  intro hb top tree D A x z Z q dealt bounded small j p setup s pre live c o same
  with_reducible subst s
  let W := TreeCheckWalkRecipe.family prims K circuits settings top tree D A x Z q bounded j p
  let b := W.boundary c
  have facts : CheckpointFacts D p.1.2 o.2.1.1 := by
    with_reducible exact (allFacts hb top tree D A x z Z q dealt bounded small
      j p setup c o pre live)
  have coupled : RelTriple
      (checkKernel prims K circuits D A
        (2 * halvings (tupleCount (b.batch.jobs.map (circuits b.batch.parameter ·.kind))) + 5) b.batch o)
      (hybridKernel prims K D (W.hybrid c o)) (KernelRelation D A (W.hybrid c o)) := by
    with_reducible exact (coupling hb top tree D A x z Z q dealt bounded small j p setup c o pre live facts)
  obtain ⟨r, run, bad, counted⟩ := live
  have nonzero : tupleCount (b.batch.jobs.map (circuits b.batch.parameter ·.kind)) ≠ 0 := by
    with_reducible exact (TreeCheckWalkPositions.source_count_ne_zero prims K D A circuits settings
      top tree x z j Z (TreeCheckQueryBudget.ofBound bounded).step p c o r run bad)
  have preRun : o ∈ support (b.pre prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre
      (prims := prims) (K := K) (circuits := circuits) (settings := settings) (D := D) (A := A) (Z := Z)
      (W := W) (c := c) (o := o) pre)
  have self i : (b.batch.ctx i).self = i := rfl
  have parameters i : (b.batch.ctx i).keys.parameter = b.batch.parameter := by
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    change (x i).parameter = (x (refHolder D K.publicTerm)).parameter
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl
  change r ∈ support (treeCheckBatchCont prims K circuits D A Z b.batch o) at run
  obtain ⟨_, _, _, _, i, value, records, _, _, _, _, _, _, accepted, _⟩ := bad.2
  have room := TreeCheckWalkPositions.batchCont_fuel prims K circuits settings D A Z b self parameters
    o preRun r run ⟨i, (value, records), accepted⟩ nonzero
  exact transport_of_kernel prims K circuits settings top tree D A x z Z j _ b.batch o
    (W.hybrid c o) room coupled

end ThresholdLeanXmssSecurity.TreeCheckWalkCoupling

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCoupling.setupKeys_term_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCoupling.setupKeys_term_agree

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCoupling.live_setup_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCoupling.live_setup_all

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCoupling.checkpointFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCoupling.checkpointFacts

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCoupling.checkKernel_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCoupling.checkKernel_split

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkCoupling.walkCheckpointTransport_of_checkKernelCoupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckWalkCoupling.walkCheckpointTransport_of_checkKernelCoupling
