import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutCheck.Walks

/-!
# The tuple inputs at the cut of one ceremony

`ceremonyTupleInputs` proves `CeremonyTupleInputs` in three steps.

`ceremonyTupleInputs_of_cutHeads` states that `CutHeads` gives `CeremonyTupleInputs`. `CutHeads`
states that the honest tuples at a joint start are `batchTuples` of one job list with agreeing input
sharings, and that each AND layer and `Rerand` is one reshare run of the honest operators. Then
`tupleInputs_batchTuples` gives `TupleInputs`, which reads the honest tuples only
(`tupleInputs_congr`).

`cutHeads_of_ghostHeads` states that `GhostHeads` gives `CutHeads`. The prefix of the cut has the
law of the recorded prefix on the stops (`Joint.view1_eq_prefix`), so each honest stop is the start
of the check of a recorded head. The heads have the mode and the circuits of batch `k`
(`recPrefix_shape`) and agreeing input sharings (`ghost_inputsAgree`). `GhostHeads` states that the
AND layers and `Rerand` of the recorded heads are reshare runs.

`ghostHeads_of_walks` states that `HeadReach` and `HeadDraws` give `GhostHeads`. The self-recorded
prefix (`preGhost`) has the outputs and the world of the recorded prefix (`selfPhase_exists`). The
lock step at the last round of each reshare (`selfPhase_round`) gives the delivered messages, and the
walk of the reads of `PRG` puts the draws into the end world. The randomness of each reshare run is
read from the stream cells of the end world (`cellDraws`, `drawn_of_cells`), which the reshares read
only at the positions with no filler (`reshare_congr`, `collector_congr`).
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

namespace CutBudget

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

open KnownTupleInputs

/-- The heads of the honest stops at a cut. At each joint start of a check on the support of the
prefix from a ready start, with no global event and agreeing PRSS keys, the honest tuples are
`batchTuples` of one job list in one mode from one label, with agreeing input sharings, and each AND
layer and `Rerand` of the batch is one reshare run under the PRSS keys of the start. -/
def CutHeads : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (rounds : ℕ) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    ∀ k < (chunks settings.batchSize c.jobs).length,
    ∀ z ∈ support ((ceremonyPrefix prims K circuits settings D net rounds k c).run world), ∀ start,
      jointStop D z.1 z.2 = some start → ¬ GlobalEvent z.2 → PrssKeysAgree D start.prss →
        ∃ (mode : ReshareMode) (jobs : List Circuit) (L : ℕ) (w : HashCache C × HiddenCache C)
          (inputs : C.Party → List (C.Term → List Bit)) (zs : C.Party → ℕ → Shares C Bit)
          (v' : C.Party → Shares C Bit),
          (∀ i, i ∉ D.1 → start.x i = batchTuples K mode jobs (inputs i) (zs i) (v' i)) ∧ InputsAgree D inputs ∧
          (∀ l < depth jobs, ReshareRun prims D K mode start.prss (L + l) (gatesAt jobs l).length w fun i => zs i l) ∧
          ReshareRun prims D K .peer start.prss (L + depth jobs) (outputsOf jobs).length w v'

omit [Fintype E] [DecidableEq E] in
/-- `TupleInputs` reads the tuples of the honest operators only. -/
theorem tupleInputs_congr {counts : List ℕ} {D : C.Coalition} {x y : C.Party → List (Tuple C)}
    (hxy : ∀ i, i ∉ D.1 → x i = y i) (h : TupleInputs K counts D x) : TupleInputs K counts D y := by
  obtain ⟨hcount, hmode, hcons⟩ := h
  refine ⟨fun i hi => hxy i hi ▸ hcount i hi, fun i j hi hj => hxy i hi ▸ hxy j hj ▸ hmode i j hi hj,
    fun T hT => ?_⟩
  have hx := hcons T fun i hiT j hjT hi hj => by
    have := hT i hiT j hjT hi hj
    dsimp only at this ⊢
    rwa [← hxy i hi, ← hxy j hj] at this
  intro i hiT j hjT hi hj
  have := hx i hiT j hjT hi hj
  dsimp only at this ⊢
  rwa [hxy i hi, hxy j hj] at this

omit [Fintype E] [DecidableEq E] in
/-- `CeremonyTupleInputs` from the heads of the honest stops. -/
theorem ceremonyTupleInputs_of_cutHeads (heads : CutHeads prims K circuits settings) :
    CeremonyTupleInputs prims K circuits settings := by
  intro D net rounds ℓ c world hready k hk z hz start hjoint hglobal hkeys
  obtain ⟨mode, jobs, L, w, inputs, zs, v', hx, hinputs, hlayers, hrerand⟩ :=
    heads D net rounds ℓ c world hready k hk z hz start hjoint hglobal hkeys
  have h := tupleInputs_congr K (fun i hi => (hx i hi).symm)
    (tupleInputs_batchTuples prims D K hkeys mode jobs L w inputs zs v' hinputs hlayers hrerand)
  obtain ⟨-, j, hj, -, -, hcounts, hxs, -⟩ := Joint.jointStop_some D _ _ start hjoint
  have hlead : start.counts = headCounts jobs := by
    rw [hcounts, ← h.1 j hj, hxs]
  rw [hlead]
  exact h

/-! ## The heads on the recorded prefix -/

omit [Fintype E] [DecidableEq E] in
/-- The head of a recorded batch has the mode of the settings and the circuits of its jobs. -/
theorem recHead_shape (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) (st : ℕ × ℕ)
    (z : Option ((BatchStart C × ℕ) × (ℕ × ℕ)) × Record C E)
    (hz : z ∈ support ((recHead K circuits settings ctx parameter jobs).run st).run.run) (d : (BatchStart C × ℕ) × (ℕ × ℕ))
    (hd : z.1 = some d) :
    d.1.1.mode = settings.mode ∧ d.1.1.circuits = jobs.map (circuits parameter ·.kind) := by
  obtain ⟨L, k⟩ := st
  simp only [recHead, StateT.run_bind, StateT.run_get, pure_bind, RecM.liftS, StateT.run_mk, StateT.run_lift] at hz
  rcases BatchCounters.mem_support_lift_bind _ _ z hz with rfl | ⟨p, -, h₂⟩
  · cases hd
  rcases BatchCounters.mem_support_lift_bind _ _ _ h₂ with rfl | ⟨p₁, -, h₃⟩
  · cases hd
  rcases BatchCounters.mem_support_lift_bind _ _ _ h₃ with rfl | ⟨p₂, -, h₄⟩
  · cases hd
  simp only [StateT.run_pure, OptionT.run_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at h₄
  subst h₄
  cases hd
  exact ⟨rfl, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- The head of the recorded prefix up to the check of batch `k` has the mode of the settings and the
circuits of batch `k` under the parameter of the keys. -/
theorem recPrefix_shape (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job) (st : ℕ × ℕ)
    (z : Option (Joint.PreOut C) × Record C E)
    (hz : z ∈ support ((recPrefix K circuits settings k i keys jobs).run st).run.run) (d : Joint.PreOut C)
    (hd : z.1 = some d) :
    d.1.2.2.1.mode = settings.mode ∧
      d.1.2.2.1.circuits = ((chunks settings.batchSize jobs).getD k []).map (circuits keys.parameter ·.kind) := by
  unfold recPrefix at hz
  simp only [StateT.run_bind] at hz
  obtain ⟨z₁, -, ⟨-, rfl⟩ | ⟨a, -, z₂, h₂, rfl⟩⟩ := mem_support_recM_bind _ _ z hz
  · cases hd
  obtain ⟨z₃, -, ⟨-, rfl⟩ | ⟨a₃, -, z₄, h₄, rfl⟩⟩ := mem_support_recM_bind _ _ z₂ h₂
  · cases hd
  obtain ⟨z₅, h₅, ⟨-, rfl⟩ | ⟨a₅, ha₅, z₆, h₆, rfl⟩⟩ := mem_support_recM_bind _ _ z₄ h₄
  · cases hd
  simp only [StateT.run_pure, OptionT.run_pure, WriterT.run_pure, support_pure, Set.mem_singleton_iff] at h₆
  subst h₆
  cases hd
  exact recHead_shape K circuits settings _ _ _ _ z₅ h₅ a₅ ha₅

/-! ## The input sharings of the heads -/

include prims in
/-- The head of the recorded prefix with `H` fixed to `h` has the input sharings `batchInputs` of
batch `k` with the seed of the keys. -/
theorem recPrefix_fix_inputs (h : Query C → HashOutput) (k : ℕ) (i : C.Party) (keys : Keys C) (jobs : List Job)
    (st : ℕ × ℕ) (z : Option (Joint.PreOut C) × Record C E)
    (hz : z ∈ support (simulateQ (fixHash h) ((recPrefix K circuits settings k i keys jobs).run st).run.run))
    (d : Joint.PreOut C) (hd : z.1 = some d) :
    d.1.2.2.1.inputs = batchInputs h keys.seed ((chunks settings.batchSize jobs).getD k []) i := by
  unfold recPrefix at hz
  simp only [StateT.run_bind] at hz
  obtain ⟨z₁, -, ⟨-, rfl⟩ | ⟨a, -, z₂, h₂, rfl⟩⟩ := GhostBatch.mem_support_fix_bind h _ _ z hz
  · cases hd
  obtain ⟨z₃, -, ⟨-, rfl⟩ | ⟨a₃, -, z₄, h₄, rfl⟩⟩ := GhostBatch.mem_support_fix_bind h _ _ z₂ h₂
  · cases hd
  obtain ⟨z₅, h₅, ⟨-, rfl⟩ | ⟨a₅, ha₅, z₆, h₆, rfl⟩⟩ := GhostBatch.mem_support_fix_bind h _ _ z₄ h₄
  · cases hd
  simp only [StateT.run_pure, OptionT.run_pure, WriterT.run_pure, simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at h₆
  subst h₆
  cases hd
  simp only [recHead, StateT.run_bind, StateT.run_get, pure_bind, RecM.liftS, StateT.run_mk,
    StateT.run_lift] at h₅
  rcases GhostBatch.mem_support_fix_lift_bind h _ _ z₅ h₅ with rfl | ⟨p, hp, h₇⟩
  · cases ha₅
  rcases GhostBatch.mem_support_fix_lift_bind h _ _ _ h₇ with rfl | ⟨p₁, -, h₈⟩
  · cases ha₅
  rcases GhostBatch.mem_support_fix_lift_bind h _ _ _ h₈ with rfl | ⟨p₂, -, h₉⟩
  · cases ha₅
  simp only [StateT.run_pure, OptionT.run_pure, WriterT.run_pure, simulateQ_pure, support_pure,
    Set.mem_singleton_iff] at h₉
  subst h₉
  cases ha₅
  exact (holds_bind h _ (fun q : List (C.Term → List Bit) × (ℕ × ℕ) =>
      q.1 = batchInputs h keys.seed ((chunks settings.batchSize jobs).getD k []) i) _ _
    (GhostBatch.holds_inputs h prims ⟨i, keys, a.1⟩ _) fun a ha => holds_pure h _ _ ha) _ hp p rfl

/-- The input sharings of the honest heads of the recorded prefix agree. With `H` fixed to a good
function that agrees with the clean end cache, each honest head has the input sharings `batchInputs`
of batch `k` with its seed, and the honest seeds are the seeds of the game. -/
theorem ghost_inputsAgree (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (k a : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C) (hseeds : seedsDiffer D c.keys = false)
    (y1 : (net.State × (C.Party → RStep C E RealSpec (Joint.PreOut C) (Record C E))) × StreamState C)
    (hy1 : y1 ∈ support (Joint.phase1 prims K circuits settings D net k a c world)) (b : C.Party → BatchStart C)
    (hb : ∀ i, i ∉ D.1 → ∃ p : Joint.PreOut C, (y1.1.2 i).output = some p ∧ p.1.2.2.1 = b i) :
    InputsAgree D (fun i => (b i).inputs) := by
  have hclean : (y1.1, MpcCells.cleanWorld y1.2) ∈ support ((simulateQ (streamWorld prims D)
      (executePhaseR worldRoles D net noFunctionality ([] : Record C E) a c.adversary
        fun i => Joint.pre1 K circuits settings k i c)).run (MpcCells.cleanWorld world)) := by
    unfold Joint.phase1 at hy1
    rw [MpcCells.streamWorld_run_clean, support_map]
    exact ⟨y1, hy1, rfl⟩
  have hfix : ∀ i, i ∉ D.1 → (b i).inputs = batchInputs (hashOf prims (MpcCells.cleanCache y1.2.1))
      (gameSeeds D c.keys) ((chunks settings.batchSize c.jobs).getD k []) i := by
    intro i hi
    obtain ⟨p, hp, hbp⟩ := hb i hi
    rw [← hbp]
    have hpath := executePhaseR_onPathRH prims D D net ([] : Record C E) a c.adversary
      (fun i => Joint.pre1 K circuits settings k i c) _ _ hclean _ (good_hashOf prims _)
      (agrees_hashOf prims (MpcCells.noMpc_cleanCache _)) i hi
    rcases hs : y1.1.2 i with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩
    · rw [hs] at hp hpath
      change out = some p at hp
      subst hp
      have hmem := CeremonyRecords.onPath_done hpath
      cases hkeys : c.keys i with
      | none =>
        simp only [Joint.pre1, hkeys, simulateQ_pure, support_pure, Set.mem_singleton_iff] at hmem
        cases hmem
      | some keys =>
        simp only [Joint.pre1, hkeys] at hmem
        rw [recPrefix_fix_inputs prims K circuits settings _ k i keys c.jobs c.counters _ hmem p rfl]
        exact batchInputs_congr _ _ _ _ _ fun T hT =>
          seed_eq_gameSeeds D c.keys hseeds i hi keys hkeys T hT
    · rw [hs] at hp
      cases hp
    · exact input.elim
  refine ⟨fun i j hi hj => ?_, fun m T i hiT j hjT hi hj => ?_⟩
  · show (b i).inputs.length = (b j).inputs.length
    rw [hfix i hi, hfix j hj]
    simp [batchInputs]
  dsimp only
  rw [hfix i hi, hfix j hj]
  generalize (chunks settings.batchSize c.jobs).getD k [] = js
  simp only [batchInputs, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases js[m]? with _ | job
  · rfl
  · simp [hiT, hjT]

/-! ## Draws from stream cells -/

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A free read of `PRG` from a world that has its stream cell answers the cell and keeps the world. -/
theorem freeRead_of_cell (D : C.Coalition) (x : PrgInput C) (s : HashCache C × HiddenCache C) (b : Bit)
    (hb : StreamCell prims D x s b) : ∀ z ∈ support ((streamWorld prims D (freeRead x)).run s), z = (b, s) := by
  intro z hz
  by_cases hx : Hidden D x.1
  · simp only [StreamCell, hx, ↓reduceIte] at hb
    simp only [streamWorld, hx, ↓reduceIte, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hb, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    rfl
  · simp only [StreamCell, hx, ↓reduceIte] at hb
    obtain ⟨h, hh, rfl⟩ := hb
    simp only [streamWorld, hx, ↓reduceIte] at hz
    obtain ⟨r, hr, rfl⟩ := mem_support_onHash _ s z hz
    change r ∈ support ((prgAnswer prims x).run s.1) at hr
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, support_bind, support_pure, Set.mem_iUnion,
      Set.mem_singleton_iff] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    rw [hashAnswer_of_not_isFixed prims (by rintro ⟨_, he, _⟩; cases he), OracleSpec.randomOracle,
      QueryImpl.withCaching_run_some _ hh, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Free reads of `PRG` from a world that has all their stream cells answer the cells and keep the
world. -/
theorem readAll_of_cells (D : C.Coalition) (s : HashCache C × HiddenCache C) :
    ∀ (xs : List (PrgInput C)) (bs : List Bit), List.Forall₂ (fun x b => StreamCell prims D x s b) xs bs →
      ∀ z ∈ support ((simulateQ (streamWorld prims D) (readAll xs)).run s), z = (bs, s)
  | [], [], _ => by
    intro z hz
    simp only [readAll, List.mapM_nil, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    exact hz
  | x :: xs, b :: bs, .cons hx hxs => by
    intro z hz
    have e : simulateQ (streamWorld prims D) (query (spec := WorldSpec C) (freeRead x)) =
        streamWorld prims D (freeRead x) := (simulateQ_query _ _).trans (id_map _)
    simp only [readAll, List.mapM_cons, simulateQ_bind, e, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, w, hw, rfl⟩ := hz
    obtain rfl := freeRead_of_cell prims D x s b hx y hy
    obtain rfl := readAll_of_cells D s xs bs hxs w hw
    rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Bits with their stream cells in a world are a free draw below that world. -/
theorem drawn_of_cells (D : C.Coalition) (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ)
    (w : HashCache C × HiddenCache C) (r : ℕ → Bit)
    (hr : ∀ g < count, StreamCell prims D (name, key, ρ, idx, g) w (r g)) :
    Drawn prims D name key ρ idx count w r := by
  have hcells : List.Forall₂ (fun x b => StreamCell prims D x w b)
      ((List.range count).map fun position => (name, key, ρ, idx, position)) ((List.range count).map r) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun g hg => hr g (List.mem_range.1 hg)
  obtain ⟨z, hz⟩ := support_nonempty ((simulateQ (streamWorld prims D) (freeBits name key ρ idx count)).run w)
  refine ⟨w, z, hz, ?_⟩
  rw [freeBits_eq, simulateQ_map, StateT.run_map, support_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain rfl := readAll_of_cells prims D w _ _ hcells y hy
  refine ⟨le_rfl, le_rfl, fun g hg => ?_⟩
  simp [List.getD_eq_getElem?_getD, hg]

/-! ## The reshares read the randomness at the positions with no filler -/

omit [Fintype E] [DecidableEq E] in
/-- A peer reshare reads the randomness only at the held terms with no filler below the count. -/
theorem reshare_congr (ctx : Context C) {r r' : Shares C Bit} (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit) (count : ℕ)
    (h : ∀ T, ctx.self ∈ C.holders T → T ∉ filledTerms K → ∀ g < count, r T g = r' T g) :
    reshareOut K ctx bitCodec r Zs v count = reshareOut K ctx bitCodec r' Zs v count ∧
      ∀ inbox, reshareZ K ctx bitCodec r Zs v count inbox = reshareZ K ctx bitCodec r' Zs v count inbox := by
  have hu : ∀ g < count, reshareU K ctx r Zs v g = reshareU K ctx r' Zs v g := by
    intro g hg
    unfold reshareU
    congr 1
    refine Finset.sum_congr rfl fun T hT => ?_
    obtain ⟨-, hfill, hown⟩ := Finset.mem_filter.1 hT
    exact h T (hown ▸ K.owner_held T) hfill g hg
  have hv : vector count (reshareU K ctx r Zs v) = vector count (reshareU K ctx r' Zs v) :=
    List.map_congr_left fun g hg => hu g (List.mem_range.1 hg)
  refine ⟨funext fun j => by simp only [reshareOut, hv], fun inbox => funext fun T => funext fun g => ?_⟩
  unfold reshareZ
  by_cases hc : ctx.self ∉ C.holders T ∨ count ≤ g
  · simp only [hc, ↓reduceIte]
  · have hT : ctx.self ∈ C.holders T := by tauto
    have hg : g < count := by omega
    simp only [hc, ↓reduceIte]
    split_ifs with hfill
    · refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · exact hu g hg
      · rfl
    · exact h T hT hfill g hg

omit [Fintype E] [DecidableEq E] in
/-- A collector reshare reads the randomness only at the held terms that are not `T*` of their gate,
below the count. -/
theorem collector_congr (i : C.Party) {r r' : Shares C Bit} (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit) (count : ℕ)
    (h : ∀ T, i ∈ C.holders T → ∀ g < count, T ≠ (K.collector g).1 → r T g = r' T g) :
    ∀ inbox, colOut2 K i r Zs v count inbox = colOut2 K i r' Zs v count inbox ∧
      ∀ forward, colZ K i r Zs v count inbox forward = colZ K i r' Zs v count inbox forward := by
  have hu : ∀ g < count, colU K i r Zs v g = colU K i r' Zs v g := by
    intro g hg
    unfold colU
    congr 1
    refine Finset.sum_congr rfl fun T hT => ?_
    obtain ⟨-, hstar, hown⟩ := Finset.mem_filter.1 hT
    exact h T (hown ▸ K.owner_held T) g hg hstar
  intro inbox
  have hs : ∀ g < count, colSum K i r Zs v count inbox g = colSum K i r' Zs v count inbox g := by
    intro g hg
    unfold colSum
    rw [hu g hg]
  refine ⟨funext fun hh => ?_, fun forward => funext fun T => funext fun g => ?_⟩
  · unfold colOut2
    split_ifs
    · congr 2
      refine List.map_congr_left fun g hg => hs g ?_
      simp only [forwardedTo, collectedBy, List.mem_filter, List.mem_range] at hg
      exact hg.1.1
    · rfl
  · unfold colZ
    by_cases hc : i ∉ C.holders T ∨ count ≤ g
    · simp only [hc, ↓reduceIte]
    · have hT : i ∈ C.holders T := by tauto
      have hg : g < count := by omega
      simp only [hc, ↓reduceIte]
      split_ifs with hstar hκ
      · exact hs g hg
      · rfl
      · exact h T hT g hg hstar

/-- The heads of the recorded prefix. Take an outcome of the recorded prefix up to the check of batch
`k` from a ready start, at its exact rounds, and a recorded head `b i` of each honest operator. With
no global event and agreeing PRSS keys of the heads, each AND layer and `Rerand` of the heads, with
the circuits of batch `k`, is one reshare run under the PRSS keys of the heads. -/
def GhostHeads : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (ℓ : StartBudget)
    (c : CeremonyStart C net.State) (world : StreamState C), CeremonyReady D ℓ c world →
    ∀ k < (chunks settings.batchSize c.jobs).length,
    ∀ y1 ∈ support (Joint.phase1 prims K circuits settings D net k
      (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c world),
    ∀ b : C.Party → BatchStart C,
      (∀ i, i ∉ D.1 → ∃ p : Joint.PreOut C, (y1.1.2 i).output = some p ∧ p.1.2.2.1 = b i) →
      ¬ GlobalEvent y1.2 → PrssKeysAgree D (fun i => (b i).ctx.prss) →
        ∃ (L : ℕ) (w : HashCache C × HiddenCache C),
          (∀ l < depth (batchCircuits circuits settings (gameParameter D c.keys) c.jobs k),
            ReshareRun prims D K settings.mode (fun i => (b i).ctx.prss) (L + l)
              (gatesAt (batchCircuits circuits settings (gameParameter D c.keys) c.jobs k) l).length w
              fun i => (b i).zs l) ∧
          ReshareRun prims D K .peer (fun i => (b i).ctx.prss)
            (L + depth (batchCircuits circuits settings (gameParameter D c.keys) c.jobs k))
            (outputsOf (batchCircuits circuits settings (gameParameter D c.keys) c.jobs k)).length w
            fun i => (b i).v'

/-! ## The heads from the walks of one operator -/

omit [Fintype E] [DecidableEq E] in
/-- The recorded prefix with its result as its record has, on the world, the law of the recorded
prefix on the outputs. So each outcome of the recorded prefix has an outcome of the self-recorded
prefix with the same outputs and the same world. -/
theorem selfPhase_exists (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (k a : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C)
    (y1 : (net.State × (C.Party → RStep C E RealSpec (Joint.PreOut C) (Record C E))) × StreamState C)
    (hy1 : y1 ∈ support (Joint.phase1 prims K circuits settings D net k a c world)) :
    ∃ y ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
        (none : Option (Joint.PreOut C)) a c.adversary fun i => preGhost K circuits settings k i c)).run world),
      y.2 = y1.2 ∧ ∀ i, (y.1.2 i).output = (y1.1.2 i).output := by
  have hdrop : (fun i => dropRecord (preGhost K circuits settings k i c)) =
      fun i => dropRecord (Joint.pre1 K circuits settings k i c) := by
    funext i
    simp only [dropRecord, preGhost, Functor.map_map]
  have hlaw := congrArg (fun oa => (simulateQ (streamWorld prims D) oa).run world)
    ((executePhaseR_erase worldRoles (fun g oa => worldRoles_honest_map g oa) D net noFunctionality
      (none : Option (Joint.PreOut C)) a c.adversary fun i => preGhost K circuits settings k i c).symm.trans
      ((congrArg (executePhase worldRoles D net noFunctionality a c.adversary) hdrop).trans
        (executePhaseR_erase worldRoles (fun g oa => worldRoles_honest_map g oa) D net noFunctionality
          ([] : Record C E) a c.adversary fun i => Joint.pre1 K circuits settings k i c)))
  simp only [simulateQ_map, StateT.run_map] at hlaw
  unfold Joint.phase1 at hy1
  have hmem : ((y1.1.1, fun i => (y1.1.2 i).output), y1.2) ∈ support ((fun p :
      (net.State × (C.Party → RStep C E RealSpec (Joint.PreOut C) (Record C E))) × StreamState C =>
        ((p.1.1, fun i => (p.1.2 i).output), p.2)) <$> (simulateQ (streamWorld prims D)
          (executePhaseR worldRoles D net noFunctionality ([] : Record C E) a c.adversary fun i =>
            Joint.pre1 K circuits settings k i c)).run world) := by
    rw [support_map]
    exact ⟨y1, hy1, rfl⟩
  rw [← hlaw, support_map] at hmem
  obtain ⟨y, hy, hye⟩ := hmem
  refine ⟨y, hy, congrArg Prod.snd hye, fun i => ?_⟩
  have h1 := congrArg (fun q => q.1.2 i) hye
  exact h1

omit [Fintype E] [DecidableEq E] in
/-- An honest operator with an output in the self-recorded prefix has keys, and its record is its
output. -/
theorem selfPhase_output (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (k a : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C)
    (y : (net.State × (C.Party → RStep C E RealSpec (Joint.PreOut C) (Option (Joint.PreOut C)))) × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
        (none : Option (Joint.PreOut C)) a c.adversary fun i => preGhost K circuits settings k i c)).run world))
    (i : C.Party) (hi : i ∉ D.1) (p : Joint.PreOut C) (hp : (y.1.2 i).output = some p) :
    (∃ keys, c.keys i = some keys) ∧ (y.1.2 i).record none = some p := by
  have hdone : (y.1.2 i).isDone := by
    cases hs : y.1.2 i with
    | done out record => trivial
    | wait outbox resume => rw [hs] at hp; cases hp
    | call input resume => exact input.elim
  have hmem := Joint.executePhaseR_out_mem D net noFunctionality (none : Option (Joint.PreOut C)) a c.adversary _ y.1
    (mem_support_phase prims D _ world y hy) i hi hdone
  rw [hp] at hmem
  unfold preGhost at hmem
  rw [support_map] at hmem
  obtain ⟨x, hx, hxe⟩ := hmem
  simp only [Prod.mk.injEq] at hxe
  refine ⟨?_, by rw [← hxe.2, hxe.1]⟩
  cases hkeys : c.keys i with
  | none =>
    simp only [Joint.pre1, hkeys, support_pure, Set.mem_singleton_iff] at hx
    rw [hx] at hxe
    cases hxe.1
  | some keys => exact ⟨keys, rfl⟩

omit [Fintype E] [DecidableEq E] in
/-- The lock step at one round of the self-recorded prefix. When each honest operator reaches a wait
in `Q` at the depth `n`, and each honest operator has an output, then each honest operator waits at
one joint round with a wait in `Q`, and its record is a result of the rest on the mail of that
round. -/
theorem selfPhase_round (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (k a : ℕ)
    (c : CeremonyStart C net.State) (world : StreamState C)
    (y : (net.State × (C.Party → RStep C E RealSpec (Joint.PreOut C) (Option (Joint.PreOut C)))) × StreamState C)
    (hy : y ∈ support ((simulateQ (streamWorld prims D) (executePhaseR worldRoles D net noFunctionality
        (none : Option (Joint.PreOut C)) a c.adversary fun i => preGhost K circuits settings k i c)).run world))
    (n : ℕ) (Q : C.Party → List (Query C × HashOutput) → Mail C E →
      (Mail C E → OracleComp (PartySpec C E RealSpec) (Option (Joint.PreOut C) × Option (Joint.PreOut C))) → Prop)
    (hreach : ∀ i, i ∉ D.1 → CachedOpening.ReachH (fun x => x.2 = none) (Q i) n [] (preGhost K circuits settings k i c))
    (hout : ∀ i, i ∉ D.1 → ∃ p, (y.1.2 i).output = some p) :
    ∃ (steps₀ : C.Party → RStep C E RealSpec (Joint.PreOut C) (Option (Joint.PreOut C)))
      (sent : C.Party → C.Party → Option (Msg E)), ∀ i, i ∉ D.1 → ∃ outbox resume,
        steps₀ i = .wait outbox resume ∧ (∃ hist, Q i hist outbox resume) ∧
        ∃ out, (out, (y.1.2 i).record none) ∈ support (resume (LiveRounds.roundInbox D steps₀ sent i)) := by
  have hrec : ∀ i, i ∉ D.1 → ∃ p, (y.1.2 i).record none = some p := fun i hi => by
    obtain ⟨p, hp⟩ := hout i hi
    exact ⟨p, (selfPhase_output prims K circuits settings D net k a c world y hy i hi p hp).2⟩
  rcases CachedOpening.executePhaseR_reachH prims D D net (none : Option (Joint.PreOut C)) (fun _ x => x.2 = none) Q n a
    c.adversary _ hreach world y hy with hstop | ⟨steps₀, sent, cache, -, hsteps, hrest⟩
  · by_cases hex : ∃ i, i ∉ D.1
    · exfalso
      obtain ⟨i, hi⟩ := hex
      obtain ⟨p, hp⟩ := hrec i hi
      rcases hstop i hi with h | ⟨out, h⟩
      · rw [hp] at h
        cases h
      · change (y.1.2 i).record none = none at h
        rw [hp] at h
        cases h
    · exact ⟨fun _ => .done none none, fun _ _ => none, fun i hi => absurd ⟨i, hi⟩ hex⟩
  refine ⟨steps₀, sent, fun i hi => ?_⟩
  obtain ⟨p, hp⟩ := hrec i hi
  obtain ⟨out, hout'⟩ : ∃ out, (out, (y.1.2 i).record none) ∈
      support (LiveRounds.nextR none (steps₀ i) (LiveRounds.roundInbox D steps₀ sent i)) := by
    rcases hrest i hi with h | h
    · rw [hp] at h
      cases h
    · exact h
  have hsi := hsteps i hi
  rcases hs : steps₀ i with ⟨out', r'⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at hsi hout'
  · exfalso
    simp only [LiveRounds.nextR, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout'
    change r' = none at hsi
    rw [hp, hsi] at hout'
    cases hout'.2
  · obtain ⟨hist, -, hq⟩ := hsi
    exact ⟨outbox, resume, rfl, ⟨hist, hq⟩, out, hout'⟩
  · exact input.elim

/-- The draws of a reshare at the label `ρ` from the stream cells of a world. Each held term of an
honest operator reads the cell of its stream at each position, and `0` with no cell. -/
def cellDraws (D : C.Coalition) (prss : C.Party → PrssKeys C) (ρ : ℕ) (w : HashCache C × HiddenCache C) :
    C.Party → Shares C Bit := fun i T g =>
  if h : ∃ bit, StreamCell prims D (.term T, (prss i).term T, ρ, 0, g) w bit then h.choose else 0

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem cellDraws_cell (D : C.Coalition) (prss : C.Party → PrssKeys C) (ρ : ℕ) (w : HashCache C × HiddenCache C)
    (i : C.Party) (T : C.Term) (g : ℕ) (h : ∃ bit, StreamCell prims D (.term T, (prss i).term T, ρ, 0, g) w bit) :
    StreamCell prims D (.term T, (prss i).term T, ρ, 0, g) w (cellDraws prims D prss ρ w i T g) := by
  simp only [cellDraws, h, ↓reduceDIte]
  exact h.choose_spec

omit [Fintype E] [DecidableEq E] in
/-- A peer reshare run from the delivered messages and the outputs of one round, with the stream
cells of its draws in the world `w`. -/
theorem peerRun_of_waits (D : C.Coalition) (prss : C.Party → PrssKeys C) (ρ count : ℕ)
    (w : HashCache C × HiddenCache C) (z : C.Party → Shares C Bit) {α β : Type}
    (steps₀ : C.Party → RStep C E RealSpec α β) (sent : C.Party → C.Party → Option (Msg E))
    (hcell : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → ∀ g < count,
      ∃ bit, StreamCell prims D (.term T, (prss i).term T, ρ, 0, g) w bit)
    (hfree : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → T ∉ filledTerms K → ∀ g < count,
      StreamCell prims D (.term T, (prss i).term T, ρ, 0, g) w (z i T g))
    (hwait : ∀ i, i ∉ D.1 → ∃ (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit),
      (steps₀ i).delivered = reshareOut K (localContext i) bitCodec r Zs v count ∧
      z i = reshareZ K (localContext i) bitCodec r Zs v count (LiveRounds.roundInbox D steps₀ sent i)) :
    PeerRun prims D K prss ρ count w z := by
  choose! r Zs v hdel hz using hwait
  have hagree : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → T ∉ filledTerms K → ∀ g < count,
      r i T g = cellDraws prims D prss ρ w i T g := by
    intro i hi T hT hf g hg
    have h1 : z i T g = r i T g := by
      rw [hz i hi]
      simp [reshareZ, localContext, hT, hf, Nat.not_le.2 hg]
    rw [← h1]
    exact (hfree i hi T hT hf g hg).unique prims D (cellDraws_cell prims D prss ρ w i T g (hcell i hi T hT g hg))
  have hc := fun i (hi : i ∉ D.1) => reshare_congr K (localContext i) (Zs i) (v i) count (hagree i hi)
  refine ⟨cellDraws prims D prss ρ w, Zs, v, fun i => LiveRounds.roundInbox D steps₀ sent i,
    fun i hi T hT => drawn_of_cells prims D _ _ _ _ _ _ _ fun g hg =>
      cellDraws_cell prims D prss ρ w i T g (hcell i hi T hT g hg), fun i j hi hj hji => ?_, fun i hi => ?_⟩
  · simp only [LiveRounds.roundInbox, hj, ↓reduceIte, hdel j hj, (hc j hj).1]
  · rw [hz i hi, (hc i hi).2]

omit [Fintype E] [DecidableEq E] in
/-- A collector reshare run from the delivered forwards and the outputs of its second round, with the
stream cells of its draws in the world `w`. -/
theorem collectorRun_of_waits (D : C.Coalition) (prss : C.Party → PrssKeys C) (ρ count : ℕ)
    (w : HashCache C × HiddenCache C) (z : C.Party → Shares C Bit) {α β : Type}
    (steps₀ : C.Party → RStep C E RealSpec α β) (sent : C.Party → C.Party → Option (Msg E))
    (hcell : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → ∀ g < count,
      ∃ bit, StreamCell prims D (.term T, (prss i).term T, ρ, 0, g) w bit)
    (hfree : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → ∀ g < count, T ≠ (K.collector g).1 →
      StreamCell prims D (.term T, (prss i).term T, ρ, 0, g) w (z i T g))
    (hwait : ∀ i, i ∉ D.1 → ∃ (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit) (inbox : Mail C E),
      (steps₀ i).delivered = colOut2 K i r Zs v count inbox ∧
      z i = colZ K i r Zs v count inbox (LiveRounds.roundInbox D steps₀ sent i)) :
    CollectorRun prims D K prss ρ count w z := by
  choose! r Zs v inbox hdel hz using hwait
  have hagree : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → ∀ g < count, T ≠ (K.collector g).1 →
      r i T g = cellDraws prims D prss ρ w i T g := by
    intro i hi T hT g hg hs
    have h1 : z i T g = r i T g := by
      rw [hz i hi]
      simp [colZ, hT, hs, Nat.not_le.2 hg]
    rw [← h1]
    exact (hfree i hi T hT g hg hs).unique prims D (cellDraws_cell prims D prss ρ w i T g (hcell i hi T hT g hg))
  have hc := fun i (hi : i ∉ D.1) => collector_congr K i (Zs i) (v i) count (hagree i hi) (inbox i)
  refine ⟨cellDraws prims D prss ρ w, Zs, v, inbox, fun i => LiveRounds.roundInbox D steps₀ sent i,
    fun i hi T hT => drawn_of_cells prims D _ _ _ _ _ _ _ fun g hg =>
      cellDraws_cell prims D prss ρ w i T g (hcell i hi T hT g hg), fun i j hi hj hji => ?_, fun i hi => ?_⟩
  · simp only [LiveRounds.roundInbox, hj, ↓reduceIte, hdel j hj, (hc j hj).1]
  · rw [hz i hi, (hc i hi).2]

omit [Fintype E] [DecidableEq E] in
/-- A reshare run in `mode` from one round of the self-recorded prefix where each honest operator
waits at the last round of the reshare, with the stream cells of its draws in the world `w`. -/
theorem reshareRun_of_round (D : C.Coalition) (mode : ReshareMode) (prss : C.Party → PrssKeys C) (ρ count : ℕ)
    (w : HashCache C × HiddenCache C) (z : C.Party → Shares C Bit) (out : BatchStart C → Shares C Bit)
    (steps₀ : C.Party → RStep C E RealSpec (Joint.PreOut C) (Option (Joint.PreOut C)))
    (sent : C.Party → C.Party → Option (Msg E))
    (hcell : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → ∀ g < count,
      ∃ bit, StreamCell prims D (.term T, (prss i).term T, ρ, 0, g) w bit)
    (hfree : ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → ∀ g < count, filler K mode T g = none →
      StreamCell prims D (.term T, (prss i).term T, ρ, 0, g) w (z i T g))
    (hwait : ∀ i, i ∉ D.1 → ∃ outbox resume, steps₀ i = .wait outbox resume ∧
      (∃ hist, ReshareWaitG K mode i count (HeadRel out) hist outbox resume) ∧
      ∃ x p, x ∈ support (resume (LiveRounds.roundInbox D steps₀ sent i)) ∧ x.2 = some p ∧ out p.1.2.2.1 = z i) :
    ReshareRun prims D K mode prss ρ count w z := by
  cases mode with
  | peer =>
    refine peerRun_of_waits prims K D prss ρ count w z steps₀ sent hcell
      (fun i hi T hT hf g hg => hfree i hi T hT g hg ?_) fun i hi => ?_
    · simp only [filler]
      rw [List.find?_eq_none]
      intro j _ hj
      exact hf (Finset.mem_map.2 ⟨j, Finset.mem_univ _, of_decide_eq_true hj⟩)
    · obtain ⟨outbox, resume, hs, ⟨-, r, Zs, v, hob, hres⟩, x, p, hx, hxp, hz⟩ := hwait i hi
      exact ⟨r, Zs, v, by rw [hs, hob]; rfl, by rw [← hz]; exact hres _ x hx p hxp⟩
  | collector =>
    refine collectorRun_of_waits prims K D prss ρ count w z steps₀ sent hcell
      (fun i hi T hT g hg hst => hfree i hi T hT g hg ?_) fun i hi => ?_
    · simp only [filler, Ne.symm hst, ↓reduceIte]
    · obtain ⟨outbox, resume, hs, ⟨-, r, Zs, v, inbox, hob, hres⟩, x, p, hx, hxp, hz⟩ := hwait i hi
      exact ⟨r, Zs, v, inbox, by rw [hs, hob]; rfl, by rw [← hz]; exact hres _ x hx p hxp⟩

omit [Fintype E] [DecidableEq E] in
/-- `GhostHeads` from the walks of one operator. The self-recorded prefix has the outputs and the
world of the recorded prefix (`selfPhase_exists`). Its cell walk (`RerandCells.executePhaseR_holds`)
puts the reads of each reshare into the end world, and its lock step at the last round of each
reshare (`selfPhase_round`) gives the delivered messages. -/
theorem ghostHeads_of_walks (reach : HeadReach K circuits settings) (draws : HeadDraws K circuits settings) :
    GhostHeads prims K circuits settings := by
  intro D net ℓ c world hready k hk y1 hy1 b hb hglobal hkeys
  have hseeds : seedsDiffer D c.keys = false := hready.1
  obtain ⟨y, hy, hworld, houtput⟩ := selfPhase_exists prims K circuits settings D net k _ c world y1 hy1
  have hhead : ∀ i, i ∉ D.1 → ∃ p : Joint.PreOut C, (y.1.2 i).output = some p ∧ p.1.2.2.1 = b i := by
    intro i hi
    obtain ⟨p, hp, hpb⟩ := hb i hi
    exact ⟨p, (houtput i).trans hp, hpb⟩
  have hout : ∀ i, i ∉ D.1 → ∃ p, (y.1.2 i).output = some p := fun i hi => (hhead i hi).imp fun p h => h.1
  have hrec : ∀ i, i ∉ D.1 → ∀ p : Joint.PreOut C, (y.1.2 i).output = some p → (y.1.2 i).record none = some p :=
    fun i hi p hp => (selfPhase_output prims K circuits settings D net k _ c world y hy i hi p hp).2
  have hpre : ∀ i, i ∉ D.1 → preGhost K circuits settings k i c = pure (none, none) ∨
      ∃ keys, c.keys i = some keys ∧ keys.parameter = gameParameter D c.keys := by
    intro i hi
    cases hkeysI : c.keys i with
    | none =>
      left
      simp [preGhost, Joint.pre1, hkeysI]
    | some keys => exact Or.inr ⟨keys, rfl, parameter_eq_gameParameter D c.keys hseeds i hi keys hkeysI⟩
  have hreachAll : ∀ i, i ∉ D.1 →
      (∀ l < depth (batchCircuits circuits settings (gameParameter D c.keys) c.jobs k),
        CachedOpening.ReachH (fun x => x.2 = none)
          (ReshareWaitG K settings.mode i
            (gatesAt (batchCircuits circuits settings (gameParameter D c.keys) c.jobs k) l).length
            (HeadRel fun b => b.zs l))
          (headStart circuits settings (gameParameter D c.keys) c.jobs k + l * settings.mode.rounds +
            (settings.mode.rounds - 1)) [] (preGhost K circuits settings k i c)) ∧
      CachedOpening.ReachH (fun x => x.2 = none)
        (PeerWaitG K i (outputsOf (batchCircuits circuits settings (gameParameter D c.keys) c.jobs k)).length
          (HeadRel fun b => b.v'))
        (headStart circuits settings (gameParameter D c.keys) c.jobs k +
          depth (batchCircuits circuits settings (gameParameter D c.keys) c.jobs k) * settings.mode.rounds)
        [] (preGhost K circuits settings k i c) := by
    intro i hi
    rcases hpre i hi with h | ⟨keys, hkeysI, hpar⟩
    · rw [h]
      exact ⟨fun l _ => CachedOpening.ReachH.early _ _ _ rfl, CachedOpening.ReachH.early _ _ _ rfl⟩
    · have h := reach k i c keys hkeysI hk
      rw [hpar] at h
      exact h
  have hholds : ∀ i, i ∉ D.1 → RerandCells.Holds (fun hist x => ∀ p : Joint.PreOut C, x.2 = some p →
      (∀ l < depth (batchCircuits circuits settings (gameParameter D c.keys) c.jobs k),
        ReshareReads K hist i p.1.2.2.1.ctx.prss settings.mode
          (headLabel circuits settings (gameParameter D c.keys) c.jobs c.counters.1 k + l)
          (gatesAt (batchCircuits circuits settings (gameParameter D c.keys) c.jobs k) l).length (p.1.2.2.1.zs l)) ∧
      ReshareReads K hist i p.1.2.2.1.ctx.prss .peer
        (headLabel circuits settings (gameParameter D c.keys) c.jobs c.counters.1 k +
          depth (batchCircuits circuits settings (gameParameter D c.keys) c.jobs k))
        (outputsOf (batchCircuits circuits settings (gameParameter D c.keys) c.jobs k)).length p.1.2.2.1.v')
      [] (preGhost K circuits settings k i c) := by
    intro i hi
    rcases hpre i hi with h | ⟨keys, hkeysI, hpar⟩
    · rw [h]
      exact RerandCells.Holds.pure _ _ fun p hp => by cases hp
    · have h := draws k i c keys hkeysI hk
      rw [hpar] at h
      exact h
  have hsteps := RerandCells.executePhaseR_holds prims D D net (none : Option (Joint.PreOut C)) _ _ c.adversary _
    hholds world y hy
  generalize batchCircuits circuits settings (gameParameter D c.keys) c.jobs k = cs at *
  generalize headLabel circuits settings (gameParameter D c.keys) c.jobs c.counters.1 k = L at *
  generalize headStart circuits settings (gameParameter D c.keys) c.jobs k = n at *
  have hreads : ∀ i, i ∉ D.1 → ∃ hist, RerandCells.Celled prims D hist y1.2 ∧
      (∀ l < depth cs, ReshareReads K hist i (b i).ctx.prss settings.mode (L + l) (gatesAt cs l).length ((b i).zs l)) ∧
      ReshareReads K hist i (b i).ctx.prss .peer (L + depth cs) (outputsOf cs).length (b i).v' := by
    intro i hi
    obtain ⟨p, hp, hpb⟩ := hhead i hi
    have hr := hrec i hi p hp
    have hsi := hsteps i hi
    rcases hs : y.1.2 i with ⟨out, record⟩ | ⟨outbox, resume⟩ | ⟨input, resume⟩ <;> rw [hs] at hsi hr hp
    · obtain ⟨hist, hcel, hP⟩ := hsi
      obtain ⟨hlay, hre⟩ := hP p hr
      rw [hpb] at hlay hre
      exact ⟨hist, hworld ▸ hcel, hlay, hre⟩
    · cases hp
    · exact input.elim
  refine ⟨L, y1.2, fun l hl => ?_, ?_⟩
  · obtain ⟨steps₀, sent, hround⟩ := selfPhase_round prims K circuits settings D net k _ c world y hy
      (n + l * settings.mode.rounds + (settings.mode.rounds - 1))
      (fun i => ReshareWaitG K settings.mode i (gatesAt cs l).length (HeadRel fun b => b.zs l))
      (fun i hi => (hreachAll i hi).1 l hl) hout
    refine reshareRun_of_round prims K D settings.mode _ _ _ y1.2 _ (fun b => b.zs l) steps₀ sent
      (fun i hi T hT g hg => ?_) (fun i hi T hT g hg hf => ?_) fun i hi => ?_
    · obtain ⟨hist, hcel, hlay, -⟩ := hreads i hi
      obtain ⟨bit, hmem⟩ := (hlay l hl T hT g hg).1
      exact ⟨bit, hcel _ hmem⟩
    · obtain ⟨hist, hcel, hlay, -⟩ := hreads i hi
      exact hcel _ ((hlay l hl T hT g hg).2 hf)
    · obtain ⟨outbox, resume, hs, hq, out, hx⟩ := hround i hi
      obtain ⟨p, hp, hpb⟩ := hhead i hi
      exact ⟨outbox, resume, hs, hq, _, p, hx, hrec i hi p hp, by rw [hpb]⟩
  · obtain ⟨steps₀, sent, hround⟩ := selfPhase_round prims K circuits settings D net k _ c world y hy
      (n + depth cs * settings.mode.rounds)
      (fun i => PeerWaitG K i (outputsOf cs).length (HeadRel fun b => b.v'))
      (fun i hi => (hreachAll i hi).2) hout
    refine reshareRun_of_round prims K D .peer _ _ _ y1.2 _ (fun b => b.v') steps₀ sent
      (fun i hi T hT g hg => ?_) (fun i hi T hT g hg hf => ?_) fun i hi => ?_
    · obtain ⟨hist, hcel, -, hre⟩ := hreads i hi
      obtain ⟨bit, hmem⟩ := (hre T hT g hg).1
      exact ⟨bit, hcel _ hmem⟩
    · obtain ⟨hist, hcel, -, hre⟩ := hreads i hi
      exact hcel _ ((hre T hT g hg).2 hf)
    · obtain ⟨outbox, resume, hs, hq, out, hx⟩ := hround i hi
      obtain ⟨p, hp, hpb⟩ := hhead i hi
      exact ⟨outbox, resume, hs, hq, _, p, hx, hrec i hi p hp, by rw [hpb]⟩

/-- `CutHeads` from the heads of the recorded prefix. The prefix of the cut has the law of the
recorded prefix on the stops (`Joint.view1_eq_prefix`), and each honest stop is the start of the check
of a recorded head (`Joint.honest_stop`). A prefix with fewer rounds than `prefixRounds` has no joint
start. -/
theorem cutHeads_of_ghostHeads (heads : GhostHeads prims K circuits settings) :
    CutHeads prims K circuits settings := by
  intro D net rounds ℓ c world hready k hk z hz start hjoint hglobal hkeys
  have hseeds : seedsDiffer D c.keys = false := hready.1
  obtain ⟨hall, j, hj, -, hprssS, -, hxS, -⟩ := Joint.jointStop_some D _ _ start hjoint
  by_cases hfuel : prefixRounds circuits settings (gameParameter D c.keys) c.jobs k ≤ rounds
  swap
  · exfalso
    obtain ⟨point, rest, hpt⟩ := hall j hj
    have hnone := executePhase_support_short D net _ rounds (by omega) c.adversary _
      (fun i hi => timed_cutCeremony K circuits settings k i c _ fun keys hkeys =>
        parameter_eq_gameParameter D c.keys hseeds i hi keys hkeys) z.1 (mem_support_phase prims D _ world z hz) j hj
    rw [hnone] at hpt
    cases hpt
  have hlaw := support_eq_of_evalDistEq
    (Joint.view1_eq_prefix prims K circuits settings D net k rounds c world hseeds hk hfuel)
  have hview : Joint.viewCut net z ∈ support (Joint.view1 K net <$> Joint.phase1 prims K circuits settings D net k
      (prefixRounds circuits settings (gameParameter D c.keys) c.jobs k) c world) := by
    rw [hlaw, support_map]
    exact ⟨z, hz, rfl⟩
  rw [support_map] at hview
  obtain ⟨y1, hy1, hvy⟩ := hview
  have hjV : Joint.jointStopV (E := E) D (Joint.view1 K net y1) = some start := by
    rw [hvy, ← hjoint, Joint.jointStop_viewCut]
    rfl
  have hfacts := fun i hi => Joint.honest_stop prims K circuits settings D net k c world y1 hy1 start hjV i hi
  obtain ⟨-, -, -, -, hprssV, -, hxV, -⟩ := Joint.jointStop_some D _ _ start hjV
  have hworld : y1.2 = z.2 := congrArg (fun v => v.2.2) hvy
  obtain ⟨-, pj, -, -, -, -⟩ := hfacts j hj
  let fallback : C.Party → BatchStart C := fun i =>
    { pj.1.2.2.1 with ctx := { pj.1.2.2.1.ctx with prss := start.prss i } }
  let b : C.Party → BatchStart C := fun i =>
    if i ∈ D.1 then fallback i else ((y1.1.2 i).output.map (·.1.2.2.1)).getD (fallback i)
  have hb : ∀ i, i ∉ D.1 → ∃ p : Joint.PreOut C, (y1.1.2 i).output = some p ∧ p.1.2.2.1 = b i ∧
      stopPoint i (Joint.ofView (E := E) ((Joint.view1 K net y1).2.1 i)) = pointOf K (b i) := by
    intro i hi
    obtain ⟨-, p, -, hp, -, hstop⟩ := hfacts i hi
    have hbi : b i = p.1.2.2.1 := by simp only [b, hi, ↓reduceIte, hp, Option.map_some, Option.getD_some]
    exact ⟨p, hp, hbi.symm, hbi ▸ hstop⟩
  have hbprss : (fun i => (b i).ctx.prss) = start.prss := by
    funext i
    by_cases hi : i ∈ D.1
    · simp only [b, fallback, hi, ↓reduceIte]
    · obtain ⟨p, -, -, hstop⟩ := hb i hi
      rw [hprssV]
      dsimp only
      rw [hstop]
      rfl
  have hshape : ∀ i, i ∉ D.1 → (b i).mode = settings.mode ∧
      (b i).circuits = batchCircuits circuits settings (gameParameter D c.keys) c.jobs k := by
    intro i hi
    obtain ⟨keys, p, hkeysI, hp, hmem, -⟩ := hfacts i hi
    obtain ⟨p', hp', hbp, -⟩ := hb i hi
    obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
    simp only [Joint.pre1, hkeysI] at hmem
    rw [← hbp, batchCircuits, ← parameter_eq_gameParameter D c.keys hseeds i hi keys hkeysI]
    exact recPrefix_shape K circuits settings k i keys c.jobs c.counters _ hmem p hp
  have hinputs := ghost_inputsAgree prims K circuits settings D net k _ c world hseeds y1 hy1 b
    fun i hi => (hb i hi).imp fun p h => ⟨h.1, h.2.1⟩
  obtain ⟨L, w, hlayers, hrerand⟩ :=
    heads D net ℓ c world hready k hk y1 hy1 b (fun i hi => (hb i hi).imp fun p h => ⟨h.1, h.2.1⟩)
      (hworld ▸ hglobal) (hbprss ▸ hkeys)
  rw [← hbprss]
  refine ⟨settings.mode, batchCircuits circuits settings (gameParameter D c.keys) c.jobs k, L, w,
    fun i => (b i).inputs, fun i => (b i).zs, fun i => (b i).v', fun i hi => ?_, hinputs, hlayers, hrerand⟩
  obtain ⟨p, -, -, hstop⟩ := hb i hi
  rw [hxV]
  dsimp only
  rw [hstop, ← (hshape i hi).1, ← (hshape i hi).2]
  rfl

/-- `CeremonyTupleInputs`. -/
theorem ceremonyTupleInputs : CeremonyTupleInputs prims K circuits settings :=
  ceremonyTupleInputs_of_cutHeads prims K circuits settings (cutHeads_of_ghostHeads prims K circuits settings
    (ghostHeads_of_walks prims K circuits settings (headReach K circuits settings) (headDraws K circuits settings)))

end CutBudget

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.CutBudget.ceremonyTupleInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.CutBudget.ceremonyTupleInputs
