import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.First
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Stream
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ready.Glue

/-!
# The readiness and the flag of the game with the first record

`firstRunOf_keepsState` carries an invariant of the state of the game through `firstRunOf`, for each
run, when each run of a tree keeps it and the writes of the signing phase do not change it.

`passReadyHop` states `PassReadyHop`. A start that the game records as not ready fails the ledger or
the provenance, because no record before it means consistent honest keys (`PassInv`). The world of
the record is below the final world, the final world is within the ledger, and the ledger is
downward closed (`ledgerFits_of_le`). The snapshot of each record has the provenance.

`passFlagFirst` states `PassFlagFirst`. The runs of the real game with the shared event have the law
of the real state of the runs of `passFirst` (`PassTracksAt`). The win test at the end does not change
the flag, and the flag of `passFirst` comes with a first record (`FlagRecorded`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

open Ready (Keeps KeepsT keeps_pure keeps_bind keeps_get_bind keeps_get keeps_modify keeps_lift keepsT_lift
  keepsT_bind keepsT_simulateQ)

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## An invariant of the state through the game -/

section Walk

variable {σ : Type} (I : FirstState C σ → Prop)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstTreeRunsOf_keepsState (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (I : FirstState C net.State → Prop) (run : RunOf C net.State)
    (ready : RealState C net.State → StreamState C → Prop) (tree : Tree)
    (hrun : Keeps (fun s (_ : StreamState C) => I s) (firstTreeRunOf prims D net run ready tree)) :
    ∀ count, Keeps (fun s (_ : StreamState C) => I s) (firstTreeRunsOf prims runLimit D net run ready tree count)
  | 0 => keeps_pure _
  | count + 1 => by
    unfold firstTreeRunsOf
    refine keeps_get_bind fun s => ?_
    split_ifs
    · exact keeps_bind hrun fun _ => firstTreeRunsOf_keepsState D net I run ready tree hrun count
    · exact keeps_pure _

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstTreeRequestOf_keepsState (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (I : FirstState C net.State → Prop) (run : RunOf C net.State)
    (ready : RealState C net.State → StreamState C → Prop) (b : Fin (2 ^ layerHeight))
    (hrun : Keeps (fun s (_ : StreamState C) => I s) (firstTreeRunOf prims D net run ready (.bottom b))) :
    Keeps (fun s (_ : StreamState C) => I s) (firstTreeRequestOf prims runLimit D net run ready b) := by
  unfold firstTreeRequestOf
  refine keeps_bind (firstTreeRunsOf_keepsState prims runLimit D net I run ready _ hrun 1) fun _ =>
    keeps_get_bind fun s => ?_
  split
  · exact keeps_bind (keeps_lift (fun _ _ _ h _ => h) (Ready.simulateQ_le prims D _)) fun _ => keeps_pure _
  · exact keeps_pure _

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstSignRequest_keepsState (D : C.Coalition) (i : C.Party) (e : KeyIndex) (q : TsigQuery C)
    (hclosed : ∀ s : FirstState C σ, I s →
      I { s with real := { s.real with closed := Function.update s.real.closed (treeOf e) true } }) :
    KeepsT (fun s (_ : StreamState C) => I s) (firstSignRequest (σ := σ) prims D i e q) := by
  unfold firstSignRequest
  refine keepsT_bind (keepsT_lift (keeps_modify _ fun s _ hs => hclosed s hs)) fun _ =>
    keepsT_bind (keepsT_lift keeps_get) fun s => ?_
  exact operatorAnswer_keepsG prims _ (fun _ _ _ h _ => h) D _ _ e q

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstSigningOf_keepsState (D : C.Coalition) (A : DkgTsigAdversary C E) (run : RunOf C A.net.State)
    (ready : RealState C A.net.State → StreamState C → Prop) (I : FirstState C A.net.State → Prop)
    (hrun : ∀ tree, Keeps (fun s (_ : StreamState C) => I s) (firstTreeRunOf prims D A.net run ready tree))
    (hclosed : ∀ (s : FirstState C A.net.State) (e : KeyIndex), I s →
      I { s with real := { s.real with closed := Function.update s.real.closed (treeOf e) true } })
    (hadversary : ∀ (s : FirstState C A.net.State) (state : A.net.State), I s →
      I { s with real := { s.real with adversary := state } }) :
    Keeps (fun s (_ : StreamState C) => I s) (firstSigningOf prims runLimit D A run ready) := by
  unfold firstSigningOf
  refine keeps_get_bind fun s => ?_
  split
  · refine keeps_bind (keepsT_simulateQ _ (fun q => ?_) _ _) fun _ => keeps_pure _
    rcases q with t | q | q
    · exact keepsT_lift (keeps_lift (fun _ _ _ h _ => h) (Ready.simulateQ_le prims D _))
    · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
      · exact fun t => keeps_pure _
      · exact keepsT_lift (firstTreeRequestOf_keepsState prims runLimit D A.net I run ready b (hrun _))
      · exact firstSignRequest_keepsState prims I D i e _ fun s hs => hclosed s e hs
      · exact firstSignRequest_keepsState prims I D i e _ fun s hs => hclosed s e hs
    · rcases q with _ | state
      · exact keepsT_lift (keeps_bind keeps_get fun _ => keeps_pure _)
      · exact keepsT_lift (keeps_modify _ fun s _ hs => hadversary s state hs)
  · exact keeps_pure _

end Walk

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- An invariant of the state of the game holds at each final state of `firstRunOf`, when it holds at
each start after the seed generation, each run of a tree keeps it, and the writes of the signing
phase keep it. -/
theorem firstRunOf_keepsState (D : C.Coalition) (A : DkgTsigAdversary C E) (run : RunOf C A.net.State)
    (ready : RealState C A.net.State → StreamState C → Prop) (I : FirstState C A.net.State → Prop)
    (hstart : ∀ (state : A.net.State) (keys : C.Party → Option (Keys C)) (ok : Bool) (world : StreamState C),
      I ⟨seedState D state keys ok, if (seedState D state keys ok).flag then some (.seeds, world) else none⟩)
    (hrun : ∀ tree, Keeps (fun s (_ : StreamState C) => I s) (firstTreeRunOf prims D A.net run ready tree))
    (hclosed : ∀ (s : FirstState C A.net.State) (e : KeyIndex), I s →
      I { s with real := { s.real with closed := Function.update s.real.closed (treeOf e) true } })
    (hadversary : ∀ (s : FirstState C A.net.State) (state : A.net.State), I s →
      I { s with real := { s.real with adversary := state } }) :
    ∀ r ∈ support (firstRunOf prims runLimit D A run ready), I r.1 := by
  intro r hr
  unfold firstRunOf at hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨y, -, hr⟩ := hr
  rcases y with ⟨⟨state, keys⟩, world⟩
  simp only [StateT.run_get, support_pure, Set.mem_singleton_iff, exists_eq_left, StateT.run_pure] at hr
  obtain ⟨t, -, x, ⟨z, hz, hx⟩, rfl⟩ := hr
  exact keeps_bind (firstTreeRunsOf_keepsState prims runLimit D A.net I run ready .top (hrun _) runLimit)
    (fun _ => firstSigningOf_keepsState prims runLimit D A run ready I hrun hclosed hadversary) _ t.2
    (hstart t.1.1 keys t.1.2 world) x
    (by rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff]; exact ⟨z, hz, hx⟩)

/-! ## The readiness of each start -/

/-- With no record, the honest keys are consistent. Each start that is recorded as not ready fails
the ledger or the provenance. -/
def PassInv (budget : StartBudget) (D : C.Coalition) {σ : Type} (s : FirstState C σ) : Prop :=
  (s.first = none → seedsDiffer D (fun i => (s.real.operators i).keys) = false) ∧
    ∀ tree index w, s.first = some (.unready tree index, w) → ¬ (LedgerFits budget w ∧ HiddenProvenance D w)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstTreeRunOf_passInv (budget : StartBudget) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (run : RunOf C net.State) (tree : Tree) :
    Keeps (fun s (_ : StreamState C) => PassInv budget D s)
      (firstTreeRunOf prims D net run (PassReady budget D) tree) := by
  intro s world hs z hz
  simp only [firstTreeRunOf, inStream, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc,
    StateT.run_set, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨x, -, y, -, rfl⟩ := hz
  obtain ⟨hseeds, hunready⟩ := hs
  have hkeys : (fun j => ((s.real.operators j).keep (committed y.1.2 (fun i => x.1.1.2 i) j) tree).keys) =
      fun j => (s.real.operators j).keys :=
    funext fun j => Ready.keep_keys _ _ _
  refine ⟨fun hn => ?_, fun tree' index w hw => ?_⟩
  · obtain ⟨hn₁, -⟩ := Ready.orElse_eq_none hn
    obtain ⟨hfirst, -⟩ := Ready.orElse_eq_none hn₁
    change seedsDiffer D (fun j => ((s.real.operators j).keep (committed y.1.2 (fun i => x.1.1.2 i) j) tree).keys)
      = false
    rw [hkeys]
    exact hseeds hfirst
  · cases hfirst : s.first with
    | some v =>
      simp only [hfirst, Ready.some_orElse] at hw
      exact hunready tree' index w (hfirst.trans hw)
    | none =>
      simp only [hfirst, Ready.none_orElse] at hw
      by_cases hready : PassReady budget D s.real world
      · simp only [hready, ite_true, Ready.none_orElse] at hw
        split_ifs at hw
        simp at hw
      · simp only [hready, ite_false, Ready.some_orElse] at hw
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
        exact fun h => hready ⟨hseeds hfirst, h⟩

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The ledger is downward closed in the world. -/
theorem ledgerFits_of_le {budget : StartBudget} {w w' : StreamState C} (h : LedgerFits budget w') (hle : w ≤ w') :
    LedgerFits budget w := by
  obtain ⟨⟨S, hS, hcover⟩, ⟨seen, keys, ⟨hcoin, hexpand⟩, hseen, hkeys⟩, ⟨salts, hsalts, hcard⟩, hhidden⟩ := h
  refine ⟨⟨S, hS, fun x hx => hcover x ?_⟩, ⟨seen, keys, ⟨fun tag label bits hL hx =>
    hcoin tag label bits hL (Ready.cell_ne_none_of_le hle.1 hx), fun key idx hx =>
    hexpand key idx (Ready.cell_ne_none_of_le hle.1 hx)⟩, hseen, hkeys⟩,
    ⟨salts, fun salt x hx => hsalts salt x (Ready.cell_ne_none_of_le hle.1 hx), hcard⟩, fun name => ?_⟩
  · simp only [splitRegionCache, QueryCache.ofFn_apply] at hx ⊢
    split_ifs at hx ⊢
    · exact Ready.cell_ne_none_of_le hle.1 hx
    · exact hx
  · obtain ⟨keys, hcard, hcover⟩ := hhidden name
    exact ⟨keys, hcard, fun key ρ idx position hx => hcover key ρ idx position (Ready.cell_ne_none_of_le hle.2 hx)⟩

omit [Fintype E] [DecidableEq E] in
/-- The cells of class `digest` at the end of `passFirst` lie within the class budget of the
adversary and the honest digest cells of the game. -/
theorem passFirst_digest (D : C.Coalition) (A : DkgTsigAdversary C E)
    (ready : RealState C A.net.State → StreamState C → Prop) (own : HashClass → ℕ)
    (hA : DkgTsigClassBounded circuits settings runLimit A own) :
    ∀ r ∈ support (passFirst prims K circuits settings runLimit D A ready),
      FirstCounts.Within .digest r.2.1 (own .digest + gameBatches settings runLimit * termHashes C) := by
  intro r hr
  obtain ⟨start, step, forge, hsum, hs, hround, hf⟩ := hA .digest
  unfold passFirst at hr
  rw [passTreeRun_eq_blockRun] at hr
  have h := FirstCounts.firstRunOf_within prims runLimit .digest
    (fun tree => treeFuel circuits settings * step + treeBatches settings tree * termHashes C) (by decide) D A _ _ _
    ready (start + setupRounds * step + 0) step forge
    (FirstCounts.seedBlock_bound .digest D A.net start step 0 hs hround DigestBudgets.seedHonest_digest)
    (FirstCounts.voteRound_adds .digest (by decide) D A.net step hround) hf
    (fun tree s => passBlock_adds K circuits settings .digest D A.net step hround _
      (DigestBudgets.treeHonest_digest K circuits settings) tree s) DigestBudgets.signQuiet_digest r hr
  have e : FirstCounts.remaining runLimit
      (fun tree => treeFuel circuits settings * step + treeBatches settings tree * termHashes C + step)
        (fun _ => 0) =
      runLimit * (1 + 2 ^ layerHeight) * treeFuel circuits settings * step + runLimit * (1 + 2 ^ layerHeight) * step +
        gameBatches settings runLimit * termHashes C := by
    simp only [FirstCounts.remaining, Nat.sub_zero, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, gameBatches, ← Finset.sum_mul]
    ring
  have e' : dkgTsigRounds circuits settings runLimit * step =
      setupRounds * step + step + runLimit * (1 + 2 ^ layerHeight) * treeFuel circuits settings * step +
        runLimit * (1 + 2 ^ layerHeight) * step := by
    unfold dkgTsigRounds
    ring
  rw [e] at h
  exact h.mono (by omega)

/-- The final world of `passFirst` is within the ledger `startBudget`, for each readiness test. -/
theorem passFirst_ledger (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ)
    (bounded : DkgTsigBounded circuits settings runLimit A q)
    (ready : RealState C A.net.State → StreamState C → Prop) :
    ∀ r ∈ support (passFirst prims K circuits settings runLimit D A ready),
      LedgerFits (startBudget circuits settings runLimit C q) r.2 := by
  intro r hr
  obtain ⟨cells, hcard, hcover⟩ := passFirst_digest prims K circuits settings runLimit D A ready _
    (dkgTsigBounded_classBounded circuits settings runLimit bounded) r hr
  refine ⟨⟨cells, hcard, fun x hx => ?_⟩,
    soundAtEndOf prims circuits settings runLimit D A q bounded _
      (fun step hround => passTreeRun_sound prims K circuits settings D A.net step hround) ready r hr,
    ⟨cells.image FirstCounts.saltOf, fun salt x hx =>
      Finset.mem_image.2 ⟨.digest salt x, hcover _ (by simp [GameCount.CellIn, queryClass]) hx, rfl⟩,
      Finset.card_image_le.trans hcard⟩,
    firstRunOf_hiddenKeyBound prims runLimit D A _ (passTreeRun_hidden prims K circuits settings D A.net) ready r hr⟩
  simp only [splitRegionCache, QueryCache.ofFn_apply] at hx
  split_ifs at hx with hd
  · exact hcover x ((FirstCounts.cellIn_digest_iff x).2 hd) hx
  · exact absurd rfl hx

/-- In the game that tests `PassReady` at each start, no start is recorded as not ready with no
global event. -/
theorem passReadyHop : PassReadyHop prims K circuits settings runLimit := by
  intro D A q bounded
  unfold passFirstProb
  rw [prEvent_eq_zero_of_forall_mem_support _ _ fun r hr => ?_, ENNReal.toReal_zero]
  rintro ⟨tree, index, w, hw, -⟩
  have hinv := firstRunOf_keepsState prims runLimit D A _ _ (PassInv (startBudget circuits settings runLimit C q) D)
    (fun state keys ok world => ⟨fun hn => by
        have hf : (seedState D state keys ok).flag = false := by
          by_contra hflag
          simp only [Bool.not_eq_false] at hflag
          simp [hflag] at hn
        simp only [seedState, startState, Bool.or_eq_false_iff] at hf
        cases ok
        · simp [seedsDiffer, committed, seedState, startState]
        · exact hf.1,
      fun tree index w hw => by
        split_ifs at hw
        simp at hw⟩)
    (fun tree => firstTreeRunOf_passInv prims _ D A.net _ tree) (fun _ _ h => h) (fun _ _ h => h) r hr
  have hle : w ≤ r.2 := RecordedCache.recordedBelowOf prims runLimit D A _
    (by rw [passTreeRun_eq_blockRun]; exact RecordedCache.blockRun_grows prims D _ _ _) _ r hr _ w hw
  have hprov : HiddenProvenance D w := (firstRunOf_provInv prims runLimit (provenanceSeedGen prims)
    (provenanceCounted prims) (provenanceSigning prims) D A _ (passTreeRun_provenance prims K circuits settings D A.net)
    _ r hr).2 _ w hw
  exact hinv.2 tree index w hw ⟨ledgerFits_of_le (passFirst_ledger prims K circuits settings runLimit D A q bounded _ r hr)
    hle, hprov⟩

/-! ## The law of the flag -/

section PassTracks

variable {σ : Type}

/-- From the state `s`, the real game `x` in `streamWorld` has the law of the real state of `y`. -/
def PassTracksAt {α : Type} (x : SharedM C ProbComp (StreamState C) σ α) (y : FirstM C σ α) (s : FirstState C σ) :
    Prop :=
  x.run s.real = (fun r => (r.1, r.2.real)) <$> y.run s

/-- `PassTracksAt` from each state. -/
def PassTracks {α : Type} (x : SharedM C ProbComp (StreamState C) σ α) (y : FirstM C σ α) : Prop :=
  ∀ s, PassTracksAt x y s

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem passTracks_pure {α : Type} (a : α) :
    PassTracks (pure a : SharedM C ProbComp (StreamState C) σ α) (pure a : FirstM C σ α) := by
  intro s
  simp [PassTracksAt]

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem passTracks_bind {α β : Type} {x : SharedM C ProbComp (StreamState C) σ α} {y : FirstM C σ α}
    {f : α → SharedM C ProbComp (StreamState C) σ β} {g : α → FirstM C σ β} (hxy : PassTracks x y)
    (hfg : ∀ a, PassTracks (f a) (g a)) : PassTracks (x >>= f) (y >>= g) := by
  intro s
  have h : x.run s.real = (fun r => (r.1, r.2.real)) <$> y.run s := hxy s
  unfold PassTracksAt
  rw [StateT.run_bind, StateT.run_bind, h, bind_map_left, map_bind]
  congr 1
  funext r
  exact hfg r.1 r.2

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem passTracks_lift {α : Type} (x : StateT (StreamState C) ProbComp α) :
    PassTracks (StateT.lift x : SharedM C ProbComp (StreamState C) σ α) (StateT.lift x : FirstM C σ α) := by
  intro s
  simp [PassTracksAt]

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem passTracks_get_bind {α : Type} {f : RealState C σ → SharedM C ProbComp (StreamState C) σ α}
    {g : FirstState C σ → FirstM C σ α} (h : ∀ s, PassTracksAt (f s.real) (g s) s) :
    PassTracks (get >>= f) (get >>= g) := by
  intro s
  simpa [PassTracksAt] using h s

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem passTracks_modify (f : RealState C σ → RealState C σ) (g : FirstState C σ → FirstState C σ)
    (real : ∀ s, (g s).real = f s.real) :
    PassTracks (modify f : SharedM C ProbComp (StreamState C) σ Unit) (modify g : FirstM C σ Unit) := by
  intro s
  simp [PassTracksAt, real]

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem passTracks_map_get {α : Type} (f : RealState C σ → α) :
    PassTracks (f <$> (get : SharedM C ProbComp (StreamState C) σ _)) ((fun s => f s.real) <$> (get : FirstM C σ _)) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact passTracks_get_bind fun s => passTracks_pure _ s

/-- `PassTracks` from each state of the signing game. -/
def PassTracksSign {α : Type} (x : StateT (TsigState C) (SharedM C ProbComp (StreamState C) σ) α)
    (y : StateT (TsigState C) (FirstM C σ) α) : Prop :=
  ∀ st, PassTracks (x.run st) (y.run st)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem passTracksSign_bind {α β : Type} {x : StateT (TsigState C) (SharedM C ProbComp (StreamState C) σ) α}
    {y : StateT (TsigState C) (FirstM C σ) α} {f : α → StateT (TsigState C) (SharedM C ProbComp (StreamState C) σ) β}
    {g : α → StateT (TsigState C) (FirstM C σ) β} (hxy : PassTracksSign x y) (hfg : ∀ a, PassTracksSign (f a) (g a)) :
    PassTracksSign (x >>= f) (y >>= g) := fun st =>
  passTracks_bind (hxy st) fun r => hfg r.1 r.2

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem passTracksSign_lift {α : Type} {x : SharedM C ProbComp (StreamState C) σ α} {y : FirstM C σ α}
    (hxy : PassTracks x y) :
    PassTracksSign (StateT.lift x : StateT (TsigState C) (SharedM C ProbComp (StreamState C) σ) α) (StateT.lift y) :=
  fun _ => passTracks_bind hxy fun _ => passTracks_pure _

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem passTracksSign_simulateQ {ι α : Type} {spec : OracleSpec ι}
    (implx : QueryImpl spec (StateT (TsigState C) (SharedM C ProbComp (StreamState C) σ)))
    (imply : QueryImpl spec (StateT (TsigState C) (FirstM C σ)))
    (h : ∀ t, PassTracksSign (implx t) (imply t)) (oa : OracleComp spec α) :
    PassTracksSign (simulateQ implx oa) (simulateQ imply oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun st => by simpa using passTracks_pure (C := C) (σ := σ) (a, st)
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query]
    exact passTracksSign_bind (by simpa using h t) ih

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A computation of the world, in the real game and in the game with the first record. -/
theorem passTracks_world (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α) :
    PassTracks (worldHomOver (streamWorld prims D) σ oa) (firstHom prims D σ oa) :=
  passTracks_lift _

end PassTracks

/-! ## The runs and the signing phase -/

omit [Fintype E] [DecidableEq E] in
theorem passTracks_sharedRun (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (ready : RealState C net.State → StreamState C → Prop) (tree : Tree) :
    PassTracks (sharedRun K circuits settings (streamWorld prims D) id Mode.real D net parameter seeds dealt emu tree)
      (firstTreeRunOf prims D net (passTreeRun prims K circuits settings D net) ready tree) := by
  intro s
  have hnot : ¬ s.real.runs tree < Mode.real.emulated tree := by simp [Mode.real]
  unfold PassTracksAt sharedRun
  simp only [StateT.run_bind, StateT.run_get, pure_bind, ite_eq_right hnot]
  unfold sharedRunWith firstTreeRunOf passTreeRun
  simp [inWorld, inStream, StateT.run_lift]

omit [Fintype E] [DecidableEq E] in
theorem passTracks_sharedRuns (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (ready : RealState C net.State → StreamState C → Prop) (tree : Tree) :
    ∀ count, PassTracks (sharedRuns K circuits settings runLimit (streamWorld prims D) id Mode.real D net parameter seeds
        dealt emu tree count)
      (firstTreeRunsOf prims runLimit D net (passTreeRun prims K circuits settings D net) ready tree count)
  | 0 => passTracks_pure ()
  | count + 1 => by
    unfold sharedRuns firstTreeRunsOf
    refine passTracks_get_bind fun s => ?_
    by_cases h : mayRun runLimit D s.real tree
    · simp only [h, ↓reduceIte]
      exact passTracks_bind (passTracks_sharedRun prims K circuits settings D net parameter seeds dealt emu ready tree)
        (fun _ => passTracks_sharedRuns D net parameter seeds dealt emu ready tree count) s
    · simp only [h, ↓reduceIte]
      exact passTracks_pure () s

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem passTracksSign_get_bind {σ α : Type}
    {f : RealState C σ → StateT (TsigState C) (SharedM C ProbComp (StreamState C) σ) α}
    {g : FirstState C σ → StateT (TsigState C) (FirstM C σ) α}
    (h : ∀ s st, PassTracksAt ((f s.real).run st) ((g s).run st) s) :
    PassTracksSign (StateT.lift get >>= f) (StateT.lift get >>= g) := by
  intro st s
  simpa [PassTracksAt] using h s st

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem passTracksSign_signRequest (D : C.Coalition) {σ : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    PassTracksSign
      (do
        StateT.lift (modify fun s : RealState C σ => { s with closed := Function.update s.closed (treeOf e) true })
        let s ← StateT.lift get
        operatorAnswer (sharedLift (streamWorld prims D))
          (fun x => sharedLift (streamWorld prims D) (prfValue (gameSeeds D fun i => (s.operators i).keys) x))
          (s.operators i) e q :
        StateT (TsigState C) (SharedM C ProbComp (StreamState C) σ) (TsigSpec C q))
      (firstSignRequest (σ := σ) prims D i e q) := by
  refine passTracksSign_bind (passTracksSign_lift (passTracks_modify _ _ fun _ => rfl)) fun _ => ?_
  refine passTracksSign_get_bind fun s st => ?_
  have key := passTracks_world prims D (σ := σ) ((operatorAnswer (m := OracleComp (WorldSpec C))
    (fun oa => free (liftComp oa _)) (fun x => free (liftComp (prfValue (gameSeeds D fun j =>
      (s.real.operators j).keys) x) _)) (s.real.operators i) e q).run st) s
  rw [hom_operatorAnswer, hom_operatorAnswer] at key
  exact key

omit [Fintype E] [DecidableEq E] in
theorem passTracksSign_oracles (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (ready : RealState C A.net.State → StreamState C → Prop) (q : TsigQuery C) :
    PassTracksSign (sharedOwnOracles K circuits settings runLimit (streamWorld prims D) id Mode.real D A.net parameter seeds
        dealt emu q)
      (firstOraclesOf prims runLimit D A.net (passTreeRun prims K circuits settings D A.net) ready q) := by
  unfold sharedOwnOracles
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact fun st => passTracks_pure _
  · dsimp only
    unfold firstOraclesOf firstTreeRequestOf
    refine passTracksSign_lift (passTracks_bind (passTracks_sharedRuns prims K circuits settings runLimit D A.net parameter seeds
      dealt emu ready _ 1) fun _ => passTracks_get_bind fun s => ?_)
    rcases heldBottom D s.real.operators b with _ | tree
    · exact passTracks_pure _ s
    · exact passTracks_bind (passTracks_lift _) (fun _ => passTracks_pure _) s
  · exact passTracksSign_signRequest prims D i e _
  · exact passTracksSign_signRequest prims D i e _

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A computation of the real game followed by a computation that keeps the real state sets the flag
at most as likely as the tracked computation of the game with the first record. -/
theorem flag_le_of_passTracks {σ α β : Type} (fs : FirstState C σ) (w : StreamState C)
    (Y : SharedM C ProbComp (StreamState C) σ α) (Y' : FirstM C σ α) (f : α → SharedM C ProbComp (StreamState C) σ β)
    (hY : PassTracksAt Y Y' fs) (hf : ∀ a s w, ∀ z ∈ support (((f a).run s).run w), z.1.2 = s) :
    Pr{let z ← ((Y >>= f).run fs.real).run w}[z.1.2.flag = true] ≤
      Pr{let z ← ((Y' >>= fun _ => pure ()).run fs).run w}[z.1.2.real.flag = true] := by
  have hY' : Y.run fs.real = (fun r => (r.1, r.2.real)) <$> Y'.run fs := hY
  rw [StateT.run_bind, hY', bind_map_left, StateT.run_bind, StateT.run_bind, StateT.run_bind]
  refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun a => ?_
  by_cases hflag : a.1.2.real.flag = true
  · simp [hflag]
  · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz => ?_]
    · exact bot_le
    · rw [hf _ _ _ z hz]
      exact hflag

omit [Fintype E] [DecidableEq E] in
/-- The flag after the signing phase of the real game is at most as likely as the flag after the
signing phase of `passFirst`. The win test at the end keeps the real state. -/
theorem signing_flag_le (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (ready : RealState C A.net.State → StreamState C → Prop) (fs : FirstState C A.net.State) (w : StreamState C) :
    Pr{let z ← ((sharedSigning K circuits settings runLimit (streamWorld prims D) id true Mode.real D A parameter seeds
        dealt emu).run fs.real).run w}[z.1.2.flag = true] ≤
      Pr{let z ← ((firstSigningOf prims runLimit D A (passTreeRun prims K circuits settings D A.net) ready).run
        fs).run w}[z.1.2.real.flag = true] := by
  unfold sharedSigning firstSigningOf
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases topHolder D fs.real.operators with _ | ⟨keys, top⟩
  · simp
  · simp only [↓reduceIte]
    refine flag_le_of_passTracks fs w _ _ _ (passTracksSign_simulateQ _ _ (fun t => ?_) _ _ fs) fun p s₀ w₀ z hz => ?_
    · rcases t with t | q | q
      · exact passTracksSign_lift (passTracks_lift _)
      · exact passTracksSign_oracles prims K circuits settings runLimit D A parameter seeds dealt emu ready q
      · rcases q with _ | state
        · exact passTracksSign_lift (passTracks_map_get (·.adversary))
        · exact passTracksSign_lift (passTracks_modify _ _ fun _ => rfl)
    · rw [StateT.run_bind, StateT.run_get, pure_bind] at hz
      have hdealt : SeedHitProof.Dealt.hmap (worldHomOver (streamWorld prims D) A.net.State)
          (worldDealt D s₀.operators keys.parameter top) =
            { dealtWith (m := SharedM C ProbComp (StreamState C) A.net.State) (sharedLift (streamWorld prims D))
                keys.parameter (fun i => ((s₀.operators i).keys).getD noKeys) top
                (fun x => sharedLift (streamWorld prims D) (prfValue (gameSeeds D fun i => (s₀.operators i).keys) x)) with
              bottom := fun b => pure (heldBottom D s₀.operators b) } := by
        unfold SeedHitProof.Dealt.hmap worldDealt
        congr 1
      have h₁ := hom_forgeryWins (worldHomOver (streamWorld prims D) A.net.State) (fun oa => free (liftComp oa _))
        (worldDealt D s₀.operators keys.parameter top) p.2 p.1
      rw [hdealt] at h₁
      have hz' : z ∈ support (((worldHomOver (streamWorld prims D) A.net.State (forgeryWins
          (fun oa => free (liftComp oa _)) (worldDealt D s₀.operators keys.parameter top) p.2 p.1)).run s₀).run w₀) := by
        rw [h₁]
        exact hz
      change z ∈ support (((StateT.lift _ : SharedM C ProbComp (StreamState C) A.net.State Bool).run s₀).run w₀) at hz'
      simp only [StateT.run_lift, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hz'
      obtain ⟨y, -, rfl⟩ := hz'
      rfl

omit [Fintype E] [DecidableEq E] in
/-- The flag after the runs of the top tree and the signing phase of the real game is at most as
likely as the flag after those of `passFirst`. -/
theorem rest_flag_le (D : C.Coalition) (A : DkgTsigAdversary C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (dealt : C.Party → Keys C) (emu : C.Party → Option (Keys C))
    (ready : RealState C A.net.State → StreamState C → Prop) (fs : FirstState C A.net.State) (w : StreamState C) :
    Pr{let z ← ((sharedRuns K circuits settings runLimit (streamWorld prims D) id Mode.real D A.net parameter seeds
        dealt emu .top runLimit >>= fun _ => sharedSigning K circuits settings runLimit (streamWorld prims D) id true
          Mode.real D A parameter seeds dealt emu).run fs.real).run w}[z.1.2.flag = true] ≤
      Pr{let z ← ((firstTreeRunsOf prims runLimit D A.net (passTreeRun prims K circuits settings D A.net) ready .top
        runLimit >>=
        fun _ => firstSigningOf prims runLimit D A (passTreeRun prims K circuits settings D A.net) ready).run
          fs).run w}[z.1.2.real.flag = true] := by
  have h : (sharedRuns K circuits settings runLimit (streamWorld prims D) id Mode.real D A.net parameter seeds dealt
      emu .top runLimit).run fs.real = (fun r => (r.1, r.2.real)) <$>
        (firstTreeRunsOf prims runLimit D A.net (passTreeRun prims K circuits settings D A.net) ready .top runLimit).run
          fs :=
    passTracks_sharedRuns prims K circuits settings runLimit D A.net parameter seeds dealt emu ready .top runLimit fs
  rw [StateT.run_bind, h, bind_map_left, StateT.run_bind, StateT.run_bind, StateT.run_bind]
  exact prEvent_bind_mono_of_forall_le _ _ _ _ _ fun a =>
    signing_flag_le prims K circuits settings runLimit D A parameter seeds dealt emu ready a.1.2 a.2

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- Each run of a tree keeps `FlagRecorded`. A run that sets the flag records itself when no record
is there. -/
theorem firstTreeRunOf_flagRecorded (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (run : RunOf C net.State) (ready : RealState C net.State → StreamState C → Prop) (tree : Tree) :
    Keeps (fun s (_ : StreamState C) => FlagRecorded s) (firstTreeRunOf prims D net run ready tree) := by
  intro s world hs z hz
  simp only [firstTreeRunOf, inStream, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc,
    StateT.run_set, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨x, -, y, hy, rfl⟩ := hz
  have hsplit := Vote.voteRound_split_run worldRoles D net x.1.1.1 x.1.1.2 (treeVote tree) (streamWorld prims D) x.2
    y hy
  intro hflag
  dsimp only at hflag ⊢
  rw [hsplit, Bool.or_false] at hflag
  cases hfirst : s.first with
  | some v => simp
  | none =>
    have hf : s.real.flag = false := by
      cases h : s.real.flag
      · rfl
      · exact absurd hfirst (hs h)
    rw [hf, Bool.false_or] at hflag
    simp [hflag]

omit [Fintype E] [DecidableEq E] in
/-- The flag of the real game with the shared event comes with a first record of `passFirst`, for
each readiness test. -/
theorem passFlagFirst : PassFlagFirst prims K circuits settings runLimit := by
  intro D A ready
  rw [realProb_eq_stream]
  unfold passFirstProb
  refine ENNReal.toReal_mono (prEvent_ne_top _) (le_trans ?_ (prEvent_mono_of_support _
    (fun r => r.1.real.flag = true) _ fun r hr hflag => ?_))
  · unfold sharedStream passFirst firstRunOf sharedRestOf sharedRest
    rw [StateT.run'_eq, StateT.run_bind, StateT.run_bind, map_bind]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun a => ?_
    rcases a with ⟨⟨state, keys⟩, world⟩
    simp only [inWorld, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure, StateT.run_lift, StateT.run_set,
      map_bind, map_pure, bind_assoc, votedStart_startState]
    dsimp only [startState]
    refine prEvent_bind_mono_of_support _ _ _ fun p _ => ?_
    have h := rest_flag_le prims K circuits settings runLimit D A (gameParameter D keys) (gameSeeds D keys)
      (fun i => (keys i).getD noKeys) (committed p.1.2 fun _ => none) ready
      ⟨seedState D p.1.1 keys p.1.2, if (seedState D p.1.1 keys p.1.2).flag then some (.seeds, world) else none⟩ p.2
    simp only [prEvent_norm, StateT.run_bind] at h ⊢
    exact h
  · exact firstRunOf_keepsState prims runLimit D A _ ready FlagRecorded
      (fun state keys ok world hstart => by
        change (seedState D state keys ok).flag = true at hstart
        simp [hstart])
      (fun tree => firstTreeRunOf_flagRecorded prims D A.net _ ready tree) (fun _ _ h => h) (fun _ _ h => h) r hr
        hflag

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passReadyHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passReadyHop

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.passFlagFirst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.passFlagFirst
