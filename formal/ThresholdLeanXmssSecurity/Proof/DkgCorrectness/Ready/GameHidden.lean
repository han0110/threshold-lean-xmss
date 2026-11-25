import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.OneKey
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HeadLaw
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutBounds
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ready.Glue
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ready.GameSound

/-!
# The hidden keys at the end of the game

`ceremonyThen_split` states that one ceremony and then local steps are a PRSS setup and then a
program that draws only under the keys of that setup. So the program of a top tree, and the head and
the tail of a bottom tree, start with one setup each (`treeProgram_top_setupFirst`,
`bottomHead_setupFirst`, `bottomTail_setupFirst`). `treeRun_hiddenKeyBound` states that one run of
`tree` adds at most `treeSetups tree` keys under each hidden name, when the honest operators hold one
parameter. A bottom tree is split one time at the round count of its head. `firstRunOf_hiddenKeyBound`
is the walk of `firstRunOf` for each run with that bound (`HiddenRun`), and `hiddenAtEnd` proves
`HiddenAtEnd` by its instance at `streamTreeRun`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

open DigestBudgets (ClassBound StateBound)
open Draws (NoBad NoBadS SetupFirst)
open FirstCounts (remaining remaining_update mayRun_lt QuietKeeps FrameKeeps firstTreeRuns_walk firstSigning_walk)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)

attribute [local instance] Classical.propDecidable

attribute [local irreducible] wrongOutput

/-! ## The programs of a tree start with a setup -/

section Programs

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (D : C.Coalition)
  (K : Constants C E) (circuits : Circuits) (settings : Settings)

attribute [local instance] inhabitedField

/-- One ceremony and then local steps with no call of `PRG` are a PRSS setup and then a program that
draws only under the keys of that setup. -/
theorem ceremonyThen_split (i : C.Party) (keys : Keys C) (jobs : List Job) {β γ : Type}
    (g : Option (List (List Bit)) → StateT (ℕ × ℕ) (PartyM C E RealSpec) β) (hg : ∀ o, StateBound .stream (g o) 0)
    (st : ℕ × ℕ) (h : β × (ℕ × ℕ) → PartyM C E RealSpec γ) (hh : ∀ a, ClassBound .stream (h a) 0) :
    ∃ R : PrssKeys C → PartyM C E RealSpec γ,
      ((ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs >>= g).run
        st >>= h) = prssSetup i >>= R ∧ ∀ prss, NoBad D (NameKey i prss) (R prss) := by
  obtain ⟨f, hf, hnb⟩ := Draws.ceremonyRun_split (D := D) K circuits settings i keys jobs
  refine ⟨fun prss => (f prss >>= g).run st >>= h, ?_, fun prss => Draws.NoBad.bind
    ((Draws.NoBadS.bind (hnb prss) fun o => Draws.NoBadS.of_state (hg o)) st) fun a => Draws.NoBad.of_class (hh a)⟩
  rw [hf]
  simp only [bind_assoc, StateT.run_bind, StateT.run_lift, pure_bind]

omit [Field E] [Algebra Bit E] in
/-- The ceremonies of the top tree are its one ceremony and then local steps. -/
theorem ceremonyOutput_top_eq
    (lift : ∀ {α : Type}, OracleComp HashSpec α → StateT (ℕ × ℕ) (PartyM C E RealSpec) α)
    (hlift : ∀ {α : Type} (oa : OracleComp HashSpec α), StateBound .stream (lift oa) 0) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit)))) (top : TopTree) :
    ∃ g : Option (List (List Bit)) → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option TreeOutput),
      ceremonyOutput lift parameter run top .top = run topJobs >>= g ∧ ∀ o, StateBound .stream (g o) 0 := by
  unfold ceremonyOutput
  refine ⟨_, rfl, fun o => ?_⟩
  rcases o with _ | outputs
  · exact StateBound.pure _
  · exact StateBound.bind_zero (hlift _) fun _ => StateBound.pure _

/-- The program of the top tree starts with one setup. -/
theorem newTree_top_split (i : C.Party) (keys : Keys C) (top : TopTree) :
    ∃ R : PrssKeys C → PartyM C E RealSpec TreeOutput,
      newTree K circuits settings i keys top .top = prssSetup i >>= R ∧ ∀ prss, NoBad D (NameKey i prss) (R prss) := by
  obtain ⟨g, hg, hgb⟩ := ceremonyOutput_top_eq (fun oa => StateT.lift (oracleStep (tweakable oa)))
    (fun oa => DigestBudgets.lift_tweakable_bound (c := .stream) nofun oa) keys.parameter
    (ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys) top
  unfold newTree
  rw [hg]
  simp only [StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc]
  refine ceremonyThen_split D K circuits settings i keys topJobs g hgb _ _ (fun a => ?_)
  refine ClassBound.bind_zero (ClassBound.pure _) fun o => ?_
  rcases o with _ | output
  · exact ClassBound.failure
  · exact ClassBound.pure _

omit [Field E] [Algebra Bit E] in
/-- A local step of `Th` and then a program with no call of `PRG` make no call of `PRG`. -/
theorem lift_tweakable_bind_bound {β γ : Type} (oa : OracleComp HashSpec β)
    (f : β → StateT (ℕ × ℕ) (PartyM C E RealSpec) γ) (hf : ∀ b, StateBound .stream (f b) 0) :
    StateBound .stream (StateT.lift (oracleStep (tweakable oa)) >>= f) 0 :=
  StateBound.bind_zero (DigestBudgets.lift_tweakable_bound (c := .stream) nofun oa) hf

/-- The head of a bottom tree is its first ceremony and then local steps. -/
theorem firstPart_eq (i : C.Party) (keys : Keys C) (b : Fin (2 ^ layerHeight)) :
    ∃ g : Option (List (List Bit)) → StateT (ℕ × ℕ) (PartyM C E RealSpec)
        (Option (List (List Bit) × Digest × Randomizer × Encoding)),
      CheckTiming.firstPart K circuits settings i keys b =
        ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys (bottomJobs b)
          >>= g ∧ ∀ o, StateBound .stream (g o) 0 := by
  unfold CheckTiming.firstPart
  refine ⟨_, rfl, fun o => ?_⟩
  rcases o with _ | outputs
  · exact StateBound.pure _
  dsimp only
  generalize (merkleNode keys.parameter bottomLayer (fun e l => (bCpk b outputs e l).2.2) layerHeight b.val :
    OracleComp HashSpec Digest) = m1
  refine lift_tweakable_bind_bound m1 _ fun root => ?_
  refine lift_tweakable_bind_bound _ _ fun base => ?_
  refine lift_tweakable_bind_bound _ _ fun found => ?_
  rcases found with _ | ⟨randomness, encoding⟩
  · exact StateBound.pure _
  · exact StateBound.pure _

/-- The tail of a bottom tree is its second ceremony and then local steps. -/
theorem secondPart_eq (i : C.Party) (keys : Keys C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (x : List (List Bit) × Digest × Randomizer × Encoding) :
    ∃ g : Option (List (List Bit)) → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option TreeOutput),
      CheckTiming.secondPart K circuits settings i keys top b x =
        ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys
          (signJobs b x.2.2.2) >>= g ∧ ∀ o, StateBound .stream (g o) 0 := by
  unfold CheckTiming.secondPart
  refine ⟨_, rfl, fun o => ?_⟩
  rcases o with _ | values
  · exact StateBound.pure _
  dsimp only
  generalize (merklePath keys.parameter topLayer top.chainEnd (topKey b) : OracleComp HashSpec _) = m1
  refine lift_tweakable_bind_bound m1 _ fun path => ?_
  refine lift_tweakable_bind_bound _ _ fun topRoot => ?_
  split_ifs
  · exact StateBound.pure _
  · exact StateBound.pure _

/-- The head of a bottom tree starts with one setup. -/
theorem bottomHead_setupFirst {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight)) :
    SetupFirst D fun i => CheckTiming.bottomHead K circuits settings i (s.operators i) b := by
  intro j _
  beta_reduce
  unfold CheckTiming.bottomHead
  rcases hk : (s.operators j).keys with _ | keys <;> rcases ht : (s.operators j).top with _ | top
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · right
    obtain ⟨g, hg, hgb⟩ := firstPart_eq K circuits settings j keys b
    dsimp only
    rw [hg]
    refine ceremonyThen_split D K circuits settings j keys (bottomJobs b) g hgb _ _ (fun p => ?_)
    rcases p with ⟨_ | x, st⟩
    · exact ClassBound.failure
    · exact ClassBound.pure _

/-- The tail of a bottom tree after the head results `heads` starts with one setup. -/
theorem bottomTail_setupFirst {σ : Type} (s : RealState C σ) (b : Fin (2 ^ layerHeight))
    (heads : C.Party → Option ((List (List Bit) × Digest × Randomizer × Encoding) × (ℕ × ℕ))) :
    SetupFirst D fun i => (heads i).elim failure (CheckTiming.bottomTail K circuits settings i (s.operators i) b) := by
  intro j _
  beta_reduce
  rcases hh : heads j with _ | x
  · exact Or.inl rfl
  simp only [Option.elim]
  unfold CheckTiming.bottomTail
  rcases hk : (s.operators j).keys with _ | keys <;> rcases ht : (s.operators j).top with _ | top
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · right
    obtain ⟨g, hg, hgb⟩ := secondPart_eq K circuits settings j keys top b x.1
    dsimp only
    rw [hg]
    refine ceremonyThen_split D K circuits settings j keys _ g hgb _ _ (fun p => ?_)
    rcases p with ⟨_ | out, st⟩
    · exact ClassBound.failure
    · exact ClassBound.pure _

/-- The program of the top tree starts with one setup. -/
theorem treeProgram_top_setupFirst {σ : Type} (s : RealState C σ) :
    SetupFirst D fun i => treeProgram K circuits settings i (s.operators i) .top := by
  intro j _
  beta_reduce
  unfold treeProgram
  rcases hk : (s.operators j).keys with _ | keys
  · exact Or.inl rfl
  · exact Or.inr (newTree_top_split D K circuits settings j keys _)

end Programs

/-! ## The hidden keys of one run of a tree -/

section TreeRun

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

attribute [local instance] inhabitedField

/-- The honest operators with keys hold one parameter. -/
def ParamAgree (D : C.Coalition) (operators : C.Party → OperatorState C) : Prop :=
  ∃ parameter : PublicParameter, ∀ i, i ∉ D.1 → ∀ keys, (operators i).keys = some keys → keys.parameter = parameter

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A world whose new hidden cells are under the cached answer of one input for each name has one more
key under each name. -/
theorem hiddenKeyBound_of_cellsIn {w w' : StreamState C} {m : ℕ} (input : KeyName C → Query C)
    (hb : HiddenKeyBound w.2 m)
    (hc : Draws.CellsIn (fun N k => (∃ ρ idx position, w.2 ((N, k), ρ, idx, position) ≠ none) ∨
      w'.1 (input N) = some k) w') :
    HiddenKeyBound w'.2 (m + 1) := by
  intro N
  obtain ⟨K0, hK0, hcells⟩ := hb N
  refine ⟨K0 ∪ (w'.1 (input N)).toFinset, ?_, fun key ρ idx position hcell => ?_⟩
  · calc (K0 ∪ (w'.1 (input N)).toFinset).card ≤ K0.card + (w'.1 (input N)).toFinset.card :=
          Finset.card_union_le _ _
      _ ≤ m + 1 := by
          gcongr
          cases w'.1 (input N) <;> simp
  · rcases hc N key ρ idx position hcell with ⟨ρ', idx', position', hold⟩ | hnew
    · exact Finset.mem_union_left _ (hcells key ρ' idx' position' hold)
    · exact Finset.mem_union_right _ (Option.mem_toFinset.2 hnew)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A phase whose honest programs start with a setup adds at most one key under each hidden name. -/
theorem phase_hiddenKeyBound (D : C.Coalition) {β : Type} (net : Adversary C E Unit PEmpty PEmpty) (fuel : ℕ)
    (st : net.State) (program : C.Party → PartyM C E RealSpec β) (h : SetupFirst D program) (w : StreamState C)
    (m : ℕ) (hb : HiddenKeyBound w.2 m) :
    ∀ r ∈ support ((simulateQ (streamWorld prims D)
        (executePhase worldRoles D net noFunctionality fuel st program)).run w), HiddenKeyBound r.2.2 (m + 1) := by
  intro r hr
  obtain ⟨input, hc⟩ := Draws.executePhase_oneKey (D := D) prims net fuel st program h w r hr
  exact hiddenKeyBound_of_cellsIn input hb hc

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation with no call of `PRG` on the free copy keeps the hidden cache. -/
theorem simulateQ_hidden_eq (D : C.Coalition) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (h : IsQueryBoundP oa (HonestIn .stream) 0) :
    ∀ w, ∀ y ∈ support ((simulateQ (streamWorld prims D) oa).run w), y.2.2 = w.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro w y hy
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rfl
  | query_bind t k ih =>
    intro w y hy
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have ht : ¬ HonestIn (C := C) .stream t := by
      rcases h.1 with h1 | h1
      · exact h1
      · omega
    have hk := h.2 z.1
    simp only [ht, ↓reduceIte] at hk
    have hz' : z.2.2 = w.2 := by
      rcases t with t | (n | q | x)
      · obtain ⟨r, -, rfl⟩ := mem_support_onHash _ w z hz
        rfl
      · obtain ⟨r, -, rfl⟩ := mem_support_onHash _ w z hz
        rfl
      · obtain ⟨r, -, rfl⟩ := mem_support_onHash _ w z hz
        rfl
      · exact absurd rfl ht
    rw [ih z.1 hk z.2 y hy, hz']

/-- The phase of one run of `tree` adds at most `treeSetups tree` keys under each hidden name, when
the honest operators hold one parameter. A bottom tree is split one time at the round count of its
head. -/
theorem treePhase_hiddenKeyBound (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) (w : StreamState C) (m : ℕ) (hpar : ParamAgree D s.operators)
    (hb : HiddenKeyBound w.2 m) :
    ∀ r ∈ support ((simulateQ (streamWorld prims D) (executePhase worldRoles D net noFunctionality
      (treeFuel circuits settings) s.adversary fun i => treeProgram K circuits settings i (s.operators i) tree)).run w),
      HiddenKeyBound r.2.2 (m + treeSetups tree) := by
  intro r hr
  cases tree with
  | top =>
    exact phase_hiddenKeyBound prims D net _ _ _ (treeProgram_top_setupFirst D K circuits settings s) w m hb r hr
  | bottom b =>
    obtain ⟨parameter, hparam⟩ := hpar
    have hn := headFuel circuits settings parameter b
    have hprog : (fun i => treeProgram K circuits settings i (s.operators i) (.bottom b)) =
        fun i => CheckTiming.bottomHead K circuits settings i (s.operators i) b >>=
          CheckTiming.bottomTail K circuits settings i (s.operators i) b :=
      funext fun i => CheckTiming.treeProgram_bottom K circuits settings i (s.operators i) b
    have hfuel : treeFuel circuits settings = CheckTiming.firstRounds circuits settings parameter (.bottom b) +
        (treeFuel circuits settings - CheckTiming.firstRounds circuits settings parameter (.bottom b)) := by omega
    rw [hprog, hfuel] at hr
    rw [OracleComp.support_eq_of_evalDistEq (WorldSplit.executePhase_split prims D net _ _ s.adversary _ _
      (fun i hi => CheckTiming.timed_bottomHead K circuits settings parameter i (s.operators i) b (hparam i hi)) w)]
      at hr
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨r1, hr1, hr⟩ := hr
    have h1 := phase_hiddenKeyBound prims D net _ _ _ (bottomHead_setupFirst D K circuits settings s b) w m hb r1 hr1
    have h2 := phase_hiddenKeyBound prims D net _ _ _ (bottomTail_setupFirst D K circuits settings s b r1.1.2) r1.2
      (m + 1) h1 r hr
    simpa [treeSetups, Nat.add_assoc] using h2

/-- One run of `tree` adds at most `treeSetups tree` keys under each hidden name, when the honest
operators hold one parameter. The monitor writes no hidden cell. -/
theorem streamTreeRun_hiddenKeyBound (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) (w : StreamState C) (m : ℕ) (hpar : ParamAgree D s.operators)
    (hb : HiddenKeyBound w.2 m) :
    ∀ z ∈ support ((streamTreeRun prims K circuits settings D net tree s).run w),
      HiddenKeyBound z.2.2 (m + treeSetups tree) := by
  intro z hz
  unfold streamTreeRun at hz
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨r, hr, y, hy, rfl⟩ := hz
  have hmon : y.2.2 = r.2.2 := simulateQ_hidden_eq prims D _ ((noCall_iff _ _).1
    (GameCount.wrongOutput_noCall D _ (fun t ht h =>
      FirstCounts.monitorCall_not_adds (c := .stream) nofun ht (adds_of_honestIn h)) _ _ _)) r.2 y hy
  rw [show (((r.1, y.1), y.2) : _ × StreamState C).2.2 = y.2.2 from rfl, hmon]
  exact treePhase_hiddenKeyBound prims K circuits settings D net tree s w m hpar hb r hr

end TreeRun

/-! ## The walk of the game -/

section Walk

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (D : C.Coalition)

attribute [local instance] inhabitedField

/-- The potential of the walk. The honest operators hold one parameter, and under each name the keys
of the hidden cells with the setups of the runs that remain are at most `k`. -/
def HiddenPot {σ : Type} (k : ℕ) (s : FirstState C σ) (w : StreamState C) : Prop :=
  ParamAgree D s.real.operators ∧ ∀ name, ∃ keys : Finset HashOutput,
    keys.card + remaining runLimit treeSetups s.real.runs ≤ k ∧
      ∀ key ρ idx position, w.2 ((name, key), ρ, idx, position) ≠ none → key ∈ keys

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem hiddenPot_mono {σ : Type} : ∀ k k' (s : FirstState C σ) w, k ≤ k' →
    HiddenPot runLimit D k s w → HiddenPot runLimit D k' s w := by
  rintro k k' s w hk ⟨hp, h⟩
  exact ⟨hp, fun name => by
    obtain ⟨keys, hc, hcover⟩ := h name
    exact ⟨keys, hc.trans hk, hcover⟩⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A computation of the world with no call of `PRG` on the free copy keeps the potential. -/
theorem inStream_hiddenMoves {σ β : Type} (oa : OracleComp (WorldSpec C) β)
    (h : IsQueryBoundP oa (HonestIn .stream) 0) :
    FirstCounts.Moves (HiddenPot runLimit D) 0 (inStream (σ := σ) prims D oa) := by
  rintro k s w hs z hz
  simp only [inStream, StateT.run_lift, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  have he := simulateQ_hidden_eq prims D oa h w y hy
  refine ⟨hs.1, fun name => ?_⟩
  obtain ⟨keys, hc, hcover⟩ := hs.2 name
  refine ⟨keys, by simpa using hc, fun key ρ idx position hcell => hcover key ρ idx position ?_⟩
  change y.2.2 _ ≠ none at hcell
  rwa [he] at hcell

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Each run of the run `run` adds at most `treeSetups tree` keys under each hidden name, when the
honest operators hold one parameter. `streamTreeRun_hiddenKeyBound` states it for `streamTreeRun`. -/
def HiddenRun {σ : Type} (run : RunOf C σ) : Prop :=
  ∀ (tree : Tree) (s : RealState C σ) (w : StreamState C) (m : ℕ), ParamAgree D s.operators →
    HiddenKeyBound w.2 m → ∀ z ∈ support ((run tree s).run w), HiddenKeyBound z.2.2 (m + treeSetups tree)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A run of `tree` that the game allows keeps the potential. Its setups come from the runs that
remain. Its vote keeps the hidden streams. -/
theorem firstTreeRun_hiddenPot (net : Adversary C E Unit PEmpty PEmpty) (run : RunOf C net.State)
    (hhidden : HiddenRun D run) (ready : RealState C net.State → StreamState C → Prop) (tree : Tree)
    (k : ℕ) (s : FirstState C net.State) (w : StreamState C)
    (hs : HiddenPot runLimit D k s w) (hrun : s.real.runs tree < runLimit) :
    ∀ z ∈ support (((firstTreeRunOf prims D net run ready tree).run s).run w),
      HiddenPot runLimit D k z.1.2 z.2 := by
  intro z hz
  simp only [firstTreeRunOf, inStream, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc,
    StateT.run_set, StateT.run_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨x, hx, y, hy, rfl⟩ := hz
  have he := simulateQ_hidden_eq prims D _ (FirstCounts.voteRound_honestIn .stream (by decide) D net x.1.1.1 _
    fun j q hq => by
      obtain ⟨output, -, rfl⟩ := Option.map_eq_some_iff.1 hq
      exact FirstCounts.queryClass_treeVote tree output) x.2 y hy
  obtain ⟨hpar, hcells⟩ := hs
  have e := remaining_update runLimit treeSetups s.real.runs tree hrun
  have hb : HiddenKeyBound w.2 (k - remaining runLimit treeSetups s.real.runs) := fun name => by
    obtain ⟨keys, hc, hcover⟩ := hcells name
    exact ⟨keys, by omega, hcover⟩
  have hk : remaining runLimit treeSetups s.real.runs ≤ k := by
    obtain ⟨keys, hc, -⟩ := hcells (.parameter)
    omega
  have h := hhidden tree s.real w _ hpar hb x hx
  refine ⟨?_, fun name => ?_⟩
  · obtain ⟨parameter, hp⟩ := hpar
    exact ⟨parameter, fun i hi keys hkeys => hp i hi keys (by
      change ((s.real.operators i).keep (committed y.1.2 x.1.1.2 i) tree).keys = some keys at hkeys
      rwa [Ready.keep_keys] at hkeys)⟩
  · obtain ⟨keys, hc, hcover⟩ := h name
    refine ⟨keys, ?_, fun key ρ idx position hcell => hcover key ρ idx position ?_⟩
    · change keys.card + remaining runLimit treeSetups (Function.update s.real.runs tree (s.real.runs tree + 1)) ≤ k
      omega
    change y.2.2 _ ≠ none at hcell
    rwa [he] at hcell


omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- No computation makes a call of the empty predicate. -/
theorem isQueryBoundP_false {ι α : Type} {spec : OracleSpec ι} {h : DecidablePred fun _ : ι => False}
    (oa : OracleComp spec α) : @IsQueryBoundP _ _ _ oa (fun _ => False) h 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl not_false, fun u => by simpa only [↓reduceIte] using ih u⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem hiddenPot_quiet {σ : Type} : QuietKeeps prims D .stream (σ := σ) (HiddenPot runLimit D) := fun oa h =>
  inStream_hiddenMoves prims runLimit D oa (honestIn_of_adds h)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem hiddenPot_frame {σ : Type} : FrameKeeps (C := C) (σ := σ) (HiddenPot runLimit D) := by
  intro k s s' w hops hruns hpot
  obtain ⟨hpar, hcells⟩ := hpot
  refine ⟨by rw [hops]; exact hpar, fun name => ?_⟩
  obtain ⟨keys, hc, hcover⟩ := hcells name
  exact ⟨keys, by rw [hruns]; exact hc, hcover⟩

end Walk

/-! ## The hidden keys at the end of the game -/

section End

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

attribute [local instance] inhabitedField

/-- The setups of `runLimit` runs of each tree are `gameSetups`. -/
theorem remaining_treeSetups : remaining runLimit treeSetups (fun _ => 0) = gameSetups runLimit := by
  simp only [remaining, Nat.sub_zero, treeSetups, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    gameSetups]
  ring

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The honest operators that leave the seed generation with keys hold one parameter. -/
theorem paramAgree_start (D : C.Coalition) (A : DkgTsigAdversary C E) (state : A.net.State)
    (keys : C.Party → Option (Keys C)) (world : StreamState C)
    (hy : ((state, keys), world) ∈ support ((simulateQ (streamWorld prims D) (realExecution D A.net noFunctionality
      setupRounds (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [])).run (∅, ∅))) :
    ParamAgree D (startState D state keys).operators := by
  unfold realExecution at hy
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hy
  obtain ⟨a, -, hy⟩ := hy
  have hagree := SetupParameter.seedParameterAgree (E := E) prims D A.net a.1 a.2 _ hy
  by_cases h : ∃ j, j ∉ D.1 ∧ ∃ kj, keys j = some kj
  · obtain ⟨j, hj, kj, hkj⟩ := h
    exact ⟨kj.parameter, fun i hi ki hki => hagree i j ki kj hi hj hki hkj⟩
  · refine ⟨0, fun i hi ki hki => absurd ⟨i, hi, ki, hki⟩ h⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The hidden keys at the end of `firstRunOf`, for each readiness test and each run with the bound
`HiddenRun`. Each name has at most the setups of `runLimit` runs of each tree. -/
theorem firstRunOf_hiddenKeyBound (D : C.Coalition) (A : DkgTsigAdversary C E) (run : RunOf C A.net.State)
    (hhidden : HiddenRun D run) (ready : RealState C A.net.State → StreamState C → Prop) :
    ∀ r ∈ support (firstRunOf prims runLimit D A run ready),
      HiddenKeyBound r.2.2 (gameSetups runLimit) := by
  intro r hr
  unfold firstRunOf at hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨y, hy, hr⟩ := hr
  rcases y with ⟨⟨state, keys⟩, world⟩
  simp only [StateT.run_get, support_pure, Set.mem_singleton_iff, exists_eq_left, StateT.run_pure] at hr
  obtain ⟨t, ht, x, ⟨z, hz, hx⟩, rfl⟩ := hr
  have hseed := (GameCount.bound_iff _ _ _).1 (DigestBudgets.seedHonest (C := C) (E := E) (c := .stream) nofun D A.net)
  have hworld : world.2 = ∅ := simulateQ_hidden_eq prims D _ hseed (∅, ∅) _ hy
  have hvote : t.2.2 = world.2 := simulateQ_hidden_eq prims D _ (FirstCounts.voteRound_honestIn .stream (by decide)
    D A.net state (fun i => (keys i).map seedVote) fun j q hq => by
      obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.1 hq
      rfl) world t ht
  have hpot : HiddenPot runLimit D (remaining runLimit treeSetups (fun _ => 0))
      (⟨seedState D t.1.1 keys t.1.2, if (seedState D t.1.1 keys t.1.2).flag then some (.seeds, world) else none⟩ :
        FirstState C A.net.State) t.2 := by
    obtain ⟨parameter, hp⟩ := paramAgree_start prims D A state keys world hy
    refine ⟨⟨parameter, fun i hi k hk => hp i hi k (Vote.committed_eq_some hk)⟩,
      fun name => ⟨∅, by simp; rfl, fun key ρ idx position h => ?_⟩⟩
    rw [hvote, hworld] at h
    exact absurd rfl h
  have hcall : ∀ t, FirstCounts.Moves (σ := A.net.State) (HiddenPot runLimit D) 0
      (inStream prims D (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)))) := by
    intro t
    refine inStream_hiddenMoves prims runLimit D _ ?_
    rw [ThresholdLeanXmssSecurity.adversary_query]
    change IsQueryBoundP (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _)
      (HonestIn .stream) 0
    rw [isQueryBoundP_query_iff]
    exact fun h => h.elim
  obtain ⟨-, hcells⟩ := FirstCounts.moves_bind
    (firstTreeRuns_walk prims runLimit D A.net (HiddenPot runLimit D) run ready .top
      (firstTreeRun_hiddenPot prims runLimit D A.net run hhidden ready .top) runLimit)
    (fun _ => firstSigning_walk prims runLimit D .stream nofun
      (DigestBudgets.signQuiet nofun) A run (HiddenPot runLimit D)
      (hiddenPot_mono runLimit D) ready
      (fun tree => firstTreeRun_hiddenPot prims runLimit D A.net run hhidden ready tree)
      (hiddenPot_quiet prims runLimit D) (hiddenPot_frame runLimit D) (fun _ => False) (fun _ h => h) (fun t => by simpa using hcall t) 0
      fun _ _ => isQueryBoundP_false _)
    _ _ t.2 hpot x (by rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff]; exact ⟨z, hz, hx⟩)
  intro name
  obtain ⟨keys', hc, hcover⟩ := hcells name
  refine ⟨keys', ?_, hcover⟩
  rw [← remaining_treeSetups runLimit]
  omega

/-- At the end of the game each hidden name has at most `gameSetups` keys. -/
theorem hiddenAtEnd : HiddenAtEnd prims K circuits settings runLimit := fun D A _ _ r hr =>
  firstRunOf_hiddenKeyBound prims runLimit D A _
    (fun tree s w m => streamTreeRun_hiddenKeyBound prims K circuits settings D A.net tree s w m) _ r hr

end End

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.hiddenAtEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.hiddenAtEnd

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.streamTreeRun_hiddenKeyBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.streamTreeRun_hiddenKeyBound
