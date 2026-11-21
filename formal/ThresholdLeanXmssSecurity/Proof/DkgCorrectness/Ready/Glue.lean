import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ready.Budgets
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Route
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.RunsUnion

/-!
# The readiness hop at the test `RunReadyL`

Part 1 carries `HiddenProvenance` through `firstRunOf` for each test and each run that keeps it
(`firstRunOf_provInv`, with `firstRunWith_provInv` as its instance) and proves three of its four
preservation statements. Part 2 proves `ReadyHopL` from the four budget parts
at the test `RunReadyL` (`readyHopL_of_budgets`). Part 3 couples the game at `RunReadyL` with the game
at `RunReady` (`firstRunWith_coupled`), so that each budget part at `RunReady` gives the part at
`RunReadyL`. `readyHopL_of_ends` proves `ReadyHopL` from `Ready.SoundAtEnd`, `HiddenAtEnd` and
`ProvenanceTreeRun`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

open Ready (Keeps KeepsT keeps_pure keeps_bind keeps_get_bind keeps_get keeps_modify keeps_lift keepsT_lift
  keepsT_bind keepsT_simulateQ)

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-! ## Generic walk lemmas -/

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The answer of an honest operator is a lifted computation of the world with no call of the class
`stream`. It is the form of `Ready.operatorAnswer_keeps` and of `DigestBudgets.signQuiet`. -/
theorem operatorAnswer_world {σ : Type} (D : C.Coalition) (operators : C.Party → OperatorState C)
    (operator : OperatorState C) (e : KeyIndex) (q : TsigQuery C) (t : TsigState C) :
    ∃ X : OracleComp (WorldSpec C) (TsigSpec C q × TsigState C),
      (operatorAnswer (m := FirstM C σ) (firstLift prims D) (firstValue prims D operators) operator e q).run t =
        StateT.lift (simulateQ (streamWorld prims D) X) ∧ IsQueryBoundP X (FirstCounts.Adds .stream) 0 := by
  unfold operatorAnswer
  split
  · rename_i keys top _ _ _ _
    rw [ownAnswer_run]
    let ψ := simulateQ' (streamWorld prims D)
    let freeLift : ∀ {β : Type}, OracleComp (RoSpec C) β → OracleComp (WorldSpec C) β :=
      fun oa => free (liftComp oa _)
    let value : Point → OracleComp (WorldSpec C) Digest :=
      fun x => freeLift (prfValue (gameSeeds D fun i => (operators i).keys) x)
    let dealt := dealtWith freeLift keys.parameter (fun _ => keys) top value
    have hdealt : SeedHitProof.Dealt.hmap (streamLift C σ) (SeedHitProof.Dealt.hmap ψ dealt) =
        dealtWith (m := FirstM C σ) (fun oa => firstLift prims D oa) keys.parameter (fun _ => keys) top
          (firstValue prims D operators) := by
      simp only [SeedHitProof.Dealt.hmap, dealt, dealtWith, SeedHitProof.hom_map, SeedHitProof.hom_referenceTree]
      rfl
    rw [← hdealt]
    let t' : TsigState C := { t with trees := fun b => some (operator.bottom b) }
    have hom₁ := SeedHitProof.hom_tsigOracles (streamLift C σ) (fun oa => ψ (freeLift oa))
      (SeedHitProof.Dealt.hmap ψ dealt) q t'
    have hom₂ := SeedHitProof.hom_tsigOracles ψ freeLift dealt q t'
    change ∃ X, (tsigOracles (fun oa => streamLift C σ (ψ (freeLift oa)))
      (SeedHitProof.Dealt.hmap (streamLift C σ) (SeedHitProof.Dealt.hmap ψ dealt)) q).run t' =
        StateT.lift (simulateQ (streamWorld prims D) X) ∧ IsQueryBoundP X (FirstCounts.Adds .stream) 0
    rw [← hom₁, ← hom₂]
    exact ⟨_, rfl, DigestBudgets.signQuiet (c := .stream) (by decide) D operators keys top q t'⟩
  · exact ⟨pure (noAnswer q, t), StateT.ext fun s => by simp, trivial⟩

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The answer of an honest operator keeps each invariant that holds in each larger world. It is
`Ready.operatorAnswer_keeps` for a general invariant. -/
theorem operatorAnswer_keepsG {σ : Type} (I : FirstState C σ → StreamState C → Prop)
    (grow : ∀ s w w', I s w → w ≤ w' → I s w') (D : C.Coalition) (operators : C.Party → OperatorState C)
    (operator : OperatorState C) (e : KeyIndex) (q : TsigQuery C) :
    KeepsT I (operatorAnswer (m := FirstM C σ) (firstLift prims D) (firstValue prims D operators) operator e q) := by
  intro t
  obtain ⟨X, hX, -⟩ := operatorAnswer_world prims D operators operator e q t
  rw [hX]
  exact keeps_lift grow (Ready.simulateQ_le prims D X)

/-! ## Part 1. The provenance through the game -/

/-- The saved snapshot of the first bad record has the provenance. -/
def SnapProvenance (D : C.Coalition) {σ : Type} (s : FirstState C σ) : Prop :=
  ∀ stage w, s.first = some (stage, w) → HiddenProvenance D w

/-- The invariant of the provenance walk. The present world and the saved snapshot have the
provenance. A witness in the final cache alone could come after the snapshot. -/
def ProvInv (D : C.Coalition) {σ : Type} (s : FirstState C σ) (world : StreamState C) : Prop :=
  HiddenProvenance D world ∧ SnapProvenance D s

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem keeps_provInv {D : C.Coalition} {σ α : Type} {m : FirstM C σ α}
    (hsnap : Keeps (fun s (_ : StreamState C) => SnapProvenance D s) m)
    (hworld : ∀ s w, HiddenProvenance D w → ∀ z ∈ support ((m.run s).run w), HiddenProvenance D z.2) :
    Keeps (ProvInv D) m :=
  fun s w hs z hz => ⟨hworld s w hs.1 z hz, hsnap s w hs.2 z hz⟩

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem inStream_provInv (D : C.Coalition) {σ β : Type} {oa : OracleComp (WorldSpec C) β}
    (h : KeepsProvenance prims D oa) : Keeps (ProvInv D) (inStream (σ := σ) prims D oa) := by
  refine keeps_provInv (keeps_lift (fun _ _ _ h _ => h) (Ready.simulateQ_le prims D oa)) fun s w hw z hz => ?_
  simp only [inStream, StateT.run_lift, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact h w hw y hy

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A world with the provenance keeps it when its hash cache grows and its hidden cache stays. -/
theorem hiddenProvenance_of_le {D : C.Coalition} {w w' : StreamState C} (hw : HiddenProvenance D w)
    (h₁ : w.1 ≤ w'.1) (h₂ : w'.2 = w.2) : HiddenProvenance D w' := by
  intro name key ρ idx position hname hcell
  rw [h₂] at hcell
  obtain ⟨kind, parts, h⟩ := hw name key ρ idx position hname hcell
  exact ⟨kind, parts, h₁ h⟩

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A call of `streamWorld` other than a free `PRG` call keeps the provenance. Only a free `PRG`
call under a hidden name writes the hidden cache. -/
theorem streamWorld_keepsProvenance (D : C.Coalition) (t : (WorldSpec C).Domain)
    (ht : ∀ x, t ≠ .inr (.inr (.inr x))) :
    ∀ w, HiddenProvenance D w → ∀ z ∈ support ((streamWorld prims D t).run w), HiddenProvenance D z.2 := by
  intro w hw z hz
  refine hiddenProvenance_of_le hw (Ready.streamWorld_le prims D t w z hz).1 ?_
  rcases t with ((u | y) | (u | q | x))
  · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hz
    rfl
  · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hz
    rfl
  · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hz
    rfl
  · obtain ⟨r, -, rfl⟩ := FirstCounts.onHash_support hz
    rfl
  · exact absurd rfl (ht x)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- A computation of the world with no call of `p` keeps the provenance, when each free `PRG` call is
a call of `p`. -/
theorem keepsProvenance_of_noCall (D : C.Coalition) (p : (WorldSpec C).Domain → Prop)
    (hp : ∀ x, p (.inr (.inr (.inr x)))) {α : Type} (oa : OracleComp (WorldSpec C) α) :
    IsQueryBoundP oa p 0 → KeepsProvenance prims D oa := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro _ w hw z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hw
  | query_bind t f ih =>
    intro h w hw z hz
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have hpt : ¬ p t := h.1.resolve_right (lt_irrefl 0)
    have hcont : IsQueryBoundP (f y.1) p 0 := by simpa only [hpt, ite_false] using h.2 y.1
    exact ih y.1 hcont y.2 (streamWorld_keepsProvenance prims D t (fun x hx => hpt (hx ▸ hp x)) w hw y hy) z hz

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- `ProvenanceSeedGen`. The seed generation makes no honest call of the class `stream`. -/
theorem provenanceSeedGen : ProvenanceSeedGen prims (C := C) (E := E) := fun D A =>
  keepsProvenance_of_noCall prims D (HonestIn .stream) (fun _ => rfl) _
    ((GameCount.bound_iff _ _ _).1 (DigestBudgets.seedHonest (c := .stream) (by decide) D A.net))

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- `ProvenanceCounted`. A counted call goes to the hash cache. -/
theorem provenanceCounted : ProvenanceCounted prims (C := C) := fun D _ oa =>
  keepsProvenance_of_noCall prims D (HonestIn .stream) (fun _ => rfl) _ (DigestBudgets.honestIn_adversary .stream oa)

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- `ProvenanceSigning`. The answers and `F` make no call of the class `stream`. -/
theorem provenanceSigning : ProvenanceSigning prims (C := C) := by
  intro D σ operators operator e q st fs x world hw
  refine ⟨fun r hr => ?_, fun r hr => ?_⟩
  · obtain ⟨X, hX, hbound⟩ := operatorAnswer_world prims D operators operator e q st
    rw [hX] at hr
    simp only [StateT.run_lift, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hr
    obtain ⟨y, hy, rfl⟩ := hr
    exact keepsProvenance_of_noCall prims D _ (fun _ => rfl) X hbound world hw y hy
  · simp only [firstValue, firstLift, inStream, StateT.run_lift, StateT.run_bind, mem_support_bind_iff,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨y, hy, rfl⟩ := hr
    exact keepsProvenance_of_noCall prims D (HonestIn .stream) (fun _ => rfl) _
      (DigestBudgets.free_liftComp_bound .stream _ (fun _ => Iff.rfl) _ 0
        ((SigningSelectionProof.noCall_iff _ _).1
        (DigestBudgets.noCall_of_onlySign (by decide) (GameCount.onlySign_prfValue _ x)))) world hw y hy

/-- Each run of the run `run` keeps the provenance of the hidden keys. `ProvenanceTreeRun` states it for
`streamTreeRun`. -/
def ProvenanceRun (D : C.Coalition) {σ : Type} (run : RunOf C σ) : Prop :=
  ∀ (tree : Tree) (s : RealState C σ) (world : StreamState C), HiddenProvenance D world →
    ∀ r ∈ support ((run tree s).run world), HiddenProvenance D r.2

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstTreeRunOf_provInv (D : C.Coalition) {σ : Type} (run : RunOf C σ) (treeRun : ProvenanceRun D run)
    (ready : RealState C σ → StreamState C → Prop) (tree : Tree) :
    Keeps (ProvInv D) (firstTreeRunOf run ready tree) := by
  intro s world hs z hz
  unfold firstTreeRunOf at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, mem_support_bind_iff, StateT.run_set,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
  have hafter : HiddenProvenance D x.2 := treeRun tree s.real world hs.1 x hx
  refine ⟨hafter, fun stage w hw => ?_⟩
  change ((s.first <|> if ready s.real world then none
    else some (.unready tree (s.real.runs tree), world)) <|>
      if x.1.2 then some (.run tree (s.real.runs tree), x.2) else none) = some (stage, w) at hw
  cases hfirst : s.first with
  | some v =>
    rw [hfirst, Ready.some_orElse, Ready.some_orElse] at hw
    exact hs.2 stage w (hfirst.trans hw)
  | none =>
    rw [hfirst, Ready.none_orElse] at hw
    by_cases hready : ready s.real world
    · rw [ite_eq_left hready, Ready.none_orElse] at hw
      split_ifs at hw
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
      exact hafter
    · rw [ite_eq_right hready, Ready.some_orElse] at hw
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
      exact hs.1

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstTreeRunsOf_provInv (D : C.Coalition) {σ : Type} (run : RunOf C σ) (treeRun : ProvenanceRun D run)
    (ready : RealState C σ → StreamState C → Prop) (tree : Tree) :
    ∀ count, Keeps (ProvInv D) (firstTreeRunsOf runLimit D run ready tree count)
  | 0 => keeps_pure _
  | count + 1 => by
    unfold firstTreeRunsOf
    refine keeps_get_bind fun s => ?_
    split_ifs
    · exact keeps_bind (firstTreeRunOf_provInv D run treeRun ready tree) fun _ =>
        firstTreeRunsOf_provInv D run treeRun ready tree count
    · exact keeps_pure _

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstValue_provInv (signing : ProvenanceSigning prims (C := C)) (D : C.Coalition) {σ : Type}
    (operators : C.Party → OperatorState C) (x : Point) :
    Keeps (ProvInv D) (firstValue (σ := σ) prims D operators x) :=
  keeps_provInv (keeps_lift (fun _ _ _ h _ => h) (Ready.simulateQ_le prims D _))
    fun s w hw z hz =>
      (signing D operators (operators ⟨0, by have := C.one_le_t; unfold Committee.n; omega⟩)
        (topKey ⟨0, Nat.two_pow_pos _⟩) (.tree ⟨0, Nat.two_pow_pos _⟩) ⟨D.1, fun _ => none, [], fun _ => none⟩
        s x w hw).2 z hz

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstTreeRequestOf_provInv (signing : ProvenanceSigning prims (C := C)) (D : C.Coalition) {σ : Type}
    (run : RunOf C σ) (treeRun : ProvenanceRun D run) (ready : RealState C σ → StreamState C → Prop)
    (b : Fin (2 ^ layerHeight)) :
    Keeps (ProvInv D) (firstTreeRequestOf prims runLimit D run ready b) := by
  unfold firstTreeRequestOf
  refine keeps_bind (firstTreeRunsOf_provInv runLimit D run treeRun ready _ 1)
    fun _ => keeps_get_bind fun s => ?_
  split
  · exact keeps_bind (firstValue_provInv prims signing D _ _) fun _ => keeps_pure _
  · exact keeps_pure _

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstSignRequest_provInv (signing : ProvenanceSigning prims (C := C)) (D : C.Coalition) {σ : Type}
    (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    KeepsT (ProvInv D) (firstSignRequest (σ := σ) prims D i e q) := by
  unfold firstSignRequest
  refine keepsT_bind (keepsT_lift (keeps_modify _ fun s w hs => hs)) fun _ =>
    keepsT_bind (keepsT_lift keeps_get) fun s => fun t => ?_
  exact keeps_provInv (operatorAnswer_keepsG prims _ (fun _ _ _ h _ => h) D _ _ e q t)
    fun fs w hw z hz => (signing D s.real.operators (s.real.operators i) e q t fs (.randomizer topLayer e) w hw).1 z hz

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstOraclesOf_provInv (signing : ProvenanceSigning prims (C := C)) (D : C.Coalition) {σ : Type}
    (run : RunOf C σ) (treeRun : ProvenanceRun D run) (ready : RealState C σ → StreamState C → Prop)
    (q : TsigQuery C) :
    KeepsT (ProvInv D) (firstOraclesOf prims runLimit D run ready q) := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact fun t => keeps_pure _
  · exact keepsT_lift (firstTreeRequestOf_provInv prims runLimit signing D run treeRun ready b)
  · exact firstSignRequest_provInv prims signing D i e _
  · exact firstSignRequest_provInv prims signing D i e _

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstSigningOf_provInv (counted : ProvenanceCounted prims (C := C))
    (signing : ProvenanceSigning prims (C := C)) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (run : RunOf C A.net.State) (treeRun : ProvenanceRun D run) (ready : RealState C A.net.State → StreamState C → Prop) :
    Keeps (ProvInv D) (firstSigningOf prims runLimit D A run ready) := by
  unfold firstSigningOf
  refine keeps_get_bind fun s => ?_
  split
  · refine keeps_bind (keepsT_simulateQ _ (fun q => ?_) _ _) fun _ => keeps_pure _
    rcases q with t | q | q
    · exact keepsT_lift (inStream_provInv prims D (counted D _))
    · exact firstOraclesOf_provInv prims runLimit signing D run treeRun ready q
    · rcases q with _ | state
      · exact keepsT_lift (keeps_bind keeps_get fun _ => keeps_pure _)
      · exact keepsT_lift (keeps_modify _ fun s w hs => hs)
  · exact keeps_pure _

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
/-- The walk of the game for each run that keeps the provenance. Each final state of `firstRunOf`,
for each test, has the provenance in its final world and in its saved snapshot. -/
theorem firstRunOf_provInv (seedGen : ProvenanceSeedGen prims (C := C) (E := E))
    (counted : ProvenanceCounted prims (C := C)) (signing : ProvenanceSigning prims (C := C)) (D : C.Coalition)
    (A : DkgTsigAdversary C E) (run : RunOf C A.net.State) (treeRun : ProvenanceRun D run)
    (ready : RealState C A.net.State → StreamState C → Prop) :
    ∀ r ∈ support (firstRunOf prims runLimit D A run ready), ProvInv D r.1 r.2 := by
  intro r hr
  unfold firstRunOf at hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨y, hy, hr⟩ := hr
  rcases y with ⟨⟨state, keys⟩, world⟩
  simp only [StateT.run_get, support_pure, Set.mem_singleton_iff, exists_eq_left, StateT.run_pure] at hr
  obtain ⟨x, ⟨z, hz, hx⟩, rfl⟩ := hr
  have hworld : HiddenProvenance D world := seedGen D A (∅, ∅) (provenance_empty D) _ hy
  have hstart : ProvInv D (⟨startState D state keys,
      if (startState D state keys).flag then some (.seeds, world) else none⟩ : FirstState C A.net.State) world := by
    refine ⟨hworld, fun stage w hw => ?_⟩
    split_ifs at hw
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
    exact hworld
  exact keeps_bind (firstTreeRunsOf_provInv runLimit D run treeRun ready .top runLimit)
    (fun _ => firstSigningOf_provInv prims runLimit counted signing D A run treeRun ready)
    _ world hstart x (by rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff]; exact ⟨z, hz, hx⟩)

omit [Fintype E] [DecidableEq E] in
/-- The walk of the game. Each final state of `firstRunWith`, for each test, has the provenance in
its final world and in its saved snapshot. -/
theorem firstRunWith_provInv (seedGen : ProvenanceSeedGen prims (C := C) (E := E))
    (treeRun : ProvenanceTreeRun prims K circuits settings) (counted : ProvenanceCounted prims (C := C))
    (signing : ProvenanceSigning prims (C := C)) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (ready : RealState C A.net.State → StreamState C → Prop) :
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A ready), ProvInv D r.1 r.2 :=
  firstRunOf_provInv prims runLimit seedGen counted signing D A _ (treeRun D A.net) ready

omit [Fintype E] [DecidableEq E] in
/-- `ProvenanceAtUnready` from the four preservation statements. -/
theorem provenanceAtUnready_of_keeps (seedGen : ProvenanceSeedGen prims (C := C) (E := E))
    (treeRun : ProvenanceTreeRun prims K circuits settings) (counted : ProvenanceCounted prims (C := C))
    (signing : ProvenanceSigning prims (C := C)) :
    ProvenanceAtUnready prims K circuits settings runLimit := by
  intro D A q _ r hr tree index w hw _
  exact (firstRunWith_provInv prims K circuits settings runLimit seedGen treeRun counted signing D A _ r hr).2 _ w hw

/-! ## Part 2. The readiness hop at the test `RunReadyL` -/

/-- A budget part `part D q w` at each start that `firstRunWith` at the test `RunReadyL` records as
not ready, with no global event. -/
def AtUnreadyL (part : C.Coalition → ℕ → StreamState C → Prop) : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A
        (RunReadyL prims (startBudget circuits settings runLimit C q) D)),
      ∀ tree index w, r.1.first = some (.unready tree index, w) → ¬ GlobalEvent w → part D q w

/-- `Ready.SplitAtUnready` at the test `RunReadyL`. -/
def SplitAtUnreadyL : Prop :=
  AtUnreadyL prims K circuits settings runLimit fun _ q w =>
    SplitCacheBound (splitRegionCache SplitHashDomain w.1) (startBudget circuits settings runLimit C q).split

/-- `Ready.SoundAtUnready` at the test `RunReadyL`. -/
def SoundAtUnreadyL : Prop :=
  AtUnreadyL prims K circuits settings runLimit fun _ q w =>
    ∃ (seen : Finset (Query C)) (keys : Finset HashOutput), SoundCache 0 w.1 seen keys ∧
      seen.card ≤ (startBudget circuits settings runLimit C q).coins ∧
      keys.card ≤ (startBudget circuits settings runLimit C q).keys

/-- `Ready.SaltsAtUnready` at the test `RunReadyL`. -/
def SaltsAtUnreadyL : Prop :=
  AtUnreadyL prims K circuits settings runLimit fun _ q w =>
    ∃ salts : Finset (List Bit), DigestSaltsCovered w.1 salts ∧
      salts.card ≤ (startBudget circuits settings runLimit C q).salts

/-- `Ready.HiddenAtUnready` at the test `RunReadyL`. -/
def HiddenAtUnreadyL : Prop :=
  AtUnreadyL prims K circuits settings runLimit fun _ q w =>
    HiddenKeyBound w.2 (startBudget circuits settings runLimit C q).hiddenKeys

/-- Each recorded start that is not ready fails a budget part or the provenance, and its world is
below `world`. -/
def UnreadyFailsL (budget : StartBudget) (D : C.Coalition) (first : Option (Stage × StreamState C))
    (world : StreamState C) : Prop :=
  ∀ tree index w, first = some (.unready tree index, w) →
    ¬ (Ready.BudgetPart budget w ∧ HiddenProvenance D w) ∧ w ≤ world

/-- `Ready.Inv` at the test `RunReadyL`. -/
def InvL (budget : StartBudget) (D : C.Coalition) {σ : Type} (s : FirstState C σ) (world : StreamState C) : Prop :=
  (s.first = none → Ready.Live prims D s.real world) ∧ UnreadyFailsL budget D s.first world

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem invL_grow (budget : StartBudget) (D : C.Coalition) {σ : Type} (s : FirstState C σ) (w w' : StreamState C)
    (h : InvL prims budget D s w) (hle : w ≤ w') : InvL prims budget D s w' := by
  refine ⟨fun hn => ?_, fun tree index w₁ hw => ?_⟩
  · obtain ⟨hseeds, htop⟩ := h.1 hn
    refine ⟨hseeds, fun i hi top htop' => ?_⟩
    obtain ⟨w₀, z, hz, hz1, hz2⟩ := htop i hi top htop'
    exact ⟨w₀, z, hz, hz1, le_trans hz2 hle⟩
  · obtain ⟨hfail, hw₁⟩ := h.2 tree index w₁ hw
    exact ⟨hfail, le_trans hw₁ hle⟩

omit [Fintype E] [DecidableEq E] in
/-- `Ready.firstTreeRun_keeps` at the test `RunReadyL`. -/
theorem firstTreeRunWith_keepsL (budget : StartBudget) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) :
    Keeps (InvL prims budget D) (firstTreeRunWith prims K circuits settings D net (RunReadyL prims budget D) tree) := by
  intro s world hs z hz
  unfold firstTreeRunWith firstTreeRunOf at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, mem_support_bind_iff, StateT.run_set,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
  obtain ⟨hlive, hunready⟩ := hs
  have hgrow : world ≤ x.2 := Ready.streamTreeRun_le prims K circuits settings D net tree s.real world x hx
  have hkeys : (fun j => ((s.real.operators j).keep (x.1.1.2 j) tree).keys) = fun j => (s.real.operators j).keys :=
    funext fun j => Ready.keep_keys _ _ _
  refine ⟨fun hn => ?_, fun tree' index w hw => ?_⟩
  · obtain ⟨hn₁, hn₂⟩ := Ready.orElse_eq_none hn
    obtain ⟨hfirst, -⟩ := Ready.orElse_eq_none hn₁
    have hbad : x.1.2 = false := by
      by_contra hb
      simp [hb] at hn₂
    obtain ⟨hseeds, htop⟩ := hlive hfirst
    refine ⟨?_, fun i hi topTree htop' => ?_⟩
    · change seedsDiffer D (fun j => ((s.real.operators j).keep (x.1.1.2 j) tree).keys) = false
      rw [hkeys]
      exact hseeds
    · change ((s.real.operators i).keep (x.1.1.2 i) tree).top = some topTree at htop'
      change ∃ w z, z ∈ support (Ready.freeRun prims D
        (Ready.refTop D fun j => ((s.real.operators j).keep (x.1.1.2 j) tree).keys) w) ∧
          z.1 = some (.top topTree) ∧ z.2 ≤ x.2
      rw [hkeys]
      have old : (s.real.operators i).top = some topTree →
          ∃ w z, z ∈ support (Ready.freeRun prims D (Ready.refTop D fun j => (s.real.operators j).keys) w) ∧
            z.1 = some (.top topTree) ∧ z.2 ≤ x.2 := fun h => by
        obtain ⟨w₀, z₀, hz₀, hz₀1, hz₀2⟩ := htop i hi topTree h
        exact ⟨w₀, z₀, hz₀, hz₀1, le_trans hz₀2 hgrow⟩
      cases tree with
      | bottom b => exact old htop'
      | top =>
        cases hold : (s.real.operators i).top with
        | some t =>
          simp only [OperatorState.keep, hold, Ready.some_orElse] at htop'
          exact old (hold.trans htop')
        | none =>
          simp only [OperatorState.keep, hold, Ready.none_orElse] at htop'
          have hout : x.1.1.2 i = some (.top topTree) := Ready.topTree_eq_some htop'
          obtain ⟨w₀, z₀, hz₀, hz₀2, hz₀3⟩ := Ready.streamTreeRun_top prims K circuits settings D net s.real world x hx
          refine ⟨w₀, z₀, hz₀, ?_, le_of_eq hz₀2⟩
          rw [← hz₀3 hbad i hi (by rw [hout]; rfl), hout]
  · cases hfirst : s.first with
    | some v =>
      simp only [hfirst, Ready.some_orElse] at hw
      obtain ⟨hfail, hw'⟩ := hunready tree' index w (hfirst.trans hw)
      exact ⟨hfail, le_trans hw' hgrow⟩
    | none =>
      simp only [hfirst, Ready.none_orElse] at hw
      by_cases hready : RunReadyL prims budget D s.real world
      · simp only [hready, ite_true, Ready.none_orElse] at hw
        split_ifs at hw
        simp at hw
      · simp only [hready, ite_false, Ready.some_orElse] at hw
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
        exact ⟨fun hb => hready ⟨Ready.runReady_of_live prims budget D s.real world (hlive hfirst) hb.1, hb.2⟩,
          hgrow⟩

omit [Fintype E] [DecidableEq E] in
theorem firstTreeRunsWith_keepsL (budget : StartBudget) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : ∀ count, Keeps (InvL prims budget D)
      (firstTreeRunsWith prims K circuits settings runLimit D net (RunReadyL prims budget D) tree count)
  | 0 => keeps_pure _
  | count + 1 => by
    unfold firstTreeRunsWith firstTreeRunsOf
    refine keeps_get_bind fun s => ?_
    split_ifs
    · exact keeps_bind (firstTreeRunWith_keepsL prims K circuits settings budget D net tree) fun _ =>
        firstTreeRunsWith_keepsL budget D net tree count
    · exact keeps_pure _

omit [Fintype E] [DecidableEq E] in
theorem firstTreeRequestWith_keepsL (budget : StartBudget) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) : Keeps (InvL prims budget D)
      (firstTreeRequestWith prims K circuits settings runLimit D net (RunReadyL prims budget D) b) := by
  unfold firstTreeRequestWith firstTreeRequestOf
  refine keeps_bind (firstTreeRunsWith_keepsL prims K circuits settings runLimit budget D net _ 1) fun _ =>
    keeps_get_bind fun s => ?_
  split
  · exact keeps_bind (keeps_lift (invL_grow prims budget D) (Ready.simulateQ_le prims D _)) fun _ => keeps_pure _
  · exact keeps_pure _

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstSignRequest_keepsL (budget : StartBudget) (D : C.Coalition) {σ : Type} (i : C.Party) (e : KeyIndex)
    (q : TsigQuery C) : KeepsT (InvL prims budget D) (firstSignRequest (σ := σ) prims D i e q) := by
  unfold firstSignRequest
  refine keepsT_bind (keepsT_lift (keeps_modify _ fun s w hs => hs)) fun _ =>
    keepsT_bind (keepsT_lift keeps_get) fun s => ?_
  exact operatorAnswer_keepsG prims _ (invL_grow prims budget D) D _ _ e q

omit [Fintype E] [DecidableEq E] in
theorem firstSigningWith_keepsL (budget : StartBudget) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    Keeps (InvL prims budget D) (firstSigningWith prims K circuits settings runLimit D A
        (RunReadyL prims budget D)) := by
  unfold firstSigningWith firstSigningOf
  refine keeps_get_bind fun s => ?_
  split
  · refine keeps_bind (keepsT_simulateQ _ (fun q => ?_) _ _) fun _ => keeps_pure _
    rcases q with t | q | q
    · exact keepsT_lift (keeps_lift (invL_grow prims budget D) (Ready.simulateQ_le prims D _))
    · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
      · exact fun t => keeps_pure _
      · exact keepsT_lift (firstTreeRequestWith_keepsL prims K circuits settings runLimit budget D A.net b)
      · exact firstSignRequest_keepsL prims budget D i e _
      · exact firstSignRequest_keepsL prims budget D i e _
    · rcases q with _ | state
      · exact keepsT_lift (keeps_bind keeps_get fun _ => keeps_pure _)
      · exact keepsT_lift (keeps_modify _ fun s w hs => hs)
  · exact keeps_pure _

omit [Fintype E] [DecidableEq E] in
/-- `Ready.firstRun_unreadyFails` at the test `RunReadyL`. -/
theorem firstRunWith_unreadyFailsL (budget : StartBudget) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A (RunReadyL prims budget D)),
      UnreadyFailsL budget D r.1.first r.2 := by
  intro r hr
  unfold firstRunWith firstRunOf at hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨y, -, hr⟩ := hr
  rcases y with ⟨⟨state, keys⟩, world⟩
  simp only [StateT.run_get, support_pure, Set.mem_singleton_iff, exists_eq_left, StateT.run_pure] at hr
  obtain ⟨x, ⟨z, hz, hx⟩, rfl⟩ := hr
  have hstart : InvL prims budget D (⟨startState D state keys,
      if (startState D state keys).flag then some (.seeds, world) else none⟩ : FirstState C A.net.State) world := by
    refine ⟨fun hn => ⟨?_, fun i _ topTree htop => ?_⟩, fun tree index w hw => ?_⟩
    · by_contra hflag
      simp only [startState, Bool.not_eq_false] at hflag hn
      simp [hflag] at hn
    · cases htop
    · split_ifs at hw
      simp at hw
  exact (keeps_bind (firstTreeRunsWith_keepsL prims K circuits settings runLimit budget D A.net .top runLimit)
    (fun _ => firstSigningWith_keepsL prims K circuits settings runLimit budget D A) _ world hstart x
    (by rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff]; exact ⟨z, hz, hx⟩)).2

omit [Fintype E] [DecidableEq E] in
/-- `ReadyHopL` from the four budget parts at the test `RunReadyL` and `ProvenanceAtUnready`. -/
theorem readyHopL_of_budgets (split : SplitAtUnreadyL prims K circuits settings runLimit)
    (sound : SoundAtUnreadyL prims K circuits settings runLimit)
    (salts : SaltsAtUnreadyL prims K circuits settings runLimit)
    (hidden : HiddenAtUnreadyL prims K circuits settings runLimit)
    (provenance : ProvenanceAtUnready prims K circuits settings runLimit) :
    ReadyHopL prims K circuits settings runLimit := by
  intro D A q bounded
  unfold firstProbWith
  rw [prEvent_eq_zero_of_forall_mem_support _ _ fun r hr => ?_, ENNReal.toReal_zero]
  rintro ⟨tree, index, w, hw, hglobal⟩
  exact (firstRunWith_unreadyFailsL prims K circuits settings runLimit _ D A r hr tree index w hw).1
    ⟨⟨split D A q bounded r hr tree index w hw hglobal, sound D A q bounded r hr tree index w hw hglobal,
      salts D A q bounded r hr tree index w hw hglobal, hidden D A q bounded r hr tree index w hw hglobal⟩,
      provenance D A q bounded r hr tree index w hw hglobal⟩

/-! ## Part 3. The game at `RunReadyL` against the game at `RunReady`

The test changes only the record `first`. `Coupled` relates a state of the game at `RunReadyL` with a
state of the game at `RunReady`. They have one real state. A clear new record gives a clear old
record. A new `.unready` record is the old record, or its world has the budget parts, because a start
that fails only the provenance passed `RunReady`. -/

/-- A state of the game at `RunReadyL` and a state of the game at `RunReady`. -/
def Coupled (budget : StartBudget) {σ : Type} (s s' : FirstState C σ) : Prop :=
  s.real = s'.real ∧ (s.first = none → s'.first = none) ∧
    ∀ tree index w, s.first = some (.unready tree index, w) →
      s'.first = some (.unready tree index, w) ∨ Ready.BudgetPart budget w

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem coupled_refl (budget : StartBudget) {σ : Type} (s : FirstState C σ) : Coupled budget s s :=
  ⟨rfl, id, fun _ _ _ h => Or.inl h⟩

/-- From coupled states, `m` and `m'` give one value, one world and coupled states. -/
def Sim (budget : StartBudget) {σ α : Type} (m m' : FirstM C σ α) : Prop :=
  ∀ s s' w, Coupled budget s s' → ∀ z ∈ support ((m.run s).run w),
    ∃ z' ∈ support ((m'.run s').run w), z.1.1 = z'.1.1 ∧ Coupled budget z.1.2 z'.1.2 ∧ z.2 = z'.2

/-- `Sim` in the signing phase, from each state of the signing game. -/
def SimT (budget : StartBudget) {σ α : Type} (m m' : StateT (TsigState C) (FirstM C σ) α) : Prop :=
  ∀ t, Sim budget (m.run t) (m'.run t)

section Sim

variable {budget : StartBudget} {σ : Type}

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem sim_pure {α : Type} (a : α) : Sim (C := C) budget (pure a : FirstM C σ α) (pure a) := by
  intro s s' w hc z hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨((a, s'), w), by simp, rfl, hc, rfl⟩

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem sim_bind {α β : Type} {m m' : FirstM C σ α} {f f' : α → FirstM C σ β} (hm : Sim budget m m')
    (hf : ∀ a, Sim budget (f a) (f' a)) : Sim budget (m >>= f) (m' >>= f') := by
  intro s s' w hc z hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  obtain ⟨y', hy', h1, h2, h3⟩ := hm s s' w hc y hy
  obtain ⟨z', hz', k1, k2, k3⟩ := hf y.1.1 y.1.2 y'.1.2 y.2 h2 z hz
  refine ⟨z', ?_, k1, k2, k3⟩
  simp only [StateT.run_bind, mem_support_bind_iff]
  exact ⟨y', hy', by rw [← h1, ← h3]; exact hz'⟩

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem sim_get_bind {β : Type} {f f' : FirstState C σ → FirstM C σ β}
    (hf : ∀ s s', Coupled budget s s' → Sim budget (f s) (f' s')) : Sim budget (get >>= f) (get >>= f') := by
  intro s s' w hc z hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hz ⊢
  exact hf s s' hc s s' w hc z hz

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem sim_lift {α : Type} (x : StateT (StreamState C) ProbComp α) :
    Sim budget (StateT.lift x : FirstM C σ α) (StateT.lift x) := by
  intro s s' w hc z hz
  simp only [StateT.run_lift, StateT.run_bind, mem_support_bind_iff, StateT.run_pure, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact ⟨((y.1, s'), y.2), by simp only [StateT.run_lift, StateT.run_bind, mem_support_bind_iff,
    StateT.run_pure, support_pure, Set.mem_singleton_iff]; exact ⟨y, hy, rfl⟩, rfl, hc, rfl⟩

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem sim_modify (f : FirstState C σ → FirstState C σ)
    (hf : ∀ s s', Coupled budget s s' → Coupled budget (f s) (f s')) :
    Sim budget (modify f : FirstM C σ Unit) (modify f) := by
  intro s s' w hc z hz
  simp only [StateT.run_modify] at hz
  subst hz
  exact ⟨(((), f s'), w), by simp, rfl, hf s s' hc, rfl⟩

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem simT_lift {α : Type} {m m' : FirstM C σ α} (hm : Sim budget m m') :
    SimT budget (StateT.lift m : StateT (TsigState C) (FirstM C σ) α) (StateT.lift m') := fun t => by
  rw [StateT.run_lift, StateT.run_lift]
  exact sim_bind hm fun _ => sim_pure _

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem simT_bind {α β : Type} {m m' : StateT (TsigState C) (FirstM C σ) α}
    {f f' : α → StateT (TsigState C) (FirstM C σ) β} (hm : SimT budget m m') (hf : ∀ a, SimT budget (f a) (f' a)) :
    SimT budget (m >>= f) (m' >>= f') := fun t => by
  rw [StateT.run_bind, StateT.run_bind]
  exact sim_bind (hm t) fun y => hf y.1 y.2

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem simT_simulateQ {ι : Type} {spec : OracleSpec ι} (impl impl' : QueryImpl spec (StateT (TsigState C) (FirstM C σ)))
    (h : ∀ q, SimT budget (impl q) (impl' q)) {α : Type} (oa : OracleComp spec α) :
    SimT budget (simulateQ impl oa) (simulateQ impl' oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun t => by simp only [simulateQ_pure, StateT.run_pure]; exact sim_pure _
  | query_bind q k ih =>
    intro t
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind]
    exact sim_bind (h q t) fun y => ih y.1 y.2

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem simT_get_bind {β : Type} {f f' : FirstState C σ → StateT (TsigState C) (FirstM C σ) β}
    (hf : ∀ s s', Coupled budget s s' → SimT budget (f s) (f' s')) :
    SimT budget (StateT.lift get >>= f) (StateT.lift get >>= f') := fun t => by
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  exact sim_get_bind fun s s' hc => hf s s' hc t

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem sim_map_get {β : Type} (f : FirstState C σ → β) (hf : ∀ s s', Coupled budget s s' → f s = f s') :
    Sim budget (f <$> get : FirstM C σ β) (f <$> get) := by
  rw [map_eq_bind_pure_comp]
  exact sim_get_bind fun s s' hc => by
    simp only [Function.comp_apply, hf s s' hc]
    exact sim_pure _

end Sim

omit [Fintype E] [DecidableEq E] [Field E] [Algebra Bit E] in
theorem firstSignRequest_sim (budget : StartBudget) (D : C.Coalition) {σ : Type} (i : C.Party) (e : KeyIndex)
    (q : TsigQuery C) : SimT budget (firstSignRequest (σ := σ) prims D i e q) (firstSignRequest prims D i e q) := by
  unfold firstSignRequest
  refine simT_bind (simT_lift (sim_modify _ fun s s' hc => ⟨by rw [hc.1], hc.2⟩)) fun _ =>
    simT_get_bind fun s s' hc t => ?_
  rw [← hc.1]
  obtain ⟨X, hX, -⟩ := operatorAnswer_world prims D s.real.operators (s.real.operators i) e q t
  rw [hX]
  exact sim_lift _

omit [Fintype E] [DecidableEq E] in
theorem firstTreeRunWith_sim (budget : StartBudget) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) :
    Sim budget (firstTreeRunWith prims K circuits settings D net (RunReadyL prims budget D) tree)
      (firstTreeRunWith prims K circuits settings D net (RunReady prims budget D) tree) := by
  intro s s' w hc z hz
  unfold firstTreeRunWith firstTreeRunOf at hz
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, mem_support_bind_iff, StateT.run_set,
    StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨_, ⟨x, hx, rfl⟩, rfl⟩ := hz
  obtain ⟨hreal, hnone, hun⟩ := hc
  rw [hreal] at hx
  refine ⟨(((), ⟨⟨x.1.1.1, fun i => (s'.real.operators i).keep (x.1.1.2 i) tree,
      Function.update s'.real.runs tree (s'.real.runs tree + 1), s'.real.closed, s'.real.flag || x.1.2⟩,
      (s'.first <|> if RunReady prims budget D s'.real w then none
        else some (.unready tree (s'.real.runs tree), w)) <|>
        if x.1.2 then some (.run tree (s'.real.runs tree), x.2) else none⟩), x.2), ?_, rfl, ⟨?_, ?_, ?_⟩, rfl⟩
  · unfold firstTreeRunWith firstTreeRunOf
    simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, mem_support_bind_iff, StateT.run_set,
      StateT.run_pure, support_pure, Set.mem_singleton_iff]
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  · dsimp only
    rw [hreal]
  · intro hn
    dsimp only at hn ⊢
    obtain ⟨hn₁, hn₂⟩ := Ready.orElse_eq_none hn
    obtain ⟨hfirst, hready⟩ := Ready.orElse_eq_none hn₁
    have hreadyL : RunReadyL prims budget D s.real w := by
      by_contra h
      simp [h] at hready
    have hold : RunReady prims budget D s'.real w := hreal ▸ hreadyL.1
    rw [hnone hfirst, Ready.none_orElse, ite_eq_left hold, Ready.none_orElse, ← hreal]
    exact hn₂
  · intro tree' index w' hw
    dsimp only at hw ⊢
    cases hfirst : s.first with
    | some v =>
      rw [hfirst, Ready.some_orElse, Ready.some_orElse] at hw
      rcases hun tree' index w' (hfirst.trans hw) with h | h
      · exact Or.inl (by rw [h, Ready.some_orElse, Ready.some_orElse])
      · exact Or.inr h
    | none =>
      rw [hfirst, Ready.none_orElse] at hw
      rw [hnone hfirst, Ready.none_orElse]
      by_cases hreadyL : RunReadyL prims budget D s.real w
      · rw [ite_eq_left hreadyL, Ready.none_orElse] at hw
        split_ifs at hw; simp at hw
      · rw [ite_eq_right hreadyL, Ready.some_orElse] at hw
        obtain ⟨⟨⟩, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
        by_cases hold : RunReady prims budget D s'.real w
        · exact Or.inr hold.2.2
        · left
          rw [ite_eq_right hold, Ready.some_orElse, hreal]

omit [Fintype E] [DecidableEq E] in
theorem firstTreeRunsWith_sim (budget : StartBudget) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) : ∀ count,
    Sim budget (firstTreeRunsWith prims K circuits settings runLimit D net (RunReadyL prims budget D) tree count)
      (firstTreeRunsWith prims K circuits settings runLimit D net (RunReady prims budget D) tree count)
  | 0 => sim_pure _
  | count + 1 => by
    unfold firstTreeRunsWith firstTreeRunsOf
    refine sim_get_bind fun s s' hc => ?_
    rw [hc.1]
    split_ifs
    · exact sim_bind (firstTreeRunWith_sim prims K circuits settings budget D net tree) fun _ =>
        firstTreeRunsWith_sim budget D net tree count
    · exact sim_pure _

omit [Fintype E] [DecidableEq E] in
theorem firstTreeRequestWith_sim (budget : StartBudget) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) :
    Sim budget (firstTreeRequestWith prims K circuits settings runLimit D net (RunReadyL prims budget D) b)
      (firstTreeRequestWith prims K circuits settings runLimit D net (RunReady prims budget D) b) := by
  unfold firstTreeRequestWith firstTreeRequestOf
  refine sim_bind (firstTreeRunsWith_sim prims K circuits settings runLimit budget D net _ 1) fun _ =>
    sim_get_bind fun s s' hc => ?_
  rw [hc.1]
  cases heldBottom D s'.real.operators b with
  | none => exact sim_pure _
  | some tree => exact sim_bind (sim_lift _) fun _ => sim_pure _

omit [Fintype E] [DecidableEq E] in
theorem firstSigningWith_sim (budget : StartBudget) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    Sim budget (firstSigningWith prims K circuits settings runLimit D A (RunReadyL prims budget D))
      (firstSigningWith prims K circuits settings runLimit D A (RunReady prims budget D)) := by
  unfold firstSigningWith firstSigningOf
  refine sim_get_bind fun s s' hc => ?_
  rw [hc.1]
  cases topHolder D s'.real.operators with
  | none => exact sim_pure _
  | some kt =>
    refine sim_bind (simT_simulateQ _ _ (fun q => ?_) _ _) fun _ => sim_pure _
    rcases q with t | q | q
    · exact simT_lift (sim_lift _)
    · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
      · exact fun t => sim_pure _
      · exact simT_lift (firstTreeRequestWith_sim prims K circuits settings runLimit budget D A.net b)
      · exact firstSignRequest_sim prims budget D i e _
      · exact firstSignRequest_sim prims budget D i e _
    · rcases q with _ | state
      · exact simT_lift (sim_map_get _ fun s s' hc => by rw [hc.1])
      · exact simT_lift (sim_modify _ fun s s' hc => ⟨by rw [hc.1], hc.2⟩)

omit [Fintype E] [DecidableEq E] in
/-- Each final state of the game at `RunReadyL` has a coupled final state of the game at `RunReady`,
with the same world. -/
theorem firstRunWith_coupled (budget : StartBudget) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A (RunReadyL prims budget D)),
      ∃ r' ∈ support (firstRunWith prims K circuits settings runLimit D A
          (RunReady prims budget D)), Coupled budget r.1 r'.1 ∧ r.2 = r'.2 := by
  intro r hr
  unfold firstRunWith firstRunOf at hr
  unfold firstRunWith firstRunOf
  simp only [StateT.run_bind, mem_support_bind_iff] at hr ⊢
  obtain ⟨y, hy, hr⟩ := hr
  rcases y with ⟨⟨state, keys⟩, world⟩
  simp only [StateT.run_get, support_pure, Set.mem_singleton_iff, exists_eq_left, StateT.run_pure] at hr ⊢
  obtain ⟨x, ⟨z, hz, hx⟩, rfl⟩ := hr
  have hbody := sim_bind (firstTreeRunsWith_sim prims K circuits settings runLimit budget D A.net .top runLimit)
    (fun _ => firstSigningWith_sim prims K circuits settings runLimit budget D A) _ _ world (coupled_refl budget _) x
    (by rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff]; exact ⟨z, hz, hx⟩)
  obtain ⟨x', hx', -, hc, hw⟩ := hbody
  rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff] at hx'
  obtain ⟨z', hz', hx'⟩ := hx'
  exact ⟨_, ⟨_, hy, _, ⟨z', hz', hx'⟩, rfl⟩, hc, hw⟩

omit [Fintype E] [DecidableEq E] in
/-- A budget part `part` of the game at `RunReady` at its recorded starts gives the same part at the
recorded starts of the game at `RunReadyL`, when each world with the budget parts has `part`. -/
theorem atUnreadyL_of_old (part : C.Coalition → ℕ → StreamState C → Prop)
    (hbudget : ∀ D q w, Ready.BudgetPart (startBudget circuits settings runLimit C q) w → part D q w)
    (old : ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
      ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A
          (RunReady prims (startBudget circuits settings runLimit C q) D)),
        ∀ tree index w, r.1.first = some (.unready tree index, w) → ¬ GlobalEvent w → part D q w) :
    AtUnreadyL prims K circuits settings runLimit part := by
  intro D A q bounded r hr tree index w hw hglobal
  obtain ⟨r', hr', hc, -⟩ := firstRunWith_coupled prims K circuits settings runLimit _ D A r hr
  rcases hc.2.2 tree index w hw with h | h
  · exact old D A q bounded r' hr' tree index w h hglobal
  · exact hbudget D q w h

omit [Fintype E] [DecidableEq E] in
theorem splitAtUnreadyL_of_old (h : Ready.SplitAtUnready prims K circuits settings runLimit) :
    SplitAtUnreadyL prims K circuits settings runLimit :=
  atUnreadyL_of_old prims K circuits settings runLimit _ (fun _ _ _ hb => hb.1) fun D A q b => h D A q b

omit [Fintype E] [DecidableEq E] in
theorem soundAtUnreadyL_of_old (h : Ready.SoundAtUnready prims K circuits settings runLimit) :
    SoundAtUnreadyL prims K circuits settings runLimit :=
  atUnreadyL_of_old prims K circuits settings runLimit _ (fun _ _ _ hb => hb.2.1) fun D A q b => h D A q b

omit [Fintype E] [DecidableEq E] in
theorem saltsAtUnreadyL_of_old (h : Ready.SaltsAtUnready prims K circuits settings runLimit) :
    SaltsAtUnreadyL prims K circuits settings runLimit :=
  atUnreadyL_of_old prims K circuits settings runLimit _ (fun _ _ _ hb => hb.2.2.1) fun D A q b => h D A q b

omit [Fintype E] [DecidableEq E] in
theorem hiddenAtUnreadyL_of_old (h : Ready.HiddenAtUnready prims K circuits settings runLimit) :
    HiddenAtUnreadyL prims K circuits settings runLimit :=
  atUnreadyL_of_old prims K circuits settings runLimit _ (fun _ _ _ hb => hb.2.2.2) fun D A q b => h D A q b

omit [Fintype E] [DecidableEq E] in
/-- The split part at the test `RunReadyL`, from the proved count of the class `digest`. -/
theorem splitAtUnreadyL : SplitAtUnreadyL prims K circuits settings runLimit :=
  splitAtUnreadyL_of_old prims K circuits settings runLimit (Ready.splitAtUnready_of_end prims K circuits settings
    runLimit (FirstCounts.splitAtEnd_of_premises prims K circuits settings runLimit DigestBudgets.seedHonest_digest
      (DigestBudgets.treeHonest_digest K circuits settings) DigestBudgets.signQuiet_digest))

omit [Fintype E] [DecidableEq E] in
/-- The salt part at the test `RunReadyL`, from the proved count of the class `digest`. -/
theorem saltsAtUnreadyL : SaltsAtUnreadyL prims K circuits settings runLimit :=
  saltsAtUnreadyL_of_old prims K circuits settings runLimit (Ready.saltsAtUnready_of_end prims K circuits settings
    runLimit (FirstCounts.saltsAtEnd_of_premises prims K circuits settings runLimit DigestBudgets.seedHonest_digest
      (DigestBudgets.treeHonest_digest K circuits settings) DigestBudgets.signQuiet_digest))

/-- The hidden streams at the end of `firstRunWith` at the test `RunReady` have at most `gameSetups`
keys under each name. -/
def HiddenAtEnd : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ r ∈ support (firstRunWith prims K circuits settings runLimit D A
        (RunReady prims (startBudget circuits settings runLimit C q) D)),
      HiddenKeyBound r.2.2 (startBudget circuits settings runLimit C q).hiddenKeys

omit [Fintype E] [DecidableEq E] in
/-- `Ready.HiddenAtUnready` from the bound at the end, as `Ready.soundAtUnready_of_end`. -/
theorem hiddenAtUnready_of_end (h : HiddenAtEnd prims K circuits settings runLimit) :
    Ready.HiddenAtUnready prims K circuits settings runLimit := by
  intro D A q bounded r hr tree index w hw _
  have hle := (Ready.firstRun_unreadyFails prims K circuits settings runLimit _ D A r hr tree index w hw).2
  intro name
  obtain ⟨keys, hcard, hcover⟩ := h D A q bounded r hr name
  exact ⟨keys, hcard, fun key ρ idx position hx =>
    hcover key ρ idx position (Ready.cell_ne_none_of_le hle.2 hx)⟩

omit [Fintype E] [DecidableEq E] in
/-- `ReadyHopL` from the bounds at the end of the game, `Ready.SoundAtEnd` and `HiddenAtEnd`, and
`ProvenanceTreeRun`. -/
theorem readyHopL_of_ends (sound : Ready.SoundAtEnd prims K circuits settings runLimit)
    (hidden : HiddenAtEnd prims K circuits settings runLimit)
    (treeRun : ProvenanceTreeRun prims K circuits settings) :
    ReadyHopL prims K circuits settings runLimit :=
  readyHopL_of_budgets prims K circuits settings runLimit (splitAtUnreadyL prims K circuits settings runLimit)
    (soundAtUnreadyL_of_old prims K circuits settings runLimit
      (Ready.soundAtUnready_of_end prims K circuits settings runLimit sound))
    (saltsAtUnreadyL prims K circuits settings runLimit)
    (hiddenAtUnreadyL_of_old prims K circuits settings runLimit
      (hiddenAtUnready_of_end prims K circuits settings runLimit hidden))
    (provenanceAtUnready_of_keeps prims K circuits settings runLimit (provenanceSeedGen prims) treeRun
      (provenanceCounted prims) (provenanceSigning prims))

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.readyHopL_of_ends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.readyHopL_of_ends

