import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Hops
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Walk
import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# The union over the runs

`runsUnionHopOf` bounds the probability that `firstRunOf` records a first bad event of a run with no
global event by the sum of the bounds of the runs (`RunBadOf`), for each run and each readiness test.
`runsUnionHop` proves `RunsUnionHopW` as its instance at `streamTreeRun`.

* `Weight` is a potential on the state of the game. While no bad event is recorded and the flag is
  not set, it is the sum of the bounds of the remaining runs of each tree. After the first bad event
  it is the indicator of the target event.
* `Super` says that a computation does not raise the expected potential. The tree runs, the tree
  requests, the signing answers and the state cell of the adversary keep it (`firstSigning_super`).
* `runsUnionHopOf` proves the hop from these facts and from the premise that each bound is not
  negative.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
  OracleComp.ProgramLogic

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

namespace RunsUnion

/-! ## Computations that do not raise an expected potential -/

section Super

variable {C : Committee} {σ : Type} (V : FirstState C σ → ℝ≥0∞)

/-- A computation of the game whose expected potential at the end is at most the potential at the
start, from each state of the game and of the world. -/
def Super {α : Type} (m : FirstM C σ α) : Prop :=
  ∀ s world, wp ((m.run s).run world) (fun z => V z.1.2) ≤ V s

/-- A computation of the signing phase that is `Super` from each state of the signing game. -/
def SuperT {α : Type} (m : StateT (TsigState C) (FirstM C σ) α) : Prop := ∀ t, Super V (m.run t)

variable {V}

theorem super_pure {α : Type} (a : α) : Super V (pure a : FirstM C σ α) := by
  intro s world
  simp only [StateT.run_pure, wp_pure, le_refl]

theorem super_bind {α β : Type} {m : FirstM C σ α} {f : α → FirstM C σ β} (hm : Super V m)
    (hf : ∀ a, Super V (f a)) : Super V (m >>= f) := by
  intro s world
  simp only [StateT.run_bind, wp_bind]
  exact le_trans (wp_mono _ fun y => hf y.1.1 y.1.2 y.2) (hm s world)

/-- A computation that reads the state needs the bound only from the state that it reads. -/
theorem super_get_bind {β : Type} {f : FirstState C σ → FirstM C σ β}
    (hf : ∀ s world, wp (((f s).run s).run world) (fun z => V z.1.2) ≤ V s) : Super V (get >>= f) := by
  intro s world
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  exact hf s world

theorem super_get : Super V (get : FirstM C σ _) := by
  intro s world
  simp only [StateT.run_get, StateT.run_pure, wp_pure, le_refl]

theorem super_modify (f : FirstState C σ → FirstState C σ) (h : ∀ s, V (f s) = V s) :
    Super V (modify f : FirstM C σ Unit) := by
  intro s world
  simp only [StateT.run_modify, StateT.run_pure, wp_pure, h, le_refl]

/-- A computation of the world keeps the state of the game, so it keeps the potential. -/
theorem super_lift {α : Type} (x : StateT (StreamState C) ProbComp α) :
    Super V (StateT.lift x : FirstM C σ α) := by
  intro s world
  simp only [StateT.run_lift, StateT.run_bind, StateT.run_pure, wp_bind, wp_pure, wp_const, le_refl]

theorem superT_lift {α : Type} {m : FirstM C σ α} (hm : Super V m) :
    SuperT V (StateT.lift m : StateT (TsigState C) (FirstM C σ) α) := fun t => by
  rw [StateT.run_lift]
  exact super_bind hm fun _ => super_pure _

theorem superT_bind {α β : Type} {m : StateT (TsigState C) (FirstM C σ) α}
    {f : α → StateT (TsigState C) (FirstM C σ) β} (hm : SuperT V m) (hf : ∀ a, SuperT V (f a)) :
    SuperT V (m >>= f) := fun t => by
  rw [StateT.run_bind]
  exact super_bind (hm t) fun y => hf y.1 y.2

theorem superT_simulateQ {ι : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT (TsigState C) (FirstM C σ)))
    (h : ∀ q, SuperT V (impl q)) {α : Type} (oa : OracleComp spec α) : SuperT V (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact fun t => by rw [simulateQ_pure, StateT.run_pure]; exact super_pure _
  | query_bind q k ih =>
    intro t
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind]
    exact super_bind (h q t) fun y => ih y.1 y.2

end Super

/-! ## The potential of the runs -/

section Weight

variable {C : Committee} (runLimit : ℕ) (e : Tree → ℝ≥0∞)

/-- The target event of `RunsUnionHopW` on the record of the first bad event. A run is the first bad
event, with no global event in its world. -/
def Target (first : Option (Stage × StreamState C)) : Prop :=
  ∃ tree index world, first = some (.run tree index, world) ∧ ¬ GlobalEvent world

/-- The sum of the bounds `e` of the remaining runs of each tree. -/
def remaining (runs : Tree → ℕ) : ℝ≥0∞ :=
  ((runLimit - runs .top : ℕ) : ℝ≥0∞) * e .top +
    ∑ b : Fin (2 ^ layerHeight), ((runLimit - runs (.bottom b) : ℕ) : ℝ≥0∞) * e (.bottom b)

/-- The potential of a state of the game. With no record and no flag it is `remaining`, with no
record and the flag it is `⊤`, and with a record it is the indicator of `Target`. -/
def Weight {σ : Type} (s : FirstState C σ) : ℝ≥0∞ :=
  match s.first with
  | some _ => propInd (Target s.first)
  | none => if s.real.flag then ⊤ else remaining runLimit e s.real.runs

theorem target_run (tree : Tree) (index : ℕ) (world : StreamState C) :
    Target (some (Stage.run tree index, world)) ↔ ¬ GlobalEvent world := by
  constructor
  · rintro ⟨_, _, _, h, hg⟩
    cases h
    exact hg
  · exact fun hg => ⟨tree, index, world, rfl, hg⟩

theorem cast_sub_succ {n r : ℕ} (h : r < n) : ((n - r : ℕ) : ℝ≥0∞) = ((n - (r + 1) : ℕ) : ℝ≥0∞) + 1 := by
  rw [show n - r = n - (r + 1) + 1 by omega, Nat.cast_succ]

/-- One more run of `tree` lowers `remaining` by the bound of `tree`. -/
theorem remaining_update (runs : Tree → ℕ) (tree : Tree) (h : runs tree < runLimit) :
    remaining runLimit e (Function.update runs tree (runs tree + 1)) + e tree = remaining runLimit e runs := by
  cases tree with
  | top =>
    have hb : ∀ b : Fin (2 ^ layerHeight),
        Function.update runs Tree.top (runs .top + 1) (.bottom b) = runs (.bottom b) :=
      fun b => Function.update_of_ne (by simp) _ _
    simp only [remaining, Function.update_self, hb, cast_sub_succ h]
    ring
  | bottom b₀ =>
    have hb : ∀ b, b ≠ b₀ →
        Function.update runs (Tree.bottom b₀) (runs (.bottom b₀) + 1) (.bottom b) = runs (.bottom b) :=
      fun b hb => Function.update_of_ne (by simpa using hb) _ _
    have ht : Function.update runs (Tree.bottom b₀) (runs (.bottom b₀) + 1) .top = runs .top :=
      Function.update_of_ne (by simp) _ _
    simp only [remaining, ht]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b₀), ← Finset.add_sum_erase _ _ (Finset.mem_univ b₀),
      Finset.sum_congr rfl fun b hb' => by rw [hb b (Finset.ne_of_mem_erase hb')], Function.update_self,
      cast_sub_succ h]
    ring

end Weight

/-! ## The runs keep the potential -/

section Game

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The bound `ε tree` of a run of `tree` with the run `run` that has its event and no global event at
its end, from each start that passes the readiness test `ready` and has no flag. `RunBadW` is the
instance at `streamTreeRun`. -/
def RunBadOf {σ : Type} (run : RunOf C σ) (ready : RealState C σ → StreamState C → Prop) (ε : Tree → ℝ) : Prop :=
  ∀ (tree : Tree) (s : RealState C σ) (world : StreamState C), ready s world → s.flag = false →
    (Pr{let r ← (run tree s).run world}[r.1.2 = true ∧ ¬ GlobalEvent r.2]).toReal ≤ ε tree

/-- The bound of `RunBadOf` as an expectation. -/
theorem runBad_wp {σ : Type} (run : RunOf C σ) (ready : RealState C σ → StreamState C → Prop) (ε : Tree → ℝ)
    (hbad : RunBadOf run ready ε) (tree : Tree) (s : RealState C σ)
    (world : StreamState C) (hready : ready s world) (hflag : s.flag = false) :
    wp ((run tree s).run world)
      (fun r => propInd (r.1.2 = true ∧ ¬ GlobalEvent r.2)) ≤ ENNReal.ofReal (ε tree) := by
  rw [← prEvent_eq_wp_propInd]
  exact (ENNReal.ofReal_toReal (prEvent_ne_top _)).symm.le.trans
    (ENNReal.ofReal_le_ofReal (hbad tree s world hready hflag))

/-- One allowed run of `tree` does not raise the expected potential. A ready start with no record and
no flag trades the bound of one run of `tree` for the event of `RunBadW`. -/
theorem firstTreeRun_super {σ : Type} (run : RunOf C σ) (ready : RealState C σ → StreamState C → Prop)
    (ε : Tree → ℝ) (hbad : RunBadOf run ready ε) (tree : Tree) (s : FirstState C σ)
    (world : StreamState C) (hruns : s.real.runs tree < runLimit) :
    wp (((firstTreeRunOf run ready tree).run s).run world)
      (fun z => Weight runLimit (fun t => ENNReal.ofReal (ε t)) z.1.2) ≤
        Weight runLimit (fun t => ENNReal.ofReal (ε t)) s := by
  unfold firstTreeRunOf
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, StateT.run_set, StateT.run_pure,
    wp_bind, wp_pure]
  cases hfirst : s.first with
  | some v =>
    simp only [Weight, hfirst, Ready.some_orElse, wp_const, le_refl]
  | none =>
    cases hflag : s.real.flag with
    | true => simp only [Weight, hfirst, hflag, ite_true, le_top]
    | false =>
      by_cases hready : ready s.real world
      · simp only [Weight, hfirst, hflag, hready, ite_true, Ready.none_orElse, Bool.false_or]
        set e : Tree → ℝ≥0∞ := fun t => ENNReal.ofReal (ε t)
        set after := remaining runLimit e (Function.update s.real.runs tree (s.real.runs tree + 1))
        calc _ ≤ wp ((run tree s.real).run world)
              (fun x => propInd (x.1.2 = true ∧ ¬ GlobalEvent x.2) + after) := by
              refine wp_mono _ fun x => ?_
              cases hx : x.1.2 with
              | true =>
                simp only [ite_true, target_run, true_and]
                exact le_self_add
              | false =>
                simp only [Bool.false_eq_true, ite_false, false_and]
                exact le_add_self
          _ ≤ e tree + after := by
              rw [wp_add, wp_const]
              exact add_le_add_left (runBad_wp run ready ε hbad tree s.real world
                hready hflag) _
          _ = _ := by
              rw [add_comm, remaining_update runLimit e _ tree hruns]
              simp only [Bool.false_eq_true, ite_false]
      · simp only [Weight, hfirst, hready, ite_false, Ready.none_orElse, Ready.some_orElse]
        have hnot : ¬ Target (some (Stage.unready tree (s.real.runs tree), world)) := by
          rintro ⟨_, _, _, h, -⟩
          cases h
        simp only [hnot, propInd_false, wp_const, zero_le]

omit [Field E] [Algebra Bit E] in
theorem runs_lt_of_mayRun (D : C.Coalition) {σ : Type} (s : RealState C σ) (tree : Tree)
    (h : mayRun runLimit D s tree) : s.runs tree < runLimit := by
  cases tree with
  | top => exact h.1
  | bottom b => exact h.2.1

variable (ε : Tree → ℝ)

theorem firstTreeRuns_super {σ : Type} (D : C.Coalition) (run : RunOf C σ)
    (ready : RealState C σ → StreamState C → Prop) (hbad : RunBadOf run ready ε) (tree : Tree) :
    ∀ count, Super (Weight runLimit fun t => ENNReal.ofReal (ε t)) (firstTreeRunsOf runLimit D run ready tree count)
  | 0 => super_pure _
  | count + 1 => by
    unfold firstTreeRunsOf
    refine super_get_bind fun s world => ?_
    split_ifs with h
    · rw [StateT.run_bind, StateT.run_bind, wp_bind]
      exact le_trans (wp_mono _ fun y => firstTreeRuns_super D run ready hbad tree count y.1.2 y.2)
        (firstTreeRun_super runLimit run ready ε hbad tree s world
          (runs_lt_of_mayRun runLimit D s.real tree h))
    · exact super_pure _ s world

theorem firstTreeRequest_super {σ : Type} (D : C.Coalition) (run : RunOf C σ)
    (ready : RealState C σ → StreamState C → Prop) (hbad : RunBadOf run ready ε) (b : Fin (2 ^ layerHeight)) :
    Super (Weight runLimit fun t => ENNReal.ofReal (ε t)) (firstTreeRequestOf prims runLimit D run ready b) := by
  unfold firstTreeRequestOf
  refine super_bind (firstTreeRuns_super runLimit ε D run ready hbad _ 1) fun _ =>
    super_get_bind fun s world => ?_
  split
  · exact super_bind (super_lift _) (fun _ => super_pure _) s world
  · exact super_pure _ s world

omit [Field E] [Algebra Bit E] in
/-- The answer of an honest operator is a computation of the world, so it keeps the potential. -/
theorem operatorAnswer_super {σ : Type} (V : FirstState C σ → ℝ≥0∞) (D : C.Coalition)
    (operators : C.Party → OperatorState C) (operator : OperatorState C) (e : KeyIndex) (q : TsigQuery C) :
    SuperT V (operatorAnswer (m := FirstM C σ) (firstLift prims D) (firstValue prims D operators) operator e q) := by
  intro t
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
    change Super V ((tsigOracles (fun oa => streamLift C σ (ψ (freeLift oa)))
      (SeedHitProof.Dealt.hmap (streamLift C σ) (SeedHitProof.Dealt.hmap ψ dealt)) q).run t')
    rw [← hom₁, ← hom₂]
    exact super_lift _
  · exact super_pure _

omit [Field E] [Algebra Bit E] in
theorem firstSignRequest_super (D : C.Coalition) {σ : Type} (V : FirstState C σ → ℝ≥0∞)
    (hV : ∀ s : FirstState C σ, ∀ closed, V { s with real := { s.real with closed := closed } } = V s)
    (i : C.Party) (e : KeyIndex) (q : TsigQuery C) :
    SuperT V (firstSignRequest (σ := σ) prims D i e q) := by
  unfold firstSignRequest
  refine superT_bind (superT_lift (super_modify _ fun s => hV s _)) fun _ =>
    superT_bind (superT_lift super_get) fun s => ?_
  exact operatorAnswer_super prims V D _ _ e q

theorem firstOracles_super {σ : Type} (D : C.Coalition) (run : RunOf C σ)
    (ready : RealState C σ → StreamState C → Prop) (hbad : RunBadOf run ready ε) (q : TsigQuery C) :
    SuperT (Weight runLimit fun t => ENNReal.ofReal (ε t)) (firstOraclesOf prims runLimit D run ready q) := by
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · exact fun t => super_pure _
  · exact superT_lift (firstTreeRequest_super prims runLimit ε D run ready hbad b)
  · exact firstSignRequest_super prims D _ (fun _ _ => rfl) i e _
  · exact firstSignRequest_super prims D _ (fun _ _ => rfl) i e _

omit [Field E] [Algebra Bit E] in
theorem firstSigning_super (D : C.Coalition) (A : DkgTsigAdversary C E) (run : RunOf C A.net.State)
    (ready : RealState C A.net.State → StreamState C → Prop) (hbad : RunBadOf run ready ε) :
    Super (Weight runLimit fun t => ENNReal.ofReal (ε t)) (firstSigningOf prims runLimit D A run ready) := by
  unfold firstSigningOf
  refine super_get_bind fun s world => ?_
  split
  · refine super_bind (superT_simulateQ _ (fun q => ?_) _ _) (fun _ => super_pure _) s world
    rcases q with t | q | q
    · exact superT_lift (super_lift _)
    · exact firstOracles_super prims runLimit ε D run ready hbad q
    · rcases q with _ | state
      · change SuperT _ (StateT.lift ((fun s : FirstState C A.net.State => s.real.adversary) <$> get))
        rw [map_eq_bind_pure_comp]
        exact superT_lift (super_bind super_get fun _ => super_pure _)
      · exact superT_lift (super_modify _ fun _ => rfl)
  · exact super_pure _ s world

omit [Field E] [Algebra Bit E] in
/-- The bound of `RunsUnionHopW` in `ℝ≥0∞` for each run, with the bounds of the runs as `ofReal`. -/
theorem firstRun_target (D : C.Coalition) (A : DkgTsigAdversary C E) (run : RunOf C A.net.State)
    (ready : RealState C A.net.State → StreamState C → Prop) (hbad : RunBadOf run ready ε) :
    Pr{let r ← firstRunOf prims runLimit D A run ready}[Target r.1.first] ≤
      (runLimit : ℝ≥0∞) * ENNReal.ofReal (ε .top) +
        ∑ b : Fin (2 ^ layerHeight), (runLimit : ℝ≥0∞) * ENNReal.ofReal (ε (.bottom b)) := by
  set V := Weight (C := C) (σ := A.net.State) runLimit fun t => ENNReal.ofReal (ε t)
  have hsuper : Super V (firstTreeRunsOf runLimit D run ready .top runLimit >>=
      fun _ => firstSigningOf prims runLimit D A run ready) :=
    super_bind (firstTreeRuns_super runLimit ε D run ready hbad .top runLimit)
      fun _ => firstSigning_super prims runLimit ε D A run ready hbad
  have hend : ∀ z : FirstState C A.net.State, propInd (Target z.first) ≤ V z := by
    intro z
    simp only [V, Weight]
    cases hz : z.first with
    | some v => exact le_refl _
    | none =>
      have hnot : ¬ Target (none : Option (Stage × StreamState C)) := by
        rintro ⟨_, _, _, h, -⟩
        cases h
      simp only [hnot, propInd_false, zero_le]
  rw [prEvent_eq_wp_propInd]
  unfold firstRunOf
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, wp_bind, wp_pure, pure_bind]
  refine wp_le_const_of_support _ fun x _ => ?_
  set fs : FirstState C A.net.State := ⟨startState D x.1.1 x.1.2,
    if (startState D x.1.1 x.1.2).flag = true then some (Stage.seeds, x.2) else none⟩
  have hstep := hsuper fs x.2
  simp only [StateT.run_bind, wp_bind] at hstep
  refine le_trans (wp_mono _ fun y => wp_mono _ fun z => hend z.1.2) (le_trans hstep ?_)
  simp only [V, fs, Weight]
  cases hflag : (startState D x.1.1 x.1.2).flag with
  | true =>
    have hnot : ¬ Target (some (Stage.seeds, x.2)) := by
      rintro ⟨_, _, _, h, -⟩
      cases h
    simp only [ite_true, hnot, propInd_false, zero_le]
  | false =>
    simp only [Bool.false_eq_true, ite_false, remaining, startState, Nat.sub_zero, le_refl]

omit [Field E] [Algebra Bit E] in
/-- The union over the runs for each run, from `firstRun_target` and the bounds of `RunBadOf` that are
not negative. -/
theorem runsUnionHopOf (D : C.Coalition) (A : DkgTsigAdversary C E) (run : RunOf C A.net.State)
    (ready : RealState C A.net.State → StreamState C → Prop) (ε : Tree → ℝ) (hpos : ∀ tree, 0 ≤ ε tree)
    (hbad : RunBadOf run ready ε) :
    (Pr{let r ← firstRunOf prims runLimit D A run ready}[
        ∃ tree index world, r.1.first = some (.run tree index, world) ∧ ¬ GlobalEvent world]).toReal ≤
      runLimit * (ε .top + ∑ b : Fin (2 ^ layerHeight), ε (.bottom b)) := by
  have hsum : 0 ≤ ∑ b : Fin (2 ^ layerHeight), ε (.bottom b) :=
    Finset.sum_nonneg fun b _ => hpos (.bottom b)
  refine ENNReal.toReal_le_of_le_ofReal (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hpos .top) hsum)) ?_
  refine le_trans (firstRun_target prims runLimit ε D A run ready hbad) (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ENNReal.ofReal_add (hpos .top) hsum,
    ENNReal.ofReal_sum_of_nonneg fun b _ => hpos (.bottom b), mul_add, Finset.mul_sum]

/-- The union over the runs of `firstRunWith`, the instance of `runsUnionHopOf` at `streamTreeRun`. -/
theorem runsUnionHop : RunsUnionHopW prims K circuits settings runLimit (C := C) (E := E) := by
  intro D A ready ε hpos hbad
  unfold firstProbWith firstRunWith
  exact runsUnionHopOf prims runLimit D A _ ready ε hpos hbad

end Game

end RunsUnion

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.RunsUnion.runsUnionHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.RunsUnion.runsUnionHop
