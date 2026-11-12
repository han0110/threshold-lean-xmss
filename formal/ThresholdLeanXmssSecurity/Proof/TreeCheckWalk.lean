import ThresholdLeanXmssSecurity.Proof.TreeCheckCutParts
import ThresholdLeanXmssSecurity.Proof.TreeLockstepOpenedRest
import ThresholdLeanXmssSecurity.Proof.MainStages

/-!
# The circuit prefix at the counted check cut

`Reject` concerns the deterministic correctness bit of `multVerifyLeak`, not
acceptance by the randomized GS20 check. The inconsistent PRSS keys in item 5
of `TreeSimCheckFinish` require a `.sharedKeys` collision, which the current
`TreeCheckBranchBad` excludes. That trace therefore does not refute this target.

The prefix trace below records the actual layers, including their saved tuples.
It does not assume that the multiplication gadgets returned correct products.
The circuit argument reuses `stages_layer_correct` from the GS20 main proof.
The pinned and current leanVM proofs were searched; this replicated-share
prefix invariant is specific to the threshold protocol.

`treeCheck_batch_saved_correct` applies this induction to an actual joint
`treeCheckBatchPre`. `treeCheck_open_reject` combines it with an actual
successful opening of those same saved copies outside the budget collision
event. Its explicit `MainInputs` premise is about the prefix's input shares.
The theorem has no assertion about the probability of GS20 acceptance.

`TreeCheckBatchWalkParts` requires a whole-run witness. In particular,
the global walk must produce the common batch/check/open boundaries, including
operators that later abort, prove the actual PRF inputs satisfy `MainInputs`
and have the dealer's plain values, and relate the opened output to the indexed
bad record. The existing named `Split`, `Unreached`, `Consistent`, `Jobs`,
`Queries`, `Cache`, `Prior`, `Budget` and `Transport` obligations are unchanged;
the local implication here does not close the global `Reject` obligation.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

/-- The algebraic trace of the real circuit layers. Multiplication outputs
are arbitrary; correctness is established only when verification accepts. -/
inductive TreeCheckLayerTrace (mode : ReshareMode) (jobs : List Circuit)
    (inputs : MainInput C) : ℕ → (MainInput C × List (Tuple C)) → Prop
  | zero : TreeCheckLayerTrace mode jobs inputs 0 (inputs, [])
  | step {n p} (trace : TreeCheckLayerTrace mode jobs inputs n p) (z : Shares C Bit) :
      TreeCheckLayerTrace mode jobs inputs (n + 1)
        (appendLayer jobs n p.1 z,
          p.2 ++ [⟨layerX K jobs n p.1, layerY K jobs n p.1, z,
            (gatesAt jobs n).length, mode⟩])

namespace TreeCheckLayerTrace

variable {K} {mode : ReshareMode} {jobs : List Circuit} {inputs : MainInput C}

theorem at_zero {p : MainInput C × List (Tuple C)}
    (h : TreeCheckLayerTrace K mode jobs inputs 0 p) : p = (inputs, []) := by
  cases h
  rfl

theorem lengths {n : ℕ} {p : MainInput C × List (Tuple C)}
    (h : TreeCheckLayerTrace K mode jobs inputs n p) :
    p.1.length = inputs.length ∧ p.2.length = n := by
  induction h with
  | zero => simp
  | step h z ih => simpa [appendLayer] using ih

theorem step_iff {n : ℕ} {p : MainInput C × List (Tuple C)} :
    TreeCheckLayerTrace K mode jobs inputs (n + 1) p ↔
      ∃ prev z, TreeCheckLayerTrace K mode jobs inputs n prev ∧
        p = (appendLayer jobs n prev.1 z,
          prev.2 ++ [⟨layerX K jobs n prev.1, layerY K jobs n prev.1, z,
            (gatesAt jobs n).length, mode⟩]) := by
  constructor
  · intro h
    cases h with
    | step h z => exact ⟨_, z, h, rfl⟩
  · rintro ⟨prev, z, h, rfl⟩
    exact h.step z

theorem shape {n : ℕ} {p : MainInput C × List (Tuple C)}
    (h : TreeCheckLayerTrace K mode jobs inputs n p) :
    p.2.map (fun t => (t.count, t.mode)) =
      (List.range n).map (fun l => ((gatesAt jobs l).length, mode)) := by
  induction h with
  | zero => rfl
  | step h z ih => simp only [List.map_append, List.map_cons, List.map_nil,
      List.range_succ, ih]

end TreeCheckLayerTrace

/-- Successful real layer execution supplies the trace; no tuple-correctness
or agreement hypothesis enters this extraction. -/
theorem treeCheck_layers_trace {ι : Type} {G : OracleSpec ι}
    (gadgets : RunGadgets C E G) (jobs : List Circuit) (inputs : MainInput C)
    (n : ℕ) (initial final : RunState C) (p : MainInput C × List (Tuple C))
    (run : some (p, final) ∈ support (((List.range n).foldlM
      (layerBody K gadgets jobs) (inputs, [])).run initial).run) :
    TreeCheckLayerTrace K gadgets.mode jobs inputs n p := by
  induction n generalizing p final with
  | zero =>
    simp only [List.range_zero, List.foldlM_nil, StateT.run_pure, OptionT.run_pure,
      support_pure, Set.mem_singleton_iff, Option.some.injEq] at run
    cases run
    exact .zero
  | succ n ih =>
    rw [List.range_succ, List.foldlM_append] at run
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure, StateT.run_bind] at run
    obtain ⟨prev, hprev, hlast⟩ := treeSimCheck_some_bind _ _ _ run
    unfold layerBody at hlast
    simp only [StateT.run_bind, StateT.run_pure] at hlast
    obtain ⟨z, _, he⟩ := treeSimCheck_some_bind _ _ _ hlast
    have eq : (p, final) = ((appendLayer jobs n prev.1.1 z.1,
        prev.1.2 ++ [⟨layerX K jobs n prev.1.1, layerY K jobs n prev.1.1, z.1,
          (gatesAt jobs n).length, gadgets.mode⟩]), z.2) := by
      simpa only [OptionT.run_pure, support_pure, Set.mem_singleton_iff,
        Option.some.injEq] using he
    cases eq
    exact (ih prev.2 prev.1 hprev).step z.1

/-- The saved pre-check values retain the real layer trace and its final
rerandomization tuple. -/
theorem treeCheck_beforeVerify_trace (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : MainInput C) (initial final : RunState C)
    (v : Shares C Bit) (tuples : List (Tuple C))
    (run : some ((v, tuples), final) ∈ support
      ((treeSimCheckBeforeVerify K ctx mode jobs inputs).run initial).run) :
    ∃ p, TreeCheckLayerTrace K mode jobs inputs (depth jobs) p ∧
      tuples = p.2 ++ [⟨outputShares K jobs p.1, one K, v, (outputsOf jobs).length, .peer⟩] := by
  unfold treeSimCheckBeforeVerify at run
  simp only [StateT.run_bind, StateT.run_pure] at run
  obtain ⟨p, hp, htail⟩ := treeSimCheck_some_bind _ _ _ run
  obtain ⟨z, _, he⟩ := treeSimCheck_some_bind _ _ _ htail
  have eq : ((v, tuples), final) = ((z.1, p.1.2 ++
      [⟨outputShares K jobs p.1.1, one K, z.1, (outputsOf jobs).length, .peer⟩]), z.2) := by
    simpa only [OptionT.run_pure, support_pure, Set.mem_singleton_iff,
      Option.some.injEq] using he
  cases eq
  exact ⟨p.1, treeCheck_layers_trace K (realRunGadgets K ctx mode) jobs inputs
    (depth jobs) initial p.2 p.1 hp, rfl⟩

/-- Agreement and product correctness at an index depend only on the honest
tuples at that index. Corrupt local views are unrestricted. -/
theorem treeCheck_tuple_good_congr (D : C.Coalition)
    (a b : C.Party → List (Tuple C)) (m : ℕ)
    (same : ∀ i, i ∉ D.1 → (a i)[m]? = (b i)[m]?) :
    (stagesAgreeAt D a m ∧ stagesProductAt D a m) ↔
      (stagesAgreeAt D b m ∧ stagesProductAt D b m) := by
  have agree : stagesAgreeAt D a m ↔ stagesAgreeAt D b m := by
    unfold stagesAgreeAt
    refine forall_congr' fun T => forall₂_congr fun i hi =>
      forall₂_congr fun j hj => forall_congr' fun hiD => forall_congr' fun hjD => ?_
    rw [same i hiD, same j hjD]
  have product : stagesProductAt D a m ↔ stagesProductAt D b m := by
    unfold stagesProductAt
    rw [stages_tupleAt_congr D a b m same]
  exact and_congr agree product

/-- The deterministic verification bit checks each tuple, not merely the
randomized linear combination used by the protocol. -/
theorem treeCheck_verified_tuples (D : C.Coalition)
    (views : C.Party → List (Tuple C)) (N : ℕ)
    (lengths : ∀ i, i ∉ D.1 → (views i).length = N)
    (shape : ∀ i, i ∉ D.1 → ∀ j, j ∉ D.1 →
      (views i).map (fun t => (t.count, t.mode)) =
        (views j).map (fun t => (t.count, t.mode)))
    (accept : (multVerifyLeak D (stagesHonest D views)).2.2) :
    ∀ m < N, stagesAgreeAt D views m ∧ stagesProductAt D views m := by
  have count : (firstInput (stagesHonest D views)).length = N :=
    stages_firstInput D views (fun v => v.length = N) lengths
  change decide (_ ∧ _) = true at accept
  obtain ⟨agree, product⟩ := of_decide_eq_true accept
  rw [count] at agree product
  have hag := (stages_realAgree_iff D views N lengths shape).mp agree
  intro m hm
  refine ⟨hag m hm, ?_⟩
  exact product _ (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩)

/-- Correct accepted tuples determine correct circuit wires even if the
actual multiplication outputs were chosen maliciously. This induction uses
the extracted prefix trace, not an assumed ideal execution. -/
theorem treeCheck_layers_correct (D : C.Coalition) (mode : ReshareMode)
    (jobs : List Circuit) (x : C.Party → MainInput C)
    (inputs : MainInputs jobs D x) (n : ℕ)
    (p : C.Party → MainInput C × List (Tuple C))
    (traces : ∀ i, i ∉ D.1 → TreeCheckLayerTrace K mode jobs (x i) n (p i))
    (correct : ∀ m < n, stagesAgreeAt D (fun i => (p i).2) m ∧
      stagesProductAt D (fun i => (p i).2) m) :
    ∃ W Ts, LayerInv jobs (stagesX D x) n (fun _ => (W, Ts)) W Ts ∧
      ∀ i, i ∉ D.1 → ∀ T, i ∈ C.holders T → ∀ k,
        ((p i).1.getD k fun _ => []) T = (W.getD k fun _ => []) T := by
  induction n generalizing p with
  | zero =>
    obtain ⟨W, Ts, inv, held⟩ := (stages_inv_zero D jobs x inputs).correct (by simp)
    refine ⟨W, Ts, inv, fun i hi T hiT k => ?_⟩
    have eq : p i = (x i, []) := (traces i hi).at_zero
    simpa only [eq] using held i hi T hiT k
  | succ n ih =>
    have steps : ∀ i, ∃ prev z, i ∉ D.1 →
        TreeCheckLayerTrace K mode jobs (x i) n prev ∧
        p i = (appendLayer jobs n prev.1 z,
          prev.2 ++ [⟨layerX K jobs n prev.1, layerY K jobs n prev.1, z,
            (gatesAt jobs n).length, mode⟩]) := by
      intro i
      by_cases hi : i ∈ D.1
      · exact ⟨([], []), fun _ _ => 0, fun h => (h hi).elim⟩
      · obtain ⟨prev, z, ht, he⟩ := TreeCheckLayerTrace.step_iff.mp (traces i hi)
        exact ⟨prev, z, fun _ => ⟨ht, he⟩⟩
    choose prev z step using steps
    have ht : ∀ i, i ∉ D.1 → TreeCheckLayerTrace K mode jobs (x i) n (prev i) :=
      fun i hi => (step i hi).1
    have hlen : ∀ i, i ∉ D.1 → (prev i).2.length = n :=
      fun i hi => (ht i hi).lengths.2
    have old : ∀ m < n, stagesAgreeAt D (fun i => (prev i).2) m ∧
        stagesProductAt D (fun i => (prev i).2) m := by
      intro m hm
      refine (treeCheck_tuple_good_congr D (fun i => (p i).2)
        (fun i => (prev i).2) m ?_).mp (correct m (by omega))
      intro i hi
      rw [(step i hi).2]
      exact stages_getElem?_append_lt _ _ m (by rw [hlen i hi]; exact hm)
    obtain ⟨W, Ts, inv, held⟩ := ih prev ht old
    have last := (treeCheck_tuple_good_congr D (fun i => (p i).2)
      (fun i => (prev i).2 ++ [⟨layerX K jobs n (prev i).1,
        layerY K jobs n (prev i).1, z i, (gatesAt jobs n).length, mode⟩]) n
      (fun i hi => by rw [(step i hi).2])).mp (correct n (by omega))
    have width : ∀ i, i ∉ D.1 → (prev i).1.length = jobs.length := by
      intro i hi
      rw [(ht i hi).lengths.1]
      exact (inputs.choose_spec.2.1 i hi).1
    obtain ⟨W', Ts', inv', held'⟩ := stages_layer_correct K D mode jobs x n
      (fun i => (prev i).1) z (fun i => (prev i).2) n W Ts hlen inv held width last.1 last.2
    refine ⟨W', Ts', inv', fun i hi T hiT k => ?_⟩
    simpa only [(step i hi).2] using held' i hi T hiT k

/-- The tuples handed to verification, including the saved output sharing. -/
def treeCheckSavedTuples (jobs : List Circuit)
    (p : C.Party → MainInput C × List (Tuple C)) (v : C.Party → Shares C Bit) :
    C.Party → List (Tuple C) := fun i => (p i).2 ++
      [⟨outputShares K jobs (p i).1, one K, v i, (outputsOf jobs).length, .peer⟩]

/-- Deterministically accepted tuples force the saved output sharing to be
the circuit output. The representative is an honest holder of each term. -/
theorem treeCheck_saved_correct (D : C.Coalition) (mode : ReshareMode)
    (jobs : List Circuit) (x : C.Party → MainInput C)
    (inputs : MainInputs jobs D x)
    (p : C.Party → MainInput C × List (Tuple C)) (v : C.Party → Shares C Bit)
    (traces : ∀ i, i ∉ D.1 → TreeCheckLayerTrace K mode jobs (x i) (depth jobs) (p i))
    (accept : (multVerifyLeak D (stagesHonest D (treeCheckSavedTuples K jobs p v))).2.2) :
    (∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < (outputsOf jobs).length →
      v i T g = v (refHolder D T) T g) ∧
    assemble jobs (shareValue (fun T => v (refHolder D T) T)) =
      mainOutputs jobs (stagesX D x) := by
  let views := treeCheckSavedTuples K jobs p v
  have lengths : ∀ i, i ∉ D.1 → (p i).2.length = depth jobs :=
    fun i hi => (traces i hi).lengths.2
  have hlen : ∀ i, i ∉ D.1 → (views i).length = depth jobs + 1 := by
    intro i hi
    simp [views, treeCheckSavedTuples, lengths i hi]
  have shape : ∀ i, i ∉ D.1 → ∀ j, j ∉ D.1 →
      (views i).map (fun t => (t.count, t.mode)) =
        (views j).map (fun t => (t.count, t.mode)) := by
    intro i hi j hj
    simp only [views, treeCheckSavedTuples, List.map_append, (traces i hi).shape,
      (traces j hj).shape, List.map_cons, List.map_nil]
  have good := treeCheck_verified_tuples D views (depth jobs + 1) hlen shape accept
  have layers : ∀ m < depth jobs, stagesAgreeAt D (fun i => (p i).2) m ∧
      stagesProductAt D (fun i => (p i).2) m := by
    intro m hm
    refine (treeCheck_tuple_good_congr D views (fun i => (p i).2) m ?_).mp (good m (by omega))
    intro i hi
    exact stages_getElem?_append_lt _ _ m (by rw [lengths i hi]; exact hm)
  obtain ⟨W, Ts, inv, wires⟩ := treeCheck_layers_correct K D mode jobs x inputs (depth jobs) p traces layers
  have last (i : C.Party) (hi : i ∉ D.1) : (views i)[depth jobs]? =
      some ⟨outputShares K jobs (p i).1, one K, v i, (outputsOf jobs).length, .peer⟩ := by
    change ((p i).2 ++ [_])[depth jobs]? = _
    rw [← lengths i hi]
    exact stages_getElem?_append_eq _ _
  have lastAt (i : C.Party) (hi : i ∉ D.1) : stagesAt views i (depth jobs) =
      ⟨outputShares K jobs (p i).1, one K, v i, (outputsOf jobs).length, .peer⟩ := by
    unfold stagesAt
    rw [last i hi]
    rfl
  have reached : ∀ i, i ∉ D.1 → depth jobs < (views i).length := by
    intro i hi
    rw [hlen i hi]
    omega
  have held : ∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < (outputsOf jobs).length →
      v i T g = v (refHolder D T) T g := by
    intro i T g hi hiT hg
    obtain ⟨hrT, hr⟩ := refHolder_spec D T
    have eq := (good (depth jobs) (by omega)).1 T i hiT (refHolder D T) hrT hi hr g
      (by rw [last i hi]; exact hg)
    rw [last i hi, last _ hr] at eq
    exact congrArg (fun a => a.2.2) (Option.some.inj eq)
  refine ⟨held, assemble_eq K jobs (stagesX D x) (fun _ => (W, Ts)) W Ts inv _ ?_⟩
  intro g hg
  have count : (tupleAt (stagesHonest D views) (depth jobs)).count = (outputsOf jobs).length :=
    stages_tupleAt_count' D views (depth jobs) (outputsOf jobs).length
      (fun i hi => by rw [last i hi]; rfl)
  have product := (good (depth jobs) (by omega)).2 g (by rw [count]; exact hg)
  have hx : shareValue (tupleAt (stagesHonest D views) (depth jobs)).x g =
      shareValue (outputShares K jobs W) g := by
    unfold shareValue
    refine Finset.sum_congr rfl fun T _ => ?_
    obtain ⟨i, hiT, hi, eq⟩ := stages_tupleAt_x D views (depth jobs) reached T
    rw [eq, lastAt i hi]
    exact congrFun (outputShares_congr K jobs (p i).1 W T (wires i hi T hiT)) g
  have hy : shareValue (tupleAt (stagesHonest D views) (depth jobs)).y g = 1 := by
    rw [← shareValue_one K g]
    unfold shareValue
    refine Finset.sum_congr rfl fun T _ => ?_
    obtain ⟨i, _, hi, eq⟩ := stages_tupleAt_y D views (depth jobs) reached T
    rw [eq, lastAt i hi]
  have hz : shareValue (tupleAt (stagesHonest D views) (depth jobs)).z g =
      shareValue (fun T => v (refHolder D T) T) g := by
    unfold shareValue
    refine Finset.sum_congr rfl fun T _ => ?_
    obtain ⟨i, hiT, hi, eq⟩ := stages_tupleAt_z D views (depth jobs) reached T
    rw [eq, lastAt i hi]
    exact held i T g hi hiT hg
  rw [hz, hx, hy, mul_one] at product
  exact product

/-- Data retained by the actual batch prefix, with a default used only for
operators absent from that prefix. Live honest operators never use it. -/
def treeCheckPrefixData (o : Option (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C)) :
    MainInput C × (Shares C Bit × List (Tuple C)) × RunState C :=
  o.getD ([], ((fun _ _ => 0, []), ⟨fun _ => [], 0, 0⟩))

theorem treeCheck_batchPrefix_trace (circuits : Circuits) (settings : Settings)
    (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ)
    (data : MainInput C × (Shares C Bit × List (Tuple C)) × RunState C)
    (run : some data ∈ support (treeSimCheckBatchPrefix K circuits settings ctx jobs initial).run) :
    ∃ p, TreeCheckLayerTrace K settings.mode
      (jobs.map (circuits ctx.keys.parameter ·.kind)) data.1
      (depth (jobs.map (circuits ctx.keys.parameter ·.kind))) p ∧
      data.2.1.2 = p.2 ++ [⟨outputShares K (jobs.map (circuits ctx.keys.parameter ·.kind)) p.1,
        one K, data.2.1.1, (outputsOf (jobs.map (circuits ctx.keys.parameter ·.kind))).length, .peer⟩] := by
  unfold treeSimCheckBatchPrefix at run
  obtain ⟨inputs, _, htail⟩ := treeSimCheck_some_bind _ _ _ run
  obtain ⟨out, hout, he⟩ := treeSimCheck_some_bind _ _ _ htail
  have eq : data = (inputs, out) := by
    simpa only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] using he
  cases eq
  exact treeCheck_beforeVerify_trace K ctx settings.mode _ inputs _ out.2 out.1.1 out.1.2 hout

/-- At an actual joint batch checkpoint, deterministic verification implies
correct saved outputs. `inputs` refers to that checkpoint's actual PRF input
shares; it is not an ideal-output or rejection assumption. -/
theorem treeCheck_batch_saved_correct (prims : Primitives) (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (b : TreeCheckBatchBoundary A)
    (parameter : ∀ i, (b.ctx i).keys.parameter = b.parameter)
    (o : (A.State × (C.Party → Option
      (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (run : o ∈ support (treeCheckBatchPre prims K circuits settings D A b))
    (live : ∀ i, i ∉ D.1 → (o.1.2 i).isSome)
    (inputs : MainInputs (b.jobs.map (circuits b.parameter ·.kind)) D
      (fun i => (treeCheckPrefixData (o.1.2 i)).1))
    (accept : (multVerifyLeak D (stagesHonest D
      (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.2))).2.2) :
    let js := b.jobs.map (circuits b.parameter ·.kind)
    let v := fun i => (treeCheckPrefixData (o.1.2 i)).2.1.1
    (∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < (outputsOf js).length →
      v i T g = v (refHolder D T) T g) ∧
    assemble js (shareValue (fun T => v (refHolder D T) T)) =
      mainOutputs js (stagesX D (fun i => (treeCheckPrefixData (o.1.2 i)).1)) := by
  dsimp only
  obtain ⟨log, replay⟩ := treeSimCheckReplay_of_support _ _
    (treeCheck_logged_support prims D _ _ run)
  have traces : ∀ i, ∃ p, i ∉ D.1 →
      TreeCheckLayerTrace K settings.mode (b.jobs.map (circuits b.parameter ·.kind))
        (treeCheckPrefixData (o.1.2 i)).1 (depth (b.jobs.map (circuits b.parameter ·.kind))) p ∧
      (treeCheckPrefixData (o.1.2 i)).2.1.2 = p.2 ++
        [⟨outputShares K (b.jobs.map (circuits b.parameter ·.kind)) p.1, one K,
          (treeCheckPrefixData (o.1.2 i)).2.1.1,
          (outputsOf (b.jobs.map (circuits b.parameter ·.kind))).length, .peer⟩] := by
    intro i
    by_cases hi : i ∈ D.1
    · exact ⟨([], []), fun h => (h hi).elim⟩
    obtain ⟨data, hd⟩ := Option.isSome_iff_exists.mp (live i hi)
    have localRun := treeSimCheck_phase_replay D A noFunctionality (fun _ _ => True)
      (b.rounds circuits settings) b.state _ o.1 ⟨log, replay, fun _ _ _ => trivial⟩ i hi data hd
    obtain ⟨_, localRun, _⟩ := localRun
    obtain ⟨p, ht, he⟩ := treeCheck_batchPrefix_trace K circuits settings (b.ctx i) b.jobs b.initial
      data localRun.mem_support
    refine ⟨p, fun _ => ?_⟩
    simpa only [hd, treeCheckPrefixData, Option.getD_some, parameter i] using And.intro ht he
  choose p hp using traces
  have eq : stagesHonest D (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.2) =
      stagesHonest D (treeCheckSavedTuples K (b.jobs.map (circuits b.parameter ·.kind)) p
        (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.1)) := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [stagesHonest, hi]
    · simp only [stagesHonest, if_neg hi, treeCheckSavedTuples, (hp i hi).2]
  rw [eq] at accept
  exact treeCheck_saved_correct K D settings.mode _ _ inputs p _ (fun i hi => (hp i hi).1) accept

section Opening

variable (prims : Primitives) (circuits : Circuits) (settings : Settings)
variable (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
variable (b : TreeCheckBatchBoundary A)
variable (o : (A.State × (C.Party → Option
  (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)

set_option quotPrecheck false
local notation "js" => b.jobs.map (circuits b.parameter ·.kind)
local notation "saved" => fun i => (treeCheckPrefixData (o.1.2 i)).2.1.1
local notation "inputViews" => fun i => (treeCheckPrefixData (o.1.2 i)).1
local notation "tupleViews" => fun i => (treeCheckPrefixData (o.1.2 i)).2.1.2

set_option maxHeartbeats 800000 in
/-- A successful actual opening of these saved copies returns the plain
circuit outputs when deterministic verification accepts. The sent copy
hashes and the collision guard concern the actual opening log. -/
theorem treeCheck_open_saved_correct
    (parameter : ∀ i, (b.ctx i).keys.parameter = b.parameter)
    (pref : o ∈ support (treeCheckBatchPre prims K circuits settings D A b))
    (present : ∀ i, i ∉ D.1 → (o.1.2 i).isSome)
    (inputs : MainInputs js D inputViews)
    (accept : (multVerifyLeak D (stagesHonest D tupleViews)).2.2)
    (live : C.Party → Bool) (ds : C.Party → List HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) (s final : TreeSimState C) (out : ℕ → Bit)
    (hashes : ∀ h, h ∉ D.1 → live h = true →
      (ds h).length = C.terms.length ∧ ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer s.2 (.copy (vector (outputsOf js).length (saved h T))) u)
    (run : (some out, final) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (treeSimOpenHead K D live (outputsOf js).length saved ds sent i)
        (LocalSpec C)))).run s))
    (good : ¬ TreeSimHashBudgetCollision final.2) :
    assemble js out = mainOutputs js (stagesX D inputViews) := by
  obtain ⟨held, correct⟩ := treeCheck_batch_saved_correct K prims circuits settings D A b parameter
    o pref present inputs accept
  have value : ∀ g < (outputsOf js).length,
      out g = shareValue (fun T => saved (refHolder D T) T) g := by
    with_reducible
      exact treeLockstep_open_head_value prims K D live (outputsOf js).length saved
        (fun T => saved (refHolder D T) T) held ds sent i s final out hashes run good
  exact (treeLockstep_assemble_congr js out
    (shareValue (fun T => saved (refHolder D T) T)) value).trans correct

/-- A wrong output of the actual opening cannot coexist with deterministic
acceptance of the checkpoint tuples. This is the local `Reject` implication;
the global walk must still produce these boundaries and its dealer input link. -/
theorem treeCheck_open_reject
    (parameter : ∀ i, (b.ctx i).keys.parameter = b.parameter)
    (pref : o ∈ support (treeCheckBatchPre prims K circuits settings D A b))
    (present : ∀ i, i ∉ D.1 → (o.1.2 i).isSome)
    (inputs : MainInputs js D inputViews)
    (live : C.Party → Bool) (ds : C.Party → List HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) (s final : TreeSimState C) (out : ℕ → Bit)
    (hashes : ∀ h, h ∉ D.1 → live h = true →
      (ds h).length = C.terms.length ∧ ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer s.2 (.copy (vector (outputsOf js).length (saved h T))) u)
    (run : (some out, final) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (treeSimOpenHead K D live (outputsOf js).length saved ds sent i)
        (LocalSpec C)))).run s))
    (good : ¬ TreeSimHashBudgetCollision final.2)
    (wrong : assemble js out ≠ mainOutputs js (stagesX D inputViews)) :
    ¬ (multVerifyLeak D (stagesHonest D tupleViews)).2.2 := by
  intro accept
  exact wrong (treeCheck_open_saved_correct K prims circuits settings D A b o parameter pref
    present inputs accept live ds sent i s final out hashes run good)

end Opening

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_layers_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_layers_trace

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_layers_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_layers_correct

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_batch_saved_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_batch_saved_correct

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_open_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_open_reject

end ThresholdLeanXmssSecurity
