import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkCoverage

/-!
# Tuple consistency of the fixed source walk

This file concerns `WalkConsistent` of the fixed family `family` of
`TreeCheckWalkRecipe`. The family, its decoder and its witness are not changed.

## The route

`Consistent` starts at a decoded checkpoint `(c, o)`. So `decode_sound` gives
`Fits`, and `o` is in the support of the canonical `boundary.pre`. This file
does not use the coverage of the walk, and it does not use
`selected_signing_decode_hit` or its `fixed` premise.

At a decoded checkpoint all operators run the same jobs from the same counters,
the same adversary state and the same world. Only the context
`⟨i, x i, setupKeys setup i⟩` differs. The input shares of the batch are PRF
shares of public points, computed again from the seeds (`inputShares`). The
opened outputs of earlier batches fix the signing encoding and so the jobs, but
the decoded boundary fixes those jobs for all operators, and no earlier output
is an input wire of batch `j`. So the term `D` of a coalition with `t - 1`
operators needs no separate argument here.

## Lemmas

* `wiresAt T w` is the list of the term `T` parts of the wires `w`.
  `layerX_congr`, `layerY_congr`, `outputShares_congr` and
  `appendLayer_congr` show that the term `T` part of a layer depends only on
  the term `T` part of its wires and of its products.
* `trace_agree` and `saved_agree` show that two traces of the real layers
  (`TreeCheckLayerTrace`) with equal term `T` inputs and equal term `T`
  products have equal term `T` parts of `x`, `y` and `z` in each tuple.
* `products_of_parts` joins the products that a corrupt operator fills and the
  other products into all products.
* `consistent_of_transcript` gives `Consistent` for a walk with standard
  tuples from `Transcript` of the same walk.
* `walkConsistent_of_transcript` gives `WalkConsistent` from
  `WalkTranscript`.

## The transcript clause

`Transcript` holds at the same supported live checkpoints as `Consistent`.
For each term `T` and two honest holders of `T` with checkpoint rows, it states
two equalities.

* The term `T` parts of the input shares are equal.
* The term `T` parts of the products in each saved tuple are equal at each
  position that no corrupt operator fills (`unfilledView`).

It has no premise on the tuples, and it states nothing about `x` and `y`.

## Truth of the transcript clause

`TreeCheckWalkTranscript.walkTranscript` proves the transcript clause in Lean,
along this argument.

* Each honest holder of `T` queries `prf (seed T)` on the same public points.
  The seeds agree by `DealtInputs`. `streamWorld` answers a query from its
  caches, which only grow, so equal queries get equal answers.
* In peer mode `z T g` is the value of the filler of `T`
  (`treeSim_reshareZ_value`). An honest filler sends one value to all
  holders. A term with no filler gets the PRSS mask `r T g`. Collector mode
  uses the collector of gate `g` in the same way. The final `rerand` uses
  peer mode.
* Equal masks need equal term keys and equal labels. The labels start at the
  common counters. `treeAgreementSetupKeys` gives equal term keys when the
  setup log has no budget collision. The log of the counted bad continuation
  of a live checkpoint extends the setup log (`sourceWalk_log_prefix`), and it
  has no budget collision.
* `treeAgreementSetupKeys` needs `setup i = some _`. By `initial_program`, an
  honest operator with no setup row has the program `failure` at the start of
  the walk. An aborted program stays aborted along the walk, and by `Fits` its
  canonical first local pass aborts. So it has no checkpoint row.

`TreeCheckMaskExtraction.layers_replay` gives a joint replay of the layers only
for the empty coalition. `TreeCheckWalkTranscript` gives the replay for a
nonempty coalition.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option linter.unusedSectionVars false

noncomputable section

namespace ThresholdLeanXmssSecurity
namespace TreeCheckWalkConsistent

open TreeCheckWalkRecipe TreeCheckWalkCoverage

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

section Algebra

/-- The term `T` parts of a list of wires. -/
def wiresAt (T : C.Term) (w : MainInput C) : List (List Bit) := w.map (· T)

/-- The term `T` parts of `x`, `y` and `z` of a tuple, as in `TupleInputs`. -/
def tupleView (T : C.Term) (τ : Tuple C) : List Bit × List Bit × List Bit :=
  (vector τ.count (τ.x T), vector τ.count (τ.y T), vector τ.count (τ.z T))

/-- The term `T` part of the products of a tuple. -/
def productView (T : C.Term) (τ : Tuple C) : List Bit := vector τ.count (τ.z T)

variable (D : C.Coalition)

/-- The products of a tuple at the positions that a corrupt operator fills, as
in the premise of `TupleInputs`. -/
def filledView (T : C.Term) (τ : Tuple C) : List Bit :=
  vector τ.count fun g => if ∃ j ∈ D.1, filler K τ.mode T g = some j then τ.z T g else 0

/-- The products of a tuple at the positions that no corrupt operator fills. -/
def unfilledView (T : C.Term) (τ : Tuple C) : List Bit :=
  vector τ.count fun g => if ∃ j ∈ D.1, filler K τ.mode T g = some j then 0 else τ.z T g

omit [Fintype E] [DecidableEq E] in
theorem vector_eq {R : Type} {n m : ℕ} {f g : ℕ → R} (h : vector n f = vector m g) :
    n = m ∧ ∀ a < n, f a = g a := by
  have hl := congrArg List.length h
  simp only [vector, List.length_map, List.length_range] at hl
  subst hl
  refine ⟨rfl, fun a ha => ?_⟩
  have point := congrArg (·[a]?) h
  simpa [vector, ha] using point

omit [Fintype E] [DecidableEq E] in
theorem vector_congr {R : Type} {n : ℕ} {f g : ℕ → R} (h : ∀ a < n, f a = g a) :
    vector n f = vector n g := by
  unfold vector
  exact List.map_congr_left fun a ha => h a (List.mem_range.mp ha)

omit [Fintype E] [DecidableEq E] in
theorem getD_at (T : C.Term) (w : MainInput C) (k : ℕ) :
    (w.getD k fun _ => []) T = (wiresAt T w).getD k [] := by
  unfold wiresAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[k]? <;> rfl

omit [Fintype E] [DecidableEq E] in
theorem share_congr (a : Affine) (T publicTerm : C.Term) {w w' : MainInput C} (k : ℕ)
    (same : wiresAt T w = wiresAt T w') :
    a.share (w.getD k fun _ => []) publicTerm T = a.share (w'.getD k fun _ => []) publicTerm T := by
  unfold Affine.share
  rw [getD_at T w k, getD_at T w' k, same]

omit [Fintype E] [DecidableEq E] in
theorem layerX_congr (jobs : List Circuit) (n : ℕ) (T : C.Term) {w w' : MainInput C}
    (same : wiresAt T w = wiresAt T w') : layerX K jobs n w T = layerX K jobs n w' T := by
  funext g
  unfold layerX
  rcases (gatesAt jobs n)[g]? with _ | ⟨k, ab⟩
  · rfl
  · exact share_congr ab.1 T K.publicTerm k same

omit [Fintype E] [DecidableEq E] in
theorem layerY_congr (jobs : List Circuit) (n : ℕ) (T : C.Term) {w w' : MainInput C}
    (same : wiresAt T w = wiresAt T w') : layerY K jobs n w T = layerY K jobs n w' T := by
  funext g
  unfold layerY
  rcases (gatesAt jobs n)[g]? with _ | ⟨k, ab⟩
  · rfl
  · exact share_congr ab.2 T K.publicTerm k same

omit [Fintype E] [DecidableEq E] in
theorem outputShares_congr (jobs : List Circuit) (T : C.Term) {w w' : MainInput C}
    (same : wiresAt T w = wiresAt T w') : outputShares K jobs w T = outputShares K jobs w' T := by
  funext g
  unfold outputShares
  rcases (outputsOf jobs)[g]? with _ | ⟨k, a⟩
  · rfl
  · exact share_congr a T K.publicTerm k same

omit [Fintype E] [DecidableEq E] in
theorem appendLayer_congr (jobs : List Circuit) (n : ℕ) (T : C.Term) {w w' : MainInput C}
    {z z' : Shares C Bit} (same : wiresAt T w = wiresAt T w')
    (products : ∀ g < (gatesAt jobs n).length, z T g = z' T g) :
    wiresAt T (appendLayer jobs n w z) = wiresAt T (appendLayer jobs n w' z') := by
  have hl : w.length = w'.length := by
    simpa only [wiresAt, List.length_map] using congrArg List.length same
  apply List.ext_getElem
  · simp [wiresAt, appendLayer, hl]
  · intro k hk hk'
    have hw : k < w.length := by simpa [wiresAt, appendLayer] using hk
    have entry : w[k] T = w'[k] T := by
      have point := congrArg (·[k]?) same
      simpa [wiresAt, hw, hl ▸ hw] using point
    simp only [wiresAt, appendLayer, List.getElem_map, List.getElem_zipIdx]
    rw [entry]
    congr 1
    apply List.map_congr_left
    rintro ⟨gate, g⟩ hmem
    have hg : g < (gatesAt jobs n).length := by
      have := (List.mem_filter.mp hmem).1
      simpa using (List.mem_zipIdx this).2.1
    exact products g hg

/-- Two traces of the real layers with equal term `T` inputs and products have
equal term `T` wires and tuples. The products may be arbitrary. -/
theorem trace_agree (T : C.Term) (mode : ReshareMode) (jobs : List Circuit)
    {a b : MainInput C} {n : ℕ} {p q : MainInput C × List (Tuple C)}
    (hp : TreeCheckLayerTrace K mode jobs a n p) (hq : TreeCheckLayerTrace K mode jobs b n q)
    (inputs : wiresAt T a = wiresAt T b)
    (products : p.2.map (productView T) = q.2.map (productView T)) :
    wiresAt T p.1 = wiresAt T q.1 ∧ p.2.map (tupleView T) = q.2.map (tupleView T) := by
  induction hp generalizing q with
  | zero =>
    rw [hq.at_zero]
    exact ⟨inputs, rfl⟩
  | step trace z ih =>
    rename_i m prev
    obtain ⟨prev', z', trace', rfl⟩ := TreeCheckLayerTrace.step_iff.mp hq
    have lengths : (prev.2.map (productView T)).length = (prev'.2.map (productView T)).length := by
      simp only [List.length_map, trace.lengths.2, trace'.lengths.2]
    simp only [List.map_append, List.map_cons, List.map_nil] at products
    obtain ⟨before, last⟩ := List.append_inj products lengths
    have last := List.cons.inj last
    obtain ⟨-, values⟩ := vector_eq last.1
    obtain ⟨wires, tuples⟩ := ih trace' before
    refine ⟨appendLayer_congr jobs m T wires values, ?_⟩
    have zs : vector (gatesAt jobs m).length (z T) = vector (gatesAt jobs m).length (z' T) := last.1
    simp only [List.map_append, List.map_cons, List.map_nil, tuples, tupleView]
    rw [layerX_congr K jobs m T wires, layerY_congr K jobs m T wires, zs]

/-- The saved tuples of two traces, with the final `rerand` tuple, have equal
term `T` parts when their inputs and products have equal term `T` parts. -/
theorem saved_agree (T : C.Term) (mode : ReshareMode) (jobs : List Circuit)
    {a b : MainInput C} {p q : MainInput C × List (Tuple C)} (v v' : Shares C Bit)
    (hp : TreeCheckLayerTrace K mode jobs a (depth jobs) p)
    (hq : TreeCheckLayerTrace K mode jobs b (depth jobs) q)
    (inputs : wiresAt T a = wiresAt T b)
    (products : (p.2 ++ [Tuple.mk (outputShares K jobs p.1) (one K) v (outputsOf jobs).length .peer]).map
        (productView T) =
      (q.2 ++ [Tuple.mk (outputShares K jobs q.1) (one K) v' (outputsOf jobs).length .peer]).map
        (productView T)) :
    (p.2 ++ [Tuple.mk (outputShares K jobs p.1) (one K) v (outputsOf jobs).length .peer]).map
        (tupleView T) =
      (q.2 ++ [Tuple.mk (outputShares K jobs q.1) (one K) v' (outputsOf jobs).length .peer]).map
        (tupleView T) := by
  have lengths : (p.2.map (productView T)).length = (q.2.map (productView T)).length := by
    simp only [List.length_map, hp.lengths.2, hq.lengths.2]
  simp only [List.map_append, List.map_cons, List.map_nil] at products
  obtain ⟨before, last⟩ := List.append_inj products lengths
  obtain ⟨wires, tuples⟩ := trace_agree K T mode jobs hp hq inputs before
  have zs : vector (outputsOf jobs).length (v T) = vector (outputsOf jobs).length (v' T) :=
    (List.cons.inj last).1
  simp only [List.map_append, List.map_cons, List.map_nil, tuples, tupleView,
    outputShares_congr K jobs T wires, zs]

omit [Fintype E] [DecidableEq E] in
/-- The products that a corrupt operator fills and the other products give all
products. -/
theorem products_of_parts (T : C.Term) :
    ∀ (l l' : List (Tuple C)), l.map (filledView K D T) = l'.map (filledView K D T) →
      l.map (unfilledView K D T) = l'.map (unfilledView K D T) →
      l.map (productView T) = l'.map (productView T)
  | [], [], _, _ => rfl
  | [], _ :: _, filled, _ => by simp at filled
  | _ :: _, [], filled, _ => by simp at filled
  | τ :: l, σ :: l', filled, unfilled => by
    simp only [List.map_cons, List.cons.injEq] at filled unfilled ⊢
    refine ⟨?_, products_of_parts T l l' filled.2 unfilled.2⟩
    obtain ⟨count, first⟩ := vector_eq filled.1
    obtain ⟨-, second⟩ := vector_eq unfilled.1
    unfold productView
    rw [← count]
    apply vector_congr
    intro g hg
    have split : ∀ ρ : Tuple C, ρ.z T g =
        (if ∃ j ∈ D.1, filler K ρ.mode T g = some j then ρ.z T g else 0) +
          (if ∃ j ∈ D.1, filler K ρ.mode T g = some j then 0 else ρ.z T g) := by
      intro ρ
      split_ifs <;> simp
    rw [split τ, split σ, first g hg, second g hg]

end Algebra

section Walk

variable (circuits : Circuits) (settings : Settings)
variable {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}

variable (D) in
/-- At each supported live checkpoint, two honest holders of a term `T` with
checkpoint rows have equal term `T` inputs, and equal term `T` products at each
position that no corrupt operator fills. -/
def Transcript (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))
    (W : TreeCheckTailWalk A) : Prop :=
  ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
      support (W.cut prims K circuits settings D Z).pre →
    (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
      (.inl (c, o)) →
    ∀ (T : C.Term) (i k : C.Party) di dk, i ∈ C.holders T → k ∈ C.holders T → i ∉ D.1 → k ∉ D.1 →
      o.1.2 i = some di → o.1.2 k = some dk →
      wiresAt T di.1 = wiresAt T dk.1 ∧
        di.2.1.2.map (unfilledView K D T) = dk.2.1.2.map (unfilledView K D T)

/-- `Consistent` of a walk with standard tuples follows from its `Transcript`. -/
theorem consistent_of_transcript {top : TopTree} {tree : Tree} {x : C.Party → Keys C} {z : Aux}
    {Z : Distinguisher C A.State TreeOutput} {j : Fin (treeBatches settings tree)}
    {W : TreeCheckTailWalk A}
    (standard : W.StandardTuples circuits D)
    (self : ∀ c i, ((W.boundary c).batch.ctx i).self = i)
    (parameter : ∀ c i, ((W.boundary c).batch.ctx i).keys.parameter = (W.boundary c).batch.parameter)
    (transcript : Transcript prims K circuits settings D top tree x z Z j W) :
    W.Consistent prims K circuits settings D top tree x z Z j := by
  intro c o hs live hc hm
  refine ⟨hc, hm, fun T filled i hiT k hkT hi hk => ?_⟩
  obtain ⟨r, hr, hbad, _⟩ := id live
  obtain ⟨_, _, _, _, i₀, value, records, _, _, _, _, _, _, hout, _⟩ := hbad.2
  have pre := TreeCheckTailWalk.mem_support_cut_pre hs
  have rows := (W.boundary c).counts prims K circuits settings D Z (self c) (parameter c)
    o pre r hr ⟨i₀, (value, records), hout⟩
  obtain ⟨di, hdi, -⟩ := rows i hi
  obtain ⟨dk, hdk, -⟩ := rows k hk
  obtain ⟨inputs, unfilled⟩ := transcript c o hs live T i k di dk hiT hkT hi hk hdi hdk
  have filledRows := filled i hiT k hkT hi hk
  obtain ⟨-, tuples⟩ := standard c o
  simp only [tuples i hi, tuples k hk, hdi, hdk, Option.map_some, Option.getD_some]
    at filledRows ⊢
  have products := products_of_parts K D T _ _ filledRows unfilled
  obtain ⟨pi, hti, hei⟩ := treeCheck_batchPrefix_trace K circuits settings _ _ _ di
    ((W.boundary c).prefix_support prims K circuits settings D o pre i hi di hdi)
  obtain ⟨pk, htk, hek⟩ := treeCheck_batchPrefix_trace K circuits settings _ _ _ dk
    ((W.boundary c).prefix_support prims K circuits settings D o pre k hk dk hdk)
  rw [parameter c i] at hti hei
  rw [parameter c k] at htk hek
  rw [hei, hek] at products
  change di.2.1.2.map (tupleView T) = dk.2.1.2.map (tupleView T)
  rw [hei, hek]
  exact saved_agree K T settings.mode _ _ _ hti htk inputs products

/-- The `Transcript` clause, for the fixed family. -/
def WalkTranscript : Prop :=
  AtWalk prims K circuits settings fun top tree D _ x z Z _ _ j _ W =>
    Transcript prims K circuits settings D top tree x z Z j W

set_option maxRecDepth 2000 in
/-- `WalkConsistent` for the fixed family follows from `WalkTranscript` of the
same family. -/
theorem walkConsistent_of_transcript (transcript : WalkTranscript prims K circuits settings) :
    WalkConsistent prims K circuits settings := by
  intro hb top tree D A x z Z q dealt bounded small j p hp
  obtain ⟨-, standard, self⟩ :=
    walkSplit prims K circuits settings hb top tree D A x z Z q dealt bounded small j p hp
  obtain ⟨⟨-, parameter⟩, -, -⟩ :=
    walkSplit prims K circuits settings hb top tree D A x z Z q dealt bounded small j p hp
  have rows := transcript hb top tree D A x z Z q dealt bounded small j p hp
  with_reducible exact consistent_of_transcript prims K circuits settings standard self parameter rows

end Walk

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkConsistent.trace_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trace_agree

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkConsistent.saved_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms saved_agree

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkConsistent.products_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms products_of_parts

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkConsistent.consistent_of_transcript' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms consistent_of_transcript

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkConsistent.walkConsistent_of_transcript' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkConsistent_of_transcript

end TreeCheckWalkConsistent
end ThresholdLeanXmssSecurity
