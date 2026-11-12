import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkSource

/-!
# Saved tuples of an all-honest batch

A shared-mask trace records the actual peer or collector resharing formulas at
each multiplication layer and at the final rerandomization. Arbitrary common
term streams and symmetric pair streams suffice: no independence or freshness
assumption is needed for the resulting tuple products.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeCheckAllHonestProof
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

/-- The actual outputs of a reshare with honest deliveries and common stream values. -/
def maskOutputs (K : Constants C E) (mode : ReshareMode)
    (rr : C.Term → ℕ → Bit) (zz : C.Pair → ℕ → Bit) (v : C.Party → ℕ → Bit)
    (count : ℕ) : C.Party → Shares C Bit := match mode with
  | .peer => fun i => reshareZ K (localContext i) bitCodec (honestR rr i) (honestZ zz i) (v i) count
      (fun k => reshareOut K (localContext k) bitCodec (honestR rr k) (honestZ zz k) (v k) count i)
  | .collector => fun i => colZ K i (honestR rr i) (honestZ zz i) (v i) count
      (fun k => colOut1 K k (honestR rr k) (honestZ zz k) (v k) count i)
      (fun k => colOut2 K k (honestR rr k) (honestZ zz k) (v k) count
        (fun k' => colOut1 K k' (honestR rr k') (honestZ zz k') (v k') count k) i)

/-- Both communication patterns produce the same held views of a sharing of the input sum. -/
theorem maskOutputs_common (K : Constants C E) (mode : ReshareMode)
    (rr : C.Term → ℕ → Bit) (zz : C.Pair → ℕ → Bit) (v : C.Party → ℕ → Bit) (count : ℕ) :
    ∃ z : Shares C Bit, (∀ g, ∑ T, z T g = ∑ i, v i g) ∧
      maskOutputs K mode rr zz v count =
        fun i T g => if i ∈ C.holders T ∧ g < count then z T g else 0 := by
  cases mode with
  | peer =>
    refine ⟨honestShare K localContext rr zz v,
      sum_honestShare K localContext rr zz v (fun _ => rfl), ?_⟩
    funext i T g
    exact reshareZ_honest K localContext rr zz v bitCodec bitCodec_roundTrip (fun _ => rfl) count i T g
  | collector =>
    refine ⟨colShare K rr zz v, sum_colShare K rr zz v, ?_⟩
    funext i T g
    exact colZ_honest K rr zz v count i T g

/-- Appending the multiplication output and its saved tuple. -/
def layerUpdate (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit) (l : ℕ)
    (p : C.Party → MainInput C × List (Tuple C)) (z : C.Party → Shares C Bit) :
    C.Party → MainInput C × List (Tuple C) := fun i =>
  (appendLayer jobs l (p i).1 (z i), (p i).2 ++
    [⟨layerX K jobs l (p i).1, layerY K jobs l (p i).1, z i, (gatesAt jobs l).length, mode⟩])

/-- A synchronized sequence of the actual honest resharing formulas. -/
inductive MaskLayerTrace (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit)
    (x : C.Party → MainInput C) : ℕ → (C.Party → MainInput C × List (Tuple C)) → Prop
  | zero : MaskLayerTrace K mode jobs x 0 (fun i => (x i, []))
  | step {l p} (previous : MaskLayerTrace K mode jobs x l p)
      (rr : C.Term → ℕ → Bit) (zz : C.Pair → ℕ → Bit) :
      MaskLayerTrace K mode jobs x (l + 1)
        (layerUpdate K mode jobs l p (maskOutputs K mode rr zz
          (fun i => mulRep K (localContext i) (layerX K jobs l (p i).1) (layerY K jobs l (p i).1))
          (gatesAt jobs l).length))

/-- Shared masks preserve common circuit wires and product tuples at every layer. -/
theorem MaskLayerTrace.invariant (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit)
    (x : C.Party → MainInput C) (inputs : MainInputs jobs noCoalition x)
    {l : ℕ} {p : C.Party → MainInput C × List (Tuple C)}
    (trace : MaskLayerTrace K mode jobs x l p) :
    ∃ W Ts, LayerInv jobs x l p W Ts := by
  induction trace with
  | zero => exact ⟨_, _, layerInv_zero jobs x inputs⟩
  | @step l p previous rr zz ih =>
    obtain ⟨W, Ts, inv⟩ := ih
    obtain ⟨z, sum, outputs⟩ := maskOutputs_common K mode rr zz
      (fun i => mulRep K (localContext i) (layerX K jobs l (p i).1) (layerY K jobs l (p i).1))
      (gatesAt jobs l).length
    rw [outputs]
    exact ⟨_, _, layerInv_step K jobs x mode l p W Ts inv z sum⟩

/-- The final saved views use a peer rerandomization of the actual output wires. -/
def SavedByMasks (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit)
    (x : C.Party → MainInput C) (views : C.Party → List (Tuple C)) : Prop :=
  ∃ (p : C.Party → MainInput C × List (Tuple C)) (rr : C.Term → ℕ → Bit)
      (zz : C.Pair → ℕ → Bit), MaskLayerTrace K mode jobs x (depth jobs) p ∧
    views = treeCheckSavedTuples K jobs p (maskOutputs K .peer rr zz
      (fun i => ownerSum K (localContext i) (outputShares K jobs (p i).1)) (outputsOf jobs).length)

/-- Common product tuples make the deterministic verifier accept. -/
theorem verify_of_agree (views : C.Party → List (Tuple C)) (Ts : List (Tuple C))
    (lengths : ∀ i, (views i).length = Ts.length)
    (agree : ∀ i m (hm : m < Ts.length),
      TupleAgrees i ((views i)[m]'(by rw [lengths]; exact hm)) Ts[m])
    (products : ∀ τ ∈ Ts, IsProduct τ) :
    (multVerifyLeak noCoalition (stagesHonest noCoalition views)).2.2 = true := by
  have present : stagesHonest noCoalition views = fun i => some (views i) := by
    funext i
    simp [stagesHonest]
  rw [present]
  have len : (firstInput fun i => some (views i)).length = Ts.length := by
    rw [firstInput_some_pos, lengths]
  have tuples : (List.range Ts.length).map (tupleAt fun i => some (views i)) = Ts := by
    apply List.ext_getElem (by simp)
    intro k hk hk'
    simpa using tupleAt_of_agree views Ts lengths agree k hk'
  change decide (_ ∧ _) = true
  rw [decide_eq_true_eq]
  dsimp only
  rw [len, tuples]
  constructor
  · intro k hk T i hi j hj _ _ g hg
    simp only [Option.bind_some, List.getElem?_eq_getElem (show k < (views i).length by rw [lengths]; exact hk),
      List.getElem?_eq_getElem (show k < (views j).length by rw [lengths]; exact hk), Option.map_some,
      Option.some.injEq, Prod.mk.injEq]
    obtain ⟨ix, iy, iz⟩ := (agree i k hk).1 T hi
    obtain ⟨jx, jy, jz⟩ := (agree j k hk).1 T hj
    exact ⟨congrFun (ix.trans jx.symm) g, congrFun (iy.trans jy.symm) g,
      congrFun (iz.trans jz.symm) g⟩
  · exact products

/-- Every tuple saved by common mask rounds is a correct tuple of the deterministic verifier. -/
theorem SavedByMasks.verified (K : Constants C E) (mode : ReshareMode) (jobs : List Circuit)
    (x : C.Party → MainInput C) (inputs : MainInputs jobs noCoalition x)
    (views : C.Party → List (Tuple C)) (saved : SavedByMasks K mode jobs x views) :
    (multVerifyLeak noCoalition (stagesHonest noCoalition views)).2.2 = true := by
  obtain ⟨p, rr, zz, trace, rfl⟩ := saved
  obtain ⟨W, Ts, inv⟩ := trace.invariant K mode jobs x inputs
  obtain ⟨z, sum, outputs⟩ := maskOutputs_common K .peer rr zz
    (fun i => ownerSum K (localContext i) (outputShares K jobs (p i).1)) (outputsOf jobs).length
  rw [outputs]
  let n := (outputsOf jobs).length
  let v : C.Party → Shares C Bit := fun i T g => if i ∈ C.holders T ∧ g < n then z T g else 0
  let w : Shares C Bit := fun T g => if g < n then z T g else 0
  let tail : Tuple C := ⟨outputShares K jobs W, one K, w, n, .peer⟩
  have held : ∀ i T, i ∈ C.holders T → outputShares K jobs (p i).1 T = outputShares K jobs W T :=
    fun i T hi => outputShares_congr K jobs _ _ T (inv.agree i T hi)
  have len : ∀ i, (treeCheckSavedTuples K jobs p v i).length = (Ts ++ [tail]).length := by
    intro i
    simp only [treeCheckSavedTuples, List.length_append, List.length_singleton, inv.length_tuples]
  apply verify_of_agree _ (Ts ++ [tail]) len
  · intro i
    exact tupleAgrees_append i _ _ _ _ (inv.length_tuples i) (inv.agree_tuples i)
      ⟨fun T hi => ⟨held i T hi, rfl, funext fun g => by simp [v, w, tail, hi]⟩, rfl, rfl⟩
  · intro τ hτ
    rcases List.mem_append.mp hτ with old | last
    · exact inv.product τ old
    · obtain rfl := List.mem_singleton.mp last
      intro g hg
      change shareValue w g = shareValue (outputShares K jobs W) g * shareValue (one K) g
      rw [shareValue_one, mul_one, ← sum_ownerSum K _ _ held, ← sum g]
      exact Finset.sum_congr rfl fun T _ => if_pos hg

end ThresholdLeanXmssSecurity.TreeCheckAllHonestProof

namespace ThresholdLeanXmssSecurity.TreeCheckAllHonestProof
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- Each context reads its held term key and the common key of each unordered pair. -/
def SharedPrss (ctx : C.Party → Context C) : Prop :=
  ∃ (terms : C.Term → HashOutput) (pairs : C.Pair → HashOutput),
    (∀ i, (ctx i).self = i) ∧
    (∀ i T, i ∈ C.holders T → (ctx i).prss.term T = terms T) ∧
    (∀ i j (h : i ≠ j), (ctx i).prss.pair j = pairs (C.pairOf i j h))

/-- The actual all-honest scheduler supplies one shared-mask trace for its own saved views. -/
def BatchMaskExtraction (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) : Prop :=
  ∀ (A : Adversary C E (Keys C) PEmpty PEmpty) (b : TreeCheckBatchBoundary A),
    (∀ i, (b.ctx i).keys.parameter = b.parameter) → SharedPrss b.ctx →
    ∀ o ∈ support (treeCheckBatchPre prims K circuits settings noCoalition A b),
    (∀ i, (o.1.2 i).isSome) →
    SavedByMasks K settings.mode (b.jobs.map (circuits b.parameter ·.kind))
      (fun i => (treeCheckPrefixData (o.1.2 i)).1)
      (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.2)

/-- The deterministic verification bit of an actual, coherently keyed all-honest prefix. -/
def AllHonestSavedTuples (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) : Prop :=
  ∀ (A : Adversary C E (Keys C) PEmpty PEmpty) (b : TreeCheckBatchBoundary A),
    (∀ i, (b.ctx i).keys.parameter = b.parameter) → SharedPrss b.ctx →
    ∀ o ∈ support (treeCheckBatchPre prims K circuits settings noCoalition A b),
    (∀ i, (o.1.2 i).isSome) →
    MainInputs (b.jobs.map (circuits b.parameter ·.kind)) noCoalition
      (fun i => (treeCheckPrefixData (o.1.2 i)).1) →
    (multVerifyLeak noCoalition (stagesHonest noCoalition
      (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.2))).2.2 = true

omit [Fintype E] [DecidableEq E] in
/-- Shared-mask extraction gives actual saved-tuple correctness without probabilistic estimates. -/
theorem allHonestSavedTuples_of_extraction (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (source : BatchMaskExtraction prims K circuits settings) :
    AllHonestSavedTuples prims K circuits settings := by
  intro A b parameters shared o run present inputs
  exact SavedByMasks.verified K settings.mode _ _ inputs _
    (source A b parameters shared o run present)

/-- An actual all-honest opening with a common seed view supplies its own valid batch inputs. -/
theorem opening_inputs (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (b : TreeCheckBatchBoundary A)
    (self : ∀ i, (b.ctx i).self = i)
    (o : (A.State × (C.Party → Option
      (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (run : o ∈ support (treeCheckBatchPre prims K circuits settings noCoalition A b))
    (present : ∀ i, (o.1.2 i).isSome)
    (opening : TreeCheckOpeningAt prims K circuits noCoalition A b o) :
    MainInputs (b.jobs.map (circuits b.parameter ·.kind)) noCoalition
      (fun i => (treeCheckPrefixData (o.1.2 i)).1) := by
  have values : (fun i => (treeCheckPrefixData (o.1.2 i)).1) =
      batchInputs opening.hash opening.seeds b.jobs := by
    funext i
    obtain ⟨data, hd⟩ := Option.isSome_iff_exists.mp (present i)
    have h := treeCheck_batchPrefix_inputs prims K circuits settings noCoalition A b self
      opening.seeds opening.seed o run opening.hash opening.rows i (by simp) data hd
    simpa only [hd, treeCheckPrefixData, Option.getD_some] using h
  rw [values]
  exact treeCheck_batchInputs_main noCoalition opening.hash opening.seeds circuits b.parameter b.jobs

/-- A live wrong-opening certificate contradicts all-honest saved-tuple correctness. -/
theorem no_wrong_opening_of_extraction (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (source : BatchMaskExtraction prims K circuits settings)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (b : TreeCheckBatchBoundary A)
    (parameters : ∀ i, (b.ctx i).keys.parameter = b.parameter) (shared : SharedPrss b.ctx)
    (o : (A.State × (C.Party → Option
      (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (run : o ∈ support (treeCheckBatchPre prims K circuits settings noCoalition A b))
    (present : ∀ i, (o.1.2 i).isSome)
    (opening : TreeCheckOpeningAt prims K circuits noCoalition A b o) : False := by
  have self := shared.choose_spec.choose_spec.1
  have inputs := opening_inputs prims K circuits settings A b self o run present opening
  have accepted := allHonestSavedTuples_of_extraction prims K circuits settings source
    A b parameters shared o run present inputs
  exact treeCheck_open_dealer_reject prims K circuits settings noCoalition A b parameters self
    opening.seeds opening.seed o run (fun i _ => present i) opening.hash opening.rows
    opening.live opening.ds opening.sent opening.party opening.before opening.after opening.output
    opening.hashes opening.run opening.good opening.wrong accepted

end ThresholdLeanXmssSecurity.TreeCheckAllHonestProof

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.maskOutputs_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.maskOutputs_common

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.MaskLayerTrace.invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.MaskLayerTrace.invariant

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.verify_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.verify_of_agree

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.SavedByMasks.verified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.SavedByMasks.verified

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.allHonestSavedTuples_of_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.allHonestSavedTuples_of_extraction

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.opening_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.opening_inputs

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.no_wrong_opening_of_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeCheckAllHonestProof.no_wrong_opening_of_extraction
