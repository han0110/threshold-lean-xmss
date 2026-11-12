import ThresholdLeanXmssSecurity.Proof.TreeTwinBoundaries

/-!
# One fixed family of ceremony twin boundaries

The padding and twelve round kinds use the same concrete batch callers.
The three code-only linked kinds are empty; the source programs occur in
these data-bearing kinds. A caller includes its actual remaining chunks,
the public continuation between bottom-tree runs, and both output gadgets.

The digest prefix must couple all live holders before installing its swap.
At the distinguished hidden term they have one history on each side. After
the swap, cached digest reads use the simulated history in the twin cache;
freshness of the first holder alone says nothing about these later reads.
The digest certificate below records both the real log and those twin reads.

The source-only final-opening kind fixes both program shapes but imposes no
equality between their masked claims.
`TreeTwinKindNext` requires reachability of the real configuration `a`;
neither reachability nor `treeTwinReq` fixes the simulated claim and masks.
A recorder at this round distinguishes unequal opening views while aborting,
with unchanged caches and log. This obstruction does not assert a reachable
ceremony instance or negate the existential `TreeTwinLinkedGoal`.

In `Scheme.check`, the final mask `w` is sampled before ExtendMult, whose
result `q` is fixed before the digest exchange and the final public challenge.
The entry padding fixes the challenge lookup table for every possible Coin
result, not the result selected by the later adaptive Coin exchange. A joint
prefix coupling may therefore use a challenge-dependent mask translation;
it need not keep the same pair of masks for different challenges.
For fixed masks, equality of the first opening coordinate at two distinct
challenges forces equality of the corresponding claim. A relation requiring
equal openings at the final round must therefore account for the joint law
of the earlier masks and the challenge; adding an equality conjunct there
alone does not provide that law.

GS20, Protocol 15 and Lemma 11 (Hybrid 2, pp. 24–25), instead reconstruct the
final sharings from uniform masked secrets, corrupt shares and the residual.
`finalMaskNetwork_sameRun` in `Check.lean` realizes its challenge-dependent triangular
bijection when the public transcript and challenge precede independent hidden
mask and product tables. For this ceremony a deferred-table factorization
must cover ExtendMult, the whole-holder digest swap and the final Coin,
retaining the actual cache and log. It also needs the Shamir, local-shift and
equal-residual equations of that theorem. Pointwise closure of the kinds
below does not supply that factorization. K8 and K9 omit the equal tags and
labels needed at K10; K8–K11 omit hidden-shift support and future-cache
frames. Those frames alone do not repair the final-mask obstruction.

The deferred segment starts before `randElements 2` and ends after the
final Coin. Its outer prefix contains the corrupt-visible messages,
adversary state, live set, known shares, malicious offsets, receivers and
selected challenge. Its decoder reconstructs the actual log, both caches
and suspended honest programs from that prefix and the two hidden tables
used by `finalMaskNetwork_sameRun`; the decoded log and caches need not be
independent of those tables. `executePhase_finalMasks` gives the initial
table separation for the
functionality hybrid; transferring it to this actual PRSS segment requires
its visible field-message and whole-holder digest couplings. The table law
must hold jointly with all adaptive replies and the selected challenge.
To recover the original per-round linked goal, that law must also produce
conditional kernels at each intermediate boundary; a terminal distribution
equality alone does not establish `TreeTwinKindNext`.

`Scheme.record` appends two `elementBits`-bit field encodings at every slice,
halving and final ExtendMult. The history cap includes these records:
`tupleCount + 2 * elementBits * (halvings tupleCount + 1)` for each batch.
`historyLimit_covers` bounds the resulting record fold, including partial
prefixes. A compiler must identify that fold in its actual saved histories;
the pre-check history bound alone does not identify the later records.
-/

set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeTwinLinked2

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The largest end label of a ceremony of `tree`, over the encodings of the second run. -/
def labelCap (tree : Tree) (parameter : PublicParameter) : ℕ :=
  Finset.univ.sup fun enc : Encoding =>
    lockstepStart circuits parameter (lockstepChunks settings enc tree) (treeBatches settings tree)

/-- The padded challenge addresses. The corrupt entries of the saved data read `(0, 0)` and `(0, 1)`. -/
def tagLabels (tree : Tree) (parameter : PublicParameter) : List (ℕ × ℕ) :=
  (0, 0) :: (0, 1) :: (List.range (treeBatches settings tree)).flatMap fun k =>
    (List.range (labelCap circuits settings tree parameter + 2)).map fun label => (k, label)

/-- Bit tuple histories followed by every two-product field reshare of
`check`, including final randomization. -/
def historyLimit : ℕ :=
  maxBatch circuits settings fun cs =>
    tupleCount cs + (halvings (tupleCount cs) + 1) * (2 * elementBits)

/-- Every actual field reshare records at most `count` field encodings. -/
theorem recordPeer_element_length (i : C.Party) (h : C.Term → List Bit)
    (z : Shares C E) (count : ℕ) (T : C.Term) :
    (recordPeer K (elementCodec K) i h z count T).length ≤ (h T).length + count * elementBits := by
  have length (gs : List ℕ) :
      (gs.flatMap (fun g => List.ofFn (K.encode (z T g)))).length = gs.length * elementBits := by
    induction gs with
    | nil => simp
    | cons g gs ih => simp [ih, Nat.add_mul, Nat.add_comm]
  unfold recordPeer
  split_ifs
  · simp only [List.length_append, elementCodec, Function.comp_def]
    rw [length]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right elementBits ((List.length_filter_le _ _).trans_eq List.length_range)) _
  · omega

/-- A list of two-product field reshares has the source history budget. -/
theorem fieldHistories_length (i : C.Party) (h : C.Term → List Bit)
    (zs : List (Shares C E)) (T : C.Term) :
    ((zs.foldl (fun hist z => recordPeer K (elementCodec K) i hist z 2) h) T).length ≤
      (h T).length + zs.length * (2 * elementBits) := by
  induction zs generalizing h with
  | nil => simp
  | cons z zs ih =>
    rw [List.foldl_cons]
    have step := recordPeer_element_length K i h z 2 T
    have rest := ih (recordPeer K (elementCodec K) i h z 2)
    simp only [List.length_cons, Nat.add_mul, one_mul]
    omega

/-- The source has `sliceBits` slice reshares, the remaining halvings, and
one final randomization reshare. -/
theorem finalField_count (count : ℕ) :
    sliceBits + (halvings count - sliceBits) + 1 = halvings count + 1 := by
  simp [halvings]

/-- The enlarged padding covers every history with the initial bit bound
and the exact field-reshare count of the batch, including partial prefixes. -/
theorem historyLimit_covers (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (enc : Encoding) (jobs : List Job)
    (jobs_mem : jobs ∈ chunks settings.batchSize topJobs ∨
      jobs ∈ chunks settings.batchSize (bottomJobs b) ∨
      jobs ∈ chunks settings.batchSize (signJobs b enc))
    (i : C.Party) (h : C.Term → List Bit) (zs : List (Shares C E)) (T : C.Term)
    (initial : (h T).length ≤ tupleCount (runCircuits circuits parameter jobs))
    (count : zs.length ≤ halvings (tupleCount (runCircuits circuits parameter jobs)) + 1) :
    ((zs.foldl (fun hist z => recordPeer K (elementCodec K) i hist z 2) h) T).length ≤
      historyLimit circuits settings := by
  exact (fieldHistories_length K i h zs T).trans
    ((Nat.add_le_add initial (Nat.mul_le_mul_right _ count)).trans
      (measure_le_maxBatch circuits settings
        (fun cs => tupleCount cs + (halvings (tupleCount cs) + 1) * (2 * elementBits))
        parameter b enc jobs jobs_mem))

/-- The padding of the route. -/
def padding (tree : Tree) (parameter : PublicParameter) (seeds : C.Term → HashOutput) :
    OracleComp (LocalSpec C) Unit :=
  treeTwinEntryPadding K circuits settings seeds (tagLabels circuits settings tree parameter)
    (historyLimit circuits settings)

/-- The honest operators run batch `k` of some encoding, at `offset` labels after its start. -/
def Position (tree : Tree) (D : C.Coalition) (parameter : PublicParameter) (circs : List Circuit)
    (offset : ℕ) (st : C.Party → RunState C) : Prop :=
  ∃ (enc : Encoding) (k : ℕ), k < treeBatches settings tree ∧
    circs = runCircuits circuits parameter ((lockstepChunks settings enc tree).getD k []) ∧
    offset ≤ batchLabels circuits parameter ((lockstepChunks settings enc tree).getD k []) ∧
    ∀ i, i ∉ D.1 → (st i).tag = k ∧
      (st i).label = lockstepStart circuits parameter (lockstepChunks settings enc tree) k + offset

set_option maxRecDepth 8000 in
/-- A position gives a padded address. -/
theorem position_mem (tree : Tree) (D : C.Coalition) (parameter : PublicParameter)
    (circs : List Circuit) (offset : ℕ) (st : C.Party → RunState C)
    (h : Position circuits settings tree D parameter circs offset st) (extra : ℕ) (he : extra ≤ 1)
    (i : C.Party) (hi : i ∉ D.1) :
    ((st i).tag, (st i).label + extra) ∈ tagLabels circuits settings tree parameter := by
  obtain ⟨enc, k, hk, -, bound, at_⟩ := h
  have hlen : (lockstepChunks settings enc tree).length = treeBatches settings tree :=
    lockstepChunks_length settings enc tree
  have step : lockstepStart circuits parameter (lockstepChunks settings enc tree) k + offset ≤
      lockstepStart circuits parameter (lockstepChunks settings enc tree) (k + 1) := by
    rw [lockstepStart_succ circuits parameter _ k (by omega)]
    omega
  have mono : lockstepStart circuits parameter (lockstepChunks settings enc tree) (k + 1) ≤
      lockstepStart circuits parameter (lockstepChunks settings enc tree) (treeBatches settings tree) := by
    unfold lockstepStart
    have hsub : ((lockstepChunks settings enc tree).take (k + 1)).Sublist
        ((lockstepChunks settings enc tree).take (treeBatches settings tree)) :=
      (List.take_sublist_take_left (by omega : k + 1 ≤ treeBatches settings tree))
    exact List.Sublist.sum_le_sum (hsub.map _) (fun _ _ => Nat.zero_le _)
  have cap : lockstepStart circuits parameter (lockstepChunks settings enc tree) (treeBatches settings tree) ≤
      labelCap circuits settings tree parameter :=
    Finset.le_sup (f := fun enc : Encoding =>
      lockstepStart circuits parameter (lockstepChunks settings enc tree) (treeBatches settings tree))
      (Finset.mem_univ enc)
  have hl := (at_ i hi).2
  have ht := (at_ i hi).1
  unfold tagLabels
  refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨k, List.mem_range.2 hk,
    List.mem_map.2 ⟨(st i).label + extra, List.mem_range.2 (by omega), by rw [ht]⟩⟩))

/-- The three source-level callers of a batched ceremony run. -/
inductive BatchPhase where
  | top
  | bottom (b : Fin (2 ^ layerHeight))
  | sign (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit))
      (root : Digest) (randomness : Randomness) (encoding : Encoding)

def BatchPhase.tree : BatchPhase → Tree
  | .top => .top
  | .bottom b | .sign b _ _ _ _ => .bottom b

def BatchPhase.jobs : BatchPhase → List Job
  | .top => topJobs
  | .bottom b => bottomJobs b
  | .sign b _ _ _ enc => signJobs b enc

def BatchPhase.start (phase : BatchPhase) : ℕ :=
  match phase with
  | .sign b _ _ _ _ => (chunks settings.batchSize (bottomJobs b)).length
  | _ => 0

/-- One position in the actual chunks of one public run. -/
structure BatchSite (tree : Tree) where
  phase : BatchPhase
  tree_eq : phase.tree = tree
  index : ℕ
  bound : index < (chunks settings.batchSize phase.jobs).length

def BatchSite.jobs {tree : Tree} (site : BatchSite settings tree) : List Job :=
  (chunks settings.batchSize site.phase.jobs).getD site.index []

def BatchSite.tag {tree : Tree} (site : BatchSite settings tree) : ℕ :=
  site.phase.start settings + site.index

/-- The batch body of `ceremonyWith` or `treeSimIdealCont`. -/
def batchRun (D : C.Coalition) (parameter : PublicParameter) (openings : List (List (List Bit)))
    (ideal : Bool) (ctx : Context C) (jobs : List Job) :
    StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit))) := do
  let (label, k) ← get
  let inputs ← StateT.lift (jobs.mapM (inputShares ctx))
  let gadgets := if ideal then treeSimGadgets K circuits settings D parameter ctx.keys.seed openings ctx k jobs
    else realRunGadgets K ctx settings.mode
  let (outputs, state) ← StateT.lift
    ((runJobs K gadgets (runCircuits circuits parameter jobs) inputs).run ⟨fun _ => [], label, k⟩)
  set (state.label, k + 1)
  pure (some outputs)

/-- The public suffix of one run; a bottom first run chooses and executes
its signing run, with the counters that the first run left. -/
def phaseFinish (D : C.Coalition) (parameter : PublicParameter) (openings : List (List (List Bit)))
    (top : TopTree) (ideal : Bool) (ctx : Context C) (phase : BatchPhase)
    (outputs : List (List Bit)) (counters : ℕ × ℕ) : PartyM C E RealSpec TreeOutput := do
  match phase with
  | .top => return (← treeLockstepTopFinish parameter outputs []).1
  | .bottom b =>
    let chosen ← oracleStep (tweakable (treeLockstepPublicChoiceCode parameter b outputs))
    let some (root, randomness, enc) := chosen | failure
    let values ← (batched settings.batchSize
      (batchRun K circuits settings D parameter openings ideal ctx) (signJobs b enc)).run' counters
    return (← treeLockstepBottomFinish parameter top b outputs root randomness values []).1
  | .sign b first root randomness _ =>
    return (← treeLockstepBottomFinish parameter top b first root randomness (some outputs) []).1

/-- The exact continuation after the current `runJobs`, including the
remaining `mapM` and the option fold used by `batched`. -/
def batchCaller (tree : Tree) (D : C.Coalition) (parameter : PublicParameter)
    (openings : List (List (List Bit))) (top : TopTree) (ideal : Bool) (ctx : Context C)
    (site : BatchSite settings tree) (prior : List (Option (List (List Bit))))
    (out : List (List Bit) × RunState C) : PartyM C E RealSpec TreeOutput := do
  let rest ← (((chunks settings.batchSize site.phase.jobs).drop (site.index + 1)).mapM
    (batchRun K circuits settings D parameter openings ideal ctx)).run (out.2.label, site.tag settings + 1)
  let some outputs := (prior ++ some out.1 :: rest.1).foldlM (fun acc batch => batch.map (acc ++ ·)) []
    | failure
  phaseFinish K circuits settings D parameter openings top ideal ctx site.phase outputs rest.2

/-- A code is the current real/simulated batch, with its own fixed public
caller. In particular this does not impose positive output width. -/
def BatchLink (top : TopTree) (tree : Tree) (D : C.Coalition) (parameter : PublicParameter)
    (openings : List (List (List Bit))) (code : TreeTwinCode C E) (st : C.Party → RunState C) : Prop :=
  ∃ (site : BatchSite settings tree) (prior : C.Party → List (Option (List (List Bit)))),
    code.2.2.2.2.1 = runCircuits circuits parameter (site.jobs settings) ∧
    (∀ i, i ∉ D.1 → (st i).tag = site.tag settings ∧ (prior i).length = site.index) ∧
    code.2.2.1 = (fun i => realRunGadgets K (code.1 i) settings.mode) ∧
    code.2.2.2.1 = (fun i => treeSimGadgets K circuits settings D parameter
      (code.2.1 i).keys.seed openings (code.2.1 i) (site.tag settings) (site.jobs settings)) ∧
    (∀ i, i ∉ D.1 → code.2.2.2.2.2.1 i =
      batchCaller K circuits settings tree D parameter openings top false (code.1 i) site (prior i)) ∧
    (∀ i, i ∉ D.1 → code.2.2.2.2.2.2 i =
      batchCaller K circuits settings tree D parameter openings top true (code.2.1 i) site (prior i))

/-- Live holders of the distinguished hidden term have one history. -/
def CommonHistory (D : C.Coalition) (live : C.Party → Bool) (st : C.Party → RunState C) : Prop :=
  ∀ T, lackedTerm D.1 = some T → ∀ i j, i ∉ D.1 → j ∉ D.1 →
    live i = true → live j = true → i ∈ C.holders T → j ∈ C.holders T →
    (st i).history T = (st j).history T

section Stages

variable (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (openings : List (List (List Bit)))

/-- The original Rerand caller, with actual batch code and no artificial
positive-output restriction. A nonempty check is identified by tuple count. -/
structure Caller where
  peer : TreeSimPeerData K D
  rest : TreeStagesRerandTail K D peer
  batch : BatchLink K circuits settings top tree D parameter openings (treeTwinRerandCode K D rest) peer.st₁
  data : TreeTwinRunData K D peer.ctx₁ peer.ctx₂ rest.p₁ rest.p₂
  link : TreeTwinRerandLink K D rest
  sent : C.Party → Mail C E
  nonzero₁ : ∀ i, i ∉ D.1 → ((rest.p₁ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0
  nonzero₂ : ∀ i, i ∉ D.1 → ((rest.p₂ i).2.map (·.count)).sum + (outputsOf rest.circs).length ≠ 0

namespace Caller

def checkData (c : Caller K circuits settings top tree D parameter openings) : TreeTwinCheckCoinData K D :=
  c.rest.checkCoinData K D c.peer c.nonzero₁ c.nonzero₂ c.sent c.data

def count₁ (c : Caller K circuits settings top tree D parameter openings) (i : C.Party) : ℕ :=
  (((c.checkData K circuits settings top tree D parameter openings).tuples₁ i).map (·.count)).sum

/-- The check's saved caller and count are shared by the two source forms. -/
def Slice (c : Caller K circuits settings top tree D parameter openings)
    (q : TreeStagesExtendMultChallenge K D) (remaining : List ℕ) : Prop :=
  ∃ (τ₁ τ₂ : C.Party → List E) (j : ℕ) (v₁ v₂ : C.Party → Shares C E × Shares C E × E),
    (∀ i, i ∉ D.1 → q.body₁ i = treeStagesSliceBody K (q.ctx₁ i) (τ₁ i)
      (c.count₁ K circuits settings top tree D parameter openings i) j remaining (v₁ i)
      ((c.checkData K circuits settings top tree D parameter openings).finish₁ i)) ∧
    (∀ i, i ∉ D.1 → q.body₂ i = treeStagesSliceBody K (q.ctx₂ i) (τ₂ i)
      (c.count₁ K circuits settings top tree D parameter openings i) j remaining (v₂ i)
      ((c.checkData K circuits settings top tree D parameter openings).finish₂ i))

def Halving (c : Caller K circuits settings top tree D parameter openings)
    (q : TreeStagesExtendMultChallenge K D) (remaining : List ℕ) : Prop :=
  ∃ (j : ℕ) (v₁ v₂ : C.Party → (ℕ → E) × (ℕ → E) × E),
    (∀ i, i ∉ D.1 → q.body₁ i = treeStagesHalvingBody K (q.ctx₁ i)
      (sliceWidth (c.count₁ K circuits settings top tree D parameter openings i)) j remaining (v₁ i)
      ((c.checkData K circuits settings top tree D parameter openings).finish₁ i)) ∧
    (∀ i, i ∉ D.1 → q.body₂ i = treeStagesHalvingBody K (q.ctx₂ i)
      (sliceWidth (c.count₁ K circuits settings top tree D parameter openings i)) j remaining (v₂ i)
      ((c.checkData K circuits settings top tree D parameter openings).finish₂ i))

end Caller

/-- Saved check source, its batch position, and the count of that same caller. -/
def SavedPlus (q : TreeStagesExtendMultChallenge K D) : Prop :=
  (∀ i, i ∉ D.1 → (q.st₁ i).tag = (q.st₂ i).tag) ∧
  ∃ (c : Caller K circuits settings top tree D parameter openings) (remaining : List ℕ) (offset : ℕ),
    q.ctx₁ = c.peer.ctx₁ ∧ q.ctx₂ = c.peer.ctx₂ ∧
    (c.Slice K circuits settings top tree D parameter openings q remaining ∨
      c.Halving K circuits settings top tree D parameter openings q remaining) ∧
    Position circuits settings tree D parameter c.rest.circs offset q.st₁ ∧
    (∀ i, i ∉ D.1 → c.count₁ K circuits settings top tree D parameter openings i = tupleCount c.rest.circs) ∧
    CommonHistory D (fun _ => true) q.st₁ ∧ CommonHistory D (fun _ => true) q.st₂

/-- A source check with another slice or halving field exchange. -/
def Advancing (q : TreeStagesExtendMultChallenge K D) : Prop :=
  ∃ c : Caller K circuits settings top tree D parameter openings,
    q.ctx₁ = c.peer.ctx₁ ∧ q.ctx₂ = c.peer.ctx₂ ∧
    ((∃ next remaining, c.Slice K circuits settings top tree D parameter openings q (next :: remaining) ∨
      c.Halving K circuits settings top tree D parameter openings q (next :: remaining)) ∨
    (c.Slice K circuits settings top tree D parameter openings q [] ∧ ∃ next remaining,
      ∀ i, i ∉ D.1 → List.range
        (halvings (c.count₁ K circuits settings top tree D parameter openings i) - sliceBits) = next :: remaining))

/-- A source check whose next segment is exactly randomization. -/
def Finishing (q : TreeStagesExtendMultChallenge K D) : Prop :=
  ∃ c : Caller K circuits settings top tree D parameter openings,
    q.ctx₁ = c.peer.ctx₁ ∧ q.ctx₂ = c.peer.ctx₂ ∧
    (c.Halving K circuits settings top tree D parameter openings q [] ∨
      (c.Slice K circuits settings top tree D parameter openings q [] ∧
        ∀ i, i ∉ D.1 → halvings (c.count₁ K circuits settings top tree D parameter openings i) ≤ sliceBits))

/-- The count link gives a single halving schedule, as in
`TreeTwinBoundaries.Caller.check_cases`, without output-width positivity. -/
theorem SavedPlus.check_cases (q : TreeStagesExtendMultChallenge K D)
    (h : SavedPlus K circuits settings top tree D parameter openings q) :
    Advancing K circuits settings top tree D parameter openings q ∨
      Finishing K circuits settings top tree D parameter openings q := by
  obtain ⟨_, c, remaining, _, ctx₁, ctx₂, shape, _, counts, _⟩ := h
  cases remaining with
  | cons next remaining => exact Or.inl ⟨c, ctx₁, ctx₂, Or.inl ⟨next, remaining, shape⟩⟩
  | nil =>
    rcases shape with slice | halving
    · cases schedule : List.range (halvings (tupleCount c.rest.circs) - sliceBits) with
      | nil =>
        have zero : halvings (tupleCount c.rest.circs) - sliceBits = 0 := by
          simpa using congrArg List.length schedule
        refine Or.inr ⟨c, ctx₁, ctx₂, Or.inr ⟨slice, ?_⟩⟩
        intro i hi
        rw [counts i hi]
        omega
      | cons next remaining =>
        exact Or.inl ⟨c, ctx₁, ctx₂, Or.inr ⟨slice, next, remaining,
          fun i hi => by rw [counts i hi, schedule]⟩⟩
    · exact Or.inr ⟨c, ctx₁, ctx₂, Or.inl halving⟩

/-- The recipe-preservation condition used to formulate `CheckLoopNext`: it
retains the position, shared history and actual caller. -/
def SavedPlusClosure : Prop :=
  ∀ q, SavedPlus K circuits settings top tree D parameter openings q →
    Advancing K circuits settings top tree D parameter openings q →
    ∃ recipe : TreeTwinHonestReductionRecipe K D q, ∀ rnd δ sent values,
      SavedPlus K circuits settings top tree D parameter openings
        ((recipe.reduction K D rnd δ sent).step K D values)

/-- K1: both collector exchanges of the actual remaining AND schedule. -/
def CollectorStage (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (d : TreeSimCollectorData K D) (s : TreeStagesCollectorSchedule K D d),
    BatchLink K circuits settings top tree D parameter openings (treeTwinScheduleCode K D s) d.st₁ ∧
    Position circuits settings tree D parameter s.circs s.layer d.st₁ ∧
    s.layer :: s.rest = (List.range (depth s.circs)).drop s.layer ∧
    (∀ i, i ∉ D.1 → ((s.p₁ i).2.map (·.count)).sum +
      ((s.layer :: s.rest).map (fun l => (gatesAt s.circs l).length)).sum +
      (outputsOf s.circs).length = tupleCount s.circs) ∧
    δ = d.δ ∧ TreeSimFutureEmpty (s.ρ + 1) a.2.1.2 ∧
    TreeTwinRunData K D s.ctx₁ s.ctx₂ s.p₁ s.p₂ ∧ TreeTwinScheduleLink K D s ∧
    ((∃ live, CommonHistory D live d.st₁ ∧ CommonHistory D live d.st₂ ∧
      a.1.2 = treeSimCollectorPartial K D live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
      b.1.2 = treeSimCollectorPartial K D live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) ∨
    ∃ sent, CommonHistory D (fun _ => true) d.st₁ ∧ CommonHistory D (fun _ => true) d.st₂ ∧
      a.1.2 = treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent ∧
      b.1.2 = treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent)

/-- K2: a peer AND layer, retaining its products and remaining layers. -/
def PeerStage (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (d : TreeSimPeerData K D) (layer : ℕ) (remaining : List ℕ)
    (s : TreeStagesPeerSchedule K D d (layer :: remaining)) (live : C.Party → Bool),
    BatchLink K circuits settings top tree D parameter openings
      (d.ctx₁, d.ctx₂, s.gadgets₁, s.gadgets₂, s.circs, s.finish₁, s.finish₂) d.st₁ ∧
    Position circuits settings tree D parameter s.circs layer d.st₁ ∧
    layer :: remaining = (List.range (depth s.circs)).drop layer ∧
    (∀ i, i ∉ D.1 → ((s.p₁ i).2.map (·.count)).sum +
      ((layer :: remaining).map (fun l => (gatesAt s.circs l).length)).sum +
      (outputsOf s.circs).length = tupleCount s.circs) ∧
    (∀ i, i ∉ D.1 → d.v₁ i = mulRep K (d.ctx₁ i)
      (layerX K s.circs layer (s.p₁ i).1) (layerY K s.circs layer (s.p₁ i).1)) ∧
    (∀ i, i ∉ D.1 → d.v₂ i = mulRep K (d.ctx₂ i)
      (layerX K s.circs layer (s.p₂ i).1) (layerY K s.circs layer (s.p₂ i).1)) ∧
    TreeTwinRunData K D d.ctx₁ d.ctx₂ s.p₁ s.p₂ ∧
    CommonHistory D live d.st₁ ∧ CommonHistory D live d.st₂ ∧
    δ = d.δ ∧ TreeSimFutureEmpty (s.ρ + 1) a.2.1.2 ∧
    a.1.2 = treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
    b.1.2 = treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂

/-- K3: Rerand, including a zero-tuple batch. -/
def RerandStage (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (next : TreeSimPeerData K D) (rest : TreeStagesRerandTail K D next) (live : C.Party → Bool),
    BatchLink K circuits settings top tree D parameter openings (treeTwinRerandCode K D rest) next.st₁ ∧
    Position circuits settings tree D parameter rest.circs (depth rest.circs) next.st₁ ∧
    (∀ i, i ∉ D.1 → ((rest.p₁ i).2.map (·.count)).sum + (outputsOf rest.circs).length = tupleCount rest.circs) ∧
    CommonHistory D live next.st₁ ∧ CommonHistory D live next.st₂ ∧
    δ = next.δ ∧ TreeSimFutureEmpty (rest.ρ + 1) a.2.1.2 ∧
    TreeSimFutureEmpty (rest.ρ + 1) b.2.2 ∧ TreeSimFutureZero (rest.ρ + 1) next.δ ∧
    TreeTwinRunData K D next.ctx₁ next.ctx₂ rest.p₁ rest.p₂ ∧ TreeTwinRerandLink K D rest ∧
    a.1.2 = treeSimPeerPartial K D next.ctx₁ live next.count next.rnd₁ next.v₁ next.st₁ next.k₁ ∧
    b.1.2 = treeSimPeerPartial K D next.ctx₂ live next.count next.rnd₂ next.v₂ next.st₂ next.k₂

/-- K4: the first check Coin with the saved Rerand caller. -/
def RerandCoinStage (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (c : Caller K circuits settings top tree D parameter openings) (rnd : C.Party → PrssOutput C E),
    let n := c.rest.coinNext K D c.peer c.rest.keys c.rest.verify₁ c.rest.verify₂ c.nonzero₁ c.nonzero₂ c.sent
    Position circuits settings tree D parameter c.rest.circs (depth c.rest.circs + 1) n.st₁ ∧
    (∀ i, i ∉ D.1 → c.count₁ K circuits settings top tree D parameter openings i = tupleCount c.rest.circs) ∧
    CommonHistory D n.live n.st₁ ∧ CommonHistory D n.live n.st₂ ∧
    δ = c.peer.δ ∧ TreeSimFutureZero (c.rest.ρ + 2) δ ∧
    TreeSimFutureEmpty (c.rest.ρ + 2) a.2.1.2 ∧ TreeSimFutureEmpty (c.rest.ρ + 2) b.2.2 ∧
    a.1.2 = treeSimCoinPartial K D n.live n.count rnd n.st₁ n.next₁ ∧
    b.1.2 = treeSimCoinPartial K D n.live n.count rnd n.st₂ n.next₂

/-- The three field values sent in the final `openSh`. -/
def finalVector (ctx : Context C) (claim : (ℕ → E) × (ℕ → E) × E)
    (w q : Shares C E) (r : E) : ℕ → E := fun k => match k with
  | 0 => conv K ctx w 0 + r * (conv K ctx w 0 + claim.1 0)
  | 1 => conv K ctx w 1 + r * (conv K ctx w 1 + claim.2.1 0)
  | _ => conv K ctx q 0 + (claim.2.2 + conv K ctx q 0 + conv K ctx q 1) * r + conv K ctx q 1 * r ^ 2

def finalAfterCoin (ctx : Context C) (claim : (ℕ → E) × (ℕ → E) × E) (w q : Shares C E)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (out : E × RunState C) : PartyM C E RealSpec TreeOutput := do
  let opened ← openSh K ctx (finalVector K ctx claim w q out.1) 3
  require (opened 0 * opened 1 = opened 2)
  finish ((), out.2)

/-- The continuation of randomization ExtendMult in `finalStep`. -/
def finalAfterField (ctx : Context C) (claim : (ℕ → E) × (ℕ → E) × E) (w : Shares C E)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C E × RunState C) : PartyM C E RealSpec TreeOutput := do
  let digest ← (treeStagesSaltedDigest K ctx).run out.2
  let coin ← (challenge K (realCheckGadgets K ctx)).run digest.2
  finalAfterCoin K ctx claim w out.1 finish coin

/-- Shared source data of randomization, digest, final Coin and `openSh`. -/
structure FinalData where
  caller : Caller K circuits settings top tree D parameter openings
  claim₁ : C.Party → (ℕ → E) × (ℕ → E) × E
  claim₂ : C.Party → (ℕ → E) × (ℕ → E) × E
  w₁ : C.Party → Shares C E
  w₂ : C.Party → Shares C E

namespace FinalData

def finish₁ (f : FinalData K circuits settings top tree D parameter openings) :=
  (f.caller.checkData K circuits settings top tree D parameter openings).finish₁

def finish₂ (f : FinalData K circuits settings top tree D parameter openings) :=
  (f.caller.checkData K circuits settings top tree D parameter openings).finish₂

def products₁ (f : FinalData K circuits settings top tree D parameter openings) (i : C.Party) : List (Product C E) :=
  let ctx := f.caller.peer.ctx₁ i
  [.shamir (fun _ => conv K ctx (f.w₁ i) 0) (fun _ => conv K ctx (f.w₁ i) 1) 1,
    .shamir (fun _ => conv K ctx (f.w₁ i) 0 + (f.claim₁ i).1 0)
      (fun _ => conv K ctx (f.w₁ i) 1 + (f.claim₁ i).2.1 0) 1]

def products₂ (f : FinalData K circuits settings top tree D parameter openings) (i : C.Party) : List (Product C E) :=
  let ctx := f.caller.peer.ctx₂ i
  [.shamir (fun _ => conv K ctx (f.w₂ i) 0) (fun _ => conv K ctx (f.w₂ i) 1) 1,
    .shamir (fun _ => conv K ctx (f.w₂ i) 0 + (f.claim₂ i).1 0)
      (fun _ => conv K ctx (f.w₂ i) 1 + (f.claim₂ i).2.1 0) 1]

end FinalData

/-- K8: randomization ExtendMult and its salt/digest continuation. -/
def FinalFieldStage (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (f : FinalData K circuits settings top tree D parameter openings) (d : TreeSimExtendMultData K D)
    (live : C.Party → Bool) (offset : ℕ),
    d.ctx₁ = f.caller.peer.ctx₁ ∧ d.ctx₂ = f.caller.peer.ctx₂ ∧ d.count = 2 ∧
    d.v₁ = (fun i => contextProductValues K (d.ctx₁ i) (f.products₁ K circuits settings top tree D parameter openings i)) ∧
    d.v₂ = (fun i => contextProductValues K (d.ctx₂ i) (f.products₂ K circuits settings top tree D parameter openings i)) ∧
    d.k₁ = (fun i => finalAfterField K (d.ctx₁ i) (f.claim₁ i) (f.w₁ i)
      (f.finish₁ K circuits settings top tree D parameter openings i)) ∧
    d.k₂ = (fun i => finalAfterField K (d.ctx₂ i) (f.claim₂ i) (f.w₂ i)
      (f.finish₂ K circuits settings top tree D parameter openings i)) ∧
    Position circuits settings tree D parameter f.caller.rest.circs offset d.st₁ ∧
    CommonHistory D live d.st₁ ∧ CommonHistory D live d.st₂ ∧
    δ = d.δ ∧
    a.1.2 = treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
    b.1.2 = treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂

/-- Real logged answers and cached answers at the simulated histories
after the whole-holder swap. -/
def DigestCertificate (live : C.Party → Bool) (st₁ st₂ : C.Party → RunState C)
    (salts : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (log : TreeSimLog C) (cache : HashCache C) : Prop :=
  CommonHistory D live st₁ ∧ CommonHistory D live st₂ ∧
  ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T → ∃ h₁ h₂ d,
    TreeSimHashAnswer log (.history ((st₁ i).history T)) h₁ ∧
    TreeSimHashAnswer log (.digest (vector 256 (salts i T)) h₁) d ∧
    cache (.history ((st₂ i).history T)) = some h₂ ∧
    cache (.digest (vector 256 (salts i T)) h₂) = some d ∧
    (ds i)[C.terms.idxOf T]? = some d

/-- K9: the digest exchange with the actual final challenge. -/
def DigestStage (_δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (f : FinalData K circuits settings top tree D parameter openings)
    (live : C.Party → Bool) (st₁ st₂ : C.Party → RunState C)
    (q₁ q₂ : C.Party → Shares C E) (salts : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) (offset : ℕ),
    Position circuits settings tree D parameter f.caller.rest.circs offset st₁ ∧
    DigestCertificate D live st₁ st₂ salts ds a.2.2 a.2.1.1 ∧
    a.1.2 = treeSimCheckWaiting K D live (.digests ds) (fun i =>
      (challenge K (realCheckGadgets K (f.caller.peer.ctx₁ i))).run (st₁ i) >>=
        finalAfterCoin K (f.caller.peer.ctx₁ i) (f.claim₁ i) (f.w₁ i) (q₁ i)
          (f.finish₁ K circuits settings top tree D parameter openings i)) ∧
    b.1.2 = treeSimCheckWaiting K D live (.digests ds) (fun i =>
      (challenge K (realCheckGadgets K (f.caller.peer.ctx₂ i))).run (st₂ i) >>=
        finalAfterCoin K (f.caller.peer.ctx₂ i) (f.claim₂ i) (f.w₂ i) (q₂ i)
          (f.finish₂ K circuits settings top tree D parameter openings i))

/-- K10: the final Coin, including the bounded sampler and masked opening. -/
def FinalCoinStage (_δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (f : FinalData K circuits settings top tree D parameter openings) (live : C.Party → Bool)
    (st₁ st₂ : C.Party → RunState C) (q₁ q₂ : C.Party → Shares C E)
    (rnd : C.Party → PrssOutput C E) (offset : ℕ),
    Position circuits settings tree D parameter f.caller.rest.circs offset st₁ ∧
    (∀ i, i ∉ D.1 → (st₁ i).tag = (st₂ i).tag ∧ (st₁ i).label = (st₂ i).label) ∧
    a.1.2 = treeSimCoinPartial K D live 1 rnd st₁ (fun i =>
      treeStagesChallengeTail K (st₁ i).tag (st₁ i).label
        (finalAfterCoin K (f.caller.peer.ctx₁ i) (f.claim₁ i) (f.w₁ i) (q₁ i)
          (f.finish₁ K circuits settings top tree D parameter openings i))) ∧
    b.1.2 = treeSimCoinPartial K D live 1 rnd st₂ (fun i =>
      treeStagesChallengeTail K (st₂ i).tag (st₂ i).label
        (finalAfterCoin K (f.caller.peer.ctx₂ i) (f.claim₂ i) (f.w₂ i) (q₂ i)
          (f.finish₂ K circuits settings top tree D parameter openings i)))

/-- K11: the three-element Shamir opening followed by the output gadget. -/
def FinalOpenStage (_δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (f : FinalData K circuits settings top tree D parameter openings) (live : C.Party → Bool)
    (st₁ st₂ : C.Party → RunState C) (q₁ q₂ : C.Party → Shares C E) (r : C.Party → E) (offset : ℕ),
    Position circuits settings tree D parameter f.caller.rest.circs offset st₁ ∧
    a.1.2 = treeSimCheckWaiting K D live
      (.opening (fun i => finalVector K (f.caller.peer.ctx₁ i) (f.claim₁ i) (f.w₁ i) (q₁ i) (r i)))
      (fun i => f.finish₁ K circuits settings top tree D parameter openings i ((), st₁ i)) ∧
    b.1.2 = treeSimCheckWaiting K D live
      (.opening (fun i => finalVector K (f.caller.peer.ctx₂ i) (f.claim₂ i) (f.w₂ i) (q₂ i) (r i)))
      (fun i => f.finish₂ K circuits settings top tree D parameter openings i ((), st₂ i))

/-- K12: OpenRep and the actual remaining batch caller. -/
def OutputStage (_δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (site : BatchSite settings tree) (prior : C.Party → List (Option (List (List Bit))))
    (ctx₁ ctx₂ : C.Party → Context C) (live : C.Party → Bool)
    (st₁ st₂ : C.Party → RunState C) (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput),
    let circs := runCircuits circuits parameter (site.jobs settings)
    Position circuits settings tree D parameter circs (batchLabels circuits parameter (site.jobs settings)) st₁ ∧
    (∀ i, i ∉ D.1 → (st₁ i).tag = site.tag settings ∧ (prior i).length = site.index) ∧
    a.1.2 = treeSimOpenPartial K D live (outputsOf circs).length v ds (fun i out =>
      batchCaller K circuits settings tree D parameter openings top false (ctx₁ i) site (prior i)
        (assemble circs out, st₁ i)) ∧
    b.1.2 = treeSimOpenPartial K D live (outputsOf circs).length v ds (fun i out =>
      batchCaller K circuits settings tree D parameter openings top true (ctx₂ i) site (prior i)
        (assemble circs out, st₂ i))

/-- The twelve fixed source kinds. -/
def kinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop) :=
  [CollectorStage K circuits settings top tree D A parameter openings,
   PeerStage K circuits settings top tree D A parameter openings,
   RerandStage K circuits settings top tree D A parameter openings,
   RerandCoinStage K circuits settings top tree D A parameter openings,
   TreeTwinExtendChallengeStage K D (SavedPlus K circuits settings top tree D parameter openings),
   TreeTwinChallengeCoinStage K D (SavedPlus K circuits settings top tree D parameter openings),
   TreeTwinStoppedCoinStage K D,
   FinalFieldStage K circuits settings top tree D A parameter openings,
   DigestStage K circuits settings top tree D A parameter openings,
   FinalCoinStage K circuits settings top tree D A parameter openings,
   FinalOpenStage K circuits settings top tree D A parameter openings,
   OutputStage K circuits settings top tree D A parameter openings]

end Stages

section Fields

variable (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
  (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C)) (r : Unit × HashCache C)

/-- Entry into this fixed list, using exactly the openings of the common prefix. -/
def Entry : Prop :=
  TreeTwinEntry3 prims K circuits settings top tree D A parameter seeds pairs z p r
    (treeTwinReq D (treeTwinDataStage K D (fun _ => False)
      (treeTwinLinkedKinds K D (fun _ => False)
        (kinds K circuits settings top tree D A parameter p.1.2))))

/-- One driver round of one source kind, into the same fixed list. -/
def Next (Kind : (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop) : Prop :=
  TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r (fun _ => False)
    (treeTwinLinkedKinds K D (fun _ => False) (kinds K circuits settings top tree D A parameter p.1.2)) Kind

/-- Collector and peer layers, including the Rerand-to-check boundary. -/
def LayersAt : Prop :=
  Next prims K circuits settings top tree D A parameter seeds pairs z p r
    (CollectorStage K circuits settings top tree D A parameter p.1.2) ∧
  Next prims K circuits settings top tree D A parameter seeds pairs z p r
    (PeerStage K circuits settings top tree D A parameter p.1.2) ∧
  Next prims K circuits settings top tree D A parameter seeds pairs z p r
    (RerandStage K circuits settings top tree D A parameter p.1.2)

/-- The first check Coin and an advancing slice/halving Coin. -/
def CheckLoopAt : Prop :=
  Next prims K circuits settings top tree D A parameter seeds pairs z p r
    (RerandCoinStage K circuits settings top tree D A parameter p.1.2) ∧
  Next prims K circuits settings top tree D A parameter seeds pairs z p r
    (TreeTwinChallengeCoinStage K D (fun q =>
      SavedPlus K circuits settings top tree D parameter p.1.2 q ∧
      Advancing K circuits settings top tree D parameter p.1.2 q))

/-- The last slice/halving Coin, randomization, digest, final Coin and opening. -/
def FinalAt : Prop :=
  Next prims K circuits settings top tree D A parameter seeds pairs z p r
    (TreeTwinChallengeCoinStage K D (fun q =>
      SavedPlus K circuits settings top tree D parameter p.1.2 q ∧
      Finishing K circuits settings top tree D parameter p.1.2 q)) ∧
  Next prims K circuits settings top tree D A parameter seeds pairs z p r
    (FinalFieldStage K circuits settings top tree D A parameter p.1.2) ∧
  Next prims K circuits settings top tree D A parameter seeds pairs z p r
    (DigestStage K circuits settings top tree D A parameter p.1.2) ∧
  Next prims K circuits settings top tree D A parameter seeds pairs z p r
    (FinalCoinStage K circuits settings top tree D A parameter p.1.2) ∧
  Next prims K circuits settings top tree D A parameter seeds pairs z p r
    (FinalOpenStage K circuits settings top tree D A parameter p.1.2)

/-- ExtendMult preserves the same saved check predicate. -/
theorem extendNext :
    Next prims K circuits settings top tree D A parameter seeds pairs z p r
      (TreeTwinExtendChallengeStage K D (SavedPlus K circuits settings top tree D parameter p.1.2)) :=
  treeTwinKindNext_extendChallenge prims K circuits settings top tree D A parameter seeds pairs z p r
    (fun _ => False) (SavedPlus K circuits settings top tree D parameter p.1.2) _
    (by simp [kinds, treeTwinLinkedKinds])

/-- The two source cases cover the challenge Coin of this same saved caller. -/
theorem challengeNext
    (advancing : Next prims K circuits settings top tree D A parameter seeds pairs z p r
      (TreeTwinChallengeCoinStage K D (fun q => SavedPlus K circuits settings top tree D parameter p.1.2 q ∧
        Advancing K circuits settings top tree D parameter p.1.2 q)))
    (finishing : Next prims K circuits settings top tree D A parameter seeds pairs z p r
      (TreeTwinChallengeCoinStage K D (fun q => SavedPlus K circuits settings top tree D parameter p.1.2 q ∧
        Finishing K circuits settings top tree D parameter p.1.2 q))) :
    Next prims K circuits settings top tree D A parameter seeds pairs z p r
      (TreeTwinChallengeCoinStage K D (SavedPlus K circuits settings top tree D parameter p.1.2)) := by
  intro n δ swaps a b reach bound good active salts req stage
  obtain ⟨q, rnd, sent, coinRnd, saved, rest⟩ := stage
  rcases saved.check_cases K circuits settings top tree D parameter p.1.2 q with ha | hf
  · exact advancing n δ swaps a b reach bound good active salts req ⟨q, rnd, sent, coinRnd, ⟨saved, ha⟩, rest⟩
  · exact finishing n δ swaps a b reach bound good active salts req ⟨q, rnd, sent, coinRnd, ⟨saved, hf⟩, rest⟩

/-- All twelve cases use one witness; stopped Coins and ExtendMult have generic laws. -/
theorem closedAt
    (layers : LayersAt prims K circuits settings top tree D A parameter seeds pairs z p r)
    (checks : CheckLoopAt prims K circuits settings top tree D A parameter seeds pairs z p r)
    (finals : FinalAt prims K circuits settings top tree D A parameter seeds pairs z p r)
    (output : Next prims K circuits settings top tree D A parameter seeds pairs z p r
      (OutputStage K circuits settings top tree D A parameter p.1.2)) :
    ∀ Kind ∈ kinds K circuits settings top tree D A parameter p.1.2,
      Next prims K circuits settings top tree D A parameter seeds pairs z p r Kind := by
  intro Kind mem
  simp only [kinds, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact layers.1
  · exact layers.2.1
  · exact layers.2.2
  · exact checks.1
  · exact extendNext prims K circuits settings top tree D A parameter seeds pairs z p r
  · exact challengeNext prims K circuits settings top tree D A parameter seeds pairs z p r checks.2 finals.1
  · exact treeTwinKindNext_stoppedCoin prims K circuits settings top tree D A parameter seeds pairs z p r _ _
  · exact finals.2.1
  · exact finals.2.2.1
  · exact finals.2.2.2.1
  · exact finals.2.2.2.2
  · exact output

end Fields

/-- The layer rounds for every good prefix with this fixed padding. -/
def LayersNext : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∀ r ∈ support ((simulateQ (localAnswer prims)
      (padding K circuits settings tree parameter seeds)).run p.2.2.1.1),
    LayersAt prims K circuits settings top tree D A parameter seeds pairs z p r

/-- The advancing check rounds for the same witness. -/
def CheckLoopNext : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∀ r ∈ support ((simulateQ (localAnswer prims)
      (padding K circuits settings tree parameter seeds)).run p.2.2.1.1),
    CheckLoopAt prims K circuits settings top tree D A parameter seeds pairs z p r

/-- The final-check rounds, including the whole-holder digest prefix. -/
def FinalNext : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∀ r ∈ support ((simulateQ (localAnswer prims)
      (padding K circuits settings tree parameter seeds)).run p.2.2.1.1),
    FinalAt prims K circuits settings top tree D A parameter seeds pairs z p r

/-- The output exchange, public continuation and next batch entry. -/
def OutputNext : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∀ r ∈ support ((simulateQ (localAnswer prims)
      (padding K circuits settings tree parameter seeds)).run p.2.2.1.1),
    Next prims K circuits settings top tree D A parameter seeds pairs z p r
      (OutputStage K circuits settings top tree D A parameter p.1.2)

/-- The actual setup continuation enters the same twelve-kind relation. -/
def EntryStage : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∀ r ∈ support ((simulateQ (localAnswer prims)
      (padding K circuits settings tree parameter seeds)).run p.2.2.1.1),
    Entry prims K circuits settings top tree D A parameter seeds pairs z p r

/-- The five local obligations assemble the original linked goal with one
fixed padding and one fixed list; no part chooses an independent witness. -/
theorem treeTwinLinkedGoal_of_closed
    (layers : LayersNext prims K circuits settings)
    (checks : CheckLoopNext prims K circuits settings)
    (finals : FinalNext prims K circuits settings)
    (output : OutputNext prims K circuits settings)
    (entry : EntryStage prims K circuits settings) :
    TreeTwinLinkedGoal prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq small p hp good
  refine ⟨padding K circuits settings tree parameter seeds, fun r hr => ?_⟩
  refine ⟨fun _ => False, kinds K circuits settings top tree D A parameter p.1.2,
    fun _ h => h.elim, entry hb top tree D A parameter seeds pairs z Z q hq small p hp good r hr, ?_⟩
  intro Kind mem
  rcases List.mem_cons.1 mem with rfl | mem
  · intro n δ swaps a b _ _ _ _ _ _ stage
    obtain ⟨_, _, _, _, _, _, allowed, _⟩ := stage
    exact allowed.elim
  · exact closedAt prims K circuits settings top tree D A parameter seeds pairs z p r
      (layers hb top tree D A parameter seeds pairs z Z q hq small p hp good r hr)
      (checks hb top tree D A parameter seeds pairs z Z q hq small p hp good r hr)
      (finals hb top tree D A parameter seeds pairs z Z q hq small p hp good r hr)
      (output hb top tree D A parameter seeds pairs z Z q hq small p hp good r hr) Kind mem

/-- For fixed masks, equality of the first final-opening coordinate at
two challenges forces equality of the corresponding input claim. -/
theorem finalVector_two_challenges (ctx₁ ctx₂ : Context C)
    (claim₁ claim₂ : (ℕ → E) × (ℕ → E) × E) (w₁ w₂ q₁ q₂ : Shares C E)
    (r s : E) (different : r ≠ s)
    (hr : finalVector K ctx₁ claim₁ w₁ q₁ r 0 = finalVector K ctx₂ claim₂ w₂ q₂ r 0)
    (hs : finalVector K ctx₁ claim₁ w₁ q₁ s 0 = finalVector K ctx₂ claim₂ w₂ q₂ s 0) :
    claim₁.1 0 = claim₂.1 0 := by
  simp only [finalVector] at hr hs
  have prod : (r - s) * (claim₁.1 0 - claim₂.1 0) = 0 := by
    linear_combination (1 + s) * hr - (1 + r) * hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left (sub_ne_zero.mpr different))

/-- Three distinct challenges identify every coefficient of the actual
final opening when both mask tables have already been fixed. -/
theorem finalVector_three_challenges (ctx₁ ctx₂ : Context C)
    (claim₁ claim₂ : (ℕ → E) × (ℕ → E) × E) (w₁ w₂ q₁ q₂ : Shares C E)
    (r s t : E) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hr : finalVector K ctx₁ claim₁ w₁ q₁ r = finalVector K ctx₂ claim₂ w₂ q₂ r)
    (hs : finalVector K ctx₁ claim₁ w₁ q₁ s = finalVector K ctx₂ claim₂ w₂ q₂ s)
    (ht : finalVector K ctx₁ claim₁ w₁ q₁ t = finalVector K ctx₂ claim₂ w₂ q₂ t) :
    claim₁.1 0 = claim₂.1 0 ∧ claim₁.2.1 0 = claim₂.2.1 0 ∧ claim₁.2.2 = claim₂.2.2 ∧
    conv K ctx₁ w₁ 0 = conv K ctx₂ w₂ 0 ∧ conv K ctx₁ w₁ 1 = conv K ctx₂ w₂ 1 ∧
    conv K ctx₁ q₁ 0 = conv K ctx₂ q₂ 0 ∧ conv K ctx₁ q₁ 1 = conv K ctx₂ q₂ 1 := by
  have ar := congrFun hr 0
  have as := congrFun hs 0
  have br := congrFun hr 1
  have bs := congrFun hs 1
  have cr := congrFun hr 2
  have cs := congrFun hs 2
  have ct := congrFun ht 2
  simp only [finalVector] at ar as br bs cr cs ct
  have cancel {x y : E} (h : (r - s) * (x - y) = 0) : x = y :=
    sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hrs))
  have ha : claim₁.1 0 = claim₂.1 0 := finalVector_two_challenges K ctx₁ ctx₂
    claim₁ claim₂ w₁ w₂ q₁ q₂ r s hrs (congrFun hr 0) (congrFun hs 0)
  have hb : claim₁.2.1 0 = claim₂.2.1 0 := by
    apply cancel
    linear_combination (1 + s) * br - (1 + r) * bs
  have hw₀ : conv K ctx₁ w₁ 0 = conv K ctx₂ w₂ 0 := by
    apply cancel
    linear_combination r * as - s * ar
  have hw₁ : conv K ctx₁ w₁ 1 = conv K ctx₂ w₂ 1 := by
    apply cancel
    linear_combination r * bs - s * br
  have hq₁ : conv K ctx₁ q₁ 1 = conv K ctx₂ q₂ 1 := by
    have prod : ((r - s) * (r - t) * (s - t)) *
        (conv K ctx₁ q₁ 1 - conv K ctx₂ q₂ 1) = 0 := by
      linear_combination (s - t) * cr + (t - r) * cs + (r - s) * ct
    exact sub_eq_zero.mp ((mul_eq_zero.mp prod).resolve_left
      (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hrs) (sub_ne_zero.mpr hrt)) (sub_ne_zero.mpr hst)))
  rw [hq₁] at cr cs
  have hq₀ : conv K ctx₁ q₁ 0 = conv K ctx₂ q₂ 0 := by
    apply cancel
    linear_combination r * cs - s * cr
  have hd : claim₁.2.2 = claim₂.2.2 := by
    apply cancel
    linear_combination (1 + s) * cr - (1 + r) * cs
  exact ⟨ha, hb, hd, hw₀, hw₁, hq₀, hq₁⟩

/-- A single fixed pair of masks cannot equalize two possible public
challenges when the first claims differ. The possible-challenge premise is
explicit: it cannot be inferred merely from the source program. -/
theorem finalVector_no_fixed_masks (ctx₁ ctx₂ : Context C)
    (claim₁ claim₂ : (ℕ → E) × (ℕ → E) × E)
    (different : claim₁.1 0 ≠ claim₂.1 0) (r s : E) (hrs : r ≠ s) :
    ¬ ∃ w₁ w₂ q₁ q₂ : Shares C E,
      finalVector K ctx₁ claim₁ w₁ q₁ r = finalVector K ctx₂ claim₂ w₂ q₂ r ∧
      finalVector K ctx₁ claim₁ w₁ q₁ s = finalVector K ctx₂ claim₂ w₂ q₂ s := by
  rintro ⟨w₁, w₂, q₁, q₂, hr, hs⟩
  exact different (finalVector_two_challenges K ctx₁ ctx₂ claim₁ claim₂ w₁ w₂ q₁ q₂ r s hrs
    (congrFun hr 0) (congrFun hs 0))

/-- Zero masks and claims 0 and 1 give distinct actual opening views to
any corrupt recipient of a live honest sender, at every nonzero challenge. -/
theorem finalVector_view_ne (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (i j : C.Party) (honest : i ∉ D.1) (corrupt : j ∈ D.1) (r : E) (nonzero : r ≠ 0) :
    treeSimCheckView D (fun _ => true) (.opening (fun k =>
      finalVector K (ctx₁ k) (0, 0, 0) 0 0 r)) ≠
    treeSimCheckView D (fun _ => true) (.opening (fun k =>
      finalVector K (ctx₂ k) (1, 0, 0) 0 0 r)) := by
  intro same
  have ne : j ≠ i := by rintro rfl; exact honest corrupt
  have eq := congrFun (congrFun same j) i
  simp only [treeSimCheckView, corrupt, honest,
    treeSimCheckOut, openOutbox, ne, if_false] at eq
  have vectors := Msg.elements.inj (Option.some.inj eq)
  have first := congrArg (fun xs : List E => xs.getD 0 0) vectors
  simp [vector, finalVector, conv] at first
  exact nonzero first.symm

/-- Any unequal first coordinate of a live honest sender is visible to a
corrupt recipient; the continuation and all other coordinates are irrelevant. -/
theorem openingView_ne_of_first (D : C.Coalition) (live : C.Party → Bool)
    (v₁ v₂ : C.Party → ℕ → E) (i j : C.Party) (honest : i ∉ D.1)
    (active : live i = true) (corrupt : j ∈ D.1) (different : v₁ i 0 ≠ v₂ i 0) :
    treeSimCheckView D live (.opening v₁) ≠ treeSimCheckView D live (.opening v₂) := by
  intro same
  have ne : j ≠ i := by rintro rfl; exact honest corrupt
  have eq := congrFun (congrFun same j) i
  simp only [treeSimCheckView, corrupt, honest, active,
    treeSimCheckOut, openOutbox, ne, if_false] at eq
  have vectors := Msg.elements.inj (Option.some.inj eq)
  exact different (by simpa [vector] using congrArg (fun xs : List E => xs.getD 0 0) vectors)

/-- An adversary may record and abort at just this state. Its earlier rounds
are unrestricted, so the premise is compatible with a nontrivial prefix. -/
theorem recordAt_round (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (save : (C.Party → C.Party → Option (Msg E)) → A.State)
    (record : ∀ view, A.round state view = pure (save view, fun _ _ => some .abort))
    (j : C.Party) (corrupt : j ∈ D.1) (live : C.Party → Bool)
    (kind : TreeSimCheckKind C E) (k : C.Party → PartyM C E RealSpec TreeOutput) :
    stepRound worldRoles D A noFunctionality state (treeSimCheckWaiting K D live kind k) =
      pure (save (treeSimCheckView D live kind), (fun _ => Step.done none),
        (fun _ _ => some .abort)) := by
  rw [treeSim_check_round_factor, record]
  have rejected : ∀ i, treeSimCheckResult K D live kind (fun _ _ => some .abort) i = none := by
    intro i
    have abort : anyAbort (treeSimCheckInbox D live kind (fun _ _ => some .abort) i) = true := by
      apply List.any_eq_true.mpr
      exact ⟨j, by simp [Committee.parties], by simp [treeSimCheckInbox, corrupt, Msg.isAbort]⟩
    simp [treeSimCheckResult, abort]
  simp only [worldRoles, liftComp_pure, counted_pure, pure_bind]
  have resume : treeSimResumeAll (fun i (_ : Unit) => k i)
      (treeSimCheckResult K D live kind (fun _ _ => some .abort)) = pure (fun _ => Step.done none) := by
    unfold treeSimResumeAll
    rw [sequenceFin_congr_pure _ (fun _ => Step.done none)
      (fun i => by rw [rejected i]; rfl), free_pure]
  rw [resume, pure_bind]

/-- A final-round recorder rules out state equality for unequal views.
The bad event reads the unchanged actual log. -/
theorem recordAt_no_coupling (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (save : (C.Party → C.Party → Option (Msg E)) → A.State)
    (injective : Function.Injective save)
    (record : ∀ view, A.round state view = pure (save view, fun _ _ => some .abort))
    (j : C.Party) (corrupt : j ∈ D.1) (live : C.Party → Bool)
    (v₁ v₂ : C.Party → ℕ → E)
    (different : treeSimCheckView D live (.opening v₁) ≠ treeSimCheckView D live (.opening v₂))
    (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (Bad : TreeSimLog C → Prop) (good : ¬ Bad a.2) :
    ¬ RelTriple
      ((stepRound (treeSimRealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live (.opening v₁) k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D A noFunctionality state
        (treeSimCheckWaiting K D live (.opening v₂) k₂)).run b)
      (fun u z => Bad u.2.2 ∨ u.1.1 = z.1.1) := by
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [recordAt_round K D A state save record j corrupt, recordAt_round K D A state save record j corrupt]
  simp only [simulateQ_pure, StateT.run_pure]
  intro h
  obtain ⟨coupling, supported⟩ := relTriple_iff_relWP.mp h
  have eq := SPMF.IsCoupling.pure_iff.mp (by simpa only [evalDist_pure] using coupling.2)
  have property : Bad a.2 ∨ save (treeSimCheckView D live (.opening v₁)) =
      save (treeSimCheckView D live (.opening v₂)) := by
    simpa only [eq, support_pure, Set.mem_singleton_iff, forall_eq] using supported
  exact property.elim good (fun h => different (injective h))

/-- This adversary records the current view and aborts every honest party.
Its state distinguishes different final openings without making any query. -/
def recordingAbort : Adversary C E (Keys C) PEmpty PEmpty where
  State := C.Party → C.Party → Option (Msg E)
  start := fun _ _ => pure (fun _ _ => none)
  round := fun _ view => pure (view, fun _ _ => some .abort)
  answer := fun _ x => nomatch x

/-- An abort from a corrupt party prevents every saved final caller from running. -/
theorem recordingAbort_round (D : C.Coalition) (j : C.Party) (corrupt : j ∈ D.1)
    (state : (recordingAbort (C := C) (E := E)).State) (live : C.Party → Bool)
    (kind : TreeSimCheckKind C E) (k : C.Party → PartyM C E RealSpec TreeOutput) :
    stepRound worldRoles D recordingAbort noFunctionality state (treeSimCheckWaiting K D live kind k) =
      pure (treeSimCheckView D live kind, (fun _ => Step.done none), (fun _ _ => some .abort)) := by
  exact recordAt_round K D recordingAbort state id (fun _ => rfl) j corrupt live kind k

/-- A query-free recorder distinguishes unequal opening views and aborts.
The log and caches stay fixed, so a false initial bad event cannot pay for it. -/
theorem recordingAbort_no_coupling (D : C.Coalition) (j : C.Party) (corrupt : j ∈ D.1)
    (state : (recordingAbort (C := C) (E := E)).State) (live : C.Party → Bool)
    (v₁ v₂ : C.Party → ℕ → E)
    (different : treeSimCheckView D live (.opening v₁) ≠ treeSimCheckView D live (.opening v₂))
    (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (Bad : TreeSimLog C → Prop) (good : ¬ Bad a.2) :
    ¬ RelTriple
      ((stepRound (treeSimRealRoles prims D) D recordingAbort noFunctionality state
        (treeSimCheckWaiting K D live (.opening v₁) k₁)).run a)
      ((stepRound (treeSimIdealRoles prims D) D recordingAbort noFunctionality state
        (treeSimCheckWaiting K D live (.opening v₂) k₂)).run b)
      (fun u z => Bad u.2.2 ∨ u.1.1 = z.1.1) := by
  exact recordAt_no_coupling prims K D recordingAbort state id (fun _ _ h => h) (fun _ => rfl)
    j corrupt live v₁ v₂ different k₁ k₂ a b Bad good

/-- A concrete pair admitted by the source-only final opening kind has no
one-round equality coupling. This does not assert that its real side is a
reached ceremony boundary. -/
theorem finalOpenStage_counterexample (top : TopTree) (tree : Tree) (D : C.Coalition)
    (parameter : PublicParameter) (openings : List (List (List Bit)))
    (c : Caller K circuits settings top tree D parameter openings)
    (st : C.Party → RunState C) (offset : ℕ)
    (position : Position circuits settings tree D parameter c.rest.circs offset st)
    (i j : C.Party) (honest : i ∉ D.1) (corrupt : j ∈ D.1)
    (r : E) (nonzero : r ≠ 0) (cache : TreeSimState C)
    (Bad : TreeSimLog C → Prop) (good : ¬ Bad cache.2) :
    ∃ (a : TreeSimConfig (recordingAbort (C := C) (E := E)) (TreeSimState C))
      (b : TreeSimConfig (recordingAbort (C := C) (E := E)) (HashCache C × HiddenCache C)),
      FinalOpenStage K circuits settings top tree D recordingAbort parameter openings (fun _ => 0) a b ∧
      ¬ RelTriple
        ((stepRound (treeSimRealRoles prims D) D recordingAbort noFunctionality a.1.1 a.1.2).run a.2)
        ((stepRound (treeSimIdealRoles prims D) D recordingAbort noFunctionality b.1.1 b.1.2).run b.2)
        (fun u z => Bad u.2.2 ∨ u.1.1 = z.1.1) := by
  let f : FinalData K circuits settings top tree D parameter openings :=
    ⟨c, fun _ => (0, 0, 0), fun _ => (1, 0, 0), 0, 0⟩
  let v₁ := fun i => finalVector K (c.peer.ctx₁ i) (0, 0, 0) 0 0 r
  let v₂ := fun i => finalVector K (c.peer.ctx₂ i) (1, 0, 0) 0 0 r
  let k₁ := fun i => f.finish₁ K circuits settings top tree D parameter openings i ((), st i)
  let k₂ := fun i => f.finish₂ K circuits settings top tree D parameter openings i ((), st i)
  let state : (recordingAbort (C := C) (E := E)).State := fun _ _ => none
  refine ⟨((state, treeSimCheckWaiting K D (fun _ => true) (.opening v₁) k₁), cache),
    ((state, treeSimCheckWaiting K D (fun _ => true) (.opening v₂) k₂), cache.1), ?_, ?_⟩
  · exact ⟨f, fun _ => true, st, st, 0, 0, fun _ => r, offset, position, rfl, rfl⟩
  · exact recordingAbort_no_coupling prims K D j corrupt state (fun _ => true) v₁ v₂
      (finalVector_view_ne K D c.peer.ctx₁ c.peer.ctx₂ i j honest corrupt r nonzero) k₁ k₂ cache cache.1 Bad good

section Obstruction

variable (top : TopTree) (tree : Tree) (D : C.Coalition)
  (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
  (openings : List (List (List Bit)))
  (f : FinalData K circuits settings top tree D parameter openings)
  (live : C.Party → Bool) (st : C.Party → RunState C) (q : C.Party → Shares C E)
  (r : C.Party → E) (offset n : ℕ)
  (position : Position circuits settings tree D parameter f.caller.rest.circs offset st)
  (a : TreeSimConfig A (TreeSimState C))
  (shape : a.1.2 = treeSimCheckWaiting K D live
    (.opening (fun i => finalVector K (f.caller.peer.ctx₁ i) (f.claim₁ i) (f.w₁ i) (q i) (r i)))
    (fun i => f.finish₁ K circuits settings top tree D parameter openings i ((), st i)))
  (δ : HiddenAddress C → Bit) (cache : HashCache C × HiddenCache C)
  (related : TreeSimStreamRel δ a.2 cache)
  (save : (C.Party → C.Party → Option (Msg E)) → A.State) (injective : Function.Injective save)
  (record : ∀ view, A.round a.1.1 view = pure (save view, fun _ _ => some .abort))
  (i j : C.Party) (honest : i ∉ D.1) (active : live i = true)
  (corrupt : j ∈ D.1) (nonzero : r i ≠ 0)

include position shape related injective record honest active corrupt nonzero in
/-- For an arbitrary real final opening, K11 admits a simulated first
coordinate larger by `r i`. The pair satisfies the full twin relation; only
the simulated claim and masks are chosen here. -/
theorem finalOpenStage_arbitrary_real
    (Bad : TreeSimLog C → Prop) (good : ¬ Bad a.2.2) :
    ∃ b : TreeSimConfig A (HashCache C × HiddenCache C),
      treeTwinReq D (treeTwinDataStage K D (fun _ => False)
        (treeTwinLinkedKinds K D (fun _ => False)
          (kinds K circuits settings top tree D A parameter openings))) n δ a b ∧
      FinalOpenStage K circuits settings top tree D A parameter openings δ a b ∧
      ¬ RelTriple
        ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
        ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
        (fun u z => Bad u.2.2 ∨ u.1.1 = z.1.1) := by
  let v₁ := fun i => finalVector K (f.caller.peer.ctx₁ i) (f.claim₁ i) (f.w₁ i) (q i) (r i)
  let shifted : C.Party → (ℕ → E) × (ℕ → E) × E := fun i =>
    (fun _ => v₁ i 0 / r i + 1, 0, 0)
  let f' : FinalData K circuits settings top tree D parameter openings :=
    { f with claim₂ := shifted, w₂ := 0 }
  let v₂ := fun i => finalVector K (f.caller.peer.ctx₂ i) (shifted i) 0 0 (r i)
  let k₁ := fun i => f.finish₁ K circuits settings top tree D parameter openings i ((), st i)
  let k₂ := fun i => f.finish₂ K circuits settings top tree D parameter openings i ((), st i)
  let b : TreeSimConfig A (HashCache C × HiddenCache C) :=
    ((a.1.1, treeSimCheckWaiting K D live (.opening v₂) k₂), cache)
  have stage : FinalOpenStage K circuits settings top tree D A parameter openings δ a b :=
    ⟨f', live, st, st, q, 0, r, offset, position, shape, rfl⟩
  have flags := treeTwin_flags_of_sameKind D a.1.2 b.1.2 (fun k hk => by
    rw [shape]
    dsimp only [b]
    by_cases hl : live k = true
    · simp only [treeSimCheckWaiting, hk, if_false, hl, if_true, treeSimCheckStep]
      exact Or.inr ⟨_, _, _, _, rfl, rfl⟩
    · simp only [treeSimCheckWaiting, hk, if_false, hl]
      exact Or.inl ⟨rfl, rfl⟩)
  have different : treeSimCheckView D live (.opening v₁) ≠ treeSimCheckView D live (.opening v₂) := by
    apply openingView_ne_of_first D live v₁ v₂ i j honest active corrupt
    have value : v₂ i 0 = v₁ i 0 + r i := by
      simp only [v₂, finalVector, conv, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
        zero_add, shifted]
      field_simp
    rw [value]
    exact fun eq => nonzero (by linear_combination -eq)
  refine ⟨b, ⟨related, rfl, flags.1, flags.2, Or.inr (Or.inr ⟨_, ?_, stage⟩)⟩, stage, ?_⟩
  · simp [treeTwinLinkedKinds, kinds]
  · rw [shape]
    exact recordAt_no_coupling prims K D A a.1.1 save injective record j corrupt live
      v₁ v₂ different k₁ k₂ a.2 cache Bad good

include position shape related injective record honest active corrupt nonzero in
/-- At any reached, good real opening with a live honest sender and a
final-round recorder, the K11 `Next` obligation is false. Reachability is a
hypothesis about `a` only; the simulated counterexample is constructed. -/
theorem finalOpenNext_false_of_reached
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (openings_eq : openings = p.1.2) (pad : Unit × HashCache C)
    (reach : TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((pad.2, p.2.2.1.2), p.2.2.2) n a)
    (bound : n + 3 ≤ ceremonyFuel circuits settings)
    (good : ¬ TreeSimBad3 prims K circuits settings top tree D A
      (dealtKeys parameter seeds pairs) z a.2.2) :
    ¬ Next prims K circuits settings top tree D A parameter seeds pairs z p pad
      (FinalOpenStage K circuits settings top tree D A parameter p.1.2) := by
  subst openings
  obtain ⟨b, req, stage, impossible⟩ := finalOpenStage_arbitrary_real prims K circuits settings
    top tree D A parameter p.1.2 f live st q r offset n position a shape δ cache related
    save injective record i j honest active corrupt nonzero _ good
  have notDone : ¬ AllDone D a.1.2 := by
    intro done
    have hi := done i honest
    rw [shape] at hi
    simp [treeSimCheckWaiting, honest, active, treeSimCheckStep, Step.isDone] at hi
  intro next
  have step := next n δ [] a b reach bound good notDone (by simp)
    (by simpa [treeStagesTwin, treeStagesSwapAll] using req)
    (by simpa [treeStagesTwin, treeStagesSwapAll] using stage)
  apply impossible
  apply relTriple_post_mono (by simpa [treeStagesTwin, treeStagesSwapAll] using step)
  intro u v h
  rcases h with bad | ⟨extra, δ', _, rel⟩
  · exact Or.inl bad
  · exact Or.inr rel.2.1

include position shape injective record honest active corrupt nonzero in
/-- The local obstruction needs no assumption about a simulated cache:
zero translation and the real cache itself always satisfy `TreeSimStreamRel`. -/
theorem finalOpenNext_false_of_reached_same_cache
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (openings_eq : openings = p.1.2) (pad : Unit × HashCache C)
    (reach : TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((pad.2, p.2.2.1.2), p.2.2.2) n a)
    (bound : n + 3 ≤ ceremonyFuel circuits settings)
    (good : ¬ TreeSimBad3 prims K circuits settings top tree D A
      (dealtKeys parameter seeds pairs) z a.2.2) :
    ¬ Next prims K circuits settings top tree D A parameter seeds pairs z p pad
      (FinalOpenStage K circuits settings top tree D A parameter p.1.2) := by
  have related : TreeSimStreamRel (fun _ => 0) a.2 a.2.1 := by
    refine ⟨rfl, fun x => ?_⟩
    simp
  exact finalOpenNext_false_of_reached prims K circuits settings top tree D A parameter
    openings f live st q r offset n position a shape (fun _ => 0) a.2.1 related
    save injective record i j honest active corrupt nonzero seeds pairs z p openings_eq pad reach bound good

end Obstruction

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.position_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms position_mem

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.SavedPlus.check_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SavedPlus.check_cases

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.extendNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms extendNext

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.challengeNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms challengeNext

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.closedAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms closedAt

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.treeTwinLinkedGoal_of_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinLinkedGoal_of_closed

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.finalVector_two_challenges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalVector_two_challenges

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.finalVector_view_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalVector_view_ne

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.recordingAbort_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingAbort_round

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.recordingAbort_no_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordingAbort_no_coupling

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.finalOpenStage_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalOpenStage_counterexample

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.finalVector_three_challenges' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalVector_three_challenges

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.finalVector_no_fixed_masks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalVector_no_fixed_masks

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.openingView_ne_of_first' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms openingView_ne_of_first

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.recordAt_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordAt_round

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.recordAt_no_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordAt_no_coupling

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.finalOpenStage_arbitrary_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalOpenStage_arbitrary_real

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.finalOpenNext_false_of_reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalOpenNext_false_of_reached

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.finalOpenNext_false_of_reached_same_cache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalOpenNext_false_of_reached_same_cache

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.recordPeer_element_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms recordPeer_element_length

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.fieldHistories_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fieldHistories_length

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.finalField_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalField_count

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinLinked2.historyLimit_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms historyLimit_covers

end TreeTwinLinked2
end ThresholdLeanXmssSecurity
