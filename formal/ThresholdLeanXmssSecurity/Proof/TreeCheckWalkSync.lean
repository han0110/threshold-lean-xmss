import ThresholdLeanXmssSecurity.Proof.TreeCheckWalk
import ThresholdLeanXmssSecurity.Proof.TreeLockstepLateBottom

/-!
# Inputs and rejection at synchronized batch boundaries

The input family `batchInputs` supplies dealer values at corrupt indices while
retaining the actual honest PRF inputs. This matters because `MainInputs`
requires consistency at every holder, including corrupt holders, whereas the
network's absent corrupt outputs have empty default projections.

All comparisons use one coherent hash function from the same retained execution.
Opening evidence refers to the saved copies of the actual batch prefix.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section
namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

def TreeCheckPrgQuery : (RoSpec C).Domain → Prop
  | .inl _ => False
  | .inr _ => True

/-- A hash-only oracle computation is fixed by its coherent hash replies. -/
theorem treeCheck_hash_replay {α : Type} (prims : Primitives)
    (hash : Query C → HashOutput)
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (hashes : ∀ q u, allowed (.inl (.inl (.inr (.inl q)))) u → hash q = u)
    (p : OracleComp (RoSpec C) α) (noPrg : IsQueryBoundP p TreeCheckPrgQuery 0)
    (a : α) (run : TreeSimCheckAllowed allowed (oracleStep p : PartyM C E RealSpec α).run (some a)) :
    a = D prims hash p := by
  induction p using OracleComp.inductionOn generalizing a with
  | pure b => exact Option.some.inj run.pure_inv
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at noPrg
    cases t with
    | inr t => simpa [TreeCheckPrgQuery] using noPrg.1
    | inl q =>
      rw [oracleStep_bind] at run
      obtain ⟨v, hv, hk⟩ := run.option_bind_inv _ _ _
      change TreeSimCheckAllowed allowed
        (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
          (.inl (.inl (.inr (.inl q))))) >>= fun u => pure (some u)) (some v) at hv
      obtain ⟨u, hu, he⟩ := hv.bind_inv
      have he := Option.some.inj he.pure_inv
      subst v
      have heq := hashes q u (hu.query_inv _ _)
      rw [D_bind]
      change a = D prims hash (k (hash q))
      rw [heq]
      exact ih u (by simpa [TreeCheckPrgQuery] using noPrg.2 u) a hk

theorem treeCheck_hashOnly_flatMapM {α β : Type}
    (f : α → OracleComp (RoSpec C) (List β))
    (hf : ∀ a, IsQueryBoundP (f a) TreeCheckPrgQuery 0) :
    ∀ xs : List α, IsQueryBoundP (xs.flatMapM f) TreeCheckPrgQuery 0
  | [] => isQueryBoundP_pure _ _ _
  | a :: xs => by
    rw [List.flatMapM_cons]
    exact isQueryBoundP_bind (m := 0) (hf a) fun _ _ =>
      isQueryBoundP_bind (m := 0) (treeCheck_hashOnly_flatMapM f hf xs) fun _ _ =>
        isQueryBoundP_pure _ _ _

theorem treeCheck_inputQuery_hashOnly (ctx : Context C) (job : Job) :
    IsQueryBoundP (inputQuery ctx job) TreeCheckPrgQuery 0 := by
  unfold inputQuery
  apply isQueryBoundP_bind (m := 0) _ (fun _ _ => isQueryBoundP_pure _ _ _)
  simpa using queryBound_mapM TreeCheckPrgQuery _ 0 C.terms (fun T _ => by
    split_ifs
    · apply treeCheck_hashOnly_flatMapM
      intro x
      simp [prf, hashQuery, TreeCheckPrgQuery]
    · exact isQueryBoundP_pure _ _ _)

/-- The value at a held input depends on its seed and hash replies only. -/
theorem treeCheck_D_inputQuery (prims : Primitives) (hash : Query C → HashOutput)
    (ctx : Context C) (job : Job) (T : C.Term) :
    D prims hash (inputQuery ctx job) T =
      if ctx.self ∈ C.holders T then inputBits hash ctx.keys.seed job T else [] := by
  unfold inputQuery
  simp only [D_bind, D_pure, D_mapM]
  rw [getD_terms_idxOf]
  split_ifs <;> simp only [D_flatMapM, prf, D_map, D_hashQuery, inputBits, D_pure]

theorem treeCheck_inputShares_replay (prims : Primitives) (hash : Query C → HashOutput)
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (hashes : ∀ q u, allowed (.inl (.inl (.inr (.inl q)))) u → hash q = u)
    (ctx : Context C) (jobs : List Job) (inputs : MainInput C)
    (run : TreeSimCheckAllowed allowed
      (jobs.mapM (inputShares ctx) : PartyM C E RealSpec _).run (some inputs)) :
    inputs = jobs.map (fun job T =>
      if ctx.self ∈ C.holders T then inputBits hash ctx.keys.seed job T else []) := by
  simp only [inputShares_fun, mapM_oracleStep] at run
  have noPrg : IsQueryBoundP (jobs.mapM (inputQuery ctx)) TreeCheckPrgQuery 0 := by
    simpa using queryBound_mapM TreeCheckPrgQuery _ 0 jobs
      (fun job _ => treeCheck_inputQuery_hashOnly ctx job)
  rw [treeCheck_hash_replay prims hash allowed hashes _ noPrg inputs run, D_mapM]
  apply List.map_congr_left
  intro job _
  exact funext (treeCheck_D_inputQuery prims hash ctx job)

/-- The same complete dealer input family is valid for every static coalition. -/
theorem treeCheck_batchInputs_main (D : C.Coalition) (hash : Query C → HashOutput)
    (seeds : C.Term → HashOutput) (circuits : Circuits) (parameter : PublicParameter)
    (jobs : List Job) :
    MainInputs (jobs.map (circuits parameter ·.kind)) D (batchInputs hash seeds jobs) := by
  obtain ⟨widths, hw, lengths, consistent⟩ := batchInputs_main hash seeds circuits parameter jobs
  exact ⟨widths, hw, fun i _ => lengths i (by simp [noCoalition]), consistent⟩

/-- Every honest prefix input is the corresponding dealer input at the same
coherent hash function. The statement also applies to a party that later aborts. -/
theorem treeCheck_batchPrefix_inputs (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (b : TreeCheckBatchBoundary A)
    (self : ∀ i, (b.ctx i).self = i) (seeds : C.Term → HashOutput)
    (seed : ∀ i T, i ∉ D.1 → i ∈ C.holders T → (b.ctx i).keys.seed T = seeds T)
    (o : (A.State × (C.Party → Option
      (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (run : o ∈ support (treeCheckBatchPre prims K circuits settings D A b))
    (hash : Query C → HashOutput)
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ o.2.2 →
      TreeSimCheckWorldHashes hash t u) :
    ∀ i, i ∉ D.1 → ∀ data, o.1.2 i = some data →
      data.1 = batchInputs hash seeds b.jobs i := by
  have allowed := treeLockstep_logged_allowed prims D (TreeSimCheckWorldHashes hash) _ _ o run rows
  intro i hi data hd
  have localRun := treeSimCheck_phase_replay D A noFunctionality _ _ b.state _ o.1 allowed i hi data hd
  unfold treeSimCheckBatchPrefix at localRun
  obtain ⟨inputs, hp, htail⟩ := localRun.option_bind_inv _ _ _
  obtain ⟨rest, _, he⟩ := htail.option_bind_inv _ _ _
  have he : data = (inputs, rest) := Option.some.inj he.pure_inv
  subst data
  rw [treeCheck_inputShares_replay prims hash _ (fun q u h => h) _ _ inputs hp]
  apply List.map_congr_left
  intro job _
  funext T
  rw [self i]
  by_cases held : i ∈ C.holders T
  · simp only [if_pos held, inputBits, seed i T hi held]
  · simp only [if_neg held]

/-- Erasing corrupt input views leaves the dealer's plain circuit values. -/
theorem treeCheck_mainOutputs_dealer (prims : Primitives) (D : C.Coalition)
    (hash : Query C → HashOutput) (seeds : C.Term → HashOutput)
    (circuits : Circuits) (parameter : PublicParameter) (jobs : List Job) :
    mainOutputs (jobs.map (circuits parameter ·.kind)) (stagesX D (batchInputs hash seeds jobs)) =
      jobs.map (fun job => ThresholdLeanXmssSecurity.D prims hash
        (evalJob circuits parameter seeds job)) := by
  unfold mainOutputs
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  simp only [List.length_map] at h₂
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add, D_evalJob]
  congr 1
  rw [← inputValue_inputBits]
  congr 1
  funext T
  have he : (fun i => (stagesX D (batchInputs hash seeds jobs) i)[k]?) =
      fun i => (stagesHonest D (fun i T =>
        if i ∈ C.holders T then inputBits hash seeds jobs[k] T else []) i).map id := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [stagesX, stagesHonest, hi]
    · simp [stagesX, stagesHonest, hi, batchInputs, List.getElem?_map,
        List.getElem?_eq_getElem h₂]
  rw [he]
  obtain ⟨i, held, _, value⟩ := stages_reconstruct D
    (fun i T => if i ∈ C.holders T then inputBits hash seeds jobs[k] T else []) id T
  rw [value]
  exact if_pos held

/-- Completion preserves the input family seen by the honest circuit proof. -/
theorem treeCheck_stagesX_congr (D : C.Coalition) (x y : C.Party → MainInput C)
    (same : ∀ i, i ∉ D.1 → x i = y i) : stagesX D x = stagesX D y := by
  funext i
  by_cases hi : i ∈ D.1 <;> simp [stagesX, hi, same]

/-- Deterministic acceptance gives the saved circuit output for any completion
of the actual honest inputs satisfying `MainInputs`. -/
theorem treeCheck_batch_saved_correct_completed (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (b : TreeCheckBatchBoundary A)
    (parameter : ∀ i, (b.ctx i).keys.parameter = b.parameter)
    (o : (A.State × (C.Party → Option
      (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (run : o ∈ support (treeCheckBatchPre prims K circuits settings D A b))
    (live : ∀ i, i ∉ D.1 → (o.1.2 i).isSome)
    (x : C.Party → MainInput C)
    (inputs : MainInputs (b.jobs.map (circuits b.parameter ·.kind)) D x)
    (same : ∀ i, i ∉ D.1 → (treeCheckPrefixData (o.1.2 i)).1 = x i)
    (accept : (multVerifyLeak D (stagesHonest D
      (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.2))).2.2) :
    let js := b.jobs.map (circuits b.parameter ·.kind)
    let v := fun i => (treeCheckPrefixData (o.1.2 i)).2.1.1
    (∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < (outputsOf js).length →
      v i T g = v (refHolder D T) T g) ∧
    assemble js (shareValue (fun T => v (refHolder D T) T)) = mainOutputs js (stagesX D x) := by
  dsimp only
  obtain ⟨log, replay⟩ := treeSimCheckReplay_of_support _ _
    (treeCheck_logged_support prims D _ _ run)
  have traces : ∀ i, ∃ p, i ∉ D.1 →
      TreeCheckLayerTrace K settings.mode (b.jobs.map (circuits b.parameter ·.kind))
        (x i) (depth (b.jobs.map (circuits b.parameter ·.kind))) p ∧
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
    have hx : data.1 = x i := by simpa [hd, treeCheckPrefixData] using same i hi
    simpa only [hd, treeCheckPrefixData, Option.getD_some, parameter i, hx] using And.intro ht he
  choose p hp using traces
  have eq : stagesHonest D (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.2) =
      stagesHonest D (treeCheckSavedTuples K (b.jobs.map (circuits b.parameter ·.kind)) p
        (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.1)) := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [stagesHonest, hi]
    · simp only [stagesHonest, if_neg hi, treeCheckSavedTuples, (hp i hi).2]
  rw [eq] at accept
  exact treeCheck_saved_correct K D settings.mode _ x inputs p _ (fun i hi => (hp i hi).1) accept

set_option maxHeartbeats 800000 in
/-- The actual opening rejects a wrong dealer output under deterministic
verification, using completed PRF inputs rather than empty corrupt defaults. -/
theorem treeCheck_open_dealer_reject (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (b : TreeCheckBatchBoundary A)
    (parameter : ∀ i, (b.ctx i).keys.parameter = b.parameter)
    (self : ∀ i, (b.ctx i).self = i) (seeds : C.Term → HashOutput)
    (seed : ∀ i T, i ∉ D.1 → i ∈ C.holders T → (b.ctx i).keys.seed T = seeds T)
    (o : (A.State × (C.Party → Option
      (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C)
    (pref : o ∈ support (treeCheckBatchPre prims K circuits settings D A b))
    (present : ∀ i, i ∉ D.1 → (o.1.2 i).isSome)
    (hash : Query C → HashOutput)
    (rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ o.2.2 →
      TreeSimCheckWorldHashes hash t u)
    (live : C.Party → Bool) (ds : C.Party → List HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) (s final : TreeSimState C) (out : ℕ → Bit)
    (hashes : ∀ h, h ∉ D.1 → live h = true →
      (ds h).length = C.terms.length ∧ ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer s.2 (.copy (vector
          (outputsOf (b.jobs.map (circuits b.parameter ·.kind))).length
          ((treeCheckPrefixData (o.1.2 h)).2.1.1 T))) u)
    (run : (some out, final) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (treeSimOpenHead K D live
        (outputsOf (b.jobs.map (circuits b.parameter ·.kind))).length
        (fun h => (treeCheckPrefixData (o.1.2 h)).2.1.1) ds sent i) (LocalSpec C)))).run s))
    (good : ¬ TreeSimHashBudgetCollision final.2)
    (wrong : assemble (b.jobs.map (circuits b.parameter ·.kind)) out ≠
      b.jobs.map (fun job => ThresholdLeanXmssSecurity.D prims hash
        (evalJob circuits b.parameter seeds job))) :
    ¬ (multVerifyLeak D (stagesHonest D
      (fun h => (treeCheckPrefixData (o.1.2 h)).2.1.2))).2.2 := by
  intro accept
  have same : ∀ h, h ∉ D.1 →
      (treeCheckPrefixData (o.1.2 h)).1 = batchInputs hash seeds b.jobs h := by
    intro h hh
    obtain ⟨data, hd⟩ := Option.isSome_iff_exists.mp (present h hh)
    simpa only [hd, treeCheckPrefixData, Option.getD_some] using
      treeCheck_batchPrefix_inputs prims K circuits settings D A b self seeds seed o pref hash rows h hh data hd
  obtain ⟨held, correct⟩ := treeCheck_batch_saved_correct_completed prims K circuits settings D A b
    parameter o pref present _ (treeCheck_batchInputs_main D hash seeds circuits b.parameter b.jobs)
      same accept
  have value : ∀ g < (outputsOf (b.jobs.map (circuits b.parameter ·.kind))).length,
      out g = shareValue (fun T => (treeCheckPrefixData (o.1.2 (refHolder D T))).2.1.1 T) g := by
    with_reducible
      exact treeLockstep_open_head_value prims K D live _
        (fun h => (treeCheckPrefixData (o.1.2 h)).2.1.1)
        (fun T => (treeCheckPrefixData (o.1.2 (refHolder D T))).2.1.1 T)
        held ds sent i s final out hashes run good
  apply wrong
  exact (treeLockstep_assemble_congr _ out _ value).trans
    (correct.trans (treeCheck_mainOutputs_dealer prims D hash seeds circuits b.parameter b.jobs))

/-- An opening of the checkpoint's own saved copies, with its actual local
run and one coherent dealer hash view. -/
structure TreeCheckOpeningAt (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (b : TreeCheckBatchBoundary A)
    (o : (A.State × (C.Party → Option
      (MainInput C × (Shares C Bit × List (Tuple C)) × RunState C))) × TreeSimState C) where
  seeds : C.Term → HashOutput
  seed : ∀ i T, i ∉ D.1 → i ∈ C.holders T → (b.ctx i).keys.seed T = seeds T
  hash : Query C → HashOutput
  rows : ∀ t u, (⟨t, u⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ o.2.2 →
    TreeSimCheckWorldHashes hash t u
  live : C.Party → Bool
  ds : C.Party → List HashOutput
  sent : C.Party → Mail C E
  party : C.Party
  before : TreeSimState C
  after : TreeSimState C
  output : ℕ → Bit
  hashes : ∀ h, h ∉ D.1 → live h = true →
    (ds h).length = C.terms.length ∧ ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
      TreeSimHashAnswer before.2 (.copy (vector
        (outputsOf (b.jobs.map (circuits b.parameter ·.kind))).length
        ((treeCheckPrefixData (o.1.2 h)).2.1.1 T))) u
  run : (some output, after) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (free (liftComp (treeSimOpenHead K D live
      (outputsOf (b.jobs.map (circuits b.parameter ·.kind))).length
      (fun h => (treeCheckPrefixData (o.1.2 h)).2.1.1) ds sent party) (LocalSpec C)))).run before)
  good : ¬ TreeSimHashBudgetCollision after.2
  wrong : assemble (b.jobs.map (circuits b.parameter ·.kind)) output ≠
    b.jobs.map (fun job => ThresholdLeanXmssSecurity.D prims hash
      (evalJob circuits b.parameter seeds job))

namespace TreeCheckBatchWalk

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (top : TopTree) (tree : Tree) (D : C.Coalition)
variable (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
variable (Z : Distinguisher C A.State TreeOutput) (j : Fin (treeBatches settings tree))

/-- Every live boundary has an actual wrong opening of its saved values. -/
def Opening (W : TreeCheckBatchWalk A) : Prop :=
  ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
    support (W.cut prims K circuits settings D Z).pre →
    (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j
      (.inl (c, o)) → Nonempty (TreeCheckOpeningAt prims K circuits D A (W.boundary c) o)

/-- The opening linkage yields the exact cut rejection predicate. -/
theorem reject_of_opening (W : TreeCheckBatchWalk A)
    (standard : W.StandardTuples circuits D)
    (self : ∀ c i, ((W.boundary c).ctx i).self = i)
    (parameter : ∀ c i, ((W.boundary c).ctx i).keys.parameter = (W.boundary c).parameter)
    (unreached : W.Unreached prims K circuits settings D top tree x z j)
    (opening : W.Opening prims K circuits settings top tree D A x z Z j) :
    (W.cut prims K circuits settings D Z).Reject prims K circuits settings top tree D A x z j := by
  rintro (⟨c, o⟩ | r) hs hlive
  · obtain ⟨proof⟩ := opening c o hs hlive
    obtain ⟨r, hr, hbad, _⟩ := hlive
    obtain ⟨_, _, _, _, i, value, records, _, _, _, _, _, _, hout, _⟩ := hbad.2
    have present := treeCheckBatch_live prims K circuits D A Z (W.boundary c) o r hr
      ⟨i, (value, records), hout⟩
    have reject := treeCheck_open_dealer_reject prims K circuits settings D A (W.boundary c)
      (parameter c) (self c) proof.seeds proof.seed o (mem_support_cut_pre hs) present proof.hash proof.rows
      proof.live proof.ds proof.sent proof.party proof.before proof.after proof.output proof.hashes proof.run
      proof.good proof.wrong
    have same : (fun i => if i ∈ D.1 then none else some ((W.hybrid c o).tuples i)) =
        stagesHonest D (fun i => (treeCheckPrefixData (o.1.2 i)).2.1.2) := by
      funext i
      by_cases hi : i ∈ D.1
      · simp [stagesHonest, hi]
      · simp only [if_neg hi, stagesHonest, (standard c o).2 i hi]
        cases o.1.2 i <;> rfl
    change ¬ (multVerifyLeak D (fun i => if i ∈ D.1 then none else some ((W.hybrid c o).tuples i))).2.2
    rw [same]
    exact reject
  · obtain ⟨r', hr, bad, counted⟩ := hlive
    have he : r' = r := by simpa [cut] using hr
    subst r'
    exact (unreached r (mem_support_cut_pre_inr hs) ⟨bad, counted⟩).elim

end TreeCheckBatchWalk

/-- Replacing an absent snapshot by the aborted step is an exact inverse. -/
theorem treeCheck_snapshot_restore {α : Type} (step : Step C E RealSpec α) :
    (treeLateSnapshotOut step).getD (.done none) = step := by
  cases step with
  | done out => cases out <;> rfl
  | wait out k => rfl
  | call impossible k => exact impossible.elim

/-- The exact global phase cut retains pending local heads and their aborts.
It does not commute the final hashes of one batch past the next batch's queries. -/
theorem treeCheck_snapshot_split {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) :
    executePhase worldRoles D A noFunctionality (n + fuel) state program = (do
      let captured ← executePhase worldRoles D A noFunctionality n state
        (fun i => treeLateSnapshot n (program i))
      executeRounds worldRoles D A noFunctionality fuel captured.1
        (fun i => (captured.2 i).getD (.done none))) := by
  rw [treeLateSnapshot_phase, bind_map_left]
  simp only [treeCheck_snapshot_restore, executePhase, executeRounds_add, bind_assoc]

/-- Logging the pending-step cut retains the original final state, both caches,
and the entire log for every initial state and every continuation fuel. -/
theorem treeCheck_snapshot_logged {α : Type} (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) (s : TreeSimState C) :
    (simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (n + fuel) state program)).run s = (do
      let captured ← (simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality n state
          (fun i => treeLateSnapshot n (program i)))).run s
      (simulateQ (treeSimLoggedWorld prims D)
        (executeRounds worldRoles D A noFunctionality fuel captured.1.1
          (fun i => (captured.1.2 i).getD (.done none)))).run captured.2) := by
  rw [treeCheck_snapshot_split D A n fuel state program]
  simp only [simulateQ_bind, StateT.run_bind]

/-- The synchronized-walk clauses of the counted cut, with the original
quantifiers and the original literal `Split`, `Consistent`, and `Reject`. -/
def TreeCheckWalkSyncGoal (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x → IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
        ∀ p ∈ support (treeSaltSetup prims D A x z), ∃ W : TreeCheckBatchWalk A,
          W.Split prims K circuits settings D top tree x Z p ∧
          W.StandardTuples circuits D ∧
          (∀ c i, ((W.boundary c).ctx i).self = i) ∧
          (W.cut prims K circuits settings D Z).Jobs prims K circuits settings top tree D A x z j ∧
          W.Unreached prims K circuits settings D top tree x z j ∧
          W.Consistent prims K circuits settings D top tree x z Z j ∧
          (W.cut prims K circuits settings D Z).Reject prims K circuits settings top tree D A x z j

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_hash_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_hash_replay

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_batchPrefix_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_batchPrefix_inputs

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_mainOutputs_dealer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_mainOutputs_dealer

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_batch_saved_correct_completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_batch_saved_correct_completed

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_open_dealer_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_open_dealer_reject

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckBatchWalk.reject_of_opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeCheckBatchWalk.reject_of_opening

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_snapshot_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_snapshot_split

/-- info: 'ThresholdLeanXmssSecurity.treeCheck_snapshot_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheck_snapshot_logged

end ThresholdLeanXmssSecurity
