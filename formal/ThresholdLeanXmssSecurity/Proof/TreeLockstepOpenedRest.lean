import ThresholdLeanXmssSecurity.Proof.TreeLockstepOpened

/-!
# Recorded rerandomization and synchronized openings

Filled peer terms occur in the recorded history. Equal histories therefore
determine the saved rerandomized copies at their common offsets, even though
the later check appends different suffixes. Unfilled terms are absent from
the history; their copies instead agree by the shared PRSS key and cache.
No correctness assumption on the multiplication tuples is needed here.

`treeLockstep_check_beforeSalt_boundary` extracts the actual joint pre-salt
state and its surviving suffix. `treeLockstep_check_history_agreement` pulls
digest agreement back to the initial checkpoint. `treeLockstep_checked_rerand_held`
then obtains common saved copies from that check and common-cache PRSS readiness.
`treeLockstep_open_saved_outputs` passes their canonical job outputs to the
original audited continuation, from its actual post-opening cache and log.

`TreeLockstepOpenedGoal` requires the whole audited ceremony invariant: obtain these synchronized
batch/check/open cuts, common contexts and absolute labels, and the unfilled
PRSS readiness certificates from one reached execution. The bottom-tree batch
induction must also carry the common first-run outputs into the second run's
job selection. Per-party final-record support does not supply these joint facts;
assuming `TreeLockstepRecordsAgreeGoal` would make that argument circular.

The target concerns successful final outputs. As review P2 explains, final records do not cover aborted prefixes.
The pinned and current leanVM proofs were searched; the history and
replicated-share argument is specific to this threshold protocol. The generic
digest/opening factorizations below reuse the local TreeSim/TreeSimStages proofs
with an arbitrary return type so that audit records are retained.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- The same ready stream block determines its finite values, for visible
AES streams as well as hidden lazy streams. -/
theorem treeLockstep_stream_values (prims : Primitives) (D : C.Coalition)
    (name : KeyName C) (key : HashOutput) (label idx count : ℕ)
    (a b : ℕ → Bit) (hash : HashCache C) (cache : HiddenCache C)
    (ha : TreeSimStreamReady prims D name key label idx count a hash cache)
    (hb : TreeSimStreamReady prims D name key label idx count b hash cache) :
    ∀ g < count, a g = b g := by
  unfold TreeSimStreamReady at ha hb
  split_ifs at ha hb with hidden
  · intro g hg
    exact Option.some.inj ((ha g hg).symm.trans (hb g hg))
  · obtain ⟨da, hda, hva⟩ := ha
    obtain ⟨db, hdb, hvb⟩ := hb
    have hd : da = db := Option.some.inj (hda.symm.trans hdb)
    subst db
    exact fun g hg => (hva g hg).trans (hvb g hg).symm

section Records
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

/-- Counts and modes alone determine history lengths. This does not assume
the stronger `TupleInputs` relation or agreement of tuple values. -/
theorem treeLockstep_filledHistory_length (i j : C.Party) (T : C.Term)
    (hi : i ∈ C.holders T) (hj : j ∈ C.holders T) (a b : List (Tuple C))
    (counts : a.map (·.count) = b.map (·.count))
    (modes : a.map (·.mode) = b.map (·.mode)) :
    (filledHistory K i a T).length = (filledHistory K j b T).length := by
  have shape := map_pair_eq a b (·.count) (·.mode) counts modes
  have eq := congrArg (fun xs : List (ℕ × ReshareMode) =>
    (xs.map fun p => ((List.range p.1).filter fun g => (filler K p.2 T g).isSome).length).sum) shape
  simpa only [filledHistory, if_pos hi, if_pos hj, List.length_flatMap,
    List.length_map, List.map_map, Function.comp_def] using eq

theorem treeLockstep_recordMode_filled (i : C.Party) (T : C.Term)
    (held : i ∈ C.holders T) (filled : T ∈ filledTerms K)
    (h : C.Term → List Bit) (v : Shares C Bit) (count : ℕ) :
    recordMode K .peer i h v count T = h T ++ vector count (v T) := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp filled
  have hf (g : ℕ) : (filler K .peer (K.filled j) g).isSome = true := by
    rw [filler, List.find?_isSome]
    exact ⟨j, by simp [Committee.parties], by simp⟩
  simp only [recordMode, if_pos held, hf, List.filter_true, bitCodec,
    Function.comp_def, ← List.map_eq_flatMap, vector]

/-- Later check records cannot conceal disagreement at the rerandomization
segment. Only the preceding lengths need to agree. -/
theorem treeLockstep_recorded_rerand (i j : C.Party) (T : C.Term)
    (hi : i ∈ C.holders T) (hj : j ∈ C.holders T) (filled : T ∈ filledTerms K)
    (a b : C.Term → List Bit) (v w : Shares C Bit) (count : ℕ)
    (left right : List Bit) (lengths : (a T).length = (b T).length)
    (histories : recordMode K .peer i a v count T ++ left =
      recordMode K .peer j b w count T ++ right) :
    vector count (v T) = vector count (w T) := by
  rw [treeLockstep_recordMode_filled K i T hi filled,
    treeLockstep_recordMode_filled K j T hj filled,
    List.append_assoc, List.append_assoc] at histories
  have tails := (List.append_inj histories lengths).2
  exact List.append_inj_left tails (by simp [vector])

/-- Equal checked histories and shared stream blocks determine every held
rerandomized copy. Recipient-specific corrupt messages remain unrestricted. -/
theorem treeLockstep_rerand_held (prims : Primitives) (D : C.Coalition)
    (ctx : C.Party → Context C) (label count : ℕ)
    (r v : C.Party → Shares C Bit) (hash : HashCache C) (cache : HiddenCache C)
    (keys : Consistent D (fun i T => (ctx i).prss.term T))
    (ready : ∀ i T, i ∉ D.1 → i ∈ C.holders T → T ∉ filledTerms K →
      TreeSimStreamReady prims D (.term T) ((ctx i).prss.term T) label 0 count (r i T) hash cache)
    (unfilled : ∀ i T g, i ∉ D.1 → i ∈ C.holders T → T ∉ filledTerms K →
      g < count → v i T g = r i T g)
    (before tail : C.Party → C.Term → List Bit)
    (lengths : ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (before i T).length = (before j T).length)
    (histories : ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      recordMode K .peer i (before i) (v i) count T ++ tail i T =
      recordMode K .peer j (before j) (v j) count T ++ tail j T) :
    ∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < count →
      v i T g = v (refHolder D T) T g := by
  intro i T g hi hiT hg
  obtain ⟨hjT, hj⟩ := refHolder_spec D T
  by_cases filled : T ∈ filledTerms K
  · have eq := treeLockstep_recorded_rerand K i (refHolder D T) T hiT hjT filled
      (before i) (before (refHolder D T)) (v i) (v (refHolder D T)) count
      (tail i T) (tail (refHolder D T) T)
      (lengths T i _ hi hj hiT hjT) (histories T i _ hi hj hiT hjT)
    simpa only [vector_getD _ _ g hg] using congrArg (fun xs => xs.getD g 0) eq
  · rw [unfilled i T g hi hiT filled hg, unfilled _ T g hj hjT filled hg]
    have hr := ready i T hi hiT filled
    have hs := ready (refHolder D T) T hj hjT filled
    have hk := keys T i hiT (refHolder D T) hjT hi hj
    dsimp only at hk
    rw [hk] at hr
    exact treeLockstep_stream_values prims D (.term T) _ label 0 count _ _ hash cache hr hs g hg

end Records

section Checkpoint
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

/-- The saved sharing really is the last peer tuple, at the history offset
given by the preceding circuit layers. This is derived from actual support. -/
theorem treeLockstep_beforeVerify_rerand (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) (label tag : ℕ)
    (out : Shares C Bit × List (Tuple C)) (final : RunState C)
    (run : some (out, final) ∈ support
      ((treeSimCheckBeforeVerify K ctx mode jobs inputs).run ⟨fun _ => [], label, tag⟩).run) :
    ∃ tuples x,
      out.2 = tuples ++ [⟨x, one K, out.1, (outputsOf jobs).length, .peer⟩] ∧
      final.history = recordMode K .peer ctx.self (filledHistory K ctx.self tuples)
        out.1 (outputsOf jobs).length ∧
      tuples.map (·.count) = (List.range (depth jobs)).map (fun l => (gatesAt jobs l).length) ∧
      tuples.map (·.mode) = (List.range (depth jobs)).map (fun _ => mode) := by
  simp only [treeSimCheckBeforeVerify, StateT.run_bind, StateT.run_pure] at run
  obtain ⟨⟨p, st⟩, hp, run⟩ := treeSimCheck_some_bind _ _ _ run
  obtain ⟨⟨z, next⟩, hz, he⟩ := treeSimCheck_some_bind _ _ _ run
  simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq,
    Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl⟩
  obtain ⟨hh, _, _, hc, hm⟩ := treeSimCheck_layers_state K ctx mode jobs
    (List.range (depth jobs)) (inputs, []) ⟨fun _ => [], label, tag⟩ p st
      (by funext T; simp [filledHistory]) hp
  refine ⟨p.2, outputShares K jobs p.1, rfl, ?_, ?_, ?_⟩
  · rw [treeSimCheck_rerand_state K ctx mode _ _ st z final hz]
    exact congrArg (fun h => recordMode K .peer ctx.self h z _) hh
  · simpa only [List.map_nil, List.nil_append] using hc
  · simpa only [List.map_nil, List.nil_append] using hm

/-- The same offset certificate for a live joint batch checkpoint, without
discarding the original joint replay premise. -/
theorem treeLockstep_batchPrefix_rerand (circuits : Circuits) (settings : Settings)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, (ctx i).self = i)
    (parameter : PublicParameter) (parameters : ∀ i, (ctx i).keys.parameter = parameter)
    (jobs : List Job) (initial : ℕ × ℕ) (log : TreeSimLog C)
    (r : A.State × (C.Party → Option
      (List (C.Term → List Bit) × (Shares C Bit × List (Tuple C)) × RunState C)))
    (run : TreeSimCheckReplay (executePhase worldRoles D A noFunctionality fuel state
      (fun i => treeSimCheckBatchPrefix K circuits settings (ctx i) jobs initial)) log r)
    (live : ∀ i, i ∉ D.1 → (r.2 i).isSome) :
    ∀ i, i ∉ D.1 → ∃ data tuples x, r.2 i = some data ∧
      data.2.1.2 = tuples ++ [⟨x, one K, data.2.1.1,
        (outputsOf (jobs.map (circuits parameter ·.kind))).length, .peer⟩] ∧
      data.2.2.history = recordMode K .peer i (filledHistory K i tuples) data.2.1.1
        (outputsOf (jobs.map (circuits parameter ·.kind))).length ∧
      tuples.map (·.count) = (List.range (depth (jobs.map (circuits parameter ·.kind)))).map
        (fun l => (gatesAt (jobs.map (circuits parameter ·.kind)) l).length) ∧
      tuples.map (·.mode) = (List.range (depth (jobs.map (circuits parameter ·.kind)))).map
        (fun _ => settings.mode) := by
  intro i hi
  obtain ⟨data, hd⟩ := Option.isSome_iff_exists.mp (live i hi)
  obtain ⟨_, replay, _⟩ := treeSimCheck_phase_replay D A noFunctionality (fun _ _ => True)
    fuel state _ r ⟨log, run, fun _ _ _ => trivial⟩ i hi data hd
  have h := replay.mem_support
  unfold treeSimCheckBatchPrefix at h
  obtain ⟨inputs, _, h⟩ := treeSimCheck_some_bind _ _ _ h
  obtain ⟨p, hp, he⟩ := treeSimCheck_some_bind _ _ _ h
  have he' : data = (inputs, p) := by simpa using he
  subst data
  obtain ⟨tuples, x, ht, hh, hc, hm⟩ := treeLockstep_beforeVerify_rerand K (ctx i)
    settings.mode _ inputs initial.1 initial.2 p.1 p.2 hp
  exact ⟨(inputs, p), tuples, x, hd, by simpa only [parameters i] using ht,
    by simpa only [parameters i, self i] using hh,
    by simpa only [parameters i] using hc, by simpa only [parameters i] using hm⟩

end Checkpoint

section Timing
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

private theorem openedRest_timed_require {α : Type} (n : ℕ) (p : Prop)
    (k : Unit → PartyM C E RealSpec α) (hk : ∀ u, TreeSimCheckTimed n (k u).run) :
    TreeSimCheckTimed n (require p >>= k).run := by
  unfold require
  split_ifs
  · simpa only [pure_bind] using hk ()
  · exact .abort n

theorem treeLockstep_timed_coin (ctx : Context C) (count : ℕ) (st : RunState C) :
    TreeSimCheckTimed 1 (((realCheckGadgets (G := RealSpec) K ctx).coin count).run st).run := by
  rw [realCoin_run]
  apply TreeSimCheckTimed.oracle_bind 0
  intro rnd
  unfold openSh
  rw [bind_assoc]
  apply TreeSimCheckTimed.exchange_bind 0
  intro inbox
  simp only [bind_assoc]
  exact openedRest_timed_require 0 _ _ (fun _ => .done _)

theorem treeLockstep_timed_digest (ctx : Context C) (salts : Shares C Bit) (st : RunState C) :
    TreeSimCheckTimed 1 ((compareDigests (E := E) (G := RealSpec) ctx salts).run st).run := by
  rw [compareDigests_run]
  exact TreeSimCheckTimed.oracle_bind 0 _ _ (fun _ =>
    TreeSimCheckTimed.exchange_bind 0 _ _ (fun _ =>
      openedRest_timed_require 0 _ _ (fun _ => .done _)))

/-- Challenge expansion stays before the continuation's next exchange. -/
theorem treeLockstep_timed_challenge {α : Type} (ctx : Context C) (n : ℕ)
    (k : E × RunState C → PartyM C E RealSpec α)
    (hk : ∀ p, TreeSimCheckTimed (n + 1) (k p).run) (st : RunState C) :
    TreeSimCheckTimed (n + 2)
      (((challenge K (realCheckGadgets K ctx)).run st) >>= k).run := by
  simp only [challenge, coinKey, StateT.run_bind, StateT.run_get,
    StateT.run_lift, pure_bind, bind_assoc]
  rw [show n + 2 = 1 + (n + 1) by omega]
  apply (treeLockstep_timed_coin K ctx 1 st).bind
  intro p
  apply TreeSimCheckTimed.oracle_bind n
  intro key
  apply TreeSimCheckTimed.oracle_bind n
  intro value
  cases value with
  | none => exact .abort (n + 1)
  | some value => simpa only [StateT.run_pure, pure_bind] using hk (value, p.2)

theorem treeLockstep_timed_extendMult (ctx : Context C) (products : List (Product C E))
    (st : RunState C) :
    TreeSimCheckTimed 1 (((realCheckGadgets (G := RealSpec) K ctx).extendMult products).run st).run := by
  rw [realExtendMult_run]
  exact TreeSimCheckTimed.oracle_bind 0 _ _ (fun _ =>
    TreeSimCheckTimed.exchange_bind 0 _ _ (fun _ => .done _))

private theorem openedRest_timed_slice {α : Type} (ctx : Context C) (τ : List E)
    (count : ℕ) (p : Shares C E × Shares C E × E) (j n : ℕ)
    (k : (Shares C E × Shares C E × E) × RunState C → PartyM C E RealSpec α)
    (hk : ∀ p, TreeSimCheckTimed (n + 1) (k p).run) (st : RunState C) :
    TreeSimCheckTimed (2 + n + 1)
      (((sliceStep K ctx (realCheckGadgets K ctx) τ count p j).run st) >>= k).run := by
  rcases p with ⟨x, y, d⟩
  simp only [sliceStep, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  rw [show 2 + n + 1 = 1 + (n + 2) by omega]
  apply (treeLockstep_timed_extendMult K ctx _ st).bind
  intro t
  exact treeLockstep_timed_challenge K ctx n _ (fun _ => hk _) t.2

private theorem openedRest_timed_halving {α : Type} (ctx : Context C)
    (width : ℕ) (p : (ℕ → E) × (ℕ → E) × E) (j n : ℕ)
    (k : ((ℕ → E) × (ℕ → E) × E) × RunState C → PartyM C E RealSpec α)
    (hk : ∀ p, TreeSimCheckTimed (n + 1) (k p).run) (st : RunState C) :
    TreeSimCheckTimed (2 + n + 1)
      (((halvingStep K ctx (realCheckGadgets K ctx) width p j).run st) >>= k).run := by
  rcases p with ⟨x, y, d⟩
  simp only [halvingStep, StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  rw [show 2 + n + 1 = 1 + (n + 2) by omega]
  apply (treeLockstep_timed_extendMult K ctx _ st).bind
  intro t
  exact treeLockstep_timed_challenge K ctx n _ (fun _ => hk _) t.2

private theorem openedRest_timed_fold {α β γ : Type}
    (f : α → β → RunM C E RealSpec α)
    (hf : ∀ a b n (k : α × RunState C → PartyM C E RealSpec γ),
      (∀ p, TreeSimCheckTimed (n + 1) (k p).run) → ∀ st,
      TreeSimCheckTimed (2 + n + 1) ((f a b).run st >>= k).run)
    (xs : List β) (a : α) (n : ℕ)
    (k : α × RunState C → PartyM C E RealSpec γ)
    (hk : ∀ p, TreeSimCheckTimed (n + 1) (k p).run) (st : RunState C) :
    TreeSimCheckTimed (2 * xs.length + n + 1) ((xs.foldlM f a).run st >>= k).run := by
  induction xs generalizing a st with
  | nil => simpa only [List.foldlM_nil, StateT.run_pure, pure_bind,
      List.length_nil, Nat.mul_zero, Nat.zero_add] using hk (a, st)
  | cons b xs ih =>
    simp only [List.foldlM_cons, StateT.run_bind, bind_assoc, List.length_cons]
    convert hf a b (2 * xs.length + n) _ (fun p => ih p.1 p.2) st using 1; omega

/-- The actual final reshare, storing the polynomial subsequently checked. -/
def treeLockstepFinalBeforeSalt (ctx : Context C) (p : (ℕ → E) × (ℕ → E) × E) :
    RunM C E RealSpec (E → ℕ → E) := do
  let gadgets := realCheckGadgets K ctx
  let w ← gadgets.randElements 2
  let wa := conv K ctx w.1 0
  let wb := conv K ctx w.1 1
  let q ← gadgets.extendMult [.shamir (fun _ => wa) (fun _ => wb) 1,
    .shamir (fun _ => wa + p.1 0) (fun _ => wb + p.2.1 0) 1]
  let q₀ := conv K ctx q 0
  let q₂ := conv K ctx q 1
  pure fun r k => match k with
    | 0 => wa + r * (wa + p.1 0)
    | 1 => wb + r * (wb + p.2.1 0)
    | _ => q₀ + (p.2.2 + q₀ + q₂) * r + q₂ * r ^ 2

/-- The actual final randomization through its digest exchange. -/
def treeLockstepFinalPrefix (ctx : Context C) (p : (ℕ → E) × (ℕ → E) × E) :
    RunM C E RealSpec (E → ℕ → E) := do
  let polynomial ← treeLockstepFinalBeforeSalt K ctx p
  treeStagesSaltedDigest K ctx
  pure polynomial

theorem treeLockstep_finalBeforeSalt_timed (ctx : Context C)
    (p : (ℕ → E) × (ℕ → E) × E) (st : RunState C) :
    TreeSimCheckTimed 1 ((treeLockstepFinalBeforeSalt K ctx p).run st).run := by
  unfold treeLockstepFinalBeforeSalt
  change TreeSimCheckTimed 1 ((prssRandomness ctx (elementCodec K) 1 2 >>= _).run st).run
  rw [prssRandomness_run]
  apply TreeSimCheckTimed.oracle_bind 0
  intro w
  simp only [StateT.run_bind, StateT.run_pure]
  exact Nat.add_zero 1 ▸ (treeLockstep_timed_extendMult K ctx _ _).bind (fun _ => .done _)

theorem treeLockstep_finalPrefix_timed (ctx : Context C)
    (p : (ℕ → E) × (ℕ → E) × E) (st : RunState C) :
    TreeSimCheckTimed 2 ((treeLockstepFinalPrefix K ctx p).run st).run := by
  simp only [treeLockstepFinalPrefix, treeLockstepFinalBeforeSalt, treeStagesSaltedDigest,
    bind_assoc, pure_bind]
  change TreeSimCheckTimed 2 ((prssRandomness ctx (elementCodec K) 1 2 >>= _).run st).run
  rw [prssRandomness_run]
  apply TreeSimCheckTimed.oracle_bind 1
  intro w
  rw [StateT.run_bind]
  apply (treeLockstep_timed_extendMult K ctx _ _).bind (n := 1)
  intro q
  change TreeSimCheckTimed 1 ((prssRandomness ctx bitCodec 2 256 >>= _).run q.2).run
  rw [prssRandomness_run]
  apply TreeSimCheckTimed.oracle_bind 0
  intro salts
  simp only [StateT.run_bind, StateT.run_pure]
  exact Nat.add_zero 1 ▸ (treeLockstep_timed_digest (E := E) ctx salts.1 _).bind (fun _ => .done _)

/-- The slice and dimension reductions, with the final randomization kept
as their explicit continuation. -/
def treeLockstepCheckPrefixWith {α : Type} (ctx : Context C) (tuples : List (Tuple C))
    (finish : ((ℕ → E) × (ℕ → E) × E) → RunM C E RealSpec α) : RunM C E RealSpec α := do
  let gadgets := realCheckGadgets K ctx
  let count := (tuples.map (·.count)).sum
  let τ ← expand K (← coinKey K gadgets) (coins count)
  StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
  let p ← (List.range sliceBits).foldlM (sliceStep K ctx gadgets τ count)
    ((fun T k => wordWeightOf K τ count k * liftedPart tuples (·.x) T k : Shares C E),
      liftedPart tuples (·.y), conv K ctx (claimOf K τ count (liftedPart tuples (·.z))) 0)
  let p' ← (List.range (halvings count - sliceBits)).foldlM
    (halvingStep K ctx gadgets (sliceWidth count))
    (conv K ctx p.1, conv K ctx p.2.1, p.2.2)
  finish p'

/-- The nonzero tuple check through its digest exchange. -/
def treeLockstepCheckPrefix (ctx : Context C) (tuples : List (Tuple C)) :
    RunM C E RealSpec (E → ℕ → E) :=
  treeLockstepCheckPrefixWith K ctx tuples (treeLockstepFinalPrefix K ctx)

/-- The cut immediately after the final reshare and before the salt draw. -/
def treeLockstepCheckBeforeSalt (ctx : Context C) (tuples : List (Tuple C)) :
    RunM C E RealSpec (E → ℕ → E) :=
  treeLockstepCheckPrefixWith K ctx tuples (treeLockstepFinalBeforeSalt K ctx)

/-- A syntax-level boundary, independent of messages or arithmetic success.
Early aborts remain aborts; every success reaches the same digest exchange. -/
private theorem openedRest_checkPrefixWith_timed {α : Type} (ctx : Context C)
    (tuples : List (Tuple C)) (n : ℕ)
    (finish : ((ℕ → E) × (ℕ → E) × E) → RunM C E RealSpec α)
    (timed : ∀ p st, TreeSimCheckTimed (n + 1) ((finish p).run st).run) (st : RunState C) :
    TreeSimCheckTimed (2 * sliceBits + 2 * (halvings (tuples.map (·.count)).sum - sliceBits) + n + 2)
      ((treeLockstepCheckPrefixWith K ctx tuples finish).run st).run := by
  unfold treeLockstepCheckPrefixWith
  simp only [coinKey, StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind, bind_assoc]
  rw [show 2 * sliceBits + 2 * (halvings (tuples.map (·.count)).sum - sliceBits) + n + 2 =
      1 + (2 * sliceBits + 2 * (halvings (tuples.map (·.count)).sum - sliceBits) + n + 1) by omega]
  apply (treeLockstep_timed_coin K ctx 1 st).bind
  intro coin
  apply TreeSimCheckTimed.oracle_bind
  intro key
  unfold expand
  simp only [StateT.run_lift, bind_assoc, pure_bind]
  apply TreeSimCheckTimed.oracle_bind
  intro τ
  apply openedRest_timed_require
  intro _
  convert openedRest_timed_fold (sliceStep K ctx (realCheckGadgets K ctx) τ _)
    (openedRest_timed_slice K ctx τ _) (List.range sliceBits) _
    (2 * (halvings (tuples.map (·.count)).sum - sliceBits) + n) _ ?_ coin.2 using 1
  · simp only [List.length_range]; omega
  · intro p
    convert openedRest_timed_fold (halvingStep K ctx (realCheckGadgets K ctx) _)
      (openedRest_timed_halving K ctx _) (List.range _) _ n _
      (fun p => timed p.1 p.2) p.2 using 1
    simp only [List.length_range]

theorem treeLockstep_checkPrefix_timed (ctx : Context C) (tuples : List (Tuple C))
    (st : RunState C) :
    TreeSimCheckTimed (2 * sliceBits + 2 * (halvings (tuples.map (·.count)).sum - sliceBits) + 3)
      ((treeLockstepCheckPrefix K ctx tuples).run st).run :=
  openedRest_checkPrefixWith_timed K ctx tuples 1 _ (treeLockstep_finalPrefix_timed K ctx) st

theorem treeLockstep_checkBeforeSalt_timed (ctx : Context C) (tuples : List (Tuple C))
    (st : RunState C) :
    TreeSimCheckTimed (2 * sliceBits + 2 * (halvings (tuples.map (·.count)).sum - sliceBits) + 2)
      ((treeLockstepCheckBeforeSalt K ctx tuples).run st).run :=
  openedRest_checkPrefixWith_timed K ctx tuples 0 _ (treeLockstep_finalBeforeSalt_timed K ctx) st

theorem treeLockstep_checkPrefix_eq (ctx : Context C) (tuples : List (Tuple C)) :
    treeLockstepCheckPrefix K ctx tuples = (do
      let polynomial ← treeLockstepCheckBeforeSalt K ctx tuples
      treeStagesSaltedDigest K ctx
      pure polynomial) := by
  simp only [treeLockstepCheckPrefix, treeLockstepCheckBeforeSalt, treeLockstepCheckPrefixWith,
    treeLockstepFinalPrefix, bind_assoc]

/-- The unchanged post-digest challenge and scalar test. -/
def treeLockstepCheckSuffix (ctx : Context C) (polynomial : E → ℕ → E) :
    RunM C E RealSpec Unit := do
  let r ← challenge K (realCheckGadgets K ctx)
  let opened ← StateT.lift (openSh K ctx (polynomial r) 3)
  StateT.lift (require (opened 0 * opened 1 = opened 2))

theorem treeLockstep_check_eq (ctx : Context C) (tuples : List (Tuple C))
    (nonzero : (tuples.map (·.count)).sum ≠ 0) :
    check K ctx (realCheckGadgets K ctx) tuples =
      treeLockstepCheckPrefix K ctx tuples >>= treeLockstepCheckSuffix K ctx := by
  rw [check_eq K ctx _ tuples nonzero]
  simp only [treeLockstepCheckPrefix, treeLockstepCheckPrefixWith, treeLockstepFinalPrefix,
    treeLockstepFinalBeforeSalt, treeStagesSaltedDigest, treeLockstepCheckSuffix,
    finalStep, bind_assoc, pure_bind]
  rfl

theorem treeLockstep_checkSuffix_exchange {α : Type} (ctx : Context C)
    (polynomial : E → ℕ → E) (st : RunState C)
    (k : Unit × RunState C → PartyM C E RealSpec α) :
    TreeSimCheckExchange ((treeLockstepCheckSuffix K ctx polynomial).run st >>= k) := by
  unfold treeLockstepCheckSuffix challenge coinKey
  simp only [StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind, bind_assoc]
  exact (treeSimCheck_realCoin_exchange K ctx 1 st).bind _

/-- A successful continuation of the actual nonempty check certifies a
shared post-digest scheduler boundary and live honest prefixes. The three
parts retain the single joint replay and its exact log decomposition. -/
theorem treeLockstep_check_replay_split {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (tuples : C.Party → List (Tuple C)) (count : ℕ)
    (counts : ∀ i, ((tuples i).map (·.count)).sum = count) (nonzero : count ≠ 0)
    (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (log : TreeSimLog C) (out : A.State × (C.Party → Option α))
    (run : TreeSimCheckReplay (executePhase worldRoles D A noFunctionality
      (2 * sliceBits + 2 * (halvings count - sliceBits) + 3 + fuel) state
      (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) >>= k i)) log out)
    (accepted : ∃ i value, out.2 i = some value) :
    ∃ pref first next middle last, log = first ++ middle ++ last ∧
      TreeSimCheckReplay (executePhase worldRoles D A noFunctionality
        (2 * sliceBits + 2 * (halvings count - sliceBits) + 3) state
        (fun i => (treeLockstepCheckPrefix K (ctx i) (tuples i)).run (st i))) first pref ∧
      (∀ i, i ∉ D.1 → (pref.2 i).isSome) ∧
      TreeSimCheckReplay (free (Concrete.sequenceFin fun i => continueStep
        (fun p => (treeLockstepCheckSuffix K (ctx i) p.1).run p.2 >>= k i)
        (.done (pref.2 i)))) middle next ∧
      TreeSimCheckReplay (executeRounds worldRoles D A noFunctionality fuel pref.1 next) last out := by
  have hn (i) : ((tuples i).map (·.count)).sum ≠ 0 := by rw [counts i]; exact nonzero
  simp only [treeLockstep_check_eq K _ _ (hn _), StateT.run_bind, bind_assoc] at run
  apply treeSimCheckTimed_phase_replay_live D A
    (2 * sliceBits + 2 * (halvings count - sliceBits) + 2) fuel state _ _ ?_ ?_ log out run accepted
  · intro i
    simpa only [counts i] using treeLockstep_checkPrefix_timed K (ctx i) (tuples i) (st i)
  · intro i p
    exact treeLockstep_checkSuffix_exchange K (ctx i) p.1 p.2 (k i)

end Timing

section SaltedBoundary
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

-- Polymorphic versions of TreeSimStages' same-named TreeOutput lemmas.
-- The audited continuation returns TreeOutput together with its records.
theorem treeLockstep_saltedDigest_factor {α : Type} (ctx : Context C) (st : RunState C)
    (k : Unit × RunState C → PartyM C E RealSpec α) :
    free (advance (((treeStagesSaltedDigest K ctx).run st >>= k).run)) =
      (free (liftComp (prssDraw ctx (bitCodec (E := E)) st.label 2 256) (LocalSpec C)) >>= fun salts =>
        free (advance (((compareDigests ctx salts.1).run (nextLabel st) >>= k).run))) := by
  unfold treeStagesSaltedDigest
  change free (advance ((((prssRandomness ctx (bitCodec (E := E)) 2 256 >>= fun salts =>
    compareDigests ctx salts.1).run st) >>= k).run)) = _
  rw [prssRandomness_run, bind_assoc]
  simp only [advance_oracleStep_bind, free_bind]

theorem treeLockstep_saltedDigest_partial_log {α : Type} (D : C.Coalition) (live : C.Party → Bool)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll
      (fun i (_ : Unit) => (treeStagesSaltedDigest K (ctx i)).run (st i) >>= k i)
      (fun i => if i ∈ D.1 then none else if live i then some () else none))).run s)) :
    ∃ ds, r.1 = treeSimCheckWaiting K D live (.digests ds) (fun i => k i ((), nextLabel (st i))) ∧
      ∀ i, i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T → ∃ salt h d,
        TreeSimHashAnswer r.2.2 (.history ((st i).history T)) h ∧
        TreeSimHashAnswer r.2.2 (.digest salt h) d ∧ (ds i)[C.terms.idxOf T]? = some d := by
  let P := fun i (v : Step C E RealSpec α) (log : TreeSimLog C) => ∃ ds,
    v = treeSimCheckWaiting K D live (.digests (fun _ => ds)) (fun j => k j ((), nextLabel (st j))) i ∧
    (i ∉ D.1 → live i = true → ∀ T, i ∈ C.holders T → ∃ salt h d,
      TreeSimHashAnswer log (.history ((st i).history T)) h ∧
      TreeSimHashAnswer log (.digest salt h) d ∧ ds[C.terms.idxOf T]? = some d)
  have certificates : ∀ i, P i (r.1 i) r.2.2 := by
    apply treeStages_resumeAll_log prims D _ _ P _ _ s r hr
    · intro i v l l' hpref hp
      obtain ⟨ds, hv, hc⟩ := hp
      refine ⟨ds, hv, ?_⟩
      intro hi hl T held
      obtain ⟨salt, h, d, hh, hd, idx⟩ := hc hi hl T held
      exact ⟨salt, h, d, treeStages_hashAnswer_mono hpref _ _ hh,
        treeStages_hashAnswer_mono hpref _ _ hd, idx⟩
    · intro i a u hu
      by_cases hi : i ∈ D.1
      · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
          support_pure, Set.mem_singleton_iff] at hu
        subst u
        exact ⟨[], by simp [treeSimCheckWaiting, hi], fun hn => (hn hi).elim⟩
      · simp only [if_neg hi] at hu
        by_cases hl : live i = true
        · simp only [if_pos hl, treeSimResume, treeLockstep_saltedDigest_factor,
            simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hu
          obtain ⟨rnd, hrnd, hu⟩ := hu
          change u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
            (worldRoles.honest (advance (((compareDigests (ctx i) rnd.1.1).run
              (nextLabel (st i)) >>= k i).run)))).run rnd.2) at hu
          rw [treeSim_digest_entry (K := K), self i hi] at hu
          simp only [simulateQ_map, StateT.run_map, support_map] at hu
          obtain ⟨v, hv, rfl⟩ := hu
          refine ⟨v.1, by simp [treeSimCheckWaiting, hi, hl], ?_⟩
          intro _ _ T held
          obtain ⟨h, d, hh, hd, idx⟩ := treeStages_digestQuery_log prims D i rnd.1.1
            (nextLabel (st i)).history rnd.2 v hv T held
          exact ⟨vector 256 (rnd.1.1 T), h, d, hh, hd, idx⟩
        · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
            support_pure, Set.mem_singleton_iff] at hu
          subst u
          exact ⟨[], by simp [treeSimCheckWaiting, hi, hl], fun _ hh => (hl hh).elim⟩
  choose ds steps cert using certificates
  exact ⟨ds, funext steps, cert⟩

private theorem openedRest_resume_none {α β : Type} (D : C.Coalition) (k : C.Party → β → PartyM C E RealSpec α)
    (out : C.Party → Option β) (s : TreeSimState C)
    (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k out)).run s)) :
    ∀ i, out i = none → r.1 i = .done none := by
  apply treeStages_resumeAll_log prims D k out
    (fun i step _ => out i = none → step = .done none) (fun _ _ _ _ _ h => h) ?_ s r run
  intro i cache next hnext hn
  rw [hn] at hnext
  simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
    mem_support_pure_iff] at hnext
  exact congrArg Prod.fst hnext

/-- The actual sampled-salt and digest round, with an arbitrary audited continuation. -/
theorem treeLockstep_saltedDigest_round_histories {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (live : C.Party → Bool)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C)
    (r : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (do
      let waiting ← treeSimResumeAll
        (fun i (_ : Unit) => (treeStagesSaltedDigest K (ctx i)).run (st i) >>= k i)
        (fun i => if i ∈ D.1 then none else if live i then some () else none)
      stepRound worldRoles D A noFunctionality state waiting)).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2)
    (survives : ∃ i, r.1.2.1 i ≠ .done none) :
    ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (st i).history T = (st j).history T := by
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨before, hbefore, hround⟩ := run
  obtain ⟨ds, waiting, recorded⟩ :=
    treeLockstep_saltedDigest_partial_log prims K D live ctx self st k s before hbefore
  rw [waiting, treeSim_check_round_factor] at hround
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    mem_support_bind_iff, mem_support_pure_iff] at hround
  obtain ⟨adv, hadv, next, hnext, rfl⟩ := hround
  obtain ⟨i, hi⟩ := survives
  have passed : treeSimCheckResult K D live (.digests ds) adv.1.2 i = some () := by
    have hn := openedRest_resume_none prims D _ _ adv.2 next hnext i
    cases he : treeSimCheckResult K D live (.digests ds) adv.1.2 i with
    | none => exact (hi (hn he)).elim
    | some u => cases u; rfl
  apply treeLockstep_digest_accepted_histories K D live (fun i => (st i).history) ds next.2.2
    ?_ good adv.1.2 i passed
  have grows := ((treeSimLoggedWorld_prefix prims D _ before.2 adv hadv).trans
    (treeSimLoggedWorld_prefix prims D _ adv.2 next hnext)).subset
  intro h hh hl T hT
  obtain ⟨salt, hist, digest, hh', hd, idx⟩ := recorded h hh hl T hT
  exact ⟨salt, hist, digest, hh'.imp (fun h => grows h) (fun h => grows h),
    hd.imp (fun h => grows h) (fun h => grows h), idx⟩

/-- Prefix certificates extend to any surviving suffix of the actual
sampled-salt phase, including arbitrary later batches and selective aborts. -/
theorem treeLockstep_saltedDigest_phase_histories {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (fuel + 1) state
        (fun i => (treeStagesSaltedDigest K (ctx i)).run (st i) >>= k i))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2)
    (accepted : ∃ i value, r.1.2 i = some value) :
    ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (st i).history T = (st j).history T := by
  let resume := fun i (_ : Unit) => (treeStagesSaltedDigest K (ctx i)).run (st i) >>= k i
  let active := fun i => if i ∈ D.1 then none else if true then some () else none
  have start : startSteps worldRoles D (fun i => (treeStagesSaltedDigest K (ctx i)).run (st i) >>= k i) =
      treeSimResumeAll resume active := by
    unfold startSteps treeSimResumeAll
    rw [free_sequenceFin]
    congr 1
    funext i
    by_cases hi : i ∈ D.1 <;> simp [resume, active, hi, treeSimResume, worldRoles, free_pure]
  unfold executePhase at run
  rw [start] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨before, hbefore, hrest⟩ := run
  obtain ⟨ds, waiting, _⟩ := treeLockstep_saltedDigest_partial_log prims K D (fun _ => true)
    ctx self st k s before hbefore
  have running : ¬ ∀ i, i ∉ D.1 → (before.1 i).isDone := by
    intro h
    obtain ⟨i, hi⟩ := coalition_has_honest D
    simpa [waiting, treeSimCheckWaiting, treeSimCheckStep, hi, Step.isDone] using h i hi
  rw [executeRounds, if_neg running] at hrest
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hrest
  obtain ⟨next, hnext, htail⟩ := hrest
  have survives : ∃ i, next.1.2.1 i ≠ .done none := by
    by_contra! stopped
    have he : next.1.2.1 = fun _ => .done none := funext stopped
    rw [he, executeRounds_all_none] at htail
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at htail
    subst r
    obtain ⟨i, value, hi⟩ := accepted
    cases hi
  have hpref := (treeSimLoggedWorld_prefix prims D _ next.2 r htail).subset
  apply treeLockstep_saltedDigest_round_histories prims K D A state (fun _ => true) ctx self st k
    s next ?_ ?_ survives
  · simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    exact ⟨before, hbefore, hnext⟩
  · intro bad
    obtain ⟨q, q', h, hq, hq', ne, a, b⟩ := bad
    exact good ⟨q, q', h, hq, hq', ne,
      a.imp (fun h => hpref h) (fun h => hpref h),
      b.imp (fun h => hpref h) (fun h => hpref h)⟩

end SaltedBoundary

section ReachedCheck
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

private theorem openedRest_support {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (s : TreeSimState C) (r : α × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    r.1 ∈ support p := by
  apply support_simulateQ_run'_subset (treeSimLoggedWorld prims D) p s
  rw [StateT.run'_eq, support_map]
  exact ⟨r, hr, rfl⟩

private theorem openedRest_salted_exchange {α : Type} (ctx : Context C) (st : RunState C)
    (k : Unit × RunState C → PartyM C E RealSpec α) :
    TreeSimCheckExchange ((treeStagesSaltedDigest K ctx).run st >>= k) := by
  unfold treeStagesSaltedDigest
  change TreeSimCheckExchange ((prssRandomness ctx bitCodec 2 256 >>= _).run st >>= k)
  rw [prssRandomness_run, bind_assoc]
  apply TreeSimCheckExchange.oracle_bind
  intro salts
  rw [compareDigests_run, bind_assoc]
  apply TreeSimCheckExchange.oracle_bind
  intro ds
  rw [bind_assoc]
  exact TreeSimCheckExchange.exchange_bind _ _

private theorem openedRest_resume_start {α β : Type} (D : C.Coalition)
    (k : C.Party → β → PartyM C E RealSpec α) (out : C.Party → Option β) (data : C.Party → β)
    (corrupt : ∀ i, i ∈ D.1 → out i = none)
    (honest : ∀ i, i ∉ D.1 → out i = some (data i)) :
    free (Concrete.sequenceFin fun i => continueStep (k i) (.done (out i))) =
      startSteps worldRoles D (fun i => k i (data i)) := by
  unfold startSteps
  rw [free_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi, corrupt i hi, continueStep, free_pure]
  · simp [hi, honest i hi, continueStep, worldRoles]

/-- The nonempty real check reaches one actual pre-salt state vector. Any
successful audited continuation forces its honest held histories to agree.
The prefix cache and the whole remaining execution are retained together. -/
theorem treeLockstep_check_beforeSalt_boundary {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (tuples : C.Party → List (Tuple C)) (count : ℕ)
    (counts : ∀ i, ((tuples i).map (·.count)).sum = count) (nonzero : count ≠ 0)
    (st : C.Party → RunState C)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (2 * sliceBits + 2 * (halvings count - sliceBits) + 2 + (fuel + 1)) state
        (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) >>= k i))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2)
    (accepted : ∃ i value, r.1.2 i = some value) :
    ∃ (pref : (A.State × (C.Party → Option ((E → ℕ → E) × RunState C))) × TreeSimState C)
      (data : C.Party → (E → ℕ → E) × RunState C),
      pref ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality
          (2 * sliceBits + 2 * (halvings count - sliceBits) + 2) state
          (fun i => (treeLockstepCheckBeforeSalt K (ctx i) (tuples i)).run (st i)))).run s) ∧
      (∀ i, i ∉ D.1 → pref.1.2 i = some (data i)) ∧
      (∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
        (data i).2.history T = (data j).2.history T) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (executePhase worldRoles D A noFunctionality (fuel + 1) pref.1.1
          (fun i => (treeStagesSaltedDigest K (ctx i)).run (data i).2 >>= fun p =>
            (treeLockstepCheckSuffix K (ctx i) (data i).1).run p.2 >>= k i))).run pref.2) := by
  let cont := fun i (p : (E → ℕ → E) × RunState C) =>
    (treeStagesSaltedDigest K (ctx i)).run p.2 >>= fun q =>
      (treeLockstepCheckSuffix K (ctx i) p.1).run q.2 >>= k i
  have hn (i) : ((tuples i).map (·.count)).sum ≠ 0 := by rw [counts i]; exact nonzero
  simp only [treeLockstep_check_eq K _ _ (hn _), treeLockstep_checkPrefix_eq,
    StateT.run_bind, bind_assoc, pure_bind] at run
  rw [treeSimCheckTimed_phase_split D A
    (2 * sliceBits + 2 * (halvings count - sliceBits) + 1) (fuel + 1) state
    (fun i => (treeLockstepCheckBeforeSalt K (ctx i) (tuples i)).run (st i)) cont
    (fun i => by simpa only [counts i] using treeLockstep_checkBeforeSalt_timed K (ctx i) (tuples i) (st i))] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨pref, hpref, next, hnext, htail⟩ := run
  have live := treeSimCheck_exchange_continuations_live D A (fuel + 1) pref.1.1 pref.1.2 cont
    (fun i p => openedRest_salted_exchange K (ctx i) p.2 _) next.1
    (openedRest_support prims D _ _ _ hnext) r.1 (openedRest_support prims D _ _ _ htail) accepted
  let data := fun i => (pref.1.2 i).getD (0, st i)
  have hd (i) (hi : i ∉ D.1) : pref.1.2 i = some (data i) := by
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (live i hi)
    simp [data, hp]
  have corrupt := treeStages_phase_corrupt (treeSimLoggedWorld prims D) D A
    (2 * sliceBits + 2 * (halvings count - sliceBits) + 2) state
    (fun i => (treeLockstepCheckBeforeSalt K (ctx i) (tuples i)).run (st i)) s pref
    (by simpa only [simulateQ_executePhase] using hpref)
  have hstart := openedRest_resume_start D cont pref.1.2 data corrupt hd
  have suffix : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality (fuel + 1) pref.1.1
        (fun i => cont i (data i)))).run pref.2) := by
    unfold executePhase
    rw [← hstart]
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff]
    exact ⟨next, hnext, htail⟩
  refine ⟨pref, data, hpref, hd, ?_, suffix⟩
  exact treeLockstep_saltedDigest_phase_histories prims K D A fuel pref.1.1 ctx self
    (fun i => (data i).2) _ pref.2 r suffix good accepted

end ReachedCheck

section History
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

private def OpenedRestHistory {α : Type} (p : RunM C E RealSpec α) : Prop :=
  ∀ st value final, some (value, final) ∈ support (p.run st).run →
    ∀ T, st.history T <+: final.history T

private theorem OpenedRestHistory.pure {α : Type} (a : α) :
    OpenedRestHistory (C := C) (E := E) (pure a) := by
  intro st value final h T
  have he : (value, final) = (a, st) := by simpa using h
  cases he
  exact List.prefix_refl _

private theorem OpenedRestHistory.lift {α : Type} (p : PartyM C E RealSpec α) :
    OpenedRestHistory (StateT.lift p) := by
  intro st value final h T
  simp only [StateT.run_lift] at h
  obtain ⟨a, _, h⟩ := treeSimCheck_some_bind _ _ _ h
  have he : (value, final) = (a, st) := by simpa using h
  cases he
  exact List.prefix_refl _

private theorem OpenedRestHistory.get :
    OpenedRestHistory (get : RunM C E RealSpec (RunState C)) := by
  intro st value final h T
  have he : (value, final) = (st, st) := by simpa only [StateT.run_get,
    OptionT.run_pure, mem_support_pure_iff, Option.some.injEq] using h
  cases he
  exact List.prefix_refl _

private theorem OpenedRestHistory.bind {α β : Type}
    {p : RunM C E RealSpec α} {k : α → RunM C E RealSpec β}
    (hp : OpenedRestHistory p) (hk : ∀ a, OpenedRestHistory (k a)) :
    OpenedRestHistory (p >>= k) := by
  intro st value final h T
  rw [StateT.run_bind] at h
  obtain ⟨⟨a, mid⟩, ha, hb⟩ := treeSimCheck_some_bind _ _ _ h
  exact (hp st a mid ha T).trans (hk a mid value final hb T)

private theorem OpenedRestHistory.fold {α β : Type} (f : α → β → RunM C E RealSpec α)
    (hf : ∀ a b, OpenedRestHistory (f a b)) (xs : List β) (a : α) :
    OpenedRestHistory (xs.foldlM f a) := by
  induction xs generalizing a with
  | nil => exact .pure _
  | cons b xs ih => exact (hf a b).bind ih

private theorem openedRest_rand_history {R : Type} [Zero R]
    (ctx : Context C) (codec : Codec C E R) (idx count : ℕ) :
    OpenedRestHistory (prssRandomness ctx codec idx count) := by
  intro st value final h T
  rw [realRand_run] at h
  obtain ⟨a, _, h⟩ := treeSimCheck_some_bind _ _ _ h
  have he : (value, final) = (a, nextLabel st) := by simpa using h
  cases he
  exact List.prefix_refl _

private theorem openedRest_coin_history (ctx : Context C) (count : ℕ) :
    OpenedRestHistory ((realCheckGadgets K ctx).coin count) := by
  intro st value final h T
  rw [realCoin_run] at h
  obtain ⟨a, _, h⟩ := treeSimCheck_some_bind _ _ _ h
  obtain ⟨opened, _, h⟩ := treeSimCheck_some_bind _ _ _ h
  have he : (value, final) = (vector count opened, nextLabel st) := by simpa using h
  cases he
  exact List.prefix_refl _

private theorem openedRest_extend_history (ctx : Context C) (products : List (Product C E)) :
    OpenedRestHistory ((realCheckGadgets K ctx).extendMult products) := by
  intro st value final h T
  rw [realExtendMult_run] at h
  obtain ⟨a, _, h⟩ := treeSimCheck_some_bind _ _ _ h
  obtain ⟨inbox, _, h⟩ := treeSimCheck_some_bind _ _ _ h
  simp only [OptionT.run_pure, mem_support_pure_iff, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  dsimp only
  unfold recordPeer
  split_ifs
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

private theorem openedRest_coinKey_history (ctx : Context C) :
    OpenedRestHistory (coinKey K (realCheckGadgets K ctx)) := by
  exact OpenedRestHistory.get.bind fun _ => (openedRest_coin_history K ctx 1).bind
    fun _ => .lift _

private theorem openedRest_challenge_history (ctx : Context C) :
    OpenedRestHistory (challenge K (realCheckGadgets K ctx)) := by
  apply (openedRest_coinKey_history K ctx).bind
  intro key
  apply (OpenedRestHistory.lift (oracleStep (findChallenge K key challengeTries 0))).bind
  intro r
  cases r
  · exact .lift _
  · exact .pure _

private theorem openedRest_slice_history (ctx : Context C) (τ : List E) (count : ℕ)
    (p : Shares C E × Shares C E × E) (j : ℕ) :
    OpenedRestHistory (sliceStep K ctx (realCheckGadgets K ctx) τ count p j) := by
  rcases p with ⟨x, y, d⟩
  exact (openedRest_extend_history K ctx _).bind fun _ =>
    (openedRest_challenge_history K ctx).bind fun _ => .pure _

private theorem openedRest_halving_history (ctx : Context C) (width : ℕ)
    (p : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    OpenedRestHistory (halvingStep K ctx (realCheckGadgets K ctx) width p j) := by
  rcases p with ⟨x, y, d⟩
  exact (openedRest_extend_history K ctx _).bind fun _ =>
    (openedRest_challenge_history K ctx).bind fun _ => .pure _

private theorem openedRest_finalBeforeSalt_history (ctx : Context C)
    (p : (ℕ → E) × (ℕ → E) × E) :
    OpenedRestHistory (treeLockstepFinalBeforeSalt K ctx p) := by
  exact (openedRest_rand_history ctx (elementCodec K) 1 2).bind fun _ =>
    (openedRest_extend_history K ctx _).bind fun _ => .pure _

/-- Every pre-salt history retains the complete checkpoint history as a
prefix. The proof permits arbitrary successful local oracle/network replies. -/
theorem treeLockstep_checkBeforeSalt_history (ctx : Context C) (tuples : List (Tuple C))
    (st : RunState C) (value : E → ℕ → E) (final : RunState C)
    (run : some (value, final) ∈ support ((treeLockstepCheckBeforeSalt K ctx tuples).run st).run) :
    ∀ T, st.history T <+: final.history T := by
  have invariant : OpenedRestHistory (treeLockstepCheckBeforeSalt K ctx tuples) := by
    apply (openedRest_coinKey_history K ctx).bind
    intro key
    apply (OpenedRestHistory.lift (oracleStep _)).bind
    intro τ
    apply (OpenedRestHistory.lift (require _)).bind
    intro _
    apply (OpenedRestHistory.fold _ (openedRest_slice_history K ctx τ _) _ _).bind
    intro p
    exact (OpenedRestHistory.fold _ (openedRest_halving_history K ctx _) _ _).bind
      (openedRest_finalBeforeSalt_history K ctx)
  exact invariant st value final run

end History

section AgreedCheckpoint
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

/-- Agreement at the digest forces agreement of the initial checkpoint
histories. This uses the actual joint check and its arbitrary continuation;
the sole length hypothesis is independent of the stored tuple values. -/
theorem treeLockstep_check_history_agreement {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (tuples : C.Party → List (Tuple C)) (count : ℕ)
    (counts : ∀ i, ((tuples i).map (·.count)).sum = count) (nonzero : count ≠ 0)
    (st : C.Party → RunState C)
    (lengths : ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      ((st i).history T).length = ((st j).history T).length)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (2 * sliceBits + 2 * (halvings count - sliceBits) + 2 + (fuel + 1)) state
        (fun i => (check K (ctx i) (realCheckGadgets K (ctx i)) (tuples i)).run (st i) >>= k i))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) (accepted : ∃ i value, r.1.2 i = some value) :
    ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (st i).history T = (st j).history T := by
  obtain ⟨pref, data, hpref, hd, agreement, _⟩ := treeLockstep_check_beforeSalt_boundary prims K
    D A fuel state ctx self tuples count counts nonzero st k s r run good accepted
  obtain ⟨log, replay⟩ := treeSimCheckReplay_of_support _ pref.1 (openedRest_support prims D _ _ _ hpref)
  have retained (i : C.Party) (hi : i ∉ D.1) :
      ∀ T, (st i).history T <+: (data i).2.history T := by
    obtain ⟨_, localRun, _⟩ := treeSimCheck_phase_replay D A noFunctionality (fun _ _ => True)
      (2 * sliceBits + 2 * (halvings count - sliceBits) + 2) state _ pref.1
      ⟨log, replay, fun _ _ _ => trivial⟩ i hi (data i) (hd i hi)
    exact treeLockstep_checkBeforeSalt_history K (ctx i) (tuples i) (st i)
      (data i).1 (data i).2 localRun.mem_support
  intro T i j hi hj hiT hjT
  obtain ⟨left, hleft⟩ := retained i hi T
  obtain ⟨right, hright⟩ := retained j hj T
  exact List.append_inj_left (hleft.trans ((agreement T i j hi hj hiT hjT).trans hright.symm))
    (lengths T i j hi hj hiT hjT)

end AgreedCheckpoint

section CheckedCopies
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

/-- The complete transfer from an actually accepted check to the saved
rerandomized copies. Initial arithmetic products and corrupt inboxes may be
arbitrary. The unfilled-copy premise names precisely the PRSS values that
the actual rerandomization must have read from one shared cache. -/
theorem treeLockstep_checked_rerand_held {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (before : C.Party → List (Tuple C)) (input v masks : C.Party → Shares C Bit)
    (width : ℕ) (layerCounts : List ℕ) (layerModes : List ReshareMode)
    (hc : ∀ i, (before i).map (·.count) = layerCounts)
    (hm : ∀ i, (before i).map (·.mode) = layerModes)
    (st : C.Party → RunState C)
    (history : ∀ i, i ∉ D.1 → (st i).history =
      recordMode K .peer i (filledHistory K i (before i)) (v i) width)
    (keys : Consistent D (fun i T => (ctx i).prss.term T)) (label : ℕ)
    (hash : HashCache C) (cache : HiddenCache C)
    (ready : ∀ i T, i ∉ D.1 → i ∈ C.holders T → T ∉ filledTerms K →
      TreeSimStreamReady prims D (.term T) ((ctx i).prss.term T) label 0 width (masks i T) hash cache)
    (unfilled : ∀ i T g, i ∉ D.1 → i ∈ C.holders T → T ∉ filledTerms K →
      g < width → v i T g = masks i T g)
    (k : C.Party → Unit × RunState C → PartyM C E RealSpec α)
    (s : TreeSimState C) (r : (A.State × (C.Party → Option α)) × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (executePhase worldRoles D A noFunctionality
        (2 * sliceBits + 2 * (halvings (layerCounts.sum + width) - sliceBits) + 2 + (fuel + 1)) state
        (fun i => (check K (ctx i) (realCheckGadgets K (ctx i))
          (before i ++ [⟨input i, one K, v i, width, .peer⟩])).run (st i) >>= k i))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) (accepted : ∃ i value, r.1.2 i = some value) :
    ∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < width → v i T g = v (refHolder D T) T g := by
  by_cases empty : width = 0
  · subst width
    intro i T g hi hiT hg
    omega
  have lengths : ∀ T i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
      (filledHistory K i (before i) T).length = (filledHistory K j (before j) T).length := by
    intro T i j _ _ hiT hjT
    exact treeLockstep_filledHistory_length K i j T hiT hjT _ _ ((hc i).trans (hc j).symm)
      ((hm i).trans (hm j).symm)
  have checkpointLengths : ∀ T i j, i ∉ D.1 → j ∉ D.1 →
      i ∈ C.holders T → j ∈ C.holders T → ((st i).history T).length = ((st j).history T).length := by
    intro T i j hi hj hiT hjT
    rw [history i hi, history j hj,
      treeSimCheck_record_history K .peer i (before i) (input i) (one K),
      treeSimCheck_record_history K .peer j (before j) (input j) (one K)]
    apply treeLockstep_filledHistory_length K i j T hiT hjT
    · simp only [List.map_append, List.map_cons, List.map_nil, hc]
    · simp only [List.map_append, List.map_cons, List.map_nil, hm]
  have fullcounts (i : C.Party) : ((before i ++ [(⟨input i, one K, v i, width, .peer⟩ : Tuple C)]).map Tuple.count).sum =
      layerCounts.sum + width := by
    simp only [List.map_append, List.map_cons, List.map_nil, hc i, List.sum_append,
      List.sum_cons, List.sum_nil, Nat.add_zero]
  have histories := treeLockstep_check_history_agreement prims K D A fuel state ctx self
    (fun i => before i ++ [(⟨input i, one K, v i, width, .peer⟩ : Tuple C)])
    (layerCounts.sum + width) fullcounts (by omega) st checkpointLengths k s r run good accepted
  apply treeLockstep_rerand_held K prims D ctx label width masks v hash cache keys ready unfilled
    (fun i => filledHistory K i (before i)) (fun _ _ => []) lengths
  intro T i j hi hj hiT hjT
  simpa only [history i hi, history j hj, List.append_nil] using histories T i j hi hj hiT hjT

/-- In the actual peer reshare, an unfilled held output is exactly its PRSS
mask. This includes the protocol's finite-index and holder restrictions. -/
theorem treeLockstep_reshare_unfilled (ctx : Context C) (rnd : PrssOutput C Bit)
    (input : ℕ → Bit) (count : ℕ) (inbox : Mail C E) (T : C.Term) (g : ℕ)
    (held : ctx.self ∈ C.holders T) (unfilled : T ∉ filledTerms K) (inside : g < count) :
    reshareZ K ctx (bitCodec (E := E)) rnd.1 rnd.2 input count inbox T g = rnd.1 T g := by
  simp [reshareZ, held, Nat.not_le.mpr inside, unfilled]

end CheckedCopies

section SavedOpening
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

-- The TreeSim opening factorization with a general audited return type.
theorem treeLockstep_open_local_factor {α : Type} (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    free (roundLocal D (treeSimOpenPartial K D live count v ds k) sent i) = (do
      let out ← free (liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C))
      free (treeSimResume (k i) out)) := by
  have inbox : (fun j => if j ∈ D.1 then sent j i else
      (treeSimOpenPartial K D live count v ds k j).delivered i) =
      treeSimOpenInbox K D live count v ds sent i := by
    funext j
    by_cases hj : j ∈ D.1 <;> by_cases hl : live j = true <;>
      simp [treeSimOpenPartial, treeSimOpenStep, treeSimOpenInbox, Step.delivered, hj, hl]
  by_cases hi : i ∈ D.1
  · simp [roundLocal, treeSimOpenHead, treeSimOpenPartial, hi, treeSimResume,
      free_pure]
  · by_cases hl : live i = true
    · simp only [roundLocal, if_neg hi, treeSimOpenPartial, if_pos hl, treeSimOpenStep]
      simp only [treeSimOpenPartial, treeSimOpenStep] at inbox
      rw [inbox]
      unfold treeSimOpenHead
      rw [if_neg hi, if_pos hl]
      unfold exchangeResume anyAbort
      dsimp only
      split_ifs with habort
      · rfl
      · simp only [advance_oracleStep_bind, free_bind, liftComp_bind, liftComp_pure, free_pure,
          bind_assoc, pure_bind]
        apply bind_congr
        intro copyDigests
        unfold require
        split_ifs <;> simp [treeSimResume, pure_bind, free_pure]
        rfl
    · simp [roundLocal, treeSimOpenPartial, treeSimOpenHead, hi, hl,
        treeSimResume, free_pure]

/-- A surviving audited opening continuation receives the common finite
opened vector. The intermediate state is the actual head result and the
continuation runs from that same cache and log, in the scheduler's order. -/
theorem treeLockstep_open_saved_value {α : Type} (D : C.Coalition) (live : C.Party → Bool)
    (count : ℕ) (v : C.Party → Shares C Bit) (V : Shares C Bit)
    (held : ∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < count → v i T g = V T g)
    (ds : C.Party → List HashOutput)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α) (sent : C.Party → Mail C E) (i : C.Party)
    (s : TreeSimState C) (r : Step C E RealSpec α × TreeSimState C)
    (hashes : ∀ h, h ∉ D.1 → live h = true →
      (ds h).length = C.terms.length ∧ ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer s.2 (.copy (vector count (v h T))) u)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (roundLocal D (treeSimOpenPartial K D live count v ds k) sent i))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) (survives : r.1 ≠ .done none) :
    ∃ out mid,
      (some out, mid) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C)))).run s) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free (advance (k i out).run))).run mid) ∧
      ∀ g < count, out g = shareValue V g := by
  rw [treeLockstep_open_local_factor] at run
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨⟨out, mid⟩, hhead, hrest⟩ := run
  cases out with
  | none =>
    simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at hrest
    exact (survives (congrArg Prod.fst hrest)).elim
  | some out =>
    refine ⟨out, mid, hhead, hrest, ?_⟩
    apply treeLockstep_open_head_value prims K D live count v V held ds sent i s mid out hashes hhead
    have hpref := (treeSimLoggedWorld_prefix prims D _ mid r hrest).subset
    rintro ⟨q, q', h, hq, hq', ne, a, b⟩
    exact good ⟨q, q', h, hq, hq', ne,
      a.imp (fun h => hpref h) (fun h => hpref h),
      b.imp (fun h => hpref h) (fun h => hpref h)⟩

end SavedOpening

section BatchOutput
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

theorem treeLockstep_assemble_congr (jobs : List Circuit) (a b : ℕ → Bit)
    (eq : ∀ g < (outputsOf jobs).length, a g = b g) : assemble jobs a = assemble jobs b := by
  unfold assemble
  refine List.ext_getElem (by simp) fun k hk _ => ?_
  simp only [List.length_map, List.length_zipIdx] at hk
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  refine List.ext_getElem (by simp [vector]) fun g hg _ => ?_
  simp only [vector, List.getElem_map, List.getElem_range, List.length_map] at hg ⊢
  apply eq
  have hoff : ((jobs.map (·.outputs)).take k).map List.length =
      (jobs.map (·.outputs.length)).take k := by simp [List.map_take]; rfl
  have hget := getElem?_flatIdx (jobs.map (·.outputs)) 0 k g (by simpa using hk) (by simpa using hg)
  rw [hoff, ← outputsOf_eq] at hget
  by_contra hn
  rw [List.getElem?_eq_none (by omega)] at hget
  cases hget

/-- The next audited batch computation receives one canonical list of job
outputs. This is the original continuation in its actual post-opening state. -/
theorem treeLockstep_open_saved_outputs {α : Type} (D : C.Coalition) (live : C.Party → Bool)
    (jobs : List Circuit) (v : C.Party → Shares C Bit) (V : Shares C Bit)
    (held : ∀ i T g, i ∉ D.1 → i ∈ C.holders T → g < (outputsOf jobs).length → v i T g = V T g)
    (ds : C.Party → List HashOutput)
    (k : C.Party → List (List Bit) → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) (s : TreeSimState C)
    (r : Step C E RealSpec α × TreeSimState C)
    (hashes : ∀ h, h ∉ D.1 → live h = true →
      (ds h).length = C.terms.length ∧ ∀ T, ∃ u, (ds h)[C.terms.idxOf T]? = some u ∧
        TreeSimHashAnswer s.2 (.copy (vector (outputsOf jobs).length (v h T))) u)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (roundLocal D (treeSimOpenPartial K D live (outputsOf jobs).length v ds
        (fun i out => k i (assemble jobs out))) sent i))).run s))
    (good : ¬ TreeSimHashBudgetCollision r.2.2) (survives : r.1 ≠ .done none) :
    ∃ out mid,
      (some out, mid) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (treeSimOpenHead K D live (outputsOf jobs).length v ds sent i)
          (LocalSpec C)))).run s) ∧
      assemble jobs out = assemble jobs (shareValue V) ∧
      r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (free (advance (k i (assemble jobs (shareValue V))).run))).run mid) := by
  obtain ⟨out, mid, hhead, hrest, common⟩ := treeLockstep_open_saved_value prims K D live
    (outputsOf jobs).length v V held ds (fun i out => k i (assemble jobs out)) sent i s r
    hashes run good survives
  have he := treeLockstep_assemble_congr jobs out (shareValue V) common
  exact ⟨out, mid, hhead, he, by simpa only [he] using hrest⟩

end BatchOutput

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_batchPrefix_rerand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_batchPrefix_rerand

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_checkPrefix_timed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_checkPrefix_timed

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_check_replay_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_check_replay_split

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_saltedDigest_round_histories' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_saltedDigest_round_histories

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_check_beforeSalt_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_check_beforeSalt_boundary

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_check_history_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_check_history_agreement

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_checked_rerand_held' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_checked_rerand_held

/-- info: 'ThresholdLeanXmssSecurity.treeLockstep_open_saved_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstep_open_saved_outputs

end ThresholdLeanXmssSecurity
