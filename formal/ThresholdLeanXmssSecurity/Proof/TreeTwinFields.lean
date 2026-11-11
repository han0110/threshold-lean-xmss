import ThresholdLeanXmssSecurity.Proof.TreeStagesRelation

/-!
# The fields of the twin relation

`TreeStagesRelation.lean` reduces `TreeSimStagesGoal2` to `TreeStagesTwinRelation`. This file
proves the fields that do not need stage data, and it names the others as `Prop`s.

* `TreeTwinWithin n p` states that the program `p` makes at most `n` exchanges, for every inbox.
* `treeTwinAfterSetupWithin` bounds the honest program after the PRSS setup by
  `ceremonyBatches * maxBatch (runRounds mode)`. Each batch makes at most `batchRounds` exchanges.
* `treeTwin_progress` proves the field `progress` from this bound.
* `treeTwin_freeHit` proves the field `freeHit` from `TreeTwinDigestDrawnGoal`. This goal states
  that each honest digest call of a round hashes a salt that the same round draws, at an address
  that holds no earlier hidden salt. Then a hit on a swapped salt is `TreeSimSaltReuse`.
* `treeTwinReq` is the equal-cache relation. It holds `TreeSimStreamRel`, the equal adversary
  states, the equal output flags, and a stage relation `Stage`. The fields `stream` and `agree`
  are its projections.
* `treeSimStagesGoal2_of_twinFields` gives `TreeSimStagesGoal2` from `TreeTwinDigestGoal` and
  `TreeTwinStageGoal`. The second goal asks for a padding and a `Stage` with the fields `entry`
  and `next`.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- A program makes at most `n` exchanges, for every inbox and every local answer. It is the bound
form of `TreeSimCheckTimed` of `TreeSimCheck.lean`, which counts exact exchanges and has no local
work after the last exchange. The lemmas below follow the proofs of the `TreeSimCheckTimed` lemmas. -/
inductive TreeTwinWithin {α : Type} :
    ℕ → OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | pure (n : ℕ) (out : Option α) : TreeTwinWithin n (pure out)
  | queryLocal (n : ℕ) (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) (Option α))
      (h : ∀ r, TreeTwinWithin n (k r)) :
      TreeTwinWithin n (.roll (.inl (.inl q)) k)
  | round (n : ℕ) (out : Mail C E)
      (k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α))
      (h : ∀ r, TreeTwinWithin n (k r)) :
      TreeTwinWithin (n + 1) (.roll (.inl (.inr out)) k)

/-- A step makes at most `n` more exchanges. -/
def TreeTwinWithinStep {α : Type} (n : ℕ) (step : Step C E RealSpec α) : Prop :=
  match n, step with
  | _, .done _ => True
  | 0, .wait _ _ => False
  | n + 1, .wait _ resume => ∀ inbox, TreeTwinWithin n (resume inbox)
  | _, .call input _ => input.elim

theorem TreeTwinWithin.advance_mem {α : Type} {n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : TreeTwinWithin n p) :
    ∀ step ∈ support (advance p), TreeTwinWithinStep n step := by
  induction h with
  | pure n out =>
    intro step hs
    change step ∈ support (Pure.pure (.done out) : OracleComp (LocalSpec C) (Step C E RealSpec α)) at hs
    have he : step = .done out := by simpa using hs
    subst step
    cases n <;> trivial
  | queryLocal n q k h ih =>
    intro step hs
    obtain ⟨r, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hs
    exact ih r step hr
  | round n out k h ih =>
    intro step hs
    have he : step = .wait out k := by simpa [advance] using hs
    subst step
    exact h

theorem TreeTwinWithin.mono {α : Type} {n m : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : TreeTwinWithin n p) (hnm : n ≤ m) :
    TreeTwinWithin m p := by
  induction h generalizing m with
  | pure n out => exact .pure m out
  | queryLocal n q k h ih => exact .queryLocal m q k fun r => ih r hnm
  | round n out k h ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact .round m out k fun r => ih r (by omega)

theorem TreeTwinWithin.of_timed {α : Type} {n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : TreeSimCheckTimed n p) :
    TreeTwinWithin n p := by
  induction h with
  | abort n => exact .pure n none
  | done a => exact .pure 0 (some a)
  | queryLocal n q k h ih => exact .queryLocal (n + 1) q k ih
  | round n out k h ih => exact .round n out k ih

theorem TreeTwinWithin.bind {α β : Type} {m n : ℕ}
    {p : PartyM C E RealSpec α} {k : α → PartyM C E RealSpec β}
    (hp : TreeTwinWithin m p.run) (hk : ∀ a, TreeTwinWithin n (k a).run) :
    TreeTwinWithin (m + n) (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change TreeTwinWithin (m + n)
    (p.run >>= fun a => a.elim (Pure.pure none) (fun a => (k a).run))
  generalize p.run = oa at hp ⊢
  induction hp with
  | pure m out =>
    cases out with
    | none => simpa only [pure_bind, Option.elim_none] using TreeTwinWithin.pure (m + n) (none : Option β)
    | some a => simpa only [pure_bind, Option.elim_some] using (hk a).mono (by omega)
  | queryLocal m q f hf ih =>
    change TreeTwinWithin (m + n) (.roll (.inl (.inl q)) _)
    exact TreeTwinWithin.queryLocal (m + n) q _ fun r => by
      simpa only [OracleComp.bind_def] using ih r
  | round m out f hf ih =>
    rw [Nat.add_right_comm m 1 n]
    change TreeTwinWithin (m + n + 1) (.roll (.inl (.inr out)) _)
    exact TreeTwinWithin.round (m + n) out _ ih

theorem TreeTwinWithin.bind_support {α β : Type} {m n : ℕ}
    {p : PartyM C E RealSpec α} {k : α → PartyM C E RealSpec β}
    (hp : TreeTwinWithin m p.run) (hk : ∀ a, some a ∈ support p.run → TreeTwinWithin n (k a).run) :
    TreeTwinWithin (m + n) (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change TreeTwinWithin (m + n)
    (p.run >>= fun a => a.elim (Pure.pure none) (fun a => (k a).run))
  generalize p.run = oa at hp hk ⊢
  induction hp with
  | pure m out =>
    cases out with
    | none => simpa only [pure_bind, Option.elim_none] using TreeTwinWithin.pure (m + n) (none : Option β)
    | some a => simpa only [pure_bind, Option.elim_some] using (hk a (by simp)).mono (by omega)
  | queryLocal m q f hf ih =>
    change TreeTwinWithin (m + n) (.roll (.inl (.inl q)) _)
    exact TreeTwinWithin.queryLocal (m + n) q _ fun r => by
      simpa only [OracleComp.bind_def] using ih r fun a ha => hk a
        ((mem_support_bind_iff (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
          (.inl (.inl q)))) f _).mpr ⟨r, by simp; exact Set.mem_univ r, ha⟩)
  | round m out f hf ih =>
    rw [Nat.add_right_comm m 1 n]
    change TreeTwinWithin (m + n + 1) (.roll (.inl (.inr out)) _)
    exact TreeTwinWithin.round (m + n) out _ fun r => ih r fun a ha => hk a
      ((mem_support_bind_iff (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
        (.inl (.inr out)))) f _).mpr ⟨r, by simp; exact Set.mem_univ r, ha⟩)

theorem TreeTwinWithin.local_bind {α β : Type} (n : ℕ) (p : OracleComp (LocalSpec C) α)
    (k : α → PartyM C E RealSpec β) (hk : ∀ a, TreeTwinWithin n (k a).run) :
    TreeTwinWithin n (localStep p >>= k).run := by
  simp only [localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM,
    bind_assoc, pure_bind, Option.elim_some]
  change TreeTwinWithin n
    (liftComp p (PartySpec C E RealSpec) >>= fun a => (k a).run)
  induction p using OracleComp.inductionOn with
  | pure a => simpa only [liftComp_pure, pure_bind] using hk a
  | query_bind q f ih =>
    simp only [liftComp_bind, liftComp_query, bind_assoc]
    have hq : ((OracleSpec.query q).cont <$> liftM (OracleSpec.query (OracleSpec.query q).input) :
        OracleComp (PartySpec C E RealSpec) _) =
        OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) := by
      rw [← liftM_query_local]
      rfl
    rw [hq]
    exact TreeTwinWithin.queryLocal n q _ ih

theorem TreeTwinWithin.oracle_bind {α β : Type} (n : ℕ) (p : OracleComp (RoSpec C) α)
    (k : α → PartyM C E RealSpec β) (hk : ∀ a, TreeTwinWithin n (k a).run) :
    TreeTwinWithin n (oracleStep p >>= k).run :=
  TreeTwinWithin.local_bind n (liftComp p _) k hk

theorem TreeTwinWithin.require_bind {α : Type} (n : ℕ) (P : Prop)
    (k : Unit → PartyM C E RealSpec α) (hk : TreeTwinWithin n (k ()).run) :
    TreeTwinWithin n (require P >>= k).run := by
  by_cases hP : P
  · simpa only [require, if_pos hP, pure_bind] using hk
  · simp only [require, if_neg hP, failure_bind]
    exact TreeTwinWithin.pure n none

theorem TreeTwinWithin.state_bind {σ α β : Type} (m n : ℕ)
    (p : StateT σ (PartyM C E RealSpec) α) (k : α → StateT σ (PartyM C E RealSpec) β)
    (hp : ∀ s, TreeTwinWithin m (p.run s).run)
    (hk : ∀ a s, TreeTwinWithin n ((k a).run s).run) (s : σ) :
    TreeTwinWithin (m + n) ((p >>= k).run s).run := by
  rw [StateT.run_bind]
  exact (hp s).bind (fun a => hk a.1 a.2)

theorem TreeTwinWithin.foldlM {σ α β : Type} (n : ℕ)
    (f : α → β → StateT σ (PartyM C E RealSpec) α)
    (hf : ∀ a b s, TreeTwinWithin n ((f a b).run s).run) (xs : List β) (a : α) (s : σ) :
    TreeTwinWithin (xs.length * n) ((xs.foldlM f a).run s).run := by
  induction xs generalizing a s with
  | nil =>
    simp only [List.foldlM_nil, List.length_nil, Nat.zero_mul, StateT.run_pure, OptionT.run_pure]
    exact .pure 0 _
  | cons b xs ih =>
    simp only [List.foldlM_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    rw [Nat.add_comm]
    exact TreeTwinWithin.state_bind n (xs.length * n) (f a b)
      (fun a => xs.foldlM f a) (hf a b) (fun a s => ih a s) s

set_option backward.isDefEq.respectTransparency false in
theorem TreeTwinWithin.exchange_bind {α : Type} (n : ℕ) (out : Mail C E)
    (k : Mail C E → PartyM C E RealSpec α) (hk : ∀ inbox, TreeTwinWithin n (k inbox).run) :
    TreeTwinWithin (n + 1) (exchange out >>= k).run := by
  have he : (exchange out >>= k).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>=
        exchangeResume k := by
    simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk,
      pure_bind, Option.elimM]
    apply bind_congr
    intro inbox
    simp only [Option.elim]
    unfold exchangeResume
    split <;> simp_all
  rw [he]
  apply TreeTwinWithin.round
  intro inbox
  change TreeTwinWithin n (exchangeResume k inbox)
  unfold exchangeResume
  split_ifs
  · exact TreeTwinWithin.pure n none
  · simpa only [OptionT.run_pure, pure_bind, Option.elim_some] using hk inbox

theorem treeTwinWithin_openSh (ctx : Context C) (v : ℕ → E) (count : ℕ) :
    TreeTwinWithin 1 (openSh (G := RealSpec) K ctx v count).run := by
  unfold openSh
  exact TreeTwinWithin.exchange_bind 0 _ _ fun _ =>
    TreeTwinWithin.require_bind 0 _ _ (TreeTwinWithin.pure 0 _)

theorem treeTwinWithin_coin (ctx : Context C) (count : ℕ) (st : RunState C) :
    TreeTwinWithin 1 (((realCheckGadgets (G := RealSpec) K ctx).coin count).run st).run := by
  change TreeTwinWithin 1 ((prssRandomness ctx (elementCodec K) 1 count >>= fun o =>
    coinWith K ctx o count).run st).run
  rw [prssRandomness_run]
  refine TreeTwinWithin.oracle_bind 1 _ _ fun o => ?_
  unfold coinWith
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  exact (treeTwinWithin_openSh K ctx _ count).bind fun _ => TreeTwinWithin.pure 0 _

theorem treeTwinWithin_coinKey (ctx : Context C) (st : RunState C) :
    TreeTwinWithin 1 ((coinKey K (realCheckGadgets (G := RealSpec) K ctx)).run st).run := by
  simp only [coinKey, StateT.run_bind, StateT.run_get, StateT.run_lift, pure_bind]
  exact (treeTwinWithin_coin K ctx 1 st).bind fun _ =>
    TreeTwinWithin.oracle_bind 0 _ _ fun _ => TreeTwinWithin.pure 0 _

theorem treeTwinWithin_challenge (ctx : Context C) (st : RunState C) :
    TreeTwinWithin 1 ((challenge K (realCheckGadgets (G := RealSpec) K ctx)).run st).run := by
  simp only [challenge, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine (TreeTwinWithin.bind (n := 0) (treeTwinWithin_coinKey K ctx st) fun key => ?_ :
    TreeTwinWithin (1 + 0) _)
  refine TreeTwinWithin.oracle_bind 0 _ _ fun r => ?_
  cases r with
  | none =>
    simp only [StateT.run_lift, failure_bind]
    exact TreeTwinWithin.pure 0 none
  | some r =>
    simp only [StateT.run_pure, OptionT.run_pure]
    exact TreeTwinWithin.pure 0 _

theorem treeTwinWithin_expand (key : HashOutput) (count : ℕ) (st : RunState C) :
    TreeTwinWithin 0 ((expand (G := RealSpec) K key count).run st).run := by
  simp only [expand, StateT.run_lift]
  exact TreeTwinWithin.oracle_bind 0 _ _ fun _ => TreeTwinWithin.pure 0 _

theorem treeTwinWithin_extendMult (ctx : Context C) (products : List (Product C E))
    (st : RunState C) :
    TreeTwinWithin 1 (((realCheckGadgets (G := RealSpec) K ctx).extendMult products).run st).run := by
  change TreeTwinWithin 1 ((prssRandomness ctx (elementCodec K) 0 products.length >>= fun rnd =>
    reshare K ctx (elementCodec K) rnd _ products.length).run st).run
  rw [prssRandomness_run]
  exact TreeTwinWithin.oracle_bind 1 _ _ fun rnd =>
    TreeTwinWithin.of_timed (treeSimCheckTimed_reshare K ctx (elementCodec K) rnd _ _ _)

theorem treeTwinWithin_prssRandomness {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R)
    (idx count : ℕ) (st : RunState C) :
    TreeTwinWithin 0 ((prssRandomness (G := RealSpec) ctx codec idx count).run st).run := by
  have h := prssRandomness_run (G := RealSpec) ctx codec idx count pure st
  rw [bind_pure] at h
  rw [h]
  exact TreeTwinWithin.oracle_bind 0 _ _ fun _ => TreeTwinWithin.pure 0 _

theorem treeTwinWithin_compareDigests (ctx : Context C) (salts : Shares C Bit) (st : RunState C) :
    TreeTwinWithin 1 ((compareDigests (E := E) (G := RealSpec) ctx salts).run st).run := by
  rw [compareDigests_run]
  exact TreeTwinWithin.oracle_bind 1 _ _ fun _ => TreeTwinWithin.exchange_bind 0 _ _ fun _ =>
    TreeTwinWithin.require_bind 0 _ _ (TreeTwinWithin.pure 0 _)

theorem TreeTwinWithin.state_bind_le {σ α β : Type} {m n N : ℕ}
    {p : StateT σ (PartyM C E RealSpec) α} {k : α → StateT σ (PartyM C E RealSpec) β}
    (hp : ∀ s, TreeTwinWithin m (p.run s).run)
    (hk : ∀ a s, TreeTwinWithin n ((k a).run s).run) (hN : m + n ≤ N) (s : σ) :
    TreeTwinWithin N ((p >>= k).run s).run :=
  (TreeTwinWithin.state_bind m n p k hp hk s).mono hN

theorem treeTwinWithin_lift {σ α : Type} (n : ℕ) (p : PartyM C E RealSpec α)
    (hp : TreeTwinWithin n p.run) (s : σ) :
    TreeTwinWithin n ((StateT.lift p : StateT σ (PartyM C E RealSpec) α).run s).run := by
  rw [StateT.run_lift]
  exact Nat.add_zero n ▸ hp.bind fun _ => TreeTwinWithin.pure 0 _

theorem treeTwinWithin_require (P : Prop) :
    TreeTwinWithin 0 (require P : PartyM C E RealSpec Unit).run := by
  by_cases hP : P
  · simp only [require, if_pos hP, OptionT.run_pure]
    exact TreeTwinWithin.pure 0 _
  · simp only [require, if_neg hP, OptionT.run_failure]
    exact TreeTwinWithin.pure 0 _

theorem treeTwinWithin_check (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C) :
    TreeTwinWithin (checkLabels (tuples.map (·.count)).sum)
      ((check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples).run st).run := by
  have hs : sliceBits ≤ halvings (tuples.map (·.count)).sum := by
    unfold halvings
    omega
  unfold check
  dsimp only
  split_ifs with hzero
  · simp only [StateT.run_pure, OptionT.run_pure]
    exact TreeTwinWithin.pure _ _
  have hl : checkLabels (tuples.map (·.count)).sum = 2 * halvings (tuples.map (·.count)).sum + 5 := by
    unfold checkLabels
    rw [if_neg hzero]
  rw [hl]
  generalize halvings (tuples.map (·.count)).sum = h at hs ⊢
  refine TreeTwinWithin.state_bind_le (E := E) (m := 0) (n := 2 * h + 5)
    (fun s => TreeTwinWithin.pure 0 _) (fun _ s => ?_) (by omega) st
  refine TreeTwinWithin.state_bind_le (m := 1) (n := 2 * h + 4)
    (fun s => treeTwinWithin_coinKey K ctx s) (fun key s => ?_) (by omega) s
  refine TreeTwinWithin.state_bind_le (m := 0) (n := 2 * h + 4)
    (fun s => treeTwinWithin_expand K key _ s) (fun τ s => ?_) (by omega) s
  refine TreeTwinWithin.state_bind_le (m := 0) (n := 2 * h + 4)
    (fun s => treeTwinWithin_lift 0 _ (treeTwinWithin_require _) s)
    (fun _ s => ?_) (by omega) s
  refine TreeTwinWithin.state_bind_le (m := (List.range sliceBits).length * 2) (n := 2 * (h - sliceBits) + 4)
    (fun s => TreeTwinWithin.foldlM 2 _ (fun x j s =>
      TreeTwinWithin.state_bind_le (m := 1) (n := 1) (fun s => treeTwinWithin_extendMult K ctx _ s)
        (fun t s => TreeTwinWithin.state_bind_le (m := 1) (n := 0)
          (fun s => treeTwinWithin_challenge K ctx s) (fun r s => TreeTwinWithin.pure 0 _) (by omega) s)
        (by omega) s) _ _ s)
    (fun x s => ?_) (by simp only [List.length_range]; omega) s
  refine TreeTwinWithin.state_bind_le (m := (List.range (h - sliceBits)).length * 2) (n := 4)
    (fun s => TreeTwinWithin.foldlM 2 _ (fun x j s =>
      TreeTwinWithin.state_bind_le (m := 1) (n := 1) (fun s => treeTwinWithin_extendMult K ctx _ s)
        (fun t s => TreeTwinWithin.state_bind_le (m := 1) (n := 0)
          (fun s => treeTwinWithin_challenge K ctx s) (fun r s => TreeTwinWithin.pure 0 _) (by omega) s)
        (by omega) s) _ _ s)
    (fun y s => ?_) (by simp only [List.length_range]; omega) s
  refine TreeTwinWithin.state_bind_le (m := 0) (n := 4)
    (fun s => treeTwinWithin_prssRandomness ctx _ _ _ s) (fun w s => ?_) (by omega) s
  refine TreeTwinWithin.state_bind_le (m := 1) (n := 3)
    (fun s => treeTwinWithin_extendMult K ctx _ s) (fun q s => ?_) (by omega) s
  refine TreeTwinWithin.state_bind_le (m := 0) (n := 3)
    (fun s => treeTwinWithin_prssRandomness ctx _ _ _ s) (fun salts s => ?_) (by omega) s
  refine TreeTwinWithin.state_bind_le (m := 1) (n := 2)
    (fun s => treeTwinWithin_compareDigests ctx _ s) (fun _ s => ?_) (by omega) s
  refine TreeTwinWithin.state_bind_le (m := 1) (n := 1)
    (fun s => treeTwinWithin_challenge K ctx s) (fun r s => ?_) (by omega) s
  refine TreeTwinWithin.state_bind_le (m := 1) (n := 0)
    (fun s => treeTwinWithin_lift 1 _ (treeTwinWithin_openSh K ctx _ _) s) (fun opened s => ?_) (by omega) s
  exact treeTwinWithin_lift 0 _ (treeTwinWithin_require _) s

theorem TreeTwinWithin.map {α β : Type} {n : ℕ} (f : α → β) {p : PartyM C E RealSpec α}
    (hp : TreeTwinWithin n p.run) : TreeTwinWithin n (f <$> p).run := by
  rw [map_eq_bind_pure_comp]
  exact Nat.add_zero n ▸ hp.bind fun _ => TreeTwinWithin.pure 0 _

theorem treeTwinWithin_openRep (ctx : Context C) (v : Shares C Bit) (count : ℕ) :
    TreeTwinWithin 1 (openRep (G := RealSpec) K ctx v count).run := by
  unfold openRep
  exact TreeTwinWithin.oracle_bind 1 _ _ fun _ => TreeTwinWithin.exchange_bind 0 _ _ fun _ =>
    TreeTwinWithin.oracle_bind 0 _ _ fun _ => TreeTwinWithin.require_bind 0 _ _ (TreeTwinWithin.pure 0 _)

/-- A batch makes at most `batchRounds` exchanges. -/
theorem treeTwinWithin_ceremonyBatch (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    TreeTwinWithin (batchRounds circuits settings.mode ctx.keys.parameter jobs)
      ((ceremonyBatch K circuits settings ctx jobs : StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run
        initial).run := by
  rw [← treeSimCheckBatchAudit_erase K circuits settings ctx jobs]
  change TreeTwinWithin _ ((Prod.fst <$> (treeSimCheckBatchAudit K circuits settings ctx jobs).run).run
    initial).run
  rw [StateT.run_map, treeSimCheckBatchAudit_run_prefix]
  apply TreeTwinWithin.map
  refine (TreeTwinWithin.bind_support
    (n := checkLabels (batchCount circuits ctx.keys.parameter jobs) + 1)
    (TreeTwinWithin.of_timed (treeSimCheckBatchPrefix_timed K circuits settings ctx jobs initial))
    fun a ha => ?_).mono (by unfold batchRounds; omega)
  have hcount : (a.2.1.2.map (·.count)).sum = batchCount circuits ctx.keys.parameter jobs := by
    simp only [treeSimCheckBatchPrefix, OptionT.run_bind, Option.elimM] at ha
    obtain ⟨x, _, hx⟩ := (mem_support_bind_iff _ _ _).mp ha
    cases x with
    | none => simp at hx
    | some inputs =>
      obtain ⟨y, hy, hxy⟩ := (mem_support_bind_iff _ _ _).mp hx
      cases y with
      | none => simp at hxy
      | some q =>
        simp only [Option.elim_some, OptionT.run_pure, support_pure, Set.mem_singleton_iff,
          Option.some.injEq] at hxy
        subst a
        exact treeSimCheckBeforeVerify_count K ctx settings.mode _ inputs initial.1 initial.2
          q.1 q.2 hy
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify
  refine Nat.add_zero (checkLabels (batchCount circuits ctx.keys.parameter jobs) + 1) ▸
    TreeTwinWithin.bind ?_ (fun _ => TreeTwinWithin.pure 0 _)
  rw [← hcount]
  exact TreeTwinWithin.bind (treeTwinWithin_check K ctx a.2.1.2 a.2.2) fun x => by
    obtain ⟨fst, final⟩ := x
    exact Nat.add_zero 1 ▸ (treeTwinWithin_openRep K ctx _ _).bind fun _ => TreeTwinWithin.pure 0 _

theorem TreeTwinWithin.mapM {σ β γ : Type} (f : β → StateT σ (PartyM C E RealSpec) γ)
    (bound : β → ℕ) (hf : ∀ b s, TreeTwinWithin (bound b) ((f b).run s).run) :
    ∀ (xs : List β) (s : σ), TreeTwinWithin ((xs.map bound).sum) ((xs.mapM f).run s).run
  | [], s => by
    simp only [List.mapM_nil, List.map_nil, List.sum_nil, StateT.run_pure, OptionT.run_pure]
    exact TreeTwinWithin.pure 0 _
  | x :: xs, s => by
    simp only [List.mapM_cons, List.map_cons, List.sum_cons]
    exact TreeTwinWithin.state_bind_le (hf x) (fun a s =>
      TreeTwinWithin.state_bind_le (TreeTwinWithin.mapM f bound hf xs)
        (fun _ _ => TreeTwinWithin.pure 0 _) (Nat.add_zero _).le s) le_rfl s

/-- The batches of one run of a ceremony. -/
theorem treeTwinWithin_batched (ctx : Context C) (js : List Job) (b : Fin (2 ^ layerHeight))
    (enc : Encoding) (hjs : js = topJobs ∨ js = bottomJobs b ∨ js = signJobs b enc) (s : ℕ × ℕ) :
    TreeTwinWithin ((chunks settings.batchSize js).length *
        maxBatch circuits settings (runRounds settings.mode))
      ((batched settings.batchSize (ceremonyBatch K circuits settings ctx) js :
        StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run s).run := by
  unfold batched
  refine TreeTwinWithin.state_bind_le
    (TreeTwinWithin.mapM _ (batchRounds circuits settings.mode ctx.keys.parameter)
      (treeTwinWithin_ceremonyBatch K circuits settings ctx) _)
    (fun _ _ => TreeTwinWithin.pure 0 _) ?_ s
  rw [Nat.add_zero]
  apply chunks_rounds_le circuits settings ctx.keys.parameter b enc
  intro jobs hjobs
  rcases hjs with h | h | h
  · exact Or.inl (by rw [← h]; exact hjobs)
  · exact Or.inr (Or.inl (by rw [← h]; exact hjobs))
  · exact Or.inr (Or.inr (by rw [← h]; exact hjobs))

theorem treeTwinWithin_oracleStep {σ α : Type} (p : OracleComp (RoSpec C) α) (s : σ) :
    TreeTwinWithin 0 ((StateT.lift (oracleStep p) : StateT σ (PartyM C E RealSpec) α).run s).run := by
  apply treeTwinWithin_lift
  rw [← bind_pure (oracleStep p)]
  exact TreeTwinWithin.oracle_bind 0 _ _ fun _ => TreeTwinWithin.pure 0 _

/-- The honest program after the PRSS setup makes at most the round budget of the ceremony
after its setup. This is the round count of `ceremonyAfterSetup` for every inbox. -/
def TreeTwinAfterSetupWithin : Prop :=
  ∀ (ctx : Context C) (top : TopTree) (tree : Tree),
    TreeTwinWithin (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode))
      (ceremonyAfterSetup K circuits settings ctx top tree : PartyM C E RealSpec TreeOutput).run

theorem treeTwin_roundLocal_within {α : Type} (D : C.Coalition) (n : ℕ)
    (steps : C.Party → Step C E RealSpec α) (sent : C.Party → Mail C E)
    (hs : ∀ i, i ∉ D.1 → TreeTwinWithinStep (n + 1) (steps i)) :
    ∀ i, i ∉ D.1 → ∀ next, next ∈ support (roundLocal D steps sent i) → TreeTwinWithinStep n next := by
  intro i hi next hn
  have h := hs i hi
  cases he : steps i with
  | done out =>
    have hn' : next = .done out := by simpa only [roundLocal, he, support_pure,
      Set.mem_singleton_iff] using hn
    subst next
    cases n <;> trivial
  | call input resume => exact input.elim
  | wait out resume =>
    simp only [roundLocal, he, if_neg hi] at hn
    simp only [he, TreeTwinWithinStep] at h
    exact (h _).advance_mem next hn

/-- One round of the network lowers the exchange bound of every honest step. -/
theorem treeTwin_round_within {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (n : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (hs : ∀ i, i ∉ D.1 → TreeTwinWithinStep (n + 1) (steps i)) :
    ∀ r ∈ support (stepRound worldRoles D A noFunctionality state steps),
      ∀ i, i ∉ D.1 → TreeTwinWithinStep n (r.2.1 i) := by
  rw [stepRound_real]
  intro r hr
  obtain ⟨sent, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  obtain ⟨next, hn, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  have he : r = (sent.1, next, sent.2) := by simpa using hr
  subst r
  have hl := treeSimCheck_support_free _ hn
  intro i hi
  exact treeTwin_roundLocal_within D n steps sent.2 hs i hi (next i)
    (mem_support_sequenceFin_oc _ _ hl i)

/-- The logged real round has the support of the plain round. -/
theorem treeTwin_real_round_mem {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (s : TreeSimState C)
    (u : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) × TreeSimState C)
    (hu : u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality state steps).run s)) :
    u.1 ∈ support (stepRound worldRoles D A noFunctionality state steps) := by
  apply OracleComp.support_simulateQ_run'_subset (treeSimLoggedWorld prims D)
  rw [simulateQ_stepRound, StateT.run'_eq, support_map]
  exact ⟨u, hu, rfl⟩

/-- Every honest step of a reachable configuration after `n` rounds makes at most the rest of
the round budget. -/
theorem treeTwin_reach_within
    (within : TreeTwinAfterSetupWithin K circuits settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (s : TreeSimState C) :
    ∀ n a, TreeStagesReach prims K circuits settings top tree D A x state s n a →
      ∀ i, i ∉ D.1 → TreeTwinWithinStep
        (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) - n) (a.1.2 i) := by
  intro n
  induction n with
  | zero =>
    intro a ha i hi
    simp only [TreeStagesReach, treeStagesTrace, executeSteps, StateT.run_bind, StateT.run_pure,
      support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at ha
    obtain ⟨p, _, next, hnext, rfl⟩ := ha
    have hn : next.1 ∈ support (treeSimContinue (treeSimRealCont K circuits settings top tree x) p.1.2) := by
      apply OracleComp.support_simulateQ_run'_subset (treeSimLoggedWorld prims D)
      rw [StateT.run'_eq, support_map]
      exact ⟨next, hnext, rfl⟩
    have hi' := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _ hn) i
    simp only [Nat.sub_zero]
    cases hk : p.1.2 i with
    | none =>
      simp only [hk, continueStep, support_pure, Set.mem_singleton_iff] at hi'
      rw [hi']
      trivial
    | some prss =>
      simp only [hk, continueStep] at hi'
      exact (within ⟨i, x i, prss⟩ top tree).advance_mem _ hi'
  | succ n ih =>
    intro a ha i hi
    unfold TreeStagesReach at ha
    rw [treeStages_trace_add] at ha
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at ha
    obtain ⟨b, hb', ha⟩ := ha
    have hw := ih b hb'
    simp only [executeSteps] at ha
    split_ifs at ha with hdone
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at ha
      subst a
      have hd := hdone i hi
      revert hd
      cases b.1.2 i with
      | done out => intro _; trivial
      | wait out resume => intro hd; exact hd.elim
      | call input resume => intro hd; exact hd.elim
    · obtain ⟨j, hj, hjd⟩ : ∃ j, j ∉ D.1 ∧ ¬ (b.1.2 j).isDone := by
        by_contra hc
        exact hdone fun j hj => by_contra fun h => hc ⟨j, hj, h⟩
      obtain ⟨m, hm⟩ : ∃ m, ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) - n = m + 1 := by
        have hwj := hw j hj
        revert hwj hjd
        cases b.1.2 j with
        | done out => intro hjd; exact (hjd trivial).elim
        | call input resume => exact input.elim
        | wait out resume =>
          intro _ hwj
          cases hk : ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) - n with
          | zero => rw [hk] at hwj; exact hwj.elim
          | succ m => exact ⟨m, rfl⟩
      simp only [StateT.run_bind, support_bind, Set.mem_iUnion, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at ha
      obtain ⟨u, hu, rfl⟩ := ha
      have hm' : ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) - (n + 1) = m := by
        omega
      rw [hm']
      rw [hm] at hw
      exact treeTwin_round_within D A m b.1.1 b.1.2 hw u.1
        (treeTwin_real_round_mem prims D A b.1.1 b.1.2 b.2 u hu) i hi

theorem treeTwinWithin_ceremonyOutput_top (ctx : Context C) (top : TopTree) :
    TreeTwinWithin (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode))
      ((ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) ctx.keys.parameter
        (batched settings.batchSize (ceremonyBatch K circuits settings ctx)) top .top).run (0, 0)).run := by
  simp only [ceremonyOutput]
  refine TreeTwinWithin.state_bind_le (n := 0)
    (treeTwinWithin_batched K circuits settings ctx topJobs ⟨0, by positivity⟩ (fun _ => digit 0)
      (Or.inl rfl))
    (fun r s => ?_) (by rw [Nat.add_zero, ceremonyBatches]; exact Nat.mul_le_mul_right _ (le_max_left _ _))
    (0, 0)
  cases r with
  | none => exact TreeTwinWithin.pure 0 _
  | some outputs =>
    exact TreeTwinWithin.state_bind_le (treeTwinWithin_oracleStep _)
      (fun _ _ => TreeTwinWithin.pure 0 _) le_rfl s

theorem treeTwinWithin_ceremonyOutput_bottom (ctx : Context C) (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    TreeTwinWithin (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode))
      ((ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) ctx.keys.parameter
        (batched settings.batchSize (ceremonyBatch K circuits settings ctx)) top (.bottom b)).run
          (0, 0)).run := by
  simp only [ceremonyOutput]
  have hle := Nat.mul_le_mul_right (maxBatch circuits settings (runRounds settings.mode))
    (treeBatches_le_ceremonyBatches settings (.bottom b))
  simp only [treeBatches, Nat.add_mul] at hle
  refine TreeTwinWithin.state_bind_le
    (n := (chunks settings.batchSize (signJobs b fun _ => digit 0)).length *
      maxBatch circuits settings (runRounds settings.mode))
    (treeTwinWithin_batched K circuits settings ctx (bottomJobs b) b (fun _ => digit 0)
      (Or.inr (Or.inl rfl)))
    (fun r s => ?_) hle (0, 0)
  cases r with
  | none => exact TreeTwinWithin.pure _ _
  | some outputs =>
    refine TreeTwinWithin.state_bind_le (treeTwinWithin_oracleStep _) (fun root s => ?_)
      (Nat.zero_add _).le s
    refine TreeTwinWithin.state_bind_le (treeTwinWithin_oracleStep _) (fun base s => ?_)
      (Nat.zero_add _).le s
    refine TreeTwinWithin.state_bind_le (treeTwinWithin_oracleStep _) (fun g s => ?_)
      (Nat.zero_add _).le s
    rcases g with _ | ⟨randomness, encoding⟩
    · exact TreeTwinWithin.pure _ _
    refine TreeTwinWithin.state_bind_le (n := 0)
      (treeTwinWithin_batched K circuits settings ctx (signJobs b encoding) b encoding
        (Or.inr (Or.inr rfl)))
      (fun v s => ?_) ?_ s
    · rcases v with _ | values
      · exact TreeTwinWithin.pure _ _
      refine TreeTwinWithin.state_bind_le (treeTwinWithin_oracleStep _) (fun path s => ?_)
        (Nat.zero_add _).le s
      refine TreeTwinWithin.state_bind_le (treeTwinWithin_oracleStep _) (fun root' s => ?_)
        (Nat.zero_add _).le s
      split_ifs
      · exact TreeTwinWithin.pure _ _
      · exact TreeTwinWithin.pure _ _
    · rw [Nat.add_zero, length_chunks_signJobs settings b b encoding (fun _ => digit 0)]

/-- The round count of the ceremony after its PRSS setup. Each batch makes at most
`batchRounds` exchanges, and a ceremony has at most `ceremonyBatches` batches. -/
theorem treeTwinAfterSetupWithin : TreeTwinAfterSetupWithin K circuits settings := by
  intro ctx top tree
  unfold ceremonyAfterSetup
  refine Nat.add_zero (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)) ▸
    TreeTwinWithin.bind ?_ (fun o => ?_)
  · rw [StateT.run'_eq]
    apply TreeTwinWithin.map
    cases tree with
    | top => exact treeTwinWithin_ceremonyOutput_top K circuits settings ctx top
    | bottom b => exact treeTwinWithin_ceremonyOutput_bottom K circuits settings ctx top b
  · cases o with
    | none => exact TreeTwinWithin.pure 0 none
    | some output => exact TreeTwinWithin.pure 0 _

/-- The field `progress` of `TreeStagesTwinRelation`. A reachable configuration with an active
honest operator has a round left in the budget. -/
theorem treeTwin_progress (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (state : A.State) (s : TreeSimState C) (n : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top tree D A x state s n a)
    (active : ¬ AllDone D a.1.2) : n + 1 + 3 ≤ ceremonyFuel circuits settings := by
  obtain ⟨j, hj, hjd⟩ : ∃ j, j ∉ D.1 ∧ ¬ (a.1.2 j).isDone := by
    by_contra hc
    exact active fun j hj => by_contra fun h => hc ⟨j, hj, h⟩
  have hw := treeTwin_reach_within prims K circuits settings
    (treeTwinAfterSetupWithin K circuits settings) top tree D A x state s n a reach j hj
  have hpos : 0 < ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) - n := by
    revert hw hjd
    cases a.1.2 j with
    | done out => intro hjd; exact (hjd trivial).elim
    | call input resume => exact input.elim
    | wait out resume =>
      intro _ hw
      cases hk : ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode) - n with
      | zero => rw [hk] at hw; exact hw.elim
      | succ m => omega
  unfold ceremonyFuel setupRounds
  omega

/-- The equal-cache relation of the twins. `Stage` holds the stage data of the round `n`. -/
def treeTwinReq {A : Adversary C E (Keys C) PEmpty PEmpty} (D : C.Coalition)
    (Stage : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (n : ℕ) (δ : HiddenAddress C → Bit) (a : TreeSimConfig A (TreeSimState C))
    (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  TreeSimStreamRel δ a.2 b.2 ∧ a.1.1 = b.1.1 ∧ (AllDone D a.1.2 ↔ AllDone D b.1.2) ∧
    (∀ i, i ∉ D.1 → (a.1.2 i).output.isSome = (b.1.2 i).output.isSome) ∧ Stage n δ a b

section Fields

variable (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
  (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
  (r : Unit × HashCache C)
  (Req : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop)

/-- The field `entry` of `TreeStagesTwinRelation`. -/
def TreeTwinEntry : Prop :=
  ∀ u ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 p.2.1
    (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run ((r.2, p.2.2.1.2), p.2.2.2)),
    RelTriple
    ((simulateQ (treeSimLoggedWorld prims D)
    (treeSimContinue (treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs)) u.1.2)).run u.2)
    ((simulateQ (streamWorld prims D)
    (treeSimContinue (treeSimIdealCont K circuits settings top tree D parameter
    (fun T => if KnownTo D.1 T then seeds T else 0) p.1.2) u.1.2)).run u.2.1)
    (fun a b => TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 ∨
    ∃ δ, Req 0 δ ((u.1.1, a.1), a.2) ((u.1.1, b.1), b.2))

/-- The field `freeHit` of `TreeStagesTwinRelation`. -/
def TreeTwinFreeHit : Prop :=
  ∀ n δ swaps (a : TreeSimConfig A (TreeSimState C)) b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
    Req n δ (a.1, treeStagesTwin swaps a.2) b →
    ∀ u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2),
    (∃ l, u.2.2 = a.2.2 ++ l ∧ TreeStagesFreeHit swaps l) →
    TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z u.2.2

/-- Each honest digest call of the round log `l` hashes a salt that `l` draws at one address,
and no hidden salt of the earlier log `start` was drawn at that address. `compareDigests` draws
its salts and hashes them in one local step, and each check takes a fresh label. -/
def TreeTwinDigestDrawn (start l : TreeSimLog C) : Prop :=
  ∀ salt hist answer, (⟨.inr (.inr (.inl (.digest salt hist))), answer⟩ :
    (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ l →
    ∃ T' key' label', (∀ g : Fin 256,
      (⟨.inr (.inr (.inr (.term T', key', label', 2, g.val))), salt.getD g.val 0⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ l) ∧
      ∀ T key label, ¬ KnownTo D.1 T → (∀ g : Fin 256,
        (⟨.inr (.inr (.inr (.term T, key, label, 2, g.val))), salt.getD g.val 0⟩ :
          (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ start) →
        (T, key, label) ≠ (T', key', label')

/-- The program fact behind `freeHit`. Every reachable real round satisfies
`TreeTwinDigestDrawn`. -/
def TreeTwinDigestDrawnGoal : Prop :=
  ∀ n (a : TreeSimConfig A (TreeSimState C)),
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ∀ u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2),
    ∀ l, u.2.2 = a.2.2 ++ l → TreeTwinDigestDrawn D a.2.2 l

/-- The field `freeHit` from the program fact. A free digest call at a swapped salt draws that
salt again at a new address, which is `TreeSimSaltReuse`. -/
theorem treeTwin_freeHit
    (drawn : TreeTwinDigestDrawnGoal prims K circuits settings top tree D A parameter seeds pairs z p r) :
    TreeTwinFreeHit prims K circuits settings top tree D A parameter seeds pairs z p r Req := by
  intro n δ swaps a b reach good salts _ u hu hit
  obtain ⟨l, hl, x, hx, hist, answer, mem⟩ := hit
  obtain ⟨T', key', label', draws, fresh⟩ := drawn n a reach good u hu l hl x.1 hist answer mem
  obtain ⟨hlen, T, key, label, hidden, old⟩ := salts x hx
  refine Or.inl (Or.inr ⟨x.1, T, key, label, T', key', label', hlen, hidden,
    fresh T key label hidden old, fun g => ⟨?_, ?_⟩⟩)
  · rw [hl]
    exact List.mem_append_left _ (old g)
  · rw [hl]
    exact List.mem_append_right _ (draws g)

/-- The field `next` of `TreeStagesTwinRelation`. -/
def TreeTwinNext : Prop :=
  ∀ n δ swaps (a : TreeSimConfig A (TreeSimState C)) b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 →
    (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
    Req n δ (a.1, treeStagesTwin swaps a.2) b →
    RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run (treeStagesTwin swaps a.2))
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2)
    (fun v w => TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z v.2.2 ∨
    ∃ extra δ', (∀ x ∈ extra, TreeSimHiddenSalt D v.2.2 x.1) ∧
    Req (n + 1) δ' ((v.1.1, v.1.2.1), treeStagesTwin extra v.2) ((w.1.1, w.1.2.1), w.2))

end Fields

/-- The program fact behind `freeHit` at every good prefix and every padded cache. -/
def TreeTwinDigestGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux),
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∀ (padding : OracleComp (LocalSpec C) Unit),
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    TreeTwinDigestDrawnGoal prims K circuits settings top tree D A parameter seeds pairs z p r

/-- The stage part of `TreeSimStagesTwinRelationGoal`. It asks for a padding and a stage relation
whose `treeTwinReq` has the fields `entry`, `freeHit` and `next`. -/
def TreeTwinStageGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∃ Stage : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop,
    TreeTwinEntry prims K circuits settings top tree D A parameter seeds pairs z p r (treeTwinReq D Stage) ∧
    TreeTwinFreeHit prims K circuits settings top tree D A parameter seeds pairs z p r (treeTwinReq D Stage) ∧
    TreeTwinNext prims K circuits settings top tree D A parameter seeds pairs z p r (treeTwinReq D Stage)

/-- `TreeTwinStageGoal` without the field `freeHit`. -/
def TreeTwinStageCoreGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad2 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∃ padding : OracleComp (LocalSpec C) Unit,
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∃ Stage : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop,
    TreeTwinEntry prims K circuits settings top tree D A parameter seeds pairs z p r (treeTwinReq D Stage) ∧
    TreeTwinNext prims K circuits settings top tree D A parameter seeds pairs z p r (treeTwinReq D Stage)

/-- The field `freeHit` of every stage relation from the program fact. -/
theorem treeTwinStageGoal_of_digest
    (digest : TreeTwinDigestGoal prims K circuits settings)
    (core : TreeTwinStageCoreGoal prims K circuits settings) :
    TreeTwinStageGoal prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  obtain ⟨padding, hpadding⟩ := core hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨Stage, entry, next⟩ := hpadding r hr
  exact ⟨Stage, entry, treeTwin_freeHit prims K circuits settings top tree D A parameter seeds pairs z p r _
    (digest hb top tree D A parameter seeds pairs z p hp good padding r hr), next⟩

/-- The twin relation from the stage part. The fields `stream`, `agree` and `progress` are
proved here. -/
theorem treeSimStagesTwinRelationGoal_of_fields
    (stage : TreeTwinStageGoal prims K circuits settings) :
    TreeSimStagesTwinRelationGoal prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  obtain ⟨padding, hpadding⟩ := stage hb top tree D A parameter seeds pairs z Z q hq hsmall p hp good
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨Stage, entry, freeHit, next⟩ := hpadding r hr
  exact ⟨{
    Req := treeTwinReq D Stage
    stream := fun _ _ _ _ req => req.1
    entry := entry
    agree := fun _ _ _ _ _ _ _ req => ⟨req.2.1, req.2.2.1, req.2.2.2.1⟩
    progress := fun n a reach _ _ active =>
      treeTwin_progress prims K circuits settings top tree D A _ _ _ n a reach active
    freeHit := freeHit
    next := next }⟩

/-- `TreeSimStagesGoal2` from the stage part. -/
theorem treeSimStagesGoal2_of_twinFields
    (stage : TreeTwinStageGoal prims K circuits settings) :
    TreeSimStagesGoal2 prims K circuits settings :=
  treeSimStagesGoal2_of_twinRelation prims K circuits settings
    (treeSimStagesTwinRelationGoal_of_fields prims K circuits settings stage)

/-- `TreeSimStagesGoal2` from the program fact behind `freeHit` and the fields `entry` and `next`. -/
theorem treeSimStagesGoal2_of_digest
    (digest : TreeTwinDigestGoal prims K circuits settings)
    (core : TreeTwinStageCoreGoal prims K circuits settings) :
    TreeSimStagesGoal2 prims K circuits settings :=
  treeSimStagesGoal2_of_twinFields prims K circuits settings
    (treeTwinStageGoal_of_digest prims K circuits settings digest core)

/-- info: 'ThresholdLeanXmssSecurity.treeTwinAfterSetupWithin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinAfterSetupWithin

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_progress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_progress

/-- info: 'ThresholdLeanXmssSecurity.treeTwin_freeHit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwin_freeHit

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal2_of_twinFields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal2_of_twinFields

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal2_of_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal2_of_digest

end ThresholdLeanXmssSecurity
