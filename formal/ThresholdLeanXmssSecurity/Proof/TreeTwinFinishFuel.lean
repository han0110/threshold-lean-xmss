import ThresholdLeanXmssSecurity.Proof.TreeTwinFinishPass
import ThresholdLeanXmssSecurity.Proof.TreeTwinSegmentDefs

/-! # Syntactic exchange paths at the finishing Coin
Local answers and inboxes in these paths are arbitrary, as in `TreeTwinWithin`.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinFinishFuel
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- A prefix with exactly the specified number of exchanges. -/
inductive Reaches {α : Type} : ℕ → OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | zero (p) : Reaches 0 p
  | localAnswer {n} (q : (LocalSpec C).Domain) (k) (r : (LocalSpec C).Range q)
      (h : Reaches n (k r)) : Reaches n (.roll (.inl (.inl q)) k)
  | exchange {n} (out : Mail C E) (k) (inbox : Mail C E)
      (h : Reaches n (k inbox)) : Reaches (n + 1) (.roll (.inl (.inr out)) k)

/-- A returning path, needed to compose prefixes through an optional bind. -/
inductive Returns {α : Type} : ℕ → OracleComp (PartySpec C E RealSpec) (Option α) → α → Prop
  | pure (x) : Returns 0 (pure (some x)) x
  | localAnswer {n x} (q : (LocalSpec C).Domain) (k) (r : (LocalSpec C).Range q)
      (h : Returns n (k r) x) : Returns n (.roll (.inl (.inl q)) k) x
  | exchange {n x} (out : Mail C E) (k) (inbox : Mail C E)
      (h : Returns n (k inbox) x) : Returns (n + 1) (.roll (.inl (.inr out)) k) x

theorem _root_.ThresholdLeanXmssSecurity.TreeTwinWithin.reaches_le {α : Type} {m k : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)}
    (h : TreeTwinWithin m p) (hp : Reaches k p) : k ≤ m := by
  induction h generalizing k with
  | pure n out => cases hp; omega
  | queryLocal n q f h ih =>
    cases hp with
    | zero => omega
    | localAnswer _ _ r hr => exact ih r hr
  | round n out f h ih =>
    cases hp with
    | zero => omega
    | exchange _ _ inbox hr => exact Nat.add_le_add_right (ih inbox hr) 1

theorem Returns.bind {α β : Type} {j k : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} {x : α}
    (h : Returns j p x) (f : α → OracleComp (PartySpec C E RealSpec) (Option β))
    (hf : Reaches k (f x)) :
    Reaches (j + k) (p >>= fun o => match o with | none => Pure.pure none | some a => f a) := by
  induction h with
  | pure x => simpa using hf
  | localAnswer q g r h ih => exact .localAnswer q _ r (ih hf)
  | exchange out g inbox h ih =>
    rw [Nat.add_right_comm]
    exact .exchange out _ inbox (ih hf)

-- Prefix counterpart of TreeTwinWithin.local_bind.
theorem Reaches.local_bind {α β : Type} (n : ℕ) (p : OracleComp (LocalSpec C) α)
    (k : α → PartyM C E RealSpec β) (hk : ∀ a, Reaches n (k a).run) :
    Reaches n (localStep p >>= k).run := by
  simp only [localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM,
    bind_assoc, pure_bind, Option.elim_some]
  change Reaches n (liftComp p (PartySpec C E RealSpec) >>= fun a => (k a).run)
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
    exact .localAnswer q _ default (ih default)

theorem Reaches.oracle_bind {α β : Type} (n : ℕ) (p : OracleComp (RoSpec C) α)
    (k : α → PartyM C E RealSpec β) (hk : ∀ a, Reaches n (k a).run) :
    Reaches n (oracleStep p >>= k).run :=
  Reaches.local_bind n (liftComp p _) k hk

theorem Reaches.exchange_bind {α : Type} (n : ℕ) (out inbox : Mail C E)
    (f : Mail C E → PartyM C E RealSpec α)
    (ha : (C.parties.any fun j => Msg.isAbort (inbox j)) = false)
    (h : Reaches n (f inbox).run) : Reaches (n + 1) (ThresholdLeanXmss.exchange out >>= f).run := by
  have he : (ThresholdLeanXmss.exchange out >>= f).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>=
        exchangeResume f := by
    simp only [ThresholdLeanXmss.exchange, OptionT.run_bind, OptionT.lift, bind_assoc,
      OptionT.run_mk, pure_bind, Option.elimM]
    refine bind_congr fun inbox => ?_
    simp only [Option.elim]
    unfold exchangeResume
    split <;> simp_all
  rw [he]
  apply Reaches.exchange out _ inbox
  change Reaches n ((Pure.pure inbox : OracleComp (PartySpec C E RealSpec) _) >>= exchangeResume f)
  simp only [pure_bind]
  simpa only [exchangeResume, ha, Bool.false_eq_true, if_false] using h

/-- Constant shares interpolate for every committee. -/
theorem constant_open_agrees (K : Constants C E) (i : C.Party) (v : ℕ → E) :
    OpenAgreesN K i v 1 (fun _ => some (.elements [v 0])) := by
  intro j g hg
  have hg : g = 0 := by omega
  subst g
  have hs (j : C.Party) :
      openShareN i v (fun _ => some (.elements [v 0])) j 0 = v 0 := by
    simp [openShareN, Msg.elementAt]
  simp only [hs]
  simpa using (sum_lagrangeFirst_mul_eval K (Polynomial.C (v 0))
    (by simp) (K.point j)).symm

/-- The expansion oracle admits an answer outside the rejected pair. -/
theorem exists_challenge_hash (K : Constants C E) :
    ∃ h : HashOutput, elementOfHash K h ≠ 0 ∧ elementOfHash K h ≠ 1 := by
  have hc : 2 < Fintype.card E := by rw [card_field K]; decide
  have hn : ¬ (Finset.univ : Finset E) ⊆ {0, 1} := by
    intro h
    have := Finset.card_le_card h
    have : Fintype.card E ≤ 2 := this.trans (Finset.card_insert_le _ _ |>.trans (by simp))
    omega
  obtain ⟨e, _, he⟩ := Finset.not_subset.mp hn
  have he : e ≠ 0 ∧ e ≠ 1 := by simpa using he
  refine ⟨(hashSplit K).symm (e, default), ?_⟩
  have hh : elementOfHash K ((hashSplit K).symm (e, default)) = e := by
    rw [← hashSplit_fst, Equiv.apply_symm_apply]
  rw [hh]
  exact he

open TreeTwinLinked2 TreeTwinFinishPass

/-- The raw party program of the last halving, before suspension.
PartySpec-level port of TreeTwinFinishPass.finishing_body_program. -/
theorem finishing_body_program (K : Constants C E) (ctx : Context C) (width j : ℕ)
    (p : (ℕ → E) × (ℕ → E) × E)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C E × RunState C) (r : E) (st : RunState C) :
    treeStagesHalvingBody K ctx width j [] p finish out (r, st) =
      oracleStep (prssDraw ctx (elementCodec K) st.label 1 2) >>= fun w =>
        let claim := treeStagesHalvingUpdate K ctx width j p out.1 r
        ((prssRandomness ctx (elementCodec K) 0 2 >>= fun rnd =>
          reshare K ctx (elementCodec K) rnd
            (contextProductValues K ctx (finalProducts K ctx claim w.1)) 2).run (nextLabel st)) >>=
              finalAfterField K ctx claim w.1 finish := by
  simp only [treeStagesHalvingBody, treeStagesHalvingFold, List.foldlM_nil,
    StateT.run_bind, pure_bind]
  generalize treeStagesHalvingUpdate K ctx width j p out.1 r = claim
  rcases claim with ⟨a, b, c⟩
  unfold finalStep
  change (prssRandomness ctx (elementCodec K) 1 2 >>= _).run st >>= finish = _
  rw [prssRandomness_run, bind_assoc]
  congr 1
  funext w
  dsimp only [finalAfterField, finalAfterCoin, treeStagesSaltedDigest, finalVector,
    finalProducts, contextProductValues, realCheckGadgets]
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
    List.length_cons, List.length_nil]
  apply bind_congr
  intro rnd
  apply bind_congr
  intro q
  unfold finalAfterField
  simp only [treeStagesSaltedDigest, StateT.run_bind, bind_assoc]
  apply bind_congr
  intro salts
  apply bind_congr
  intro digest
  apply bind_congr
  intro coin
  unfold finalAfterCoin
  apply bind_congr
  intro opened
  apply bind_congr
  intro done
  cases done
  rfl

theorem salted_digest_reaches (K : Constants C E) (ctx : Context C) (st : RunState C)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput) :
    Reaches 1 (((treeStagesSaltedDigest K ctx).run st >>= finish).run) := by
  simp only [treeStagesSaltedDigest, realCheckGadgets]
  rw [prssRandomness_run, bind_assoc]
  apply Reaches.oracle_bind
  intro salts
  simp only [compareDigests, StateT.run_bind, StateT.run_get, StateT.run_lift,
    pure_bind, bind_assoc]
  apply Reaches.oracle_bind
  intro digests
  apply Reaches.exchange_bind 0 _ (fun _ => none)
  · simp [Msg.isAbort]
  · exact .zero _

theorem finishing_body_reaches (K : Constants C E) (ctx : Context C) (width j : ℕ)
    (p : (ℕ → E) × (ℕ → E) × E)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C E × RunState C) (r : E) (st : RunState C) :
    Reaches 2 (treeStagesHalvingBody K ctx width j [] p finish out (r, st)).run := by
  rw [finishing_body_program]
  apply Reaches.oracle_bind
  intro w
  dsimp only
  rw [prssRandomness_run, bind_assoc]
  apply Reaches.oracle_bind
  intro rnd
  rw [show rnd = (rnd.1, rnd.2) from rfl, reshare_run, bind_assoc]
  apply Reaches.exchange_bind 1 _ (fun _ => none)
  · simp [Msg.isAbort]
  · simp only [pure_bind, finalAfterField]
    apply salted_digest_reaches

theorem Reaches.hash_answer {α : Type} (n : ℕ) (q : Query C) (h : HashOutput)
    (f : HashOutput → PartyM C E RealSpec α) (hf : Reaches n (f h).run) :
    Reaches n (oracleStep (hashQuery q) >>= f).run := by
  exact .localAnswer (.inr (.inl q)) _ h hf

theorem challenge_tail_reaches {α : Type} (K : Constants C E) (n tag label : ℕ)
    (body : E × RunState C → PartyM C E RealSpec α) (values : List E) (st : RunState C)
    (hb : ∀ r, Reaches n (body (r, st)).run) :
    Reaches n (treeStagesChallengeTail K tag label body (values, st)).run := by
  obtain ⟨h, hh⟩ := exists_challenge_hash K
  unfold treeStagesChallengeTail
  apply Reaches.oracle_bind
  intro key
  have ht : challengeTries = (2 ^ 64 - 1) + 1 := by unfold challengeTries; omega
  rw [ht, findChallenge]
  simp only [oracleStep_bind, bind_assoc]
  apply Reaches.hash_answer n _ h
  cases hd : Classical.propDecidable (elementOfHash K h ≠ 0 ∧ elementOfHash K h ≠ 1) with
  | isTrue yes => simpa [oracleStep, localStep, liftComp_pure] using hb (elementOfHash K h)
  | isFalse no => exact False.elim (no hh)

theorem coinStep_within {α : Type} (K : Constants C E) (ctx : Context C)
    (rnd : PrssOutput C E) (st : RunState C)
    (next : List E × RunState C → PartyM C E RealSpec α) (k m : ℕ)
    (hn : ∀ values, Reaches k (next (values, nextLabel st)).run)
    (hw : TreeTwinWithinStep m (treeSimCoinStep K ctx rnd 1 st next)) : k + 1 ≤ m := by
  cases m with
  | zero => exact False.elim hw
  | succ m =>
    let v := conv K ctx rnd.1
    let inbox : Mail C E := fun _ => some (.elements [v 0])
    have ha : (C.parties.any fun j => Msg.isAbort (inbox j)) = false := by
      simp [inbox, Msg.isAbort]
    have hg : OpenAgreesN K ctx.self v 1 inbox := constant_open_agrees K ctx.self v
    have h := hw inbox
    change TreeTwinWithin m (exchangeResume (fun inbox =>
      require (OpenAgreesN K ctx.self v 1 inbox) >>= fun _ =>
        next (vector 1 (openValueN K ctx.self v inbox), nextLabel st)) inbox) at h
    simp only [exchangeResume, ha, Bool.false_eq_true, if_false, require, hg, if_pos,
      pure_bind] at h
    exact Nat.add_le_add_right (TreeTwinWithin.reaches_le h (hn _)) 1

open TreeTwinSavedSchedule TreeTwinSegment

/-- The live pivot has a syntactic three-exchange continuation. -/
theorem finishingCoin_within (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (openings : List (List (List Bit))) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (h : FinishingCoinLive K circuits settings top tree D A parameter openings δ a b) :
    ∃ i, i ∉ D.1 ∧ ∀ m, TreeTwinWithinStep m (a.1.2 i) → 3 ≤ m := by
  obtain ⟨q, rnd, sent, coinRnd, ⟨w, hw, hf⟩, live, _, _, _, _, prog, _⟩ := h
  obtain ⟨j, v₁, v₂, hp, _⟩ := hw.finishing_halving hf
  have hs := hw.state
  simp only [SavedState, hp] at hs
  have hend : halvSuffix (tupleCount w.caller.rest.circs) j = [] := by
    simpa only [hp, SavedPhase.Finishing] using hf
  have body := hs.1 q.pivotParty q.pivot.honest
  rw [hend] at body
  refine ⟨q.pivotParty, q.pivot.honest, ?_⟩
  intro m hm
  rw [prog] at hm
  simp only [treeSimCoinPartial, live q.pivotParty q.pivot.honest,
    if_true, treeSimCoinWaiting, if_neg q.pivot.honest] at hm
  apply coinStep_within K (localContext q.pivotParty) (coinRnd q.pivotParty)
    ((q.coinNext K D rnd δ sent).st₁ q.pivotParty)
    ((q.coinNext K D rnd δ sent).next₁ q.pivotParty) 2 m ?_ hm
  intro values
  change Reaches 2 (treeStagesChallengeTail K _ _ (q.body₁ q.pivotParty _) _).run
  apply challenge_tail_reaches
  intro r
  rw [body]
  exact finishing_body_reaches K _ _ _ _ _ _ _ _

/-- Actual reach and a live finishing Coin leave room for three more exchanges. -/
theorem finalSegment_fuel (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (state : A.State) (s : TreeSimState C)
    (n : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (parameter : PublicParameter) (openings : List (List (List Bit)))
    (δ : HiddenAddress C → Bit) (y : TreeSimState C)
    (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (reach : TreeStagesReach prims K circuits settings top tree D A x state s n a)
    (live : FinishingCoinLive K circuits settings top tree D A parameter openings δ (a.1, y) b) :
    n + 6 ≤ ceremonyFuel circuits settings := by
  obtain ⟨i, hi, hw⟩ := finishingCoin_within K circuits settings top tree D A parameter openings δ _ b live
  have h := hw _ (treeTwin_reach_within prims K circuits settings
    (treeTwinAfterSetupWithin K circuits settings) top tree D A x state s n a reach i hi)
  unfold ceremonyFuel setupRounds
  omega

end ThresholdLeanXmssSecurity.TreeTwinFinishFuel

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinWithin.reaches_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinWithin.reaches_le

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishFuel.Returns.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishFuel.Returns.bind

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishFuel.constant_open_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishFuel.constant_open_agrees

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishFuel.exists_challenge_hash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishFuel.exists_challenge_hash

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishFuel.finishing_body_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishFuel.finishing_body_program

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishFuel.finishing_body_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishFuel.finishing_body_reaches

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishFuel.challenge_tail_reaches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishFuel.challenge_tail_reaches

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishFuel.coinStep_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishFuel.coinStep_within

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishFuel.finishingCoin_within' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishFuel.finishingCoin_within

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishFuel.finalSegment_fuel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishFuel.finalSegment_fuel
