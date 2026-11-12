import ThresholdLeanXmssSecurity.Proof.TreeTwinPassPrefill
import ThresholdLeanXmssSecurity.Proof.TreeTwinSavedKinds

/-! # The actual finishing pass of the saved check
The last pure halving fold precedes the two field draws. Cached hidden blocks
and visible stream keys determine its term masks, and every live continuation
reads those cells during the complete party pass.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinFinishPass
open TreeTwinPrefill TreeTwinPassPrefill TreeTwinLinked2
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E)

/-- The two Shamir products in GS20 randomization. -/
def finalProducts (ctx : Context C) (claim : (ℕ → E) × (ℕ → E) × E)
    (w : Shares C E) : List (Product C E) :=
  [.shamir (fun _ => conv K ctx w 0) (fun _ => conv K ctx w 1) 1,
   .shamir (fun _ => conv K ctx w 0 + claim.1 0)
     (fun _ => conv K ctx w 1 + claim.2.1 0) 1]

/-- The last fold enters the mask draw before any further effect. -/
theorem finishing_body_program (ctx : Context C) (width j : ℕ)
    (p : (ℕ → E) × (ℕ → E) × E)
    (finish : Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (out : Shares C E × RunState C) (r : E) (st : RunState C) :
    free (advance (treeStagesHalvingBody K ctx width j [] p finish out (r, st)).run) =
      free (liftComp (prssDraw ctx (elementCodec K) st.label 1 2) (LocalSpec C)) >>= fun w =>
        let claim := treeStagesHalvingUpdate K ctx width j p out.1 r
        free (advance ((((prssRandomness ctx (elementCodec K) 0 2 >>= fun rnd =>
          reshare K ctx (elementCodec K) rnd
            (contextProductValues K ctx (finalProducts K ctx claim w.1)) 2).run (nextLabel st)) >>=
              finalAfterField K ctx claim w.1 finish).run)) := by
  simp only [treeStagesHalvingBody, treeStagesHalvingFold, List.foldlM_nil,
    StateT.run_bind, pure_bind]
  generalize treeStagesHalvingUpdate K ctx width j p out.1 r = claim
  rcases claim with ⟨a, b, c⟩
  unfold finalStep
  change free (advance (((prssRandomness ctx (elementCodec K) 1 2 >>= _).run st >>= finish).run)) = _
  rw [prssRandomness_run, bind_assoc]
  simp only [advance_oracleStep_bind, free_bind]
  congr 1
  funext w
  congr 1
  congr 1
  apply congrArg OptionT.run
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


-- Port of private TreeTwinPrefill.allowed_mapM_get (181–207).
private theorem allowed_mapM_get {ι α β : Type} {S : OracleSpec.{0, 0} ι}
    (allowed : (t : S.Domain) → S.Range t → Prop) (f : α → OracleComp S β)
    (xs : List α) (ys : List β) (h : TreeSimCheckAllowed allowed (xs.mapM f) ys) :
    ys.length = xs.length ∧ ∀ (n : ℕ) x, xs[n]? = some x →
      ∃ y, ys[n]? = some y ∧ TreeSimCheckAllowed allowed (f x) y := by
  induction xs generalizing ys with
  | nil =>
    have he : ys = [] := h.pure_inv
    subst ys
    exact ⟨rfl, by simp⟩
  | cons x xs ih =>
    simp only [List.mapM_cons] at h
    obtain ⟨y, hy, ht⟩ := h.bind_inv
    obtain ⟨tail, htail, he⟩ := ht.bind_inv
    have he : ys = y :: tail := he.pure_inv
    subst ys
    obtain ⟨length, each⟩ := ih tail htail
    refine ⟨by simp [length], ?_⟩
    intro n a ha
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      subst a
      exact ⟨y, rfl, hy⟩
    | succ n => exact each n a ha


/-- Initial cached terms, including the codec's padded tail. -/
def predictedTerms (D : C.Coalition) (h : HashCache C) (c : HiddenCache C)
    (ctx : Context C) (label idx count : ℕ) : Shares C E := fun T =>
  if ctx.self ∈ C.holders T then
    treeStagesFieldResult K count (treeStagesDecode K count fun g =>
      if Hidden D (.term T) then (c ((.term T, ctx.prss.term T), label, idx, g.val)).getD 0
      else prims.aes.eval (truncateHash ((h (.streamKey (ctx.prss.term T))).getD 0))
        (label, idx, g.val))
  else fun _ => 0

/-- Every visible held term queries its AES key, when the field width is positive. -/
theorem prss_terms_hash_read {α : Type} (D : C.Coalition) (ctx : Context C)
    (label idx count : ℕ) (positive : 0 < count)
    (k : PrssOutput C E → OracleComp (WorldSpec C) α) (s : TreeSimState C)
    (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)) >>= k)).run s)) :
    ∀ T, ctx.self ∈ C.holders T → ¬ Hidden D (.term T) →
      r.2.1.1 (.streamKey (ctx.prss.term T)) ≠ none := by
  obtain ⟨rnd, hdraw, _⟩ := (treeLockstep_logged_run_allowed prims D _ s r run).bind_inv
  have hr := free_ro_allowed (TreeLockstepWorldStreams prims D r.2.1) _ rnd hdraw
  unfold prssDraw at hr
  obtain ⟨terms, hterms, _⟩ := hr.bind_inv
  intro T held visible
  obtain ⟨_, each⟩ := allowed_mapM_get _ _ C.terms terms hterms
  obtain ⟨values, _, hv⟩ := each (C.terms.idxOf T) T (List.getElem?_idxOf (mem_terms T))
  simp only [if_pos held] at hv
  obtain ⟨bits, hb, _⟩ := hv.bind_inv
  have answers := (treeLockstep_prg_stream_answers prims D r.2.1 _ (fun _ _ h => h)
    (.term T) (ctx.prss.term T) label idx (elementBits * count) bits hb).1
  have first := answers 0 (by unfold elementBits; omega)
  simp only [TreeLockstepStreamAnswer, visible, if_false] at first
  obtain ⟨key, hk, _⟩ := first
  rw [hk]
  exact Option.some_ne_none _

/-- The actual field draw is determined by its initially cached term cells. -/
theorem prssDraw_predicted (D : C.Coalition) (ctx : Context C) (label idx count : ℕ)
    (s : TreeSimState C) (r : PrssOutput C E × TreeSimState C)
    (hidden : ∀ T, ctx.self ∈ C.holders T → Hidden D (.term T) →
      ∀ g : Fin (count * elementBits), s.1.2 ((.term T, ctx.prss.term T), label, idx, g.val) ≠ none)
    (visible : ∀ T, ctx.self ∈ C.holders T → ¬ Hidden D (.term T) →
      s.1.1 (.streamKey (ctx.prss.term T)) ≠ none)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)))).run s)) :
    r.1.1 = predictedTerms prims K D s.1.1 s.1.2 ctx label idx count := by
  have growH := treeSim_logged_grows prims D _ s r run
  have growC := treeSim_hidden_grows_logged prims D _ s r run
  have hr := free_ro_allowed (TreeLockstepWorldStreams prims D r.2.1) _ r.1
    (treeLockstep_logged_run_allowed prims D _ s r run)
  unfold prssDraw at hr
  obtain ⟨terms, hterms, rest⟩ := hr.bind_inv
  obtain ⟨pairs, _, he⟩ := rest.bind_inv
  have result := he.pure_inv
  obtain ⟨_, each⟩ := allowed_mapM_get _ _ C.terms terms hterms
  funext T
  obtain ⟨values, hv, hvalues⟩ := each (C.terms.idxOf T) T (List.getElem?_idxOf (mem_terms T))
  have val : r.1.1 T = values := by
    rw [result]
    simp [List.getD_eq_getElem?_getD, hv]
  rw [val]
  by_cases held : ctx.self ∈ C.holders T
  · simp only [if_pos held] at hvalues
    obtain ⟨bits, hb, he⟩ := hvalues.bind_inv
    have valueEq : values = fun g => K.encode.symm fun b => bits (elementBits * g + b) := he.pure_inv
    have answers := treeLockstep_prg_stream_answers prims D r.2.1 _ (fun _ _ h => h)
      (.term T) (ctx.prss.term T) label idx (elementBits * count) bits hb
    have bitEq (g : Fin (count * elementBits)) : bits g.val =
        if Hidden D (.term T) then (s.1.2 ((.term T, ctx.prss.term T), label, idx, g.val)).getD 0
        else prims.aes.eval (truncateHash ((s.1.1 (.streamKey (ctx.prss.term T))).getD 0))
          (label, idx, g.val) := by
      have ha := answers.1 g.val (by simpa only [Nat.mul_comm] using g.isLt)
      by_cases hh : Hidden D (.term T)
      · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (hidden T held hh g)
        have ha : r.2.1.2 ((.term T, ctx.prss.term T), label, idx, g.val) = some (bits g.val) := by
          simpa only [TreeLockstepStreamAnswer, hh, if_true] using ha
        have eq := Option.some.inj ((growC hv).symm.trans ha)
        simp [hh, hv, eq]
      · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp (visible T held hh)
        simp only [TreeLockstepStreamAnswer, hh, if_false] at ha
        obtain ⟨v', hv', ha⟩ := ha
        have eq := Option.some.inj ((growH hv).symm.trans hv')
        simpa [hh, hv, ← eq] using ha
    funext g
    rw [valueEq]
    simp only [predictedTerms, if_pos held, treeStagesFieldResult]
    by_cases hg : g < count
    · rw [dif_pos hg, treeStagesDecode_apply]
      congr 1
      funext b
      have hb : elementBits * g + b.val < count * elementBits := by
        have := (finProdFinEquiv (⟨g, hg⟩, b)).isLt
        change b.val + elementBits * g < count * elementBits at this
        omega
      have index : finProdFinEquiv (⟨g, hg⟩, b) =
          (⟨elementBits * g + b.val, hb⟩ : Fin (count * elementBits)) := by
        apply Fin.ext
        simp [finProdFinEquiv, Nat.add_comm]
      rw [index]
      exact bitEq ⟨elementBits * g + b.val, hb⟩
    · rw [dif_neg hg]
      congr 1
      funext b
      apply answers.2
      have hm := Nat.mul_le_mul_right elementBits (Nat.le_of_not_gt hg)
      rw [Nat.mul_comm g elementBits, Nat.mul_comm count elementBits] at hm
      omega
  · simp only [if_neg held] at hvalues
    simpa only [predictedTerms, if_neg held] using hvalues.pure_inv

/-- Erasing the log preserves the same initial-cache prediction. -/
theorem prssDraw_predicted_stream (D : C.Coalition) (ctx : Context C) (label idx count : ℕ)
    (s : HashCache C × HiddenCache C) (r : PrssOutput C E × (HashCache C × HiddenCache C))
    (hidden : ∀ T, ctx.self ∈ C.holders T → Hidden D (.term T) →
      ∀ g : Fin (count * elementBits), s.2 ((.term T, ctx.prss.term T), label, idx, g.val) ≠ none)
    (visible : ∀ T, ctx.self ∈ C.holders T → ¬ Hidden D (.term T) →
      s.1 (.streamKey (ctx.prss.term T)) ≠ none)
    (run : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)))).run s)) :
    r.1.1 = predictedTerms prims K D s.1 s.2 ctx label idx count := by
  rw [← treeSimLoggedWorld_erase prims D _ s [], support_map] at run
  obtain ⟨u, hu, rfl⟩ := run
  exact prssDraw_predicted prims K D ctx label idx count (s, []) u hidden visible hu

/-- Visible-term reads in the stream world, with the log erased. -/
theorem prss_terms_hash_read_stream {α : Type} (D : C.Coalition) (ctx : Context C)
    (label idx count : ℕ) (positive : 0 < count)
    (k : PrssOutput C E → OracleComp (WorldSpec C) α) (s : HashCache C × HiddenCache C)
    (r : α × (HashCache C × HiddenCache C))
    (run : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) label idx count) (LocalSpec C)) >>= k)).run s)) :
    ∀ T, ctx.self ∈ C.holders T → ¬ Hidden D (.term T) →
      r.2.1 (.streamKey (ctx.prss.term T)) ≠ none := by
  rw [← treeSimLoggedWorld_erase prims D _ s [], support_map] at run
  obtain ⟨u, hu, rfl⟩ := run
  exact prss_terms_hash_read prims K D ctx label idx count positive k (s, []) u hu

/-- Both cache components read by one live party's finishing mask draw. -/
def FinishingReads (D : C.Coalition) (ctx : Context C) (label : ℕ)
    (s : HashCache C × HiddenCache C) : Prop :=
  ∀ T, ctx.self ∈ C.holders T →
    (Hidden D (.term T) → ∀ g < 2 * elementBits,
      s.2 ((.term T, ctx.prss.term T), label, 1, g) ≠ none) ∧
    (¬ Hidden D (.term T) → s.1 (.streamKey (ctx.prss.term T)) ≠ none)

private theorem finishingReads_mono (D : C.Coalition) (ctx : Context C) (label : ℕ)
    {s t : HashCache C × HiddenCache C} (hh : s.1 ≤ t.1) (hc : s.2 ≤ t.2)
    (h : FinishingReads D ctx label s) : FinishingReads D ctx label t := by
  intro T held
  refine ⟨fun hidden g hg => ?_, fun visible => ?_⟩
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((h T held).1 hidden g hg)
    rw [hc hv]
    exact Option.some_ne_none _
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp ((h T held).2 visible)
    rw [hh hv]
    exact Option.some_ne_none _

/-- The complete actual pass after coin delivery reads every cell of any
party whose coin output and covered cached challenge both accept. -/
theorem finishing_pass_reads_stream (D : C.Coalition)
    (ctx : C.Party → Context C) (width j : ℕ)
    (p : C.Party → (ℕ → E) × (ℕ → E) × E)
    (finish : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (prior : C.Party → Shares C E × RunState C) (tag hashLabel : C.Party → ℕ)
    (coinOut : C.Party → Option (List E × RunState C))
    (base : HashCache C) (s : HashCache C × HiddenCache C)
    (r : (C.Party → Step C E RealSpec TreeOutput) × (HashCache C × HiddenCache C))
    (base_le : base ≤ s.1)
    (run : r ∈ support ((simulateQ (streamWorld prims D)
      (treeSimResumeAll (fun i => treeStagesChallengeTail K (tag i) (hashLabel i)
        (treeStagesHalvingBody K (ctx i) width j [] (p i) (finish i) (prior i))) coinOut)).run s))
    (i : C.Party) (values : List E) (st : RunState C) (challenge : E)
    (coin : coinOut i = some (values, st))
    (covered : TreeStagesChallengeCovered K base (tag i) (hashLabel i) values)
    (accept : treeStagesCachedChallenge K base (tag i) (hashLabel i) values = some challenge) :
    FinishingReads D (ctx i) st.label r.2 := by
  unfold treeSimResumeAll at run
  rw [free_sequenceFin, simulateQ_sequenceFin] at run
  apply sequenceFin_establish _ (fun t => base ≤ t.1) (FinishingReads D (ctx i) st.label)
    (fun k t u hu ht => ht.trans (treeSim_stream_grows prims D _ t u hu))
    (fun k t u hu ht => finishingReads_mono D (ctx i) st.label
      (treeSim_stream_grows prims D _ t u hu) (treeSim_hidden_grows prims D _ t u hu) ht)
    i ?_ s r run base_le
  intro t u hu ht
  simp only [coin, treeSimResume] at hu
  rw [treeStages_challenge_tail_factor] at hu
  simp only [simulateQ_bind, StateT.run_bind] at hu
  rw [treeStages_challengeQuery_replay prims K D _ _ _ t
    (treeStages_challengeCovered_mono K ht _ _ _ covered),
    ← treeStages_cachedChallenge_mono K ht _ _ _ covered, accept, pure_bind] at hu
  simp only [treeSimResume] at hu
  rw [finishing_body_program] at hu
  intro T held
  exact ⟨fun hidden g hg => prss_terms_read_stream prims K D (ctx i) st.label 1 2 _ t u hu
      T held hidden g (by simpa [Nat.mul_comm] using hg),
    prss_terms_hash_read_stream prims K D (ctx i) st.label 1 2 (by omega) _ t u hu T held⟩

/-- The logged complete pass has exactly the same read certificate. -/
theorem finishing_pass_reads (D : C.Coalition)
    (ctx : C.Party → Context C) (width j : ℕ)
    (p : C.Party → (ℕ → E) × (ℕ → E) × E)
    (finish : C.Party → Unit × RunState C → PartyM C E RealSpec TreeOutput)
    (prior : C.Party → Shares C E × RunState C) (tag hashLabel : C.Party → ℕ)
    (coinOut : C.Party → Option (List E × RunState C))
    (base : HashCache C) (s : TreeSimState C)
    (r : (C.Party → Step C E RealSpec TreeOutput) × TreeSimState C)
    (base_le : base ≤ s.1.1)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (treeSimResumeAll (fun i => treeStagesChallengeTail K (tag i) (hashLabel i)
        (treeStagesHalvingBody K (ctx i) width j [] (p i) (finish i) (prior i))) coinOut)).run s))
    (i : C.Party) (values : List E) (st : RunState C) (challenge : E)
    (coin : coinOut i = some (values, st))
    (covered : TreeStagesChallengeCovered K base (tag i) (hashLabel i) values)
    (accept : treeStagesCachedChallenge K base (tag i) (hashLabel i) values = some challenge) :
    FinishingReads D (ctx i) st.label r.2.1 := by
  apply finishing_pass_reads_stream prims K D ctx width j p finish prior tag hashLabel coinOut
    base s.1 (r.1, r.2.1) base_le ?_ i values st challenge coin covered accept
  rw [← treeSimLoggedWorld_erase prims D _ s.1 s.2, support_map]
  exact ⟨r, run, rfl⟩

/-- Recover the bit translation after both encoded field regions. -/
def twoFieldCacheDelta (D : C.Coalition) (l₀ i₀ n₀ l₁ i₁ n₁ : ℕ)
    (old : HiddenAddress C → Bit) (c₁ c₂ : HiddenCache C) : HiddenAddress C → Bit :=
  treeStagesFieldCacheDelta D l₁ i₁ n₁
    (treeStagesFieldCacheDelta D l₀ i₀ n₀ old c₁ c₂) c₁ c₂

/-- Both block certificates and their joint frame recover the exact cache relation. -/
theorem twoFieldCaches_related (D : C.Coalition) (l₀ i₀ n₀ l₁ i₁ n₁ : ℕ)
    (δ₀ : KeyName C → Fin n₀ → E) (δ₁ : KeyName C → Fin n₁ → E)
    (old : HiddenAddress C → Bit) (base₁ base₂ c₁ c₂ : HiddenCache C)
    (h : TwoFieldCaches K D l₀ i₀ n₀ l₁ i₁ n₁ δ₀ δ₁ base₁ base₂ c₁ c₂)
    (rel : TreeSimHiddenRel old base₁ base₂) :
    TreeSimHiddenRel (twoFieldCacheDelta D l₀ i₀ n₀ l₁ i₁ n₁ old c₁ c₂) c₁ c₂ := by
  have block (label idx count : ℕ) (δ : KeyName C → Fin count → E)
      (hb : TreeStagesFieldBlock K D label idx count δ c₁ c₂) (x : HiddenAddress C)
      (hx : TreeStagesFieldRegion D label idx count x) (previous : HiddenAddress C → Bit) :
      c₂ x = (c₁ x).map (fun v => v + treeStagesFieldCacheDelta D label idx count previous c₁ c₂ x) := by
    rcases x with ⟨⟨name, key⟩, lab, ix, pos⟩
    rcases hx with ⟨hh, hl, hi, hp⟩
    dsimp only at hl hi hp
    subst lab; subst ix
    have region : TreeStagesFieldRegion D label idx count ((name, key), label, idx, pos) :=
      ⟨hh, rfl, rfl, hp⟩
    rcases hb name key hh with hf | ⟨bits, h₁, h₂⟩
    · simp [treeStagesFieldCacheDelta, region, hf.1 ⟨pos, hp⟩, hf.2 ⟨pos, hp⟩]
    · simp [treeStagesFieldCacheDelta, region, h₁ ⟨pos, hp⟩, h₂ ⟨pos, hp⟩]

  intro x
  by_cases h₁ : TreeStagesFieldRegion D l₁ i₁ n₁ x
  · exact block l₁ i₁ n₁ δ₁ h.second x h₁ _
  · simp only [twoFieldCacheDelta, treeStagesFieldCacheDelta, if_neg h₁]
    by_cases h₀ : TreeStagesFieldRegion D l₀ i₀ n₀ x
    · exact block l₀ i₀ n₀ δ₀ h.first x h₀ old
    · simp only [if_neg h₀, h.frame₁ x h₀ h₁, h.frame₂ x h₀ h₁]
      exact rel x

/-- Neither field region changes a visible-key translation. -/
theorem twoFieldCacheDelta_visible (D : C.Coalition) (l₀ i₀ n₀ l₁ i₁ n₁ : ℕ)
    (old : HiddenAddress C → Bit) (c₁ c₂ : HiddenCache C)
    (visible : ∀ x, ¬ Hidden D x.1.1 → old x = 0) :
    ∀ x, ¬ Hidden D x.1.1 → twoFieldCacheDelta D l₀ i₀ n₀ l₁ i₁ n₁ old c₁ c₂ x = 0 :=
  treeStages_fieldCacheDelta_visible D l₁ i₁ n₁ _ c₁ c₂
    (treeStages_fieldCacheDelta_visible D l₀ i₀ n₀ old c₁ c₂ visible)

/-- Labels beyond both regions retain their original translation. -/
theorem twoFieldCacheDelta_future (D : C.Coalition) (l₀ i₀ n₀ l₁ i₁ n₁ bound : ℕ)
    (old : HiddenAddress C → Bit) (c₁ c₂ : HiddenCache C)
    (after₀ : l₀ < bound) (after₁ : l₁ < bound) (future : TreeSimFutureZero bound old) :
    TreeSimFutureZero bound (twoFieldCacheDelta D l₀ i₀ n₀ l₁ i₁ n₁ old c₁ c₂) := by
  intro x hx
  have hn₀ : ¬ TreeStagesFieldRegion D l₀ i₀ n₀ x := fun h => by have := h.2.1; omega
  have hn₁ : ¬ TreeStagesFieldRegion D l₁ i₁ n₁ x := fun h => by have := h.2.1; omega
  simp [twoFieldCacheDelta, treeStagesFieldCacheDelta, hn₀, hn₁, future x hx]

/-- The joint frame preserves empty future labels beyond both field regions. -/
theorem twoFieldCaches_future (D : C.Coalition) (l₀ i₀ n₀ l₁ i₁ n₁ bound : ℕ)
    (δ₀ : KeyName C → Fin n₀ → E) (δ₁ : KeyName C → Fin n₁ → E)
    (base₁ base₂ c₁ c₂ : HiddenCache C)
    (h : TwoFieldCaches K D l₀ i₀ n₀ l₁ i₁ n₁ δ₀ δ₁ base₁ base₂ c₁ c₂)
    (after₀ : l₀ < bound) (after₁ : l₁ < bound)
    (future₁ : TreeSimFutureEmpty bound base₁) (future₂ : TreeSimFutureEmpty bound base₂) :
    TreeSimFutureEmpty bound c₁ ∧ TreeSimFutureEmpty bound c₂ := by
  have outside (x : HiddenAddress C) (hx : bound ≤ x.2.1) :
      ¬ TreeStagesFieldRegion D l₀ i₀ n₀ x ∧ ¬ TreeStagesFieldRegion D l₁ i₁ n₁ x := by
    constructor <;> intro h <;> have := h.2.1 <;> omega
  exact ⟨fun x hx => (h.frame₁ x (outside x hx).1 (outside x hx).2).trans (future₁ x hx),
    fun x hx => (h.frame₂ x (outside x hx).1 (outside x hx).2).trans (future₂ x hx)⟩

/-- Once all honest parties are live, partial waiting is full waiting. -/
theorem extendMultPartial_allLive {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (live : C.Party → Bool) (count : ℕ) (rnd : C.Party → PrssOutput C E)
    (v : C.Party → ℕ → E) (st : C.Party → RunState C)
    (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α)
    (allLive : ∀ i, i ∉ D.1 → live i = true) :
    treeSimExtendMultPartial K D ctx live count rnd v st k =
      treeSimExtendMultWaiting K D ctx count rnd v st k := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [treeSimExtendMultPartial, treeSimExtendMultWaiting, hi]
  · simp [treeSimExtendMultPartial, allLive i hi]

end ThresholdLeanXmssSecurity.TreeTwinFinishPass

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishPass.finishing_body_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishPass.finishing_body_program

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishPass.prss_terms_hash_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishPass.prss_terms_hash_read

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishPass.prssDraw_predicted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishPass.prssDraw_predicted

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishPass.prssDraw_predicted_stream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishPass.prssDraw_predicted_stream

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishPass.prss_terms_hash_read_stream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishPass.prss_terms_hash_read_stream

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishPass.finishing_pass_reads_stream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishPass.finishing_pass_reads_stream

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishPass.finishing_pass_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishPass.finishing_pass_reads

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishPass.twoFieldCaches_related' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishPass.twoFieldCaches_related

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishPass.twoFieldCacheDelta_visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishPass.twoFieldCacheDelta_visible

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishPass.twoFieldCacheDelta_future' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishPass.twoFieldCacheDelta_future

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishPass.twoFieldCaches_future' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishPass.twoFieldCaches_future

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinFinishPass.extendMultPartial_allLive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeTwinFinishPass.extendMultPartial_allLive
