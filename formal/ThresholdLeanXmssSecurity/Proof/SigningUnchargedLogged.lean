import ThresholdLeanXmssSecurity.Proof.SigningPartnerBound

/-!
# The uncharged lane on the log of the run

`SigningPartnerBoundProof.hiddenCoreAt_of_logged` needs `UnchargedLaneBoundLogged`. This module
reduces it to two named claims.

## The joint run

`jointRun` runs `verifyFinal` under `loggedImpl`. So one execution holds both logs.

* `jointRun_logged` drops the candidates and gives `loggedRun` exactly.
* `jointRun_verify` drops the call log and gives `verifyRun` exactly.

So `guess_hiddenInputHit` holds on the joint run with no coupling. The opening candidates need the
state at call time (`Released`), which the call log does not hold. So the flag lives on the joint
run.

## The fresh partner

`FreshSelection` says that the first call of the selected input in the log is honest.

* `monitor_hit_of_partner` shows the hit of the monitor on any log with a fresh honest selection
  and a forged input at the same key with the same valid digest. Every earlier honest valid call at
  the key must be the forged call. The final verification can call first. Then it installs the
  forged digest, and the selection meets it.
* `freshPartnerLink_of_classification` gives `BottomPartnerLogged` or `AlternativeCommitment` on
  the joint run. It uses the agreement of the log with the cache (`LogConsistent`), `Covered`, and
  the decoding of the forged digest of a win.
* `SelectionClassification` states the required property of the honest calls at the key.

## The flag

`UnchargedFlag` is the input-side `HiddenInputHit`, a bottom partner with a selection that is not
fresh (leanVM lane 2), or a top partner that no bottom ceremony resolves.
`unchargedFlag_of_win` shows that every uncharged win on the log raises it.
`UnchargedFlagCoupling` is the `hcouple` premise of `probEvent_le_of_capped` for this flag.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningUnchargedLoggedProof

open LeanXmss ThresholdLeanXmss SigningHitLaneProof SigningCostProof SigningPartnerBoundProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- An outcome of `jointRun`. -/
abbrev JointOutcome (C : Committee) :=
  (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) × List (SigningOpeningProof.HiddenKey × Digest)) ×
    LoggedState C

/-- One run with both logs. `verifyFinal` keeps the unreleased candidates, and `loggedImpl` logs
each world call with its answer. -/
def jointRun (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) : ProbComp (JointOutcome C) :=
  (simulateQ (loggedImpl prims) (SigningGuessLinkProof.verifyFinal A x)).run loggedInit

set_option maxRecDepth 100000 in
/-- A run with final metadata splits into the top-tree run, the adversary run and the
verification with its freshness check. The same decomposition applies to either counted or
logged world handlers. -/
theorem verifyFinal_support {σ : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (initial : σ)
    (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (r : (((Bool × Bool) × Option (TopTree × TsigState C × Forgery)) ×
      List (SigningOpeningProof.HiddenKey × Digest)) × σ)
    (hr : r ∈ support ((simulateQ impl (SigningGuessLinkProof.verifyFinal A x)).run initial))
    (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hm : r.1.1.2 = some (top, state, forgery)) :
    ∃ (p : Option TreeOutput × σ)
      (q : (Forgery × (TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) ×
        List (SigningOpeningProof.HiddenKey × Digest)) × σ)
      (v : ((Bool × TsigState C × Forgery) × List (SigningOpeningProof.HiddenKey × Digest)) × σ),
      p ∈ support ((simulateQ impl (SigningSecurityProof.liftFree
        (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top))).run initial) ∧
      p.1 = some (.top top) ∧
      q ∈ support ((simulateQ impl ((simulateQ (SigningOpeningProof.openingOracles x
        (SigningGuessProof.receiptDealt x top)) (A ⟨top.root, x.1⟩ top)).run
          ((SigningCoreProof.tsigInit, false), ∅, []))).run p.2) ∧
      v ∈ support ((simulateQ impl (SigningGuessLinkProof.tsigFinishLogged
        (SigningGuessProof.receiptDealt x top) q.1.2.2.1 (q.1.1, q.1.2.1.1))).run q.2) ∧
      r = ((((v.1.1.1, q.1.2.1.2), some (top, v.1.1.2.1, v.1.1.2.2)),
        q.1.2.2.2 ++ v.1.2), v.2) := by
  unfold SigningGuessLinkProof.verifyFinal at hr
  dsimp only at hr
  rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
      (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
      SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
    referenceTree_φ _ _ _ _] at hr
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨p, hp, hr⟩ := hr
  rcases hp1 : p.1 with _ | (top' | tree)
  · rw [hp1] at hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr] at hm
    cases hm
  swap
  · rw [hp1] at hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr] at hm
    cases hm
  rw [hp1] at hr
  dsimp only at hr
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨q, hq, hr⟩ := hr
  rw [simulateQ_map, StateT.run_map, support_map] at hr
  obtain ⟨v, hv, rfl⟩ := hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hm
  obtain ⟨rfl, -, -⟩ := hm
  with_reducible refine ⟨p, q, v, hp, hp1, ?_, ?_, rfl⟩
  · simpa only [SigningGuessProof.receiptDealt, dealtWith] using hq
  · simpa only [SigningGuessProof.receiptDealt] using hv

/-- The joint run without the candidates is `loggedRun`. -/
theorem jointRun_logged (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1.1, z.2)) <$> jointRun prims A x = loggedRun prims A x := by
  unfold jointRun loggedRun
  rw [← SigningGuessLinkProof.verifyFinal_forget, simulateQ_map, StateT.run_map]
  rfl

/-- The joint run without the call log is `verifyRun`. -/
theorem jointRun_verify (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) :
    (fun z => (z.1, z.2.1)) <$> jointRun prims A x = SigningGuessLinkProof.verifyRun prims A x :=
  SigningCoreProof.simulateQ_run_forget _ _ (fun t s b => by simp [loggedImpl, Functor.map_map]) _ _ _


set_option maxRecDepth 100000 in
/-- The joint run without the call log and the candidates is `exposedRun`. -/
theorem mem_exposedRun_of_joint (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) :
    (w.1.1, w.2.1) ∈ support (SigningDescentProof.exposedRun prims A x) := by
  rw [← SigningGuessLinkProof.verifyRun_forget, ← jointRun_verify, Functor.map_map, support_map, Set.mem_image]
  with_reducible exact ⟨w, hw, rfl⟩

set_option maxRecDepth 100000 in
theorem mem_verifyRun_of_joint (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) :
    (w.1, w.2.1) ∈ support (SigningGuessLinkProof.verifyRun prims A x) := by
  rw [← jointRun_verify, support_map, Set.mem_image]
  with_reducible exact ⟨w, hw, rfl⟩

section MonitorList

variable (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex)

/-- A hash entry holds the input, the digest of the answer, and `true` on the free copy. -/
abbrev Entry := XmssSecurity.HashInput × XmssSecurity.Digest × Bool

theorem foldl_hit (L : List Entry) (m : Monitor) (h : m.hit = true) :
    (L.foldl (Monitor.step keyOf) m).hit = true := by
  induction L generalizing m with
  | nil => exact h
  | cons entry L ih =>
    refine ih _ ?_
    unfold Monitor.step
    split_ifs
    · exact h
    · exact Monitor.fresh_hit keyOf m _ _ _ h

theorem foldl_seen_mono (L : List Entry) (m : Monitor) :
    m.seen ⊆ (L.foldl (Monitor.step keyOf) m).seen := by
  induction L generalizing m with
  | nil => exact le_rfl
  | cons entry L ih =>
    exact ((Set.subset_insert _ _).trans (Monitor.step_seen keyOf m entry)).trans (ih _)

theorem mem_foldl_seen (L : List Entry) (m : Monitor) (entry : Entry) (h : entry ∈ L) :
    entry.1 ∈ (L.foldl (Monitor.step keyOf) m).seen := by
  induction L generalizing m with
  | nil => simp at h
  | cons head L ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact foldl_seen_mono keyOf L _ (Monitor.step_seen keyOf m entry (Set.mem_insert _ _))
    · exact ih _ h

theorem foldl_seen_sub (L : List Entry) (m : Monitor) (input : XmssSecurity.HashInput)
    (h : input ∈ (L.foldl (Monitor.step keyOf) m).seen) : input ∈ m.seen ∨ ∃ entry ∈ L, entry.1 = input := by
  induction L generalizing m with
  | nil => exact Or.inl h
  | cons head L ih =>
    rcases ih _ h with h | ⟨entry, hentry, rfl⟩
    · unfold Monitor.step at h
      split_ifs at h
      · exact Or.inl h
      · rw [Monitor.fresh_seen] at h
        rcases h with rfl | h
        · exact Or.inr ⟨head, List.mem_cons_self, rfl⟩
        · exact Or.inl h
    · exact Or.inr ⟨entry, List.mem_cons_of_mem _ hentry, rfl⟩

variable (e : XmssSecurity.LeafIndex) (forged : XmssSecurity.HashInput) (digest : XmssSecurity.Digest)

/-- A fresh call at another key or at no key keeps the state at `e`. -/
theorem fresh_state_at (m : Monitor) (input : XmssSecurity.HashInput) (d : XmssSecurity.Digest) (honest : Bool)
    (hk : keyOf input ≠ some e) :
    (m.fresh keyOf input d honest).state.signed e = m.state.signed e ∧
      (m.fresh keyOf input d honest).state.pending e = m.state.pending e ∧
      (m.fresh keyOf input d honest).seen = insert input m.seen ∧
      ((m.fresh keyOf input d honest).hit = true ∨ (m.fresh keyOf input d honest).hit = m.hit) := by
  cases hk' : keyOf input with
  | none => rw [m.fresh_none keyOf input d honest hk']; simp
  | some e' =>
    have he : e ≠ e' := fun h => hk (h ▸ hk')
    cases hs : m.state.signed e' with
    | none =>
      rw [m.fresh_unsigned keyOf input d honest e' hk' hs]
      split_ifs <;>
        simp [XmssSecurity.EncodingMonitor.State.install, XmssSecurity.EncodingMonitor.State.addPending,
          Function.update_of_ne he]; tauto
    | some target => rw [m.fresh_signed keyOf input d honest e' hk' target hs]; simp; tauto

/-- The state before the selection. The monitor has hit, or `e` is unsigned and holds the forged
digest as pending once the forged input is seen, or `e` is signed with the forged digest. -/
def PreInv (m : Monitor) : Prop :=
  m.hit = true ∨ (m.state.signed e = none ∧ (forged ∈ m.seen → digest ∈ m.state.pending e)) ∨
    m.state.signed e = some digest

theorem preInv_step (hforged : keyOf forged = some e) (hvalid : XmssSecurity.TargetSum.ValidDigest digest)
    (m : Monitor) (hm : PreInv e forged digest m) (entry : Entry)
    (hcons : entry.1 = forged → entry.2.1 = digest)
    (hforeign : entry.2.2 = true → keyOf entry.1 = some e → XmssSecurity.TargetSum.ValidDigest entry.2.1 →
      entry.1 = forged) :
    PreInv e forged digest (m.step keyOf entry) := by
  obtain ⟨input, d, honest⟩ := entry
  simp only at hcons hforeign
  unfold Monitor.step
  split_ifs with hseen
  · exact hm
  by_cases hk : keyOf input = some e
  · rcases hm with hm | ⟨hs, hpend⟩ | hs
    · exact Or.inl (Monitor.fresh_hit keyOf m _ _ _ hm)
    · rw [m.fresh_unsigned keyOf input d honest e hk hs]
      split_ifs with hv hh
      · obtain rfl := hforeign hh hk hv
        obtain rfl := hcons rfl
        right; right
        simp [XmssSecurity.EncodingMonitor.State.install]
      · right; left
        refine ⟨by simpa [XmssSecurity.EncodingMonitor.State.addPending] using hs, fun hf => ?_⟩
        simp only [XmssSecurity.EncodingMonitor.State.addPending, Function.update_self, Finset.mem_insert]
        rcases hf with rfl | hf
        · exact Or.inl (hcons rfl).symm
        · exact Or.inr (hpend hf)
      · right; left
        refine ⟨hs, fun hf => ?_⟩
        rcases hf with rfl | hf
        · exact (hv ((hcons rfl) ▸ hvalid)).elim
        · exact hpend hf
    · rw [m.fresh_signed keyOf input d honest e hk digest hs]
      exact Or.inr (Or.inr hs)
  · obtain ⟨hsigned, hpending, hseen', hhit⟩ := fresh_state_at keyOf e m input d honest hk
    have hne : input ≠ forged := fun h => hk (h ▸ hforged)
    rcases hm with hm | ⟨hs, hpend⟩ | hs
    · exact Or.inl (Monitor.fresh_hit keyOf m _ _ _ hm)
    · right; left
      refine ⟨hsigned.trans hs, fun hf => ?_⟩
      rw [hseen'] at hf
      rw [hpending]
      rcases hf with h | hf
      · exact (hne h.symm).elim
      · exact hpend hf
    · exact Or.inr (Or.inr (hsigned.trans hs))

theorem preInv_foldl (hforged : keyOf forged = some e) (hvalid : XmssSecurity.TargetSum.ValidDigest digest)
    (L : List Entry) (m : Monitor) (hm : PreInv e forged digest m)
    (hcons : ∀ entry ∈ L, entry.1 = forged → entry.2.1 = digest)
    (hforeign : ∀ entry ∈ L, entry.2.2 = true → keyOf entry.1 = some e →
      XmssSecurity.TargetSum.ValidDigest entry.2.1 → entry.1 = forged) :
    PreInv e forged digest (L.foldl (Monitor.step keyOf) m) := by
  induction L generalizing m with
  | nil => exact hm
  | cons entry L ih =>
    exact ih _ (preInv_step keyOf e forged digest hforged hvalid m hm entry (hcons entry List.mem_cons_self)
      (hforeign entry List.mem_cons_self)) (fun en h => hcons en (List.mem_cons_of_mem _ h))
      (fun en h => hforeign en (List.mem_cons_of_mem _ h))

/-- The state after the selection. The monitor has hit, or `e` is signed with the selected digest
and the forged input is not seen yet. -/
def PostInv (m : Monitor) : Prop :=
  m.hit = true ∨ (m.state.signed e = some digest ∧ forged ∉ m.seen)

theorem postInv_foldl (hforged : keyOf forged = some e) (L : List Entry) (m : Monitor)
    (hm : PostInv e forged digest m) (hcons : ∀ entry ∈ L, entry.1 = forged → entry.2.1 = digest) :
    PostInv e forged digest (L.foldl (Monitor.step keyOf) m) := by
  induction L generalizing m with
  | nil => exact hm
  | cons entry L ih =>
    refine ih _ ?_ (fun en h => hcons en (List.mem_cons_of_mem _ h))
    obtain ⟨input, d, honest⟩ := entry
    have hc := hcons _ List.mem_cons_self
    simp only at hc
    unfold Monitor.step
    split_ifs with hseen
    · exact hm
    rcases hm with hm | ⟨hs, hf⟩
    · exact Or.inl (Monitor.fresh_hit keyOf m _ _ _ hm)
    by_cases hi : input = forged
    · subst hi
      obtain rfl := hc rfl
      rw [m.fresh_signed keyOf input d honest e hforged d hs]
      exact Or.inl (by simp)
    by_cases hk : keyOf input = some e
    · rw [m.fresh_signed keyOf input d honest e hk digest hs]
      right
      refine ⟨hs, ?_⟩
      rintro (h | h)
      · exact hi h.symm
      · exact hf h
    · obtain ⟨hsigned, -, hseen', hhit⟩ := fresh_state_at keyOf e m input d honest hk
      rcases hhit with hhit | -
      · exact Or.inl hhit
      right
      refine ⟨hsigned.trans hs, ?_⟩
      rw [hseen']
      rintro (h | h)
      · exact hi h.symm
      · exact hf h

/-- The monitor hits on a log with a fresh honest selection `selected` at `e` and a forged input
at `e` with the same valid digest, if every earlier honest valid call at `e` is on the forged
input. -/
theorem monitor_hit_of_partner (selected : XmssSecurity.HashInput) (hselected : keyOf selected = some e)
    (hforged : keyOf forged = some e) (hne : selected ≠ forged)
    (hvalid : XmssSecurity.TargetSum.ValidDigest digest) (pre post : List Entry)
    (hpre : ∀ entry ∈ pre, entry.1 ≠ selected)
    (hcons : ∀ entry ∈ pre ++ post, entry.1 = forged → entry.2.1 = digest)
    (hmem : ∃ entry ∈ pre ++ post, entry.1 = forged)
    (hforeign : ∀ entry ∈ pre, entry.2.2 = true → keyOf entry.1 = some e →
      XmssSecurity.TargetSum.ValidDigest entry.2.1 → entry.1 = forged) :
    ((pre ++ (selected, digest, true) :: post).foldl (Monitor.step keyOf) Monitor.empty).hit = true := by
  rw [List.foldl_append, List.foldl_cons]
  set m1 := pre.foldl (Monitor.step keyOf) Monitor.empty
  have h1 : PreInv e forged digest m1 := by
    refine preInv_foldl keyOf e forged digest hforged hvalid pre _ ?_
      (fun en h => hcons en (List.mem_append_left _ h)) hforeign
    right; left
    exact ⟨rfl, fun h => absurd h (Set.notMem_empty _)⟩
  have hnot : selected ∉ m1.seen := by
    intro h
    rcases foldl_seen_sub keyOf pre _ selected h with h | ⟨en, hen, rfl⟩
    · exact Set.notMem_empty _ h
    · exact hpre en hen rfl
  rw [Monitor.step_of_not_seen keyOf m1 _ hnot]
  dsimp only
  rcases h1 with h1 | ⟨hs, hpend⟩ | hs
  · exact foldl_hit keyOf post _ (Monitor.fresh_hit keyOf m1 _ _ _ h1)
  · rw [m1.fresh_unsigned keyOf selected digest true e hselected hs, if_pos hvalid, if_pos rfl]
    by_cases hf : forged ∈ m1.seen
    · exact foldl_hit keyOf post _ (by simp [hpend hf])
    have hm2 : PostInv e forged digest ⟨insert selected m1.seen, m1.state.install e digest,
        m1.hit || decide (digest ∈ m1.state.pending e)⟩ := by
      refine Or.inr ⟨by simp [XmssSecurity.EncodingMonitor.State.install], fun h => ?_⟩
      rcases Set.mem_insert_iff.1 h with h | h
      · exact hne h.symm
      · exact hf h
    have hpost := postInv_foldl keyOf e forged digest hforged post _ hm2
      (fun en h => hcons en (List.mem_append_right _ h))
    rcases hpost with h | ⟨-, hnf⟩
    · exact h
    obtain ⟨en, hen, rfl⟩ := hmem
    rcases List.mem_append.1 hen with hen | hen
    · exact (hf (mem_foldl_seen keyOf pre _ en hen)).elim
    · exact (hnf (mem_foldl_seen keyOf post _ en hen)).elim
  · rw [m1.fresh_signed keyOf selected digest true e hselected digest hs]
    exact foldl_hit keyOf post _ (by simp)

end MonitorList

/-- Each hash entry of the log has its digest in the cache. -/
def LogConsistent (s : LoggedState C) : Prop :=
  ∀ entry ∈ s.2.filterMap hashEntry, ∃ output, s.1.1 (.hash entry.1) = some output ∧
    XmssSecurity.truncateHash output = entry.2.1

theorem logConsistent_step (t : (WorldSpec C).Domain) (s : LoggedState C) (hs : LogConsistent s)
    (r : (WorldSpec C).Range t × LoggedState C) (hr : r ∈ support ((loggedImpl prims t).run s)) :
    LogConsistent r.2 := by
  simp only [loggedImpl, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  have hgrow := SigningCacheProof.countImpl_grows prims t s.1 z hz
  intro entry hentry
  simp only [QueryLog.logQuery, List.filterMap_append, List.mem_append] at hentry
  rcases hentry with hentry | hentry
  · obtain ⟨output, ho, hd⟩ := hs entry hentry
    exact ⟨output, hgrow ho, hd⟩
  simp only [SigningCacheProof.countImpl, SeedHitProof.withCount, StateT.run_mk, support_map,
    Set.mem_image] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rcases t with ((n | (q | p)) | prog) | (n | (q | p))
  · simp [QueryLog.singleton, hashEntry] at hentry
  · change w ∈ support (((Query C →ₒ HashOutput).randomOracle q).run s.1.1) at hw
    have hself := (randomOracle_support q s.1.1 w hw).2.1
    cases q
    case hash input =>
      simp [QueryLog.singleton, hashEntry] at hentry
      subst hentry
      exact ⟨w.1, hself, rfl⟩
    all_goals simp [QueryLog.singleton, hashEntry] at hentry
  · simp [QueryLog.singleton, hashEntry] at hentry
  · simp [QueryLog.singleton, hashEntry] at hentry
  · simp [QueryLog.singleton, hashEntry] at hentry
  · change w ∈ support (((Query C →ₒ HashOutput).randomOracle q).run s.1.1) at hw
    have hself := (randomOracle_support q s.1.1 w hw).2.1
    cases q
    case hash input =>
      simp [QueryLog.singleton, hashEntry] at hentry
      subst hentry
      exact ⟨w.1, hself, rfl⟩
    all_goals simp [QueryLog.singleton, hashEntry] at hentry
  · simp [QueryLog.singleton, hashEntry] at hentry

set_option maxRecDepth 100000 in
theorem joint_logConsistent (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) : LogConsistent w.2 :=
  SeedHitProof.support_simulateQ_inv (loggedImpl prims) LogConsistent
    (fun t s hs r hr => logConsistent_step prims t s hs r hr) _ loggedInit
    (fun entry h => by simp [loggedInit] at h) w hw

set_option maxRecDepth 100000 in
theorem joint_covered (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C)
    (hw : w ∈ support (jointRun prims A x)) (keyOf : XmssSecurity.HashInput → Option XmssSecurity.LeafIndex) :
    Covered keyOf w.2 := by
  have hinv := SeedHitProof.support_simulateQ_inv (loggedImpl prims)
    (fun s => ¬Programmed s.2 → Covered keyOf s)
    (fun t s hs r hr => covered_step prims keyOf t s hs r hr) _ loggedInit
    (fun _ input h => (h rfl).elim) w hw
  refine hinv ?_
  have hz : (w.1.1, w.2) ∈ support (loggedRun prims A x) := by
    rw [← jointRun_logged, support_map, Set.mem_image]
    with_reducible exact ⟨w, hw, rfl⟩
  exact noProgramQuery prims C A x _ hz

set_option maxRecDepth 100000 in
/-- The forged digest of a win decodes. -/
theorem forged_decode (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (r : Outcome C)
    (hr : r ∈ support (SigningDescentProof.exposedRun prims A x))
    (hwin : r.1.1 = (true, false)) (top : TopTree) (state : TsigState C) (forgery : Forgery)
    (hmeta : r.1.2 = some (top, state, forgery)) :
    ∃ encoding, XmssSecurity.TargetSum.decodeDigest
      (XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView r.2.1)
        x.1 forgery.signature.leafIndex
        (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness)) = some encoding := by
  obtain ⟨top', state', forgery', hmeta', _, hresolved, _⟩ :=
    SigningCacheProof.exposedRun_facts prims A x r hr hwin
  rw [hmeta] at hmeta'
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hmeta')
  have hverified := (XmssSecurity.Concrete.CacheReplay.eval_verify _ _ _ _ _).symm.trans
    (SigningCacheProof.resolves_value hresolved)
  obtain ⟨encoding, hdecode, -⟩ :=
    (XmssSecurity.Concrete.verifyFromCache_eq_true_iff _ _ _ _ _).mp hverified
  exact ⟨encoding, hdecode⟩

/-- The first hash call on `input` in a log is a call of the free copy. -/
def FirstCallHonest (log : QueryLog (WorldSpec C)) (input : XmssSecurity.HashInput) : Prop :=
  ∃ digest, (log.filterMap hashEntry).find? (fun entry => decide (entry.1 = input)) = some (input, digest, true)

/-- The selection at the key of the forgery is fresh. Its first call in the log is honest, so no
call reads it before the grind. -/
def FreshSelection (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  ∃ top state forgery, w.1.1.2 = some (top, state, forgery) ∧
    let z := finalOf x (w.1.1, w.2.1) top state forgery
    ∃ selected, (z.honestKey prims).selected = some selected ∧
      FirstCallHonest w.2.2 (XmssSecurity.Concrete.CacheView.encodingInput x.1 z.key selected)

/-- A bottom partner with a fresh selection is the bottom partner on the log, unless `ρ` comes from
a commitment collision. -/
def FreshPartnerLink : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C),
    w ∈ support (jointRun prims A x) → w.1.1.1 = (true, false) →
    SigningPartnerLinkProof.BottomPartnerCase prims x (w.1.1, w.2.1) → FreshSelection prims x w →
    BottomPartnerLogged x (w.1.1, w.2) ∨ SigningGuessProof.AlternativeCommitment x.2.1 x.1 w.2.1.1

/-- The honest calls at the key of the forgery before the selection. Before the first call of the
selected input, every free-copy call at `e` with a valid digest is on the forged input, unless `ρ`
comes from a commitment collision.

* The free-copy calls at `e` are the trials of the grinds at `e`, the final verification, and the
  grind of `honestSignature`.
* A grind at `e` runs for the message in `st.bound e` with a `ρ` that opens `c_e`. With `ρ_e`, it
  reaches no valid trial before the selection. Another `ρ` is `AlternativeCommitment`.
* The final verification calls the forged input. -/
def SelectionClassification : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C),
    w ∈ support (jointRun prims A x) → w.1.1.1 = (true, false) →
    ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 w.2.1.1 →
    ∀ top state forgery, w.1.1.2 = some (top, state, forgery) →
    ∀ selected, ((finalOf x (w.1.1, w.2.1) top state forgery).honestKey prims).selected = some selected →
    ∀ (pre post : List Entry) (digest : XmssSecurity.Digest),
      w.2.2.filterMap hashEntry = pre ++
        (XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex selected, digest, true) ::
          post →
      (∀ entry ∈ pre,
        entry.1 ≠ XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex selected) →
      ∀ entry ∈ pre, entry.2.2 = true →
        XmssSecurity.encodingInputLeafIndex? x.1 entry.1 = some forgery.signature.leafIndex →
        XmssSecurity.TargetSum.ValidDigest entry.2.1 →
        entry.1 = XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex
          (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness)

set_option maxRecDepth 100000 in
/-- The partner link from the classification of the honest calls. -/
theorem freshPartnerLink_of_classification (hclass : SelectionClassification (C := C) prims) :
    FreshPartnerLink (C := C) prims := by
  intro A x w hw hwin hcase hfresh
  by_cases halt : SigningGuessProof.AlternativeCommitment x.2.1 x.1 w.2.1.1
  · exact Or.inr halt
  left
  obtain ⟨top, state, forgery, hm, selected, hsel, hne, heq⟩ := hcase
  obtain ⟨top', state', forgery', hm', selected', hsel', hfirst⟩ := hfresh
  rw [hm] at hm'
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm')
  obtain rfl : selected' = selected := Option.some.inj (hsel'.symm.trans hsel)
  obtain ⟨digest, hfind⟩ := hfirst
  obtain ⟨-, pre, post, hsplit, hpre⟩ := List.find?_eq_some_iff_append.1 hfind
  have hkey : (finalOf x (w.1.1, w.2.1) top state forgery).key = forgery.signature.leafIndex := rfl
  have hcache : (finalOf x (w.1.1, w.2.1) top state forgery).cache = w.2.1.1 := rfl
  simp only [hkey, hcache] at hsplit hpre heq
  have hcons := joint_logConsistent prims A x w hw
  obtain ⟨encoding, hdecode⟩ := forged_decode prims A x (w.1.1, w.2.1)
    (mem_exposedRun_of_joint prims A x w hw) hwin top state forgery hm
  have hinj := XmssSecurity.Concrete.CacheView.encodingInput_injective x.1 forgery.signature.leafIndex
  have hpre' : ∀ entry ∈ pre, entry.1 ≠
      XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex selected' :=
    fun entry h => by simpa using hpre entry h
  obtain ⟨outputS, hS, hdS⟩ := hcons _ (hsplit ▸ List.mem_append_right pre List.mem_cons_self)
  simp only at hS hdS
  have hSdigest : XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView w.2.1.1) x.1
      forgery.signature.leafIndex selected' = digest := by
    simp only [XmssSecurity.Concrete.CacheView.encodingHash, XmssSecurity.Concrete.CacheView.digestAt,
      SigningDescentProof.thView]
    rw [hS]
    exact hdS
  have hFdigest : XmssSecurity.Concrete.CacheView.encodingHash (SigningDescentProof.thView w.2.1.1) x.1
      forgery.signature.leafIndex
      (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness) = digest :=
    heq.symm.trans hSdigest
  rw [hFdigest] at hdecode
  have hvalid : XmssSecurity.TargetSum.ValidDigest digest := ⟨encoding, hdecode⟩
  have hFne : XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex selected' ≠
      XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex
        (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness) :=
    fun h => hne (hinj h)
  obtain ⟨outputF, hF⟩ : ∃ output, w.2.1.1 (.hash (XmssSecurity.Concrete.CacheView.encodingInput x.1
      forgery.signature.leafIndex
        (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness))) = some output := by
    cases hc : w.2.1.1 (.hash (XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex
        (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness))) with
    | some output => exact ⟨output, rfl⟩
    | none =>
      simp only [XmssSecurity.Concrete.CacheView.encodingHash, XmssSecurity.Concrete.CacheView.digestAt,
        SigningDescentProof.thView] at hFdigest
      rw [hc] at hFdigest
      rw [← hFdigest, XmssSecurity.TargetSum.decodeDigest_zero_eq_none] at hdecode
      cases hdecode
  have hFdigest' : XmssSecurity.truncateHash outputF = digest := by
    simp only [XmssSecurity.Concrete.CacheView.encodingHash, XmssSecurity.Concrete.CacheView.digestAt,
      SigningDescentProof.thView] at hFdigest
    rw [hF] at hFdigest
    exact hFdigest
  have hseen := joint_covered prims A x w hw (XmssSecurity.encodingInputLeafIndex? x.1) _ (by rw [hF]; simp)
  unfold monitorOf at hseen
  rw [hsplit] at hseen
  have hmem : ∃ entry ∈ pre ++ post, entry.1 = XmssSecurity.Concrete.CacheView.encodingInput x.1
      forgery.signature.leafIndex (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness) := by
    rcases foldl_seen_sub _ _ _ _ hseen with h | ⟨entry, hentry, hEq⟩
    · exact absurd h (Set.notMem_empty _)
    rcases List.mem_append.1 hentry with h | h
    · exact ⟨entry, List.mem_append_left _ h, hEq⟩
    rcases List.mem_cons.1 h with rfl | h
    · exact (hFne hEq).elim
    · exact ⟨entry, List.mem_append_right _ h, hEq⟩
  have hconsF : ∀ entry ∈ pre ++ post, entry.1 = XmssSecurity.Concrete.CacheView.encodingInput x.1
      forgery.signature.leafIndex (forgery.message, (XmssSecurity.Bridge.toModelSig forgery.signature).randomness) →
      entry.2.1 = digest := by
    intro entry hentry hEq
    have hin : entry ∈ w.2.2.filterMap hashEntry := by
      rw [hsplit]
      rcases List.mem_append.1 hentry with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
    obtain ⟨output, ho, hd⟩ := hcons entry hin
    rw [hEq, hF] at ho
    rw [← hd, ← Option.some.inj ho, hFdigest']
  unfold BottomPartnerLogged monitorOf
  rw [hsplit]
  exact monitor_hit_of_partner _ forgery.signature.leafIndex _ digest _
    (XmssSecurity.encodingInputLeafIndex?_encodingInput _ _ _)
    (XmssSecurity.encodingInputLeafIndex?_encodingInput _ _ _) hFne hvalid pre post hpre' hconsF hmem
    (hclass A x w hw hwin halt top state forgery hm selected' hsel pre post digest hsplit hpre')

/-- The combined flag of the uncharged lane on the joint run.

* An input-side hit. An adversary call or a verification call carried an unreleased opening or a
  hidden chain value below the opened position (`HiddenInputHit` of the candidate log).
* A bottom partner whose selection is not fresh. This is the cached selection of leanVM lane 2.
* A top partner that no successful bottom ceremony resolves.
-/
def UnchargedFlag (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) : Prop :=
  SigningOpeningProof.HiddenInputHit x (SigningGuessLinkProof.chainTarget prims x (w.1, w.2.1)) (w.1, w.2.1) ∨
    (SigningPartnerLinkProof.BottomPartnerCase prims x (w.1.1, w.2.1) ∧ ¬FreshSelection prims x w) ∨
    (SigningGuessProof.TopPartner prims x (w.1.1, w.2.1) ∧
      ¬∃ key, SigningGuessProof.ResolvedTopPartner x key w.2.1.1)

set_option maxRecDepth 100000 in
/-- An uncharged win on the log raises the combined flag. -/
theorem unchargedFlag_of_win (hlink : FreshPartnerLink (C := C) prims) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) (w : JointOutcome C) (hw : w ∈ support (jointRun prims A x))
    (hu : UnchargedWinLogged prims x (w.1.1, w.2)) : UnchargedFlag prims x w := by
  obtain ⟨hwin, hnc⟩ := hu
  have ho := mem_exposedRun_of_joint prims A x w hw
  obtain ⟨top, state, forgery, hm, hbad⟩ :=
    SigningCacheProof.signing_run_badEvent_closed prims A x (w.1.1, w.2.1) ho hwin
  rcases hbad with hhit | hguess | hbottom | htop
  · exact (hnc (Or.inl (Or.inl ⟨hwin, top, state, forgery, hm, hhit⟩))).elim
  · exact Or.inl (SigningGuessLinkProof.guess_hiddenInputHit prims A x (w.1, w.2.1)
      (mem_verifyRun_of_joint prims A x w hw) top state forgery hm hguess)
  · have hcase : SigningPartnerLinkProof.BottomPartnerCase prims x (w.1.1, w.2.1) :=
      ⟨top, state, forgery, hm, hbottom⟩
    by_cases hfresh : FreshSelection prims x w
    · rcases hlink A x w hw hwin hcase hfresh with h | h
      · exact (hnc (Or.inr h)).elim
      · exact (hnc (Or.inl (Or.inr (Or.inl h)))).elim
    · exact Or.inr (Or.inl ⟨hcase, hfresh⟩)
  · exact Or.inr (Or.inr ⟨⟨top, state, forgery, hm, htop⟩,
      fun h => hnc (Or.inl (Or.inr (Or.inr h)))⟩)


/-- The one open coupling. It is the `hcouple` premise of `SigningOpeningProof.probEvent_le_of_capped`
for `UnchargedFlag`. A capped hybrid with uniform secrets of type `K → Digest` and output targets
of probability `2^-128` (`hout`) raises its flag at least as often as the joint run raises
`UnchargedFlag`. -/
def UnchargedFlagCoupling : Prop :=
  ∀ (A : TsigAdversary C) (q : ℕ) (x : SigningSecurityProof.Keys3 C),
    x ∈ support (TprfSecurityProof.keyGen3 (C := C)) →
    ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2 →
    (∀ r ∈ support (runSigningWorld prims (SigningSecurityProof.gameAfter A x)), r.2 ≤ q) →
    q < 2 ^ 127 →
    ∃ (κ σ β K : Type) (spec : OracleSpec κ) (_ : Fintype K) (_ : DecidableEq K)
      (_ : SampleableType (K → Digest)) (impl : QueryImpl spec (StateT σ ProbComp))
      (inputSide p : κ → Prop) (keyOf : κ → K) (point : κ → Digest)
      (outHit : (t : κ) → σ × ℕ → spec t × (σ × ℕ) → Prop)
      (oa : OracleComp (spec + SigningOpeningProof.RevealSpec K Digest) β) (σ₀ : σ),
      (∀ t σ₁ n, p t → ¬inputSide t →
        Pr[outHit t (σ₁, n) | (SigningOpeningProof.countImpl impl p t).run (σ₁, n)] ≤
          (2 ^ 128 : ℝ≥0∞)⁻¹) ∧
      Pr[UnchargedFlag prims x | jointRun prims A x] ≤
        Pr[fun r => r.2.2.2 = true | $ᵗ (K → Digest) >>= fun s =>
          (simulateQ (SigningOpeningProof.revealImpl (SigningOpeningProof.countImpl impl p)
            (SigningOpeningProof.cappedCall p q) inputSide outHit keyOf point s) oa).run
              ((σ₀, 0), fun _ => none, false)]

set_option maxRecDepth 100000 in
/-- The uncharged lane on the log from the fresh partner link and the coupling. -/
theorem unchargedLaneBoundLogged_of_coupling (hlink : FreshPartnerLink (C := C) prims)
    (hcouple : UnchargedFlagCoupling (C := C) prims) : UnchargedLaneBoundLogged (C := C) prims := by
  intro A q x hx hkeys hq hsmall
  obtain ⟨κ, σ, β, K, spec, _, _, _, impl, inputSide, p, keyOf, point, outHit, oa, σ₀, hout, hflag⟩ :=
    hcouple A q x hx hkeys hq hsmall
  have hle : Pr[UnchargedWinLogged prims x | loggedRun prims A x] ≤
      Pr[UnchargedFlag prims x | jointRun prims A x] := by
    rw [← jointRun_logged, probEvent_map]
    exact probEvent_mono fun w hw hu => unchargedFlag_of_win prims hlink A x w hw hu
  exact hle.trans (SigningOpeningProof.probEvent_le_of_capped impl inputSide p
    (jointRun prims A x) (UnchargedFlag prims x) keyOf point q outHit hout oa σ₀ hflag)

/-- The signing core from the classification of the honest calls and the coupling. -/
theorem hiddenCoreAt_of_coupling (hclass : SelectionClassification (C := C) prims)
    (hcouple : UnchargedFlagCoupling (C := C) prims) : SigningCoreProof.HiddenCoreAt prims C :=
  hiddenCoreAt_of_logged prims
    (unchargedLaneBoundLogged_of_coupling prims (freshPartnerLink_of_classification prims hclass) hcouple)

end SigningUnchargedLoggedProof

end ThresholdLeanXmssSecurity

/--
info: 'ThresholdLeanXmssSecurity.SigningUnchargedLoggedProof.freshPartnerLink_of_classification' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningUnchargedLoggedProof.freshPartnerLink_of_classification

/--
info: 'ThresholdLeanXmssSecurity.SigningUnchargedLoggedProof.unchargedLaneBoundLogged_of_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningUnchargedLoggedProof.unchargedLaneBoundLogged_of_coupling

/--
info: 'ThresholdLeanXmssSecurity.SigningUnchargedLoggedProof.hiddenCoreAt_of_coupling' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningUnchargedLoggedProof.hiddenCoreAt_of_coupling

/--
info: 'ThresholdLeanXmssSecurity.SigningUnchargedLoggedProof.verifyFinal_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.SigningUnchargedLoggedProof.verifyFinal_support
