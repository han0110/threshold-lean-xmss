import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.BottomCut
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.BottomCosts
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.BottomEnds

/-!
# The laws of the reduction of a bottom slot

`bottomReductionViewWith` states that the reduction of bottom slot `j` with the real challenger and the
distinguisher after `post` accepts with the probability of `UsedHit` in `bottomCutGameWith post`, the
hybrid cut at the slot. Each place that the prefix reaches passes the guard (`bottomPrefix_guard`).
`bottomLawReal_of_cut` and `bottomLawFresh_of_cut` give the two laws from the game side of each.
`walkCore` is `forgeWalk` with the pause as data, and `fixedGame_bottomCut` reduces the game side to the
law of the game after each pause.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_bind noCall_pure noCall_map)

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (prims : Primitives)

/-! ## No programming call -/

theorem noProgT_signingImpl (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain) :
    NoProgT (signingImpl K circuits settings runLimit j D A t) := by
  rcases t with t | q | q
  · exact NoProgT.lift (NoProg.lift (Collision.noProgram_adversary _))
  · exact noProgT_fixedOracles K circuits settings runLimit j D A q
  · rcases q with _ | state
    · exact NoProgT.lift (fun _ => noCall_pure _ _)
    · exact NoProgT.lift (NoProg.modify _)

theorem noProg_pauseAt (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (p : BottomPause C A.net.State) :
    NoCall WorldProgramQuery (pauseAt K circuits settings runLimit j D A p) := by
  unfold pauseAt
  split_ifs
  all_goals try exact noCall_pure _ _
  · refine noCall_bind _ (Collision.noProgram_free _) fun fresh => ?_
    refine noCall_bind _ (Collision.noProgram_executePhase D A.net _ _ _) fun r => ?_
    obtain ⟨adversary, heads⟩ := r
    dsimp only
    split_ifs <;> exact noCall_pure _ _

theorem noProgT_forgeWalk (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (keys : Keys C) (top : TopTree)
    (oa : OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery) :
    NoProgT (forgeWalk K circuits settings runLimit j D A keys top oa) := by
  induction oa using OracleComp.inductionOn with
  | pure forgery =>
    intro st
    change NoProg ((forgeWalk K circuits settings runLimit j D A keys top (PFunctor.FreeM.pure forgery)).run st)
    simp only [forgeWalk, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, StateT.run_pure]
    refine (((NoProg.get.bind fun s => ?_).bind fun _ => NoProg.pure _).bind fun _ => NoProg.pure _)
    rw [forgeryWins_eq_free]
    exact NoProg.lift (Collision.noProgram_free _)
  | query_bind t next ih =>
    intro st
    change NoProg ((forgeWalk K circuits settings runLimit j D A keys top (PFunctor.FreeM.liftBind t next)).run st)
    have hstep : NoProg ((signingImpl K circuits settings runLimit j D A t >>= fun a =>
        forgeWalk K circuits settings runLimit j D A keys top (next a)).run st) := by
      rw [StateT.run_bind]
      exact (noProgT_signingImpl K circuits settings runLimit j D A t st).bind fun p => ih p.1 p.2
    by_cases ht : ∃ b, t = .inr (.inl (.tree b))
    · obtain ⟨b, rfl⟩ := ht
      simp only [forgeWalk, StateT.run_bind, StateT.run_lift]
      refine NoProg.get.bind fun s => ?_
      dsimp only
      split_ifs
      · simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift]
        exact (NoProg.lift (noProg_pauseAt K circuits settings runLimit j D A _)).bind fun _ => NoProg.pure _
      · rw [StateT.run_bind] at hstep ⊢
        exact (noProgT_signingImpl K circuits settings runLimit j D A _ st).bind fun p => ih p.1 p.2
    · rcases t with u | (q | q)
      · simpa only [forgeWalk] using hstep
      · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
        · simpa only [forgeWalk] using hstep
        · exact absurd ⟨b, rfl⟩ ht
        · simpa only [forgeWalk] using hstep
        · simpa only [forgeWalk] using hstep
      · simpa only [forgeWalk] using hstep

theorem noProg_bottomPrefix (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    NoCall WorldProgramQuery (bottomPrefix K circuits settings runLimit j D A) := by
  unfold bottomPrefix
  refine noCall_bind _ (Collision.noProgram_realExecution D A.net _ _ _ _) fun p => ?_
  obtain ⟨state, keys⟩ := p
  refine noCall_bind _ (Collision.noProgram_voteRound D A.net _ _) fun v => ?_
  refine noCall_bind _ ?_ fun q => noCall_pure _ _
  refine ((noProg_fixedTreeRuns K circuits settings runLimit j D A.net _ _).bind fun _ => NoProg.get.bind
    fun s => ?_) _
  split
  · exact NoProg.pure _
  · intro s'
    rw [StateT.run'_eq, StateT.run_map]
    exact noCall_map _ _ (noProgT_forgeWalk K circuits settings runLimit j D A _ _ _ _ s')

theorem noProg_resumeAfter (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (p : BottomPause C A.net.State)
    (s : RealState C A.net.State) : NoCall WorldProgramQuery (resumeAfter K circuits settings runLimit j D A p s) := by
  unfold resumeAfter
  refine noCall_bind _ ?_ fun r => ?_
  · refine (NoProg.get.bind fun s' => ?_) s
    split
    · exact (NoProg.lift (Collision.noProgram_free _)).bind fun _ => NoProg.pure _
    · exact NoProg.pure _
  · obtain ⟨answer, s'⟩ := r
    refine noCall_bind _ (noProgT_simulateQ _ (noProgT_signingImpl K circuits settings runLimit (j + 1) D A) _ _ _)
      fun q => ?_
    obtain ⟨⟨forgery, st⟩, s''⟩ := q
    refine noCall_bind _ ?_ fun _ => noCall_pure _ _
    rw [forgeryWins_eq_free]
    exact NoProg.lift (Collision.noProgram_free _) _

theorem noProg_finishResume (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (p : BottomPause C A.net.State)
    (X : OracleComp (WorldSpec C) (A.net.State × (C.Party → Option TreeOutput))) (hX : NoCall WorldProgramQuery X) :
    NoCall WorldProgramQuery (X >>= fun r => finishRun D A.net p r >>= fun s =>
      resumeAfter K circuits settings runLimit j D A p s) := by
  refine noCall_bind _ hX fun r => ?_
  unfold finishRun
  rw [bind_assoc]
  refine noCall_bind _ (noProgram_wrongOutput D _ _ _) fun _ => ?_
  rw [bind_assoc]
  exact noCall_bind _ (Collision.noProgram_voteRound D A.net _ _) fun _ => by
    rw [pure_bind]
    exact noProg_resumeAfter K circuits settings runLimit j D A p _

theorem noProg_bottomRest (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (place : BottomPlace C A.net.State)
    (out : C.Party → Option (Keys C)) :
    NoCall WorldProgramQuery (bottomRest K circuits settings runLimit j D A place out) := by
  cases place with
  | finished => exact noCall_pure _ _
  | dead p =>
    simp only [bottomRest]
    exact noCall_bind _ (noProg_fixedTreeRun K circuits settings runLimit (j + 1) D A.net _ _) fun r =>
      noProg_resumeAfter K circuits settings runLimit j D A p _
  | live p adversary heads =>
    simp only [bottomRest]
    split_ifs
    · exact noProg_finishResume K circuits settings runLimit j D A p _ (Collision.noProgram_executePhase D A.net _ _ _)
    · exact noProg_finishResume K circuits settings runLimit j D A p _ (Collision.noProgram_executePhase D A.net _ _ _)
  | skip p adversary heads =>
    simp only [bottomRest]
    exact noProg_finishResume K circuits settings runLimit j D A p _ (Collision.noProgram_executePhase D A.net _ _ _)

/-! ## The guard holds at each reachable place -/

theorem fixedTreeRuns_bounded (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    ∀ (count : ℕ) (s : RealState C net.State), RunsBounded runLimit s →
      ∀ r ∈ support ((fixedTreeRuns K circuits settings runLimit j (wrongOutput D) D net tree count).run s),
        RunsBounded runLimit r.2
  | 0, s, hs, r, hr => by
    simp only [fixedTreeRuns, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
    exact hs
  | count + 1, s, hs, r, hr => by
    simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split_ifs at hr with hm
    · rw [StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨p, hp, hr⟩ := hr
      exact fixedTreeRuns_bounded j D net tree count p.2 (fixedTreeRun_bounded K circuits settings runLimit j D net
        tree s hs (FirstCounts.mayRun_lt runLimit hm) p hp) r hr
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
      exact hs

theorem signingImpl_bounded (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain) (st : TsigState C) (s : RealState C A.net.State)
    (hs : RunsBounded runLimit s) :
    ∀ r ∈ support (((signingImpl K circuits settings runLimit j D A t).run st).run s), RunsBounded runLimit r.2 := by
  intro r hr
  by_cases ht : ∃ b, t = .inr (.inl (.tree b))
  · obtain ⟨b, rfl⟩ := ht
    change r ∈ support (((StateT.lift (fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D A.net b) :
      StateT (TsigState C) (RealM C A.net.State) _).run st).run s) at hr
    rw [run_lift_tsig, support_map] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    unfold fixedTreeRequest at hq
    rw [StateT.run_bind, mem_support_bind_iff] at hq
    obtain ⟨x, hx, hq⟩ := hq
    rw [(requestRest_adds D b x.2).2 q hq]
    exact fixedTreeRuns_bounded K circuits settings runLimit j D A.net _ 1 s hs x hx
  · intro t'
    rw [(signingImpl_quiet K circuits settings runLimit j D A t (fun b h => ht ⟨b, h⟩) st s).2 r hr]
    exact hs t'

theorem pauseAt_guard (forge j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (p : BottomPause C A.net.State)
    (hp : PauseInRange runLimit forge j p) :
    ∀ place ∈ support (pauseAt K circuits settings runLimit j D A p), PlaceGuard runLimit forge j D place := by
  intro place hplace
  unfold pauseAt at hplace
  split at hplace
  · obtain rfl := OracleComp.eq_of_mem_support_pure _ hplace
    exact ⟨hp, by assumption⟩
  · split at hplace
    · obtain rfl := OracleComp.eq_of_mem_support_pure _ hplace
      exact hp
    · obtain ⟨fresh, _, hplace⟩ := OracleComp.mem_support_bind_peel _ _ hplace
      obtain ⟨⟨adversary, heads⟩, _, hplace⟩ := OracleComp.mem_support_bind_peel _ _ hplace
      dsimp only at hplace
      split at hplace <;> obtain rfl := OracleComp.eq_of_mem_support_pure _ hplace <;> exact hp

theorem forgeWalk_guard (forge j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (keys : Keys C) (top : TopTree)
    (oa : OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery) :
    ∀ n, n ≤ forge → IsQueryBoundP oa (ForgeInClass .prssSetup) n → ∀ (st : TsigState C) (s : RealState C A.net.State),
      RunsBounded runLimit s →
      ∀ r ∈ support (((forgeWalk K circuits settings runLimit j D A keys top oa).run st).run s),
        PlaceGuard runLimit forge j D r.1.1 := by
  induction oa using OracleComp.inductionOn with
  | pure forgery =>
    intro n _ _ st s _ r hr
    change r ∈ support (((forgeWalk K circuits settings runLimit j D A keys top (PFunctor.FreeM.pure forgery)).run
      st).run s) at hr
    simp only [forgeWalk, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨_, _, rfl⟩ := hr
    trivial
  | query_bind t next ih =>
    intro n hn hb st s hs r hr
    rw [isQueryBoundP_query_bind_iff] at hb
    obtain ⟨_, hnext⟩ := hb
    change r ∈ support (((forgeWalk K circuits settings runLimit j D A keys top
      (PFunctor.FreeM.liftBind t next)).run st).run s) at hr
    have hstep : ∀ r ∈ support (((signingImpl K circuits settings runLimit j D A t >>= fun a =>
        forgeWalk K circuits settings runLimit j D A keys top (next a)).run st).run s),
        PlaceGuard runLimit forge j D r.1.1 := by
      intro r hr
      rw [StateT.run_bind, StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨q, hq, hr⟩ := hr
      exact ih q.1.1 _ (by split_ifs <;> omega) (hnext q.1.1) q.1.2 q.2
        (signingImpl_bounded K circuits settings runLimit j D A t st s hs q hq) r hr
    by_cases ht : ∃ b, t = .inr (.inl (.tree b))
    · obtain ⟨b, rfl⟩ := ht
      have hQ : ¬ ForgeInClass (C := C) (σ := A.net.State) .prssSetup (.inr (.inl (.tree b))) := fun h => h
      simp only [hQ, ite_false] at hnext
      simp only [forgeWalk, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_pure, pure_bind] at hr
      split_ifs at hr with hc
      · simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, StateT.run_pure, bind_assoc,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
        obtain ⟨place, hplace, rfl⟩ := hr
        refine pauseAt_guard K circuits settings runLimit forge j D A _ ?_ place hplace
        exact ⟨hc.2, hs, FirstCounts.mayRun_lt runLimit hc.1, fun a => (hnext a).mono hn⟩
      · exact hstep r hr
    · rcases t with u | (q | q)
      · exact hstep r (by simpa only [forgeWalk] using hr)
      · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
        · exact hstep r (by simpa only [forgeWalk] using hr)
        · exact absurd ⟨b, rfl⟩ ht
        · exact hstep r (by simpa only [forgeWalk] using hr)
        · exact hstep r (by simpa only [forgeWalk] using hr)
      · exact hstep r (by simpa only [forgeWalk] using hr)

/-- Each place that the prefix reaches passes the guard. -/
theorem bottomPrefix_guard (forge j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge) :
    ∀ place ∈ support (bottomPrefix K circuits settings runLimit j D A), PlaceGuard runLimit forge j D place := by
  intro place hplace
  unfold bottomPrefix at hplace
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hplace
  obtain ⟨⟨state, keys⟩, _, v, _, q, hq, rfl⟩ := hplace
  rw [StateT.run_bind, mem_support_bind_iff] at hq
  obtain ⟨x, hx, hq⟩ := hq
  have hb := fixedTreeRuns_bounded K circuits settings runLimit j D A.net .top runLimit _
    (fun _ => Nat.zero_le _) x hx
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hq
  split at hq
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hq
    rw [hq]
    trivial
  · rw [StateT.run'_eq, StateT.run_map, support_map] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    exact forgeWalk_guard K circuits settings runLimit forge j D A _ _ _ forge le_rfl (hforge _ _) _ _ hb y hy

/-! ## The reduction side of the laws -/

/-- Hybrid `j` cut at bottom slot `j`, with the outputs of the setup of a live slot through `post`. It
runs the prefix, at a live place the setup of the slot as its own phase, and the game after the slot. -/
def bottomCutGameWith (post : (C.Party → Option (Keys C)) → ProbComp (C.Party → Option (Keys C))) (j : ℕ)
    (D : C.Coalition) (A : DkgTsigAdversary C E) : OracleComp (WorldSpec C) Unit := do
  match ← bottomPrefix K circuits settings runLimit j D A with
  | .live p adversary heads => do
    let r ← executePhase worldRoles D A.net noFunctionality setupRounds adversary
      fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))
    let outputs ← free (liftComp (post r.2) (LocalSpec C))
    bottomRest K circuits settings runLimit j D A (.live p r.1 heads) outputs
  | place => bottomRest K circuits settings runLimit j D A place fun _ => none

theorem noProg_bottomCutGameWith (post : (C.Party → Option (Keys C)) → ProbComp (C.Party → Option (Keys C)))
    (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) :
    NoCall WorldProgramQuery (bottomCutGameWith K circuits settings runLimit post j D A) := by
  unfold bottomCutGameWith
  refine noCall_bind _ (noProg_bottomPrefix K circuits settings runLimit j D A) fun place => ?_
  cases place with
  | live p adversary heads =>
    exact noCall_bind _ (Collision.noProgram_executePhase D A.net _ _ _) fun r =>
      noCall_bind _ (Collision.noProgram_free _) fun outputs => noProg_bottomRest K circuits settings runLimit j D A _ _
  | finished => exact noProg_bottomRest K circuits settings runLimit j D A _ _
  | dead p => exact noProg_bottomRest K circuits settings runLimit j D A _ _
  | skip p adversary heads => exact noProg_bottomRest K circuits settings runLimit j D A _ _

theorem bind_map_congr_support {α β γ : Type} {m₁ : ProbComp α} {m₂ : ProbComp β} {φ : β → α}
    {f : α → ProbComp γ} {g : β → ProbComp γ} (h : m₁ = φ <$> m₂) (hfg : ∀ b ∈ support m₂, f (φ b) =ᵈ g b) :
    m₁ >>= f =ᵈ m₂ >>= g := by
  subst h
  rw [bind_map_left]
  exact EvalDistEq.bind_congr_of_support (spec := unifSpec) m₂ hfg

/-- An idle place of the reduction. The phase of the challenger leaves the state of the reduction, and
the distinguisher ignores the outputs. -/
theorem bottomView_idle (post : (C.Party → Option (Keys C)) → ProbComp (C.Party → Option (Keys C)))
    (D : C.Coalition) (A : DkgTsigAdversary C E) (forge j : ℕ) (place : BottomPlace C A.net.State)
    (hplace : ∀ p a h, place ≠ .live p a h) (hg : PlaceGuard runLimit forge j D place) (priv : KeyJointState C)
    (h0 : HashCache C) :
    ((simulateQ (worldAnswer prims) (executePhase worldRoles D (bottomReduction K circuits settings runLimit prims j D A)
        noFunctionality setupRounds (priv, place) fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C)))).run h0
        >>= fun a => (fun x => x.1) <$> (simulateQ (localAnswer prims)
          (postZ post (bottomDistinguisher K circuits settings runLimit prims forge j D A) a.1)).run a.2) =ᵈ
      (fun p => decide (UsedHit D p.1.2)) <$> (simulateQ (localAnswer prims)
        ((simulateQ (slotHandler prims D) (bottomRest K circuits settings runLimit j D A place fun _ => none)).run
          priv)).run h0 := by
  let R := bottomReduction K circuits settings runLimit prims j D A
  let st : R.State := (priv, place)
  let phase := executePhase worldRoles D R noFunctionality setupRounds st
    fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))
  let Z0 : OracleComp (LocalSpec C) Bool := (fun x => decide (UsedHit D x.2)) <$>
    (simulateQ (slotHandler prims D) (bottomRest K circuits settings runLimit j D A place fun _ => none)).run priv
  have hround : ∀ sent, R.round st sent = pure (st, fun _ _ => none) := by
    intro sent
    cases place with
    | live p a h => exact absurd rfl (hplace p a h)
    | _ => rfl
  have hidle := executePhase_idle D R st hround setupRounds fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))
  have hrest : ∀ out : C.Party → Option (Keys C),
      bottomRest K circuits settings runLimit j D A place out =
        bottomRest K circuits settings runLimit j D A place fun _ => none := by
    intro out
    cases place with
    | live p a h => exact absurd rfl (hplace p a h)
    | _ => rfl
  have hdrop : ((simulateQ (worldAnswer prims) phase).run h0 >>= fun a =>
      (fun x => x.1) <$> (simulateQ (localAnswer prims)
        (postZ post (bottomDistinguisher K circuits settings runLimit prims forge j D A) a.1)).run a.2) =ᵈ
      (simulateQ (worldAnswer prims) (phase >>= fun _ => worldRoles.adversary Z0)).run' h0 := by
    rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
    refine EvalDistEq.bind_congr_of_support (spec := unifSpec) ((simulateQ (worldAnswer prims) phase).run h0)
      fun a ha => ?_
    have ha' : a.1 ∈ support phase := support_simulateQ_run'_subset (worldAnswer prims) _ h0 (by
      rw [StateT.run'_eq, support_map]
      exact ⟨a, ha, rfl⟩)
    have hst : a.1.1 = st := hidle a.1 ha'
    obtain ⟨⟨st', out⟩, h1⟩ := a
    dsimp only at hst
    subst hst
    rw [simulateQ_world_adversary]
    simp only [postZ, simulateQ_bind, simulateQ_local_sample_seedGensecurity, StateT.run_bind,
      StateT.run_lift, bind_assoc, pure_bind, map_bind]
    have hZ : ∀ outputs, bottomDistinguisher K circuits settings runLimit prims forge j D A ((priv, place), outputs) =
        Z0 := by
      intro outputs
      unfold bottomDistinguisher
      rw [ite_eq_left hg, hrest]
    simp only [st, hZ]
    exact EvalDistEq.bind_const (post out) ((fun x => x.1) <$> (simulateQ (localAnswer prims) Z0).run h1)
  refine hdrop.trans ?_
  refine (discardAnswer prims phase (worldRoles.adversary Z0) h0
    (Collision.noProgram_executePhase D _ setupRounds st _) (Collision.noProgram_adversary Z0)).trans ?_
  rw [simulateQ_world_adversary, StateT.run'_eq]
  simp only [Z0, simulateQ_map, StateT.run_map, Functor.map_map]
  exact EvalDistEq.rfl

/-- The reduction of bottom slot `j` with the real challenger and the distinguisher after `post`
accepts with the probability of `UsedHit` in the cut of hybrid `j` with `post`. -/
theorem bottomReductionViewWith (post : (C.Party → Option (Keys C)) → ProbComp (C.Party → Option (Keys C)))
    (D : C.Coalition) (A : DkgTsigAdversary C E) (forge j : ℕ)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge) :
    accepts prims (distinguish (setupExec D (bottomReduction K circuits settings runLimit prims j D A) [])
        (postZ post (bottomDistinguisher K circuits settings runLimit prims forge j D A))) =
      usedHitProb prims D ((fun _ => true) <$> bottomCutGameWith K circuits settings runLimit post j D A) := by
  have hpart := partition_run prims D ((fun _ => true) <$> bottomCutGameWith K circuits settings runLimit post j D A)
    (allQueries_of_noCall (noCall_map _ _ (noProg_bottomCutGameWith K circuits settings runLimit post j D A)))
    ∅ keyJointInitial
  rw [mergeSetup_empty] at hpart
  unfold usedHitProb
  rw [hpart, accepts_eq_probOutput]
  have key : (simulateQ (worldAnswer prims) (distinguish (setupExec D
      (bottomReduction K circuits settings runLimit prims j D A) [])
      (postZ post (bottomDistinguisher K circuits settings runLimit prims forge j D A)))).run' ∅ =ᵈ
      (fun z => decide (UsedHit D z.1.2)) <$> (simulateQ (localAnswer prims)
        ((simulateQ (slotHandler prims D) ((fun _ => true) <$>
          bottomCutGameWith K circuits settings runLimit post j D A)).run keyJointInitial)).run ∅ := by
    have hstart : ∀ x z (h : HashCache C),
        (simulateQ (localAnswer prims) ((bottomReduction K circuits settings runLimit prims j D A).start x z)).run h =
          (fun p => (((p.1.2, p.1.1) : (bottomReduction K circuits settings runLimit prims j D A).State), p.2)) <$>
            (simulateQ (localAnswer prims) ((simulateQ (slotHandler prims D)
              (bottomPrefix K circuits settings runLimit j D A)).run keyJointInitial)).run h := by
      intro x z h
      change (simulateQ (localAnswer prims) ((fun r => (r.2, r.1)) <$> (simulateQ (slotHandler prims D)
        (bottomPrefix K circuits settings runLimit j D A)).run keyJointInitial)).run h = _
      rw [simulateQ_map, StateT.run_map]
    simp only [distinguish, setupExec, realExecution, bind_assoc, simulateQ_bind, StateT.run'_eq,
      StateT.run_bind, map_bind, simulateQ_world_adversary, bottomCutGameWith, simulateQ_map, StateT.run_map]
    refine bind_map_congr_support (hstart _ _ ∅) fun z hz => ?_
    obtain ⟨⟨place, priv⟩, h0⟩ := z
    have hg := bottomPrefix_guard K circuits settings runLimit forge j D A hforge place
      (mem_support_twoLevel prims D _ keyJointInitial ∅ ((place, priv), h0) hz)
    simp only [Functor.map_map]
    cases place with
    | live p adversary heads =>
      have hc := executePhase_coupling prims D A.net (bottomReduction K circuits settings runLimit prims j D A)
        (fun priv st => (priv, BottomPlace.live p st heads)) (fun _ _ _ => rfl) setupRounds adversary
        (fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))) (fun i => setupKeys_setup i) priv h0
      simp only
      rw [← hc, bind_map_left]
      simp only [simulateQ_bind, StateT.run_bind, map_bind]
      refine EvalDistEq.bind_congr EvalDistEq.rfl fun w => ?_
      rw [honest_run prims D _ (free_setup (liftComp_setup _)) _ _, simulateQ_world_sample]
      have hg' : PlaceGuard runLimit forge j D (BottomPlace.live p w.1.1.1 heads) := hg
      simp only [postZ, bottomDistinguisher, hg', ite_true, simulateQ_bind, simulateQ_local_sample_seedGensecurity,
        StateT.run_bind, StateT.run_lift, simulateQ_map, StateT.run_map, Functor.map_map, bind_assoc, pure_bind,
        map_bind, bind_map_left]
      exact EvalDistEq.rfl
    | finished =>
      exact bottomView_idle K circuits settings runLimit prims post D A forge j .finished
        (fun _ _ _ h => by simp at h) hg priv h0
    | dead p =>
      exact bottomView_idle K circuits settings runLimit prims post D A forge j (.dead p)
        (fun _ _ _ h => by simp at h) hg priv h0
    | skip p adversary heads =>
      exact bottomView_idle K circuits settings runLimit prims post D A forge j (.skip p adversary heads)
        (fun _ _ _ h => by simp at h) hg priv h0
  rw [key.prEvent_eq, prEvent_map, prEvent_map]
  simp only [decide_eq_true_eq, usedHit_mergeSetup]

/-- The game side of the real law of bottom slot `j`. -/
def BottomGameCut : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (forge : ℕ),
    (∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge) →
    ∀ j, runLimit ≤ j → j < gameSetups runLimit →
    fixedProb K circuits settings runLimit prims D A j =
      usedHitProb prims D ((fun _ => true) <$> bottomCutGameWith K circuits settings runLimit pure j D A)

/-- The game side of the fresh law of bottom slot `j`. -/
def BottomGameCutFresh : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (forge : ℕ),
    (∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge) →
    ∀ j, runLimit ≤ j → j < gameSetups runLimit →
    fixedProb K circuits settings runLimit prims D A (j + 1) =
      usedHitProb prims D ((fun _ => true) <$> bottomCutGameWith K circuits settings runLimit (freshPost D) j D A)

/-- `BottomLawReal` from its game side. -/
theorem bottomLawReal_of_cut (cut : BottomGameCut K circuits settings runLimit prims) :
    BottomLawReal K circuits settings runLimit prims := by
  intro D A forge hforge j hlo hhi
  rw [cut D A forge hforge j hlo hhi, ← bottomReductionViewWith K circuits settings runLimit prims pure D A forge j hforge,
    postZ_pure]

/-- `BottomLawFresh` from its game side. -/
theorem bottomLawFresh_of_cut (cut : BottomGameCutFresh K circuits settings runLimit prims) :
    BottomLawFresh K circuits settings runLimit prims := by
  intro D A forge hforge j hlo hhi
  rw [cut D A forge hforge j hlo hhi, seedGenHiddenZ_eq,
    bottomReductionViewWith K circuits settings runLimit prims (freshPost D) D A forge j hforge]

/-! ## The walk of `forge` with the pause as data -/

/-- `forgeWalk` without the end, with the oracles of hybrid `h`. It gives the forgery at the end of
`forge`, or the pause at the request of the run of slot `j`. -/
def walkCore (h j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (keys : Keys C) (top : TopTree) :
    OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery →
      StateT (TsigState C) (RealM C A.net.State) (Forgery ⊕ BottomPause C A.net.State)
  | .pure forgery => pure (.inl forgery)
  | .liftBind (Sum.inr (Sum.inl (.tree b))) next => do
      let s ← StateT.lift get
      if mayRun runLimit D s (.bottom b) ∧ fixedSlot runLimit s.runs (.bottom b) + slotParity runLimit j = j then do
        let tsig ← get
        pure (.inr ⟨s, tsig, keys, top, b, next⟩)
      else do
        let answer ← signingImpl K circuits settings runLimit h D A (Sum.inr (Sum.inl (.tree b)))
        walkCore h j D A keys top (next answer)
  | .liftBind t next => do
      let answer ← signingImpl K circuits settings runLimit h D A t
      walkCore h j D A keys top (next answer)

/-- The win test of `forge` with the keys `keys` and the top tree `top`. -/
def winTest {σ : Type} (D : C.Coalition) (keys : Keys C) (top : TopTree) (forgery : Forgery) :
    StateT (TsigState C) (RealM C σ) Bool := do
  let st ← get
  StateT.lift (do
    let s ← get
    forgeryWins realLift (canonicalDealt D s.operators keys.parameter top) st forgery)

/-- The end of `forgeWalk` after `walkCore`. -/
def walkEnd (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (keys : Keys C) (top : TopTree) :
    Forgery ⊕ BottomPause C A.net.State → StateT (TsigState C) (RealM C A.net.State) (BottomPlace C A.net.State)
  | .inl forgery => do
      let _ ← winTest D keys top forgery
      pure .finished
  | .inr p => StateT.lift (StateT.lift (pauseAt K circuits settings runLimit j D A p))

/-- The rest of hybrid `j` after `walkCore`. -/
def walkRest (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (keys : Keys C) (top : TopTree) :
    Forgery ⊕ BottomPause C A.net.State → StateT (TsigState C) (RealM C A.net.State) Bool
  | .inl forgery => winTest D keys top forgery
  | .inr p => do
      let answer ← signingImpl K circuits settings runLimit j D A (Sum.inr (Sum.inl (.tree p.b)))
      let forgery ← simulateQ (signingImpl K circuits settings runLimit j D A) (p.next answer)
      winTest D keys top forgery

theorem lift_get_bind_const {τ σ α : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (x : StateT τ (StateT σ m) α) :
    (StateT.lift get : StateT τ (StateT σ m) σ) >>= (fun _ => x) = x := by
  ext st s
  simp [StateT.run_bind, StateT.run_lift]

theorem get_bind_const {σ α : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (x : StateT σ m α) :
    (get : StateT σ m σ) >>= (fun _ => x) = x := by
  ext s
  simp

/-- `forgeWalk` is `walkCore` and then its end. -/
theorem forgeWalk_eq (j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (keys : Keys C) (top : TopTree)
    (oa : OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery) :
    forgeWalk K circuits settings runLimit j D A keys top oa =
      walkCore K circuits settings runLimit j j D A keys top oa >>= walkEnd K circuits settings runLimit j D A keys top := by
  induction oa using OracleComp.inductionOn with
  | pure forgery =>
    change forgeWalk K circuits settings runLimit j D A keys top (PFunctor.FreeM.pure forgery) =
      walkCore K circuits settings runLimit j j D A keys top (PFunctor.FreeM.pure forgery) >>= _
    simp only [forgeWalk, walkCore, pure_bind, walkEnd, winTest, bind_assoc]
  | query_bind t next ih =>
    change forgeWalk K circuits settings runLimit j D A keys top (PFunctor.FreeM.liftBind t next) =
      walkCore K circuits settings runLimit j j D A keys top (PFunctor.FreeM.liftBind t next) >>= _
    by_cases ht : ∃ b, t = .inr (.inl (.tree b))
    · obtain ⟨b, rfl⟩ := ht
      simp only [forgeWalk, walkCore, bind_assoc]
      refine bind_congr fun s => ?_
      split_ifs
      · simp only [bind_assoc, pure_bind, walkEnd]
      · simp only [bind_assoc, ih]
    · rcases t with u | (q | q)
      · simp only [forgeWalk, walkCore, bind_assoc, ih]
      · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
        · simp only [forgeWalk, walkCore, bind_assoc, ih]
        · exact absurd ⟨b, rfl⟩ ht
        · simp only [forgeWalk, walkCore, bind_assoc, ih]
        · simp only [forgeWalk, walkCore, bind_assoc, ih]
      · simp only [forgeWalk, walkCore, bind_assoc, ih]

/-- The signing phase of hybrid `j` is `walkCore` and then the rest of hybrid `j`. -/
theorem simulateQ_signing_eq (h j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (keys : Keys C) (top : TopTree)
    (oa : OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery) :
    simulateQ (signingImpl K circuits settings runLimit h D A) oa >>= winTest D keys top =
      walkCore K circuits settings runLimit h j D A keys top oa >>= walkRest K circuits settings runLimit h D A keys top := by
  induction oa using OracleComp.inductionOn with
  | pure forgery =>
    change simulateQ (signingImpl K circuits settings runLimit h D A) (pure forgery) >>= _ =
      walkCore K circuits settings runLimit h j D A keys top (PFunctor.FreeM.pure forgery) >>= _
    simp only [simulateQ_pure, pure_bind, walkCore, walkRest]
  | query_bind t next ih =>
    rw [simulateQ_query_bind, bind_assoc]
    change _ = walkCore K circuits settings runLimit h j D A keys top (PFunctor.FreeM.liftBind t next) >>= _
    by_cases ht : ∃ b, t = .inr (.inl (.tree b))
    · obtain ⟨b, rfl⟩ := ht
      simp only [walkCore, bind_assoc]
      have e : ∀ s : RealState C A.net.State,
          ((if mayRun runLimit D s (.bottom b) ∧ fixedSlot runLimit s.runs (.bottom b) + slotParity runLimit j = j then
            (get : StateT (TsigState C) (RealM C A.net.State) _) >>= fun tsig =>
              (pure (Sum.inr ⟨s, tsig, keys, top, b, next⟩) : StateT (TsigState C) (RealM C A.net.State)
                (Forgery ⊕ BottomPause C A.net.State))
          else signingImpl K circuits settings runLimit h D A (Sum.inr (Sum.inl (.tree b))) >>= fun answer =>
            walkCore K circuits settings runLimit h j D A keys top (next answer)) >>=
            walkRest K circuits settings runLimit h D A keys top) =
          (signingImpl K circuits settings runLimit h D A (Sum.inr (Sum.inl (.tree b))) >>= fun answer =>
            simulateQ (signingImpl K circuits settings runLimit h D A) (next answer) >>= winTest D keys top) := by
        intro s
        split_ifs
        · simp only [bind_assoc, pure_bind, walkRest]
          exact get_bind_const _
        · simp only [bind_assoc, ih]
      simp only [e]
      exact (lift_get_bind_const _).symm
    · have hstep : (signingImpl K circuits settings runLimit h D A t >>= fun answer =>
          simulateQ (signingImpl K circuits settings runLimit h D A) (next answer) >>= winTest D keys top) =
          (signingImpl K circuits settings runLimit h D A t >>= fun answer =>
            walkCore K circuits settings runLimit h j D A keys top (next answer)) >>=
            walkRest K circuits settings runLimit h D A keys top := by
        simp only [bind_assoc, ih]
      rcases t with u | (q | q)
      · (simp only [walkCore]; exact hstep)
      · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
        · (simp only [walkCore]; exact hstep)
        · exact absurd ⟨b, rfl⟩ ht
        · (simp only [walkCore]; exact hstep)
        · (simp only [walkCore]; exact hstep)
      · (simp only [walkCore]; exact hstep)

theorem run_bind_two {σ τ α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m] (x : StateT τ (StateT σ m) α)
    (f : α → StateT τ (StateT σ m) β) (st : τ) (s : σ) :
    ((x >>= f).run st).run s = (x.run st).run s >>= fun q => ((f q.1.1).run q.1.2).run q.2 := by
  rw [StateT.run_bind, StateT.run_bind]

/-- The facts at a pause that `walkCore` reaches. -/
theorem walkCore_support (h j forge : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (keys : Keys C) (top : TopTree)
    (oa : OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery) :
    ∀ n, n ≤ forge → IsQueryBoundP oa (ForgeInClass .prssSetup) n → ∀ (st : TsigState C) (s : RealState C A.net.State),
      RunsBounded runLimit s →
      ∀ r ∈ support (((walkCore K circuits settings runLimit h j D A keys top oa).run st).run s), ∀ p,
        r.1.1 = .inr p → PauseInRange runLimit forge j p ∧ mayRun runLimit D p.state (.bottom p.b) ∧
          p.tsig = r.1.2 ∧ p.state = r.2 ∧ p.keys = keys ∧ p.top = top := by
  induction oa using OracleComp.inductionOn with
  | pure forgery =>
    intro n _ _ st s _ r hr p hp
    change r ∈ support (((walkCore K circuits settings runLimit h j D A keys top (PFunctor.FreeM.pure forgery)).run
      st).run s) at hr
    simp only [walkCore, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp at hp
  | query_bind t next ih =>
    intro n hn hb st s hs r hr p hp
    rw [isQueryBoundP_query_bind_iff] at hb
    obtain ⟨_, hnext⟩ := hb
    change r ∈ support (((walkCore K circuits settings runLimit h j D A keys top
      (PFunctor.FreeM.liftBind t next)).run st).run s) at hr
    have hstep : ∀ r ∈ support (((signingImpl K circuits settings runLimit h D A t >>= fun a =>
        walkCore K circuits settings runLimit h j D A keys top (next a)).run st).run s), r.1.1 = .inr p →
        PauseInRange runLimit forge j p ∧ mayRun runLimit D p.state (.bottom p.b) ∧
          p.tsig = r.1.2 ∧ p.state = r.2 ∧ p.keys = keys ∧ p.top = top := by
      intro r hr hp
      rw [run_bind_two, mem_support_bind_iff] at hr
      obtain ⟨q, hq, hr⟩ := hr
      exact ih q.1.1 _ (by split_ifs <;> omega) (hnext q.1.1) q.1.2 q.2
        (signingImpl_bounded K circuits settings runLimit h D A t st s hs q hq) r hr p hp
    by_cases ht : ∃ b, t = .inr (.inl (.tree b))
    · obtain ⟨b, rfl⟩ := ht
      have hQ : ¬ ForgeInClass (C := C) (σ := A.net.State) .prssSetup (.inr (.inl (.tree b))) := fun h => h
      simp only [hQ, ite_false] at hnext
      simp only [walkCore, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_pure, pure_bind] at hr
      split_ifs at hr with hc
      · simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hr
        subst hr
        simp only [Sum.inr.injEq] at hp
        subst hp
        exact ⟨⟨hc.2, hs, FirstCounts.mayRun_lt runLimit hc.1, fun a => (hnext a).mono hn⟩, hc.1, rfl, rfl, rfl, rfl⟩
      · exact hstep r hr hp
    · rcases t with u | (q | q)
      · exact hstep r (by simpa only [walkCore] using hr) hp
      · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
        · exact hstep r (by simpa only [walkCore] using hr) hp
        · exact absurd ⟨b, rfl⟩ ht
        · exact hstep r (by simpa only [walkCore] using hr) hp
        · exact hstep r (by simpa only [walkCore] using hr) hp
      · exact hstep r (by simpa only [walkCore] using hr) hp

/-- Before the run of slot `j` the runs have slots below `j`, so hybrids `j` and `h ≥ j` agree on a
request. -/
theorem fixedTreeRequest_congr_below (h j : ℕ) (hjh : j ≤ h) (hlo : runLimit ≤ j) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight)) (s : RealState C net.State)
    (hk : mayRun runLimit D s (.bottom b) → bottomRuns s.runs < (j - runLimit) / 2) :
    (fixedTreeRequest K circuits settings runLimit h (wrongOutput D) D net b).run s =
      (fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D net b).run s := by
  unfold fixedTreeRequest
  rw [StateT.run_bind, StateT.run_bind]
  congr 1
  simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs with hm
  · have hlt := hk hm
    rw [StateT.run_bind, StateT.run_bind, fixedTreeRun_congr K circuits settings runLimit h j D net _ s fun c hc => ?_]
    have hc' : c < 2 := hc
    refine sampleSlot_eq_lt h j _ ?_ ?_ <;> rw [fixedSlot_bottom_eq] <;> omega
  · rfl

/-- A call of `forge` that is not a request of a tree has one answer in each hybrid. -/
theorem signingImpl_nontree (h h' : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain) (ht : ∀ b, t ≠ .inr (.inl (.tree b))) :
    signingImpl K circuits settings runLimit h D A t = signingImpl K circuits settings runLimit h' D A t := by
  rcases t with u | (q | q)
  · change (StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query u)))) :
      StateT (TsigState C) (RealM C A.net.State) _) =
      (StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift (OracleSpec.query u)))) :
      StateT (TsigState C) (RealM C A.net.State) _)
    rfl
  · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
    · change (pure (noAnswer (.corrupt i)) : StateT (TsigState C) (RealM C A.net.State) _) =
        (pure (noAnswer (.corrupt i)) : StateT (TsigState C) (RealM C A.net.State) _)
      rfl
    · exact absurd rfl (ht b)
    · change signRequest D i e (.round1 i J e message) = signRequest D i e (.round1 i J e message)
      rfl
    · change signRequest D i e (.round2 i J e message parts) = signRequest D i e (.round2 i J e message parts)
      rfl
  · rcases q with _ | state
    · change (StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _)) :
        StateT (TsigState C) (RealM C A.net.State) _) =
        (StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _)) : StateT (TsigState C) (RealM C A.net.State) _)
      rfl
    · change (StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state }) :
        StateT (TsigState C) (RealM C A.net.State) _) =
        (StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state }) :
        StateT (TsigState C) (RealM C A.net.State) _)
      rfl

private theorem fixedTreeRequest_state (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) (s : RealState C net.State) :
    ∀ r ∈ support ((fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D net b).run s),
      ∃ x ∈ support ((fixedTreeRuns K circuits settings runLimit j (wrongOutput D) D net (.bottom b) 1).run s),
        r.2 = x.2 := by
  unfold fixedTreeRequest
  rw [StateT.run_bind]
  intro r hr
  obtain ⟨x, hx, hy⟩ := OracleComp.mem_support_bind_peel _ _ hr
  exact ⟨x, hx, (requestRest_adds D b x.2).2 r hy⟩

private theorem fixedTreeRuns_one (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (tree : Tree) (s : RealState C net.State) :
    (fixedTreeRuns K circuits settings runLimit j (wrongOutput D) D net tree 1).run s =
      if mayRun runLimit D s tree then (fixedTreeRun K circuits settings runLimit j (wrongOutput D) D net tree).run s
      else pure ((), s) := by
  simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · simp only [StateT.run_bind, StateT.run_pure]
    exact bind_pure _
  · rfl

/-- A request increments the bottom run count exactly when the guard permits a run. -/
private theorem fixedTreeRequest_bottomRuns (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) (s : RealState C net.State) :
    ∀ r ∈ support ((fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D net b).run s),
      bottomRuns r.2.runs = if mayRun runLimit D s (.bottom b) then bottomRuns s.runs + 1 else bottomRuns s.runs := by
  intro r hr
  obtain ⟨x, hx, he⟩ := fixedTreeRequest_state K circuits settings runLimit j D net b s r hr
  rw [he]
  rw [fixedTreeRuns_one] at hx
  split_ifs at hx ⊢ with hm
  · rw [fixedTreeRun_runs K circuits settings runLimit j D net _ s x hx, bottomRuns_update]
  · obtain rfl := OracleComp.eq_of_mem_support_pure _ hx
    rfl

theorem fixedTreeRequest_runs_le (j : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty)
    (b : Fin (2 ^ layerHeight)) (s : RealState C net.State) (k : ℕ)
    (hk : mayRun runLimit D s (.bottom b) → bottomRuns s.runs < k) (hs : bottomRuns s.runs ≤ k) :
    ∀ r ∈ support ((fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D net b).run s),
      bottomRuns r.2.runs ≤ k := by
  intro r hr
  rw [fixedTreeRequest_bottomRuns K circuits settings runLimit j D net b s r hr]
  split
  · exact hk (by assumption)
  · exact hs

/-- `walkCore` reads only slots below `j` before the pause, so the hybrid of its oracles does not matter
for `h ≥ j`. -/
theorem walkCore_congr (h j : ℕ) (hjh : j ≤ h) (hlo : runLimit ≤ j) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (keys : Keys C) (top : TopTree) (oa : OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery) :
    ∀ (st : TsigState C) (s : RealState C A.net.State), bottomRuns s.runs ≤ (j - runLimit) / 2 →
      ((walkCore K circuits settings runLimit h j D A keys top oa).run st).run s =
        ((walkCore K circuits settings runLimit j j D A keys top oa).run st).run s := by
  induction oa using OracleComp.inductionOn with
  | pure forgery => intro st s _; rfl
  | query_bind t next ih =>
    intro st s hs
    change ((walkCore K circuits settings runLimit h j D A keys top (PFunctor.FreeM.liftBind t next)).run st).run s =
      ((walkCore K circuits settings runLimit j j D A keys top (PFunctor.FreeM.liftBind t next)).run st).run s
    by_cases ht : ∃ b, t = .inr (.inl (.tree b))
    · obtain ⟨b, rfl⟩ := ht
      simp only [walkCore, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_pure, pure_bind]
      split_ifs with hc
      · rfl
      · have hk : mayRun runLimit D s (.bottom b) → bottomRuns s.runs < (j - runLimit) / 2 := by
          intro hm
          have hne : fixedSlot runLimit s.runs (.bottom b) + slotParity runLimit j ≠ j := fun e => hc ⟨hm, e⟩
          rw [fixedSlot_bottom_eq] at hne
          unfold slotParity at hne
          omega
        have e : ((signingImpl K circuits settings runLimit h D A (.inr (.inl (.tree b)))).run st).run s =
            ((signingImpl K circuits settings runLimit j D A (.inr (.inl (.tree b)))).run st).run s :=
          lift_run_congr _ _ st s (fixedTreeRequest_congr_below K circuits settings runLimit h j hjh hlo D A.net b s hk)
        rw [run_bind_two, run_bind_two, e]
        refine bind_congr_of_forall_mem_support _ fun q hq => ih q.1.1 q.1.2 q.2 ?_
        change q ∈ support (((StateT.lift (fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D A.net b) :
          StateT (TsigState C) (RealM C A.net.State) _).run st).run s) at hq
        rw [run_lift_tsig, support_map] at hq
        obtain ⟨x, hx, rfl⟩ := hq
        exact fixedTreeRequest_runs_le K circuits settings runLimit j D A.net b s _ hk hs x hx
    · have hsig : ∀ st' s', ((signingImpl K circuits settings runLimit h D A t).run st').run s' =
          ((signingImpl K circuits settings runLimit j D A t).run st').run s' := by
        intro st' s'
        rw [signingImpl_nontree K circuits settings runLimit h j D A t fun b e => ht ⟨b, e⟩]
      have hstep : ((signingImpl K circuits settings runLimit h D A t >>= fun a =>
          walkCore K circuits settings runLimit h j D A keys top (next a)).run st).run s =
          ((signingImpl K circuits settings runLimit j D A t >>= fun a =>
          walkCore K circuits settings runLimit j j D A keys top (next a)).run st).run s := by
        rw [run_bind_two, run_bind_two, hsig]
        refine bind_congr_of_forall_mem_support _ fun q hq => ih q.1.1 q.1.2 q.2 ?_
        rw [(signingImpl_quiet K circuits settings runLimit j D A t (fun b e => ht ⟨b, e⟩) st s).2 q hq]
        exact hs
      rcases t with u | (q | q)
      · simpa only [walkCore] using hstep
      · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
        · simpa only [walkCore] using hstep
        · exact absurd ⟨b, rfl⟩ ht
        · simpa only [walkCore] using hstep
        · simpa only [walkCore] using hstep
      · simpa only [walkCore] using hstep

/-- The top runs have slots below `runLimit ≤ j`, so hybrids `j` and `h ≥ j` agree on them. -/
theorem fixedTreeRuns_top_congr_below (h j : ℕ) (hjh : j ≤ h) (hlo : runLimit ≤ j) (D : C.Coalition)
    (net : Adversary C E Unit PEmpty PEmpty) :
    ∀ (m : ℕ) (s : RealState C net.State),
      (fixedTreeRuns K circuits settings runLimit h (wrongOutput D) D net .top m).run s =
        (fixedTreeRuns K circuits settings runLimit j (wrongOutput D) D net .top m).run s
  | 0, s => rfl
  | m + 1, s => by
    simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with hm
    · have hlt := FirstCounts.mayRun_lt runLimit hm
      rw [StateT.run_bind, StateT.run_bind, fixedTreeRun_congr K circuits settings runLimit h j D net .top s
        fun c hc => sampleSlot_eq_lt h j _ (by simp only [fixedSlot, treeSetups] at hc ⊢; omega)
          (by simp only [fixedSlot, treeSetups] at hc ⊢; omega)]
      exact bind_congr fun p => fixedTreeRuns_top_congr_below h j hjh hlo D net m p.2
    · rfl

theorem signingImpl_runs_mono (h : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain) (st : TsigState C) (s : RealState C A.net.State) :
    ∀ r ∈ support (((signingImpl K circuits settings runLimit h D A t).run st).run s),
      bottomRuns s.runs ≤ bottomRuns r.2.runs := by
  intro r hr
  by_cases ht : ∃ b, t = .inr (.inl (.tree b))
  · obtain ⟨b, rfl⟩ := ht
    change r ∈ support (((StateT.lift (fixedTreeRequest K circuits settings runLimit h (wrongOutput D) D A.net b) :
      StateT (TsigState C) (RealM C A.net.State) _).run st).run s) at hr
    rw [run_lift_tsig, support_map] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    rw [fixedTreeRequest_bottomRuns K circuits settings runLimit h D A.net b s q hq]
    split <;> omega
  · rw [(signingImpl_quiet K circuits settings runLimit h D A t (fun b e => ht ⟨b, e⟩) st s).2 r hr]

theorem fixedTreeRequest_congr_above (j h : ℕ) (hjh : j ≤ h) (hh : h ≤ j + 1) (hlo : runLimit ≤ j)
    (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight)) (s : RealState C net.State)
    (hs : (j - runLimit) / 2 + 1 ≤ bottomRuns s.runs) :
    (fixedTreeRequest K circuits settings runLimit j (wrongOutput D) D net b).run s =
      (fixedTreeRequest K circuits settings runLimit h (wrongOutput D) D net b).run s := by
  unfold fixedTreeRequest
  rw [StateT.run_bind, StateT.run_bind]
  congr 1
  simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs
  · rw [StateT.run_bind, StateT.run_bind, fixedTreeRun_congr K circuits settings runLimit j h D net _ s
      fun c _ => sampleSlot_eq j h _ (by rw [fixedSlot_bottom_eq]; omega) (by rw [fixedSlot_bottom_eq]; omega)]
  · rfl

/-- After the run of slot `j` the runs have slots above `j`, so hybrids `j` and `j + 1` agree on the rest
of `forge`. -/
theorem signing_congr_above (j : ℕ) (hlo : runLimit ≤ j) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (oa : OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery) (st : TsigState C)
    (s : RealState C A.net.State) (hs : (j - runLimit) / 2 + 1 ≤ bottomRuns s.runs) :
    ((simulateQ (signingImpl K circuits settings runLimit j D A) oa).run st).run s =
      ((simulateQ (signingImpl K circuits settings runLimit (j + 1) D A) oa).run st).run s := by
  refine simulateQ_run_congr_inv _ _ (fun s : RealState C A.net.State => (j - runLimit) / 2 + 1 ≤ bottomRuns s.runs)
    (fun t st s hs => ?_) (fun t st s hs r hr => le_trans hs
      (signingImpl_runs_mono K circuits settings runLimit j D A t st s r hr)) oa st s hs
  by_cases ht : ∃ b, t = .inr (.inl (.tree b))
  · obtain ⟨b, rfl⟩ := ht
    exact lift_run_congr _ _ st s (fixedTreeRequest_congr_above K circuits settings runLimit j (j + 1) (Nat.le_succ j) le_rfl hlo D A.net b s hs)
  · rw [signingImpl_nontree K circuits settings runLimit j (j + 1) D A t fun b e => ht ⟨b, e⟩]

/-- The game after the prefix of the cut, from the place. -/
def cutRest (post : (C.Party → Option (Keys C)) → ProbComp (C.Party → Option (Keys C))) (j : ℕ) (D : C.Coalition)
    (A : DkgTsigAdversary C E) : BottomPlace C A.net.State → OracleComp (WorldSpec C) Unit
  | .live p adversary heads => do
    let r ← executePhase worldRoles D A.net noFunctionality setupRounds adversary
      fun i => (setupKeys .prss i : PartyM C E RealSpec (Keys C))
    let outputs ← free (liftComp (post r.2) (LocalSpec C))
    bottomRest K circuits settings runLimit j D A (.live p r.1 heads) outputs
  | place => bottomRest K circuits settings runLimit j D A place fun _ => none

theorem bottomCutGameWith_eq (post : (C.Party → Option (Keys C)) → ProbComp (C.Party → Option (Keys C))) (j : ℕ)
    (D : C.Coalition) (A : DkgTsigAdversary C E) :
    bottomCutGameWith K circuits settings runLimit post j D A =
      bottomPrefix K circuits settings runLimit j D A >>= cutRest K circuits settings runLimit post j D A := by
  unfold bottomCutGameWith
  refine bind_congr fun place => ?_
  cases place <;> rfl

/-- The signing phase of hybrid `h` with the win test as `winTest`. -/
theorem fixedSigning_walk (h : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (s : RealState C A.net.State) :
    (fixedSigning K circuits settings runLimit h (wrongOutput D) D A).run s =
      (match topHolder D s.operators with
        | none => pure false
        | some (keys, top) => (fun p => p.1) <$> (simulateQ (signingImpl K circuits settings runLimit h D A)
            (A.forge ⟨top.root, keys.parameter⟩ top) >>= winTest D keys top).run ⟨D.1, fun _ => none, [], fun _ => none⟩ :
        RealM C A.net.State Bool).run s := by
  unfold fixedSigning
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases topHolder D s.operators with _ | ⟨keys, top⟩
  · rfl
  · simp only [winTest, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, map_bind,
      bind_assoc, map_pure, bind_pure]
    rfl

/-- The request of the tree of a pause in hybrid `h`, as a lift to the signing state. -/
theorem treeRequest_lift_run (h : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (b : Fin (2 ^ layerHeight))
    {β : Type} (k : Option (BottomTree × Digest) → StateT (TsigState C) (RealM C A.net.State) β) (st : TsigState C)
    (s : RealState C A.net.State) :
    ((StateT.lift (fixedTreeRequest K circuits settings runLimit h (wrongOutput D) D A.net b) >>= k).run st).run s =
      (fixedTreeRequest K circuits settings runLimit h (wrongOutput D) D A.net b).run s >>= fun q =>
        ((k q.1).run st).run q.2 := by
  rw [run_bind_two, run_lift_tsig, bind_map_left]

/-- The game after the pause in hybrid `h`, as the run of the tree and `resumeAfter`. -/
theorem walkRest_pause (h j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (p : BottomPause C A.net.State)
    (hm : mayRun runLimit D p.state (.bottom p.b))
    (hsig : ∀ (oa : OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery) st
      (s : RealState C A.net.State), (j - runLimit) / 2 + 1 ≤ bottomRuns s.runs →
      ((simulateQ (signingImpl K circuits settings runLimit h D A) oa).run st).run s =
        ((simulateQ (signingImpl K circuits settings runLimit (j + 1) D A) oa).run st).run s)
    (hk : bottomRuns p.state.runs = (j - runLimit) / 2) :
    (fun _ => ()) <$> ((walkRest K circuits settings runLimit h D A p.keys p.top (.inr p)).run p.tsig).run p.state =
      (fixedTreeRun K circuits settings runLimit h (wrongOutput D) D A.net (.bottom p.b)).run p.state >>= fun x =>
        resumeAfter K circuits settings runLimit j D A p x.2 := by
  have e : walkRest K circuits settings runLimit h D A p.keys p.top (.inr p) =
      StateT.lift (fixedTreeRequest K circuits settings runLimit h (wrongOutput D) D A.net p.b) >>= fun answer =>
        simulateQ (signingImpl K circuits settings runLimit h D A) (p.next answer) >>= winTest D p.keys p.top := rfl
  rw [e, treeRequest_lift_run]
  unfold fixedTreeRequest
  simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind, hm, ite_true, bind_assoc, StateT.run_pure,
    map_bind]
  refine bind_congr_of_forall_mem_support _ fun x hx => ?_
  have hx' := fixedTreeRun_runs K circuits settings runLimit h D A.net _ p.state x hx
  unfold resumeAfter
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  refine bind_congr_of_forall_mem_support _ fun y hy => ?_
  obtain ⟨answer, s2⟩ := y
  have hs2 : s2 = x.2 := (requestRest_adds D p.b x.2).2 _ hy
  subst hs2
  rw [hsig _ _ _ (by rw [hx', bottomRuns_update, hk])]
  simp only [winTest, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc, map_bind,
    StateT.run_pure, map_pure]

/-! ## The honest keys through the walk -/

/-- The honest operators with keys hold one parameter. -/
def OneParameter {σ : Type} (D : C.Coalition) (s : RealState C σ) : Prop :=
  ∃ parameter : PublicParameter, ∀ i, i ∉ D.1 → ∀ keys, (s.operators i).keys = some keys → keys.parameter = parameter

theorem oneParameter_stateParameter {σ : Type} (D : C.Coalition) (s : RealState C σ) (h : OneParameter D s) :
    ∀ i, i ∉ D.1 → ∀ keys, (s.operators i).keys = some keys → keys.parameter = stateParameter D s := by
  obtain ⟨parameter, hp⟩ := h
  intro i hi keys hk
  rw [hp i hi keys hk]
  unfold stateParameter gameParameter
  split
  · rename_i i₀ h₀
    have h₁ := List.find?_some h₀
    simp only [decide_eq_true_eq] at h₁
    obtain ⟨k₀, hk₀⟩ := Option.isSome_iff_exists.1 h₁.2
    dsimp only
    rw [hk₀, Option.map_some, Option.getD_some, hp i₀ h₁.1 k₀ hk₀]
  · rename_i h₀
    have := List.find?_eq_none.1 h₀ i (by simp [Committee.parties])
    simp [hi, hk] at this

theorem fixedTreeRun_keys (h : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) :
    ∀ r ∈ support ((fixedTreeRun K circuits settings runLimit h (wrongOutput D) D net tree).run s),
      ∀ i, (r.2.operators i).keys = (s.operators i).keys := by
  intro r hr i
  unfold fixedTreeRun at hr
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc, StateT.run_set,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hr
  cases tree <;> rfl

theorem fixedTreeRuns_keys (h : ℕ) (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) :
    ∀ (count : ℕ) (s : RealState C net.State),
      ∀ r ∈ support ((fixedTreeRuns K circuits settings runLimit h (wrongOutput D) D net tree count).run s),
        ∀ i, (r.2.operators i).keys = (s.operators i).keys
  | 0, s, r, hr, i => by
    simp only [fixedTreeRuns, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
  | count + 1, s, r, hr, i => by
    simp only [fixedTreeRuns, StateT.run_bind, StateT.run_get, pure_bind] at hr
    split_ifs at hr
    · rw [StateT.run_bind, mem_support_bind_iff] at hr
      obtain ⟨x, hx, hr⟩ := hr
      rw [fixedTreeRuns_keys h D net tree count x.2 r hr i, fixedTreeRun_keys K circuits settings runLimit h D net tree s
        x hx i]
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]

theorem signRequest_state {σ : Type} (D : C.Coalition) (i : C.Party) (e : KeyIndex) (q : TsigQuery C)
    (st : TsigState C) (s : RealState C σ) :
    ∀ r ∈ support (((signRequest D i e q).run st).run s),
      r.2 = { s with closed := Function.update s.closed (treeOf e) true } := by
  intro r hr
  unfold signRequest at hr
  simp only [StateT.run_bind, run_lift_tsig, StateT.run_modify, StateT.run_get, map_pure, pure_bind] at hr
  exact (operatorAnswer_adds D _ _ e q st { s with closed := Function.update s.closed (treeOf e) true }).2 r hr

theorem signingImpl_keys (h : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E)
    (t : (LocalSpec C + (TsigSpec C + StateSpec A.net.State)).Domain) (st : TsigState C) (s : RealState C A.net.State) :
    ∀ r ∈ support (((signingImpl K circuits settings runLimit h D A t).run st).run s),
      ∀ i, (r.2.operators i).keys = (s.operators i).keys := by
  intro r hr i
  rcases t with t | q | q
  · change r ∈ support (((StateT.lift (StateT.lift (worldRoles.adversary (OracleComp.lift
      (OracleSpec.query t)))) : StateT (TsigState C) (RealM C A.net.State) _).run st).run s) at hr
    rw [run_lift_tsig, StateT.run_lift, support_map] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hp
    obtain ⟨_, _, rfl⟩ := hp
    rfl
  · rcases q with i' | b | ⟨i', J, e, message⟩ | ⟨i', J, e, message, parts⟩
    · change r ∈ support (((pure (noAnswer (.corrupt i')) : StateT (TsigState C) (RealM C A.net.State) _).run
        st).run s) at hr
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
    · change r ∈ support (((StateT.lift (fixedTreeRequest K circuits settings runLimit h (wrongOutput D) D A.net b) :
        StateT (TsigState C) (RealM C A.net.State) _).run st).run s) at hr
      rw [run_lift_tsig, support_map] at hr
      obtain ⟨q, hq, rfl⟩ := hr
      unfold fixedTreeRequest at hq
      rw [StateT.run_bind, mem_support_bind_iff] at hq
      obtain ⟨x, hx, hq⟩ := hq
      rw [(requestRest_adds D b x.2).2 q hq]
      exact fixedTreeRuns_keys K circuits settings runLimit h D A.net _ 1 s x hx i
    · rw [signRequest_state D i' e (.round1 i' J e message) st s r hr]
    · rw [signRequest_state D i' e (.round2 i' J e message parts) st s r hr]
  · rcases q with _ | state
    · change r ∈ support (((StateT.lift ((·.adversary) <$> (get : RealM C A.net.State _)) :
        StateT (TsigState C) (RealM C A.net.State) _).run st).run s) at hr
      rw [run_lift_tsig, support_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      change p ∈ support (pure (s.adversary, s) : OracleComp (WorldSpec C) _) at hp
      obtain rfl : p = (s.adversary, s) := hp
      rfl
    · change r ∈ support (((StateT.lift (modify fun s : RealState C A.net.State => { s with adversary := state }) :
        StateT (TsigState C) (RealM C A.net.State) _).run st).run s) at hr
      rw [run_lift_tsig, support_map] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      change p ∈ support (pure (PUnit.unit, { s with adversary := state }) : OracleComp (WorldSpec C) _) at hp
      obtain rfl : p = (PUnit.unit, { s with adversary := state }) := hp
      rfl

/-- `walkCore` keeps the keys of the operators. -/
theorem walkCore_keys (h j : ℕ) (D : C.Coalition) (A : DkgTsigAdversary C E) (keys : Keys C) (top : TopTree)
    (oa : OracleComp (LocalSpec C + (TsigSpec C + StateSpec A.net.State)) Forgery) :
    ∀ (st : TsigState C) (s : RealState C A.net.State),
      ∀ r ∈ support (((walkCore K circuits settings runLimit h j D A keys top oa).run st).run s),
        ∀ i, (r.2.operators i).keys = (s.operators i).keys := by
  induction oa using OracleComp.inductionOn with
  | pure forgery =>
    intro st s r hr i
    change r ∈ support (((walkCore K circuits settings runLimit h j D A keys top (PFunctor.FreeM.pure forgery)).run
      st).run s) at hr
    simp only [walkCore, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
  | query_bind t next ih =>
    intro st s r hr i
    change r ∈ support (((walkCore K circuits settings runLimit h j D A keys top
      (PFunctor.FreeM.liftBind t next)).run st).run s) at hr
    have hstep : ∀ r ∈ support (((signingImpl K circuits settings runLimit h D A t >>= fun a =>
        walkCore K circuits settings runLimit h j D A keys top (next a)).run st).run s),
        (r.2.operators i).keys = (s.operators i).keys := by
      intro r hr
      rw [run_bind_two, mem_support_bind_iff] at hr
      obtain ⟨q, hq, hr⟩ := hr
      rw [ih q.1.1 q.1.2 q.2 r hr i, signingImpl_keys K circuits settings runLimit h D A t st s q hq i]
    by_cases ht : ∃ b, t = .inr (.inl (.tree b))
    · obtain ⟨b, rfl⟩ := ht
      simp only [walkCore, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_pure, pure_bind] at hr
      split_ifs at hr
      · simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hr
        rw [hr]
      · exact hstep r hr
    · rcases t with u | (q | q)
      · exact hstep r (by simpa only [walkCore] using hr)
      · rcases q with i' | b | ⟨i', J, e, message⟩ | ⟨i', J, e, message, parts⟩
        · exact hstep r (by simpa only [walkCore] using hr)
        · exact absurd ⟨b, rfl⟩ ht
        · exact hstep r (by simpa only [walkCore] using hr)
        · exact hstep r (by simpa only [walkCore] using hr)
      · exact hstep r (by simpa only [walkCore] using hr)

/-- A bind whose two continuations agree on the support of the first computation in `jointKeyWorld`. -/
theorem JEq.bind_world {D : C.Coalition} {α β : Type} (X : OracleComp (WorldSpec C) α)
    {f g : α → OracleComp (WorldSpec C) β}
    (hfg : ∀ w, ∀ z ∈ support ((simulateQ (jointKeyWorld prims D false) X).run w), JEq prims D (f z.1) (g z.1)) :
    JEq prims D (X >>= f) (X >>= g) := fun w => by
  simp only [simulateQ_bind, StateT.run_bind]
  exact EvalDistEq.bind_congr_of_support (spec := unifSpec) _ fun z hz => hfg w z hz z.2

/-- Hybrid `h ∈ {j, j + 1}` against the cut at bottom slot `j`, from the law of the game after each pause. -/
theorem fixedGame_bottomCut (h : ℕ) (post : (C.Party → Option (Keys C)) → ProbComp (C.Party → Option (Keys C)))
    (D : C.Coalition) (A : DkgTsigAdversary C E) (forge j : ℕ)
    (hforge : ∀ pk top, IsQueryBoundP (A.forge pk top) (ForgeInClass .prssSetup) forge)
    (hlo : runLimit ≤ j) (hjh : j ≤ h)
    (hseed : ∀ w, ∀ z ∈ support ((simulateQ (jointKeyWorld prims D false) (realExecution D A.net noFunctionality
      setupRounds (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [])).run w),
      OneParameter D (startState D z.1.1 z.1.2))
    (hpause : ∀ p : BottomPause C A.net.State, PauseInRange runLimit forge j p →
      mayRun runLimit D p.state (.bottom p.b) → OneParameter D p.state →
      JEq prims D ((fun _ => ()) <$>
          (((walkRest K circuits settings runLimit h D A p.keys p.top (.inr p)).run p.tsig).run p.state))
        (pauseAt K circuits settings runLimit j D A p >>= cutRest K circuits settings runLimit post j D A)) :
    JEq prims D ((fun _ => ()) <$> fixedGame K circuits settings runLimit h D A)
      (bottomCutGameWith K circuits settings runLimit post j D A) := by
  rw [bottomCutGameWith_eq]
  unfold fixedGame fixedRun bottomPrefix
  simp only [map_bind, bind_assoc]
  refine JEq.bind_world prims _ fun w z hz => ?_
  have hone := hseed w z hz
  obtain ⟨⟨state, keys⟩, w'⟩ := z
  dsimp only at hone ⊢
  refine JEq.bind_world prims _ fun w₂ v _ => ?_
  obtain ⟨⟨state, ok⟩, w₂'⟩ := v
  replace hone : OneParameter D (seedState D state keys ok) := by
    obtain ⟨parameter, hpar⟩ := hone
    refine ⟨parameter, fun i hi k hk => hpar i hi k ?_⟩
    cases ok <;> simp_all [seedState, startState, committed]
  dsimp only
  rw [StateT.run_bind, StateT.run_bind, fixedTreeRuns_top_congr_below K circuits settings runLimit h j hjh hlo D A.net]
  simp only [bind_assoc]
  refine JEq.bind_support prims _ fun q hq => ?_
  have hb := fixedTreeRuns_bounded K circuits settings runLimit j D A.net .top runLimit _
    (fun _ => Nat.zero_le _) q hq
  have hkq := fixedTreeRuns_keys K circuits settings runLimit j D A.net .top runLimit _ q hq
  have h0 : bottomRuns q.2.runs = 0 := by
    rw [fixedTreeRuns_top_bottomRuns K circuits settings runLimit j D A.net runLimit _ q hq]
    simp [bottomRuns, seedState, startState]
  rw [fixedSigning_walk K circuits settings runLimit h D A q.2]
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  rcases hk : topHolder D q.2.operators with _ | ⟨keys', top'⟩
  · apply JEq.of_eq
    simp [cutRest, bottomRest]
  · dsimp only
    rw [← StateT.run_bind, simulateQ_signing_eq K circuits settings runLimit h j D A keys' top', StateT.run'_eq,
      forgeWalk_eq K circuits settings runLimit j D A keys' top', StateT.run_map, StateT.run_map,
      run_bind_two, run_bind_two, walkCore_congr K circuits settings runLimit h j hjh hlo D A keys' top' _ _ _
        (by rw [h0]; exact Nat.zero_le _)]
    simp only [map_bind, bind_assoc, Functor.map_map]
    refine JEq.bind_support prims _ fun r hr => ?_
    have hsupp := walkCore_support K circuits settings runLimit j j forge D A keys' top' _ forge le_rfl (hforge _ _) _ q.2
      hb r hr
    obtain ⟨⟨x, st⟩, s'⟩ := r
    cases x with
    | inl f =>
      apply JEq.of_eq
      simp [walkRest, walkEnd, cutRest, bottomRest]
    | inr p =>
      obtain ⟨hp, hm, htsig, hstate, hkeys, htop⟩ := hsupp p rfl
      have hkr := walkCore_keys K circuits settings runLimit j j D A keys' top' _ _ q.2 _ hr
      have hone' : OneParameter D p.state := by
        obtain ⟨parameter, hpar⟩ := hone
        refine ⟨parameter, fun i hi k hk => hpar i hi k ?_⟩
        dsimp only at hstate
        rw [hstate, hkr i, hkq i] at hk
        exact hk
      dsimp only at htsig hstate
      subst htsig hstate hkeys htop
      refine JEq.trans prims (JEq.of_eq prims ?_) ((hpause p hp hm hone').trans prims (JEq.of_eq prims ?_))
      · simp only [map_pure, bind_map_left]
        rw [map_eq_bind_pure_comp]
        rfl
      · simp only [walkEnd, StateT.run_lift]
        simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, map_bind, map_pure]

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.fixedGame_bottomCut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.fixedGame_bottomCut

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomLawReal_of_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.bottomLawReal_of_cut
