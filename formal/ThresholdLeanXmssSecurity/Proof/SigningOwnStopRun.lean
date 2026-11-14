import ThresholdLeanXmssSecurity.Proof.SigningOwnStopWalk

/-!
# The support part of the ledger run and the R1 bound with the own budget

* `ledger_forger` states that one query of the forger keeps the ledger paid with no free unit.
* `ledger_finish` states that the finish adds at most one free unit, the bottom digest call of the
  verification.
* `ledgerRun_paid` bounds the ledger at each outcome of the ledger run by the own keyed calls of
  the log and one unit.
* `expected_logCost_split_eq` and `expected_logCost_le` move the cost of the log to the source run.
* `r1OwnSource` proves `R1OwnSource` from the stopped potential, the support part and the law of
  the log.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open OracleComp OracleSpec ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace SigningOwnStop

open HashSig LeanXmss ThresholdLeanXmss SigningFlatProof SigningFlatEagerProof SigningJointEagerProof
  SigningPartnerBoundProof SigningReleasedLinkProof SigningReleasedAlignProof SigningOwnForger

attribute [local instance] Classical.propDecidable

variable {C : Committee} (prims : Primitives)

/-- The R1 bound with the own budget on the source run, in the form of
`SigningOneRunProof.split_r1Hit_bound`. The keyed calls of the free copy cost nothing before a second
opening of a commitment, apart from one call of the verification. -/
def R1OwnSource : Prop :=
  ∀ (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C),
    Pr{let z ←
        SigningOneRunProof.splitRunAt prims A x}[SigningOneRunProof.R1HitRow z ∧
        ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1] ≤
      (2 ^ 128 : ℝ≥0∞)⁻¹ * (SigningGuessProof.sourceExpectedCost prims A x (ownKeyedCost x) + (1 : ℕ))

/-! ## The handlers -/

/-- The cost of the log does not fall along a run of the ledger world, because the log only
grows. -/
theorem ledger_run_logCost_le {α : Type} (x : SigningSecurityProof.Keys3 C)
    (c : (WorldSpec C).Domain → ℕ) (oa : OracleComp (WorldSpec C) α) (p : LedgerState C)
    (r : α × LedgerState C) (hr : r ∈ support ((simulateQ (ledgerWorld prims x) oa).run p)) :
    SigningGuessLaneProof.logCost c p.1.1.1.1.2 ≤ SigningGuessLaneProof.logCost c r.2.1.1.1.1.2 := by
  induction oa using OracleComp.inductionOn generalizing p with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    obtain ⟨hsplit, -⟩ := ledgerWorld_support prims x t p mid hmid
    have hlog : mid.2.1.1.1.1.2 = p.1.1.1.1.2.logQuery t mid.1 :=
      world_log prims x t (p.1.1, p.2) _ hsplit
    have hrest := ih mid.1 mid.2 hr
    rw [hlog, logCost_logQuery] at hrest
    omega

/-- A run of the ledger world that leaves the ledger unchanged is paid with no free unit. -/
theorem paid_of_ledger_eq {α : Type} (x : SigningSecurityProof.Keys3 C)
    (oa : OracleComp (WorldSpec C) α) (p : LedgerState C) (r : α × LedgerState C)
    (hr : r ∈ support ((simulateQ (ledgerWorld prims x) oa).run p)) (hledger : r.2.1.2 = p.1.2) :
    Paid x 0 p r.2 := by
  have h := ledger_run_logCost_le prims x (ownKeyedCost x) oa p r hr
  unfold Paid
  omega

/-- A run of the ledger world with no call of the free copy at each key is paid with no free
unit. -/
theorem ledger_run_atKey {α : Type} (x : SigningSecurityProof.Keys3 C)
    (oa : OracleComp (WorldSpec C) α)
    (h : ∀ e, SigningSelectionProof.NoCall
      (SigningSelectionProof.FreeQ (C := C) (SigningSelectionProof.AtKey x.1 e)) oa)
    (p : LedgerState C) (r : α × LedgerState C)
    (hr : r ∈ support ((simulateQ (ledgerWorld prims x) oa).run p)) : Paid x 0 p r.2 :=
  ledger_run_bound prims x oa 0 (freeKeyed_of_atKey x.1 oa h) p r hr

/-- A query of the forger other than a round-2 request makes no call of the free copy on a bottom
digest input. -/
theorem opening_freeKeyed (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain)
    (ht : ∀ i J e message parts, t ≠ .inr (.round2 i J e message parts))
    (s : (TsigState C × Bool) × Finset (Fin (2 ^ layerHeight)) × List (SigningOpeningProof.HiddenKey × Digest)) :
    ((SigningOpeningProof.openingOracles x (dealtOf x top) t).run s).IsQueryBoundP
      (SigningSelectionProof.FreeQ (Keyed x.1)) 0 := by
  rcases t with t | q
  · simp only [SigningOpeningProof.openingOracles, SigningCoreProof.flaggedOracles, StateT.run_mk,
      isQueryBoundP_map_iff]
    erw [adversary_query, isQueryBoundP_query_iff]
    rintro ⟨input, h, -⟩
    cases h
  · refine freeKeyed_of_atKey x.1 _ fun e => ?_
    simp only [SigningOpeningProof.openingOracles, SigningCoreProof.flaggedOracles, StateT.run_mk]
    exact SigningSelectionProof.noCall_map _ _ (SigningSelectionProof.noCall_map _ _
      (SigningSelectionProof.tsigOracles_noCall x top e q
        (fun i J e' message parts h => ht i J e' message parts (h ▸ rfl)) s.1.1))

set_option backward.isDefEq.respectTransparency false in
/-- A round-2 request keeps the ledger paid. The search of the signer is a rerun or runs after the
stop. -/
theorem ledger_round2 (x : SigningSecurityProof.Keys3 C) (top : TopTree) (i : C.Party) (J : C.Quorum)
    (e : KeyIndex) (message : Message) (parts : C.Party → Digest) (p : LedgerState C)
    (hinv : StopInv prims x top (p.1.1, p.2))
    (r : ((TsigSpec C).Range (.round2 i J e message parts) × TsigState C) × LedgerState C)
    (hr : r ∈ support ((simulateQ (ledgerWorld prims x)
      ((tsigOracles (fun oa => SigningCoreProof.honestLift oa) (dealtOf x top)
        (.round2 i J e message parts)).run p.2.1.1)).run p)) : Paid x 0 p r.2 := by
  simp only [tsigOracles, StateT.run_bind, StateT.run_get, pure_bind] at hr
  split at hr
  · simp only [StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at hr
    rw [hr]
    exact Paid.refl x p
  rename_i hguard
  have hb : p.2.1.1.bound e = some message := by tauto
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨rTree, hTree, hr⟩ := hr
  have hpTree : Paid x 0 p rTree.2 := ledger_run_atKey prims x _
    (fun e' => SigningSelectionProof.bottomOnce_noCall x top e' _ _) p rTree hTree
  have hsTree := ledger_run_forget prims x _ p rTree hTree
  have hTreeGrow := world_run_cache_le prims x _ _ _ hsTree
  have hTreeCarried := world_run_carried prims x _ _ _ hsTree
  cases ht : rTree.1.1 with
  | none =>
    simp only [ht, StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at hr
    rw [hr]
    exact hpTree
  | some tree =>
    simp only [ht, StateT.run_bind, SigningSelectionProof.run_liftM, bind_map_left, simulateQ_bind,
      StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨own, hown, selected, hselected, hfinish⟩ := hr
    have hpOwn : Paid x 0 rTree.2 own.2 := ledger_run_atKey prims x _
      (fun e' => SigningSelectionProof.noCall_liftFree _ _ (SigningSelectionProof.eval_bound _ _ _ _ _ _))
      rTree.2 own hown
    have hsOwn := ledger_run_forget prims x _ rTree.2 own hown
    have hOwnGrow := world_run_cache_le prims x _ _ _ hsOwn
    have hOwnCarried := world_run_carried prims x _ _ _ hsOwn
    obtain ⟨initial, built, hbuilt, hbtree, hble⟩ :=
      world_bottomOnce_tree prims x top (treeOf e) p.2.1.1 (p.1.1, p.2) hinv.2 _ hsTree tree ht
    have hagree : TreeAgrees x own.2.1.1.1.1.1.1 tree e :=
      treeAgrees_of_run prims x top e _ (hinv.1.mono (hTreeGrow.trans hOwnGrow)) tree initial built
        (by with_reducible exact hbuilt) hbtree (hble.trans hOwnGrow)
    have hbOwn : own.2.2.1.1.bound e = some message := by
      have hcar : own.2.2 = p.2 := hOwnCarried.trans hTreeCarried
      rw [hcar]
      exact hb
    have hr : r.2 = selected.2 := by
      rcases hsel : selected.1 with _ | values
      · rw [hsel] at hfinish
        simp only [StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at hfinish
        rw [hfinish]
      · rw [hsel] at hfinish
        simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind, simulateQ_pure,
          mem_support_pure_iff] at hfinish
        rw [hfinish]
    rw [hr]
    simp only [signRound2With, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hselected
    obtain ⟨code, hcode, hafter⟩ := hselected
    have hpCode : Paid x 0 own.2 code.2 := paid_of_ledger_eq prims x _ own.2 code hcode
      (ledger_signCodeword prims x e message _ tree own.2 hagree hbOwn code hcode)
    have hpAfter : Paid x 0 code.2 selected.2 := by
      rcases hc : code.1 with _ | ⟨randomness, encoding⟩
      · rw [hc] at hafter
        simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hafter
        rw [hafter]
        exact Paid.refl x _
      · rw [hc] at hafter
        refine ledger_run_atKey prims x _ (fun e' => ?_) code.2 selected hafter
        refine SigningSelectionProof.noCall_bind _
          (SigningSelectionProof.noCall_sequenceFin _ _ fun index => ?_)
          fun _ => SigningSelectionProof.noCall_pure _ _
        split
        · exact SigningSelectionProof.noCall_map _ _
            (SigningSelectionProof.noCall_liftFree _ _ (SigningSelectionProof.eval_bound _ _ _ _ _ _))
        · exact SigningSelectionProof.noCall_pure _ _
    exact ((hpTree.trans hpOwn).trans (hpCode.trans hpAfter)).mono le_rfl

/-- The honest signature at a bound key keeps the ledger paid. Its search is a rerun or runs after
the stop. -/
theorem ledger_honestSignature (x : SigningSecurityProof.Keys3 C) (top : TopTree) (e : KeyIndex)
    (message : Message) (q : LedgerState C) (htop : TopRun prims x top q.1.1.1.1.1.1)
    (hb : q.2.1.1.bound e = some message) (r : Option Signature × LedgerState C)
    (hr : r ∈ support ((simulateQ (ledgerWorld prims x)
      (honestSignature (fun oa => SigningCoreProof.honestLift oa) (dealtOf x top) e message)).run q)) :
    Paid x 0 q r.2 := by
  unfold honestSignature at hr
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨built, hbuilt, hr⟩ := hr
  have hpBuilt : Paid x 0 q built.2 := ledger_run_atKey prims x _
    (fun e' => SigningSelectionProof.bottom_noCall x top e' _) q built hbuilt
  have hsBuilt := ledger_run_forget prims x _ q built hbuilt
  have hBuiltGrow := world_run_cache_le prims x _ _ _ hsBuilt
  have hBuiltCarried := world_run_carried prims x _ _ _ hsBuilt
  rcases htree : built.1 with _ | tree
  · rw [htree] at hr
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    rw [hr]
    exact hpBuilt
  rw [htree] at hr
  have hagree : TreeAgrees x built.2.1.1.1.1.1.1 tree e := by
    change (built.1, (built.2.1.1, built.2.2)) ∈ support ((simulateQ (SigningReleasedLinkProof.world prims x)
      ((SigningGuessProof.receiptDealt x top).bottom (treeOf e))).run (q.1.1, q.2)) at hsBuilt
    rw [SigningGuessProof.receiptDealt_bottom] at hsBuilt
    simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hsBuilt
    obtain ⟨raw, hraw, hrawEq⟩ := hsBuilt
    obtain ⟨count, hcount⟩ := world_liftFree_replay prims x _ (q.1.1, q.2) raw
      (by with_reducible exact hraw) raw.2.1.1.1.1.1 le_rfl 0
    have hcache : raw.2.1.1.1.1.1 = built.2.1.1.1.1.1.1 :=
      congrArg (fun w => w.2.1.1.1.1.1) hrawEq
    have hfirst := congrArg Prod.fst hrawEq
    rw [htree] at hfirst
    have hout : raw.1 = some (.bottom tree) := by
      revert hfirst
      rcases raw.1 with _ | (_ | tree')
      · intro h; exact absurd h (by simp)
      · intro h; exact absurd h (by simp)
      · intro h; simp only [Option.some.injEq] at h; rw [h]
    exact treeAgrees_of_run prims x top e _ (htop.mono hBuiltGrow) tree (raw.2.1.1.1.1.1, 0)
      (raw.1, raw.2.1.1.1.1.1, count) (by with_reducible exact hcount) hout hcache.le
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨rho, hrho, code, hcode, hr⟩ := hr
  have hpRho : Paid x 0 built.2 rho.2 := ledger_run_atKey prims x _
    (fun e' => SigningSelectionProof.noCall_liftFree _ _ (SigningSelectionProof.prfValue_bound _ _ _))
    built.2 rho hrho
  have hsRho := ledger_run_forget prims x _ built.2 rho hrho
  have hRhoGrow := world_run_cache_le prims x _ _ _ hsRho
  have hRhoCarried := world_run_carried prims x _ _ _ hsRho
  have hbRho : rho.2.2.1.1.bound e = some message := by
    have hcar : rho.2.2 = q.2 := hRhoCarried.trans hBuiltCarried
    rw [hcar]
    exact hb
  have hpCode : Paid x 0 rho.2 code.2 := paid_of_ledger_eq prims x _ rho.2 code hcode
    (ledger_signCodeword prims x e message rho.1 tree rho.2 (hagree.mono hRhoGrow) hbRho code hcode)
  have hpRest : Paid x 0 code.2 r.2 := by
    rcases hc : code.1 with _ | ⟨randomness, encoding⟩
    · rw [hc] at hr
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
      rw [hr]
      exact Paid.refl x _
    · rw [hc] at hr
      refine ledger_run_atKey prims x _ (fun e' => ?_) code.2 r hr
      refine SigningSelectionProof.noCall_bind _
        (SigningSelectionProof.noCall_sequenceFin _ _ fun index => ?_) fun _ => ?_
      · split
        · exact SigningSelectionProof.noCall_liftFree _ _ (SigningSelectionProof.prfValue_bound _ _ _)
        · exact SigningSelectionProof.noCall_pure _ _
        · refine SigningSelectionProof.noCall_bind _ ?_ fun _ => SigningSelectionProof.noCall_pure _ _
          exact SigningSelectionProof.noCall_liftFree _ _ (SigningSelectionProof.prfValue_bound _ _ _)
      · refine SigningSelectionProof.noCall_bind _ (SigningSelectionProof.noCall_liftFree _ _
          (SigningSelectionProof.tweakable_bound _ _ (SigningSelectionProof.merklePath_bound x.1 e' _ _ _)))
          fun _ => SigningSelectionProof.noCall_pure _ _
  exact ((hpBuilt.trans hpRho).trans (hpCode.trans hpRest)).mono le_rfl

/-- One query of the forger keeps the ledger paid. -/
theorem ledger_forger (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (p : LedgerState C)
    (hinv : StopInv prims x top (p.1.1, p.2))
    (r : (LocalSpec C + TsigSpec C).Range t × LedgerState C)
    (hr : r ∈ support ((flatWith (SigningOpeningProof.openingOracles x (dealtOf x top))
      (ledgerWorld prims x) t).run p)) : Paid x 0 p r.2 := by
  simp only [flatWith, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  change Paid x 0 p z.2
  by_cases hq : ∃ i J e message parts, t = .inr (.round2 i J e message parts)
  · obtain ⟨i, J, e, message, parts, rfl⟩ := hq
    simp only [SigningOpeningProof.openingOracles, SigningCoreProof.flaggedOracles, StateT.run_mk,
      simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hz
    obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hz
    exact ledger_round2 prims x top i J e message parts p hinv w hw
  · push Not at hq
    exact ledger_run_bound prims x _ 0 (opening_freeKeyed x top t hq p.2) p z hz

/-- The finish adds at most one free unit, the bottom digest call of the verification. -/
theorem ledger_finish (x : SigningSecurityProof.Keys3 C) (top : TopTree) (forgery : Forgery)
    (p : LedgerState C) (hinv : StopInv prims x top (p.1.1, p.2))
    (hrel : SigningGuessProof.ReleasedBound p.2.1.1) (hc : p.2.1.1.corrupt.card ≤ C.t - 1)
    (r : ((Bool × TsigState C × Forgery) × List (SigningOpeningProof.HiddenKey × Digest)) × LedgerState C)
    (hr : r ∈ support ((simulateQ (ledgerWorld prims x)
      (SigningGuessLinkProof.tsigFinishLogged (dealtOf x top) p.2.2.1 (forgery, p.2.1.1))).run p)) :
    Paid x 1 p r.2 := by
  rw [SigningGuessLinkProof.tsigFinishLogged_eq] at hr
  simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨v, hv, hr⟩ := hr
  have hpv : Paid x 1 p v.2 := ledger_run_except prims x
    (XmssSecurity.Concrete.CacheView.encodingInput x.1 forgery.signature.leafIndex
      (forgery.message, (forgery.signature.layers bottomLayer).randomizer)) _
    (freeKeyed_except_of_atKey x.1 _ _ fun e => SigningSelectionProof.noCall_liftFree _ _
      (SigningSelectionProof.loggedTweakable_bound x.1 _ _ _ _
        (SigningSelectionProof.verify_bound x.1 e _ _ _))) p v hv
  have hsv := ledger_run_forget prims x _ p v hv
  have hvGrow := world_run_cache_le prims x _ _ _ hsv
  have hvCarried := world_run_carried prims x _ _ _ hsv
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  change Paid x 1 p w.2
  split at hw
  · simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hw
    rw [hw]
    exact hpv
  rename_i hsigners
  have hb := SigningSelectionProof.message_of_signers p.2.1.1 hrel hc _ _ hsigners
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  have hbv : v.2.2.1.1.bound forgery.signature.leafIndex = some forgery.message := by
    have hcar : v.2.2 = p.2 := hvCarried
    rw [hcar]
    exact hb
  exact (hpv.trans (ledger_honestSignature prims x top _ _ v.2 (hinv.1.mono hvGrow) hbv u hu)).mono le_rfl

/-! ## The run -/

/-- One query of the forger in the ledger run is one query of the forger in the split run. -/
theorem ledger_forger_split (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (p : LedgerState C)
    (r : (LocalSpec C + TsigSpec C).Range t × LedgerState C)
    (hr : r ∈ support ((flatWith (SigningOpeningProof.openingOracles x (dealtOf x top))
      (ledgerWorld prims x) t).run p)) :
    (r.1, (r.2.1.1, r.2.2)) ∈ support ((forger prims x top t).run (p.1.1, p.2)) := by
  have h := forgets_flatWith (SigningOpeningProof.openingOracles x (dealtOf x top)) (ledgerWorld prims x)
    (world prims x) (ledgerWorld_forgets prims x) t p.1.1 p.1.2 p.2
  rw [← h, support_map]
  exact ⟨r, hr, rfl⟩

/-- One query of the forger keeps the invariant of the walk, the release records and the bound of
the corruption. -/
theorem ledger_forger_inv (x : SigningSecurityProof.Keys3 C) (top : TopTree)
    (t : (LocalSpec C + TsigSpec C).Domain) (p : LedgerState C)
    (hinv : StopInv prims x top (p.1.1, p.2)) (hrel : SigningGuessProof.ReleasedBound p.2.1.1)
    (hc : p.2.1.1.corrupt.card ≤ C.t - 1)
    (r : (LocalSpec C + TsigSpec C).Range t × LedgerState C)
    (hr : r ∈ support ((flatWith (SigningOpeningProof.openingOracles x (dealtOf x top))
      (ledgerWorld prims x) t).run p)) :
    StopInv prims x top (r.2.1.1, r.2.2) ∧ SigningGuessProof.ReleasedBound r.2.2.1.1 ∧
      r.2.2.1.1.corrupt.card ≤ C.t - 1 := by
  have hs := ledger_forger_split prims x top t p r hr
  have hgame := forger_source prims x top t (p.1.1, p.2) _ hs
  refine ⟨⟨hinv.1.mono (forger_cache_le prims x top t _ _ hs), forger_stored prims x top t _ hinv.2 _ hs⟩,
    ?_, SigningGuessProof.gameOracles_corrupt_le _ t _ _ hc hgame⟩
  rcases t with t | q
  · change (r.1, r.2.2.1.1) ∈ support ((fun a => (a, p.2.1.1)) <$>
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t))) at hgame
    rw [support_map] at hgame
    obtain ⟨a, -, ha⟩ := hgame
    have hst : p.2.1.1 = r.2.2.1.1 := congrArg Prod.snd ha
    rw [← hst]
    exact hrel
  · exact SigningGuessProof.tsigOracles_releasedBound _ _ q p.2.1.1 _ hrel hgame

/-- On each outcome of the ledger run, the ledger is at most the own keyed calls of the log and one
unit. The proof joins the dealer, the queries of the forger and the finish. -/
theorem ledgerRun_paid (A : TsigAdversary C) (x : SigningSecurityProof.Keys3 C)
    (z : JointResult C × LedgerState C) (hz : z ∈ support (ledgerRun prims A x)) :
    z.2.1.2 ≤ SigningGuessLaneProof.logCost (ownKeyedCost x) z.2.1.1.1.1.2 + 1 := by
  have hgoal : ∀ (n : ℕ) (q : LedgerState C), n ≤ 1 → Paid x n ledgerInit q →
      q.1.2 ≤ SigningGuessLaneProof.logCost (ownKeyedCost x) q.1.1.1.1.2 + 1 := by
    intro n q hn h
    have h0 : SigningGuessLaneProof.logCost (ownKeyedCost x) (ledgerInit (C := C)).1.1.1.1.2 = 0 := rfl
    have h1 : (ledgerInit (C := C)).1.2 = 0 := rfl
    unfold Paid at h
    rw [h0, h1] at h
    omega
  unfold ledgerRun ledgerGame jointGameWith at hz
  simp only [StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨setup, hsetup, hz⟩ := hz
  have hpaid := ledger_run_bound prims x _ 0 (dealer_freeKeyed x) ledgerInit setup hsetup
  have hsplit := ledger_run_forget prims x _ ledgerInit setup hsetup
  have hcarried := world_run_carried prims x _ _ _ hsplit
  cases hout : setup.1 with
  | none =>
    simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact hgoal 0 _ (by omega) hpaid
  | some tree =>
    cases tree with
    | bottom tree =>
      simp only [hout, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]
      exact hgoal 0 _ (by omega) hpaid
    | top top =>
      simp only [hout, StateT.run_bind, getCarried, StateT.run_mk, pure_bind,
        mem_support_bind_iff] at hz
      obtain ⟨middle, hmiddle, finished, hfinished, hz⟩ := hz
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
      rw [show referenceTree (fun oa => SigningSecurityProof.liftFree (tweakable oa))
          (fun p => SigningSecurityProof.liftFree (prfValue x.2.1 p)) x.1 emptyTop .top =
          SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top) from
        referenceTree_φ _ _ _ _] at hsplit
      obtain ⟨count, hcount⟩ := world_liftFree_replay prims x _ _ _ hsplit setup.2.1.1.1.1.1.1 le_rfl 0
      have htop : TopRun prims x top setup.2.1.1.1.1.1.1 :=
        ⟨(setup.2.1.1.1.1.1.1, 0), (setup.1, setup.2.1.1.1.1.1.1, count), hcount, hout, le_rfl⟩
      have hstate : setup.2.2 = (ledgerInit (C := C)).2 := hcarried
      have hstored : SigningGuessProof.StoredTreeRuns prims x top setup.2.1.1.1.1.1.1 setup.2.2.1.1 := by
        rw [hstate]
        simp [SigningGuessProof.StoredTreeRuns, SigningCoreProof.tsigInit, ledgerInit,
          SigningOneRunProof.monitoredInit]
      have hrel : SigningGuessProof.ReleasedBound setup.2.2.1.1 := by
        rw [hstate]
        intro e message i hm
        simp [SigningCoreProof.tsigInit, ledgerInit, SigningOneRunProof.monitoredInit] at hm
      have hc : setup.2.2.1.1.corrupt.card ≤ C.t - 1 := by
        rw [hstate]
        simp [SigningCoreProof.tsigInit, ledgerInit, SigningOneRunProof.monitoredInit]
      have hinv := SeedHitProof.support_simulateQ_inv
        (flatWith (SigningOpeningProof.openingOracles x (dealtOf x top)) (ledgerWorld prims x))
        (fun p : LedgerState C => (StopInv prims x top (p.1.1, p.2) ∧
          SigningGuessProof.ReleasedBound p.2.1.1 ∧ p.2.1.1.corrupt.card ≤ C.t - 1) ∧
          Paid x 0 ledgerInit p)
        (fun t p hp r hr => ⟨ledger_forger_inv prims x top t p hp.1.1 hp.1.2.1 hp.1.2.2 r hr,
          (hp.2.trans (ledger_forger prims x top t p hp.1.1 r hr)).mono le_rfl⟩)
        _ setup.2 ⟨⟨⟨htop, hstored⟩, hrel, hc⟩, hpaid⟩ middle hmiddle
      have hfin := ledger_finish prims x top middle.1 middle.2 hinv.1.1 hinv.1.2.1 hinv.1.2.2
        finished hfinished
      rw [hz]
      exact hgoal 1 _ le_rfl ((hinv.2.trans hfin).mono (by omega))

/-! ## The law of the own keyed calls -/

/-- The cost of the log of the split run has the law of the cost of the log of `loggedRun`. -/
theorem expected_logCost_split_eq (c : (WorldSpec C).Domain → ℕ) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    ∑' z, Pr{let y ← SigningOneRunProof.splitRunAt prims A x}[y = z] *
        (SigningGuessLaneProof.logCost c z.2.1.1.1.2 : ℝ≥0∞) =
      ∑' z, Pr{let y ← SigningCostProof.loggedRun prims A x}[y = z] *
        (SigningGuessLaneProof.logCost c z.2.2 : ℝ≥0∞) := by
  have h1 := OracleComp.tsum_prEvent_map_mul (SigningOneRunProof.splitRunAt prims A x)
    (fun z => (z.1, (z.2.1.1.1, z.2.2))) (fun y => (SigningGuessLaneProof.logCost c y.2.1.2 : ℝ≥0∞))
  rw [SigningOneRunProof.splitRunAt_oneRun] at h1
  have h2 := OracleComp.tsum_prEvent_map_mul (SigningOneRunProof.oneRun prims A x)
    (fun z => (z.1, z.2.1.1.2, z.2.1.2)) (fun y => (SigningGuessLaneProof.logCost c y.2.2 : ℝ≥0∞))
  have h3 := OracleComp.tsum_prEvent_map_mul (SigningUnchargedLoggedProof.jointRun prims A x)
    (fun z => (z.1, z.2.1.2, z.2.2)) (fun y => (SigningGuessLaneProof.logCost c y.2.2 : ℝ≥0∞))
  have h4 := OracleComp.tsum_prEvent_map_mul (SigningUnchargedLoggedProof.jointRun prims A x)
    (fun z => (z.1.1, z.2)) (fun y => (SigningGuessLaneProof.logCost c y.2.2 : ℝ≥0∞))
  rw [SigningUnchargedLoggedProof.jointRun_logged] at h4
  have hlaw := SigningOneRunProof.evalDist_oneRun prims A x
  rw [← h1, h4]
  refine (h2.symm.trans ?_).trans h3
  exact tsum_congr fun y => by rw [hlaw.prEvent_eq (· = y)]

/-- The cost of the log of `loggedRun` in expectation is the expected cost of the source run. -/
theorem expected_logCost_le (c : (WorldSpec C).Domain → ℕ) (A : TsigAdversary C)
    (x : SigningSecurityProof.Keys3 C) :
    ∑' z, Pr{let y ← SigningCostProof.loggedRun prims A x}[y = z] *
        (SigningGuessLaneProof.logCost c z.2.2 : ℝ≥0∞) ≤
      SigningGuessProof.sourceExpectedCost prims A x c := by
  have h := XmssSecurity.expectedFinal_le (SigningCostProof.loggedImpl prims) (Inv := fun _ => True)
    (fun _ _ _ _ _ => trivial) (fun s => (SigningGuessLaneProof.logCost c s.2 : ℝ≥0∞))
    (fun t _ => (c t : ℝ≥0∞))
    (fun t s _ => by
      rw [tsum_eq_of_support _ _ (fun _ => (SigningGuessLaneProof.logCost c s.2 + c t : ℝ≥0∞) + 0)
          fun r hr => by
          rw [SigningHitLaneProof.loggedImpl_log prims t s r hr, logCost_logQuery, add_zero, Nat.cast_add],
        tsum_probOutput_mul_const_add]
      simp)
    (SigningDescentProof.finalRun A x) SigningHitLaneProof.loggedInit trivial
  have hzero : SigningGuessLaneProof.logCost c (SigningHitLaneProof.loggedInit (C := C)).2 = 0 := rfl
  rw [hzero, Nat.cast_zero, zero_add] at h
  exact h

/-! ## The assembly -/

/-- `R1OwnSource` from the potential part, the support part and the law. -/
theorem r1OwnSource : R1OwnSource prims (C := C) := by
  intro A x
  set ε : ℝ≥0∞ := (2 ^ 128 : ℝ≥0∞)⁻¹
  have hpot := ledgerRun_stopRisk_le prims A x
  have hlaw : ∑' z, Pr{let y ← ledgerRun prims A x}[y = z] *
        (SigningGuessLaneProof.logCost (ownKeyedCost x) z.2.1.1.1.1.2 : ℝ≥0∞) =
      ∑' z, Pr{let y ← SigningCostProof.loggedRun prims A x}[y = z] *
        (SigningGuessLaneProof.logCost (ownKeyedCost x) z.2.2 : ℝ≥0∞) := by
    rw [← expected_logCost_split_eq, ← ledgerRun_forget, OracleComp.tsum_prEvent_map_mul]
  rw [← ledgerRun_forget, prEvent_map]
  calc _ ≤ ∑' z, Pr{let y ← ledgerRun prims A x}[y = z] * SigningOwnR1.stopRisk x z.2.1.1.1.1.1.1 z.2.1.1.1.2 := by
        rw [OracleComp.prEvent_eq_tsum_ite]
        refine ENNReal.tsum_le_tsum fun z => ?_
        split_ifs with hz
        · have hone : SigningOwnR1.stopRisk x z.2.1.1.1.1.1.1 z.2.1.1.1.2 = 1 := by
            have hhit : z.2.1.1.1.2.hit = true := hz.1
            have halt : ¬SigningGuessProof.AlternativeCommitment x.2.1 x.1 z.2.1.1.1.1.1.1 := hz.2
            simp [SigningOwnR1.stopRisk, halt, Monitor.risk, hhit]
          rw [hone, mul_one]
        · exact bot_le
    _ ≤ ε * ∑' z, Pr{let y ← ledgerRun prims A x}[y = z] * (z.2.1.2 : ℝ≥0∞) := hpot
    _ ≤ ε * ∑' z, Pr{let y ← ledgerRun prims A x}[y = z] *
          ((1 : ℝ≥0∞) + (SigningGuessLaneProof.logCost (ownKeyedCost x) z.2.1.1.1.1.2 : ℝ≥0∞)) := by
        refine mul_le_mul' le_rfl (tsum_le_of_support _ _ _ fun z hz => ?_)
        have h := ledgerRun_paid prims A x z hz
        calc (z.2.1.2 : ℝ≥0∞) ≤
              ((SigningGuessLaneProof.logCost (ownKeyedCost x) z.2.1.1.1.1.2 + 1 : ℕ) : ℝ≥0∞) := by
              exact_mod_cast h
          _ = _ := by push_cast; ring
    _ = ε * ((1 : ℝ≥0∞) + ∑' z, Pr{let y ← ledgerRun prims A x}[y = z] *
          (SigningGuessLaneProof.logCost (ownKeyedCost x) z.2.1.1.1.1.2 : ℝ≥0∞)) := by
        rw [tsum_probOutput_mul_const_add]
    _ = ε * ((1 : ℝ≥0∞) + ∑' z, Pr{let y ← SigningCostProof.loggedRun prims A x}[y = z] *
          (SigningGuessLaneProof.logCost (ownKeyedCost x) z.2.2 : ℝ≥0∞)) := by
        rw [hlaw]
    _ ≤ _ := by
        rw [add_comm, Nat.cast_one]
        gcongr
        exact expected_logCost_le prims _ A x

end SigningOwnStop

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_logCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_logCost_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.paid_of_ledger_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.paid_of_ledger_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_atKey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_run_atKey

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.opening_freeKeyed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.opening_freeKeyed

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_round2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_round2

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_honestSignature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_honestSignature

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_forger' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_forger

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_finish

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_forger_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_forger_split

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledger_forger_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledger_forger_inv

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.ledgerRun_paid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.ledgerRun_paid

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.expected_logCost_split_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.expected_logCost_split_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.expected_logCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.expected_logCost_le

/-- info: 'ThresholdLeanXmssSecurity.SigningOwnStop.r1OwnSource' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningOwnStop.r1OwnSource
