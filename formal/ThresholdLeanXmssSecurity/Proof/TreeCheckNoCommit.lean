import ThresholdLeanXmssSecurity.Proof.TreeCheckGuess

/-!
# The audited program after the setup makes no commitment query

This module proves `TreeCheckAfterSetupAuditNoCommit` (`TreeCheckGuess`) and with it
`TreeCheckUncountedGuess` (`treeCheckUncountedGuess_of_audit`).

The proof walks the program as `TreeSimHashCount.ceremony_bound` does, with the predicate
`FreeHashIn IsCommit` in place of `Region`. A commitment query is in `Region`
(`commit_region`), so each `Region` lemma with a zero bound transfers. The lemmas with a nonzero
bound query only `.digest`, `.history`, `.coinKey` and `.copy`, so they get new proofs with a zero
bound. The walk runs on `ceremonyAfterSetup`, and `treeSimCheckAfterSetupAudit_erase` moves the
bound to the audited program.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

namespace TreeCheckNoCommit

open TreeSimHashCount

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]
variable {ι α : Type} {G : OracleSpec ι}

theorem commit_region (t : (LocalSpec C).Domain) (h : FreeHashIn IsCommit t) : Region t := by
  obtain ⟨q, ⟨phase, j, i, reveal, rfl⟩, rfl⟩ := h
  exact ⟨.commit phase j i reveal, by simp [splitLocalHashInput, IsFixed], trivial⟩

theorem ro_of_region {oa : OracleComp (RoSpec C) α}
    (h : IsQueryBoundP oa (fun t => Region (C := C) (.inr t)) 0) :
    IsQueryBoundP oa (fun t => FreeHashIn (C := C) IsCommit (.inr t)) 0 :=
  IsQueryBoundP.of_imp (fun _ ht => commit_region _ ht) h

theorem party_of_region {p : PartyM C E G α} (h : PartyBudget Region p 0) :
    PartyBudget (FreeHashIn IsCommit) p 0 := by
  refine IsQueryBoundP.of_imp (fun t ht => ?_) h
  rcases t with (q | _) | _
  · exact commit_region q ht
  · exact ht.elim
  · exact ht.elim

theorem run_of_region {σ : Type} {p : StateT σ (PartyM C E G) α} (h : RunBudget Region p 0) :
    RunBudget (FreeHashIn IsCommit) p 0 :=
  fun s => party_of_region (h s)

theorem hash_noCommit (q : Query C) (hq : ¬ IsCommit q) :
    IsQueryBoundP (hashQuery q) (fun t => FreeHashIn (C := C) IsCommit (.inr t)) 0 := by
  change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl q))) _ 0
  rw [isQueryBoundP_query_iff]
  rintro ⟨q', hq', he⟩
  simp only [Sum.inr.injEq, Sum.inl.injEq] at he
  exact (hq (he ▸ hq')).elim

variable (K : Constants C E)

theorem compare_noCommit (ctx : Context C) (salts : Shares C Bit) :
    RunBudget (FreeHashIn IsCommit) (compareDigests ctx salts : RunM C E G _) 0 := by
  unfold compareDigests
  refine RunBudget.bind_zero (RunBudget.get) (fun s => ?_)
  refine RunBudget.bind_zero (RunBudget.lift (oracle_bound ?_)) (fun ds => ?_)
  · simpa using queryBound_mapM (fun t => FreeHashIn (C := C) IsCommit (.inr t)) _ 0 C.terms
      (fun T _ => by
        split_ifs
        · exact isQueryBoundP_bind (n := 0) (m := 0)
            (hash_noCommit _ (by simp [IsCommit])) (fun _ _ => hash_noCommit _ (by simp [IsCommit]))
        · exact isQueryBoundP_pure _ _ _)
  · exact RunBudget.bind_zero (RunBudget.lift (party_of_region (PartyBudget.of_all
      (PartyBound.exchange _)))) (fun inbox =>
        RunBudget.lift (party_of_region (PartyBudget.of_all (PartyBound.require _))))

theorem coinKey_noCommit (gadgets : CheckGadgets C E G) (hg : GadgetBounds gadgets) :
    RunBudget (FreeHashIn IsCommit) (coinKey K gadgets) 0 := by
  unfold coinKey
  exact RunBudget.bind_zero RunBudget.get (fun s => RunBudget.bind_zero (run_of_region (hg.coin 1))
    (fun values => RunBudget.lift (oracle_bound (hash_noCommit _ (by simp [IsCommit])))))

theorem challenge_noCommit (gadgets : CheckGadgets C E G) (hg : GadgetBounds gadgets) :
    RunBudget (FreeHashIn IsCommit) (challenge K gadgets) 0 := by
  unfold challenge
  refine RunBudget.bind_zero (coinKey_noCommit K gadgets hg) (fun key => ?_)
  refine RunBudget.bind_zero
    (RunBudget.lift (oracle_bound (ro_of_region (findChallenge_zero K key _ _)))) (fun out => ?_)
  cases out with
  | none => exact .lift (party_of_region (PartyBudget.of_all PartyBound.failure))
  | some r => exact .pure _ 0

theorem slice_noCommit (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : GadgetBounds gadgets) (τ : List E) (count : ℕ)
    (v : Shares C E × Shares C E × E) (j : ℕ) :
    RunBudget (FreeHashIn IsCommit) (sliceStep K ctx gadgets τ count v j) 0 := by
  rcases v with ⟨xs, ys, d⟩
  unfold sliceStep
  exact (run_of_region (hg.mult _)).bind_zero (fun _ =>
    (challenge_noCommit K gadgets hg).bind_zero (fun _ => .pure _ 0))

theorem halving_noCommit (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : GadgetBounds gadgets) (width : ℕ)
    (v : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    RunBudget (FreeHashIn IsCommit) (halvingStep K ctx gadgets width v j) 0 := by
  rcases v with ⟨a, b, d⟩
  unfold halvingStep
  exact (run_of_region (hg.mult _)).bind_zero (fun _ =>
    (challenge_noCommit K gadgets hg).bind_zero (fun _ => .pure _ 0))

theorem final_noCommit (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : GadgetBounds gadgets) (v : (ℕ → E) × (ℕ → E) × E) :
    RunBudget (FreeHashIn IsCommit) (finalStep K ctx gadgets v) 0 := by
  rcases v with ⟨a, b, d⟩
  unfold finalStep
  exact (run_of_region (hg.elements 2)).bind_zero (fun w =>
    (run_of_region (hg.mult _)).bind_zero (fun q =>
      (run_of_region (hg.bits 256)).bind_zero (fun salts =>
        (compare_noCommit ctx salts.1).bind_zero (fun _ =>
          (challenge_noCommit K gadgets hg).bind_zero (fun r =>
            (RunBudget.lift (party_of_region (PartyBudget.of_all (RunBound.openSh K ctx _ 3)))).bind_zero
              (fun opened => RunBudget.lift (party_of_region
                (PartyBudget.of_all (PartyBound.require _)))))))))

theorem check_noCommit (ctx : Context C) (gadgets : CheckGadgets C E G)
    (hg : GadgetBounds gadgets) (tuples : List (Tuple C)) :
    RunBudget (FreeHashIn IsCommit) (check K ctx gadgets tuples) 0 := by
  by_cases hz : (tuples.map (·.count)).sum = 0
  · simp only [check, hz, ↓reduceIte]
    exact .pure _ _
  · rw [check_eq K ctx gadgets tuples hz]
    exact (coinKey_noCommit K gadgets hg).bind_zero (fun key =>
      (run_of_region (expand_zero K key _)).bind_zero (fun τ =>
        (RunBudget.lift (party_of_region (PartyBudget.of_all (PartyBound.require _)))).bind_zero
          (fun _ => ((RunBudget.foldlM _ 0 (slice_noCommit K ctx gadgets hg τ _) _ _).mono (by simp)).bind_zero (fun v =>
            ((RunBudget.foldlM _ 0 (halving_noCommit K ctx gadgets hg _) _ _).mono (by simp)).bind_zero (fun v' => final_noCommit K ctx gadgets hg v')))))

theorem openRep_noCommit (ctx : Context C) (v : Shares C Bit) (count : ℕ) :
    PartyBudget (FreeHashIn IsCommit) (openRep K ctx v count : PartyM C E G _) 0 := by
  have hc (f : C.Term → List Bit) : PartyBudget (FreeHashIn IsCommit)
      (oracleStep (C.terms.mapM fun T => hashQuery (.copy (f T))) : PartyM C E G _) 0 :=
    oracle_bound (by
      simpa using (queryBound_mapM (fun t => FreeHashIn (C := C) IsCommit (.inr t))
        (fun T => hashQuery (.copy (f T))) 0 C.terms
        (fun _ _ => hash_noCommit _ (by simp [IsCommit]))))
  unfold openRep
  simpa using (hc _).bind (fun ds =>
    (party_of_region (PartyBudget.of_all (PartyBound.exchange _))).bind (fun inbox =>
      (hc _).bind (fun copies =>
        (party_of_region (PartyBudget.of_all (PartyBound.require _))).bind
          (fun _ => PartyBudget.pure _))))

theorem runJobs_noCommit (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    RunBudget (FreeHashIn IsCommit)
      (runJobs K (realRunGadgets K ctx mode : RunGadgets C E G) jobs inputs) 0 := by
  have hm : ∀ x y count, RunBudget (FreeHashIn IsCommit)
      ((realRunGadgets K ctx mode : RunGadgets C E G).mult x y count) 0 := by
    intro x y count
    change RunBudget _ (prssRandomness ctx bitCodec 0 count >>= _) 0
    exact run_of_region ((prss_zero ctx bitCodec prg_zero 0 count).bind (m := 0)
      (fun r => reshareWith_zero K ctx mode r _ count))
  have hr : ∀ v count, RunBudget (FreeHashIn IsCommit)
      ((realRunGadgets K ctx mode : RunGadgets C E G).rerand v count) 0 := by
    intro v count
    change RunBudget _ (prssRandomness ctx bitCodec 0 count >>= _) 0
    exact run_of_region ((prss_zero ctx bitCodec prg_zero 0 count).bind (m := 0)
      (fun r => reshare_zero K ctx _ r _ count))
  rw [runJobs_eq]
  refine RunBudget.bind_zero ((RunBudget.foldlM _ 0 (fun p l => ?_) _ _).mono (by simp)) (fun p => ?_)
  · unfold layerBody
    exact (hm _ _ _).bind_zero (fun z => .pure _ 0)
  · unfold tailBody
    exact (hr _ _).bind_zero (fun v =>
      (check_noCommit (G := G) K ctx _ (gadgets_zero K ctx) _).bind_zero (fun _ =>
        (RunBudget.lift (openRep_noCommit K ctx v _)).bind_zero (fun out => .pure _ 0)))

variable (circuits : Circuits) (settings : Settings)

theorem batch_noCommit (ctx : Context C) (jobs : List Job) :
    RunBudget (FreeHashIn IsCommit) (ceremonyBatch (G := G) K circuits settings ctx jobs) 0 := by
  have hi : PartyBudget (FreeHashIn IsCommit) (jobs.mapM (inputShares ctx) : PartyM C E G _) 0 :=
    party_of_region (by simpa using party_mapM (inputShares ctx) 0 (inputShares_zero ctx) jobs)
  unfold ceremonyBatch
  exact RunBudget.bind_zero RunBudget.get (fun s => (RunBudget.lift hi).bind_zero (fun inputs =>
    (RunBudget.lift (runJobs_noCommit K ctx settings.mode _ inputs ⟨fun _ => [], s.1, s.2⟩)).bind_zero
      (fun result => (RunBudget.set _).bind_zero (fun _ => RunBudget.pure _ 0))))

theorem batched_noCommit (ctx : Context C) (jobs : List Job) :
    RunBudget (FreeHashIn IsCommit)
      (batched settings.batchSize (ceremonyBatch (G := G) K circuits settings ctx) jobs) 0 := by
  unfold batched
  exact ((RunBudget.mapM _ 0 (batch_noCommit K circuits settings ctx) _).mono (by simp)).bind_zero
    (fun outputs => .pure _ 0)

theorem ceremonyOutput_noCommit {σ : Type}
    (lift : ∀ {δ : Type}, OracleComp HashSpec δ → StateT σ (PartyM C E G) δ)
    (hl : ∀ {δ : Type} (oa : OracleComp HashSpec δ), RunBudget (FreeHashIn IsCommit) (lift oa) 0)
    (run : List Job → StateT σ (PartyM C E G) (Option (List (List Bit))))
    (hr : ∀ jobs, RunBudget (FreeHashIn IsCommit) (run jobs) 0)
    (parameter : PublicParameter) (top : TopTree) (tree : Tree) :
    RunBudget (FreeHashIn IsCommit) (ceremonyOutput lift parameter run top tree) 0 := by
  cases tree with
  | top =>
    unfold ceremonyOutput
    refine (hr topJobs).bind_zero (fun outputs => ?_)
    cases outputs with
    | none => exact .pure _ 0
    | some outputs => exact (hl _).bind_zero (fun root => .pure _ 0)
  | bottom b =>
    unfold ceremonyOutput
    refine (hr (bottomJobs b)).bind_zero (fun outputs => ?_)
    cases outputs with
    | none => exact .pure _ _
    | some outputs =>
      refine (hl _).bind_zero (fun root => (hl _).bind_zero (fun base => (hl _).bind_zero
        (fun found => ?_)))
      cases found with
      | none => exact .pure _ _
      | some result =>
        refine (hr (signJobs b result.2)).bind_zero (fun values => ?_)
        cases values with
        | none => exact .pure _ 0
        | some values =>
          refine (hl _).bind_zero (fun path => (hl _).bind_zero (fun root => ?_))
          split_ifs <;> exact .pure _ 0

theorem afterSetup_noCommit (ctx : Context C) (top : TopTree) (tree : Tree) :
    PartyBudget (FreeHashIn IsCommit)
      (ceremonyAfterSetup K circuits settings ctx top tree : PartyM C E G TreeOutput) 0 := by
  unfold ceremonyAfterSetup
  have hb := ceremonyOutput_noCommit (G := G) (σ := ℕ × ℕ)
    (fun {δ} (oa : OracleComp HashSpec δ) => StateT.lift (oracleStep (tweakable oa)))
    (fun oa => RunBudget.lift (oracle_bound (ro_of_region (tweakable_zero oa))))
    (batched settings.batchSize (ceremonyBatch K circuits settings ctx))
    (batched_noCommit K circuits settings ctx) ctx.keys.parameter top tree
  refine (hb.run' (0, 0)).bind (m := 0) (fun out => ?_)
  cases out with
  | none => exact party_of_region (PartyBudget.of_all PartyBound.failure)
  | some out => exact PartyBudget.pure _

end TreeCheckNoCommit

section Audit

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The audited honest program after the PRSS setup makes no commitment query. -/
theorem treeCheckAfterSetupAuditNoCommit :
    TreeCheckAfterSetupAuditNoCommit (E := E) K circuits settings := by
  intro ctx top tree
  have h := TreeCheckNoCommit.afterSetup_noCommit (G := RealSpec) K circuits settings ctx top tree
  rw [← treeSimCheckAfterSetupAudit_erase] at h
  unfold TreeSimHashCount.PartyBudget at h ⊢
  rw [OptionT.run_map, isQueryBoundP_map_iff] at h
  exact h

theorem treeCheckUncountedGuess : TreeCheckUncountedGuess prims K circuits settings :=
  treeCheckUncountedGuess_of_audit prims K circuits settings
    (treeCheckAfterSetupAuditNoCommit K circuits settings)

end Audit

/-- info: 'ThresholdLeanXmssSecurity.treeCheckAfterSetupAuditNoCommit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckAfterSetupAuditNoCommit

/-- info: 'ThresholdLeanXmssSecurity.treeCheckUncountedGuess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckUncountedGuess

end ThresholdLeanXmssSecurity
