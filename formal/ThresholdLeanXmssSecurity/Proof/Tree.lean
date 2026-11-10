import ThresholdLeanXmssSecurity.Proof.Main
import ThresholdLeanXmssSecurity.Proof.Keygen
import ThresholdLeanXmssSecurity.Proof.Check
import VCVio.ProgramLogic.Relational.Basic
import VCVio.OracleComp.SimSemantics.StateT.StateProjection

/-!
# The ceremony

`TreeCompletenessStatement` follows from the honest run of a ceremony, batch by batch.
`TreeSecurityStatement` reduces to its distance half `TreeSecurityDistance`, which is open.
`treeSimulator_queryBound` gives the query half. The other lemmas are partial steps toward
`TreeSecurityDistance`. `DealerTreeStatement` and `TreeSuccessStatement` are open.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

/-! ## Tree completeness, the statement as two local runs -/

namespace ThresholdLeanXmssSecurity

open scoped ENNReal

attribute [local instance] Classical.propDecidable

section TreeStatement

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The honest real ceremony as a local run from the empty cache. -/
def realTreeRun (top : TopTree) (tree : Tree) (keys : C.Party → Keys C) : ProbComp (C.Party → Option TreeOutput) :=
  (simulateQ (localAnswer prims) (honestStart (fun i => (ceremony K circuits settings i (keys i) top tree :
      PartyM C E RealSpec TreeOutput)) >>=
    honestRounds noFunctionality (fun l => l.elim) (ceremonyFuel circuits settings))).run' ∅

/-- The dealer ceremony as a local run from the empty cache, with its output at every operator. -/
def idealTreeRun (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) :
    ProbComp (C.Party → Option TreeOutput) :=
  (fun r (_ : C.Party) => r.1) <$> (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
    (dealerCeremony circuits settings parameter seeds top tree)).run' ∅

theorem simulateQ_replyImpl_liftComp_ro {L R α : Type} (reply : L → R) (oa : OracleComp (RoSpec C) α) :
    simulateQ (replyImpl (C := C) reply) (liftComp oa (LocalSpec C + (L →ₒ R))) = liftComp oa (LocalSpec C) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind, liftComp_bind]
    simp only [ih]
    congr 1
    rcases t with q | x <;> rfl

theorem firstParty_mem_holders_find (seeds : C.Term → HashOutput) (parameter : PublicParameter)
    (pairKeys : C.Pair → HashOutput) (T : C.Term) :
    ((C.parties.findSome? fun i => if i ∈ C.holders T then
        (some (dealtKeys parameter seeds pairKeys i)).map (·.seed T) else none).getD 0) = seeds T := by
  obtain ⟨i, hi⟩ := exists_holder T
  have hsome : (C.parties.findSome? fun i => if i ∈ C.holders T then
      (some (dealtKeys parameter seeds pairKeys i)).map (·.seed T) else none).isSome := by
    rw [List.findSome?_isSome_iff]
    exact ⟨i, by simp [Committee.parties], by simp [hi]⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨j, -, hj⟩ := List.exists_of_findSome?_eq_some hv
  rw [hv]
  split_ifs at hj with hjT
  · simp only [Option.map_some, Option.some.injEq] at hj
    rw [← hj]
    simp [dealtKeys, hjT]

/-- The ideal side of the statement on dealt keys is the dealer ceremony. -/
theorem ideal_tree_eq (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (top : TopTree) (tree : Tree) :
    (simulateQ (localAnswer prims) (simulateQ (replyImpl (fun _ => (Finset.univ : Finset C.Party)))
        ((Ftree circuits settings top tree).run noCoalition
          fun i => some (dealtKeys parameter seeds pairKeys i)))).run' ∅ =
      idealTreeRun prims circuits settings parameter seeds top tree := by
  have hparam : (firstInput (C := C) fun i => some (dealtKeys parameter seeds pairKeys i)).parameter = parameter := by
    rw [firstInput_some_pos]; rfl
  have hseeds : (fun T => (C.parties.findSome? fun i => if i ∈ C.holders T then
      (some (dealtKeys parameter seeds pairKeys i)).map (·.seed T) else none).getD 0) = seeds :=
    funext (firstParty_mem_holders_find seeds parameter pairKeys)
  unfold Ftree idealTreeRun
  simp only [simulateQ_bind, simulateQ_replyImpl_liftComp_ro, hparam, hseeds]
  simp only [simulateQ_replyImpl_leak, simulateQ_pure, pure_bind, simulateQ_localAnswer_liftComp]
  simp [StateT.run'_eq, noCoalition]

/-- The statement reduces to a bound of the two local runs on dealt keys. -/
theorem treeCompleteness_of_runs
    (h : 0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (parameter : PublicParameter)
      (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput),
      tvDist (realTreeRun prims K circuits settings top tree (dealtKeys parameter seeds pairKeys))
        (idealTreeRun prims circuits settings parameter seeds top tree) ≤
          treeAbortError (E := E) circuits settings tree) :
    TreeCompletenessStatement prims K circuits settings := by
  intro hb top tree
  rw [completes_iff]
  rintro x ⟨parameter, seeds, pairKeys, hx⟩
  obtain rfl : x = dealtKeys parameter seeds pairKeys := funext hx
  rw [ideal_tree_eq]
  exact h hb top tree parameter seeds pairKeys

/-- A computation after another one, whose result is dropped, keeps the output of the first one. -/
theorem evalDist_run'_append {α β : Type} (X : OracleComp (LocalSpec C) α) (W : OracleComp (LocalSpec C) β)
    (s : HashCache C) :
    𝒟[(simulateQ (localAnswer prims) (X >>= fun x => W >>= fun _ => pure x)).run' s] =
      𝒟[(simulateQ (localAnswer prims) X).run' s] := by
  simp only [simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, map_bind]
  conv_rhs => rw [← bind_pure ((simulateQ (localAnswer prims) X).run s), map_bind]
  refine evalDist_bind_congr fun p _ => ?_
  simp only [StateT.run_pure, map_pure, map_bind]
  exact evalDist_eq_pure_of_support _ _ fun y hy => by simp at hy; exact hy.2.symm

/-- Two local runs from one cache are within the probability that they differ when the second
one runs after the first one. -/
theorem tvDist_le_joint {β : Type} (R I : OracleComp (LocalSpec C) β) (s : HashCache C) :
    tvDist ((simulateQ (localAnswer prims) R).run' s) ((simulateQ (localAnswer prims) I).run' s) ≤
      (Pr[fun p => p.1 ≠ p.2 | (simulateQ (localAnswer prims)
        (I >>= fun a => R >>= fun z => pure (z, a))).run' s]).toReal := by
  set J := (simulateQ (localAnswer prims) (I >>= fun a => R >>= fun z => pure (z, a))).run' s
  have hR : 𝒟[(simulateQ (localAnswer prims) R).run' s] = 𝒟[J >>= fun p => pure p.1] := by
    rw [← evalDist_run'_prepend prims I R s]
    simp only [J, simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, map_bind, bind_assoc,
      StateT.run_pure, map_pure, pure_bind, bind_map_left, map_eq_bind_pure_comp]
    rfl
  have hI : 𝒟[(simulateQ (localAnswer prims) I).run' s] = 𝒟[J >>= fun p => pure p.2] := by
    rw [← evalDist_run'_append prims I R s]
    simp only [J, simulateQ_bind, simulateQ_pure, StateT.run'_eq, StateT.run_bind, map_bind, bind_assoc,
      StateT.run_pure, map_pure, pure_bind, bind_map_left]
  calc tvDist ((simulateQ (localAnswer prims) R).run' s) ((simulateQ (localAnswer prims) I).run' s)
      = tvDist (J >>= fun p => pure p.1) (J >>= fun p => pure p.2) := by unfold tvDist; rw [hR, hI]
    _ ≤ _ := tvDist_bind_left_event_le J _ _ (fun p => p.1 ≠ p.2) fun p hp => by
        rw [not_not] at hp; rw [hp]

/-- The real ceremony on dealt keys as a local computation. -/
def realTree (top : TopTree) (tree : Tree) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) : OracleComp (LocalSpec C) (C.Party → Option TreeOutput) :=
  honestStart (fun i => (ceremony K circuits settings i (dealtKeys parameter seeds pairKeys i) top tree :
      PartyM C E RealSpec TreeOutput)) >>=
    honestRounds noFunctionality (fun l => l.elim) (ceremonyFuel circuits settings)

/-- The dealer ceremony as a local computation, with its output at every operator. -/
def idealTree (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree) :
    OracleComp (LocalSpec C) (C.Party → Option TreeOutput) :=
  liftComp ((fun r (_ : C.Party) => r.1) <$> dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C)

/-- The dealer ceremony, then the real ceremony, from the empty cache. The first output is the real one. -/
def jointTreeRun (top : TopTree) (tree : Tree) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) : ProbComp ((C.Party → Option TreeOutput) × (C.Party → Option TreeOutput)) :=
  (simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds top tree >>= fun a =>
    realTree K circuits settings top tree parameter seeds pairKeys >>= fun z => pure (z, a))).run' ∅

/-- The statement reduces to the probability that the real ceremony differs from the dealer
ceremony in one joint run. -/
theorem treeCompleteness_of_joint
    (h : 0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (parameter : PublicParameter)
      (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput),
      (Pr[fun p => p.1 ≠ p.2 | jointTreeRun prims K circuits settings top tree parameter seeds pairKeys]).toReal ≤
        treeAbortError (E := E) circuits settings tree) :
    TreeCompletenessStatement prims K circuits settings := by
  refine treeCompleteness_of_runs prims K circuits settings fun hb top tree parameter seeds pairKeys => ?_
  have hI : idealTreeRun prims circuits settings parameter seeds top tree =
      (simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds top tree)).run' ∅ := by
    rw [idealTree, simulateQ_localAnswer_liftComp, idealTreeRun, simulateQ_map]
    simp [StateT.run'_eq]
  rw [hI, realTreeRun]
  exact (tvDist_le_joint prims _ _ ∅).trans (h hb top tree parameter seeds pairKeys)

end TreeStatement

/-! ## Tree completeness, the PRSS setup of an honest ceremony -/

section PrssSetup

variable {C : Committee} {E : Type} (prims : Primitives) {I O L R α : Type}

theorem prssSetup_eq (i : C.Party) :
    (prssSetup i : PartyM C E (CallSpec I O) (PrssKeys C)) =
      localStep (liftComp sampleParts _) >>= fun own =>
        commitRevealEcho .prss i own >>= fun keys => pure ⟨keys.2.1, keys.2.2⟩ := rfl

/-- The step of operator `i` after the start of its PRSS setup, before the continuation `f`. -/
def prssStart (i : C.Party) (own : Parts C) (commitments : List HashOutput)
    (f : PrssKeys C → PartyM C E (CallSpec I O) α) : Step C E (CallSpec I O) α :=
  .wait (commitOutbox i commitments) (exchangeResume fun committed =>
    exchange (revealOutbox .prss i own) >>= fun revealed =>
      setupRest .prss i own committed revealed >>= fun keys => f ⟨keys.2.1, keys.2.2⟩)

theorem advance_prssSetup (i : C.Party) (f : PrssKeys C → PartyM C E (CallSpec I O) α) :
    advance (prssSetup i >>= f).run =
      liftComp sampleParts (LocalSpec C) >>= fun own =>
        liftComp (commitQueries .prss i own) (LocalSpec C) >>= fun commitments =>
          pure (prssStart i own commitments f) := by
  rw [prssSetup_eq, bind_assoc, advance_localStep_bind]
  refine bind_congr fun own => ?_
  simp only [bind_assoc, pure_bind]
  rw [advance_setup_start]
  rfl

/-- The PRSS keys of operator `i` in an honest setup with `H` fixed to `h`. -/
def honestPrssKeys (h : Query C → HashOutput) (parts : C.Party → Parts C) (i : C.Party) : PrssKeys C :=
  ⟨fun T => if i ∈ C.holders T then h (termInput .prss parts T) else 0,
    fun j => if hj : j = i then 0 else h (pairInput .prss parts (C.pairOf i j (Ne.symm hj)))⟩

/-- The three rounds of an honest PRSS setup with `H` fixed. Every operator continues with its
honest PRSS keys. -/
theorem simulateQ_fixedLocal_prssRounds (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (f : C.Party → PrssKeys C → PartyM C E (CallSpec I O) α) :
    simulateQ (fixedLocal prims h) (honestRounds F reply (fuel + 3)
        (fun j => prssStart j (parts j) (D prims h (commitQueries .prss j (parts j))) (f j))) =
      simulateQ (fixedLocal prims h) (Concrete.sequenceFin (fun j => advance (f j (honestPrssKeys h parts j)).run) >>=
        honestRounds F reply fuel) := by
  set keys := fun x => D prims h (deriveKeys .prss x (honestView (E := E) .prss parts x)) with hk
  set shared := fun x => D prims h (sharedQueries .prss x (keys x)) with hs
  have hkeys : ∀ j, (⟨(keys j).2.1, (keys j).2.2⟩ : PrssKeys C) = honestPrssKeys h parts j := by
    intro j
    simp only [hk, D_deriveKeys_honest]
    rfl
  have h1 : ∀ j, advance (exchangeResume (fun committed =>
        exchange (revealOutbox .prss j (parts j)) >>= fun revealed =>
          setupRest .prss j (parts j) committed revealed >>= fun keys => f j ⟨keys.2.1, keys.2.2⟩)
        fun k => commitOutbox k (D prims h (commitQueries .prss k (parts k))) j) =
      pure (.wait (revealOutbox .prss j (parts j)) (exchangeResume fun revealed =>
        setupRest .prss j (parts j) (fun k => commitOutbox (E := E) k (D prims h (commitQueries .prss k (parts k))) j)
          revealed >>= fun keys => f j ⟨keys.2.1, keys.2.2⟩)) := by
    intro j
    rw [exchangeResume_of_no_abort _ _ fun k => isAbort_commitOutbox k _ j]
    exact advance_setup_reveal _ _ _ _
  have h2 : ∀ j, simulateQ (fixedLocal prims h) (advance (exchangeResume (fun revealed =>
        setupRest .prss j (parts j) (fun k => commitOutbox (E := E) k (D prims h (commitQueries .prss k (parts k))) j)
          revealed >>= fun keys => f j ⟨keys.2.1, keys.2.2⟩) fun k => revealOutbox .prss k (parts k) j)) =
      pure (Step.wait (echoOutbox .prss j (keys j) (shared j)) (exchangeResume fun received =>
        require (echoCheck .prss j (keys j) (shared j) received) >>= fun _ =>
          f j ⟨(keys j).2.1, (keys j).2.2⟩)) := by
    intro j
    rw [exchangeResume_of_no_abort _ _ fun k => isAbort_revealOutbox _ k _ j, advance_setupRest, simulateQ_bind,
      simulateQ_fixedLocal_liftComp, pure_bind]
    split_ifs with hcheck
    · rw [simulateQ_bind, simulateQ_fixedLocal_liftComp, pure_bind,
        simulateQ_bind, simulateQ_fixedLocal_liftComp, pure_bind, simulateQ_pure]
      rfl
    · exact absurd (openCheck_honest prims h .prss parts j) hcheck
  have h3 : ∀ j, advance (exchangeResume (fun received =>
        require (echoCheck .prss j (keys j) (shared j) received) >>= fun _ => f j ⟨(keys j).2.1, (keys j).2.2⟩)
          fun k => echoOutbox (E := E) .prss k (keys k) (shared k) j) =
      advance (f j (honestPrssKeys h parts j)).run := by
    intro j
    rw [exchangeResume_of_no_abort _ _ fun k => isAbort_echoOutbox _ k _ _ j, advance_require_bind,
      if_pos (echoCheck_honest prims h .prss parts j), hkeys]
  show simulateQ _ (honestRounds _ _ (fuel + 2 + 1) _) = _
  unfold prssStart
  rw [honestRounds_wait]
  simp only [h1]
  rw [sequenceFin_pure, pure_bind, honestRounds_wait, simulateQ_bind, simulateQ_sequenceFin]
  simp only [h2]
  rw [sequenceFin_pure, pure_bind, honestRounds_wait]
  simp only [h3]

end PrssSetup

/-! ## Tree completeness, the real gadgets with `H` fixed -/

section RealGadgets

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives) {ι : Type} {G : OracleSpec ι}

/-- The terms `r_T` that operator `ctx.self` draws in round `ρ`. -/
def termDraws {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R) (ρ idx count : ℕ) :
    OracleComp (RoSpec C) (List (ℕ → R)) :=
  C.terms.mapM fun T =>
    if ctx.self ∈ C.holders T then codec.draw (.term T) (ctx.prss.term T) ρ idx count else pure fun _ => 0

/-- The pair streams `Z_ij` that operator `ctx.self` draws in round `ρ`. -/
def pairDraws {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R) (ρ idx count : ℕ) :
    OracleComp (RoSpec C) (List (ℕ → R)) :=
  C.parties.mapM fun j => if h : j = ctx.self then pure fun _ => 0
    else codec.draw (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) ρ idx count

theorem prssRandomness_eq {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R) (idx count : ℕ) :
    (prssRandomness (G := G) ctx codec idx count) = (do
      let ρ ← freshLabel
      let r ← StateT.lift (oracleStep (termDraws ctx codec ρ idx count))
      let Z ← StateT.lift (oracleStep (pairDraws ctx codec ρ idx count))
      pure (fun T => r.getD (C.terms.idxOf T) fun _ => 0, fun j => Z.getD j.val fun _ => 0)) := rfl

/-- A term of an honest PRSS round with `H` fixed, the same at every holder. -/
def honestTerm {R : Type} (h : Query C → HashOutput) (parts : C.Party → Parts C) (codec : Codec C E R)
    (ρ idx count : ℕ) (T : C.Term) : ℕ → R :=
  D prims h (codec.draw (.term T) (h (termInput .prss parts T)) ρ idx count)

/-- A pair stream of an honest PRSS round with `H` fixed, the same at both members. -/
def honestPair {R : Type} (h : Query C → HashOutput) (parts : C.Party → Parts C) (codec : Codec C E R)
    (ρ idx count : ℕ) (p : C.Pair) : ℕ → R :=
  D prims h (codec.draw (.pair p) (h (pairInput .prss parts p)) ρ idx count)

theorem D_termDraws {R : Type} [Zero R] (h : Query C → HashOutput) (parts : C.Party → Parts C) (i : C.Party)
    (keys : Keys C) (codec : Codec C E R) (ρ idx count : ℕ) (T : C.Term) :
    (D prims h (termDraws ⟨i, keys, honestPrssKeys h parts i⟩ codec ρ idx count)).getD (C.terms.idxOf T)
        (fun _ => 0) = if i ∈ C.holders T then honestTerm prims h parts codec ρ idx count T else fun _ => 0 := by
  unfold termDraws
  rw [D_mapM, getD_terms_idxOf (fun T => D prims h (if i ∈ C.holders T then
    codec.draw (.term T) ((honestPrssKeys h parts i).term T) ρ idx count else pure fun _ => 0))]
  split_ifs with hi
  · simp [honestTerm, honestPrssKeys, hi]
  · rfl

theorem D_pairDraws {R : Type} [Zero R] (h : Query C → HashOutput) (parts : C.Party → Parts C) (i : C.Party)
    (keys : Keys C) (codec : Codec C E R) (ρ idx count : ℕ) (j : C.Party) :
    (D prims h (pairDraws ⟨i, keys, honestPrssKeys h parts i⟩ codec ρ idx count)).getD j.val (fun _ => 0) =
      if hj : j = i then fun _ => 0 else honestPair prims h parts codec ρ idx count (C.pairOf i j (Ne.symm hj)) := by
  unfold pairDraws
  rw [D_mapM, getD_parties (fun j => D prims h (if hj : j = i then pure fun _ => 0 else
    codec.draw (.pair (C.pairOf i j (Ne.symm hj))) ((honestPrssKeys h parts i).pair j) ρ idx count))]
  split_ifs with hj
  · rfl
  · simp [honestPair, honestPrssKeys, hj]

/-- The honest pair streams cancel in the sum over all operators. -/
theorem sum_honestPairs {R : Type} [Field R] [CharP R 2] (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (codec : Codec C E R) (ρ idx count g : ℕ) :
    ∑ i : C.Party, ∑ j ∈ Finset.univ.erase i,
      (if hj : j = i then fun _ => 0 else honestPair prims h parts codec ρ idx count (C.pairOf i j (Ne.symm hj))) g = 0 := by
  have := sum_pairs_eq_zero (R := R) Finset.univ fun p => honestPair prims h parts codec ρ idx count p g
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [dif_pos rfl, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  rw [dif_neg hji, dif_neg (Ne.symm hji)]

end RealGadgets

/-! ### An honest peer reshare -/

section HonestReshare

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) {R : Type} [Field R]

/-- The terms of an honest PRSS round at operator `i`. -/
def honestR (rr : C.Term → ℕ → R) (i : C.Party) : Shares C R :=
  fun T => if i ∈ C.holders T then rr T else fun _ => 0

/-- The pair streams of an honest PRSS round at operator `i`. -/
def honestZ (zz : C.Pair → ℕ → R) (i : C.Party) : C.Party → ℕ → R :=
  fun j => if hj : j = i then fun _ => 0 else zz (C.pairOf i j (Ne.symm hj))

variable (ctx : C.Party → Context C) (rr : C.Term → ℕ → R) (zz : C.Pair → ℕ → R) (v : C.Party → ℕ → R)

/-- The sharing that an honest peer reshare gives, before the restriction to the held terms. -/
def honestShare (T : C.Term) (g : ℕ) : R :=
  if T ∈ filledTerms K then
    ∑ j ∈ Finset.univ.filter (K.filled · = T), reshareU K (ctx j) (honestR rr j) (honestZ zz j) (v j) g
  else rr T g

/-- An honest peer reshare shares the sum of the inputs (GS20, Lemma 4, with no corrupt operator). -/
theorem sum_honestShare [CharP R 2] (hctx : ∀ i, (ctx i).self = i) (g : ℕ) :
    ∑ T, honestShare K ctx rr zz v T g = ∑ i, v i g := by
  set u := fun j => reshareU K (ctx j) (honestR rr j) (honestZ zz j) (v j) g
  have hfill : ∑ T ∈ filledTerms K, ∑ j ∈ Finset.univ.filter (K.filled · = T), u j = ∑ j, u j := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := filledTerms K) (g := K.filled)
      (fun j _ => by simp [filledTerms])]
  have hpairs : ∑ j : C.Party, ∑ k ∈ Finset.univ.erase (ctx j).self, honestZ zz j k g = 0 := by
    have := sum_pairs_eq_zero (R := R) (C := C) Finset.univ fun p => zz p g
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [dif_pos rfl, add_zero, hctx]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    simp only [honestZ, dif_neg hki, dif_neg (Ne.symm hki)]
  have hown : ∑ j : C.Party, ∑ T ∈ Finset.univ.filter (fun T => T ∉ filledTerms K ∧ K.owner T = (ctx j).self),
      honestR rr j T g = ∑ T ∈ Finset.univ.filter (· ∉ filledTerms K), rr T g := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (· ∉ filledTerms K))
      (t := Finset.univ) (g := K.owner) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hctx, Finset.filter_filter]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hT' := (Finset.mem_filter.mp hT).2
    simp only [honestR, if_pos (hT'.2 ▸ K.owner_held T)]
  have hu : ∑ j, u j = ∑ i, v i g + ∑ T ∈ Finset.univ.filter (· ∉ filledTerms K), rr T g := by
    simp only [u, reshareU, Finset.sum_add_distrib, hpairs, add_zero, hown]
  unfold honestShare
  rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, hfill, hu, add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

/-- Each honest operator gets its held terms of `honestShare`. -/
theorem reshareZ_honest (codec : Codec C E R) (hcodec : CodecRoundTrip codec) (hctx : ∀ i, (ctx i).self = i)
    (count : ℕ) (i : C.Party) (T : C.Term) (g : ℕ) :
    reshareZ K (ctx i) codec (honestR rr i) (honestZ zz i) (v i) count
        (fun k => reshareOut K (ctx k) codec (honestR rr k) (honestZ zz k) (v k) count i) T g =
      if i ∈ C.holders T ∧ g < count then honestShare K ctx rr zz v T g else 0 := by
  unfold reshareZ honestShare
  rw [hctx]
  by_cases hiT : i ∈ C.holders T
  · by_cases hg : g < count
    · have h1 : ¬ (i ∉ C.holders T ∨ count ≤ g) := by simp [hiT]; omega
      rw [if_neg h1, if_pos (show i ∈ C.holders T ∧ g < count from ⟨hiT, hg⟩)]
      by_cases hT : T ∈ filledTerms K
      · simp only [hT, if_true]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjT : K.filled j = T := (Finset.mem_filter.mp hj).2
        by_cases hji : j = i
        · rw [if_pos hji, hji]
        · rw [if_neg hji]
          have h2 : j ≠ (ctx j).self → False := fun h => h (hctx j).symm
          simp only [reshareOut, hctx, ne_eq, Ne.symm hji, not_false_eq_true, hjT, hiT, and_self, if_true]
          rw [(hcodec _ g).1, List.getD_eq_getElem?_getD, vector, List.getElem?_map, List.getElem?_range hg]
          rfl
      · simp [hT, honestR, hiT]
    · rw [if_pos (Or.inr (by omega)), if_neg (by tauto)]
  · rw [if_pos (Or.inl hiT), if_neg (by tauto)]

end HonestReshare

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RunFacts

variable {C : Committee} (prims : Primitives)

/-- A run of computations of `H` and `PRG` of all operators gives the values with one `H` that is
`Th` on the inputs of the MPC and agrees with the final cache. -/
theorem localRun_D {β : Type} {n : ℕ} (oa : Fin n → OracleComp (RoSpec C) β) (s : HashCache C) (hs : NoMpc s)
    (z) (hz : z ∈ support ((simulateQ (localAnswer prims)
      (Concrete.sequenceFin fun i => liftComp (oa i) (LocalSpec C))).run s)) :
    s ≤ z.2 ∧ NoMpc z.2 ∧ ∃ h, Good prims h ∧ Agrees h z.2 ∧ ∀ i, z.1 i = D prims h (oa i) := by
  obtain ⟨hle, hn, hsupp⟩ := localRun_support _ s z hz
  have hn' := hn hs
  refine ⟨hle, hn', hashOf prims z.2, good_hashOf prims z.2, agrees_hashOf prims hn', ?_⟩
  have := hsupp _ (good_hashOf prims z.2) (agrees_hashOf prims hn')
  rw [simulateQ_sequenceFin] at this
  simp only [simulateQ_fixedLocal_liftComp] at this
  rw [sequenceFin_pure] at this
  simp only [support_pure, Set.mem_singleton_iff] at this
  intro i
  rw [this]

/-- A run of one computation of `H` and `PRG`. -/
theorem localRun_D_one {β : Type} (oa : OracleComp (RoSpec C) β) (s : HashCache C) (hs : NoMpc s)
    (z) (hz : z ∈ support ((simulateQ (localAnswer prims) (liftComp oa (LocalSpec C))).run s)) :
    s ≤ z.2 ∧ NoMpc z.2 ∧ ∃ h, Good prims h ∧ Agrees h z.2 ∧ z.1 = D prims h oa := by
  obtain ⟨hle, hn, hsupp⟩ := localRun_support _ s z hz
  have hn' := hn hs
  refine ⟨hle, hn', hashOf prims z.2, good_hashOf prims z.2, agrees_hashOf prims hn', ?_⟩
  have := hsupp _ (good_hashOf prims z.2) (agrees_hashOf prims hn')
  rw [simulateQ_fixedLocal_liftComp] at this
  simpa using this

/-- A coin key or an expansion, the queries that the bounds of the checks track. -/
def IsCoin (q : Query C) : Prop := (∃ k idx, q = .expand k idx) ∨ (∃ tag ρ v, q = .coinKey tag ρ v)

/-- A computation of `H` and `PRG` that keeps the coin entries of the cache. -/
def FrameR {β : Type} (oa : OracleComp (RoSpec C) β) : Prop :=
  ∀ s z, z ∈ support ((simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) oa).run s) →
    ∀ q, IsCoin q → z.2 q = s q

/-- A local computation that keeps the coin entries of the cache. -/
def FrameL {β : Type} (oa : OracleComp (LocalSpec C) β) : Prop :=
  ∀ s z, z ∈ support ((simulateQ (localAnswer prims) oa).run s) → ∀ q, IsCoin q → z.2 q = s q

variable {prims}

theorem FrameR.pure {β : Type} (b : β) : FrameR prims (pure b : OracleComp (RoSpec C) β) := by
  intro s z hz q _
  simp at hz; rw [hz]

theorem FrameR.bind {β γ : Type} {oa : OracleComp (RoSpec C) β} {f : β → OracleComp (RoSpec C) γ}
    (h : FrameR prims oa) (hf : ∀ b, FrameR prims (f b)) : FrameR prims (oa >>= f) := by
  intro s z hz q hq
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  rw [hf y.1 y.2 z hz q hq, h s y hy q hq]

theorem FrameR.map {β γ : Type} {oa : OracleComp (RoSpec C) β} (f : β → γ) (h : FrameR prims oa) :
    FrameR prims (f <$> oa) := by
  rw [map_eq_bind_pure_comp]; exact h.bind fun _ => FrameR.pure _

theorem FrameR.hashQuery {q : Query C} (hq : ¬ IsCoin q) : FrameR prims (hashQuery q) := by
  intro s z hz q' hq'
  have hne : q' ≠ q := fun e => hq (e ▸ hq')
  by_cases hfix : IsFixed q
  · obtain ⟨input, rfl, hm⟩ := hfix
    have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (ThresholdLeanXmss.hashQuery (.hash input)) =
        hashAnswer prims (.hash input) := (simulateQ_query _ _).trans (id_map _)
    rw [h1, hashAnswer_of_isFixed prims hm] at hz
    simp at hz; rw [hz]
  · rcases hs : s q' with _ | u
    · by_contra hc
      rcases support_hashQuery_entries prims hfix s z hz q' hc with h | h
      · exact h hs
      · exact hne h
    · have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (ThresholdLeanXmss.hashQuery q) =
          hashAnswer prims q := (simulateQ_query _ _).trans (id_map _)
      rw [h1] at hz
      exact grows_hashAnswer prims q s z hz hs

theorem FrameR.prg (x : PrgInput C) :
    FrameR prims (query (spec := RoSpec C) (.inr x) : OracleComp (RoSpec C) Bit) := by
  intro s z hz q hq
  have h1 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      (query (spec := RoSpec C) (.inr x) : OracleComp (RoSpec C) Bit) = prgAnswer prims x :=
    (simulateQ_query _ _).trans (id_map _)
  rw [h1] at hz
  simp [prgAnswer] at hz
  obtain ⟨p, hp, rfl⟩ := hz
  have h2 : simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims)
      (ThresholdLeanXmss.hashQuery (.streamKey x.2.1)) = hashAnswer prims (.streamKey x.2.1) :=
    (simulateQ_query _ _).trans (id_map _)
  exact FrameR.hashQuery (prims := prims) (q := .streamKey x.2.1)
    (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h) s p (by rw [h2]; exact hp) q hq

theorem FrameR.mapM {α β : Type} (f : α → OracleComp (RoSpec C) β) (hf : ∀ a, FrameR prims (f a)) :
    ∀ l : List α, FrameR prims (l.mapM f)
  | [] => FrameR.pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun b => (FrameR.mapM f hf l).bind fun _ => FrameR.pure _

theorem FrameR.ite {β : Type} (c : Prop) [Decidable c] {a b : OracleComp (RoSpec C) β}
    (ha : FrameR prims a) (hb : FrameR prims b) : FrameR prims (if c then a else b) := by
  split_ifs <;> assumption

theorem FrameR.tweakable {β : Type} (oa : OracleComp HashSpec β) : FrameR prims (tweakable (C := C) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure b => exact FrameR.pure b
  | query_bind t k ih =>
    unfold ThresholdLeanXmss.tweakable at ih ⊢
    rw [simulateQ_bind]
    refine FrameR.bind ?_ ih
    rw [simulateQ_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    exact FrameR.hashQuery (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)

theorem FrameL.liftComp {β : Type} {oa : OracleComp (RoSpec C) β} (h : FrameR prims oa) :
    FrameL prims (liftComp oa (LocalSpec C)) := by
  intro s z hz
  rw [simulateQ_localAnswer_liftComp] at hz
  exact h s z hz

theorem FrameL.pure {β : Type} (b : β) : FrameL prims (pure b : OracleComp (LocalSpec C) β) := by
  intro s z hz q _
  simp at hz; rw [hz]

theorem FrameL.bind {β γ : Type} {oa : OracleComp (LocalSpec C) β} {f : β → OracleComp (LocalSpec C) γ}
    (h : FrameL prims oa) (hf : ∀ b, FrameL prims (f b)) : FrameL prims (oa >>= f) := by
  intro s z hz q hq
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  rw [hf y.1 y.2 z hz q hq, h s y hy q hq]

theorem FrameL.sequenceFin {β : Type} : ∀ {n : ℕ} (f : Fin n → OracleComp (LocalSpec C) β),
    (∀ i, FrameL prims (f i)) → FrameL prims (Concrete.sequenceFin f)
  | 0, f, _ => by simp only [Concrete.sequenceFin]; exact FrameL.pure _
  | n + 1, f, hf => by
    simp only [Concrete.sequenceFin]
    exact (hf 0).bind fun _ => (FrameL.sequenceFin _ fun i => hf i.succ).bind fun _ => FrameL.pure _

theorem cacheOK_of_frame {Ks : Finset HashOutput} {L : ℕ} {s s' : HashCache C} (hs : CacheOK Ks L s)
    (h : ∀ q, IsCoin q → s' q = s q) : CacheOK Ks L s' := by
  intro q hq
  refine ⟨fun k idx hk => ?_, fun tag ρ v hk => ?_⟩
  · have hc : IsCoin q := Or.inl ⟨k, idx, hk⟩
    exact (hs q (by rw [← h q hc]; exact hq)).1 k idx hk
  · have hc : IsCoin q := Or.inr ⟨tag, ρ, v, hk⟩
    exact (hs q (by rw [← h q hc]; exact hq)).2 tag ρ v hk

end RunFacts

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RealSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) {ι : Type} {G : OracleSpec ι}

/-- The PRSS outputs that operator `ctx.self` draws in round `ρ`. -/
def prssDraw {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R) (ρ idx count : ℕ) :
    OracleComp (RoSpec C) (PrssOutput C R) := do
  let r ← termDraws ctx codec ρ idx count
  let Z ← pairDraws ctx codec ρ idx count
  pure (fun T => r.getD (C.terms.idxOf T) fun _ => 0, fun j => Z.getD j.val fun _ => 0)

@[simp] theorem oracleStep_pure {α : Type} (a : α) :
    (oracleStep (C := C) (E := E) (G := G) (pure a : OracleComp (RoSpec C) α)) = pure a := by
  simp [oracleStep, localStep]

/-- The state after one round label. -/
def nextLabel (st : RunState C) : RunState C := ⟨st.history, st.label + 1, st.tag⟩

theorem prssRandomness_run {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R) (idx count : ℕ)
    {α : Type} (f : PrssOutput C R → RunM C E G α) (st : RunState C) :
    (prssRandomness ctx codec idx count >>= f).run st =
      oracleStep (prssDraw ctx codec st.label idx count) >>= fun o => (f o).run (nextLabel st) := by
  simp only [prssRandomness_eq, prssDraw, freshLabel, bind_assoc, oracleStep_bind]
  simp [StateT.run_bind, StateT.run_lift, StateT.run_modifyGet, nextLabel]

def openShareN (i : C.Party) (v : ℕ → E) (inbox : Mail C E) : C.Party → ℕ → E := fun j g =>
  if j = i then v g else Msg.elementAt (inbox j) g

def OpenAgreesN (i : C.Party) (v : ℕ → E) (count : ℕ) (inbox : Mail C E) : Prop :=
  ∀ j : C.Party, ∀ g < count, openShareN i v inbox j g =
    ∑ l ∈ Finset.univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K (K.point j) l * openShareN i v inbox l g

def openValueN (i : C.Party) (v : ℕ → E) (inbox : Mail C E) : ℕ → E := fun g =>
  ∑ l ∈ Finset.univ.filter (fun l : C.Party => l.val < C.t), lagrangeFirst K 0 l * openShareN i v inbox l g

theorem openSh_eqN (ctx : Context C) (v : ℕ → E) (count : ℕ) :
    (openSh (G := G) K ctx v count) = exchange (openOut ctx.self v count) >>= fun inbox =>
      require (OpenAgreesN K ctx.self v count inbox) >>= fun _ => pure (openValueN K ctx.self v inbox) := rfl

theorem openShareN_honest (v : C.Party → ℕ → E) (count : ℕ) (i j : C.Party) (g : ℕ) (hg : g < count) :
    openShareN i (v i) (fun k => openOut (E := E) k (v k) count i) j g = v j g := by
  unfold openShareN
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj, openOut, Ne.symm hj, Msg.elementAt, vector, hg]

theorem openShN_honest (v : C.Party → ℕ → E) (vals : ℕ → E) (count : ℕ)
    (hv : ∀ g < count, IsShamir K (fun i => v i g) (vals g)) (i : C.Party) :
    OpenAgreesN K i (v i) count (fun k => openOut (E := E) k (v k) count i) ∧
      ∀ g < count, openValueN K i (v i) (fun k => openOut (E := E) k (v k) count i) g = vals g := by
  constructor
  · intro j g hg
    obtain ⟨P, hP, -, hPi⟩ := hv g hg
    simp only [openShareN_honest v count i _ g hg, hPi]
    exact (sum_lagrangeFirst_mul_eval K P hP _).symm
  · intro g hg
    obtain ⟨P, hP, hP0, hPi⟩ := hv g hg
    simp only [openValueN, openShareN_honest v count i _ g hg, hPi]
    rw [sum_lagrangeFirst_mul_eval K P hP, hP0]

theorem isAbort_openOutboxN (k : C.Party) (v : ℕ → E) (count : ℕ) (j : C.Party) :
    Msg.isAbort (openOut (E := E) k v count j) = false := by
  unfold openOut; split_ifs <;> rfl

end RealSteps

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RealRuns

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) {ι : Type} {G : OracleSpec ι}

/-- The running values after `record` of a peer reshare at operator `i`. -/
def recordPeer {R : Type} (codec : Codec C E R) (i : C.Party) (h : C.Term → List Bit) (z : Shares C R) (count : ℕ) :
    C.Term → List Bit := fun T =>
  if i ∈ C.holders T then
    h T ++ ((List.range count).filter fun g => (filler K .peer T g).isSome).flatMap (codec.toBits ∘ z T)
  else h T

theorem reshare_run {R : Type} [Field R] (ctx : Context C) (codec : Codec C E R) (r : Shares C R)
    (Zs : C.Party → ℕ → R) (v : ℕ → R) (count : ℕ) (st : RunState C) :
    (reshare (G := G) K ctx codec (r, Zs) v count).run st =
      exchange (reshareOut K ctx codec r Zs v count) >>= fun inbox =>
        pure (reshareZ K ctx codec r Zs v count inbox,
          ⟨recordPeer K codec ctx.self st.history (reshareZ K ctx codec r Zs v count inbox) count, st.label, st.tag⟩) := by
  unfold reshare
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine congrArg (_ >>= ·) (funext fun inbox => ?_)
  simp only [record, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
  rfl

/-- The products of an extended multiplication as additive shares. -/
def contextProductValues (ctx : Context C) (products : List (Product C E)) : ℕ → E :=
  fun g => match products[g]? with | some p => productShare K ctx p | none => 0

theorem realExtendMult_run (ctx : Context C) (products : List (Product C E)) (st : RunState C) :
    ((realCheckGadgets (G := G) K ctx).extendMult products).run st =
      oracleStep (prssDraw ctx (elementCodec K) st.label 0 products.length) >>= fun o =>
        exchange (reshareOut K ctx (elementCodec K) o.1 o.2 (contextProductValues K ctx products) products.length) >>=
          fun inbox => pure (reshareZ K ctx (elementCodec K) o.1 o.2 (contextProductValues K ctx products) products.length inbox,
            ⟨recordPeer K (elementCodec K) ctx.self st.history (reshareZ K ctx (elementCodec K) o.1 o.2
              (contextProductValues K ctx products) products.length inbox) products.length, st.label + 1, st.tag⟩) := by
  have := prssRandomness_run (G := G) ctx (elementCodec K) 0 products.length
    (fun o => reshare K ctx (elementCodec K) o (contextProductValues K ctx products) products.length) st
  exact this.trans (congrArg (_ >>= ·) (funext fun o => by
    rw [show o = (o.1, o.2) from rfl, reshare_run]; rfl))

theorem realCoin_run (ctx : Context C) (count : ℕ) (st : RunState C) :
    ((realCheckGadgets (G := G) K ctx).coin count).run st =
      oracleStep (prssDraw ctx (elementCodec K) st.label 1 count) >>= fun o =>
        openSh K ctx (conv K ctx o.1) count >>= fun opened => pure (vector count opened, nextLabel st) := by
  have := prssRandomness_run (G := G) ctx (elementCodec K) 1 count (fun o => coinWith K ctx o count) st
  simp only [realCheckGadgets]
  rw [this]
  refine congrArg (_ >>= ·) (funext fun o => ?_)
  simp [coinWith, StateT.run_bind, StateT.run_lift]

theorem realRand_run {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R) (idx count : ℕ) (st : RunState C) :
    (prssRandomness (G := G) ctx codec idx count).run st =
      oracleStep (prssDraw ctx codec st.label idx count) >>= fun o => pure (o, nextLabel st) := by
  have := prssRandomness_run (G := G) ctx codec idx count pure st
  simpa using this

theorem realChallenge_run (ctx : Context C) (st : RunState C) :
    (challenge K (realCheckGadgets (G := G) K ctx)).run st =
      oracleStep (prssDraw ctx (elementCodec K) st.label 1 1) >>= fun o =>
        openSh K ctx (conv K ctx o.1) 1 >>= fun opened =>
          oracleStep (challengeQuery K st.tag st.label (vector 1 opened)) >>= fun r => match r with
            | some r => pure (r, nextLabel st)
            | none => failure := by
  simp only [challenge, coinKey, challengeQuery, StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  rw [realCoin_run]
  simp only [bind_assoc, pure_bind, oracleStep_bind]
  refine congrArg (_ >>= ·) (funext fun o => congrArg (_ >>= ·) (funext fun opened => ?_))
  simp only [StateT.run_lift, bind_assoc, pure_bind]
  refine congrArg (_ >>= ·) (funext fun key => congrArg (_ >>= ·) (funext fun r => ?_))
  rcases r with _ | r
  · simp [StateT.run_lift]
  · rfl

theorem realTau_run (ctx : Context C) (count : ℕ) (st : RunState C) :
    (coinKey K (realCheckGadgets (G := G) K ctx) >>= fun key => expand K key count).run st =
      oracleStep (prssDraw ctx (elementCodec K) st.label 1 1) >>= fun o =>
        openSh K ctx (conv K ctx o.1) 1 >>= fun opened =>
          oracleStep (tauQuery K st.tag st.label (vector 1 opened) count) >>= fun τ => pure (τ, nextLabel st) := by
  simp only [coinKey, expand, tauQuery, StateT.run_bind, StateT.run_get, pure_bind, bind_assoc]
  rw [realCoin_run]
  simp only [bind_assoc, pure_bind, oracleStep_bind]
  refine congrArg (_ >>= ·) (funext fun o => congrArg (_ >>= ·) (funext fun opened => ?_))
  simp [StateT.run_lift]

end RealRuns

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section PrssValues

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (prims : Primitives)

/-- Operator `i` with its keys and the PRSS keys `kT` of its held terms and `kP` of its pairs. -/
def prssCtx (keys : C.Party → Keys C) (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (i : C.Party) :
    Context C :=
  ⟨i, keys i, ⟨fun T => if i ∈ C.holders T then kT T else 0,
    fun j => if hj : j = i then 0 else kP (C.pairOf i j (Ne.symm hj))⟩⟩

theorem D_prssDraw {R : Type} [Field R] (h : Query C → HashOutput) (keys : C.Party → Keys C)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (i : C.Party) (codec : Codec C E R) (ρ idx count : ℕ) :
    D prims h (prssDraw (prssCtx keys kT kP i) codec ρ idx count) =
      (honestR (fun T => D prims h (codec.draw (.term T) (kT T) ρ idx count)) i,
        honestZ (fun p => D prims h (codec.draw (.pair p) (kP p) ρ idx count)) i) := by
  unfold prssDraw
  simp only [D_bind, D_pure]
  refine Prod.ext (funext fun T => ?_) (funext fun j => ?_)
  · show (D prims h (termDraws _ codec ρ idx count)).getD (C.terms.idxOf T) (fun _ => 0) = _
    unfold termDraws
    rw [D_mapM, getD_terms_idxOf]
    by_cases hi : i ∈ C.holders T
    · simp [honestR, prssCtx, hi]
    · simp [honestR, prssCtx, hi, D_pure]
  · show (D prims h (pairDraws _ codec ρ idx count)).getD j.val (fun _ => 0) = _
    unfold pairDraws
    rw [D_mapM, getD_parties]
    by_cases hj : j = i
    · simp [honestZ, prssCtx, hj, D_pure]
    · simp [honestZ, prssCtx, hj]

variable {prims}

theorem FrameR.prgBits (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    FrameR prims (prgBits name key ρ idx count) := by
  unfold ThresholdLeanXmss.prgBits
  exact (FrameR.mapM _ (fun position => FrameR.prg (name, key, ρ, idx, position)) _).bind fun _ => FrameR.pure _

theorem FrameR.bitDraw (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    FrameR prims ((bitCodec (C := C) (E := E)).draw name key ρ idx count) := FrameR.prgBits _ _ _ _ _

theorem FrameR.elementDraw (K : Constants C E) (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    FrameR prims ((elementCodec K).draw name key ρ idx count) :=
  (FrameR.prgBits _ _ _ _ _).bind fun _ => FrameR.pure _

theorem FrameR.prssDraw {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R)
    (hdraw : ∀ name key ρ idx count, FrameR prims (codec.draw name key ρ idx count)) (ρ idx count : ℕ) :
    FrameR prims (prssDraw ctx codec ρ idx count) := by
  unfold ThresholdLeanXmssSecurity.prssDraw termDraws pairDraws
  refine (FrameR.mapM _ (fun T => FrameR.ite _ (hdraw _ _ _ _ _) (FrameR.pure _)) _).bind fun _ =>
    (FrameR.mapM _ (fun j => ?_) _).bind fun _ => FrameR.pure _
  split_ifs
  · exact FrameR.pure _
  · exact hdraw _ _ _ _ _

end PrssValues

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section DrawStep

variable {C : Committee} {E : Type} {I O L R α : Type} (prims : Primitives)

/-- The honest network after an own computation of `H` and `PRG` of each operator that keeps the
coin entries. Each operator continues with the value of its computation under one `H`. -/
theorem draw_step {β : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (oa : C.Party → OracleComp (RoSpec C) β) (hframe : ∀ i, FrameR prims (oa i))
    (g : C.Party → β → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (h₀ : Query C → HashOutput) (s' : HashCache C), Good prims h₀ → Agrees h₀ s' → NoMpc s' → s ≤ s' →
      (∀ q, IsCoin q → s' q = s q) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (D prims h₀ (oa i))) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep (oa i) >>= g i) >>= honestRounds F reply fuel)).run' s] ≤ ε := by
  refine probEvent_honest_local prims F reply fuel oa g event s ε fun z hz => ?_
  obtain ⟨hle, hn', h₀, hg, ha, hv⟩ := localRun_D prims oa s hn z hz
  have hfr := FrameL.sequenceFin (prims := prims) (fun i => liftComp (oa i) (LocalSpec C))
    (fun i => FrameL.liftComp (hframe i)) s z hz
  have : z.1 = fun i => D prims h₀ (oa i) := funext hv
  rw [this]
  exact h h₀ z.2 hg ha hn' hle hfr

end DrawStep

section RealGadgetSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {I O L R α : Type} (prims : Primitives)
  (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput)

theorem vector_congr' {R' : Type} (count : ℕ) (a b : ℕ → R') (h : ∀ g < count, a g = b g) :
    vector count a = vector count b := by
  unfold vector
  exact List.map_congr_left fun g hg => h g (List.mem_range.1 hg)

theorem conv_prssCtx (i : C.Party) (x : Shares C E) :
    conv K (prssCtx keys kT kP i) x = conv K (localContext i) x := rfl

/-- An honest opening of a Shamir vector. Every operator continues with the opened values. -/
theorem openSh_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (v : C.Party → ℕ → E) (vals : ℕ → E) (count : ℕ) (hv : ∀ g < count, IsShamir K (fun i => v i g) (vals g))
    (g : C.Party → (ℕ → E) → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (ε : ℝ≥0∞)
    (h : Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (openValueN K i (v i) (fun k => openOut (E := E) k (v k) count i))) >>=
          honestRounds F reply fuel)).run' s] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => openSh K (localContext i) (v i) count >>= g i) >>=
        honestRounds F reply (fuel + 1))).run' s] ≤ ε := by
  simp only [openSh_eqN, bind_assoc, localContext]
  rw [honestRounds_exchange F reply fuel (fun i => openOut i (v i) count) _
    fun k j => isAbort_openOutboxN k _ _ j]
  simp only [require_bind_of (openShN_honest K v vals count hv _).1, pure_bind]
  exact h

theorem openSh_prssCtx {ι : Type} {G : OracleSpec ι} (i : C.Party) :
    openSh (G := G) K (prssCtx keys kT kP i) = openSh K (localContext i) := rfl

theorem isShamir_honestR [CharP E 2] (rr : C.Term → ℕ → E) (k : ℕ) :
    IsShamir K (fun i => conv K (localContext i) (honestR rr i) k) (∑ T, rr T k) :=
  (isShamir_conv rr k).congr (fun i => (conv_congr i _ _ k fun T hT => by simp [honestR, hT]).symm) rfl

/-- An honest real coin of one value. Every operator continues with one common value. -/
theorem coin_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (st : C.Party → RunState C) (lab : ℕ) (hL : ∀ i, (st i).label = lab)
    (g : C.Party → List E → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (v : List E) (s' : HashCache C), NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i v (nextLabel (st i))) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => ((realCheckGadgets K (prssCtx keys kT kP i)).coin 1).run (st i) >>= fun p =>
        g i p.1 p.2) >>= honestRounds F reply (fuel + 1))).run' s] ≤ ε := by
  haveI := charP_two (E := E)
  simp only [realCoin_run, hL, bind_assoc, pure_bind, openSh_prssCtx]
  refine draw_step prims F reply (fuel + 1) _ (fun i => FrameR.prssDraw _ _ (FrameR.elementDraw K) _ _ _) _ event s hn ε
    fun h₀ s' _ _ hn' hle hfr => ?_
  simp only [D_prssDraw, conv_prssCtx]
  set rr := fun T => D prims h₀ ((elementCodec K).draw (.term T) (kT T) lab 1 1)
  refine openSh_step prims K F reply fuel (fun i => conv K (localContext i) (honestR rr i)) (fun k => ∑ T, rr T k) 1
    (fun k _ => isShamir_honestR K rr k) _ event s' ε ?_
  have hvec : ∀ i, vector 1 (openValueN K i (conv K (localContext i) (honestR rr i))
      (fun k => openOut (E := E) k (conv K (localContext k) (honestR rr k)) 1 i)) = vector 1 (fun k => ∑ T, rr T k) :=
    fun i => vector_congr' 1 _ _ ((openShN_honest K _ _ 1 (fun k _ => isShamir_honestR K rr k) i).2)
  simp only [hvec]
  exact h _ s' hn' hle hfr

/-- Honest real PRSS outputs of one round, which need no message. -/
theorem rand_step {R' : Type} [Field R'] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (codec : Codec C E R') (hdraw : ∀ name key ρ idx count, FrameR prims (codec.draw name key ρ idx count))
    (idx count : ℕ) (st : C.Party → RunState C) (lab : ℕ) (hL : ∀ i, (st i).label = lab)
    (g : C.Party → PrssOutput C R' → RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (rr : C.Term → ℕ → R') (zz : C.Pair → ℕ → R') (s' : HashCache C), NoMpc s' → s ≤ s' →
      (∀ q, IsCoin q → s' q = s q) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (honestR rr i, honestZ zz i) (nextLabel (st i))) >>=
          honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => (prssRandomness (prssCtx keys kT kP i) codec idx count).run (st i) >>= fun p =>
        g i p.1 p.2) >>= honestRounds F reply fuel)).run' s] ≤ ε := by
  simp only [realRand_run, hL, bind_assoc, pure_bind]
  refine draw_step prims F reply fuel _ (fun i => FrameR.prssDraw _ _ hdraw _ _ _) _ event s hn ε
    fun h₀ s' _ _ hn' hle hfr => ?_
  simp only [D_prssDraw]
  exact h _ _ s' hn' hle hfr

theorem isAbort_reshareOut {R' : Type} [Field R'] (codec : Codec C E R') (hcodec : CodecRoundTrip codec)
    (ctx : Context C) (r : Shares C R') (Zs : C.Party → ℕ → R') (v : ℕ → R') (count : ℕ) (j : C.Party) :
    Msg.isAbort (reshareOut K ctx codec r Zs v count j) = false := by
  unfold reshareOut; split_ifs
  · exact (hcodec _ 0).2
  · rfl

/-- An honest real extended multiplication. Every operator continues with its held terms of one
sharing of the sum of the additive shares. -/
theorem extendMult_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (products : C.Party → List (Product C E)) (n : ℕ) (hlen : ∀ i, (products i).length = n)
    (st : C.Party → RunState C) (lab : ℕ) (hL : ∀ i, (st i).label = lab)
    (g : C.Party → Shares C E → RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (Z : Shares C E), (∀ k, ∑ T, Z T k = ∑ i, extendMultShare K i (products i) k) →
      ∀ (s' : HashCache C), NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0)
          ⟨recordHistory K i (st i).history (fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0) n,
            lab + 1, (st i).tag⟩) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => ((realCheckGadgets K (prssCtx keys kT kP i)).extendMult (products i)).run (st i) >>=
        fun p => g i p.1 p.2) >>= honestRounds F reply (fuel + 1))).run' s] ≤ ε := by
  haveI := charP_two (E := E)
  simp only [realExtendMult_run, hL, hlen, bind_assoc, pure_bind]
  refine draw_step prims F reply (fuel + 1) _ (fun i => FrameR.prssDraw _ _ (FrameR.elementDraw K) _ _ _) _ event s hn ε
    fun h₀ s' _ _ hn' hle hfr => ?_
  simp only [D_prssDraw]
  set rr := fun T => D prims h₀ ((elementCodec K).draw (.term T) (kT T) lab 0 n)
  set zz := fun p => D prims h₀ ((elementCodec K).draw (.pair p) (kP p) lab 0 n)
  rw [honestRounds_exchange F reply fuel (fun i => reshareOut K (prssCtx keys kT kP i) (elementCodec K)
    (honestR rr i) (honestZ zz i) (contextProductValues K (prssCtx keys kT kP i) (products i)) n) _
    fun k j => isAbort_reshareOut K _ (elementCodec_roundTrip K) _ _ _ _ _ _]
  set Z := honestShare K (prssCtx keys kT kP) rr zz (fun i => contextProductValues K (prssCtx keys kT kP i) (products i))
  have hz : ∀ i, reshareZ K (prssCtx keys kT kP i) (elementCodec K) (honestR rr i) (honestZ zz i)
      (contextProductValues K (prssCtx keys kT kP i) (products i)) n
        (fun k => reshareOut K (prssCtx keys kT kP k) (elementCodec K) (honestR rr k) (honestZ zz k)
          (contextProductValues K (prssCtx keys kT kP k) (products k)) n i) =
      fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0 := fun i => funext fun T => funext fun k =>
    reshareZ_honest K (prssCtx keys kT kP) rr zz _ (elementCodec K) (elementCodec_roundTrip K) (fun _ => rfl) n i T k
  simp only [hz]
  exact h Z (fun k => sum_honestShare K (prssCtx keys kT kP) rr zz _ (fun _ => rfl) k) s' hn' hle hfr

end RealGadgetSteps

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section TauKs

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] (prims : Primitives)
  (K : Constants C E)

/-- The coins `τ` start with `m` nonzero values, except with probability `|Ks| / 2^256 + m / |E|`,
when the cache holds expansions only of the keys `Ks`. -/
theorem tauQuery_zero_le_Ks (tag ρ : ℕ) (v : List E) (count m : ℕ) (hm : m ≤ count) (Ks : Finset HashOutput)
    (L : ℕ) (hρ : L ≤ ρ) (s : HashCache C) (hs : CacheOK Ks L s) :
    Pr[fun z => ¬ ∀ b < m, z.1.getD b 0 ≠ 0 |
      (simulateQ (localAnswer prims) (liftComp (tauQuery K tag ρ v count) (LocalSpec C))).run s] ≤
      Ks.card / 2 ^ 256 + m / Fintype.card E := by
  rw [simulateQ_localAnswer_liftComp, tauQuery, simulateQ_bind, StateT.run_bind]
  have hq : ¬ IsFixed (C := C) (.coinKey tag ρ (v.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩; cases h
  refine probEvent_bind_le_add (p := fun z : HashOutput × HashCache C => z.1 ∉ Ks) ?_ fun z hz hkey => ?_
  · simp only [not_not]
    exact probEvent_hash_fresh_mem prims hq (coinKey_fresh hρ hs tag _) Ks
  · rw [List.range_eq_range']
    refine probEvent_expand_zero prims K z.1 count 0 m z.2 hm fun i _ => ?_
    by_contra hne
    rcases support_hashQuery_entries prims hq s z hz _ hne with h | h
    · exact hkey ((hs _ h).1 _ i rfl)
    · cases h

/-- After the coins `τ`, the cache holds expansions of one more key. -/
theorem tauQuery_cache_Ks (tag ρ : ℕ) (v : List E) (count : ℕ) (Ks : Finset HashOutput) (L : ℕ) (hρ : L ≤ ρ)
    (s : HashCache C) (hs : CacheOK Ks L s) z
    (hz : z ∈ support ((simulateQ (localAnswer prims) (liftComp (tauQuery K tag ρ v count) (LocalSpec C))).run s)) :
    ∃ k, CacheOK (insert k Ks) (ρ + 1) z.2 := by
  rw [simulateQ_localAnswer_liftComp, tauQuery, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨key, s₁⟩, h₁, hz⟩ := hz
  have hq : ¬ IsFixed (C := C) (.coinKey tag ρ (v.flatMap fun v => List.ofFn (K.encode v))) := by
    rintro ⟨_, h, _⟩; cases h
  have hs₁ := support_hashQuery_entries prims hq s _ h₁
  have hs₂ := support_expand_entries prims K key _ _ _ hz
  refine ⟨key, fun q hq' => ?_⟩
  rcases hs₂ q hq' with h | ⟨i, rfl⟩
  · rcases hs₁ q h with h | rfl
    · obtain ⟨h1, h2⟩ := hs q h
      exact ⟨fun k idx hk => Finset.mem_insert_of_mem (h1 k idx hk), fun tag' ρ' v' hk => by
        have := h2 tag' ρ' v' hk; omega⟩
    · exact ⟨fun k idx hk => (by cases hk), fun tag' ρ' v' hk => by cases hk; omega⟩
  · exact ⟨fun k idx hk => by cases hk; exact Finset.mem_insert_self _ _, fun tag' ρ' v' hk => by cases hk⟩

end TauKs

section CoinSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

/-- The coin part of a challenge or of the coins `τ`, up to the common query of `H`. -/
theorem coinPart_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (lab : ℕ)
    (g : C.Party → List E → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (v : List E) (s' : HashCache C), NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i v) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep (prssDraw (prssCtx keys kT kP i) (elementCodec K) lab 1 1) >>= fun o =>
        openSh K (prssCtx keys kT kP i) (conv K (prssCtx keys kT kP i) o.1) 1 >>= fun opened =>
          g i (vector 1 opened)) >>= honestRounds F reply (fuel + 1))).run' s] ≤ ε := by
  haveI := charP_two (E := E)
  simp only [openSh_prssCtx]
  refine draw_step prims F reply (fuel + 1) _ (fun i => FrameR.prssDraw _ _ (FrameR.elementDraw K) _ _ _) _ event s hn ε
    fun h₀ s' _ _ hn' hle hfr => ?_
  simp only [D_prssDraw, conv_prssCtx]
  set rr := fun T => D prims h₀ ((elementCodec K).draw (.term T) (kT T) lab 1 1)
  refine openSh_step prims K F reply fuel (fun i => conv K (localContext i) (honestR rr i)) (fun k => ∑ T, rr T k) 1
    (fun k _ => isShamir_honestR K rr k) _ event s' ε ?_
  have hvec : ∀ i, vector 1 (openValueN K i (conv K (localContext i) (honestR rr i))
      (fun k => openOut (E := E) k (conv K (localContext k) (honestR rr k)) 1 i)) = vector 1 (fun k => ∑ T, rr T k) :=
    fun i => vector_congr' 1 _ _ ((openShN_honest K _ _ 1 (fun k _ => isShamir_honestR K rr k) i).2)
  simp only [hvec]
  exact h _ s' hn' hle hfr

/-- An honest real challenge. It fails with probability at most `|Ks| / 2^256 + (2 / |E|)^tries`. -/
theorem challenge_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (st : C.Party → RunState C) (lab tg : ℕ) (hL : ∀ i, (st i).label = lab) (hT : ∀ i, (st i).tag = tg)
    (g : C.Party → E → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (r : E) (Ks' : Finset HashOutput) (s' : HashCache C), Ks'.card ≤ Ks.card + 1 →
      CacheOK Ks' (lab + 1) s' → NoMpc s' → s ≤ s' →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i r (nextLabel (st i))) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => (challenge K (realCheckGadgets K (prssCtx keys kT kP i))).run (st i) >>= fun p =>
        g i p.1 p.2) >>= honestRounds F reply (fuel + 1))).run' s] ≤
      (Ks.card / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries) + ε := by
  simp only [realChallenge_run, hL, hT, bind_assoc]
  refine coinPart_step prims K keys kT kP F reply fuel lab (fun i v => oracleStep (challengeQuery K tg lab v) >>=
    fun x => (match x with | some r => pure (r, nextLabel (st i)) | none => failure) >>= fun p => g i p.1 p.2)
    event s hn _ fun v s' hn' hle hfr => ?_
  have hs' := cacheOK_of_frame hs hfr
  refine (probEvent_honest_common prims F reply fuel (challengeQuery K tg lab v) _ event
    (fun z => z.1 = none) s' ε fun z hz hbad => ?_).trans
      (add_le_add (challengeQuery_none_le prims K tg lab v Ks Lk hLk s' hs') le_rfl)
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp hbad
  obtain ⟨k, hk⟩ := challengeQuery_cache prims K tg lab v Ks Lk hLk s' hs' z hz
  obtain ⟨hle', hn'', -⟩ := localRun_D_one prims _ s' hn' z hz
  simp only [hr, pure_bind]
  exact h r (insert k Ks) z.2 (Finset.card_insert_le _ _) hk hn'' (hle.trans hle')

/-- The honest real coins `τ`. The first `sliceBits` are nonzero, except with probability at most
`|Ks| / 2^256 + sliceBits / |E|`. -/
theorem tau_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (d : ℕ)
    (hd : sliceBits ≤ d)
    (st : C.Party → RunState C) (lab tg : ℕ) (hL : ∀ i, (st i).label = lab) (hT : ∀ i, (st i).tag = tg)
    (g : C.Party → List E → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (τ : List E), (∀ b < sliceBits, τ.getD b 0 ≠ 0) → ∀ (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ Ks.card + 1 → CacheOK Ks' (lab + 1) s' → NoMpc s' → s ≤ s' →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i τ (nextLabel (st i))) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => (coinKey K (realCheckGadgets K (prssCtx keys kT kP i)) >>= fun key =>
        expand K key d).run (st i) >>= fun p => g i p.1 p.2) >>= honestRounds F reply (fuel + 1))).run' s] ≤
      (Ks.card / 2 ^ 256 + sliceBits / Fintype.card E) + ε := by
  simp only [realTau_run, hL, hT, bind_assoc, pure_bind]
  refine coinPart_step prims K keys kT kP F reply fuel lab (fun i v => oracleStep (tauQuery K tg lab v d) >>=
    fun τ => g i τ (nextLabel (st i))) event s hn _ fun v s' hn' hle hfr => ?_
  have hs' := cacheOK_of_frame hs hfr
  refine (probEvent_honest_common prims F reply fuel (tauQuery K tg lab v d) _ event
    (fun z => ¬ ∀ b < sliceBits, z.1.getD b 0 ≠ 0) s' ε fun z hz hbad => ?_).trans
      (add_le_add (tauQuery_zero_le_Ks prims K tg lab v d sliceBits hd Ks Lk hLk s' hs') le_rfl)
  rw [not_not] at hbad
  obtain ⟨k, hk⟩ := tauQuery_cache_Ks prims K tg lab v d Ks Lk hLk s' hs' z hz
  obtain ⟨hle', hn'', -⟩ := localRun_D_one prims _ s' hn' z hz
  exact h z.1 hbad (insert k Ks) z.2 (Finset.card_insert_le _ _) hk hn'' (hle.trans hle')

@[simp] theorem prssCtx_self (i : C.Party) : (prssCtx keys kT kP i).self = i := rfl

theorem compareDigests_run {ι : Type} {G : OracleSpec ι} (ctx : Context C) (salts : Shares C Bit) (st : RunState C) :
    (compareDigests (G := G) ctx salts).run st =
      oracleStep (digestQuery ctx.self salts st.history) >>= fun ds =>
        exchange (digestOutbox (E := E) ctx.self ds) >>= fun inbox =>
          require (DigestsAgree (E := E) ctx.self ds inbox) >>= fun _ => pure ((), st) := by
  simp only [compareDigests, StateT.run_bind, StateT.run_lift, StateT.run_get, bind_assoc, pure_bind]
  rfl

/-- Honest digests, whose comparison passes. -/
theorem digest_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (st : C.Party → RunState C) (hh : HistAgree fun i => (st i).history)
    (salts : C.Party → Shares C Bit) (S : Shares C Bit) (hS : ∀ i T, i ∈ C.holders T → salts i T = S T)
    (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hs : CacheOK Ks Lk s) (ε : ℝ≥0∞)
    (h : ∀ (s' : HashCache C), CacheOK Ks Lk s' → NoMpc s' → s ≤ s' →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (st i)) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => (compareDigests (prssCtx keys kT kP i) (salts i)).run (st i) >>= fun p =>
        g i p.2) >>= honestRounds F reply (fuel + 1))).run' s] ≤ ε := by
  simp only [compareDigests_run, prssCtx_self, bind_assoc, pure_bind]
  refine probEvent_honest_local prims F reply (fuel + 1) (fun i => digestQuery i (salts i) (st i).history) _ event s ε
    fun z hz => ?_
  obtain ⟨hok, hlen, hag⟩ := digests_agree prims salts S hS _ hh Ks Lk s hs z hz
  obtain ⟨hle, hn', -⟩ := localRun_D prims _ s hn z hz
  rw [honestRounds_exchange F reply fuel (fun i => digestOutbox (E := E) i (z.1 i)) _
    fun k j => by unfold digestOutbox; split_ifs <;> rfl]
  simp only [require_bind_of (digestsAgree_honest z.1 hlen hag _), pure_bind]
  exact h z.2 hok hn' hle

end CoinSteps

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RealFinal

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

@[simp] theorem realCheckGadgets_randElements {ι : Type} {G : OracleSpec ι} (ctx : Context C) (c : ℕ) :
    (realCheckGadgets (G := G) K ctx).randElements c = prssRandomness ctx (elementCodec K) 1 c := rfl

@[simp] theorem realCheckGadgets_randBits {ι : Type} {G : OracleSpec ι} (ctx : Context C) (c : ℕ) :
    (realCheckGadgets (G := G) K ctx).randBits c = prssRandomness ctx bitCodec 2 c := rfl

theorem rand_step' {R' : Type} [Field R'] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (codec : Codec C E R') (hdraw : ∀ name key ρ idx count, FrameR prims (codec.draw name key ρ idx count))
    (idx count : ℕ) (st : C.Party → RunState C) (lab : ℕ) (hL : ∀ i, (st i).label = lab)
    (g : C.Party → PrssOutput C R' × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (rr : C.Term → ℕ → R') (zz : C.Pair → ℕ → R') (s' : HashCache C), NoMpc s' → s ≤ s' →
      (∀ q, IsCoin q → s' q = s q) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ((honestR rr i, honestZ zz i), nextLabel (st i))) >>=
          honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => (prssRandomness (prssCtx keys kT kP i) codec idx count).run (st i) >>= g i) >>=
        honestRounds F reply fuel)).run' s] ≤ ε :=
  rand_step prims keys kT kP F reply fuel codec hdraw idx count st lab hL (fun i a b => g i (a, b)) event s hn ε h

theorem extendMult_step' [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (products : C.Party → List (Product C E)) (n : ℕ) (hlen : ∀ i, (products i).length = n)
    (st : C.Party → RunState C) (lab : ℕ) (hL : ∀ i, (st i).label = lab)
    (g : C.Party → Shares C E × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (Z : Shares C E), (∀ k, ∑ T, Z T k = ∑ i, extendMultShare K i (products i) k) →
      ∀ (s' : HashCache C), NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ((fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0),
          ⟨recordHistory K i (st i).history (fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0) n,
            lab + 1, (st i).tag⟩)) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => ((realCheckGadgets K (prssCtx keys kT kP i)).extendMult (products i)).run (st i) >>=
        g i) >>= honestRounds F reply (fuel + 1))).run' s] ≤ ε :=
  extendMult_step prims K keys kT kP F reply fuel products n hlen st lab hL (fun i a b => g i (a, b)) event s hn ε h

theorem digest_step' [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (st : C.Party → RunState C) (hh : HistAgree fun i => (st i).history)
    (salts : C.Party → Shares C Bit) (S : Shares C Bit) (hS : ∀ i T, i ∈ C.holders T → salts i T = S T)
    (g : C.Party → Unit × RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hs : CacheOK Ks Lk s) (ε : ℝ≥0∞)
    (h : ∀ (s' : HashCache C), CacheOK Ks Lk s' → NoMpc s' → s ≤ s' →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ((), st i)) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => (compareDigests (prssCtx keys kT kP i) (salts i)).run (st i) >>= g i) >>=
        honestRounds F reply (fuel + 1))).run' s] ≤ ε :=
  digest_step prims keys kT kP F reply fuel st hh salts S hS (fun i b => g i ((), b)) event s hn Ks Lk hs ε h

theorem challenge_step' [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (st : C.Party → RunState C) (lab tg : ℕ) (hL : ∀ i, (st i).label = lab) (hT : ∀ i, (st i).tag = tg)
    (g : C.Party → E × RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (r : E) (Ks' : Finset HashOutput) (s' : HashCache C), Ks'.card ≤ Ks.card + 1 →
      CacheOK Ks' (lab + 1) s' → NoMpc s' → s ≤ s' →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (r, nextLabel (st i))) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => (challenge K (realCheckGadgets K (prssCtx keys kT kP i))).run (st i) >>= g i) >>=
        honestRounds F reply (fuel + 1))).run' s] ≤
      (Ks.card / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries) + ε :=
  challenge_step prims K keys kT kP F reply fuel st lab tg hL hT (fun i a b => g i (a, b)) event s hn Ks Lk hLk hs ε h

theorem tau_step' [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (d : ℕ)
    (hd : sliceBits ≤ d)
    (st : C.Party → RunState C) (lab tg : ℕ) (hL : ∀ i, (st i).label = lab) (hT : ∀ i, (st i).tag = tg)
    (g : C.Party → List E × RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (τ : List E), (∀ b < sliceBits, τ.getD b 0 ≠ 0) → ∀ (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ Ks.card + 1 → CacheOK Ks' (lab + 1) s' → NoMpc s' → s ≤ s' →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (τ, nextLabel (st i))) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => (coinKey K (realCheckGadgets K (prssCtx keys kT kP i)) >>= fun key =>
        expand K key d).run (st i) >>= g i) >>= honestRounds F reply (fuel + 1))).run' s] ≤
      (Ks.card / 2 ^ 256 + sliceBits / Fintype.card E) + ε :=
  tau_step prims K keys kT kP F reply fuel d hd st lab tg hL hT (fun i a b => g i (a, b)) event s hn Ks Lk hLk hs ε h

theorem real_final_bound [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (A B : C.Party → ℕ → E) (D : C.Party → E) (a b : E)
    (hA : IsShamir K (fun i => A i 0) a) (hB : IsShamir K (fun i => B i 0) b) (hD : IsShamir K D (a * b))
    (hist : C.Party → C.Term → List Bit) (hh : HistAgree hist) (lab tg : ℕ)
    (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (Ks : Finset HashOutput) (Lk : ℕ) (hLk : Lk ≤ lab) (hs : CacheOK Ks Lk s)
    (ε : ℝ≥0∞)
    (h : ∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ Ks.card + 1 → CacheOK Ks' (lab + 4) s' → NoMpc s' → s ≤ s' →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ⟨hist' i, lab + 4, tg⟩) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => (finalStep K (prssCtx keys kT kP i) (realCheckGadgets K (prssCtx keys kT kP i))
        (A i, B i, D i)).run ⟨hist i, lab, tg⟩ >>= fun p => g i p.2) >>= honestRounds F reply (fuel + 4))).run' s] ≤
      (Ks.card / 2 ^ 256 + (2 / Fintype.card E) ^ challengeTries) + ε := by
  haveI := charP_two (E := E)
  simp only [finalStep, StateT.run_bind, bind_assoc, realCheckGadgets_randElements, realCheckGadgets_randBits]
  refine rand_step' prims keys kT kP F reply (fuel + 4) (elementCodec K) (FrameR.elementDraw K) 1 2 _ lab
    (fun _ => rfl) _ event s hn _ fun r₁ zz₁ s₁ hn₁ hle₁ hfr₁ => ?_
  dsimp only [nextLabel]
  simp only [conv_prssCtx]
  set wa := fun i => conv K (localContext i) (honestR r₁ i) 0
  set wb := fun i => conv K (localContext i) (honestR r₁ i) 1
  refine extendMult_step' prims K keys kT kP F reply (fuel + 3) (fun i => [.shamir (fun _ => wa i) (fun _ => wb i) 1,
    .shamir (fun _ => wa i + A i 0) (fun _ => wb i + B i 0) 1]) 2 (fun _ => rfl) _ (lab + 1) (fun _ => rfl) _
    event s₁ hn₁ _ fun Z₂ hZ₂ s₂ hn₂ hle₂ hfr₂ => ?_
  dsimp only
  refine rand_step' prims keys kT kP F reply (fuel + 3) bitCodec (FrameR.bitDraw) 2 256 _ (lab + 1 + 1)
    (fun _ => rfl) _ event s₂ hn₂ _ fun r₃ zz₃ s₃ hn₃ hle₃ hfr₃ => ?_
  dsimp only [nextLabel]
  have hs₃ : CacheOK Ks Lk s₃ := cacheOK_of_frame (cacheOK_of_frame (cacheOK_of_frame hs hfr₁) hfr₂) hfr₃
  have hh₄ := histAgree_record K hist hh (fun i T g => if i ∈ C.holders T ∧ g < 2 then Z₂ T g else 0) Z₂ 2
    (fun i T g hi hg => by simp [hi, hg])
  refine digest_step' prims keys kT kP F reply (fuel + 2) _ hh₄ (fun i => honestR r₃ i) r₃
    (fun i T hT => by simp [honestR, hT]) _ event s₃ hn₃ Ks Lk hs₃ _ fun s₄ hs₄ hn₄ hle₄ => ?_
  dsimp only
  refine challenge_step' prims K keys kT kP F reply (fuel + 1) _ (lab + 1 + 1 + 1) tg (fun _ => rfl) (fun _ => rfl) _
    event s₄ hn₄ Ks Lk (by omega) hs₄ ε fun r Ks' s₅ hKs' hs₅ hn₅ hle₅ => ?_
  dsimp only [nextLabel]
  simp only [StateT.run_lift, bind_assoc, pure_bind, openSh_prssCtx]
  have hwa : IsShamir K wa (∑ T, r₁ T 0) := isShamir_honestR K r₁ 0
  have hwb : IsShamir K wb (∑ T, r₁ T 1) := isShamir_honestR K r₁ 1
  have hq : ∀ k < 2, IsShamir K (fun i => conv K (localContext i)
      (fun T g => if i ∈ C.holders T ∧ g < 2 then Z₂ T g else 0) k) (∑ T, Z₂ T k) := fun k hk =>
    (isShamir_conv Z₂ k).congr (fun i => (conv_congr i _ _ k fun T hT => by simp [hT, hk]).symm) rfl
  have hq0 : ∑ T, Z₂ T 0 = (∑ T, r₁ T 0) * (∑ T, r₁ T 1) := by
    rw [hZ₂ 0]
    simp only [extendMultShare, List.getElem?_cons_zero, productShare, mulSh, localContext, Finset.sum_range_one]
    exact sum_lagrangeAll_shamir K hwa hwb
  have hq1 : ∑ T, Z₂ T 1 = ((∑ T, r₁ T 0) + a) * ((∑ T, r₁ T 1) + b) := by
    rw [hZ₂ 1]
    simp only [extendMultShare, List.getElem?_cons_succ, List.getElem?_cons_zero, productShare, mulSh,
      localContext, Finset.sum_range_one]
    exact sum_lagrangeAll_shamir K (hwa.add hA) (hwb.add hB)
  set vals : ℕ → E := fun k => match k with
    | 0 => (∑ T, r₁ T 0) + r * ((∑ T, r₁ T 0) + a)
    | 1 => (∑ T, r₁ T 1) + r * ((∑ T, r₁ T 1) + b)
    | _ => (∑ T, r₁ T 0) * (∑ T, r₁ T 1) +
        (a * b + (∑ T, r₁ T 0) * (∑ T, r₁ T 1) + ((∑ T, r₁ T 0) + a) * ((∑ T, r₁ T 1) + b)) * r +
        ((∑ T, r₁ T 0) + a) * ((∑ T, r₁ T 1) + b) * r ^ 2 with hvals
  have hv : ∀ k < 3, IsShamir K (fun i => (fun k => match k with
      | 0 => wa i + r * (wa i + A i 0)
      | 1 => wb i + r * (wb i + B i 0)
      | _ => conv K (localContext i) (fun T k => if i ∈ C.holders T ∧ k < 2 then Z₂ T k else 0) 0 +
          (D i + conv K (localContext i) (fun T k => if i ∈ C.holders T ∧ k < 2 then Z₂ T k else 0) 0 +
            conv K (localContext i) (fun T k => if i ∈ C.holders T ∧ k < 2 then Z₂ T k else 0) 1) * r +
          conv K (localContext i) (fun T k => if i ∈ C.holders T ∧ k < 2 then Z₂ T k else 0) 1 * r ^ 2 : ℕ → E) k)
      (vals k) := by
    intro k hk
    interval_cases k
    · exact (hwa.add ((hwa.add hA).mul_left r)).congr (fun i => rfl) rfl
    · exact (hwb.add ((hwb.add hB).mul_left r)).congr (fun i => rfl) rfl
    · have h0 := hq 0 (by norm_num)
      have h1 := hq 1 (by norm_num)
      refine ((h0.add (((hD.add h0).add h1).mul_right r)).add (h1.mul_right (r ^ 2))).congr (fun i => rfl) ?_
      rw [hq0, hq1]; rfl
  have hfinal : vals 0 * vals 1 = vals 2 := by
    have two : (2 : E) = 0 := CharTwo.two_eq_zero
    simp only [hvals]
    linear_combination (-(a * b * r)) * two
  refine openSh_step prims K F reply fuel _ vals 3 hv _ event s₅ ε ?_
  have hc : ∀ i, openValueN K i _ (fun k => openOut (E := E) k _ 3 i) 0 *
      openValueN K i _ (fun k => openOut (E := E) k _ 3 i) 1 =
      openValueN K i _ (fun k => openOut (E := E) k _ 3 i) 2 := fun i => by
    have hval := (openShN_honest K _ vals 3 hv i).2
    rw [hval 0 (by norm_num), hval 1 (by norm_num), hval 2 (by norm_num), hfinal]
  simp only [require_bind_of (hc _)]
  exact h _ Ks' s₅ hKs' hs₅ hn₅ (hle₁.trans (hle₂.trans (hle₃.trans (hle₄.trans hle₅))))

end RealFinal

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RealHalving

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

theorem real_halving_bound [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (width : ℕ)
    (hwidth : 1 ≤ width) :
    ∀ (n j₀ : ℕ), j₀ + n = halvingSteps width → ∀ (A B : C.Party → ℕ → E) (D : C.Party → E) (Av Bv : ℕ → E),
      (∀ k, IsShamir K (fun i => A i k) (Av k)) → (∀ k, IsShamir K (fun i => B i k) (Bv k)) →
      IsShamir K D (∑ k ∈ range (halvedLength^[j₀] width), Av k * Bv k) →
      ∀ (hist : C.Party → C.Term → List Bit), HistAgree hist → ∀ (lab tg Lk c : ℕ) (Ks : Finset HashOutput),
      Lk ≤ lab → Ks.card ≤ c → ∀ (s : HashCache C), NoMpc s → CacheOK Ks Lk s → ∀ (fuel : ℕ)
      (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop) (ε : ℝ≥0∞),
      (∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
        Ks'.card ≤ c + n + 1 → CacheOK Ks' (lab + 2 * n + 4) s' → NoMpc s' → s ≤ s' →
        Pr[event | (simulateQ (localAnswer prims)
          (honestStart (fun i => g i ⟨hist' i, lab + 2 * n + 4, tg⟩) >>= honestRounds F reply fuel)).run' s'] ≤ ε) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => ((List.range' j₀ n).foldlM (halvingStep K (prssCtx keys kT kP i)
          (realCheckGadgets K (prssCtx keys kT kP i)) width) (A i, B i, D i)).run ⟨hist i, lab, tg⟩ >>= fun x =>
            (finalStep K (prssCtx keys kT kP i) (realCheckGadgets K (prssCtx keys kT kP i)) x.1).run x.2 >>=
              fun p => g i p.2) >>= honestRounds F reply (fuel + 2 * n + 4))).run' s] ≤ chalErr E c (n + 1) + ε := by
  intro n
  induction n with
  | zero =>
    intro j₀ hj A B D Av Bv hA hB hD hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event ε h
    simp only [List.range'_zero, List.foldlM_nil, StateT.run_pure, pure_bind, Nat.mul_zero, Nat.add_zero]
    rw [Nat.add_zero] at hj
    subst hj
    rw [iterate_halvingSteps width hwidth, Finset.sum_range_one] at hD
    refine (real_final_bound prims K keys kT kP F reply fuel A B D (Av 0) (Bv 0) (hA 0) (hB 0) hD hist hh lab tg g
      event s hn Ks Lk hLk hs ε fun hist' Ks' s' h1 h2 h3 h4 => h hist' Ks' s' (by omega) h2 h3 h4).trans ?_
    simp only [chalErr, zero_add, Finset.sum_range_one, Nat.add_zero]
    gcongr
  | succ n ih =>
    intro j₀ hj A B D Av Bv hA hB hD hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event ε h
    haveI := charP_two (E := E)
    rw [List.range'_succ, show fuel + 2 * (n + 1) + 4 = (fuel + 2 * n + 5) + 1 by ring]
    simp only [List.foldlM_cons, halvingStep, bind_assoc, pure_bind, StateT.run_bind]
    set ℓ := halvedLength^[j₀] width with hℓ
    set half := halvedLength ℓ with hhalf
    let hiv := fun (v : ℕ → E) k => if k + half < ℓ then v (k + half) else 0
    refine extendMult_step' prims K keys kT kP F reply (fuel + 2 * n + 5) (fun i => [.shamir (A i) (B i) half,
      .shamir (fun k => A i k + hiv (A i) k) (fun k => B i k + hiv (B i) k) half]) 2 (fun _ => rfl) _ lab
      (fun _ => rfl) _ event s hn _ fun Z₁ hZ₁ s₁ hn₁ hle₁ hfr₁ => ?_
    dsimp only
    have hs₁ := cacheOK_of_frame hs hfr₁
    rw [chalErr_succ]
    have hKc : (Ks.card : ℝ≥0∞) / 2 ^ 256 ≤ c / 2 ^ 256 := by gcongr
    refine le_trans (challenge_step' prims K keys kT kP F reply (fuel + 2 * n + 4) _ (lab + 1) tg (by intro; rfl)
      (by intro; rfl) _ event s₁ hn₁ Ks Lk (by omega) hs₁ (chalErr E (c + 1) (n + 1) + ε) ?_) ?_
    swap
    · rw [← add_assoc]
      gcongr
    intro r Ks₂ s₂ hKs₂ hs₂ hn₂ hle₂
    dsimp only [nextLabel]
    have hhi : ∀ (f : C.Party → ℕ → E) (a : ℕ → E), (∀ k, IsShamir K (fun i => f i k) (a k)) →
        ∀ k, IsShamir K (fun i => hiv (f i) k) (hiv a k) := fun f a hf k => (hf (k + half)).ite K _
    have hfold : ∀ (f : C.Party → ℕ → E) (a : ℕ → E), (∀ k, IsShamir K (fun i => f i k) (a k)) →
        ∀ k, IsShamir K (fun i => f i k + r * (f i k + hiv (f i) k)) (a k + r * (a k + hiv a k)) :=
      fun f a hf k => (hf k).add (((hf k).add (hhi f a hf k)).mul_left r)
    have hsum : ∀ (f : C.Party → ℕ → E) (a : ℕ → E), (∀ k, IsShamir K (fun i => f i k) (a k)) →
        ∀ k, IsShamir K (fun i => f i k + hiv (f i) k) (a k + hiv a k) :=
      fun f a hf k => (hf k).add (hhi f a hf k)
    have hq : ∀ k < 2, IsShamir K (fun i => conv K (localContext i)
        (fun T g => if i ∈ C.holders T ∧ g < 2 then Z₁ T g else 0) k) (∑ T, Z₁ T k) := fun k hk =>
      (isShamir_conv Z₁ k).congr (fun i => (conv_congr i _ _ k fun T hT => by simp [hT, hk]).symm) rfl
    have hq0 : ∑ T, Z₁ T 0 = ∑ k ∈ range half, Av k * Bv k := by
      rw [hZ₁ 0]
      simp only [extendMultShare, List.getElem?_cons_zero, productShare, mulSh, localContext]
      exact sum_lagrangeAll_shamir_sum K hA hB half
    have hq1 : ∑ T, Z₁ T 1 = ∑ k ∈ range half, (Av k + hiv Av k) * (Bv k + hiv Bv k) := by
      rw [hZ₁ 1]
      simp only [extendMultShare, List.getElem?_cons_succ, List.getElem?_cons_zero, productShare, mulSh,
        localContext]
      exact sum_lagrangeAll_shamir_sum K (hsum A Av hA) (hsum B Bv hB) half
    simp only [conv_prssCtx]
    refine ih (j₀ + 1) (by omega) _ _ _ (fun k => Av k + r * (Av k + hiv Av k))
      (fun k => Bv k + r * (Bv k + hiv Bv k)) (hfold A Av hA) (hfold B Bv hB) ?_ _
      (histAgree_record K hist hh _ Z₁ 2 fun i T g hi hg => by simp [hi, hg]) (lab + 1 + 1) tg (lab + 1 + 1)
      (c + 1) Ks₂ le_rfl (by omega) s₂ hn₂ hs₂ fuel g event ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
    · have h0 := hq 0 (by norm_num)
      have h1 := hq 1 (by norm_num)
      refine ((h0.add ((hD.add h1).mul_right r)).add (h1.mul_right (r ^ 2))).congr (fun i => rfl) ?_
      rw [hq0, hq1, Function.iterate_succ_apply', ← hℓ, ← hhalf, sum_range_halving_fold, sum_range_padded Av Bv ℓ]
    · have hlab : lab + 1 + 1 + 2 * n + 4 = lab + 2 * (n + 1) + 4 := by ring
      rw [hlab] at h2 ⊢
      exact h hist' Ks' s' (by omega) h2 h3 (hle₁.trans (hle₂.trans h4))

end RealHalving

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RealSlice

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

theorem real_slice_bound [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (τ : List E) (count : ℕ)
    (hτ : ∀ b < sliceBits, τ.getD b 0 ≠ 0) (hwidth : 0 < sliceWidth count) :
    ∀ (n j₀ : ℕ), j₀ + n = sliceBits → ∀ (xs ys : C.Party → Shares C E) (D : C.Party → E) (XS YS : Shares C E),
      (∀ i T, i ∈ C.holders T → xs i T = XS T ∧ ys i T = YS T) →
      IsShamir K D (∑ k ∈ range (sliceWidth count * 2 ^ (sliceBits - j₀)),
        coinProduct τ 0 (sliceBits - j₀) (k / sliceWidth count) * (∑ T, XS T k) * ∑ T, YS T k) →
      ∀ (hist : C.Party → C.Term → List Bit), HistAgree hist → ∀ (lab tg Lk c : ℕ) (Ks : Finset HashOutput),
      Lk ≤ lab → Ks.card ≤ c → ∀ (s : HashCache C), NoMpc s → CacheOK Ks Lk s → ∀ (fuel : ℕ)
      (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop) (ε : ℝ≥0∞),
      (∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
        Ks'.card ≤ c + n + halvingSteps (sliceWidth count) + 1 →
        CacheOK Ks' (lab + 2 * n + 2 * halvingSteps (sliceWidth count) + 4) s' → NoMpc s' → s ≤ s' →
        Pr[event | (simulateQ (localAnswer prims)
          (honestStart (fun i => g i ⟨hist' i, lab + 2 * n + 2 * halvingSteps (sliceWidth count) + 4, tg⟩) >>=
            honestRounds F reply fuel)).run' s'] ≤ ε) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => ((List.range' j₀ n).foldlM (sliceStep K (prssCtx keys kT kP i)
          (realCheckGadgets K (prssCtx keys kT kP i)) τ count) (xs i, ys i, D i)).run ⟨hist i, lab, tg⟩ >>= fun p =>
            ((List.range (halvingSteps (sliceWidth count))).foldlM (halvingStep K (prssCtx keys kT kP i)
              (realCheckGadgets K (prssCtx keys kT kP i)) (sliceWidth count))
              (conv K (prssCtx keys kT kP i) p.1.1, conv K (prssCtx keys kT kP i) p.1.2.1, p.1.2.2)).run p.2 >>= fun x =>
            (finalStep K (prssCtx keys kT kP i) (realCheckGadgets K (prssCtx keys kT kP i)) x.1).run x.2 >>=
              fun q => g i q.2) >>=
          honestRounds F reply (fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 4))).run' s] ≤
        chalErr E c (n + halvingSteps (sliceWidth count) + 1) + ε := by
  haveI := charP_two (E := E)
  intro n
  induction n with
  | zero =>
    intro j₀ hj xs ys D XS YS hxy hD hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event ε h
    simp only [List.range'_zero, List.foldlM_nil, StateT.run_pure, pure_bind, Nat.mul_zero, Nat.add_zero, zero_add]
    rw [Nat.add_zero] at hj
    subst hj
    rw [List.range_eq_range']
    simp only [conv_prssCtx]
    refine real_halving_bound prims K keys kT kP F reply (sliceWidth count) hwidth _ 0 (by omega) _ _ D
      (fun k => ∑ T, XS T k) (fun k => ∑ T, YS T k) (fun k => (isShamir_conv XS k).congr (fun i =>
        (conv_congr i _ _ k fun T hT => by rw [(hxy i T hT).1]).symm) rfl)
      (fun k => (isShamir_conv YS k).congr (fun i =>
        (conv_congr i _ _ k fun T hT => by rw [(hxy i T hT).2]).symm) rfl) ?_ hist hh lab tg Lk c Ks hLk hKs s hn hs
      fuel g event ε fun hist' Ks' s' h1 h2 h3 h4 => h hist' Ks' s' (by omega) h2 h3 h4
    refine hD.congr (fun i => rfl) ?_
    simp only [Nat.sub_self, pow_zero, mul_one, Function.iterate_zero, id, coinProduct_zero_width, one_mul]
  | succ n ih =>
    intro j₀ hj xs ys D XS YS hxy hD hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event ε h
    rw [List.range'_succ, show fuel + 2 * (n + 1) + 2 * halvingSteps (sliceWidth count) + 4 =
      (fuel + 2 * n + 2 * halvingSteps (sliceWidth count) + 5) + 1 by ring]
    simp only [List.foldlM_cons, sliceStep, bind_assoc, pure_bind, StateT.run_bind]
    set width := sliceWidth count with hwidth_def
    set half := width * 2 ^ (sliceBits - 1 - j₀) with hhalf
    set rest := fun k => coinProduct τ 0 (sliceBits - 1 - j₀) (k / width) with hrest
    refine extendMult_step' prims K keys kT kP F reply (fuel + 2 * n + 2 * halvingSteps width + 5)
      (fun i => [.replicated (fun T k => rest k * xs i T k) (ys i) half,
        .replicated (fun T k => rest k * (xs i T k + xs i T (k + half))) (fun T k => ys i T k + ys i T (k + half)) half])
      2 (fun _ => rfl) _ lab (fun _ => rfl) _ event s hn _ fun Z₁ hZ₁ s₁ hn₁ hle₁ hfr₁ => ?_
    dsimp only
    have hs₁ := cacheOK_of_frame hs hfr₁
    rw [show n + 1 + halvingSteps width + 1 = (n + halvingSteps width + 1) + 1 by ring, chalErr_succ]
    have hKc : (Ks.card : ℝ≥0∞) / 2 ^ 256 ≤ c / 2 ^ 256 := by gcongr
    refine le_trans (challenge_step' prims K keys kT kP F reply (fuel + 2 * n + 2 * halvingSteps width + 4) _
      (lab + 1) tg (by intro; rfl) (by intro; rfl) _ event s₁ hn₁ Ks Lk (by omega) hs₁
      (chalErr E (c + 1) (n + halvingSteps width + 1) + ε) ?_) ?_
    swap
    · rw [← add_assoc]
      gcongr
    intro r Ks₂ s₂ hKs₂ hs₂ hn₂ hle₂
    dsimp only [nextLabel]
    have hw : sliceBits - 1 - j₀ = n := by omega
    set cc := τ.getD (sliceBits - 1 - j₀) 0 with hcc
    have hc : cc ≠ 0 := hτ _ (by omega)
    let Xv := fun k => ∑ T, XS T k
    let Yv := fun k => ∑ T, YS T k
    have hq : ∀ k < 2, IsShamir K (fun i => conv K (localContext i)
        (fun T g => if i ∈ C.holders T ∧ g < 2 then Z₁ T g else 0) k) (∑ T, Z₁ T k) := fun k hk =>
      (isShamir_conv Z₁ k).congr (fun i => (conv_congr i _ _ k fun T hT => by simp [hT, hk]).symm) rfl
    have hq0 : ∑ T, Z₁ T 0 = ∑ k ∈ range half, rest k * Xv k * Yv k := by
      rw [hZ₁ 0]
      simp only [extendMultShare, List.getElem?_cons_zero]
      rw [sum_productShare_replicated K _ _ (fun T k => rest k * XS T k) YS half
        (fun i T hT => by funext k; rw [(hxy i T hT).1]) (fun i T hT => (hxy i T hT).2)]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Xv, Yv, ← Finset.mul_sum]
    have hq1 : ∑ T, Z₁ T 1 = ∑ k ∈ range half, rest k * (Xv k + Xv (k + half)) * (Yv k + Yv (k + half)) := by
      rw [hZ₁ 1]
      simp only [extendMultShare, List.getElem?_cons_succ, List.getElem?_cons_zero]
      rw [sum_productShare_replicated K _ _ (fun T k => rest k * (XS T k + XS T (k + half)))
        (fun T k => YS T k + YS T (k + half)) half
        (fun i T hT => by funext k; rw [(hxy i T hT).1]) (fun i T hT => by funext k; rw [(hxy i T hT).2])]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Xv, Yv, ← Finset.mul_sum, Finset.sum_add_distrib]
    have hsplit := slice_sum_split τ width (sliceBits - 1 - j₀) hwidth Xv Yv
    rw [show sliceBits - 1 - j₀ + 1 = sliceBits - j₀ by omega] at hsplit
    simp only [conv_prssCtx]
    refine ih (j₀ + 1) (by omega) _ _ _ (fun T k => XS T k + r * (XS T k + XS T (k + half)))
      (fun T k => YS T k + r * (YS T k + YS T (k + half)))
      (fun i T hT => ⟨by funext k; rw [(hxy i T hT).1], by funext k; rw [(hxy i T hT).2]⟩) ?_ _
      (histAgree_record K hist hh _ Z₁ 2 fun i T g hi hg => by simp [hi, hg]) (lab + 1 + 1) tg (lab + 1 + 1)
      (c + 1) Ks₂ le_rfl (by omega) s₂ hn₂ hs₂ fuel g event ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
    · have h0 := hq 0 (by norm_num)
      have h1 := hq 1 (by norm_num)
      refine (((h0.mul_left (1 + r)).add (((hD.add h0).div cc).mul_left r)).add (h1.mul_left (r * (1 + r)))).congr
        (fun i => rfl) ?_
      rw [hq0, hq1, show sliceBits - (j₀ + 1) = sliceBits - 1 - j₀ by omega]
      rw [sum_range_slice_fold rest Xv Yv half r cc _ hc hsplit]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Xv, Yv, Finset.sum_add_distrib, ← Finset.mul_sum]
      rfl
    · have hlab : lab + 1 + 1 + 2 * n + 2 * halvingSteps width + 4 =
          lab + 2 * (n + 1) + 2 * halvingSteps width + 4 := by ring
      rw [hlab] at h2 ⊢
      exact h hist' Ks' s' (by omega) h2 h3 (hle₁.trans (hle₂.trans h4))

end RealSlice

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RealCheck

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

theorem tau_split {ι : Type} {G : OracleSpec ι} {β : Type} (ctx : Context C) (d : ℕ) (st : RunState C)
    (f : List E × RunState C → PartyM C E G β) :
    ((coinKey K (realCheckGadgets (G := G) K ctx)).run st >>= fun x => (expand K x.1 d).run x.2 >>= f) =
      (coinKey K (realCheckGadgets K ctx) >>= fun key => expand K key d).run st >>= f := by
  rw [StateT.run_bind, bind_assoc]

/-- An honest real check of correct tuples. It aborts only on a coin. -/
theorem real_check_bound [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R)
    (tuples : C.Party → List (Tuple C)) (cnt : ℕ) (hcnt : ∀ i, ((tuples i).map (·.count)).sum = cnt) (hpos : cnt ≠ 0)
    (LX LY LZ : Shares C E)
    (hag : ∀ i T, i ∈ C.holders T → liftedPart (E := E) (tuples i) (·.x) T = LX T ∧
      liftedPart (E := E) (tuples i) (·.y) T = LY T ∧ liftedPart (E := E) (tuples i) (·.z) T = LZ T)
    (hprod : ∀ k, ∑ T, LZ T k = (∑ T, LX T k) * ∑ T, LY T k)
    (hist : C.Party → C.Term → List Bit) (hh : HistAgree hist) (lab tg Lk c : ℕ) (Ks : Finset HashOutput)
    (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c) (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop) (ε : ℝ≥0∞)
    (h : ∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ c + halvings cnt + 2 → CacheOK Ks' (lab + 2 * halvings cnt + 5) s' → NoMpc s' → s ≤ s' →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ⟨hist' i, lab + 2 * halvings cnt + 5, tg⟩) >>=
          honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => (check K (prssCtx keys kT kP i) (realCheckGadgets K (prssCtx keys kT kP i))
        (tuples i)).run ⟨hist i, lab, tg⟩ >>= fun p => g i p.2) >>=
          honestRounds F reply (fuel + 2 * halvings cnt + 5))).run' s] ≤
      (Ks.card / 2 ^ 256 + sliceBits / Fintype.card E) + (chalErr E (c + 1) (halvings cnt + 1) + ε) := by
  haveI := charP_two (E := E)
  have hne : ∀ i, ((tuples i).map (·.count)).sum ≠ 0 := fun i => by rw [hcnt i]; exact hpos
  simp only [check_eq _ _ _ _ (hne _), hcnt, StateT.run_bind, bind_assoc]
  rw [show fuel + 2 * halvings cnt + 5 = (fuel + 2 * halvings cnt + 4) + 1 by ring]
  simp only [tau_split]
  refine tau_step' prims K keys kT kP F reply (fuel + 2 * halvings cnt + 4) (coins cnt) (sliceBits_le_coins hpos) _
    lab tg (by intro; rfl) (by intro; rfl) _ event s hn Ks Lk hLk hs _ ?_
  intro τ hτ Ks₁ s₁ hKs₁ hs₁ hn₁ hle₁
  dsimp only [nextLabel]
  simp only [StateT.run_lift, require_bind_of hτ, pure_bind]
  have hR : halvings cnt = sliceBits + halvingSteps (sliceWidth cnt) := rfl
  rw [show List.range sliceBits = List.range' 0 sliceBits from List.range_eq_range',
    show halvings cnt - sliceBits = halvingSteps (sliceWidth cnt) by omega,
    show fuel + 2 * halvings cnt + 4 = fuel + 2 * sliceBits + 2 * halvingSteps (sliceWidth cnt) + 4 by omega,
    show halvings cnt + 1 = sliceBits + halvingSteps (sliceWidth cnt) + 1 by omega]
  refine real_slice_bound prims K keys kT kP F reply τ cnt hτ (sliceWidth_pos hpos) sliceBits 0 (by simp) _ _ _
    (fun T k => wordWeightOf K τ cnt k * LX T k) LY
    (fun i T hT => ⟨by funext k; simp only [(hag i T hT).1], (hag i T hT).2.1⟩) ?_ hist hh (lab + 1) tg (lab + 1)
    (c + 1) Ks₁ le_rfl (by omega) s₁ hn₁ hs₁ fuel g event ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
  · refine (isShamir_conv (claimOf K τ cnt LZ) 0).congr (fun i => (conv_congr i _ _ 0 fun T hT => by
      simp only [claimOf, (hag i T hT).2.2]).symm) ?_
    simp only [claimOf, Nat.sub_zero]
    rw [Finset.sum_comm, mul_comm (sliceWidth cnt)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.mul_sum, hprod k, ← Finset.mul_sum]
    simp only [sliceOf]
    ring
  · have hlab : lab + 1 + 2 * sliceBits + 2 * halvingSteps (sliceWidth cnt) + 4 = lab + 2 * halvings cnt + 5 := by
      omega
    rw [hlab] at h2 ⊢
    exact h hist' Ks' s' (by omega) h2 h3 (hle₁.trans h4)

end RealCheck

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Collector

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) {ι : Type} {G : OracleSpec ι}

/-- The running values after `record` of a reshare in `mode` at operator `i`. -/
def recordMode (mode : ReshareMode) (i : C.Party) (h : C.Term → List Bit) (z : Shares C Bit) (count : ℕ) :
    C.Term → List Bit := fun T =>
  if i ∈ C.holders T then
    h T ++ ((List.range count).filter fun g => (filler K mode T g).isSome).flatMap ((bitCodec (C := C) (E := E)).toBits ∘ z T)
  else h T

theorem reshareCollector_run (ctx : Context C) (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v : ℕ → Bit)
    (count : ℕ) (st : RunState C) :
    (reshareCollector (G := G) K ctx (r, Zs) v count).run st =
      exchange (colOut1 K ctx.self r Zs v count) >>= fun inbox =>
        exchange (colOut2 K ctx.self r Zs v count inbox) >>= fun forward =>
          pure (colZ K ctx.self r Zs v count inbox forward,
            ⟨recordMode K .collector ctx.self st.history (colZ K ctx.self r Zs v count inbox forward) count,
              st.label, st.tag⟩) := by
  unfold reshareCollector
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  refine congrArg (_ >>= ·) (funext fun inbox => ?_)
  refine congrArg (_ >>= ·) (funext fun forward => ?_)
  simp only [record, StateT.run_modify, StateT.run_pure, pure_bind]
  rfl

theorem getD_map_idxOf' {l : List ℕ} {g : ℕ} (hg : g ∈ l) (f : ℕ → Bit) : (l.map f).getD (l.idxOf g) 0 = f g := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hg)]
  simp [List.getElem_idxOf]

variable (rr : C.Term → ℕ → Bit) (zz : C.Pair → ℕ → Bit) (v : C.Party → ℕ → Bit)

/-- The sharing that an honest collector reshare gives, before the restriction to the held terms. -/
def colShare (T : C.Term) (g : ℕ) : Bit :=
  if T = (K.collector g).1 then ∑ j, colU K j (honestR rr j) (honestZ zz j) (v j) g else rr T g

theorem sum_colShare (g : ℕ) : ∑ T, colShare K rr zz v T g = ∑ i, v i g := by
  set star := (K.collector g).1
  have hpairs : ∑ j : C.Party, ∑ k ∈ Finset.univ.erase j, honestZ zz j k g = 0 := by
    have := sum_pairs_eq_zero (R := Bit) (C := C) Finset.univ fun p => zz p g
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    rw [dif_pos rfl, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    simp only [honestZ, dif_neg hki, dif_neg (Ne.symm hki)]
  have hown : ∑ j : C.Party, ∑ T ∈ Finset.univ.filter (fun T => T ≠ star ∧ K.owner T = j), honestR rr j T g =
      ∑ T ∈ Finset.univ.filter (· ≠ star), rr T g := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (· ≠ star))
      (t := Finset.univ) (g := K.owner) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.filter_filter]
    refine Finset.sum_congr rfl fun T hT => ?_
    have hT' := (Finset.mem_filter.mp hT).2
    simp only [honestR, if_pos (hT'.2 ▸ K.owner_held T)]
  have hu : ∑ j, colU K j (honestR rr j) (honestZ zz j) (v j) g =
      ∑ i, v i g + ∑ T ∈ Finset.univ.filter (· ≠ star), rr T g := by
    simp only [colU, Finset.sum_add_distrib, hpairs, add_zero]
    exact congrArg (_ + ·) hown
  unfold colShare
  rw [Finset.sum_ite, Finset.filter_eq' Finset.univ star, if_pos (Finset.mem_univ _), Finset.sum_singleton, hu,
    add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- Each honest operator gets its held terms of `colShare`. -/
theorem colZ_honest (count : ℕ) (i : C.Party) (T : C.Term) (g : ℕ) :
    colZ K i (honestR rr i) (honestZ zz i) (v i) count
        (fun k => colOut1 K k (honestR rr k) (honestZ zz k) (v k) count i)
        (fun k => colOut2 K k (honestR rr k) (honestZ zz k) (v k) count
          (fun k' => colOut1 K k' (honestR rr k') (honestZ zz k') (v k') count k) i) T g =
      if i ∈ C.holders T ∧ g < count then colShare K rr zz v T g else 0 := by
  have hsum : ∀ κ g, g < count → (K.collector g).2 = κ →
      colSum K κ (honestR rr κ) (honestZ zz κ) (v κ) count
        (fun k' => colOut1 K k' (honestR rr k') (honestZ zz k') (v k') count κ) g =
        ∑ j, colU K j (honestR rr j) (honestZ zz j) (v j) g := by
    intro κ g hg hκ
    have hmem : g ∈ collectedBy K count κ := List.mem_filter.2 ⟨List.mem_range.2 hg, by simp [hκ]⟩
    unfold colSum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ κ)]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjκ : j ≠ κ := Finset.ne_of_mem_erase hj
    simp only [colOut1, ne_eq, Ne.symm hjκ, not_false_eq_true, if_true, Msg.bitAt]
    exact getD_map_idxOf' hmem _
  unfold colZ
  by_cases hiT : i ∈ C.holders T
  · by_cases hg : g < count
    · have h1 : ¬ (i ∉ C.holders T ∨ count ≤ g) := by simp [hiT]; omega
      rw [if_neg h1, if_pos (show i ∈ C.holders T ∧ g < count from ⟨hiT, hg⟩)]
      unfold colShare
      by_cases hT : T = (K.collector g).1
      · rw [if_pos hT, if_pos hT]
        by_cases hκ : (K.collector g).2 = i
        · rw [if_pos hκ, hsum i g hg hκ]
        · rw [if_neg hκ]
          have hmem : g ∈ forwardedTo K count (K.collector g).2 i :=
            List.mem_filter.2 ⟨List.mem_filter.2 ⟨List.mem_range.2 hg, by simp⟩, by simpa [← hT] using hiT⟩
          simp only [colOut2, ne_eq, Ne.symm hκ, not_false_eq_true, if_true, Msg.bitAt]
          rw [getD_map_idxOf' hmem, hsum _ g hg rfl]
      · rw [if_neg hT, if_neg hT]
        simp [honestR, hiT]
    · rw [if_pos (Or.inr (by omega)), if_neg (by tauto)]
  · rw [if_pos (Or.inl hiT), if_neg (by tauto)]

theorem isAbort_colOut1 (i : C.Party) (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v' : ℕ → Bit) (count : ℕ)
    (j : C.Party) : Msg.isAbort (colOut1 (E := E) K i r Zs v' count j) = false := by
  unfold colOut1; split_ifs <;> rfl

theorem isAbort_colOut2 (i : C.Party) (r : Shares C Bit) (Zs : C.Party → ℕ → Bit) (v' : ℕ → Bit) (count : ℕ)
    (inbox : Mail C E) (j : C.Party) : Msg.isAbort (colOut2 K i r Zs v' count inbox j) = false := by
  unfold colOut2; split_ifs <;> rfl

end Collector

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section MultSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

theorem realMult_run {ι : Type} {G : OracleSpec ι} (ctx : Context C) (mode : ReshareMode) (x y : Shares C Bit)
    (count : ℕ) (st : RunState C) {β : Type} (f : Shares C Bit × RunState C → PartyM C E G β) :
    ((realRunGadgets K ctx mode).mult x y count).run st >>= f =
      oracleStep (prssDraw ctx (bitCodec (E := E)) st.label 0 count) >>= fun o =>
        (reshareWith K ctx mode o (mulRep K ctx x y) count).run (nextLabel st) >>= f := by
  simp only [realRunGadgets]
  rw [prssRandomness_run, bind_assoc]

theorem realRerand_run {ι : Type} {G : OracleSpec ι} (ctx : Context C) (mode : ReshareMode) (v : Shares C Bit)
    (count : ℕ) (st : RunState C) {β : Type} (f : Shares C Bit × RunState C → PartyM C E G β) :
    ((realRunGadgets K ctx mode).rerand v count).run st >>= f =
      oracleStep (prssDraw ctx (bitCodec (E := E)) st.label 0 count) >>= fun o =>
        (reshare K ctx (bitCodec (E := E)) o (ownerSum K ctx v) count).run (nextLabel st) >>= f := by
  simp only [realRunGadgets]
  rw [prssRandomness_run, bind_assoc]

/-- An honest real multiplication in `mode`. Every operator continues with its held terms of one
sharing of the sum of the `MulRep` shares. -/
theorem mult_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (mode : ReshareMode)
    (X Y : C.Party → Shares C Bit) (n : ℕ) (st : C.Party → RunState C) (lab : ℕ) (hL : ∀ i, (st i).label = lab)
    (g : C.Party → Shares C Bit × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (z : Shares C Bit), (∀ k, ∑ T, z T k = ∑ i, mulRep K (localContext i) (X i) (Y i) k) →
      ∀ (s' : HashCache C), NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ((fun T k => if i ∈ C.holders T ∧ k < n then z T k else 0),
          ⟨recordMode K mode i (st i).history (fun T k => if i ∈ C.holders T ∧ k < n then z T k else 0) n,
            lab + 1, (st i).tag⟩)) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => ((realRunGadgets K (prssCtx keys kT kP i) mode).mult (X i) (Y i) n).run (st i) >>=
        g i) >>= honestRounds F reply (fuel + mode.rounds))).run' s] ≤ ε := by
  simp only [realMult_run, hL]
  refine draw_step prims F reply _ _ (fun i => FrameR.prssDraw _ _ FrameR.bitDraw _ _ _) _ event s hn ε
    fun h₀ s' _ _ hn' hle hfr => ?_
  simp only [D_prssDraw]
  set rr := fun T => D prims h₀ ((bitCodec (C := C) (E := E)).draw (.term T) (kT T) lab 0 n)
  set zz := fun p => D prims h₀ ((bitCodec (C := C) (E := E)).draw (.pair p) (kP p) lab 0 n)
  cases mode with
  | peer =>
    simp only [reshareWith, reshare_run, bind_assoc, pure_bind, ReshareMode.rounds]
    rw [honestRounds_exchange F reply fuel (fun i => reshareOut K (prssCtx keys kT kP i) bitCodec
      (honestR rr i) (honestZ zz i) (mulRep K (prssCtx keys kT kP i) (X i) (Y i)) n) _
      fun k j => isAbort_reshareOut K _ bitCodec_roundTrip _ _ _ _ _ _]
    set Z := honestShare K (prssCtx keys kT kP) rr zz (fun i => mulRep K (prssCtx keys kT kP i) (X i) (Y i))
    have hz : ∀ i, reshareZ K (prssCtx keys kT kP i) bitCodec (honestR rr i) (honestZ zz i)
        (mulRep K (prssCtx keys kT kP i) (X i) (Y i)) n
          (fun k => reshareOut K (prssCtx keys kT kP k) bitCodec (honestR rr k) (honestZ zz k)
            (mulRep K (prssCtx keys kT kP k) (X k) (Y k)) n i) =
        fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0 := fun i => funext fun T => funext fun k =>
      reshareZ_honest K (prssCtx keys kT kP) rr zz _ bitCodec bitCodec_roundTrip (fun _ => rfl) n i T k
    simp only [hz, nextLabel, hL, prssCtx_self]
    exact h Z (fun k => sum_honestShare K (prssCtx keys kT kP) rr zz _ (fun _ => rfl) k) s' hn' hle hfr
  | collector =>
    simp only [reshareWith, reshareCollector_run, bind_assoc, pure_bind, ReshareMode.rounds, prssCtx_self]
    rw [show fuel + 2 = (fuel + 1) + 1 from rfl]
    rw [honestRounds_exchange F reply (fuel + 1) (fun i => colOut1 K i (honestR rr i) (honestZ zz i)
      (mulRep K (prssCtx keys kT kP i) (X i) (Y i)) n) _ fun k j => isAbort_colOut1 K _ _ _ _ _ _]
    rw [honestRounds_exchange F reply fuel (fun i => colOut2 K i (honestR rr i) (honestZ zz i)
      (mulRep K (prssCtx keys kT kP i) (X i) (Y i)) n
        (fun k' => colOut1 K k' (honestR rr k') (honestZ zz k') (mulRep K (prssCtx keys kT kP k') (X k') (Y k')) n i))
      _ fun k j => isAbort_colOut2 K _ _ _ _ _ _ _]
    have hz : ∀ j, colZ K j (honestR rr j) (honestZ zz j) (mulRep K (prssCtx keys kT kP j) (X j) (Y j)) n
        (fun k => colOut1 K k (honestR rr k) (honestZ zz k) (mulRep K (prssCtx keys kT kP k) (X k) (Y k)) n j)
        (fun k => colOut2 K k (honestR rr k) (honestZ zz k) (mulRep K (prssCtx keys kT kP k) (X k) (Y k)) n
          (fun k' => colOut1 K k' (honestR rr k') (honestZ zz k') (mulRep K (prssCtx keys kT kP k') (X k') (Y k')) n k)
          j) = fun T k => if j ∈ C.holders T ∧ k < n then
            colShare K rr zz (fun i => mulRep K (prssCtx keys kT kP i) (X i) (Y i)) T k else 0 :=
      fun j => funext fun T => funext fun k =>
        colZ_honest K rr zz (fun i => mulRep K (prssCtx keys kT kP i) (X i) (Y i)) n j T k
    simp only [hz, nextLabel, hL]
    exact h _ (fun k => sum_colShare K rr zz _ k) s' hn' hle hfr

end MultSteps

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal

noncomputable section

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section ReplaySteps

variable {C : Committee} {E : Type} {I O L R α : Type} (prims : Primitives)

/-- A run of a computation of `H` and `PRG` gives the value under every `H` that agrees with a later
cache. -/
theorem replay_D {β : Type} {n : ℕ} (oa : Fin n → OracleComp (RoSpec C) β) (s : HashCache C)
    (z) (hz : z ∈ support ((simulateQ (localAnswer prims)
      (Concrete.sequenceFin fun i => liftComp (oa i) (LocalSpec C))).run s))
    (h : Query C → HashOutput) (hg : Good prims h) (s' : HashCache C) (hle : z.2 ≤ s') (ha : Agrees h s') :
    ∀ i, z.1 i = D prims h (oa i) := by
  obtain ⟨-, -, hsupp⟩ := localRun_support _ s z hz
  have := hsupp h hg (ha.mono hle)
  rw [simulateQ_sequenceFin] at this
  simp only [simulateQ_fixedLocal_liftComp] at this
  rw [sequenceFin_pure] at this
  simp only [support_pure, Set.mem_singleton_iff] at this
  intro i
  rw [this]

/-- `draw_step` whose continuation knows the values under every later `H`. -/
theorem draw_step2 {β : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (oa : C.Party → OracleComp (RoSpec C) β) (hframe : ∀ i, FrameR prims (oa i))
    (g : C.Party → β → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (w : C.Party → β) (s' : HashCache C), (∀ h' s'', Good prims h' → s' ≤ s'' → Agrees h' s'' →
        ∀ i, w i = D prims h' (oa i)) → NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (w i)) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep (oa i) >>= g i) >>= honestRounds F reply fuel)).run' s] ≤ ε := by
  refine probEvent_honest_local prims F reply fuel oa g event s ε fun z hz => ?_
  obtain ⟨hle, hn', -⟩ := localRun_D prims oa s hn z hz
  have hfr := FrameL.sequenceFin (prims := prims) (fun i => liftComp (oa i) (LocalSpec C))
    (fun i => FrameL.liftComp (hframe i)) s z hz
  exact h z.1 z.2 (fun h' s'' hg hle' ha => replay_D prims oa s z hz h' hg s'' hle' ha) hn' hle hfr

end ReplaySteps

section RepSteps

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

theorem FrameR.copyHashes (count : ℕ) (v : Shares C Bit) :
    FrameR prims (C.terms.mapM fun T => ThresholdLeanXmss.hashQuery (C := C) (.copy (vector count (v T)))) :=
  FrameR.mapM _ (fun _ => FrameR.hashQuery (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)) _

theorem isAbort_repOutbox (i : C.Party) (v : Shares C Bit) (count : ℕ) (ds : List HashOutput) (j : C.Party) :
    Msg.isAbort (repOutbox (E := E) K i v count ds j) = false := by
  unfold repOutbox; split_ifs <;> rfl

/-- An honest `OpenRep`. Each operator opens the shared value at the positions below `count`. -/
theorem openRep_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (vr : C.Party → Shares C Bit) (w : Shares C Bit) (count : ℕ)
    (hvr : ∀ i T g, i ∈ C.holders T → g < count → vr i T g = w T g)
    (f : C.Party → (ℕ → Bit) → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (V : C.Party → ℕ → Bit), (∀ i g, g < count → V i g = ∑ T, w T g) →
      ∀ (s' : HashCache C), NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => f i (V i)) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => openRep K (localContext i) (vr i) count >>= f i) >>=
        honestRounds F reply (fuel + 1))).run' s] ≤ ε := by
  simp only [openRep_eq, bind_assoc]
  refine draw_step2 prims F reply (fuel + 1) _ (fun i => FrameR.copyHashes prims count (vr i)) _ event s hn ε
    fun ds s₁ hds hn₁ hle₁ hfr₁ => ?_
  rw [honestRounds_exchange F reply fuel (fun i => repOutbox (E := E) K i (vr i) count (ds i)) _
    fun k j => isAbort_repOutbox K _ _ _ _ _]
  have hcopy : ∀ i T, vector count (repCopy K i (vr i) count (fun k => repOutbox (E := E) K k (vr k) count (ds k) i) T) =
      vector count (w T) := fun i T => vector_congr' _ _ _ fun g hg => openCopy_eq K i _ w vr hvr ds T g hg
  simp only [hcopy]
  refine draw_step2 prims F reply fuel (fun i => C.terms.mapM fun T => hashQuery (C := C) (.copy (vector count (w T))))
    (fun i => FrameR.copyHashes prims count w) _ event s₁ hn₁ ε fun cs s₂ hcs hn₂ hle₂ hfr₂ => ?_
  obtain ⟨h₂, hg₂, ha₂⟩ : ∃ h₂, Good prims h₂ ∧ Agrees h₂ s₂ := ⟨hashOf prims s₂, good_hashOf prims s₂,
    agrees_hashOf prims hn₂⟩
  have hcs' : ∀ i, cs i = C.terms.map fun T => h₂ (.copy (vector count (w T))) := fun i => by
    rw [hcs h₂ s₂ hg₂ le_rfl ha₂ i, D_mapM]; simp [D_hashQuery]
  have hds' : ∀ i, ds i = C.terms.map fun T => h₂ (.copy (vector count (vr i T))) := fun i => by
    rw [hds h₂ s₂ hg₂ hle₂ ha₂ i, D_mapM]; simp [D_hashQuery]
  have hcheck : ∀ i, repCheck K i (fun k => repOutbox (E := E) K k (vr k) count (ds k) i) (cs i) := fun i => by
    rw [hcs' i]
    refine repCheck_honest K i count vr ds (fun T => h₂ (.copy (vector count (w T)))) (fun j => by simp [hds' j])
      fun j T hj => ?_
    rw [hds' j, List.getElem?_map, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem (mem_terms T))]
    simp only [Option.map_some, List.getElem_idxOf]
    rw [vector_congr' count _ _ fun g hg => hvr j T g hj hg]
  simp only [require_bind_of (hcheck _), pure_bind]
  refine h _ (fun i g hg => Finset.sum_congr rfl fun T _ => openCopy_eq K i _ w vr hvr ds T g hg) s₂ hn₂
    (hle₁.trans hle₂) fun q hq => (hfr₂ q hq).trans (hfr₁ q hq)

end RepSteps

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section RerandStep

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

/-- An honest real `Rerand`, a peer reshare of the owner sums. -/
theorem rerand_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (mode : ReshareMode)
    (V : C.Party → Shares C Bit) (n : ℕ) (st : C.Party → RunState C) (lab : ℕ) (hL : ∀ i, (st i).label = lab)
    (g : C.Party → Shares C Bit × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (z : Shares C Bit), (∀ k, ∑ T, z T k = ∑ i, ownerSum K (localContext i) (V i) k) →
      ∀ (s' : HashCache C), NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ((fun T k => if i ∈ C.holders T ∧ k < n then z T k else 0),
          ⟨recordMode K .peer i (st i).history (fun T k => if i ∈ C.holders T ∧ k < n then z T k else 0) n,
            lab + 1, (st i).tag⟩)) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => ((realRunGadgets K (prssCtx keys kT kP i) mode).rerand (V i) n).run (st i) >>=
        g i) >>= honestRounds F reply (fuel + 1))).run' s] ≤ ε := by
  simp only [realRerand_run, hL]
  refine draw_step prims F reply _ _ (fun i => FrameR.prssDraw _ _ FrameR.bitDraw _ _ _) _ event s hn ε
    fun h₀ s' _ _ hn' hle hfr => ?_
  simp only [D_prssDraw]
  set rr := fun T => D prims h₀ ((bitCodec (C := C) (E := E)).draw (.term T) (kT T) lab 0 n)
  set zz := fun p => D prims h₀ ((bitCodec (C := C) (E := E)).draw (.pair p) (kP p) lab 0 n)
  simp only [reshare_run, bind_assoc, pure_bind]
  rw [honestRounds_exchange F reply fuel (fun i => reshareOut K (prssCtx keys kT kP i) bitCodec
    (honestR rr i) (honestZ zz i) (ownerSum K (prssCtx keys kT kP i) (V i)) n) _
    fun k j => isAbort_reshareOut K _ bitCodec_roundTrip _ _ _ _ _ _]
  set Z := honestShare K (prssCtx keys kT kP) rr zz (fun i => ownerSum K (prssCtx keys kT kP i) (V i))
  have hz : ∀ i, reshareZ K (prssCtx keys kT kP i) bitCodec (honestR rr i) (honestZ zz i)
      (ownerSum K (prssCtx keys kT kP i) (V i)) n
        (fun k => reshareOut K (prssCtx keys kT kP k) bitCodec (honestR rr k) (honestZ zz k)
          (ownerSum K (prssCtx keys kT kP k) (V k)) n i) =
      fun T k => if i ∈ C.holders T ∧ k < n then Z T k else 0 := fun i => funext fun T => funext fun k =>
    reshareZ_honest K (prssCtx keys kT kP) rr zz (fun i => ownerSum K (prssCtx keys kT kP i) (V i)) bitCodec
      bitCodec_roundTrip (fun _ => rfl) n i T k
  simp only [hz, nextLabel, hL, prssCtx_self]
  exact h Z (fun k => sum_honestShare K (prssCtx keys kT kP) rr zz
    (fun i => ownerSum K (prssCtx keys kT kP i) (V i)) (fun _ => rfl) k) s' hn' hle hfr

/-- The owner sums of views that agree on the held terms sum to the shared value. -/
theorem sum_ownerSum (Vv : C.Party → Shares C Bit) (W : Shares C Bit) (hV : ∀ i T, i ∈ C.holders T → Vv i T = W T)
    (k : ℕ) : ∑ i, ownerSum K (localContext i) (Vv i) k = shareValue W k := by
  unfold ownerSum shareValue
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ) (g := K.owner)
    (fun _ _ => Finset.mem_univ _) (f := fun T => W T k)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr ?_ fun T hT => ?_
  · ext T; simp [localContext]
  · have hT' : K.owner T = i := by simpa [localContext] using (Finset.mem_filter.mp hT).2
    rw [hV i T (hT' ▸ K.owner_held T)]

end RerandStep

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Lifted

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

theorem liftedPart_nil (part : Tuple C → Shares C Bit) (T : C.Term) (k : ℕ) :
    liftedPart (E := E) [] part T k = 0 := by
  simp [liftedPart]

theorem liftedPart_cons (τ : Tuple C) (Ts : List (Tuple C)) (part : Tuple C → Shares C Bit) (T : C.Term) (k : ℕ) :
    liftedPart (E := E) (τ :: Ts) part T k =
      if k < τ.count then algebraMap Bit E (part τ T k) else liftedPart Ts part T (k - τ.count) := by
  unfold liftedPart
  rw [List.flatMap_cons]
  split_ifs with hk
  · rw [getD_append_of_lt _ _ _ _ (by simp [vector]; exact hk)]
    simp [vector, List.getD_eq_getElem?_getD, hk]
  · rw [getD_append_of_le _ _ _ _ (by simp [vector]; omega)]
    simp [vector]

/-- Tuples that agree at the held terms give the same lifted vectors there. -/
theorem liftedPart_agree' (i : C.Party) : ∀ (vs Ts : List (Tuple C)) (hlen : vs.length = Ts.length),
    (∀ m (hm : m < Ts.length), TupleAgrees i (vs[m]'(by rw [hlen]; exact hm)) Ts[m]) →
    ∀ T, i ∈ C.holders T → liftedPart (E := E) vs (·.x) T = liftedPart Ts (·.x) T ∧
      liftedPart (E := E) vs (·.y) T = liftedPart Ts (·.y) T ∧ liftedPart (E := E) vs (·.z) T = liftedPart Ts (·.z) T
  | [], [], _, _, T, _ => ⟨rfl, rfl, rfl⟩
  | v :: vs, τ :: Ts, hlen, hag, T, hT => by
    have h0 := hag 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    obtain ⟨hxyz, hc, -⟩ := h0
    obtain ⟨hx, hy, hz⟩ := hxyz T hT
    obtain ⟨ihx, ihy, ihz⟩ := liftedPart_agree' i vs Ts (by simpa using hlen)
      (fun m hm => by have := hag (m + 1) (by simpa using hm); simpa [List.getElem_cons_succ] using this) T hT
    refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩ <;>
      simp only [liftedPart_cons, hc, hx, hy, hz, ihx, ihy, ihz]

/-- Products give lifted vectors whose shared values multiply. -/
theorem liftedPart_product : ∀ (Ts : List (Tuple C)), (∀ τ ∈ Ts, IsProduct τ) → ∀ k,
    ∑ T, liftedPart (E := E) Ts (·.z) T k = (∑ T, liftedPart (E := E) Ts (·.x) T k) * ∑ T, liftedPart (E := E) Ts (·.y) T k
  | [], _, k => by simp [liftedPart_nil]
  | τ :: Ts, hp, k => by
    simp only [liftedPart_cons]
    split_ifs with hk
    · have := hp τ (List.mem_cons_self ..) k hk
      unfold shareValue at this
      rw [← map_sum, ← map_sum, ← map_sum, this, map_mul]
    · exact liftedPart_product Ts (fun τ' h => hp τ' (List.mem_cons_of_mem _ h)) _

end Lifted

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

/-- The bound of the aborts of a check of `cnt` tuples, when the cache holds expansions of `kc ≤ c` keys. -/
def checkCost (E : Type) [Fintype E] (c cnt kc : ℕ) : ℝ≥0∞ :=
  if cnt = 0 then 0 else ((kc : ℝ≥0∞) / 2 ^ 256 + sliceBits / Fintype.card E) + chalErr E (c + 1) (halvings cnt + 1)

/-- The coin keys of a check of `cnt` tuples. -/
def checkKeys (cnt : ℕ) : ℕ := if cnt = 0 then 0 else halvings cnt + 2

/-- The rounds and the round labels of a check of `cnt` tuples. -/
def checkLabels (cnt : ℕ) : ℕ := if cnt = 0 then 0 else 2 * halvings cnt + 5

theorem CacheOK.mono_label {C : Committee} {Ks : Finset HashOutput} {L L' : ℕ} {s : HashCache C}
    (h : CacheOK Ks L s) (hL : L ≤ L') : CacheOK Ks L' s := fun q hq =>
  ⟨(h q hq).1, fun tag ρ v hv => by have := (h q hq).2 tag ρ v hv; omega⟩

section CheckAny

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

theorem check_zero_run {ι : Type} {G : OracleSpec ι} (ctx : Context C) (gadgets : CheckGadgets C E G)
    (tuples : List (Tuple C)) (h0 : (tuples.map (·.count)).sum = 0) (st : RunState C) :
    (check K ctx gadgets tuples).run st = pure ((), st) := by
  simp [check, h0]

/-- An honest real check of correct tuples, with no tuple or with some tuples. -/
theorem real_check_any [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R)
    (tuples : C.Party → List (Tuple C)) (cnt : ℕ) (hcnt : ∀ i, ((tuples i).map (·.count)).sum = cnt)
    (LX LY LZ : Shares C E)
    (hag : ∀ i T, i ∈ C.holders T → liftedPart (E := E) (tuples i) (·.x) T = LX T ∧
      liftedPart (E := E) (tuples i) (·.y) T = LY T ∧ liftedPart (E := E) (tuples i) (·.z) T = LZ T)
    (hprod : ∀ k, ∑ T, LZ T k = (∑ T, LX T k) * ∑ T, LY T k)
    (hist : C.Party → C.Term → List Bit) (hh : HistAgree hist) (lab tg Lk c : ℕ) (Ks : Finset HashOutput)
    (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c) (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → Unit × RunState C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop) (ε : ℝ≥0∞)
    (h : ∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ c + checkKeys cnt → CacheOK Ks' (lab + checkLabels cnt) s' → NoMpc s' → s ≤ s' →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i ((), ⟨hist' i, lab + checkLabels cnt, tg⟩)) >>=
          honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => (check K (prssCtx keys kT kP i) (realCheckGadgets K (prssCtx keys kT kP i))
        (tuples i)).run ⟨hist i, lab, tg⟩ >>= g i) >>=
          honestRounds F reply (fuel + checkLabels cnt))).run' s] ≤ checkCost E c cnt Ks.card + ε := by
  by_cases hpos : cnt = 0
  · have h0 : ∀ i, ((tuples i).map (·.count)).sum = 0 := fun i => by rw [hcnt i, hpos]
    simp only [check_zero_run _ _ _ _ (h0 _), pure_bind, checkCost, checkLabels, checkKeys, if_pos hpos, zero_add,
      Nat.add_zero] at h ⊢
    exact h hist Ks s (by omega) (hs.mono_label hLk) hn le_rfl
  · simp only [checkCost, checkLabels, checkKeys, if_neg hpos] at h ⊢
    rw [add_assoc]
    exact real_check_bound prims K keys kT kP F reply tuples cnt hcnt hpos LX LY LZ hag hprod hist hh lab tg Lk c Ks
      hLk hKs s hn hs fuel (fun i st => g i ((), st)) event ε h

end CheckAny

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Tail

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

theorem histAgree_recordMode (mode : ReshareMode) (h : C.Party → C.Term → List Bit) (hh : HistAgree h)
    (zv : C.Party → Shares C Bit) (Z : Shares C Bit) (n : ℕ)
    (hz : ∀ i T g, i ∈ C.holders T → g < n → zv i T g = Z T g) :
    HistAgree (fun i => recordMode K mode i (h i) (zv i) n) := by
  intro T i hi j hj
  simp only [recordMode, if_pos hi, if_pos hj, hh T i hi j hj]
  congr 1
  refine List.flatMap_congr fun g hg => ?_
  have hg' : g < n := List.mem_range.1 (List.mem_filter.1 hg).1
  simp only [Function.comp_apply, hz i T g hi hg', hz j T g hj hg']

theorem openRep_prssCtx {ι : Type} {G : OracleSpec ι} (i : C.Party) :
    openRep (G := G) K (prssCtx keys kT kP i) = openRep K (localContext i) := rfl

theorem map_count_of_agree (i : C.Party) (vs Ts : List (Tuple C)) (hlen : vs.length = Ts.length)
    (hag : ∀ m (hm : m < Ts.length), TupleAgrees i (vs[m]'(by rw [hlen]; exact hm)) Ts[m]) :
    vs.map (·.count) = Ts.map (·.count) :=
  List.ext_getElem (by simp [hlen]) fun m h₁ h₂ => by
    simp only [List.getElem_map]
    exact (hag m (by simpa using h₂)).2.1

/-- The tail of an honest real batch: `Rerand`, the check and `OpenRep`. Every operator gets the
outputs of the circuits. -/
theorem tail_bound [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (mode : ReshareMode)
    (jobs : List Circuit) (x : C.Party → List (C.Term → List Bit))
    (p : C.Party → List (C.Term → List Bit) × List (Tuple C)) (W : List (C.Term → List Bit)) (Ts : List (Tuple C))
    (hinv : LayerInv jobs x (depth jobs) p W Ts) (cnt : ℕ)
    (hcnt : (Ts.map (·.count)).sum + (outputsOf jobs).length = cnt)
    (hist : C.Party → C.Term → List Bit) (hh : HistAgree hist) (lab tg Lk c : ℕ) (Ks : Finset HashOutput)
    (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c) (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → List (List Bit) × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (ε : ℝ≥0∞)
    (h : ∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      Ks'.card ≤ c + checkKeys cnt → CacheOK Ks' (lab + 1 + checkLabels cnt) s' → NoMpc s' → s ≤ s' →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (mainOutputs jobs x, ⟨hist' i, lab + 1 + checkLabels cnt, tg⟩)) >>=
          honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => (tailBody K (realRunGadgets K (prssCtx keys kT kP i) mode) jobs (p i)).run
        ⟨hist i, lab, tg⟩ >>= g i) >>= honestRounds F reply (fuel + 1 + checkLabels cnt + 1))).run' s] ≤
      checkCost E c cnt Ks.card + ε := by
  set n := (outputsOf jobs).length with hn_def
  simp only [tailBody, StateT.run_bind, bind_assoc]
  refine rerand_step prims K keys kT kP F reply (fuel + 1 + checkLabels cnt) mode
    (fun i => outputShares K jobs (p i).1) n _ lab (fun _ => rfl) _ event s hn _ fun z hz s₁ hn₁ hle₁ hfr₁ => ?_
  dsimp only
  have hO : ∀ i T, i ∈ C.holders T → outputShares K jobs (p i).1 T = outputShares K jobs W T :=
    fun i T h => outputShares_congr K jobs _ _ T (hinv.agree i T h)
  have hsum : ∀ k, ∑ T, z T k = shareValue (outputShares K jobs W) k := fun k => by
    rw [hz k, sum_ownerSum K _ _ hO]
  set zv : C.Party → Shares C Bit := fun i T k => if i ∈ C.holders T ∧ k < n then z T k else 0 with hzv
  set w : Shares C Bit := fun T k => if k < n then z T k else 0 with hw
  set Ts' := Ts ++ [(⟨outputShares K jobs W, one K, w, n, .peer⟩ : Tuple C)] with hTs'
  have hlen' : ∀ i, ((p i).2 ++ [(⟨outputShares K jobs (p i).1, one K, zv i, n, .peer⟩ : Tuple C)]).length = Ts'.length :=
    fun i => by simp [hTs', hinv.length_tuples]
  have hag' : ∀ i, ∀ m (hm : m < Ts'.length), TupleAgrees i
      (((p i).2 ++ [(⟨outputShares K jobs (p i).1, one K, zv i, n, .peer⟩ : Tuple C)])[m]'(by rw [hlen' i]; exact hm)) Ts'[m] :=
    fun i => tupleAgrees_append i _ _ _ _ (hinv.length_tuples i) (hinv.agree_tuples i)
      ⟨fun T hT => ⟨hO i T hT, rfl, funext fun g => by simp [hzv, hw, hT]⟩, rfl, rfl⟩
  have hprodTs : ∀ τ ∈ Ts', IsProduct τ := by
    intro τ hτ
    rcases List.mem_append.1 hτ with hτ | hτ
    · exact hinv.product τ hτ
    · simp only [List.mem_singleton] at hτ
      subst hτ
      intro g hg
      rw [shareValue_one, mul_one, ← hsum g]
      simp only [shareValue, hw, if_pos hg]
  have hcnt' : ∀ i, (((p i).2 ++ [(⟨outputShares K jobs (p i).1, one K, zv i, n, .peer⟩ : Tuple C)]).map (·.count)).sum = cnt :=
    fun i => by
      rw [map_count_of_agree i _ _ (hlen' i) (hag' i), hTs', List.map_append, List.sum_append, ← hcnt]
      simp
  have hh₁ := histAgree_recordMode K .peer hist hh zv z n (fun i T g hi hg => by simp [hzv, hi, hg])
  simp only [realRunGadgets]
  rw [show fuel + 1 + checkLabels cnt = (fuel + 1) + checkLabels cnt from rfl]
  refine real_check_any prims K keys kT kP F reply _ cnt hcnt' (liftedPart Ts' (·.x)) (liftedPart Ts' (·.y))
    (liftedPart Ts' (·.z)) (fun i T hT => liftedPart_agree' i _ Ts' (hlen' i) (hag' i) T hT)
    (liftedPart_product Ts' hprodTs) _ hh₁ (lab + 1) tg Lk c Ks (by omega) hKs s₁ hn₁ (cacheOK_of_frame hs hfr₁)
    (fuel + 1) _ event ε fun hist' Ks' s₂ hKs₂ hs₂ hn₂ hle₂ => ?_
  dsimp only
  simp only [StateT.run_lift, bind_assoc, pure_bind, openRep_prssCtx]
  refine openRep_step prims K F reply fuel zv w n (fun i T g hi hg => by simp [hzv, hw, hi, hg]) _ event s₂ hn₂ ε
    fun V hV s₃ hn₃ hle₃ hfr₃ => ?_
  have hA : ∀ i, assemble jobs (V i) = mainOutputs jobs x := fun i =>
    assemble_eq K jobs x p W Ts hinv (V i) fun g hg => by
      rw [hV i g hg, ← hsum g]; simp only [hw]; exact Finset.sum_congr rfl fun T _ => if_pos hg
  simp only [hA]
  have hs₃ : CacheOK Ks' (lab + 1 + checkLabels cnt) s₃ := cacheOK_of_frame hs₂ hfr₃
  exact h hist' Ks' s₃ hKs₂ hs₃ hn₃ (hle₁.trans (hle₂.trans hle₃))

end Tail

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Batch

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E) (keys : C.Party → Keys C) (kT : C.Term → HashOutput)
  (kP : C.Pair → HashOutput)

theorem tupleCount_eq (jobs : List Circuit) :
    tupleCount jobs = ((List.range (depth jobs)).map fun l => (gatesAt jobs l).length).sum + (outputsOf jobs).length := by
  unfold tupleCount
  congr 1
  · congr 1
    refine List.map_congr_left fun l _ => ?_
    rw [gatesAt_eq, length_flatIdx, List.map_map]
    rfl
  · rw [outputsOf_eq, length_flatIdx, List.map_map]
    rfl

theorem layers_bound [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (mode : ReshareMode)
    (jobs : List Circuit) (x : C.Party → List (C.Term → List Bit)) :
    ∀ (k l : ℕ) (p : C.Party → List (C.Term → List Bit) × List (Tuple C)) (W : List (C.Term → List Bit))
      (Ts : List (Tuple C)), l + k = depth jobs → LayerInv jobs x l p W Ts →
      (Ts.map (·.count)).sum = ((List.range l).map fun l' => (gatesAt jobs l').length).sum →
      ∀ (hist : C.Party → C.Term → List Bit), HistAgree hist → ∀ (lab tg Lk c : ℕ) (Ks : Finset HashOutput),
      Lk ≤ lab → Ks.card ≤ c → ∀ (s : HashCache C), NoMpc s → CacheOK Ks Lk s → ∀ (fuel : ℕ)
      (g : C.Party → List (List Bit) × RunState C → PartyM C E (CallSpec I O) α)
      (event : (C.Party → Option α) → Prop) (ε : ℝ≥0∞),
      (∀ (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
        Ks'.card ≤ c + checkKeys (tupleCount jobs) →
        CacheOK Ks' (lab + k + 1 + checkLabels (tupleCount jobs)) s' → NoMpc s' → s ≤ s' →
        Pr[event | (simulateQ (localAnswer prims)
          (honestStart (fun i => g i (mainOutputs jobs x, ⟨hist' i, lab + k + 1 + checkLabels (tupleCount jobs), tg⟩)) >>=
            honestRounds F reply fuel)).run' s'] ≤ ε) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => ((List.range' l k).foldlM (layerBody K (realRunGadgets K (prssCtx keys kT kP i) mode) jobs)
          (p i)).run ⟨hist i, lab, tg⟩ >>= fun q =>
            (tailBody K (realRunGadgets K (prssCtx keys kT kP i) mode) jobs q.1).run q.2 >>= g i) >>=
          honestRounds F reply (fuel + k * mode.rounds + 1 + checkLabels (tupleCount jobs) + 1))).run' s] ≤
        checkCost E c (tupleCount jobs) Ks.card + ε := by
  intro k
  induction k with
  | zero =>
    intro l p W Ts hl hinv hTs hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event ε h
    simp only [List.range'_zero, List.foldlM_nil, StateT.run_pure, pure_bind, zero_mul, Nat.add_zero] at h ⊢
    rw [Nat.add_zero] at hl
    subst hl
    exact tail_bound prims K keys kT kP F reply mode jobs x p W Ts hinv (tupleCount jobs)
      (by rw [hTs, tupleCount_eq]) hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event ε h
  | succ k ih =>
    intro l p W Ts hl hinv hTs hist hh lab tg Lk c Ks hLk hKs s hn hs fuel g event ε h
    rw [List.range'_succ, show fuel + (k + 1) * mode.rounds + 1 + checkLabels (tupleCount jobs) + 1 =
      (fuel + k * mode.rounds + 1 + checkLabels (tupleCount jobs) + 1) + mode.rounds by ring]
    simp only [List.foldlM_cons, layerBody, StateT.run_bind, bind_assoc, StateT.run_pure, pure_bind]
    refine mult_step prims K keys kT kP F reply _ mode (fun i => layerX K jobs l (p i).1)
      (fun i => layerY K jobs l (p i).1) (gatesAt jobs l).length _ lab (fun _ => rfl) _ event s hn _
      fun z hz s₁ hn₁ hle₁ hfr₁ => ?_
    dsimp only
    have hinv' := layerInv_step K jobs x mode l p W Ts hinv z hz
    simp only [realRunGadgets] at hinv' ⊢
    refine ih (l + 1) _ _ _ (by omega) hinv' ?_ _
      (histAgree_recordMode K mode hist hh _ z _ fun i T g hi hg => by simp [hi, hg]) (lab + 1) tg Lk c Ks
      (by omega) hKs s₁ hn₁ (cacheOK_of_frame hs hfr₁) fuel g event ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
    · rw [List.map_append, List.sum_append, hTs, List.range_succ, List.map_append, List.sum_append]
      simp
    · have hlab : lab + 1 + k + 1 + checkLabels (tupleCount jobs) = lab + (k + 1) + 1 + checkLabels (tupleCount jobs) := by
        ring
      rw [hlab] at h2 ⊢
      exact h hist' Ks' s' h1 h2 h3 (hle₁.trans h4)

end Batch

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Bits

theorem getD_bitsOfDigest (d : Digest) (b : ℕ) (hb : b < digestBits) :
    (bitsOfDigest d).getD b 0 = if d.getLsbD b then 1 else 0 := by
  simp [bitsOfDigest, List.getD_eq_getElem?_getD, hb]

theorem bit_xor (a b : Bool) : ((if (a ^^ b) then 1 else 0 : Bit)) = (if a then 1 else 0) + (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem getD_bitsOfDigest_xor (d e : Digest) (b : ℕ) (hb : b < digestBits) :
    (bitsOfDigest (d ^^^ e)).getD b 0 = (bitsOfDigest d).getD b 0 + (bitsOfDigest e).getD b 0 := by
  rw [getD_bitsOfDigest _ _ hb, getD_bitsOfDigest _ _ hb, getD_bitsOfDigest _ _ hb, BitVec.getLsbD_xor, bit_xor]

theorem getD_bitsOfDigest_foldl (ds : List Digest) (acc : Digest) (b : ℕ) (hb : b < digestBits) :
    (bitsOfDigest (ds.foldl (· ^^^ ·) acc)).getD b 0 =
      (bitsOfDigest acc).getD b 0 + (ds.map fun d => (bitsOfDigest d).getD b 0).sum := by
  induction ds generalizing acc with
  | nil => simp
  | cons d ds ih =>
    rw [List.foldl_cons, ih, getD_bitsOfDigest_xor _ _ _ hb, List.map_cons, List.sum_cons, add_assoc]

theorem bitsOfDigest_zero_getD (b : ℕ) : (bitsOfDigest (0 : Digest)).getD b 0 = 0 := by
  by_cases hb : b < digestBits
  · rw [getD_bitsOfDigest _ _ hb]; simp
  · simp [bitsOfDigest, List.getD_eq_getElem?_getD, hb]

/-- An entry of a concatenation of blocks of one length. -/
theorem getD_flatMap_block {β : Type} (f : β → List Bit) (w : ℕ) (hf : ∀ x, (f x).length = w) :
    ∀ (L : List β) (m b : ℕ) (hm : m < L.length), b < w → (L.flatMap f).getD (w * m + b) 0 = (f L[m]).getD b 0
  | [], m, _, hm, _ => absurd hm (by simp)
  | x :: L, m, b, hm, hb => by
    rw [List.flatMap_cons]
    rcases m with _ | m
    · rw [getD_append_of_lt _ _ _ _ (by rw [hf]; omega)]; simp
    · rw [getD_append_of_le _ _ _ _ (by rw [hf]; nlinarith), hf,
        show w * (m + 1) + b - w = w * m + b by rw [Nat.mul_succ]; omega]
      exact getD_flatMap_block f w hf L m b (by simpa using hm) hb

theorem length_flatMap_block {β : Type} (f : β → List Bit) (w : ℕ) (hf : ∀ x, (f x).length = w) (L : List β) :
    (L.flatMap f).length = w * L.length := by
  induction L with
  | nil => simp
  | cons x L ih => simp [hf, ih]; ring

end Bits

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Inputs

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι} (prims : Primitives)

/-- The queries of `inputShares`. -/
def inputQuery (ctx : Context C) (job : Job) : OracleComp (RoSpec C) (C.Term → List Bit) := do
  let terms ← C.terms.mapM fun T =>
    if ctx.self ∈ C.holders T then job.points.flatMapM fun x => bitsOfDigest <$> prf (ctx.keys.seed T) x
    else pure []
  pure fun T => terms.getD (C.terms.idxOf T) []

theorem inputShares_eq (ctx : Context C) (job : Job) :
    (inputShares (E := E) (G := G) ctx job) = oracleStep (inputQuery ctx job) := by
  simp only [inputShares, inputQuery]
  rw [oracleStep_bind]
  simp only [oracleStep_pure]

theorem mapM_oracleStep {α β : Type} (q : α → OracleComp (RoSpec C) β) :
    ∀ l : List α, l.mapM (fun a => (oracleStep (E := E) (G := G) (q a))) = oracleStep (l.mapM q)
  | [] => by simp [oracleStep_pure]
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons, oracleStep_bind, mapM_oracleStep q l]
    refine congrArg (_ >>= ·) (funext fun b => ?_)
    rw [oracleStep_bind]
    simp only [oracleStep_pure]

theorem D_flatMapM {α β : Type} (h : Query C → HashOutput) (f : α → OracleComp (RoSpec C) (List β)) :
    ∀ l : List α, D prims h (l.flatMapM f) = l.flatMap fun a => D prims h (f a)
  | [] => rfl
  | a :: l => by
    rw [List.flatMapM_cons, D_bind, D_bind, D_flatMapM h f l, D_pure, List.flatMap_cons]

/-- The view of term `T` of the input wires of a job, with `H` fixed to `h`. -/
def inputBits (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (job : Job) (T : C.Term) : List Bit :=
  job.points.flatMap fun x => bitsOfDigest (truncateHash (h (.prf (seeds T) x)))

theorem D_inputQuery (h : Query C → HashOutput) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (i : C.Party)
    (job : Job) (T : C.Term) :
    D prims h (inputQuery (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) job) T =
      if i ∈ C.holders T then inputBits h seeds job T else [] := by
  unfold inputQuery
  simp only [D_bind, D_pure, D_mapM]
  rw [getD_terms_idxOf]
  by_cases hi : i ∈ C.holders T
  · simp only [prssCtx, if_pos hi, D_flatMapM, prf, D_map, D_hashQuery, inputBits, dealtKeys]
  · simp only [prssCtx, if_neg hi, D_pure]

end Inputs

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section InputValues

variable {C : Committee} (prims : Primitives)

/-- The inputs of an honest batch with `H` fixed to `h`. -/
def batchInputs (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (jobs : List Job) :
    C.Party → List (C.Term → List Bit) :=
  fun i => jobs.map fun job T => if i ∈ C.holders T then inputBits h seeds job T else []

theorem length_inputBits (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (job : Job) (T : C.Term) :
    (inputBits h seeds job T).length = digestBits * job.points.length := by
  unfold inputBits
  exact length_flatMap_block _ _ (fun _ => length_bitsOfDigest _) _

theorem batchInputs_main (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (circuits : Circuits)
    (parameter : PublicParameter) (jobs : List Job) :
    MainInputs (jobs.map (circuits parameter ·.kind)) noCoalition (batchInputs h seeds jobs) := by
  refine ⟨jobs.map fun job => digestBits * job.points.length, by simp, fun i _ => ⟨by simp [batchInputs], ?_⟩, ?_⟩
  · intro k hk T
    simp only [List.length_map] at hk
    simp only [batchInputs, List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some, Option.getD_some]
    split_ifs with hi
    · rw [length_inputBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk]; rfl
    · rfl
  · intro k T i hi j hj _ _
    simp only [batchInputs, List.getElem?_map]
    rcases jobs[k]? with _ | job
    · rfl
    · simp [hi, hj]

theorem sum_terms_eq {M : Type} [AddCommMonoid M] (f : C.Term → M) : (C.terms.map f).sum = ∑ T, f T := by
  unfold Committee.terms
  exact Finset.sum_map_toList _ _

theorem inputValue_inputBits (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (job : Job) :
    inputValue (inputBits h seeds job) =
      (job.points.map fun x => (C.terms.map fun T => truncateHash (h (.prf (seeds T) x))).foldl (· ^^^ ·) 0).flatMap
        bitsOfDigest := by
  obtain ⟨T₀, -⟩ := lackedTerm_empty (C := C)
  have hne : C.terms ≠ [] := List.ne_nil_of_mem (mem_terms T₀)
  unfold inputValue
  rw [foldl_max_const _ (digestBits * job.points.length) (by simpa using hne)
    (fun a ha => by obtain ⟨T, -, rfl⟩ := List.mem_map.1 ha; exact length_inputBits h seeds job T)]
  refine List.ext_getElem (by rw [List.length_map, List.length_range,
    length_flatMap_block _ _ (fun _ => length_bitsOfDigest _), List.length_map]) fun g h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_range]
  simp only [List.length_map, List.length_range] at h₁
  have hd : 0 < digestBits := by decide
  obtain ⟨m, b, hb, rfl⟩ : ∃ m b, b < digestBits ∧ g = digestBits * m + b :=
    ⟨g / digestBits, g % digestBits, Nat.mod_lt _ hd, (Nat.div_add_mod g digestBits).symm⟩
  have hm : m < job.points.length := by
    by_contra hc; push_neg at hc; nlinarith
  rw [List.getElem_eq_getD 0, getD_flatMap_block _ _ (fun _ => length_bitsOfDigest _) _ m b (by simpa using hm) hb]
  simp only [List.getElem_map, getD_bitsOfDigest_foldl _ _ _ hb, bitsOfDigest_zero_getD, zero_add, List.map_map]
  rw [sum_terms_eq]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold inputBits
  rw [getD_flatMap_block _ _ (fun _ => length_bitsOfDigest _) _ m b hm hb]
  rfl

theorem D_evalJob (h : Query C → HashOutput) (circuits : Circuits) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (job : Job) :
    D prims h (evalJob circuits parameter seeds job) = (circuits parameter job.kind).eval
      ((job.points.map fun x => (C.terms.map fun T => truncateHash (h (.prf (seeds T) x))).foldl (· ^^^ ·) 0).flatMap
        bitsOfDigest) := by
  simp only [evalJob, prfValue, prf, D_bind, D_pure, D_mapM, D_map, D_hashQuery, List.map_map]

theorem mainOutputs_batch (h : Query C → HashOutput) (seeds : C.Term → HashOutput) (circuits : Circuits)
    (parameter : PublicParameter) (jobs : List Job) :
    mainOutputs (jobs.map (circuits parameter ·.kind)) (batchInputs h seeds jobs) =
      jobs.map fun job => D prims h (evalJob circuits parameter seeds job) := by
  unfold mainOutputs
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  simp only [List.length_map] at h₂
  simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add, D_evalJob]
  congr 1
  rw [← inputValue_inputBits]
  congr 1
  funext T
  refine reconstruct_of_agree _ T _ fun i hi => ⟨fun T => if i ∈ C.holders T then inputBits h seeds jobs[k] T else [],
    ?_, by simp [hi]⟩
  simp only [batchInputs, List.getElem?_map, List.getElem?_eq_getElem h₂, Option.map_some]

end InputValues

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section BatchStep

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] {I O L R α : Type}
  (prims : Primitives) (K : Constants C E)

theorem FrameR.flatMapM {α β : Type} (f : α → OracleComp (RoSpec C) (List β)) (hf : ∀ a, FrameR prims (f a)) :
    ∀ l : List α, FrameR prims (l.flatMapM f)
  | [] => FrameR.pure _
  | a :: l => by
    rw [List.flatMapM_cons]
    exact (hf a).bind fun _ => (FrameR.flatMapM f hf l).bind fun _ => FrameR.pure _

theorem FrameR.inputQuery (ctx : Context C) (job : Job) : FrameR prims (inputQuery ctx job) := by
  unfold ThresholdLeanXmssSecurity.inputQuery
  refine (FrameR.mapM _ (fun T => FrameR.ite _ (FrameR.flatMapM prims _ (fun x => ?_) _) (FrameR.pure _)) _).bind
    fun _ => FrameR.pure _
  exact (FrameR.hashQuery (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)).map _ |>.map _

theorem inputShares_fun {ι : Type} {G : OracleSpec ι} (ctx : Context C) :
    (inputShares (E := E) (G := G) ctx) = fun job => oracleStep (inputQuery ctx job) :=
  funext (inputShares_eq ctx)

/-- One honest real batch of a ceremony, from its inputs on. Every operator gets the outputs of the
jobs in the clear. -/
theorem batch_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (mode : ReshareMode)
    (circuits : Circuits) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (jobs : List Job)
    (lab tg Lk c : ℕ) (Ks : Finset HashOutput) (hLk : Lk ≤ lab) (hKs : Ks.card ≤ c)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK Ks Lk s) (fuel : ℕ)
    (g : C.Party → List (List Bit) × RunState C → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (ε : ℝ≥0∞)
    (h : ∀ (outs : List (List Bit)) (hist' : C.Party → C.Term → List Bit) (Ks' : Finset HashOutput) (s' : HashCache C),
      (∀ h' s'', Good prims h' → s' ≤ s'' → Agrees h' s'' →
        outs = jobs.map fun job => D prims h' (evalJob circuits parameter seeds job)) →
      Ks'.card ≤ c + checkKeys (tupleCount (jobs.map (circuits parameter ·.kind))) →
      CacheOK Ks' (lab + depth (jobs.map (circuits parameter ·.kind)) + 1 +
        checkLabels (tupleCount (jobs.map (circuits parameter ·.kind)))) s' → NoMpc s' → s ≤ s' →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (outs, ⟨hist' i, lab + depth (jobs.map (circuits parameter ·.kind)) + 1 +
          checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))), tg⟩)) >>=
            honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => (jobs.mapM (inputShares (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i))) >>=
        fun inputs => (runJobs K (realRunGadgets K (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) mode)
          (jobs.map (circuits parameter ·.kind)) inputs).run ⟨fun _ => [], lab, tg⟩ >>= g i) >>=
        honestRounds F reply (fuel + depth (jobs.map (circuits parameter ·.kind)) * mode.rounds + 1 +
          checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))) + 1))).run' s] ≤
      checkCost E c (tupleCount (jobs.map (circuits parameter ·.kind))) Ks.card + ε := by
  set circs := jobs.map (circuits parameter ·.kind) with hcircs
  simp only [inputShares_fun, mapM_oracleStep]
  refine draw_step2 prims F reply _ (fun i => jobs.mapM (inputQuery (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i)))
    (fun i => FrameR.mapM _ (fun job => FrameR.inputQuery prims _ job) _) _ event s hn _
    fun w s₁ hw hn₁ hle₁ hfr₁ => ?_
  have hwv : ∀ h' s'', Good prims h' → s₁ ≤ s'' → Agrees h' s'' → ∀ i, w i = batchInputs h' seeds jobs i := by
    intro h' s'' hg hle ha i
    rw [hw h' s'' hg hle ha i, D_mapM]
    exact List.map_congr_left fun job _ => funext fun T => D_inputQuery prims h' parameter seeds pairKeys kT kP i job T
  obtain ⟨h₁, hg₁, ha₁⟩ : ∃ h₁, Good prims h₁ ∧ Agrees h₁ s₁ := ⟨hashOf prims s₁, good_hashOf prims s₁,
    agrees_hashOf prims hn₁⟩
  have hw₁ : w = batchInputs h₁ seeds jobs := funext (hwv h₁ s₁ hg₁ le_rfl ha₁)
  rw [hw₁]
  simp only [runJobs_eq, StateT.run_bind, bind_assoc]
  rw [List.range_eq_range']
  have hW := layerInv_zero (jobs := circs) (x := batchInputs h₁ seeds jobs)
    (batchInputs_main h₁ seeds circuits parameter jobs)
  refine layers_bound prims K (dealtKeys parameter seeds pairKeys) kT kP F reply mode circs (batchInputs h₁ seeds jobs)
    (depth circs) 0 _ _ [] (by simp) hW (by simp) (fun _ _ => []) (fun _ _ _ _ _ => rfl) lab tg Lk c Ks hLk hKs s₁ hn₁
    (cacheOK_of_frame hs hfr₁) fuel g event ε fun hist' Ks' s' h1 h2 h3 h4 => ?_
  refine h _ hist' Ks' s' (fun h' s'' hg hle ha => ?_) h1 (by simpa using h2) h3 (hle₁.trans h4)
  rw [← mainOutputs_batch prims h' seeds circuits parameter jobs, ← hw₁]
  congr 1
  exact funext (hwv h' s'' hg (h4.trans hle) ha)

end BatchStep

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Chunks

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (mode : ReshareMode)

/-- One batch of a real ceremony at operator `ctx.self`. -/
def realBatch (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit))) := do
  let (label, k) ← get
  let inputs ← StateT.lift (jobs.mapM (inputShares ctx))
  let (outputs, state) ← StateT.lift ((runJobs K (realRunGadgets K ctx mode) (jobs.map (circuits parameter ·.kind))
    inputs).run ⟨fun _ => [], label, k⟩)
  set (state.label, k + 1)
  pure (some outputs)

theorem realBatch_run (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) (st : ℕ × ℕ) :
    (realBatch K circuits mode ctx parameter jobs).run st =
      jobs.mapM (inputShares ctx) >>= fun inputs =>
        (runJobs K (realRunGadgets K ctx mode) (jobs.map (circuits parameter ·.kind)) inputs).run
          ⟨fun _ => [], st.1, st.2⟩ >>= fun r => pure (some r.1, (r.2.label, st.2 + 1)) := by
  simp only [realBatch, StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc, StateT.run_set,
    StateT.run_pure]

/-- The tuple bits of a batch of jobs. -/
def batchCount (parameter : PublicParameter) (jobs : List Job) : ℕ := tupleCount (jobs.map (circuits parameter ·.kind))

/-- The rounds of a batch of jobs. -/
def batchRounds (parameter : PublicParameter) (jobs : List Job) : ℕ :=
  depth (jobs.map (circuits parameter ·.kind)) * mode.rounds + 1 + checkLabels (batchCount circuits parameter jobs) + 1

/-- The round labels of a batch of jobs. -/
def batchLabels (parameter : PublicParameter) (jobs : List Job) : ℕ :=
  depth (jobs.map (circuits parameter ·.kind)) + 1 + checkLabels (batchCount circuits parameter jobs)

/-- The bound of the aborts of the batches `js` when `c` coin keys came before. -/
def chunksCost (E : Type) [Fintype E] (parameter : PublicParameter) : ℕ → List (List Job) → ℝ≥0∞
  | _, [] => 0
  | c, jobs :: js => checkCost E c (batchCount circuits parameter jobs) c +
      chunksCost E parameter (c + checkKeys (batchCount circuits parameter jobs)) js

theorem checkCost_mono (c cnt kc : ℕ) (h : kc ≤ c) : checkCost E c cnt kc ≤ checkCost E c cnt c := by
  unfold checkCost
  split_ifs
  · exact le_rfl
  · gcongr

theorem chunks_step [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) {α : Type} :
    ∀ (js : List (List Job)) (lab k Lk c : ℕ) (Ks : Finset HashOutput), Lk ≤ lab → Ks.card ≤ c →
      ∀ (s : HashCache C), NoMpc s → CacheOK Ks Lk s → ∀ (fuel : ℕ)
      (g : C.Party → List (Option (List (List Bit))) × (ℕ × ℕ) → PartyM C E RealSpec α)
      (event : (C.Party → Option α) → Prop) (ε : ℝ≥0∞),
      (∀ (outs : List (Option (List (List Bit)))) (Ks' : Finset HashOutput) (s' : HashCache C),
        (∀ h' s'', Good prims h' → s' ≤ s'' → Agrees h' s'' →
          outs = js.map fun jobs => some (jobs.map fun job => D prims h' (evalJob circuits parameter seeds job))) →
        Ks'.card ≤ c + (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum →
        CacheOK Ks' (lab + (js.map (batchLabels circuits parameter)).sum) s' → NoMpc s' → s ≤ s' →
        Pr[event | (simulateQ (localAnswer prims)
          (honestStart (fun i => g i (outs, (lab + (js.map (batchLabels circuits parameter)).sum, k + js.length))) >>=
            honestRounds F reply fuel)).run' s'] ≤ ε) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => (js.mapM (realBatch K circuits mode (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i)
          parameter)).run (lab, k) >>= g i) >>=
          honestRounds F reply (fuel + (js.map (batchRounds circuits mode parameter)).sum))).run' s] ≤
        chunksCost circuits E parameter c js + ε := by
  intro js
  induction js with
  | nil =>
    intro lab k Lk c Ks hLk hKs s hn hs fuel g event ε h
    simp only [List.mapM_nil, StateT.run_pure, pure_bind, List.map_nil, List.sum_nil, Nat.add_zero, chunksCost,
      zero_add, List.length_nil] at h ⊢
    exact h [] Ks s (fun _ _ _ _ _ => rfl) hKs (hs.mono_label hLk) hn le_rfl
  | cons jobs js ih =>
    intro lab k Lk c Ks hLk hKs s hn hs fuel g event ε h
    simp only [List.mapM_cons, StateT.run_bind, realBatch_run, bind_assoc, pure_bind, StateT.run_pure]
    rw [show fuel + ((jobs :: js).map (batchRounds circuits mode parameter)).sum =
      (fuel + (js.map (batchRounds circuits mode parameter)).sum) + depth (jobs.map (circuits parameter ·.kind)) * mode.rounds +
        1 + checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))) + 1 by
      simp only [List.map_cons, List.sum_cons, batchRounds, batchCount]; ring]
    refine le_trans (batch_step prims K F reply mode circuits parameter seeds pairKeys kT kP jobs lab k Lk c Ks hLk hKs s hn hs
      _ _ event (chunksCost circuits E parameter (c + checkKeys (batchCount circuits parameter jobs)) js + ε) ?_) ?_
    · intro outs hist' Ks' s' houts hKs' hs' hn' hle'
      dsimp only
      refine ih _ (k + 1) _ (c + checkKeys (batchCount circuits parameter jobs)) Ks' le_rfl hKs' s' hn' hs' fuel _ event ε ?_
      intro outs' Ks'' s'' houts' hKs'' hs'' hn'' hle''
      dsimp only
      have hlab : lab + depth (jobs.map (circuits parameter ·.kind)) + 1 +
          checkLabels (tupleCount (jobs.map (circuits parameter ·.kind))) + (js.map (batchLabels circuits parameter)).sum =
          lab + ((jobs :: js).map (batchLabels circuits parameter)).sum := by
        simp only [List.map_cons, List.sum_cons, batchLabels, batchCount]; ring
      have hk : k + 1 + js.length = k + (jobs :: js).length := by simp; ring
      rw [hlab, hk]
      refine h _ Ks'' s'' (fun h' s₃ hg hle ha => ?_) (by simp only [List.map_cons, List.sum_cons]; omega) (hlab ▸ hs'') hn''
        (hle'.trans hle'')
      rw [List.map_cons, houts h' s₃ hg (hle''.trans hle) ha, houts' h' s₃ hg hle ha]
    · rw [chunksCost, add_assoc]
      gcongr
      exact checkCost_mono _ _ _ hKs

end Chunks

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section LocalStep

variable {C : Committee} {E : Type} {I O L R α : Type} (prims : Primitives)

/-- The honest network after an own local computation of each operator. -/
theorem local_step {β : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (oa : C.Party → OracleComp (LocalSpec C) β) (g : C.Party → β → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (ε : ℝ≥0∞)
    (h : ∀ z ∈ support ((simulateQ (localAnswer prims) (Concrete.sequenceFin oa)).run s),
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (z.1 i)) >>= honestRounds F reply fuel)).run' z.2] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => localStep (oa i) >>= g i) >>= honestRounds F reply fuel)).run' s] ≤ ε := by
  have hsame : SameRun prims (honestStart (fun i => localStep (oa i) >>= g i) >>= honestRounds F reply fuel)
      (Concrete.sequenceFin oa >>= fun b => honestStart (fun i => g i (b i)) >>= honestRounds F reply fuel) := by
    have hstart : SameRun prims (honestStart fun i => localStep (oa i) >>= g i)
        (Concrete.sequenceFin oa >>= fun b => honestStart fun i => g i (b i)) := by
      unfold honestStart
      simp only [advance_localStep_bind]
      have h := sameRun_sequenceFin_dep prims oa (fun i u => advance (g i u).run) (fun _ _ v => v)
      refine (SameRun.of_eq ?_).trans (h.trans (SameRun.of_eq (bind_congr fun x => bind_pure _)))
      simp only [bind_pure]
    refine (hstart.bind fun _ => SameRun.refl _ _).trans (SameRun.of_eq ?_)
    rw [bind_assoc]
  have hrun : Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => localStep (oa i) >>= g i) >>= honestRounds F reply fuel)).run' s] =
      Pr[event | (simulateQ (localAnswer prims) (Concrete.sequenceFin oa >>= fun b =>
        honestStart (fun i => g i (b i)) >>= honestRounds F reply fuel)).run' s] := by
    simp only [StateT.run'_eq, probEvent_def, evalDist_map, hsame s]
  rw [hrun, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine probEvent_bind_le_of_forall_le fun z hz => ?_
  have := h z hz
  rwa [StateT.run'_eq] at this

/-- Each operator samples its own value from `p`, and the cache stays. -/
theorem sample_step {β : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) (p : ProbComp β)
    (g : C.Party → β → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (ε : ℝ≥0∞)
    (h : ∀ b : C.Party → β, Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i (b i)) >>= honestRounds F reply fuel)).run' s] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => localStep (liftComp p (LocalSpec C)) >>= g i) >>= honestRounds F reply fuel)).run' s] ≤ ε := by
  refine local_step prims F reply fuel _ g event s ε fun z hz => ?_
  have hp : IsLocalProb (C := C) (Concrete.sequenceFin fun _ : C.Party => liftComp p (LocalSpec C)) := by
    rw [← liftComp_sequenceFin]; exact IsLocalProb.liftComp _
  rw [(IsLocalProb.support_run prims hp s z hz).1]
  exact h z.1

end LocalStep

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section SetupStep

variable {C : Committee} {E : Type} {I O L R α : Type} (prims : Primitives)

theorem not_isCoin_commit (phase : Phase) (a b : C.Party) (l : List HashOutput) : ¬ IsCoin (C := C) (.commit phase a b l) := by
  rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h

theorem FrameR.hashQuery' {q : Query C} (hq : ∀ k idx, q ≠ .expand k idx) (hq' : ∀ t ρ v, q ≠ .coinKey t ρ v) :
    FrameR prims (ThresholdLeanXmss.hashQuery q) :=
  FrameR.hashQuery (by rintro (⟨k, idx, h⟩ | ⟨t, ρ, v, h⟩); exacts [hq k idx h, hq' t ρ v h])

theorem FrameR.commitQueries (phase : Phase) (i : C.Party) (own : Parts C) : FrameR prims (commitQueries phase i own) :=
  FrameR.mapM _ (fun _ => FrameR.hashQuery' prims (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)) _

theorem FrameR.openQueries (phase : Phase) (i : C.Party) (revealed : Mail C E) :
    FrameR prims (openQueries phase i revealed) :=
  FrameR.mapM _ (fun _ => FrameR.hashQuery' prims (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)) _

theorem FrameR.sharedQueries (phase : Phase) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) : FrameR prims (sharedQueries phase i keys) :=
  FrameR.mapM _ (fun _ => FrameR.hashQuery' prims (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)) _

theorem FrameR.deriveKeys (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    FrameR prims (deriveKeys phase i view) := by
  unfold ThresholdLeanXmss.deriveKeys
  have hq : ∀ (k : KeyKind) (l : List HashOutput), FrameR prims (ThresholdLeanXmss.hashQuery (C := C) (.derive phase k l)) :=
    fun _ _ => FrameR.hashQuery' prims (fun _ _ h => by cases h) (fun _ _ _ h => by cases h)
  have hrest : ∀ parameter : HashOutput, FrameR prims (do
      let term ← C.terms.mapM fun T => if i ∈ C.holders T then
        ThresholdLeanXmss.hashQuery (C := C) (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T))
        else Pure.pure 0
      let pair ← C.parties.mapM fun j => if h : j = i then Pure.pure 0 else
        let p := C.pairOf i j (Ne.symm h)
        ThresholdLeanXmss.hashQuery (C := C) (.derive phase .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1])
      Pure.pure (parameter, fun T => term.getD (C.terms.idxOf T) 0, fun (j : C.Party) => pair.getD j.val 0)) := fun parameter =>
    (FrameR.mapM _ (fun T => by split_ifs; exacts [hq _ _, FrameR.pure _]) _).bind fun _ =>
      (FrameR.mapM _ (fun j => by split_ifs; exacts [FrameR.pure _, hq _ _]) _).bind fun _ => FrameR.pure _
  split_ifs
  · exact (hq _ _).bind hrest
  · exact (FrameR.pure _).bind hrest

/-- The PRSS keys of operator `i` from the keys `kT` of the terms and `kP` of the pairs. -/
def prssKeysOf (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (i : C.Party) : PrssKeys C :=
  ⟨fun T => if i ∈ C.holders T then kT T else 0, fun j => if hj : j = i then 0 else kP (C.pairOf i j (Ne.symm hj))⟩

/-- An honest PRSS setup. Every operator continues with its PRSS keys of one dealing. -/
theorem setup_step [Nonempty C.Party] (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (f : C.Party → PrssKeys C → PartyM C E (CallSpec I O) α) (event : (C.Party → Option α) → Prop)
    (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (s' : HashCache C), NoMpc s' → s ≤ s' →
      (∀ q, IsCoin q → s' q = s q) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => f i (prssKeysOf kT kP i)) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => prssSetup i >>= f i) >>= honestRounds F reply (fuel + 3))).run' s] ≤ ε := by
  simp only [prssSetup_eq, bind_assoc, commitRevealEcho_eq]
  refine sample_step prims F reply _ sampleParts _ event s ε fun parts => ?_
  refine draw_step2 prims F reply _ (fun i => commitQueries .prss i (parts i)) (fun i => FrameR.commitQueries prims _ _ _)
    _ event s hn ε fun cs s₁ hcs hn₁ hle₁ hfr₁ => ?_
  rw [show fuel + 3 = (fuel + 2) + 1 from rfl, honestRounds_exchange F reply (fuel + 2) (fun i => commitOutbox i (cs i)) _
    fun k j => isAbort_commitOutbox k _ j]
  rw [show fuel + 2 = (fuel + 1) + 1 from rfl, honestRounds_exchange F reply (fuel + 1)
    (fun i => revealOutbox .prss i (parts i)) _ fun k j => isAbort_revealOutbox _ k _ j]
  refine draw_step2 prims F reply _ (fun i => openQueries .prss i (honestReveals (E := E) .prss parts i))
    (fun i => FrameR.openQueries prims _ _ _) _ event s₁ hn₁ ε fun os s₂ hos hn₂ hle₂ hfr₂ => ?_
  obtain ⟨h₂, hg₂, ha₂⟩ : ∃ h₂, Good prims h₂ ∧ Agrees h₂ s₂ := ⟨hashOf prims s₂, good_hashOf prims s₂,
    agrees_hashOf prims hn₂⟩
  have hcs' : cs = fun i => D prims h₂ (commitQueries .prss i (parts i)) := funext (hcs h₂ s₂ hg₂ hle₂ ha₂)
  have hos' : os = fun i => D prims h₂ (openQueries .prss i (honestReveals (E := E) .prss parts i)) :=
    funext (hos h₂ s₂ hg₂ le_rfl ha₂)
  have hopen : ∀ i, openCheck .prss i (parts i) (fun k => commitOutbox (E := E) k (cs k) i)
      (fun k => revealOutbox .prss k (parts k) i) (os i) := fun i => by
    rw [hcs', hos']; exact openCheck_honest prims h₂ .prss parts i
  simp only [require_bind_of (hopen _), pure_bind]
  refine draw_step2 prims F reply _ (fun i => deriveKeys .prss i (setupView .prss i (parts i)
    (fun k => revealOutbox (E := E) .prss k (parts k) i))) (fun i => FrameR.deriveKeys prims _ _ _) _ event s₂ hn₂ ε
    fun ks s₃ hks hn₃ hle₃ hfr₃ => ?_
  refine draw_step2 prims F reply _ (fun i => sharedQueries .prss i (ks i)) (fun i => FrameR.sharedQueries prims _ _ _)
    _ event s₃ hn₃ ε fun sh s₄ hsh hn₄ hle₄ hfr₄ => ?_
  rw [honestRounds_exchange F reply fuel (fun i => echoOutbox (E := E) .prss i (ks i) (sh i)) _
    fun k j => isAbort_echoOutbox _ k _ _ j]
  obtain ⟨h₄, hg₄, ha₄⟩ : ∃ h₄, Good prims h₄ ∧ Agrees h₄ s₄ := ⟨hashOf prims s₄, good_hashOf prims s₄,
    agrees_hashOf prims hn₄⟩
  have hks' : ks = fun i => D prims h₄ (deriveKeys .prss i (honestView (E := E) .prss parts i)) :=
    funext (hks h₄ s₄ hg₄ hle₄ ha₄)
  have hsh' : sh = fun i => D prims h₄ (sharedQueries .prss i (ks i)) := funext (hsh h₄ s₄ hg₄ le_rfl ha₄)
  have hecho : ∀ i, echoCheck .prss i (ks i) (sh i) (fun k => echoOutbox (E := E) .prss k (ks k) (sh k) i) := fun i => by
    rw [hsh', hks']; exact echoCheck_honest prims h₄ .prss parts i
  simp only [require_bind_of (hecho _), pure_bind]
  have hkeys : ∀ i, (⟨(ks i).2.1, (ks i).2.2⟩ : PrssKeys C) =
      prssKeysOf (fun T => h₄ (termInput .prss parts T)) (fun p => h₄ (pairInput .prss parts p)) i := fun i => by
    rw [hks']; simp only [D_deriveKeys_honest]; rfl
  simp only [hkeys]
  exact h _ _ s₄ hn₄ (hle₁.trans (hle₂.trans (hle₃.trans hle₄))) fun q hq =>
    (hfr₄ q hq).trans ((hfr₃ q hq).trans ((hfr₂ q hq).trans (hfr₁ q hq)))

end SetupStep

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section CeremonyPieces

variable {C : Committee} {E : Type} {I O L R α : Type} (prims : Primitives)

/-- The honest network after one computation of `H` that every operator runs. Each operator
continues with the common value. -/
theorem common_step [Nonempty C.Party] {β : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (oa : OracleComp (RoSpec C) β) (hframe : FrameR prims oa)
    (g : C.Party → β → PartyM C E (CallSpec I O) α)
    (event : (C.Party → Option α) → Prop) (s : HashCache C) (hn : NoMpc s) (ε : ℝ≥0∞)
    (h : ∀ (v : β) (s' : HashCache C), (∀ h' s'', Good prims h' → s' ≤ s'' → Agrees h' s'' → v = D prims h' oa) →
      NoMpc s' → s ≤ s' → (∀ q, IsCoin q → s' q = s q) →
      Pr[event | (simulateQ (localAnswer prims)
        (honestStart (fun i => g i v) >>= honestRounds F reply fuel)).run' s'] ≤ ε) :
    Pr[event | (simulateQ (localAnswer prims)
      (honestStart (fun i => oracleStep oa >>= g i) >>= honestRounds F reply fuel)).run' s] ≤ ε := by
  refine draw_step2 prims F reply fuel (fun _ => oa) (fun _ => hframe) g event s hn ε fun w s' hw hn' hle hfr => ?_
  obtain ⟨h', hg', ha'⟩ : ∃ h', Good prims h' ∧ Agrees h' s' := ⟨hashOf prims s', good_hashOf prims s',
    agrees_hashOf prims hn'⟩
  have hcst : w = fun _ => D prims h' oa := funext (hw h' s' hg' le_rfl ha')
  rw [hcst]
  exact h _ s' (fun h'' s'' hg hle ha => by
    have := hw h'' s'' hg hle ha (Classical.arbitrary _); rw [hcst] at this; exact this) hn' hle hfr

theorem chunks_flatten_aux {β : Type} (size : ℕ) (l : List β) :
    ∀ m, ((List.range m).map fun k => (l.drop (size * k)).take size).flatten = l.take (size * m)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.map_append, List.flatten_append, chunks_flatten_aux size l m]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [show size * (m + 1) = size * m + size by ring, List.take_add]

theorem chunks_flatten {β : Type} (size : ℕ) (hsize : 0 < size) (l : List β) : (chunks size l).flatten = l := by
  unfold chunks
  rw [chunks_flatten_aux]
  refine List.take_of_length_le ?_
  have := Nat.div_add_mod (l.length + size - 1) size
  have := Nat.mod_lt (l.length + size - 1) hsize
  nlinarith [Nat.sub_add_cancel (show 1 ≤ l.length + size by omega)]

theorem foldlM_some_append {β : Type} : ∀ (L : List (List β)) (acc : List β),
    (L.map some).foldlM (fun acc batch => batch.map (acc ++ ·)) acc = some (acc ++ L.flatten)
  | [], acc => by simp
  | b :: L, acc => by
    simp only [List.map_cons, List.foldlM_cons, Option.map_some, Option.bind_eq_bind]
    show List.foldlM _ (acc ++ b) (List.map some L) = _
    rw [foldlM_some_append L (acc ++ b), List.flatten_cons, List.append_assoc]

end CeremonyPieces

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section CeremonyMap

theorem id_mapM {β γ : Type} (f : β → Id γ) : ∀ l : List β, (l.mapM f : Id (List γ)) = l.map f
  | [] => rfl
  | b :: l => by rw [List.mapM_cons, id_mapM f l]; rfl

theorem id_bind_eq {β γ : Type} (x : Id β) (f : β → Id γ) : x >>= f = f x := rfl

theorem id_map_eq {β γ : Type} (x : Id β) (f : β → γ) : f <$> x = f x := rfl

theorem id_pure_eq {β : Type} (b : β) : (pure b : Id β) = b := rfl

variable {m : Type → Type} [Monad m] [LawfulMonad m] (φ : ∀ {β : Type}, m β → β)
  (hpure : ∀ {β : Type} (b : β), φ (pure b : m β) = b)
  (hbind : ∀ {β γ : Type} (x : m β) (f : β → m γ), φ (x >>= f) = φ (f (φ x)))

include hpure hbind in
theorem map_mapM {β γ : Type} (f : β → m γ) : ∀ l : List β, φ (l.mapM f) = l.map fun b => φ (f b)
  | [] => by simp [hpure]
  | b :: l => by rw [List.mapM_cons, hbind, hbind, map_mapM f l, hpure]; rfl

include hpure hbind in
theorem map_batched (size : ℕ) (run : List Job → m (Option (List (List Bit)))) (jobs : List Job) :
    φ (batched size run jobs) = batched (m := Id) size (fun js => φ (run js)) jobs := by
  unfold batched
  rw [hbind, hpure, map_mapM φ hpure hbind]
  rw [id_mapM]; rfl

include hpure hbind in
theorem map_map' {β γ : Type} (f : β → γ) (x : m β) : φ (f <$> x) = f (φ x) := by
  rw [map_eq_bind_pure_comp, hbind, Function.comp, hpure]

include hpure hbind in
/-- A monad map to `Id` that keeps `pure` and `bind` commutes with `ceremonyOutput`. -/
theorem map_ceremonyOutput (lift : ∀ {β : Type}, OracleComp HashSpec β → m β) (parameter : PublicParameter)
    (run : List Job → m (Option (List (List Bit)))) (top : TopTree) (tree : Tree) :
    φ (ceremonyOutput lift parameter run top tree) =
      ceremonyOutput (m := Id) (fun oa => φ (lift oa)) parameter (fun js => φ (run js)) top tree := by
  have hmap : ∀ {β γ : Type} (f : β → γ) (x : m β), φ (f <$> x) = f (φ x) := fun f x => map_map' φ hpure hbind f x
  have hrun : ∀ js, (φ (β := Id (Option (List (List Bit)))) (run js)) = (φ (β := Option (List (List Bit))) (run js)) :=
    fun _ => rfl
  have hlift : ∀ {β : Type} (oa : OracleComp HashSpec β), (φ (β := Id β) (lift oa)) = (φ (β := β) (lift oa)) :=
    fun _ => rfl
  cases tree with
  | top =>
    simp only [ceremonyOutput, hbind, id_bind_eq, hrun, hlift]
    cases hr : φ (run topJobs) with
    | none => simp only [hpure, hr]; rfl
    | some outputs => simp only [hbind, hpure, hmap, id_bind_eq, id_map_eq, id_pure_eq, hr]
  | bottom b =>
    simp only [ceremonyOutput, hbind, id_bind_eq, hrun, hlift]
    cases hr : φ (run (bottomJobs b)) with
    | none => simp only [hpure, hr]; rfl
    | some outputs =>
      simp only [hbind, hpure, hmap, id_bind_eq, id_map_eq, id_pure_eq, hr]
      split
      · rename_i randomness encoding heq
        simp only [heq, hbind]
        cases hv : φ (run (signJobs b encoding)) with
        | none => simp only [hpure, hv]
        | some values =>
          simp only [hbind, hpure, id_bind_eq, id_pure_eq, hv]
          split <;> simp only [hpure] <;> rfl
      · rename_i heq
        simp only [heq, hpure]

end CeremonyMap

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Dealer

variable {C : Committee} (prims : Primitives) (circuits : Circuits) (settings : Settings)

theorem batched_id (size : ℕ) (hsize : 0 < size) (f : Job → List Bit) (jobs : List Job) :
    batched (m := Id) size (fun js => some (js.map f)) jobs = some (jobs.map f) := by
  unfold batched
  rw [id_bind_eq, id_mapM]
  have := foldlM_some_append ((chunks size jobs).map fun js => js.map f) []
  simp only [List.map_map, Function.comp_def] at this
  rw [id_pure_eq]
  refine this.trans ?_
  rw [List.nil_append, ← List.map_flatten, chunks_flatten size hsize]

/-- The outputs of a run in the clear with `H` fixed to `h`. -/
@[irreducible] def evalRun (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (jobs : List Job) : Option (List (List Bit)) :=
  some (jobs.map fun job => D prims h (evalJob circuits parameter seeds job))

theorem evalRun_eq (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (jobs : List Job) :
    evalRun prims circuits parameter seeds h jobs = some (jobs.map fun job => D prims h (evalJob circuits parameter seeds job)) := by
  unfold evalRun; rfl

/-- The tree of a ceremony with `H` fixed to `h`, computed in the clear. -/
def ceremonyAt (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (top : TopTree) (tree : Tree) : Option TreeOutput :=
  ceremonyOutput (m := Id) (fun oa => D prims h (tweakable oa)) parameter (evalRun prims circuits parameter seeds h) top tree

theorem D_dealerCeremony (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (top : TopTree) (tree : Tree) (hsize : 0 < settings.batchSize) :
    (D prims h (dealerCeremony circuits settings parameter seeds top tree)).1 =
      ceremonyAt prims circuits parameter seeds h top tree := by
  let φ : ∀ {β : Type}, WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) β → β :=
    fun x => (D prims h x.run).1
  have hpure : ∀ {β : Type} (b : β), φ (pure b) = b := fun b => rfl
  have hbind : ∀ {β γ : Type} (x : WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) β)
      (f : β → WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) γ), φ (x >>= f) = φ (f (φ x)) := by
    intro β γ x f
    simp only [φ, WriterT.run_bind, D_bind, D_map]
  unfold dealerCeremony ceremonyAt
  rw [show ∀ x : WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) (Option TreeOutput),
    (D prims h x.run).1 = φ x from fun _ => rfl, map_ceremonyOutput φ hpure hbind]
  congr 1
  · funext β oa
    simp only [φ, WriterT.run_liftM, D_map]
  funext js
  refine (map_batched φ hpure hbind _ _ _).trans ?_
  rw [evalRun_eq, ← batched_id settings.batchSize hsize (fun job => D prims h (evalJob circuits parameter seeds job))]
  congr 1
  funext js'
  have hl : ∀ {β : Type} (x : OracleComp (RoSpec C) β),
      φ (liftM x : WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) β) = D prims h x := fun x => by
    simp only [φ, WriterT.run_liftM, D_map]
  show φ _ = _
  erw [hbind, hbind, hpure, hl, D_mapM]

theorem ceremonyOutput_closed {m : Type → Type} [Monad m] (P : ∀ {β : Type}, m β → Prop)
    (hpure : ∀ {β : Type} (b : β), P (pure b : m β))
    (hbind : ∀ {β γ : Type} (x : m β) (f : β → m γ), P x → (∀ b, P (f b)) → P (x >>= f))
    (lift : ∀ {β : Type}, OracleComp HashSpec β → m β) (hlift : ∀ {β : Type} (oa : OracleComp HashSpec β), P (lift oa))
    (parameter : PublicParameter) (run : List Job → m (Option (List (List Bit)))) (hrun : ∀ js, P (run js))
    (top : TopTree) (tree : Tree) : P (ceremonyOutput lift parameter run top tree) := by
  cases tree with
  | top =>
    refine hbind _ _ (hrun _) fun o => ?_
    rcases o with _ | outputs
    · exact hpure _
    · exact hbind _ _ (hlift _) fun _ => hpure _
  | bottom b =>
    refine hbind _ _ (hrun _) fun o => ?_
    rcases o with _ | outputs
    · exact hpure _
    · refine hbind _ _ (hlift _) fun root => hbind _ _ (hlift _) fun base => hbind _ _ (hlift _) fun g => ?_
      rcases g with _ | ⟨randomness, encoding⟩
      · exact hpure _
      · refine hbind _ _ (hrun _) fun o' => ?_
        rcases o' with _ | values
        · exact hpure _
        · refine hbind _ _ (hlift _) fun path => hbind _ _ (hlift _) fun topRoot => ?_
          split <;> exact hpure _

theorem FrameR.evalJob (parameter : PublicParameter) (seeds : C.Term → HashOutput) (job : Job) :
    FrameR prims (evalJob circuits parameter seeds job) := by
  unfold ThresholdLeanXmss.evalJob prfValue prf
  refine (FrameR.mapM _ (fun x => (FrameR.mapM _ (fun T => ?_) _).bind fun _ => FrameR.pure _) _).bind
    fun _ => FrameR.pure _
  exact (FrameR.hashQuery (by rintro (⟨_, _, h⟩ | ⟨_, _, _, h⟩) <;> cases h)).map _

theorem FrameR.dealerCeremony (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree)
    (tree : Tree) : FrameR prims (dealerCeremony circuits settings parameter seeds top tree) := by
  unfold ThresholdLeanXmss.dealerCeremony
  refine ceremonyOutput_closed (fun {β} (x : WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) β) => FrameR prims x.run) (fun b => FrameR.pure _)
    (fun x f hx hf => ?_) _ (fun oa => ?_) _ _ (fun js => ?_) top tree
  · show FrameR prims ((x >>= f).run)
    rw [WriterT.run_bind]
    exact hx.bind fun p => (hf p.1).map _
  · show FrameR prims (WriterT.run (liftM (ThresholdLeanXmss.tweakable oa)))
    rw [WriterT.run_liftM]
    exact (FrameR.tweakable oa).map _
  · have hW : ∀ {β γ : Type} (f : β → WriterT (List (List (List Bit))) (OracleComp (RoSpec C)) γ),
        (∀ b, FrameR prims (f b).run) → ∀ l : List β, FrameR prims (l.mapM f).run := by
      intro β γ f hf l
      induction l with
      | nil => exact FrameR.pure _
      | cons b l ih =>
        rw [List.mapM_cons, WriterT.run_bind]
        refine (hf b).bind fun p => FrameR.map _ ?_
        rw [WriterT.run_bind]
        exact ih.bind fun q => FrameR.map _ (FrameR.pure _)
    show FrameR prims (WriterT.run (batched _ _ js))
    unfold batched
    rw [WriterT.run_bind]
    refine (hW _ (fun js' => ?_) _).bind fun p => FrameR.map _ (FrameR.pure _)
    rw [WriterT.run_bind]
    refine FrameR.bind ?_ fun p => FrameR.map _ ?_
    · rw [WriterT.run_liftM]
      exact (FrameR.mapM _ (fun job => FrameR.evalJob prims circuits _ _ job) _).map _
    · rw [WriterT.run_bind]
      exact FrameR.pure _ |>.bind fun _ => FrameR.map _ (FrameR.pure _)

end Dealer

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Body

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The ceremony of operator `i` after the PRSS setup. -/
def ceremonyBody (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (top : TopTree) (tree : Tree) (i : C.Party) :
    PartyM C E RealSpec TreeOutput := do
  let some output ← (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) parameter
      (batched settings.batchSize (realBatch K circuits settings.mode (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i)
        parameter)) top tree).run' (0, 0) | failure
  pure output

/-- The ceremony of operator `i` after the PRSS setup with the PRSS keys `prss`. -/
def ceremonyRest (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (top : TopTree) (tree : Tree) (i : C.Party) (prss : PrssKeys C) : PartyM C E RealSpec TreeOutput := do
  let ctx : Context C := ⟨i, dealtKeys parameter seeds pairKeys i, prss⟩
  let some output ← (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) (dealtKeys parameter seeds pairKeys i).parameter
      (batched settings.batchSize fun jobs => do
        let (label, k) ← get
        let inputs ← StateT.lift (jobs.mapM (inputShares ctx))
        let (outputs, state) ← StateT.lift ((runJobs K (realRunGadgets K ctx settings.mode)
          (jobs.map (circuits (dealtKeys parameter seeds pairKeys i).parameter ·.kind)) inputs).run
            ⟨fun _ => [], label, k⟩)
        set (state.label, k + 1)
        pure (some outputs)) top tree).run' (0, 0) | failure
  pure output

theorem ceremony_eq (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (top : TopTree) (tree : Tree) (i : C.Party) :
    (ceremony K circuits settings i (dealtKeys parameter seeds pairKeys i) top tree : PartyM C E RealSpec TreeOutput) =
      prssSetup i >>= ceremonyRest K circuits settings parameter seeds pairKeys top tree i := rfl

theorem ceremonyRest_honest (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (top : TopTree) (tree : Tree) (i : C.Party) :
    ceremonyRest K circuits settings parameter seeds pairKeys top tree i (prssKeysOf kT kP i) =
      ceremonyBody K circuits settings parameter seeds pairKeys kT kP top tree i := rfl

end Body

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section TopBody

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The chain ends of the top tree from the outputs of its run. -/
def topChainEnd (outputs : List (List Bit)) : KeyIndex → ChainIndex → Digest := fun e l =>
  digestAt (outputs.getD (((List.finRange (2 ^ layerHeight)).flatMap fun b =>
    (List.finRange numChains).map fun l => (topKey b, l)).idxOf (e, l)) []) 0

/-- The top ceremony after its run. -/
def topRest (parameter : PublicParameter) (outs : List (Option (List (List Bit)))) (st : ℕ × ℕ) :
    PartyM C E RealSpec TreeOutput :=
  match outs.foldlM (fun acc batch => batch.map (acc ++ ·)) [] with
  | some outputs => oracleStep (tweakable (merkleNode parameter topLayer (topChainEnd outputs) layerHeight 0)) >>=
      fun root => pure (.top ⟨topChainEnd outputs, root⟩)
  | none => failure

theorem ceremonyBody_top (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (top : TopTree) (i : C.Party) :
    ceremonyBody K circuits settings parameter seeds pairKeys kT kP top .top i =
      ((chunks settings.batchSize topJobs).mapM (realBatch K circuits settings.mode
        (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) parameter)).run (0, 0) >>= fun p =>
          topRest parameter p.1 p.2 := by
  unfold ceremonyBody
  simp only [ceremonyOutput, batched]
  rw [StateT.run'_eq, StateT.run_bind, StateT.run_bind]
  simp only [bind_assoc, StateT.run_pure, pure_bind, map_bind]
  refine congrArg (_ >>= ·) (funext fun p => ?_)
  unfold topRest
  split
  · rename_i outputs heq
    rw [heq]
    simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_pure, map_pure, map_bind]
    rfl
  · rename_i hne
    simp only [StateT.run_pure, map_pure, pure_bind]
    split
    · rename_i o h
      exact absurd h (hne o)
    · rfl

theorem flatten_chunks_map {β γ : Type} (size : ℕ) (hsize : 0 < size) (f : β → γ) (l : List β) :
    ((chunks size l).map fun js => js.map f).flatten = l.map f := by
  rw [← List.map_flatten, chunks_flatten size hsize]

theorem ceremonyAt_top (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (top : TopTree) :
    ceremonyAt prims circuits parameter seeds h top .top =
      some (.top ⟨topChainEnd (topJobs.map fun job => D prims h (evalJob circuits parameter seeds job)),
        D prims h (tweakable (merkleNode parameter topLayer
          (topChainEnd (topJobs.map fun job => D prims h (evalJob circuits parameter seeds job))) layerHeight 0))⟩) := by
  unfold ceremonyAt
  rw [ceremonyOutput, evalRun_eq]
  rfl

theorem top_body_bound [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (top : TopTree) (o₀ : Option TreeOutput)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s)
    (ho : ∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top .top)
    (hsize : 0 < settings.batchSize) (fuel : ℕ) :
    Pr[(· ≠ fun _ => o₀) | (simulateQ (localAnswer prims)
      (honestStart (fun i => ceremonyBody K circuits settings parameter seeds pairKeys kT kP top .top i) >>=
        honestRounds F reply (fuel + ((chunks settings.batchSize topJobs).map
          (batchRounds circuits settings.mode parameter)).sum))).run' s] ≤
      chunksCost circuits E parameter 0 (chunks settings.batchSize topJobs) := by
  simp only [ceremonyBody_top]
  rw [← add_zero (chunksCost circuits E parameter 0 _)]
  refine chunks_step prims K circuits settings.mode F reply parameter seeds pairKeys kT kP _ 0 0 0 0 ∅ le_rfl (by simp)
    s hn hs fuel (fun i p => topRest parameter p.1 p.2) _ 0 fun outs Ks' s' houts hKs' hs' hn' hle' => ?_
  dsimp only
  obtain ⟨h₀, hg₀, ha₀⟩ : ∃ h₀, Good prims h₀ ∧ Agrees h₀ s' := ⟨hashOf prims s', good_hashOf prims s',
    agrees_hashOf prims hn'⟩
  set W := topJobs.map fun job => D prims h₀ (evalJob circuits parameter seeds job) with hW
  have hfold : outs.foldlM (fun acc batch => batch.map (acc ++ ·)) [] = some W := by
    rw [houts h₀ s' hg₀ le_rfl ha₀]
    have := foldlM_some_append ((chunks settings.batchSize topJobs).map fun js =>
      js.map fun job => D prims h₀ (evalJob circuits parameter seeds job)) []
    simp only [List.map_map, Function.comp_def] at this
    rw [this, List.nil_append, flatten_chunks_map _ hsize]
  simp only [topRest, hfold]
  refine common_step prims F reply fuel _ (FrameR.tweakable _) _ _ s' hn' 0 fun v s'' hv hn'' hle'' _ => ?_
  rw [honestRounds_pure]
  obtain ⟨h₁, hg₁, ha₁⟩ : ∃ h₁, Good prims h₁ ∧ Agrees h₁ s'' := ⟨hashOf prims s'', good_hashOf prims s'',
    agrees_hashOf prims hn''⟩
  have hW₁ : W = topJobs.map fun job => D prims h₁ (evalJob circuits parameter seeds job) := by
    have e₀ := houts h₀ s' hg₀ le_rfl ha₀
    have e₁ := houts h₁ s'' hg₁ hle'' ha₁
    rw [e₀] at e₁
    have := congrArg (fun L => (L.map fun o => o.getD []).flatten) e₁
    simp only [List.map_map, Function.comp_def, Option.getD_some, flatten_chunks_map _ hsize] at this
    exact this
  have ho₁ := ho h₁ s'' hg₁ (hle'.trans hle'') ha₁
  rw [ceremonyAt_top prims circuits parameter seeds h₁ top, ← hW₁, ← hv h₁ s'' hg₁ le_rfl ha₁] at ho₁
  rw [ho₁]
  simp

end TopBody

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Cost

variable {C : Committee} {E : Type} [Fintype E] (circuits : Circuits)

/-- The terms of the checks of one batch, other than its coin keys. -/
def freshCost (E : Type) [Fintype E] (R : ℕ) : ℝ≥0∞ :=
  (sliceBits : ℝ≥0∞) / Fintype.card E + ((R + 1 : ℕ) : ℝ≥0∞) * (2 / Fintype.card E) ^ challengeTries

theorem two_mul_sum_range_add (c k : ℕ) : 2 * ∑ j ∈ range k, (c + j) ≤ (c + k) ^ 2 - c ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add]
    have h1 : (c + k) ^ 2 ≤ (c + (k + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : c ^ 2 ≤ (c + k) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have : (c + (k + 1)) ^ 2 = (c + k) ^ 2 + 2 * (c + k) + 1 := by ring
    omega

theorem chalErr_eq (c r : ℕ) : chalErr E c r = (∑ j ∈ range r, ((c + j : ℕ) : ℝ≥0∞)) / 2 ^ 256 +
    (r : ℝ≥0∞) * (2 / Fintype.card E) ^ challengeTries := by
  unfold chalErr
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem checkCost_le (c cnt R : ℕ) (hR : halvings cnt ≤ R) :
    checkCost E c cnt c ≤ (((c + checkKeys cnt) ^ 2 - c ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 + freshCost E R := by
  unfold checkCost checkKeys freshCost
  split_ifs with h0
  · simp
  · set k := halvings cnt
    rw [chalErr_eq]
    have hsum : ((c : ℝ≥0∞) / 2 ^ 256 + (∑ j ∈ range (k + 1), ((c + 1 + j : ℕ) : ℝ≥0∞)) / 2 ^ 256) =
        ((∑ j ∈ range (k + 2), (c + j) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
      rw [ENNReal.div_add_div_same, Finset.sum_range_succ' (fun j => c + j) (k + 1)]
      push_cast
      rw [add_comm]
      congr 1
      simp only [add_zero]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hle : ((∑ j ∈ range (k + 2), (c + j) : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
        (((c + (k + 2)) ^ 2 - c ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
      have e : ((∑ j ∈ range (k + 2), (c + j) : ℕ) : ℝ≥0∞) / 2 ^ 256 =
          ((2 * ∑ j ∈ range (k + 2), (c + j) : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
        rw [show (2 : ℝ≥0∞) ^ 257 = 2 * 2 ^ 256 by rw [← pow_succ'], Nat.cast_mul, Nat.cast_ofNat,
          ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
      rw [e]
      gcongr
      exact two_mul_sum_range_add c (k + 2)
    have hf : ((k + 1 : ℕ) : ℝ≥0∞) ≤ ((R + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast (by omega : k + 1 ≤ R + 1)
    calc (c : ℝ≥0∞) / 2 ^ 256 + ↑sliceBits / ↑(Fintype.card E) +
          ((∑ j ∈ range (k + 1), ((c + 1 + j : ℕ) : ℝ≥0∞)) / 2 ^ 256 + ((k + 1 : ℕ) : ℝ≥0∞) * (2 / ↑(Fintype.card E)) ^ challengeTries)
        = ((c : ℝ≥0∞) / 2 ^ 256 + (∑ j ∈ range (k + 1), ((c + 1 + j : ℕ) : ℝ≥0∞)) / 2 ^ 256) +
            (↑sliceBits / ↑(Fintype.card E) + ((k + 1 : ℕ) : ℝ≥0∞) * (2 / ↑(Fintype.card E)) ^ challengeTries) := by ring
      _ ≤ _ := by
        rw [hsum]
        gcongr

theorem chunksCost_le (parameter : PublicParameter) (R : ℕ) : ∀ (js : List (List Job)) (c : ℕ),
    (∀ jobs ∈ js, halvings (batchCount circuits parameter jobs) ≤ R) →
    chunksCost circuits E parameter c js ≤
      (((c + (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum) ^ 2 - c ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 +
        js.length * freshCost E R
  | [], c, _ => by simp [chunksCost]
  | jobs :: js, c, hR => by
    rw [chunksCost]
    have h1 := checkCost_le (E := E) c (batchCount circuits parameter jobs) R (hR jobs (List.mem_cons_self ..))
    have h2 := chunksCost_le parameter R js (c + checkKeys (batchCount circuits parameter jobs))
      fun j hj => hR j (List.mem_cons_of_mem _ hj)
    refine (add_le_add h1 h2).trans (le_of_eq ?_)
    set k := checkKeys (batchCount circuits parameter jobs)
    set K := (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum
    have hsq : (c + k) ^ 2 - c ^ 2 + ((c + k + K) ^ 2 - (c + k) ^ 2) = (c + (k + K)) ^ 2 - c ^ 2 := by
      have h₁ : c ^ 2 ≤ (c + k) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have h₂ : (c + k) ^ 2 ≤ (c + k + K) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      rw [show c + (k + K) = c + k + K by ring]
      omega
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [← hsq, Nat.cast_add, ← ENNReal.div_add_div_same]
    push_cast
    ring

end Cost

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset

noncomputable section

namespace ThresholdLeanXmssSecurity

section BottomBody

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

def bCpk (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) : KeyIndex → ChainIndex → Digest × Digest × Digest :=
  fun e l => let bits := outputs.getD ((bottomKeys b).idxOf (e, l)) []
    (digestAt bits 0, digestAt bits 1, digestAt bits 2)

def bCommitment (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) : KeyIndex → Digest :=
  fun e => digestAt (outputs.getD ((bottomKeys b).length + e.val % 2 ^ layerHeight) []) 0

def bRho (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) : Digest :=
  digestAt (outputs.getD ((bottomKeys b).length + 2 ^ layerHeight) []) 0

/-- The bottom ceremony after its second run. -/
def bottomRest2 (parameter : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit))
    (root : Digest) (randomness : Randomness) (outs : List (Option (List (List Bit)))) :
    PartyM C E RealSpec TreeOutput :=
  match outs.foldlM (fun acc batch => batch.map (acc ++ ·)) [] with
  | some values => oracleStep (tweakable (merklePath parameter topLayer top.chainEnd (topKey b))) >>= fun path =>
      oracleStep (tweakable (Concrete.layerRoot parameter topLayer (topKey b) (bytesLE 16 root)
        ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩)) >>= fun topRoot =>
      if topRoot ≠ some top.root then failure else
      pure (.bottom ⟨bCpk b outputs, bCommitment b outputs, root, ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩⟩)
  | none => failure

/-- The bottom ceremony after its first run. -/
def bottomRest (parameter : PublicParameter) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (rb : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option (List (List Bit))))
    (outs : List (Option (List (List Bit)))) (st : ℕ × ℕ) : PartyM C E RealSpec TreeOutput :=
  match outs.foldlM (fun acc batch => batch.map (acc ++ ·)) [] with
  | some outputs =>
      oracleStep (tweakable (merkleNode parameter bottomLayer (fun e l => (bCpk b outputs e l).2.2) layerHeight b.val)) >>=
        fun root => oracleStep (tweakable (truncateHash <$> Concrete.oracleHash (randomizerInput parameter topLayer
          (topKey b) (bRho b outputs) (bytesLE 16 root)))) >>= fun base =>
        oracleStep (tweakable (grind parameter topLayer (topKey b) (bytesLE 16 root) base randomizerAttemptLimit 0)) >>=
        fun g => match g with
          | some (randomness, encoding) => ((chunks settings.batchSize (signJobs b encoding)).mapM rb).run st >>= fun p =>
              bottomRest2 parameter top b outputs root randomness p.1
          | none => failure
  | none => failure

theorem ceremonyBody_bottom (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (top : TopTree) (b : Fin (2 ^ layerHeight)) (i : C.Party) :
    ceremonyBody K circuits settings parameter seeds pairKeys kT kP top (.bottom b) i =
      ((chunks settings.batchSize (bottomJobs b)).mapM (realBatch K circuits settings.mode
        (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) parameter)).run (0, 0) >>= fun p =>
          bottomRest settings parameter top b (realBatch K circuits settings.mode
            (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) parameter) p.1 p.2 := by
  unfold ceremonyBody
  simp only [ceremonyOutput, batched]
  rw [StateT.run'_eq, StateT.run_bind, StateT.run_bind]
  simp only [bind_assoc, StateT.run_pure, pure_bind, map_bind]
  refine congrArg (_ >>= ·) (funext fun p => ?_)
  unfold bottomRest
  split
  · rename_i outputs heq
    rw [heq]
    simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_pure, map_pure, map_bind,
      bCpk, bCommitment, bRho, bottomKeys]
    refine bind_congr fun root => ?_
    refine bind_congr fun base => ?_
    refine bind_congr fun g => ?_
    rcases g with _ | ⟨randomness, encoding⟩
    · simp only [StateT.run_pure, map_pure, pure_bind]
    · simp only [StateT.run_bind, bind_assoc, map_bind]
      refine bind_congr fun q => ?_
      unfold bottomRest2
      split
      · rename_i values heq'
        rw [heq']
        simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, StateT.run_pure, map_pure, map_bind]
        refine bind_congr fun path => ?_
        refine bind_congr fun topRoot => ?_
        split_ifs <;> simp only [StateT.run_pure, map_pure, pure_bind] <;> rfl
      · rename_i hne'
        simp only [StateT.run_pure, map_pure, pure_bind]
        split
        · rename_i o h
          exact absurd h (hne' o)
        · rfl
  · rename_i hne
    simp only [StateT.run_pure, map_pure, pure_bind]
    split
    · rename_i o h
      exact absurd h (hne o)
    · rfl

end BottomBody

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
variable {C : Committee} (prims : Primitives) (circuits : Circuits)

def bottomAt (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) : Id (Option TreeOutput) := do
  let root ← (D prims h (tweakable (merkleNode parameter bottomLayer (fun e l => (bCpk b outputs e l).2.2) layerHeight b.val)) : Id Digest)
  let base ← (D prims h (tweakable (truncateHash <$> Concrete.oracleHash (randomizerInput parameter topLayer
    (topKey b) (bRho b outputs) (bytesLE 16 root)))) : Id Randomness)
  let some (randomness, encoding) ← (D prims h (tweakable (grind parameter topLayer (topKey b) (bytesLE 16 root) base randomizerAttemptLimit 0)) : Id _) | pure none
  let some values ← (evalRun prims circuits parameter seeds h (signJobs b encoding) : Id _) | pure none
  let path ← (D prims h (tweakable (merklePath parameter topLayer top.chainEnd (topKey b))) : Id _)
  let topRoot ← (D prims h (tweakable (Concrete.layerRoot parameter topLayer (topKey b) (bytesLE 16 root)
    ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩)) : Id _)
  if topRoot ≠ some top.root then pure none else
    pure (some (.bottom ⟨bCpk b outputs, bCommitment b outputs, root,
      ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩⟩))

theorem ceremonyAt_bottom (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    ceremonyAt prims circuits parameter seeds h top (.bottom b) =
      bottomAt prims circuits parameter seeds h top b
        ((bottomJobs b).map fun job => D prims h (evalJob circuits parameter seeds job)) := by
  unfold ceremonyAt
  rw [ceremonyOutput, evalRun_eq]
  rfl
end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
attribute [local irreducible] D
variable {C : Committee} {E : Type} (prims : Primitives) (circuits : Circuits)

theorem honestRounds_failure {I O L R α : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ) :
    honestStart (fun _ => (failure : PartyM C E (CallSpec I O) α)) >>= honestRounds F reply fuel =
      pure (fun _ => none) := by
  simp only [honestStart, advance_run_failure, sequenceFin_pure, pure_bind]
  rw [honestRounds_done]
  · rfl
  · exact fun _ => trivial

theorem chunks_outputs {β : Type} (size : ℕ) (hsize : 0 < size) (jobs : List Job) (f : Job → β) :
    ((chunks size jobs).map fun js => some (js.map f)).foldlM (fun acc batch => batch.map (acc ++ ·)) [] =
      some (jobs.map f) := by
  have := foldlM_some_append ((chunks size jobs).map fun js => js.map f) []
  simp only [List.map_map, Function.comp_def] at this
  rw [this, List.nil_append, flatten_chunks_map _ hsize]

def bottomResult (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (root : Digest)
    (g : Option (Randomness × Encoding)) : Id (Option TreeOutput) := do
  let some (randomness, encoding) ← (g : Id _) | pure none
  let some values ← (evalRun prims circuits parameter seeds h (signJobs b encoding) : Id _) | pure none
  let path ← (D prims h (tweakable (merklePath parameter topLayer top.chainEnd (topKey b))) : Id _)
  let topRoot ← (D prims h (tweakable (Concrete.layerRoot parameter topLayer (topKey b) (bytesLE 16 root)
    ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩)) : Id _)
  if topRoot ≠ some top.root then pure none else
    pure (some (.bottom ⟨bCpk b outputs, bCommitment b outputs, root,
      ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩⟩))

theorem ceremonyAt_bottom_values (parameter : PublicParameter) (seeds : C.Term → HashOutput) (h : Query C → HashOutput)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (root : Digest) (base : Randomness)
    (g : Option (Randomness × Encoding))
    (hw : outputs = (bottomJobs b).map fun job => D prims h (evalJob circuits parameter seeds job))
    (hr : root = D prims h (tweakable (merkleNode parameter bottomLayer (fun e l => (bCpk b outputs e l).2.2) layerHeight b.val)))
    (hb : base = D prims h (tweakable (truncateHash <$> Concrete.oracleHash (randomizerInput parameter topLayer
      (topKey b) (bRho b outputs) (bytesLE 16 root)))))
    (hg : g = D prims h (tweakable (grind parameter topLayer (topKey b) (bytesLE 16 root) base randomizerAttemptLimit 0))) :
    ceremonyAt prims circuits parameter seeds h top (.bottom b) =
      bottomResult prims circuits parameter seeds h top b outputs root g := by
  rw [ceremonyAt_bottom, ← hw]
  subst root base g
  rfl

variable [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (K : Constants C E) (settings : Settings)

theorem bottom_body_bound [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (top : TopTree) (b : Fin (2 ^ layerHeight)) (o₀ : Option TreeOutput)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s)
    (ho : ∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top (.bottom b))
    (hsize : 0 < settings.batchSize) (fuel Y : ℕ) (ε : ℝ≥0∞)
    (hY : ∀ enc, ((chunks settings.batchSize (signJobs b enc)).map (batchRounds circuits settings.mode parameter)).sum ≤ Y)
    (hε : ∀ enc, chunksCost circuits E parameter
      (((chunks settings.batchSize (bottomJobs b)).map fun js => checkKeys (batchCount circuits parameter js)).sum)
      (chunks settings.batchSize (signJobs b enc)) ≤ ε) :
    Pr[(· ≠ fun _ => o₀) | (simulateQ (localAnswer prims)
      (honestStart (fun i => ceremonyBody K circuits settings parameter seeds pairKeys kT kP top (.bottom b) i) >>=
        honestRounds F reply (fuel + Y + ((chunks settings.batchSize (bottomJobs b)).map
          (batchRounds circuits settings.mode parameter)).sum))).run' s] ≤
      chunksCost circuits E parameter 0 (chunks settings.batchSize (bottomJobs b)) + ε := by
  simp only [ceremonyBody_bottom]
  refine chunks_step prims K circuits settings.mode F reply parameter seeds pairKeys kT kP _ 0 0 0 0 ∅ le_rfl (by simp)
    s hn hs (fuel + Y) (fun i p => bottomRest settings parameter top b
      (realBatch K circuits settings.mode (prssCtx (dealtKeys parameter seeds pairKeys) kT kP i) parameter) p.1 p.2)
      _ ε fun outs Ks₁ s₁ houts hKs₁ hs₁ hn₁ hle₁ => ?_
  dsimp only
  let h₁ := hashOf prims s₁
  have hg₁ := good_hashOf prims s₁
  have ha₁ := agrees_hashOf prims hn₁
  set W := (bottomJobs b).map fun job => D prims h₁ (evalJob circuits parameter seeds job) with hW
  have hfold : outs.foldlM (fun acc batch => batch.map (acc ++ ·)) [] = some W := by
    rw [houts h₁ s₁ hg₁ le_rfl ha₁, chunks_outputs _ hsize]
  have hW' : ∀ h s', Good prims h → s₁ ≤ s' → Agrees h s' →
      W = (bottomJobs b).map fun job => D prims h (evalJob circuits parameter seeds job) := by
    intro h s' hg hle ha
    have hf := hfold
    rw [houts h s' hg hle ha, chunks_outputs _ hsize] at hf
    exact (Option.some.inj hf).symm
  simp only [bottomRest, hfold]
  refine common_step prims F reply (fuel + Y) _ (FrameR.tweakable _) _ _ s₁ hn₁ ε
    fun root s₂ hr hn₂ hle₂ hfr₂ => ?_
  refine common_step prims F reply (fuel + Y) _ (FrameR.tweakable _) _ _ s₂ hn₂ ε
    fun base s₃ hb hn₃ hle₃ hfr₃ => ?_
  refine common_step prims F reply (fuel + Y) _ (FrameR.tweakable _) _ _ s₃ hn₃ ε
    fun g s₄ hg hn₄ hle₄ hfr₄ => ?_
  have ho₄ : ∀ h s', Good prims h → s₄ ≤ s' → Agrees h s' →
      o₀ = bottomResult prims circuits parameter seeds h top b W root g := by
    intro h s' hgood hle ha
    rw [ho h s' hgood (hle₁.trans (hle₂.trans (hle₃.trans (hle₄.trans hle)))) ha]
    exact ceremonyAt_bottom_values prims circuits parameter seeds h top b W root base g
      (hW' h s' hgood (hle₂.trans (hle₃.trans (hle₄.trans hle))) ha)
      (hr h s' hgood (hle₃.trans (hle₄.trans hle)) ha)
      (hb h s' hgood (hle₄.trans hle) ha) (hg h s' hgood hle ha)
  rcases g with _ | ⟨randomness, encoding⟩
  · have ho' := ho₄ (hashOf prims s₄) s₄ (good_hashOf prims s₄) le_rfl (agrees_hashOf prims hn₄)
    simp only [bottomResult, id_bind_eq, id_pure_eq] at ho'
    rw [ho', honestRounds_failure]
    simp
  · have hs₄ := cacheOK_of_frame (cacheOK_of_frame (cacheOK_of_frame hs₁ hfr₂) hfr₃) hfr₄
    have hfuel : fuel + Y = (fuel + (Y - ((chunks settings.batchSize (signJobs b encoding)).map
        (batchRounds circuits settings.mode parameter)).sum)) +
          ((chunks settings.batchSize (signJobs b encoding)).map (batchRounds circuits settings.mode parameter)).sum := by
      have := hY encoding; omega
    rw [hfuel]
    refine le_trans (chunks_step prims K circuits settings.mode F reply parameter seeds pairKeys kT kP _
      _ _ _ _ Ks₁ le_rfl hKs₁ s₄ hn₄ hs₄ _ (fun _ p => bottomRest2 parameter top b W root randomness p.1)
        _ 0 fun vals Ks₅ s₅ hvals hKs₅ hs₅ hn₅ hle₅ => ?_) (by simpa using hε encoding)
    dsimp only
    let h₅ := hashOf prims s₅
    set V := (signJobs b encoding).map fun job => D prims h₅ (evalJob circuits parameter seeds job) with hV
    have hvfold : vals.foldlM (fun acc batch => batch.map (acc ++ ·)) [] = some V := by
      rw [hvals h₅ s₅ (good_hashOf prims s₅) le_rfl (agrees_hashOf prims hn₅), chunks_outputs _ hsize]
    have hV' : ∀ h s', Good prims h → s₅ ≤ s' → Agrees h s' →
        V = (signJobs b encoding).map fun job => D prims h (evalJob circuits parameter seeds job) := by
      intro h s' hg hle ha
      have hf := hvfold
      rw [hvals h s' hg hle ha, chunks_outputs _ hsize] at hf
      exact (Option.some.inj hf).symm
    simp only [bottomRest2, hvfold]
    refine common_step prims F reply _ _ (FrameR.tweakable _) _ _ s₅ hn₅ 0
      fun path s₆ hp hn₆ hle₆ _ => ?_
    refine common_step prims F reply _ _ (FrameR.tweakable _) _ _ s₆ hn₆ 0
      fun topRoot s₇ ht hn₇ hle₇ _ => ?_
    let h₇ := hashOf prims s₇
    have hgood := good_hashOf prims s₇
    have ha := agrees_hashOf prims hn₇
    have ho' := ho₄ h₇ s₇ hgood (hle₅.trans (hle₆.trans hle₇)) ha
    have hpath := hp h₇ s₇ hgood hle₇ ha
    have htop := ht h₇ s₇ hgood le_rfl ha
    have hval := hV' h₇ s₇ hgood (hle₆.trans hle₇) ha
    unfold bottomResult at ho'
    simp only [id_bind_eq, id_pure_eq] at ho'
    rw [evalRun_eq, ← hval] at ho'
    simp only [] at ho'
    erw [← hpath, ← htop] at ho'
    split_ifs with hbad
    · rw [if_pos hbad] at ho'
      rw [ho', honestRounds_failure]
      simp
    · rw [if_neg hbad] at ho'
      rw [ho', honestRounds_pure]
      simp
end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
variable {C : Committee} (prims : Primitives) (circuits : Circuits) (settings : Settings)

theorem cacheOK_empty : CacheOK (C := C) ∅ 0 ∅ := by
  intro q hq
  exact (hq rfl).elim

theorem idealTree_value (parameter : PublicParameter) (seeds : C.Term → HashOutput) (top : TopTree) (tree : Tree)
    (hsize : 0 < settings.batchSize) (z)
    (hz : z ∈ support ((simulateQ (localAnswer prims) (idealTree circuits settings parameter seeds top tree)).run ∅)) :
    NoMpc z.2 ∧ CacheOK ∅ 0 z.2 ∧ ∃ o₀, z.1 = (fun _ => o₀) ∧
      ∀ h s', Good prims h → z.2 ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top tree := by
  obtain ⟨hle, hn, hsupp⟩ := localRun_support _ ∅ z hz
  have hn' := hn noMpc_empty
  have hfr : FrameL prims (idealTree circuits settings parameter seeds top tree) :=
    FrameL.liftComp ((FrameR.dealerCeremony prims circuits settings parameter seeds top tree).map _)
  refine ⟨hn', cacheOK_of_frame cacheOK_empty (hfr ∅ z hz), ?_⟩
  have hval : ∀ h s', Good prims h → z.2 ≤ s' → Agrees h s' →
      z.1 = fun _ => ceremonyAt prims circuits parameter seeds h top tree := by
    intro h s' hg hle' ha
    have hv := hsupp h hg (ha.mono hle')
    simp only [idealTree, simulateQ_fixedLocal_liftComp, D_map, support_pure, Set.mem_singleton_iff] at hv
    rw [D_dealerCeremony prims circuits settings parameter seeds h top tree hsize] at hv
    exact hv
  let h₀ := hashOf prims z.2
  have heq := hval h₀ z.2 (good_hashOf prims z.2) le_rfl (agrees_hashOf prims hn')
  refine ⟨ceremonyAt prims circuits parameter seeds h₀ top tree, heq, ?_⟩
  intro h s' hg hle' ha
  have e := hval h s' hg hle' ha
  rw [heq] at e
  exact congrFun e ⟨0, by have := C.one_le_t; simp only [Committee.n]; omega⟩
end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ
variable (circuits : Circuits) (settings : Settings)

theorem measure_le_maxBatch (measure : List Circuit → ℕ) (parameter : PublicParameter)
    (b : Fin (2 ^ layerHeight)) (enc : Encoding) (jobs : List Job)
    (hj : jobs ∈ chunks settings.batchSize topJobs ∨ jobs ∈ chunks settings.batchSize (bottomJobs b) ∨
      jobs ∈ chunks settings.batchSize (signJobs b enc)) :
    measure (runCircuits circuits parameter jobs) ≤ maxBatch circuits settings measure := by
  unfold maxBatch
  refine Finset.le_sup_of_le (b := (parameter, b, enc)) (s := Finset.univ)
    (f := fun x : PublicParameter × Fin (2 ^ layerHeight) × Encoding =>
      (([topJobs, bottomJobs x.2.1, signJobs x.2.1 x.2.2].flatMap (chunks settings.batchSize)).map
        fun js => measure (runCircuits circuits x.1 js)).foldl max 0) ?_ ?_
  · apply Finset.mem_univ
  apply (le_foldl_max _ 0).2
  apply List.mem_map.mpr
  refine ⟨jobs, ?_, rfl⟩
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] using hj

theorem length_chunks {α : Type} (size : ℕ) (js : List α) :
    (chunks size js).length = (js.length + size - 1) / size := by
  simp only [chunks, List.length_map, List.length_range]

theorem length_bottomJobs (b : Fin (2 ^ layerHeight)) :
    (bottomJobs b).length = (bottomJobs (0 : Fin (2 ^ layerHeight))).length := by
  simp [bottomJobs, List.length_flatMap]

theorem length_signJobs (b b' : Fin (2 ^ layerHeight)) (enc enc' : Encoding) :
    (signJobs b enc).length = (signJobs b' enc').length := by
  simp only [signJobs, List.length_map]

theorem length_chunks_signJobs (b b' : Fin (2 ^ layerHeight)) (enc enc' : Encoding) :
    (chunks settings.batchSize (signJobs b enc)).length =
      (chunks settings.batchSize (signJobs b' enc')).length := by
  rw [length_chunks, length_chunks, length_signJobs b b' enc enc']

theorem treeBatches_le_ceremonyBatches (tree : Tree) : treeBatches settings tree ≤ ceremonyBatches settings := by
  cases tree with
  | top => exact le_max_left _ _
  | bottom b =>
    simp only [treeBatches, ceremonyBatches]
    rw [length_chunks_signJobs settings b 0 (fun _ => digit 0) (fun _ => digit 0)]
    simp only [length_chunks, length_bottomJobs]
    exact le_max_right _ _

theorem sum_map_le_length_mul {α : Type} (f : α → ℕ) (l : List α) (R : ℕ) (h : ∀ x ∈ l, f x ≤ R) :
    (l.map f).sum ≤ l.length * R := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
    have hx := h x (List.mem_cons_self ..)
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem batchRounds_le_runRounds (mode : ReshareMode) (parameter : PublicParameter) (jobs : List Job) :
    batchRounds circuits mode parameter jobs ≤ runRounds mode (runCircuits circuits parameter jobs) := by
  unfold batchRounds batchCount checkLabels runRounds runCircuits
  split_ifs <;> omega

theorem chunks_rounds_le (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (enc : Encoding)
    (js : List (List Job))
    (hj : ∀ jobs ∈ js, jobs ∈ chunks settings.batchSize topJobs ∨ jobs ∈ chunks settings.batchSize (bottomJobs b) ∨
      jobs ∈ chunks settings.batchSize (signJobs b enc)) :
    (js.map (batchRounds circuits settings.mode parameter)).sum ≤
      js.length * maxBatch circuits settings (runRounds settings.mode) :=
  sum_map_le_length_mul _ _ _ fun jobs hmem =>
    (batchRounds_le_runRounds circuits settings.mode parameter jobs).trans
      (measure_le_maxBatch circuits settings _ parameter b enc jobs (hj jobs hmem))

variable {E : Type} [Fintype E]

def chunksBudget (E : Type) [Fintype E] (R B c : ℕ) : ℝ≥0∞ :=
  (((c + B * (R + 2)) ^ 2 - c ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 + B * freshCost E R

theorem checkKeys_le (cnt R : ℕ) (h : halvings cnt ≤ R) : checkKeys cnt ≤ R + 2 := by
  unfold checkKeys
  split_ifs <;> omega

theorem chunks_keys_le (parameter : PublicParameter) (R : ℕ) (js : List (List Job))
    (h : ∀ jobs ∈ js, halvings (batchCount circuits parameter jobs) ≤ R) :
    (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum ≤ js.length * (R + 2) :=
  sum_map_le_length_mul _ _ _ fun jobs hj => checkKeys_le _ _ (h jobs hj)

theorem chunksCost_le_budget (parameter : PublicParameter) (R B c : ℕ) (js : List (List Job))
    (hB : js.length ≤ B) (h : ∀ jobs ∈ js, halvings (batchCount circuits parameter jobs) ≤ R) :
    chunksCost circuits E parameter c js ≤ chunksBudget E R B c := by
  refine (chunksCost_le circuits parameter R js c h).trans ?_
  unfold chunksBudget
  have hkeys := (chunks_keys_le circuits parameter R js h).trans (Nat.mul_le_mul_right (R + 2) hB)
  gcongr

theorem chunksCost_prefix_budget (parameter : PublicParameter) (R B : ℕ) (js : List (List Job))
    (h : ∀ jobs ∈ js, halvings (batchCount circuits parameter jobs) ≤ R) :
    chunksCost circuits E parameter 0 js +
      chunksBudget E R B ((js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum) ≤
        chunksBudget E R (js.length + B) 0 := by
  refine (add_le_add (chunksCost_le (E := E) circuits parameter R js 0 h) le_rfl).trans ?_
  set c := (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum
  have hsq : c ^ 2 ≤ (c + B * (R + 2)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have heq : c ^ 2 + ((c + B * (R + 2)) ^ 2 - c ^ 2) = (c + B * (R + 2)) ^ 2 := by omega
  unfold chunksBudget
  simp only [zero_add, zero_pow (by omega : 2 ≠ 0), Nat.sub_zero]
  calc
    (c ^ 2 : ℕ) / (2 : ℝ≥0∞) ^ 257 + js.length * freshCost E R +
        (((c + B * (R + 2)) ^ 2 - c ^ 2 : ℕ) / (2 : ℝ≥0∞) ^ 257 + B * freshCost E R)
      = ((c + B * (R + 2)) ^ 2 : ℕ) / (2 : ℝ≥0∞) ^ 257 + (js.length + B) * freshCost E R := by
        calc _ = ((↑(c ^ 2) + (↑((c + B * (R + 2)) ^ 2 - c ^ 2 : ℕ) : ℝ≥0∞)) / (2 : ℝ≥0∞) ^ 257) +
            (↑js.length + ↑B) * freshCost E R := by rw [← ENNReal.div_add_div_same]; ring
          _ = _ := by rw [← Nat.cast_add, heq]
    _ ≤ _ := by
      have hc := chunks_keys_le circuits parameter R js h
      have hc' : c + B * (R + 2) ≤ (js.length + B) * (R + 2) := by
        dsimp only [c]; rw [Nat.add_mul]; omega
      gcongr
      all_goals first | exact hc' | simp only [Nat.cast_add, le_refl]

theorem freshCost_ne_top [Nonempty E] (R : ℕ) : freshCost E R ≠ ⊤ := by
  have hc : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd : (2 : ℝ≥0∞) / Fintype.card E ≠ ⊤ := ENNReal.div_ne_top (by simp) hc
  unfold freshCost
  finiteness

theorem chunksBudget_ne_top [Nonempty E] (R B c : ℕ) : chunksBudget E R B c ≠ ⊤ := by
  unfold chunksBudget
  have := freshCost_ne_top (E := E) R
  finiteness

theorem freshCost_toReal [Nonempty E] (R : ℕ) :
    (freshCost E R).toReal = (sliceBits : ℝ) / Fintype.card E + (R + 1 : ℕ) * (2 / Fintype.card E : ℝ) ^ challengeTries := by
  have hc : (Fintype.card E : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hd : (2 : ℝ≥0∞) / Fintype.card E ≠ ⊤ := ENNReal.div_ne_top (by simp) hc
  unfold freshCost
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul]

theorem chunksBudget_toReal [Nonempty E] (tree : Tree) :
    (chunksBudget E (maxBatch circuits settings fun js => halvings (tupleCount js))
      (treeBatches settings tree) 0).toReal = treeAbortError (E := E) circuits settings tree := by
  have hf := freshCost_ne_top (E := E) (maxBatch circuits settings fun js => halvings (tupleCount js))
  unfold chunksBudget treeAbortError coinFailure coinKeyCollision
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, ENNReal.toReal_mul, zero_add, zero_pow (by omega : 2 ≠ 0), Nat.sub_zero, freshCost_toReal]
  ring
end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal Finset
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ D
variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

theorem ceremony_body_bound [Nonempty C.Party] {L R : Type} (F : Functionality C PEmpty PEmpty L R) (reply : L → R)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput)
    (kT : C.Term → HashOutput) (kP : C.Pair → HashOutput) (top : TopTree) (tree : Tree) (o₀ : Option TreeOutput)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s)
    (ho : ∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top tree)
    (hsize : 0 < settings.batchSize) :
    Pr[(· ≠ fun _ => o₀) | (simulateQ (localAnswer prims)
      (honestStart (fun i => ceremonyBody K circuits settings parameter seeds pairKeys kT kP top tree i) >>=
        honestRounds F reply (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)))).run' s] ≤
      chunksBudget E (maxBatch circuits settings fun js => halvings (tupleCount js)) (treeBatches settings tree) 0 := by
  let M := maxBatch circuits settings (runRounds settings.mode)
  let H := maxBatch circuits settings fun js => halvings (tupleCount js)
  have hround := chunks_rounds_le circuits settings parameter
  have hhalves : ∀ b enc jobs,
      (jobs ∈ chunks settings.batchSize topJobs ∨ jobs ∈ chunks settings.batchSize (bottomJobs b) ∨
        jobs ∈ chunks settings.batchSize (signJobs b enc)) → halvings (batchCount circuits parameter jobs) ≤ H := by
    intro b enc jobs hj
    exact measure_le_maxBatch circuits settings (fun js => halvings (tupleCount js)) parameter b enc jobs hj
  cases tree with
  | top =>
    let js := chunks settings.batchSize topJobs
    let X := (js.map (batchRounds circuits settings.mode parameter)).sum
    have hx : X ≤ ceremonyBatches settings * M :=
      (hround 0 (fun _ => digit 0) js (fun jobs hj => Or.inl hj)).trans
        (Nat.mul_le_mul_right M (treeBatches_le_ceremonyBatches settings .top))
    have hfuel : ceremonyBatches settings * M = (ceremonyBatches settings * M - X) + X := by omega
    change Pr[(· ≠ fun _ => o₀) | (simulateQ (localAnswer prims)
      (honestStart (fun i => ceremonyBody K circuits settings parameter seeds pairKeys kT kP top .top i) >>=
        honestRounds F reply (ceremonyBatches settings * M))).run' s] ≤ _
    rw [hfuel]
    refine (top_body_bound prims K circuits settings F reply parameter seeds pairKeys kT kP top o₀ s hn hs ho hsize
      (ceremonyBatches settings * M - X)).trans ?_
    exact chunksCost_le_budget circuits parameter H js.length 0 js le_rfl
      (fun jobs hj => hhalves 0 (fun _ => digit 0) jobs (Or.inl hj))
  | bottom b =>
    let js := chunks settings.batchSize (bottomJobs b)
    let B := (chunks settings.batchSize (signJobs b fun _ => digit 0)).length
    let X := (js.map (batchRounds circuits settings.mode parameter)).sum
    let Y := B * M
    let c := (js.map fun jobs => checkKeys (batchCount circuits parameter jobs)).sum
    have hX : X ≤ js.length * M := hround b (fun _ => digit 0) js (fun jobs hj => Or.inr (Or.inl hj))
    have hY : ∀ enc, ((chunks settings.batchSize (signJobs b enc)).map
        (batchRounds circuits settings.mode parameter)).sum ≤ Y := by
      intro enc
      have h := hround b enc (chunks settings.batchSize (signJobs b enc)) (fun jobs hj => Or.inr (Or.inr hj))
      rw [length_chunks_signJobs settings b b enc (fun _ => digit 0)] at h
      exact h
    have hXY : X + Y ≤ ceremonyBatches settings * M := by
      calc X + Y ≤ js.length * M + B * M := add_le_add hX le_rfl
        _ = (treeBatches settings (.bottom b)) * M := by change js.length * M + B * M = (js.length + B) * M; ring
        _ ≤ _ := Nat.mul_le_mul_right M (treeBatches_le_ceremonyBatches settings (.bottom b))
    have hfuel : ceremonyBatches settings * M = (ceremonyBatches settings * M - (X + Y)) + Y + X := by omega
    change Pr[(· ≠ fun _ => o₀) | (simulateQ (localAnswer prims)
      (honestStart (fun i => ceremonyBody K circuits settings parameter seeds pairKeys kT kP top (.bottom b) i) >>=
        honestRounds F reply (ceremonyBatches settings * M))).run' s] ≤ _
    rw [hfuel]
    refine (bottom_body_bound (prims := prims) (K := K) (circuits := circuits) (settings := settings)
      F reply parameter seeds pairKeys kT kP top b o₀ s hn hs ho hsize (ceremonyBatches settings * M - (X + Y)) Y
        (chunksBudget E H B c) hY ?_).trans ?_
    · intro enc
      exact chunksCost_le_budget circuits parameter H B c (chunks settings.batchSize (signJobs b enc))
        (le_of_eq (length_chunks_signJobs settings b b enc (fun _ => digit 0)))
        (fun jobs hj => hhalves b enc jobs (Or.inr (Or.inr hj)))
    · exact chunksCost_prefix_budget circuits parameter H B js
        (fun jobs hj => hhalves b (fun _ => digit 0) jobs (Or.inr (Or.inl hj)))

theorem realTree_bound [Nonempty C.Party] (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairKeys : C.Pair → HashOutput) (top : TopTree) (tree : Tree) (o₀ : Option TreeOutput)
    (s : HashCache C) (hn : NoMpc s) (hs : CacheOK ∅ 0 s)
    (ho : ∀ h s', Good prims h → s ≤ s' → Agrees h s' → o₀ = ceremonyAt prims circuits parameter seeds h top tree)
    (hsize : 0 < settings.batchSize) :
    Pr[(· ≠ fun _ => o₀) | (simulateQ (localAnswer prims)
      (realTree K circuits settings top tree parameter seeds pairKeys)).run' s] ≤
      chunksBudget E (maxBatch circuits settings fun js => halvings (tupleCount js)) (treeBatches settings tree) 0 := by
  unfold realTree
  simp only [ceremony_eq]
  rw [show ceremonyFuel circuits settings =
    (ceremonyBatches settings * maxBatch circuits settings (runRounds settings.mode)) + 3 by
      unfold ceremonyFuel setupRounds; omega]
  refine setup_step prims noFunctionality (fun l => l.elim) _ _ _ s hn _
    fun kT kP s' hn' hle hfr => ?_
  simp only [ceremonyRest_honest]
  exact ceremony_body_bound prims K circuits settings noFunctionality (fun l => l.elim)
    parameter seeds pairKeys kT kP top tree o₀ s' hn' (cacheOK_of_frame hs hfr)
      (fun h s'' hg hle' ha => ho h s'' hg (hle.trans hle') ha) hsize

theorem jointTreeRun_bound [Nonempty C.Party] (top : TopTree) (tree : Tree) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairKeys : C.Pair → HashOutput) (hsize : 0 < settings.batchSize) :
    Pr[fun p => p.1 ≠ p.2 | jointTreeRun prims K circuits settings top tree parameter seeds pairKeys] ≤
      chunksBudget E (maxBatch circuits settings fun js => halvings (tupleCount js)) (treeBatches settings tree) 0 := by
  unfold jointTreeRun
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine probEvent_bind_le_of_forall_le fun z hz => ?_
  obtain ⟨hn, hs, o₀, heq, ho⟩ := idealTree_value prims circuits settings parameter seeds top tree hsize z hz
  have hbound := realTree_bound prims K circuits settings parameter seeds pairKeys top tree o₀ z.2 hn hs ho hsize
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    map_bind, map_pure, heq]
  rw [bind_pure_comp, probEvent_map]
  simpa only [StateT.run'_eq, probEvent_map, Function.comp_def] using hbound

/-- Every honest tree ceremony agrees with the dealer, up to the stated abort bound. -/
theorem treeCompleteness : TreeCompletenessStatement prims K circuits settings := by
  letI : Nonempty C.Party := ⟨⟨0, by have := C.one_le_t; simp only [Committee.n]; omega⟩⟩
  refine treeCompleteness_of_joint prims K circuits settings fun hsize top tree parameter seeds pairKeys => ?_
  have hbound := jointTreeRun_bound prims K circuits settings top tree parameter seeds pairKeys hsize
  have hreal := ENNReal.toReal_mono (chunksBudget_ne_top (E := E)
    (maxBatch circuits settings fun js => halvings (tupleCount js)) (treeBatches settings tree) 0) hbound
  rwa [chunksBudget_toReal circuits settings tree] at hreal

end ThresholdLeanXmssSecurity
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section TreeQueryBound

variable {C : Committee} {E : Type} (prims : Primitives)

/-- A simulation into a state over the world whose every step costs nothing costs nothing. -/
theorem costLe_stateT_simulateQ {ι' σ : Type} {spec' : OracleSpec ι'}
    (h : QueryImpl spec' (StateT σ (OracleComp (WorldSpec C))))
    (hh : ∀ t st, CostLe prims ((h t).run st) 0) {α : Type} (p : OracleComp spec' α) :
    ∀ st, CostLe prims ((simulateQ h p).run st) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => intro st; exact CostLe.pure prims _
  | query_bind t k ih =>
    intro st
    rw [simulateQ_bind, simulateQ_query, StateT.run_bind]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    exact ((hh t st).bind prims fun p => ih p.1 p.2).mono prims (by simp)

/-- A computation of `H` and `PRG` inside a functionality runs on the free copy. -/
theorem costLe_liftComp_ro {σ L R α : Type} (g : QueryImpl (L →ₒ R) (StateT σ (OracleComp (WorldSpec C))))
    (p : OracleComp (RoSpec C) α) : ∀ st : σ,
    CostLe prims ((simulateQ (((fun t => StateT.lift (free (C := C) (OracleComp.lift (OracleSpec.query t)))) :
      QueryImpl (LocalSpec C) (StateT σ (OracleComp (WorldSpec C)))) + g)
        (liftComp p (LocalSpec C + (L →ₒ R)))).run st) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => intro st; exact CostLe.pure prims _
  | query_bind t k ih =>
    intro st
    rw [liftComp_bind, simulateQ_bind, StateT.run_bind]
    have : simulateQ (((fun t => StateT.lift (free (C := C) (OracleComp.lift (OracleSpec.query t)))) :
        QueryImpl (LocalSpec C) (StateT σ (OracleComp (WorldSpec C)))) + g)
        (liftComp (liftM (OracleSpec.query t) : OracleComp (RoSpec C) _) (LocalSpec C + (L →ₒ R))) =
        StateT.lift (free (C := C) (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (Sum.inr t)))) := by
      rw [liftComp_def, simulateQ_query]
      simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
      erw [simulateQ_query]
      rcases t with q | x <;> rfl
    rw [this]
    exact (((CostLe.free prims _).bind prims fun _ => CostLe.pure prims _).bind prims
      fun (p : (RoSpec C).Range t × σ) => ih p.1 p.2).mono prims (by simp)

/-- The emulation monad pays what its runs pay from every stream cache. -/
def CostLeE {α : Type} (x : EmulationM C α) (n : ℕ) : Prop := ∀ s, CostLe prims ((x.run s).run) n

theorem CostLeE.mono {α : Type} {x : EmulationM C α} {n m : ℕ} (h : CostLeE prims x n) (hnm : n ≤ m) :
    CostLeE prims x m := fun s => (h s).mono prims hnm

theorem CostLeE.bind {α β : Type} {x : EmulationM C α} {f : α → EmulationM C β} {n m : ℕ}
    (hx : CostLeE prims x n) (hf : ∀ a, CostLeE prims (f a) m) : CostLeE prims (x >>= f) (n + m) := fun s => by
  rw [StateT.run_bind]
  exact CostLe.writer_bind prims _ _ (hx s) fun p => hf p.1 p.2

theorem CostLeE.pure {α : Type} (a : α) : CostLeE prims (Pure.pure a : EmulationM C α) 0 := fun _ =>
  CostLe.writer_pure prims _

theorem CostLeE.lift {α : Type} (w : WriterT (CallLog C) (OracleComp (WorldSpec C)) α) {n : ℕ}
    (h : CostLe prims w.run n) : CostLeE prims (StateT.lift w : EmulationM C α) n := fun s => by
  change CostLe prims ((w >>= fun a => Pure.pure (a, s)).run) n
  exact (CostLe.writer_bind prims _ _ h fun a => CostLe.writer_pure prims _).mono prims (by simp)

theorem CostLeE.sequenceFin {α : Type} : ∀ {n : ℕ} (f : Fin n → EmulationM C α),
    (∀ i, CostLeE prims (f i) 0) → CostLeE prims (Concrete.sequenceFin f) 0
  | 0, f, _ => CostLeE.pure prims _
  | n + 1, f, h => by
    simp only [Concrete.sequenceFin]
    exact ((h 0).bind prims fun a => ((CostLeE.sequenceFin (fun i : Fin n => f i.succ) fun i => h i.succ).bind
      prims fun rest => CostLeE.pure prims _)).mono prims (by simp)

theorem CostLeE.simulateQ (impl : QueryImpl (LocalSpec C) (EmulationM C)) (himpl : ∀ t, CostLeE prims (impl t) 0)
    {α : Type} (oa : OracleComp (LocalSpec C) α) : CostLeE prims (simulateQ impl oa) 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => exact CostLeE.pure prims _
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_query]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    exact ((himpl t).bind prims fun p => ih p).mono prims (by simp)

/-- The emulated honest operators run on the free copy. -/
theorem CostLeE.honest (D : C.Coalition) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    CostLeE prims ((emulatedRoles D).honest oa) 0 := by
  refine CostLeE.simulateQ prims _ (fun t => ?_) oa
  rcases t with u | q | x
  · exact CostLeE.lift prims _ (CostLe.writer_liftM prims _ (CostLe.free prims _))
  · exact CostLeE.lift prims _ (CostLe.writer_liftM prims _ (CostLe.free prims _))
  · dsimp only
    split_ifs
    · exact fun s => CostLe.writer_liftM prims _ (CostLe.free prims _)
    · exact CostLeE.lift prims _ (CostLe.writer_liftM prims _ (CostLe.free prims _))

/-- The observed adversary costs what it costs on the counted copy. -/
theorem CostLeE.adversary (D : C.Coalition) {α : Type} (oa : OracleComp (LocalSpec C) α) (n : ℕ)
    (h : IsQueryBoundP oa Counted n) : CostLeE prims ((emulatedRoles D).adversary oa) n :=
  CostLeE.lift prims _ (CostLe.observe prims oa n h)

theorem CostLeE.stepRound_emulated {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    CostLeE prims (stepRound (emulatedRoles D) D A noFunctionality state steps) step := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real])]
  refine ((CostLeE.adversary prims D _ step (hround _ _)).bind prims fun p =>
    ((CostLeE.sequenceFin prims _ fun j => ?_).bind prims fun steps' => CostLeE.pure prims _)).mono prims (by simp)
  split
  · exact CostLeE.pure prims _
  · split_ifs
    · exact CostLeE.pure prims _
    · exact CostLeE.honest prims D _
  · exact CostLeE.pure prims _

theorem CostLeE.executeRounds_emulated {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec α),
      CostLeE prims (executeRounds (emulatedRoles D) D A noFunctionality fuel state steps) (fuel * step)
  | 0, state, steps => by
    rw [Nat.zero_mul]
    exact CostLeE.pure prims _
  | fuel + 1, state, steps => by
    unfold executeRounds
    split_ifs
    · exact (CostLeE.pure prims _).mono prims (Nat.zero_le _)
    · exact ((CostLeE.stepRound_emulated prims D A step hround state steps).bind prims fun p =>
        CostLeE.executeRounds_emulated D A step hround fuel _ _).mono prims (by rw [Nat.succ_mul, Nat.add_comm])

theorem CostLeE.executePhase_emulated {Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) :
    CostLeE prims (executePhase (emulatedRoles D) D A noFunctionality fuel state program) (fuel * step) := by
  unfold executePhase startSteps
  refine ((CostLeE.sequenceFin prims _ fun i => ?_).bind prims fun steps =>
    CostLeE.executeRounds_emulated prims D A step hround fuel state steps).mono prims (by simp)
  split_ifs
  · exact CostLeE.pure prims _
  · exact CostLeE.honest prims D _

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- One answer of `treeSimulator` costs the rounds of the adversary in the emulated ceremony. -/
theorem costLe_treeSimulator_answer (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (st : (treeSimulator K circuits settings top tree D A).State)
    (l : PublicParameter × List (List (List Bit))) :
    CostLe prims ((treeSimulator K circuits settings top tree D A).answer st l)
      (ceremonyFuel circuits settings * step) := by
  rcases l with ⟨parameter, openings⟩
  unfold treeSimulator
  dsimp only
  exact ((CostLeE.executePhase_emulated prims D A step hround _ _ _ ∅).bind prims fun _ => CostLe.pure prims _).mono
    prims (by simp)

theorem treeSimulator_queryBound (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) :
    HasHashQueryBound (runWorld prims (distinguish (idealExecution (fun oa => oa) D
      (Ftree circuits settings top tree) (treeSimulator K circuits settings top tree D A) x z) Z)) (q + 0) := by
  obtain ⟨start, step, final, hsum, hs, hr, ha, hz⟩ := hq
  apply hasHashQueryBound_of_costLe
  unfold distinguish idealExecution
  simp only [bind_assoc]
  have hstart : CostLe prims ((treeSimulator K circuits settings top tree D A).start (corruptInputs D x) z) start :=
    ((CostLe.observe prims _ start (hs _ _)).bind prims fun _ => CostLe.pure prims _).mono prims (by simp)
  have hanswer := costLe_treeSimulator_answer prims K circuits settings top tree D A step hr
  refine CostLe.mono prims (CostLe.bind prims hstart
    (m := 0 + ((ceremonyFuel circuits settings * step + 0) + (0 + (0 + (0 + final))))) fun st => ?_) ?_
  · unfold Ftree
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    refine CostLe.bind prims (n := 0) ?_ fun p => ?_
    · exact costLe_liftComp_ro prims _ _ st
    refine (costLe_simulateQ_leak prims _ _ _ ?hl).bind prims fun r => ?_
    case hl => exact (hanswer _ _).bind prims fun _ => CostLe.pure prims _
    refine (CostLe.pure prims _).bind prims fun out => ?_
    refine (CostLe.pure prims _).bind prims fun o => ?_
    refine (CostLe.pure prims _).bind prims fun r' => ?_
    exact CostLe.of_counted prims _ _ (hz _)
  · simp only [Nat.zero_add, Nat.add_zero]
    omega

/-- The distance half of `TreeSecurityStatement`. -/
def TreeSecurityDistance (K : Constants C E) (circuits : Circuits) (settings : Settings) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    |accepts prims (distinguish (realExecution D A noFunctionality (ceremonyFuel circuits settings)
        (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput)) x z) Z) -
      accepts prims (distinguish (idealExecution (fun oa => oa) D (Ftree circuits settings top tree)
        (treeSimulator K circuits settings top tree D A) x z) Z)| ≤
      treeCheckError (E := E) circuits settings tree q + treeHashError circuits settings C tree q +
        streamKeyError C +
        PRFScheme.prfAdvantage (hiddenStreams prims.aes) (prgReduction prims D
          (distinguish (realExecution D A noFunctionality (ceremonyFuel circuits settings)
            (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput)) x z) Z))

/-- `TreeSecurityStatement` from its distance half. The query half is `treeSimulator_queryBound`. -/
theorem treeSecurity_of_distance (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (h : TreeSecurityDistance prims K circuits settings) :
    TreeSecurityStatement prims K circuits settings := fun hb top tree D A x z Z q hx hq =>
  ⟨treeSimulator_queryBound prims K circuits settings top tree D A x z Z q hq,
    h hb top tree D A x z Z q hx hq⟩

end TreeQueryBound

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Reduction
variable {C : Committee} {E : Type} (prims : Primitives) [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The probability that `prgReduction` outputs `1` against the real streams. -/
def reductionReal (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) : ℝ :=
  (Pr[= true | (hiddenStreams (C := C) prims.aes).prfRealExp (prgReduction prims D game)]).toReal

/-- The probability that `prgReduction` outputs `1` against a random function. -/
def reductionIdeal (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) : ℝ :=
  (Pr[= true | PRFScheme.prfIdealExp (prgReduction prims D game)]).toReal

theorem abs_sub_le_of_hops (D : C.Coalition) (real ideal : OracleComp (WorldSpec C) Bool) (a b : ℝ)
    (h₁ : |accepts prims real - reductionReal prims D real| ≤ a)
    (h₂ : |reductionIdeal prims D real - accepts prims ideal| ≤ b) :
    |accepts prims real - accepts prims ideal| ≤
      a + b + PRFScheme.prfAdvantage (hiddenStreams prims.aes) (prgReduction prims D real) := by
  have h₃ : |reductionReal prims D real - reductionIdeal prims D real| =
      PRFScheme.prfAdvantage (hiddenStreams prims.aes) (prgReduction prims D real) := rfl
  calc |accepts prims real - accepts prims ideal|
      = |(accepts prims real - reductionReal prims D real) + (reductionReal prims D real -
          reductionIdeal prims D real) + (reductionIdeal prims D real - accepts prims ideal)| := by ring_nf
    _ ≤ |accepts prims real - reductionReal prims D real| + |reductionReal prims D real -
          reductionIdeal prims D real| + |reductionIdeal prims D real - accepts prims ideal| :=
        abs_add_three _ _ _
    _ ≤ a + b + _ := by rw [h₃]; linarith

end Reduction

section Fuse
variable {ι κ : Type} {spec : OracleSpec ι} {spec₂ : OracleSpec κ} {σ τ : Type}

/-- One handler into a state over the oracles of an outer handler, as one handler on both states. -/
def fuse (inner : QueryImpl spec (StateT σ (OracleComp spec₂))) (outer : QueryImpl spec₂ (StateT τ ProbComp)) :
    QueryImpl spec (StateT (σ × τ) ProbComp) := fun q => StateT.mk fun st =>
  (fun r => (r.1.1, (r.1.2, r.2))) <$> (simulateQ outer ((inner q).run st.1)).run st.2

theorem run_simulateQ_fuse (inner : QueryImpl spec (StateT σ (OracleComp spec₂)))
    (outer : QueryImpl spec₂ (StateT τ ProbComp)) {α : Type} (oa : OracleComp spec α) (s : σ) (t : τ) :
    (simulateQ outer ((simulateQ inner oa).run s)).run t =
      (fun r => ((r.1, r.2.1), r.2.2)) <$> (simulateQ (fuse inner outer) oa).run (s, t) := by
  induction oa using OracleComp.inductionOn generalizing s t with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, map_bind]
    simp only [fuse, StateT.run_mk, bind_map_left]
    refine bind_congr fun r => ?_
    exact ih r.1.1 r.1.2 r.2

/-- One handler into a state over the oracles of a stateless outer handler. -/
def fuseStateless (inner : QueryImpl spec (StateT σ (OracleComp spec₂))) (outer : QueryImpl spec₂ ProbComp) :
    QueryImpl spec (StateT σ ProbComp) := fun q => StateT.mk fun s => simulateQ outer ((inner q).run s)

theorem simulateQ_run_fuseStateless (inner : QueryImpl spec (StateT σ (OracleComp spec₂)))
    (outer : QueryImpl spec₂ ProbComp) {α : Type} (oa : OracleComp spec α) (s : σ) :
    simulateQ outer ((simulateQ inner oa).run s) = (simulateQ (fuseStateless inner outer) oa).run s := by
  induction oa using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind]
    simp only [fuseStateless, StateT.run_mk]
    exact bind_congr fun r => ih r.1 r.2

end Fuse

attribute [local instance] Classical.propDecidable

section StreamWorld
variable {C : Committee} (prims : Primitives)

/-- The cache of a random function on the streams under the hidden keys. -/
abbrev HiddenCache (C : Committee) := (((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).QueryCache

/-- A handler of the hash cache on the first component. -/
def onHash {α : Type} (m : StateT (HashCache C) ProbComp α) : StateT (HashCache C × HiddenCache C) ProbComp α :=
  StateT.mk fun st => (fun r => (r.1, (r.2, st.2))) <$> m.run st.1

/-- The world where each free stream under a hidden key is a random function. -/
def streamWorld (D : C.Coalition) : QueryImpl (WorldSpec C) (StateT (HashCache C × HiddenCache C) ProbComp) :=
  fun t => match t with
  | .inl t => onHash ((localAnswer (C := C) prims + programAnswer (C := C)) t)
  | .inr (.inr (.inr x)) => if Hidden D x.1 then StateT.mk fun st =>
        (fun r => (r.1, (st.1, r.2))) <$>
          ((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle ((x.1, x.2.1), x.2.2)).run st.2
      else onHash (localAnswer prims (.inr (.inr x)))
  | .inr t => onHash (localAnswer prims t)

theorem prfIdealExp_prgReduction (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) :
    PRFScheme.prfIdealExp (prgReduction prims D game) = (simulateQ (streamWorld prims D) game).run' (∅, ∅) := by
  unfold PRFScheme.prfIdealExp prgReduction
  simp only [StateT.run'_eq, simulateQ_map, StateT.run_map, run_simulateQ_fuse, Functor.map_map]
  have hl : ∀ {β : Type} (ob : ProbComp β), simulateQ PRFScheme.prfIdealQueryImpl
      (liftM ob : OracleComp (StreamSpec C) β) = liftM ob := fun ob =>
    PRFScheme.simulateQ_prfIdealQueryImpl_liftComp ob
  rw [show fuse _ PRFScheme.prfIdealQueryImpl = streamWorld prims D from ?_]
  funext t
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals simp only [fuse, streamWorld, onHash]
  all_goals try split_ifs
  all_goals congr 1
  all_goals funext st
  case pos h =>
    simp only [QueryImpl.add_apply_inr, if_pos h, simulateQ_bind, simulateQ_pure,
      PRFScheme.simulateQ_prfIdealQueryImpl_inr, StateT.run_bind, StateT.run_pure, map_bind]
    simp [StateT.run_bind]
    rfl
  case neg h =>
    simp only [QueryImpl.add_apply_inr]
    rw [if_neg h]
    simp [hl, Functor.map_map]
  all_goals first | (simp [hl, Functor.map_map]; done) | (simp [hl, Functor.map_map]; rfl)

/-- The world where each free stream under a hidden key uses its own AES key. -/
def keyWorld (D : C.Coalition) (keys : KeyName C × HashOutput → Digest) :
    QueryImpl (WorldSpec C) (StateT (HashCache C) ProbComp) :=
  fun t => match t with
  | .inl t => (localAnswer (C := C) prims + programAnswer (C := C)) t
  | .inr (.inr (.inr x)) => if Hidden D x.1 then pure (prims.aes.eval (keys (x.1, x.2.1)) x.2.2)
      else localAnswer prims (.inr (.inr x))
  | .inr t => localAnswer prims t

theorem prfRealExp_prgReduction (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) :
    (hiddenStreams (C := C) prims.aes).prfRealExp (prgReduction prims D game) =
      ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys => (simulateQ (keyWorld prims D keys) game).run' ∅ := by
  unfold PRFScheme.prfRealExp prgReduction
  refine bind_congr fun keys => ?_
  simp only [StateT.run'_eq, simulateQ_map, simulateQ_run_fuseStateless]
  have hl : ∀ {β : Type} (ob : ProbComp β), simulateQ ((hiddenStreams (C := C) prims.aes).prfRealQueryImpl keys)
      (liftM ob : OracleComp (StreamSpec C) β) = ob := fun ob =>
    PRFScheme.simulateQ_prfRealQueryImpl_liftComp _ _ ob
  rw [show fuseStateless _ (PRFScheme.prfRealQueryImpl _ keys) = keyWorld prims D keys from ?_]
  funext t
  rcases t with ((u | q | x) | p) | (u | q | x)
  all_goals simp only [fuseStateless, keyWorld]
  all_goals try split_ifs
  case pos h =>
    simp only [QueryImpl.add_apply_inr]
    rw [if_pos h]
    refine StateT.ext fun s => ?_
    simp [StateT.run_lift, hiddenStreams]
    rfl
  case neg h =>
    simp only [QueryImpl.add_apply_inr]
    rw [if_neg h]
    refine StateT.ext fun s => ?_
    simp [hl]
  all_goals refine StateT.ext fun s => ?_
  all_goals first | (simp [hl]; done) | (simp [hl]; rfl)

/-- The cache of a lazy table of AES keys for the hidden key names. -/
abbrev KeyCache (C : Committee) := ((KeyName C × HashOutput) →ₒ Digest).QueryCache

/-- `keyWorld` with the table of AES keys sampled lazily. -/
def lazyKeyWorld (D : C.Coalition) : QueryImpl (WorldSpec C) (StateT (HashCache C × KeyCache C) ProbComp) :=
  fun t => match t with
  | .inl t => StateT.mk fun st => (fun r => (r.1, (r.2, st.2))) <$>
      ((localAnswer (C := C) prims + programAnswer (C := C)) t).run st.1
  | .inr (.inr (.inr x)) => if Hidden D x.1 then StateT.mk fun st =>
        (fun r => (prims.aes.eval r.1 x.2.2, (st.1, r.2))) <$>
          ((((KeyName C × HashOutput) →ₒ Digest).randomOracle (x.1, x.2.1)).run st.2)
      else StateT.mk fun st => (fun r => (r.1, (r.2, st.2))) <$> (localAnswer prims (.inr (.inr x))).run st.1
  | .inr t => StateT.mk fun st => (fun r => (r.1, (r.2, st.2))) <$> (localAnswer prims t).run st.1

/-- The next stage of `TreeKeyHop`: the eager table of AES keys is the lazy one. -/
def KeyTableLazy (D : C.Coalition) : Prop :=
  ∀ game : OracleComp (WorldSpec C) Bool,
    Pr[= true | ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
        (simulateQ (keyWorld prims D keys) game).run' ∅] =
      Pr[= true | (simulateQ (lazyKeyWorld prims D) game).run' (∅, ∅)]

end StreamWorld

section Hops
variable {C : Committee} {E : Type} (prims : Primitives) [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The real run of a ceremony with its distinguisher. -/
def treeRealGame (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput) : OracleComp (WorldSpec C) Bool :=
  distinguish (realExecution D A noFunctionality (ceremonyFuel circuits settings)
    (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput)) x z) Z

/-- The ideal run of a ceremony with `treeSimulator` and the distinguisher. -/
def treeIdealGame (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput) : OracleComp (WorldSpec C) Bool :=
  distinguish (idealExecution (fun oa => oa) D (Ftree circuits settings top tree)
    (treeSimulator K circuits settings top tree D A) x z) Z

/-- The real run against the real run with independent AES keys for the hidden streams. -/
def TreeKeyHop (split : ℕ → ℝ) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    |accepts prims (treeRealGame K circuits settings top tree D A x z Z) -
      (Pr[= true | ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
        (simulateQ (keyWorld prims D keys) (treeRealGame K circuits settings top tree D A x z Z)).run' ∅]).toReal| ≤
      streamKeyError C + split q

/-- The real run with random hidden streams against the ideal run. -/
def TreeSimulationHop (split : ℕ → ℝ) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q →
    |(Pr[= true | (simulateQ (streamWorld prims D) (treeRealGame K circuits settings top tree D A x z Z)).run'
        (∅, ∅)]).toReal - accepts prims (treeIdealGame K circuits settings top tree D A x z Z)| ≤
      treeCheckError (E := E) circuits settings tree q + (treeHashError circuits settings C tree q - split q)

theorem treeSecurityDistance_of_hops (split : ℕ → ℝ) (h₁ : TreeKeyHop prims K circuits settings split)
    (h₂ : TreeSimulationHop prims K circuits settings split) : TreeSecurityDistance prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq
  have := abs_sub_le_of_hops prims D (treeRealGame K circuits settings top tree D A x z Z)
    (treeIdealGame K circuits settings top tree D A x z Z) (streamKeyError C + split q)
    (treeCheckError (E := E) circuits settings tree q + (treeHashError circuits settings C tree q - split q))
    (by unfold reductionReal; rw [prfRealExp_prgReduction]; exact h₁ hb top tree D A x z Z q hx hq)
    (by unfold reductionIdeal; rw [prfIdealExp_prgReduction]; exact h₂ hb top tree D A x z Z q hx hq)
  unfold treeRealGame treeIdealGame at this
  linarith

end Hops

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

open OracleComp.DeferredSampling

section KeyTable
variable {C : Committee} (prims : Primitives)

/-- A query that both worlds answer with the same step on the hash cache. -/
theorem evalDist_lazyKeyWorld_common (D : C.Coalition) {α : Type} (t : (WorldSpec C).Domain)
    (k : (WorldSpec C).Range t → OracleComp (WorldSpec C) α) (m : StateT (HashCache C) ProbComp ((WorldSpec C).Range t))
    (hl : lazyKeyWorld prims D t = StateT.mk fun st => (fun r => (r.1, (r.2, st.2))) <$> m.run st.1)
    (hk : ∀ g, keyWorld prims D g t = m)
    (ih : ∀ u (s : HashCache C) (c : KeyCache C),
      𝒟[(simulateQ (lazyKeyWorld prims D) (k u)).run' (s, c)] =
        𝒟[($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g =>
          (simulateQ (keyWorld prims D (tableExtending c g)) (k u)).run' s])
    (s : HashCache C) (c : KeyCache C) :
    𝒟[(simulateQ (lazyKeyWorld prims D) ((liftM ((WorldSpec C).query t) : OracleComp (WorldSpec C) _) >>= k)).run' (s, c)] =
      𝒟[($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g =>
        (simulateQ (keyWorld prims D (tableExtending c g)) ((liftM ((WorldSpec C).query t) : OracleComp (WorldSpec C) _) >>= k)).run' s] := by
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
    StateT.run'_eq, StateT.run_bind, hl, hk, StateT.run_mk, bind_map_left, map_bind]
  rw [evalDist_bind_comm]
  refine evalDist_bind_congr_left _ _ _ fun r => ?_
  have := ih r.1 r.2 c
  simp only [StateT.run'_eq] at this
  rw [this]

/-- Overwriting one entry of a uniform table with a fresh uniform value keeps the table uniform,
under any continuation. -/
theorem evalDist_update_bind {D R β : Type} [Finite D] [DecidableEq D] [Finite R] [Nonempty R]
    [SampleableType R] [SampleableType (D → R)] (t : D) (Ψ : (D → R) → ProbComp β) :
    𝒟[($ᵗ R) >>= fun u => ($ᵗ (D → R)) >>= fun g => Ψ (Function.update g t u)] =
      𝒟[($ᵗ (D → R)) >>= Ψ] := by
  have h := evalDist_uniformSample_bind_update (R := R) (D := D) t
  calc 𝒟[($ᵗ R) >>= fun u => ($ᵗ (D → R)) >>= fun g => Ψ (Function.update g t u)]
      = 𝒟[(($ᵗ R) >>= fun u => ($ᵗ (D → R)) >>= fun g => pure (Function.update g t u)) >>= Ψ] := by
        simp only [bind_assoc, pure_bind]
    _ = 𝒟[($ᵗ (D → R)) >>= Ψ] := by rw [evalDist_bind, h, ← evalDist_bind]

theorem evalDist_lazyKeyWorld (D : C.Coalition) {α : Type} (game : OracleComp (WorldSpec C) α) :
    ∀ (s : HashCache C) (c : KeyCache C),
    𝒟[(simulateQ (lazyKeyWorld prims D) game).run' (s, c)] =
      𝒟[($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g =>
        (simulateQ (keyWorld prims D (tableExtending c g)) game).run' s] := by
  induction game using OracleComp.inductionOn with
  | pure a =>
    intro s c
    simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
    exact (evalDist_bind_const_neverFails _ (by simp) _).symm
  | query_bind t k ih =>
    intro s c
    rcases t with ((u | q | x) | p) | (u | q | x)
    · exact evalDist_lazyKeyWorld_common prims D _ k _ rfl (fun _ => rfl) ih s c
    · exact evalDist_lazyKeyWorld_common prims D _ k _ rfl (fun _ => rfl) ih s c
    · exact evalDist_lazyKeyWorld_common prims D _ k _ rfl (fun _ => rfl) ih s c
    · exact evalDist_lazyKeyWorld_common prims D _ k _ rfl (fun _ => rfl) ih s c
    · exact evalDist_lazyKeyWorld_common prims D _ k _ rfl (fun _ => rfl) ih s c
    · exact evalDist_lazyKeyWorld_common prims D _ k _ rfl (fun _ => rfl) ih s c
    · by_cases h : Hidden D x.1
      · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
          StateT.run'_eq, StateT.run_bind]
        simp only [lazyKeyWorld, keyWorld, if_pos h, StateT.run_mk, bind_map_left, StateT.run_pure, pure_bind]
        rcases hc : c (x.1, x.2.1) with _ | u
        · rw [QueryImpl.withCaching_run_none _ hc]
          set y := (x.1, x.2.1) with hy
          let Ψ : (KeyName C × HashOutput → Digest) → ProbComp α := fun g =>
            (fun x => x.1) <$> (simulateQ (keyWorld prims D (tableExtending c g))
              (k (prims.aes.eval (tableExtending c g y) x.2.2))).run s
          have step : ∀ u, 𝒟[(fun x => x.1) <$> (simulateQ (lazyKeyWorld prims D)
              (k (prims.aes.eval u x.2.2))).run (s, QueryCache.cacheQuery c y u)] =
              𝒟[($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g => Ψ (Function.update g y u)] := by
            intro u
            have := ih (prims.aes.eval u x.2.2) s (QueryCache.cacheQuery c y u)
            simp only [StateT.run'_eq] at this
            rw [this]
            refine evalDist_bind_congr_left _ _ _ fun g => ?_
            simp only [Ψ]
            rw [tableExtending_cacheQuery, tableExtending_update_of_none c g hc]
            have e : tableExtending c (Function.update g y u) y = u := by simp [tableExtending, hc]
            rw [e]
          rw [bind_map_left, map_bind]
          calc _ = 𝒟[($ᵗ Digest) >>= fun u => ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun g =>
                Ψ (Function.update g y u)] := evalDist_bind_congr_left _ _ _ step
            _ = _ := evalDist_update_bind y Ψ
        · rw [QueryImpl.withCaching_run_some _ hc, pure_bind]
          have := ih (prims.aes.eval u x.2.2) s c
          simp only [StateT.run'_eq] at this
          rw [this]
          have e : ∀ g : KeyName C × HashOutput → Digest, tableExtending c g (x.1, x.2.1) = u := fun g => by
            simp [tableExtending, hc]
          simp only [e]
      · exact evalDist_lazyKeyWorld_common prims D _ k (localAnswer prims (.inr (.inr x)))
          (by simp only [lazyKeyWorld, if_neg h]; rfl)
          (fun _ => by simp only [keyWorld, if_neg h]) ih s c

theorem keyTableLazy (D : C.Coalition) : KeyTableLazy prims D := by
  intro game
  have h := evalDist_lazyKeyWorld prims D game ∅ ∅
  simp only [tableExtending_empty] at h
  exact (OracleComp.probOutput_congr rfl h).symm

end KeyTable

end ThresholdLeanXmssSecurity

section FreshStreams
set_option backward.isDefEq.respectTransparency false
namespace ThresholdLeanXmssSecurity
open OracleComp.DeferredSampling
attribute [local instance] Classical.propDecidable

/-- Cache a finite table at the queried addresses, in query order. -/
def cacheFin {D R : Type} [DecidableEq D] : ∀ {n : ℕ},
    (Fin n → D) → (Fin n → R) → (D →ₒ R).QueryCache → (D →ₒ R).QueryCache
  | 0, _, _, c => c
  | _ + 1, addr, vals, c => cacheFin (fun i => addr i.succ) (fun i => vals i.succ)
      (c.cacheQuery (addr 0) (vals 0))

/-- Distinct fresh queries can be sampled first, with their exact final cache retained. -/
theorem randomOracle_sequenceFin_fresh {D R : Type} [DecidableEq D] [SampleableType R] :
    ∀ {n : ℕ} (addr : Fin n → D) (ha : Function.Injective addr) (c : (D →ₒ R).QueryCache)
      (hc : ∀ i, c (addr i) = none),
      (Concrete.sequenceFin fun i => (D →ₒ R).randomOracle (addr i)).run c =
        (fun vals => (vals, cacheFin addr vals c)) <$>
          Concrete.sequenceFin (fun _ : Fin n => ($ᵗ R))
  | 0, addr, ha, c, hc => by simp [Concrete.sequenceFin, cacheFin]
  | n + 1, addr, ha, c, hc => by
    simp only [Concrete.sequenceFin, StateT.run_bind]
    rw [QueryImpl.withCaching_run_none _ (hc 0), bind_map_left]
    simp only [map_bind]
    refine bind_congr fun a => ?_
    rw [randomOracle_sequenceFin_fresh (fun i : Fin n => addr i.succ)
      (ha.comp (Fin.succ_injective n)) _ (fun i => ?_)]
    · simp only [bind_map_left, StateT.run_pure, map_pure, cacheFin]
      rfl
    · rw [QueryCache.cacheQuery_of_ne]
      · exact hc i.succ
      · exact fun h => Fin.succ_ne_zero i (ha h)

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

/-- Independent uniform samples at finite coordinates are a uniform function table. -/
theorem evalDist_sequenceFin_uniform {R : Type} [SampleableType R] (n : ℕ) :
    𝒟[Concrete.sequenceFin (fun _ : Fin n => ($ᵗ R))] = 𝒟[$ᵗ (Fin n → R)] := by
  classical
  let oa : OracleComp (Fin n →ₒ R) (Fin n → R) :=
    Concrete.sequenceFin fun i => (OracleComp.lift (OracleSpec.query (spec := Fin n →ₒ R) i))
  have he : ∀ g : Fin n → R, evalWithAnswerFn (QueryImpl.ofFn g) oa = g := by
    intro g
    simp only [evalWithAnswerFn, oa, simulateQ_sequenceFin, simulateQ_query,
      OracleQuery.cont_query, OracleQuery.input_query, id_map, QueryImpl.ofFn_apply]
    exact congrArg Id.run (sequenceFin_pure g)
  have h := evalDist_simulateQ_randomOracle_run'_empty_eq_uniformTable oa
  simp only [he, bind_pure] at h
  rw [show (simulateQ randomOracle oa).run' ∅ =
      Concrete.sequenceFin (fun _ : Fin n => ($ᵗ R)) from ?_] at h
  · exact h
  · simp only [oa, simulateQ_sequenceFin, simulateQ_query,
      OracleQuery.cont_query, OracleQuery.input_query, id_map, StateT.run'_eq]
    change Prod.fst <$> (Concrete.sequenceFin fun i : Fin n => (Fin n →ₒ R).randomOracle i).run ∅ = _
    erw [randomOracle_sequenceFin_fresh (R := R) (fun i : Fin n => i) Function.injective_id ∅ (fun _ => rfl)]
    simp only [Functor.map_map]
    exact id_map _

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

/-- Presampling retains the full cache, so a later adaptive continuation can still use it. -/
theorem evalDist_randomOracle_sequenceFin_fresh {D R : Type} [DecidableEq D] [SampleableType R]
    {n : ℕ} (addr : Fin n → D) (ha : Function.Injective addr) (c : (D →ₒ R).QueryCache)
    (hc : ∀ i, c (addr i) = none) :
    𝒟[(Concrete.sequenceFin fun i => (D →ₒ R).randomOracle (addr i)).run c] =
      𝒟[(fun vals => (vals, cacheFin addr vals c)) <$> ($ᵗ (Fin n → R))] := by
  rw [randomOracle_sequenceFin_fresh addr ha c hc, evalDist_map, evalDist_sequenceFin_uniform,
    ← evalDist_map]

/-- Run a computation on the hidden cache, retaining the hash cache unchanged. -/
def onHidden {C : Committee} {α : Type} (p : StateT (HiddenCache C) ProbComp α) :
    StateT (HashCache C × HiddenCache C) ProbComp α :=
  StateT.mk fun st => (fun r => (r.1, (st.1, r.2))) <$> p.run st.2

theorem onHidden_sequenceFin {C : Committee} {α : Type} : ∀ {n : ℕ}
    (p : Fin n → StateT (HiddenCache C) ProbComp α),
    Concrete.sequenceFin (fun i => onHidden (p i)) = onHidden (Concrete.sequenceFin p)
  | 0, p => by ext st; simp [Concrete.sequenceFin, onHidden]
  | n + 1, p => by
    simp only [Concrete.sequenceFin]
    rw [onHidden_sequenceFin (fun i : Fin n => p i.succ)]
    ext st
    simp [onHidden, StateT.run_bind, Functor.map_map]

/-- A finite set of fresh hidden-stream positions is a uniform table, jointly with both caches. -/
theorem streamWorld_sequenceFin_fresh {C : Committee} (prims : Primitives) (D : C.Coalition)
    {n : ℕ} (addr : Fin n → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ))
    (ha : Function.Injective addr) (hh : ∀ i, Hidden D (addr i).1.1)
    (s : HashCache C) (c : HiddenCache C) (hc : ∀ i, c (addr i) = none) :
    𝒟[(simulateQ (streamWorld prims D) (Concrete.sequenceFin fun i =>
      (OracleComp.lift (OracleSpec.query (spec := WorldSpec C)
        (.inr (.inr (.inr ((addr i).1.1, (addr i).1.2, (addr i).2)))))))).run (s, c)] =
      𝒟[(fun vals => (vals, (s, cacheFin addr vals c))) <$> ($ᵗ (Fin n → Bit))] := by
  have hstep : ∀ i, streamWorld prims D
      (.inr (.inr (.inr ((addr i).1.1, (addr i).1.2, (addr i).2)))) =
      onHidden ((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle (addr i)) := by
    intro i
    simp only [streamWorld, hh i, if_true, onHidden]
  simp only [simulateQ_sequenceFin, simulateQ_spec_query, hstep]
  erw [onHidden_sequenceFin (α := Bit)]
  simp only [onHidden, StateT.run_mk, evalDist_map]
  erw [evalDist_randomOracle_sequenceFin_fresh addr ha c hc]
  rw [← evalDist_map, Functor.map_map, evalDist_map]

/-- A label absent from the cache makes every distinct finite collection of its positions fresh. -/
theorem streamWorld_freshLabel {C : Committee} (prims : Primitives) (D : C.Coalition)
    {n : ℕ} (addr : Fin n → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ))
    (ha : Function.Injective addr) (hh : ∀ i, Hidden D (addr i).1.1)
    (ρ : ℕ) (hρ : ∀ i, (addr i).2.1 = ρ)
    (s : HashCache C) (c : HiddenCache C)
    (fresh : ∀ x, x.2.1 = ρ → c x = none) :
    𝒟[(simulateQ (streamWorld prims D) (Concrete.sequenceFin fun i =>
      (OracleComp.lift (OracleSpec.query (spec := WorldSpec C)
        (.inr (.inr (.inr ((addr i).1.1, (addr i).1.2, (addr i).2)))))))).run (s, c)] =
      𝒟[(fun vals => (vals, (s, cacheFin addr vals c))) <$> ($ᵗ (Fin n → Bit))] :=
  streamWorld_sequenceFin_fresh prims D addr ha hh s c (fun i => fresh (addr i) (hρ i))

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

/-- Inserting a finite table leaves every other coordinate unchanged. -/
theorem cacheFin_of_not_mem {D R : Type} [DecidableEq D] : ∀ {n : ℕ}
    (addr : Fin n → D) (vals : Fin n → R) (c : (D →ₒ R).QueryCache) (x : D)
    (hx : ∀ i, x ≠ addr i), cacheFin addr vals c x = c x
  | 0, addr, vals, c, x, hx => rfl
  | n + 1, addr, vals, c, x, hx => by
    rw [cacheFin, cacheFin_of_not_mem _ _ _ x (fun i => hx i.succ)]
    exact QueryCache.cacheQuery_of_ne c (vals 0) (hx 0)

/-- Every sampled entry is retained in the final cache. -/
theorem cacheFin_at {D R : Type} [DecidableEq D] : ∀ {n : ℕ}
    (addr : Fin n → D) (ha : Function.Injective addr) (vals : Fin n → R)
    (c : (D →ₒ R).QueryCache) (i : Fin n), cacheFin addr vals c (addr i) = some (vals i)
  | 0, addr, ha, vals, c, i => i.elim0
  | n + 1, addr, ha, vals, c, i => by
    cases i using Fin.cases with
    | zero =>
      rw [cacheFin, cacheFin_of_not_mem _ _ _ _ (fun j h => Fin.succ_ne_zero j (ha h).symm)]
      exact QueryCache.cacheQuery_self _ _ _
    | succ i =>
      exact cacheFin_at (fun j : Fin n => addr j.succ) (ha.comp (Fin.succ_injective n)) _ _ i

/-- Sampling one round preserves the freshness of every larger round label. -/
theorem cacheFin_freshLabel {C : Committee} {n : ℕ}
    (addr : Fin n → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ)) (ρ : ℕ)
    (hρ : ∀ i, (addr i).2.1 = ρ) (vals : Fin n → Bit) (c : HiddenCache C)
    (fresh : ∀ x, ρ ≤ x.2.1 → c x = none) :
    ∀ x, ρ + 1 ≤ x.2.1 → cacheFin addr vals c x = none := by
  intro x hx
  rw [cacheFin_of_not_mem addr vals c x (fun i he => by
    have h := hρ i
    rw [← he] at h
    omega)]
  exact fresh x (by omega)

end ThresholdLeanXmssSecurity

end FreshStreams

section SequentialExecution
set_option backward.isDefEq.respectTransparency false
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

section RoundComposition
variable {C : Committee} {E : Type} {I O L R Ia α : Type}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (Ro : Roles C m) (D : C.Coalition) (A : Adversary C E Ia L R)
variable (F : Functionality C I O L R)

/-- The round runner before projecting its pending programs to outputs. -/
def executeSteps : ℕ → A.State → (C.Party → Step C E (CallSpec I O) α) →
    m (A.State × (C.Party → Step C E (CallSpec I O) α))
  | 0, state, steps => pure (state, steps)
  | fuel + 1, state, steps =>
    if ∀ i, i ∉ D.1 → (steps i).isDone then pure (state, steps) else do
      let (state, steps, _) ← stepRound Ro D A F state steps
      executeSteps fuel state steps

/-- Stopping is persistent, including when honest operators aborted. -/
theorem executeSteps_done (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α)
    (hd : ∀ i, i ∉ D.1 → (steps i).isDone) :
    executeSteps Ro D A F fuel state steps = pure (state, steps) := by
  cases fuel <;> simp only [executeSteps, if_pos hd]

/-- Running a prefix and retaining its pending programs gives exact sequential composition. -/
theorem executeSteps_add (a b : ℕ) (state : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α) :
    executeSteps Ro D A F (a + b) state steps =
      executeSteps Ro D A F a state steps >>= fun p => executeSteps Ro D A F b p.1 p.2 := by
  induction a generalizing state steps with
  | zero => simp [executeSteps]
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [executeSteps]
    split_ifs with hd
    · rw [pure_bind, executeSteps_done Ro D A F b state steps hd]
    · simp only [bind_assoc]
      exact bind_congr fun p => ih p.1 p.2.1

/-- `executeRounds` is the output projection of the runner that retains pending programs. -/
theorem executeRounds_eq_executeSteps (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α) :
    executeRounds Ro D A F fuel state steps =
      (fun p => (p.1, fun i => (p.2 i).output)) <$> executeSteps Ro D A F fuel state steps := by
  induction fuel generalizing state steps with
  | zero => simp [executeRounds, executeSteps]
  | succ fuel ih =>
    simp only [executeRounds, executeSteps]
    split_ifs
    · simp
    · rw [map_bind]
      exact bind_congr fun p => ih p.1 p.2.1

/-- Split a round budget without discarding continuations or suppressing abort frames. -/
theorem executeRounds_add (a b : ℕ) (state : A.State)
    (steps : C.Party → Step C E (CallSpec I O) α) :
    executeRounds Ro D A F (a + b) state steps =
      executeSteps Ro D A F a state steps >>= fun p => executeRounds Ro D A F b p.1 p.2 := by
  rw [executeRounds_eq_executeSteps, executeSteps_add, map_bind]
  exact bind_congr fun p => (executeRounds_eq_executeSteps Ro D A F b p.1 p.2).symm

end RoundComposition

section Continuations
variable {C : Committee} {E ι α β : Type} {G : OracleSpec ι}

/-- Continue a suspended program, without running past its next interaction. -/
def continueStep (k : α → PartyM C E G β) : Step C E G α → OracleComp (LocalSpec C) (Step C E G β)
  | .done none => pure (.done none)
  | .done (some a) => advance (k a).run
  | .wait outbox resume => pure (.wait outbox fun inbox =>
      (OptionT.mk (resume inbox) >>= k).run)
  | .call input resume => pure (.call input fun response =>
      (OptionT.mk (resume response) >>= k).run)

/-- Advancing a sequential program first advances its prefix and then attaches the continuation. -/
theorem advance_bind (p : PartyM C E G α) (k : α → PartyM C E G β) :
    advance (p >>= k).run = advance p.run >>= continueStep k := by
  simp only [OptionT.run_bind, Option.elimM]
  change advance (p.run >>= fun a => a.elim (pure none) (fun a => (k a).run)) = _
  generalize p.run = oa
  induction oa using OracleComp.inductionOn with
  | pure a =>
    simp only [pure_bind]
    change advance (a.elim (pure none) (fun a => (k a).run)) = pure (.done a) >>= continueStep k
    rw [pure_bind]
    cases a <;> rfl
  | query_bind q f ih =>
    rcases q with (q | mail) | input
    · simp only [bind_assoc]
      change (OracleComp.lift (OracleSpec.query q) >>= fun r =>
        advance (f r >>= fun a => a.elim (pure none) (fun a => (k a).run))) =
        (OracleComp.lift (OracleSpec.query q) >>= fun r => advance (f r)) >>= continueStep k
      simp only [bind_assoc]
      exact bind_congr ih
    · rw [bind_assoc]
      change pure (.wait mail (fun response => f response >>= fun a =>
        a.elim (pure none) (fun a => (k a).run))) = pure (.wait mail f) >>= continueStep k
      simp only [pure_bind, continueStep, OptionT.run_bind, OptionT.run_mk, Option.elimM]
    · rw [bind_assoc]
      change pure (.call input (fun response => f response >>= fun a =>
        a.elim (pure none) (fun a => (k a).run))) = pure (.call input f) >>= continueStep k
      simp only [pure_bind, continueStep, OptionT.run_bind, OptionT.run_mk, Option.elimM]

end Continuations

end ThresholdLeanXmssSecurity

end SequentialExecution

section GoodOutputCoupling
open scoped ENNReal
open OracleComp.ProgramLogic.Relational
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

section BadCoupling
variable {ι σ α : Type} {spec : OracleSpec ι}

/-- Once a monotone bad flag is set, a simulation cannot return to a good state. -/
theorem simulateQ_bad_absorbing (impl : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hmono : ∀ t s, bad s → ∀ r ∈ support ((impl t).run s), bad r.2)
    (game : OracleComp spec α) (s : σ) (hs : bad s) :
    ∀ r ∈ support ((simulateQ impl game).run s), bad r.2 := by
  induction game using OracleComp.inductionOn generalizing s with
  | pure a => simpa using hs
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop]
    rintro r ⟨p, hp, hr⟩
    exact ih p.1 p.2 (hmono t s hs p hp) r hr

/-- A step may first set the flag and return different answers. Only its good outputs must agree. -/
theorem simulateQ_probOutput_good_eq (I J : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hstep : ∀ t s r, ¬ bad r.2 → Pr[= r | (I t).run s] = Pr[= r | (J t).run s])
    (hI : ∀ t s, bad s → ∀ r ∈ support ((I t).run s), bad r.2)
    (hJ : ∀ t s, bad s → ∀ r ∈ support ((J t).run s), bad r.2)
    (game : OracleComp spec α) (s : σ) (r : α × σ) (hr : ¬ bad r.2) :
    Pr[= r | (simulateQ I game).run s] = Pr[= r | (simulateQ J game).run s] := by
  induction game using OracleComp.inductionOn generalizing s with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, probOutput_bind_eq_tsum]
    refine tsum_congr fun p => ?_
    by_cases hp : bad p.2
    · have hzI : Pr[= r | (simulateQ I (k p.1)).run p.2] = 0 := by
        rw [probOutput_eq_zero_iff]
        exact fun hm => hr (simulateQ_bad_absorbing I bad hI (k p.1) p.2 hp r hm)
      have hzJ : Pr[= r | (simulateQ J (k p.1)).run p.2] = 0 := by
        rw [probOutput_eq_zero_iff]
        exact fun hm => hr (simulateQ_bad_absorbing J bad hJ (k p.1) p.2 hp r hm)
      rw [hzI, hzJ, mul_zero, mul_zero]
    · rw [hstep t s p hp, ih]

/-- The two simulations assign the same total mass to the monotone bad event. -/
theorem simulateQ_probBad_eq (I J : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hstep : ∀ t s r, ¬ bad r.2 → Pr[= r | (I t).run s] = Pr[= r | (J t).run s])
    (hI : ∀ t s, bad s → ∀ r ∈ support ((I t).run s), bad r.2)
    (hJ : ∀ t s, bad s → ∀ r ∈ support ((J t).run s), bad r.2)
    (game : OracleComp spec α) (s : σ) :
    Pr[bad ∘ Prod.snd | (simulateQ I game).run s] =
      Pr[bad ∘ Prod.snd | (simulateQ J game).run s] := by
  have hg : Pr[fun r => ¬ bad r.2 | (simulateQ I game).run s] =
      Pr[fun r => ¬ bad r.2 | (simulateQ J game).run s] := by
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
    refine tsum_congr fun r => ?_
    split_ifs with hr
    · rfl
    · exact simulateQ_probOutput_good_eq I J bad hstep hI hJ game s r hr
  have h₁ := probEvent_compl ((simulateQ I game).run s) (bad ∘ Prod.snd)
  have h₂ := probEvent_compl ((simulateQ J game).run s) (bad ∘ Prod.snd)
  simp only [probFailure_eq_zero, tsub_zero] at h₁ h₂
  rw [show (fun r => ¬ (bad ∘ Prod.snd) r) = (fun r => ¬ bad r.2) from rfl, hg] at h₁
  exact (ENNReal.add_left_inj (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one)).mp
    (h₁.trans h₂.symm)

/-- Identical until bad, allowing the triggering query itself to have different bad outputs. -/
theorem tvDist_simulateQ_le_probBad_of_good_outputs
    (I J : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (hstep : ∀ t s r, ¬ bad r.2 → Pr[= r | (I t).run s] = Pr[= r | (J t).run s])
    (hI : ∀ t s, bad s → ∀ r ∈ support ((I t).run s), bad r.2)
    (hJ : ∀ t s, bad s → ∀ r ∈ support ((J t).run s), bad r.2)
    (game : OracleComp spec α) (s : σ) :
    tvDist ((simulateQ I game).run' s) ((simulateQ J game).run' s) ≤
      Pr[bad ∘ Prod.snd | (simulateQ I game).run s].toReal := by
  refine le_trans ?_ (tvDist_le_probEvent_of_probOutput_eq_of_not (bad ∘ Prod.snd)
    (fun r hr => simulateQ_probOutput_good_eq I J bad hstep hI hJ game s r hr)
    (simulateQ_probBad_eq I J bad hstep hI hJ game s))
  rw [StateT.run'_eq, StateT.run'_eq]
  exact tvDist_map_le Prod.fst _ _

end BadCoupling
end ThresholdLeanXmssSecurity
end GoodOutputCoupling

section SetupVisibility
open scoped ENNReal
open OracleComp.ProgramLogic.Relational
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

section SetupSecrecy
variable {C : Committee} (D : C.Coalition)

/-- A hidden term has only honest holders. -/
theorem hidden_term_holders {T : C.Term} (h : Hidden D (.term T)) :
    ∀ j ∈ C.holders T, j ∉ D.1 := by
  intro j hj hD
  exact h ⟨j, hD, hj⟩

/-- Every term included in a reveal to a corrupt receiver is known to the coalition. -/
theorem sharedTerms_known {i j : C.Party} (hj : j ∈ D.1) {T : C.Term}
    (hT : T ∈ sharedTerms i j) : KnownTo D.1 T := by
  have h := (List.mem_filter.mp hT).2
  simp only [decide_eq_true_eq] at h
  exact ⟨j, hj, h.2⟩

/-- PRSS reveals to corrupt receivers depend only on the terms and pairs those receivers know. -/
theorem revealTo_prss_congr (a b : Parts C) (i j : C.Party) (hj : j ∈ D.1)
    (hterm : ∀ T, KnownTo D.1 T → a.term T = b.term T) (hpair : a.pair j = b.pair j) :
    revealTo .prss a i j = revealTo .prss b i j := by
  simp only [revealTo, reduceCtorEq, ↓reduceIte, List.nil_append, hpair]
  congr 1
  exact List.map_congr_left fun T hT => hterm T (sharedTerms_known D hj hT)

/-- Changing one hidden term part changes no reveal sent to a corrupt receiver. -/
theorem revealTo_prss_hidden_term (a : Parts C) (i j : C.Party) (hj : j ∈ D.1)
    (T : C.Term) (hT : Hidden D (.term T)) (v : HashOutput) :
    revealTo .prss { a with term := Function.update a.term T v } i j = revealTo .prss a i j := by
  apply revealTo_prss_congr D _ _ i j hj
  · intro U hU
    have hne : U ≠ T := by rintro rfl; exact hT hU
    exact Function.update_of_ne hne _ _
  · rfl

/-- Changing a pair part addressed to an honest operator changes no corrupt receiver's reveal. -/
theorem revealTo_prss_hidden_pair (a : Parts C) (i j h : C.Party) (hj : j ∈ D.1)
    (hh : h ∉ D.1) (v : HashOutput) :
    revealTo .prss { a with pair := Function.update a.pair h v } i j = revealTo .prss a i j := by
  apply revealTo_prss_congr D _ _ i j hj
  · intro _ _; rfl
  · have hne : j ≠ h := by rintro rfl; exact hh hj
    exact Function.update_of_ne hne _ _

/-- The hash input of the commitment to a corrupt receiver is also unchanged. -/
theorem commit_prss_hidden_term (a : Parts C) (i j : C.Party) (hj : j ∈ D.1)
    (T : C.Term) (hT : Hidden D (.term T)) (v : HashOutput) :
    Query.commit .prss i j (revealTo .prss { a with term := Function.update a.term T v } i j) =
      Query.commit .prss i j (revealTo .prss a i j) := by
  rw [revealTo_prss_hidden_term D a i j hj T hT v]

/-- A corrupt receiver's echo contains only known term keys. -/
theorem sharedKeys_prss_congr (a b : C.Term → HashOutput) (i j : C.Party) (hj : j ∈ D.1)
    (hterm : ∀ T, KnownTo D.1 T → a T = b T) :
    Query.sharedKeys (C := C) .prss ((sharedTerms i j).map a) =
      Query.sharedKeys .prss ((sharedTerms i j).map b) := by
  congr 1
  exact List.map_congr_left fun T hT => hterm T (sharedTerms_known D hj hT)

end SetupSecrecy

section FreshDerivedKeys
variable {C : Committee} (prims : Primitives)

/-- A fresh PRSS derivation returns a uniform 256-bit value and stores exactly that answer. -/
theorem hashAnswer_prss_fresh (kind : KeyKind) (parts : List HashOutput) (s : HashCache C)
    (hs : s (.derive .prss kind parts) = none) :
    (hashAnswer prims (.derive .prss kind parts)).run s =
      (fun k => (k, s.cacheQuery (.derive .prss kind parts) k)) <$> ($ᵗ HashOutput) :=
  QueryImpl.withCaching_run_none _ hs

/-- The exact fresh-key collision probability for an arbitrary already-chosen finite set. -/
theorem prob_hashAnswer_prss_mem (kind : KeyKind) (parts : List HashOutput) (s : HashCache C)
    (hs : s (.derive .prss kind parts) = none) (S : Finset HashOutput) :
    Pr[fun r => r.1 ∈ S | (hashAnswer prims (.derive .prss kind parts)).run s] =
      (S.card : ℝ≥0∞) / 2 ^ 256 := by
  rw [hashAnswer_prss_fresh prims kind parts s hs, probEvent_map, probEvent_uniformSample]
  norm_num [HashOutput, hashOutputBits]

/-- The same fresh-key collision probability as a real-valued bound. -/
theorem prob_hashAnswer_prss_mem_toReal (kind : KeyKind) (parts : List HashOutput) (s : HashCache C)
    (hs : s (.derive .prss kind parts) = none) (S : Finset HashOutput) :
    (Pr[fun r => r.1 ∈ S | (hashAnswer prims (.derive .prss kind parts)).run s]).toReal =
      (S.card : ℝ) / 2 ^ 256 := by
  rw [prob_hashAnswer_prss_mem prims kind parts s hs S]
  simp

end FreshDerivedKeys

end ThresholdLeanXmssSecurity
end SetupVisibility

section HiddenTableReplay
open scoped ENNReal
open OracleComp.ProgramLogic.Relational
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- The honest query at one named hidden stream position. -/
def hiddenQuery {C : Committee} (x : (KeyName C × HashOutput) × ℕ × ℕ × ℕ) :
    OracleComp (WorldSpec C) Bit :=
  OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inr (x.1.1, x.1.2, x.2)))))

/-- A cached hidden-stream query returns its existing value and leaves both caches unchanged. -/
theorem streamWorld_hidden_cached {C : Committee} (prims : Primitives) (D : C.Coalition)
    (x : (KeyName C × HashOutput) × ℕ × ℕ × ℕ) (hx : Hidden D x.1.1)
    (s : HashCache C) (c : HiddenCache C) (b : Bit) (hc : c x = some b) :
    (simulateQ (streamWorld prims D) (hiddenQuery x)).run (s, c) = pure (b, (s, c)) := by
  unfold hiddenQuery
  erw [simulateQ_spec_query]
  simp only [streamWorld, hx, if_true, StateT.run_mk]
  erw [QueryImpl.withCaching_run_some _ hc]
  rfl

/-- Every later use of a presampled position reads exactly the sampled bit. -/
theorem streamWorld_hidden_cacheFin {C : Committee} (prims : Primitives) (D : C.Coalition)
    {n : ℕ} (addr : Fin n → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ))
    (ha : Function.Injective addr) (hh : ∀ i, Hidden D (addr i).1.1)
    (s : HashCache C) (c : HiddenCache C) (vals : Fin n → Bit) (i : Fin n) :
    (simulateQ (streamWorld prims D) (hiddenQuery (addr i))).run (s, cacheFin addr vals c) =
      pure (vals i, (s, cacheFin addr vals c)) :=
  streamWorld_hidden_cached prims D (addr i) (hh i) s _ _ (cacheFin_at addr ha vals c i)

/-- Any adaptive program on the presampled positions reads the table without changing either cache. -/
theorem streamWorld_replay_table {C : Committee} (prims : Primitives) (D : C.Coalition)
    {n : ℕ} (addr : Fin n → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ))
    (ha : Function.Injective addr) (hh : ∀ i, Hidden D (addr i).1.1)
    (s : HashCache C) (c : HiddenCache C) (vals : Fin n → Bit)
    {α : Type} (oa : OracleComp (Fin n →ₒ Bit) α) :
    (simulateQ (streamWorld prims D) (simulateQ (fun i => hiddenQuery (addr i)) oa)).run
        (s, cacheFin addr vals c) =
      pure (evalWithAnswerFn (QueryImpl.ofFn vals) oa, (s, cacheFin addr vals c)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, evalWithAnswerFn_pure]
  | query_bind i k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rw [streamWorld_hidden_cacheFin prims D addr ha hh s c vals i, pure_bind, ih]
    congr 1

end ThresholdLeanXmssSecurity
end HiddenTableReplay

section FreshTableRelations
open scoped ENNReal
open OracleComp.ProgramLogic.Relational
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- Read a finite family of honest stream positions. -/
def hiddenDraws {C : Committee} {n : ℕ}
    (addr : Fin n → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ)) :
    OracleComp (WorldSpec C) (Fin n → Bit) :=
  Concrete.sequenceFin fun i => hiddenQuery (addr i)

/-- Any bijection of a fresh table gives a relational coupling, including encoded field shifts. -/
theorem streamWorld_fresh_rel_bij {C : Committee} (prims : Primitives) (D : C.Coalition)
    {n : ℕ} (addr : Fin n → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ))
    (ha : Function.Injective addr) (hh : ∀ i, Hidden D (addr i).1.1)
    (s₁ s₂ : HashCache C) (c₁ c₂ : HiddenCache C)
    (hc₁ : ∀ i, c₁ (addr i) = none) (hc₂ : ∀ i, c₂ (addr i) = none)
    (f : (Fin n → Bit) → (Fin n → Bit)) (hf : Function.Bijective f) :
    RelTriple ((simulateQ (streamWorld prims D) (hiddenDraws addr)).run (s₁, c₁))
      ((simulateQ (streamWorld prims D) (hiddenDraws addr)).run (s₂, c₂))
      (fun r₁ r₂ => r₂.1 = f r₁.1 ∧
        r₁.2 = (s₁, cacheFin addr r₁.1 c₁) ∧ r₂.2 = (s₂, cacheFin addr r₂.1 c₂)) := by
  apply relTriple_of_evalDist_eq_left (streamWorld_sequenceFin_fresh prims D addr ha hh s₁ c₁ hc₁)
  apply relTriple_of_evalDist_eq_right (streamWorld_sequenceFin_fresh prims D addr ha hh s₂ c₂ hc₂).symm
  apply relTriple_map
  exact relTriple_uniformSample_bij hf _ (fun _ => ⟨rfl, rfl, rfl⟩)

/-- Couple two fresh rounds by any additive translation, retaining the exact translated caches. -/
theorem streamWorld_fresh_rel {C : Committee} (prims : Primitives) (D : C.Coalition)
    {n : ℕ} (addr : Fin n → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ))
    (ha : Function.Injective addr) (hh : ∀ i, Hidden D (addr i).1.1)
    (s₁ s₂ : HashCache C) (c₁ c₂ : HiddenCache C)
    (hc₁ : ∀ i, c₁ (addr i) = none) (hc₂ : ∀ i, c₂ (addr i) = none)
    (δ : Fin n → Bit) :
    RelTriple ((simulateQ (streamWorld prims D) (hiddenDraws addr)).run (s₁, c₁))
      ((simulateQ (streamWorld prims D) (hiddenDraws addr)).run (s₂, c₂))
      (fun r₁ r₂ => r₂.1 = r₁.1 + δ ∧
        r₁.2 = (s₁, cacheFin addr r₁.1 c₁) ∧ r₂.2 = (s₂, cacheFin addr r₂.1 c₂)) := by
  apply relTriple_of_evalDist_eq_left (streamWorld_sequenceFin_fresh prims D addr ha hh s₁ c₁ hc₁)
  apply relTriple_of_evalDist_eq_right (streamWorld_sequenceFin_fresh prims D addr ha hh s₂ c₂ hc₂).symm
  apply relTriple_map
  exact relTriple_uniformSample_bij (AddGroup.addRight_bijective δ) _ (fun _ => ⟨rfl, rfl, rfl⟩)

/-- A gadget continuation can consume the coupled tables with their exact resulting caches. -/
theorem streamWorld_fresh_bind_rel {C : Committee} (prims : Primitives) (D : C.Coalition)
    {n : ℕ} (addr : Fin n → ((KeyName C × HashOutput) × ℕ × ℕ × ℕ))
    (ha : Function.Injective addr) (hh : ∀ i, Hidden D (addr i).1.1)
    (s₁ s₂ : HashCache C) (c₁ c₂ : HiddenCache C)
    (hc₁ : ∀ i, c₁ (addr i) = none) (hc₂ : ∀ i, c₂ (addr i) = none)
    (δ : Fin n → Bit) {α β : Type}
    (k₁ : (Fin n → Bit) → HashCache C × HiddenCache C → ProbComp α)
    (k₂ : (Fin n → Bit) → HashCache C × HiddenCache C → ProbComp β)
    (R : α → β → Prop)
    (hk : ∀ vals, RelTriple (k₁ vals (s₁, cacheFin addr vals c₁))
      (k₂ (vals + δ) (s₂, cacheFin addr (vals + δ) c₂)) R) :
    RelTriple
      (((simulateQ (streamWorld prims D) (hiddenDraws addr)).run (s₁, c₁)) >>= fun r => k₁ r.1 r.2)
      (((simulateQ (streamWorld prims D) (hiddenDraws addr)).run (s₂, c₂)) >>= fun r => k₂ r.1 r.2) R := by
  refine relTriple_bind (streamWorld_fresh_rel prims D addr ha hh s₁ s₂ c₁ c₂ hc₁ hc₂ δ) ?_
  intro r₁ r₂ h
  rw [h.2.1, h.2.2, h.1]
  exact hk r₁.1

end ThresholdLeanXmssSecurity
end FreshTableRelations

section KeyJointCoupling
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- Full hash outputs for hidden named stream keys. The low half is the AES key. -/
abbrev FullKeyCache (C : Committee) := ((KeyName C × HashOutput) →ₒ HashOutput).QueryCache

/-- A public hash cache and deferred private stream-key answers, with their first owners. -/
structure KeyJointState (C : Committee) where
  hash : HashCache C
  keys : FullKeyCache C
  used : HashOutput → Option (KeyName C)
  bad : Bool

variable {C : Committee}

def KeyJointState.privateHash (s : KeyJointState C) (k : HashOutput) : Option HashOutput :=
  (s.used k).bind fun name => s.keys (name, k)

def onJointHash {α : Type} (m : StateT (HashCache C) ProbComp α) :
    StateT (KeyJointState C) ProbComp α := StateT.mk fun s =>
  (fun r => (r.1, { s with hash := r.2 })) <$> m.run s.hash

/-- A public hash query either exposes a deferred real answer or uses the public cache. -/
def jointHash (prims : Primitives) (real : Bool) (q : Query C) :
    StateT (KeyJointState C) ProbComp HashOutput := StateT.mk fun s =>
  match q with
  | .streamKey k =>
    if real then match s.hash q, s.privateHash k with
      | none, some v => pure (v, { s with hash := s.hash.cacheQuery q v })
      | _, _ => (onJointHash (hashAnswer prims q)).run s
    else (onJointHash (hashAnswer prims q)).run s
  | _ => (onJointHash (hashAnswer prims q)).run s

/-- The named private answer. The real variant reuses an already existing hash of the key. -/
def jointHidden (real : Bool) (x : KeyName C × HashOutput) :
    StateT (KeyJointState C) ProbComp HashOutput := StateT.mk fun s =>
  match s.keys x with
  | some v => pure (v, s)
  | none => do
    let v ← if real then match s.hash (.streamKey x.2) <|> s.privateHash x.2 with
      | some v => pure v
      | none => $ᵗ HashOutput
      else $ᵗ HashOutput
    pure (v, { s with keys := s.keys.cacheQuery x v, used := if (s.used x.2).isSome then s.used else Function.update s.used x.2 (some x.1) })

def jointProgram (real : Bool) (x : Query C × HashOutput) :
    StateT (KeyJointState C) ProbComp Bool := StateT.mk fun s =>
  match x.1 with
  | .streamKey k =>
    if real && (s.privateHash k).isSome then pure (false, s)
    else (onJointHash (programAnswer x)).run s
  | _ => (onJointHash (programAnswer x)).run s

def jointLocal (prims : Primitives) (real : Bool) :
    QueryImpl (LocalSpec C) (StateT (KeyJointState C) ProbComp) :=
  fun q => match q with
  | .inl u => onJointHash ((unifFwdImpl (Query C →ₒ HashOutput)) u)
  | .inr (.inl q) => jointHash prims real q
  | .inr (.inr x) => do
      let h ← jointHash prims real (.streamKey x.2.1)
      pure (prims.aes.eval (truncateHash h) x.2.2)

/-- The three bad events: public use of a private key, an already cached first use, and reuse of
one hidden key under another name. -/
def keyJointRisk (D : C.Coalition) (q : (WorldSpec C).Domain) (s : KeyJointState C) : Bool :=
  let publicHash := fun q : Query C => match q with
    | .streamKey k => (s.used k).isSome
    | _ => false
  match q with
  | .inl (.inr x) => publicHash x.1
  | .inl (.inl (.inr (.inl q))) => publicHash q
  | .inl (.inl (.inr (.inr x))) => (s.used x.2.1).isSome
  | .inr (.inr (.inl q)) => publicHash q
  | .inr (.inr (.inr x)) =>
    if Hidden D x.1 then
      !(s.keys (x.1, x.2.1)).isSome &&
        ((s.hash (.streamKey x.2.1)).isSome || (s.used x.2.1).isSome)
    else (s.used x.2.1).isSome
  | _ => false

/-- The common monitored state representation of the real and independently keyed worlds. -/
def jointKeyWorldCore (prims : Primitives) (D : C.Coalition) (real : Bool) :
    QueryImpl (WorldSpec C) (StateT (KeyJointState C) ProbComp) := fun q =>
  match q with
  | .inl (.inl q) => jointLocal prims real q
  | .inl (.inr x) => jointProgram real x
  | .inr (.inr (.inr x)) =>
    if Hidden D x.1 then do
      let h ← jointHidden real (x.1, x.2.1)
      pure (prims.aes.eval (truncateHash h) x.2.2)
    else jointLocal prims real (.inr (.inr x))
  | .inr q => jointLocal prims real q

def jointKeyWorld (prims : Primitives) (D : C.Coalition) (real : Bool) :
    QueryImpl (WorldSpec C) (StateT (KeyJointState C) ProbComp) := fun q => StateT.mk fun s =>
  (fun r => (r.1, { r.2 with bad := s.bad || keyJointRisk D q s })) <$>
    (jointKeyWorldCore prims D real q).run s

@[simp] theorem privateHash_eq_none (s : KeyJointState C) (k : HashOutput)
    (h : s.used k = none) : s.privateHash k = none := by simp [KeyJointState.privateHash, h]

theorem jointHash_eq_of_unused (prims : Primitives) (q : Query C) (s : KeyJointState C)
    (h : ∀ k, q = .streamKey k → s.used k = none) :
    (jointHash prims true q).run s = (jointHash prims false q).run s := by
  cases q <;> simp only [jointHash, StateT.run_mk, Bool.false_eq_true, if_true, if_false]
  case streamKey k => simp [privateHash_eq_none s k (h k rfl)]

theorem jointHidden_eq_of_fresh (x : KeyName C × HashOutput) (s : KeyJointState C)
    (h : s.keys x = none → s.hash (.streamKey x.2) = none ∧ s.used x.2 = none) :
    (jointHidden true x).run s = (jointHidden false x).run s := by
  cases hk : s.keys x with
  | some v => simp [jointHidden, hk]
  | none => obtain ⟨hh, hu⟩ := h hk; simp [jointHidden, hk, hh, privateHash_eq_none s x.2 hu]

theorem jointProgram_eq_of_unused (x : Query C × HashOutput) (s : KeyJointState C)
    (h : ∀ k, x.1 = .streamKey k → s.used k = none) :
    (jointProgram true x).run s = (jointProgram false x).run s := by
  rcases x with ⟨q, v⟩
  cases q <;> simp only [jointProgram, StateT.run_mk]
  case streamKey k => simp [privateHash_eq_none s k (h k rfl)]

theorem jointKeyWorldCore_eq_of_no_risk (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C) (h : keyJointRisk D q s = false) :
    (jointKeyWorldCore prims D true q).run s = (jointKeyWorldCore prims D false q).run s := by
  rcases q with ((u | q | x) | p) | (u | q | x)
  · rfl
  · exact jointHash_eq_of_unused prims q s (by
      intro k hk; subst q; simpa [keyJointRisk] using h)
  · simp only [jointKeyWorldCore, jointLocal, QueryImpl.add_apply_inr, StateT.run_bind]
    rw [jointHash_eq_of_unused prims (.streamKey x.2.1) s (by
      intro k hk; cases hk; simpa [keyJointRisk] using h)]
  · exact jointProgram_eq_of_unused p s (by
      intro k hk; rcases p with ⟨p, v⟩; dsimp at hk; subst p
      simpa [keyJointRisk] using h)
  · rfl
  · exact jointHash_eq_of_unused prims q s (by
      intro k hk; subst q; simpa [keyJointRisk] using h)
  · by_cases hh : Hidden D x.1
    · simp only [jointKeyWorldCore, if_pos hh, StateT.run_bind]
      rw [jointHidden_eq_of_fresh (x.1, x.2.1) s (by
        intro hk
        simpa [keyJointRisk, hh, hk] using h)]
    · simp only [jointKeyWorldCore, if_neg hh, jointLocal, QueryImpl.add_apply_inr, StateT.run_bind]
      rw [jointHash_eq_of_unused prims (.streamKey x.2.1) s (by
        intro k hk; cases hk; simpa [keyJointRisk, hh] using h)]

/-- The flag is absorbing, and also records a risk at the current query. -/
theorem jointKeyWorld_bad (prims : Primitives) (D : C.Coalition) (real : Bool)
    (q : (WorldSpec C).Domain) (s : KeyJointState C)
    (r : (WorldSpec C).Range q × KeyJointState C)
    (hr : r ∈ support ((jointKeyWorld prims D real q).run s)) :
    r.2.bad = (s.bad || keyJointRisk D q s) := by
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, _, rfl⟩ := hr
  rfl

/-- The monitored worlds assign identical mass to every good answer and successor state. -/
theorem jointKeyWorld_good (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C)
    (r : (WorldSpec C).Range q × KeyJointState C) (hr : r.2.bad ≠ true) :
    Pr[= r | (jointKeyWorld prims D true q).run s] =
      Pr[= r | (jointKeyWorld prims D false q).run s] := by
  by_cases h : keyJointRisk D q s = false
  · simp only [jointKeyWorld, StateT.run_mk, jointKeyWorldCore_eq_of_no_risk prims D q s h]
  · have hz (real : Bool) : Pr[= r | (jointKeyWorld prims D real q).run s] = 0 := by
      rw [probOutput_eq_zero_iff]
      intro hm
      have hb := jointKeyWorld_bad prims D real q s r hm
      have ht : keyJointRisk D q s = true := Bool.eq_true_of_not_eq_false h
      exact hr (hb.trans (by simp [ht]))
    rw [hz true, hz false]

/-- The full adaptive computation differs by at most the monitored stream-key bad event.
Application to the original worlds additionally requires cache projection lemmas. -/
theorem jointKeyWorld_coupling (prims : Primitives) (D : C.Coalition) {α : Type}
    (game : OracleComp (WorldSpec C) α) (s : KeyJointState C) :
    tvDist ((simulateQ (jointKeyWorld prims D true) game).run' s)
      ((simulateQ (jointKeyWorld prims D false) game).run' s) ≤
      Pr[fun r => r.2.bad = true | (simulateQ (jointKeyWorld prims D true) game).run s].toReal := by
  refine tvDist_simulateQ_le_probBad_of_good_outputs _ _ (fun s => s.bad = true) ?_ ?_ ?_ game s
  · exact fun q s r hr => jointKeyWorld_good prims D q s r hr
  · intro q s hs r hr
    rw [jointKeyWorld_bad prims D true q s r hr, hs]
    rfl
  · intro q s hs r hr
    rw [jointKeyWorld_bad prims D false q s r hr, hs]
    rfl

end ThresholdLeanXmssSecurity
end KeyJointCoupling

section KeyIdealProjection
namespace ThresholdLeanXmssSecurity
open OracleComp.DeferredSampling
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def splitHalves (output : HashOutput) : Digest × Digest :=
  (truncateHash output, output.extractLsb' digestBits digestBits)

theorem splitHalves_bijective : Function.Bijective splitHalves := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fun x y heq => ?_, by simp [Fintype.card_prod, hashOutputBits, digestBits]⟩
  have hlow := congrArg Prod.fst heq
  have hhigh := congrArg Prod.snd heq
  simp only [splitHalves, truncateHash] at hlow hhigh
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < digestBits
  · have := congrArg (fun b : Digest => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hlt] using this
  · have hshift : i - digestBits < digestBits := by simp [hashOutputBits, digestBits] at hi ⊢; omega
    have := congrArg (fun b : Digest => b.getLsbD (i - digestBits)) hhigh
    simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
    rwa [show digestBits + (i - digestBits) = i by omega] at this

theorem evalDist_truncateHash_uniform :
    𝒟[truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)] = 𝒟[($ᵗ Digest : ProbComp Digest)] := by
  have hmap : truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput) =
      Prod.fst <$> (splitHalves <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    simp [Functor.map_map, splitHalves]
  rw [hmap, evalDist_map, evalDist_map_bijective_uniform_cross (α := HashOutput) (β := Digest × Digest)
    splitHalves splitHalves_bijective, ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

variable {C : Committee}

def truncateKeyCache (c : FullKeyCache C) : KeyCache C := fun x => (c x).map truncateHash

theorem truncateKeyCache_cacheQuery (c : FullKeyCache C) (x : KeyName C × HashOutput) (v : HashOutput) :
    truncateKeyCache (c.cacheQuery x v) = (truncateKeyCache c).cacheQuery x (truncateHash v) := by
  funext y
  by_cases h : y = x
  · subst y; simp [truncateKeyCache]
  · simp [truncateKeyCache, QueryCache.cacheQuery_of_ne, h]

def keyJointIdealProjection (s : KeyJointState C) : HashCache C × KeyCache C :=
  (s.hash, truncateKeyCache s.keys)

theorem jointHash_false (prims : Primitives) (q : Query C) :
    jointHash prims false q = onJointHash (hashAnswer prims q) := by
  apply StateT.ext; intro s; cases q <;> rfl

theorem jointProgram_false (x : Query C × HashOutput) :
    jointProgram false x = onJointHash (programAnswer x) := by
  apply StateT.ext; intro s; rcases x with ⟨q, v⟩; cases q <;> rfl

theorem jointLocal_false (prims : Primitives) (q : (LocalSpec C).Domain) :
    jointLocal prims false q = onJointHash (localAnswer prims q) := by
  rcases q with u | q | x
  · rfl
  · exact jointHash_false prims q
  · apply StateT.ext; intro s
    simp only [jointLocal, jointHash_false, StateT.run_bind, onJointHash, StateT.run_mk,
      bind_map_left, StateT.run_pure, bind_pure_comp, localAnswer, QueryImpl.add_apply_inr,
      prgAnswer, map_bind, map_pure, StateT.run_map, Functor.map_map]

theorem onJointHash_idealProjection {α : Type} (m : StateT (HashCache C) ProbComp α)
    (s : KeyJointState C) :
    Prod.map id keyJointIdealProjection <$> (onJointHash m).run s =
      (fun r => (r.1, (r.2, truncateKeyCache s.keys))) <$> m.run s.hash := by
  simp [onJointHash, Functor.map_map, keyJointIdealProjection, Function.comp_def]

theorem jointHidden_false_projection (x : KeyName C × HashOutput) (s : KeyJointState C) :
    𝒟[(fun r => (truncateHash r.1, keyJointIdealProjection r.2)) <$> (jointHidden false x).run s] =
      𝒟[(fun r => (r.1, (s.hash, r.2))) <$>
        ((((KeyName C × HashOutput) →ₒ Digest).randomOracle x).run (truncateKeyCache s.keys))] := by
  cases hc : s.keys x with
  | some v =>
    rw [QueryImpl.withCaching_run_some _ (show truncateKeyCache s.keys x = some (truncateHash v) by
      simp [truncateKeyCache, hc])]
    simp [jointHidden, hc, keyJointIdealProjection]
  | none =>
    rw [QueryImpl.withCaching_run_none _ (show truncateKeyCache s.keys x = none by
      simp [truncateKeyCache, hc])]
    simp only [jointHidden, StateT.run_mk, hc, Bool.false_eq_true, if_false,
      bind_pure_comp, Functor.map_map]
    simp only [keyJointIdealProjection, truncateKeyCache_cacheQuery, Function.comp_def]
    have h := congrArg (fun d : SPMF Digest => (fun v => (v, (s.hash, (truncateKeyCache s.keys).cacheQuery x v))) <$> d)
      evalDist_truncateHash_uniform
    simpa only [evalDist_map, Functor.map_map, Function.comp_def, uniformSampleImpl,
      evalDist_uniformSample] using h

theorem jointKeyWorld_false_query_projection (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C) :
    𝒟[Prod.map id keyJointIdealProjection <$> (jointKeyWorld prims D false q).run s] =
      𝒟[(lazyKeyWorld prims D q).run (keyJointIdealProjection s)] := by
  have hf : Prod.map id keyJointIdealProjection <$> (jointKeyWorld prims D false q).run s =
      Prod.map id keyJointIdealProjection <$> (jointKeyWorldCore prims D false q).run s := by
    simp [jointKeyWorld, Functor.map_map, Function.comp_def, keyJointIdealProjection, Prod.map]
    rfl
  rw [hf]
  rcases q with ((u | q | x) | p) | (u | q | x)
  all_goals simp only [jointKeyWorldCore]
  all_goals try simp only [jointLocal_false, jointProgram_false, onJointHash_idealProjection,
    lazyKeyWorld, StateT.run_mk, keyJointIdealProjection, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr]
  all_goals try rfl
  case inr.inr.inr =>
    by_cases hh : Hidden D x.1
    · simp only [if_pos hh, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map,
        Functor.map_map]
      have h := congrArg (fun d : SPMF (Digest × HashCache C × KeyCache C) =>
        (fun r => (prims.aes.eval r.1 x.2.2, r.2)) <$> d) (jointHidden_false_projection (x.1, x.2.1) s)
      simpa only [evalDist_map, Functor.map_map, Function.comp_def, Prod.map, id_eq, StateT.run_mk,
        keyJointIdealProjection] using h
    · simp only [if_neg hh, jointLocal_false, onJointHash_idealProjection, StateT.run_mk]
      rfl

/-- Distributional state projection, including samplers with different representations. -/
theorem evalDist_simulateQ_state_projection {ι σ τ α : Type} {spec : OracleSpec ι}
    (I : QueryImpl spec (StateT σ ProbComp)) (J : QueryImpl spec (StateT τ ProbComp))
    (π : σ → τ)
    (hstep : ∀ q s, 𝒟[Prod.map id π <$> (I q).run s] = 𝒟[(J q).run (π s)])
    (game : OracleComp spec α) (s : σ) :
    𝒟[Prod.map id π <$> (simulateQ I game).run s] = 𝒟[(simulateQ J game).run (π s)] := by
  induction game using OracleComp.inductionOn generalizing s with
  | pure a => simp
  | query_bind q k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, map_bind]
    calc
      𝒟[(I q).run s >>= fun p => Prod.map id π <$> (simulateQ I (k p.1)).run p.2] =
          𝒟[(I q).run s >>= fun p => (simulateQ J (k p.1)).run (π p.2)] :=
        evalDist_bind_congr_left _ _ _ fun p => ih p.1 p.2
      _ = 𝒟[(Prod.map id π <$> (I q).run s) >>= fun p => (simulateQ J (k p.1)).run p.2] := by
        simp only [bind_map_left, Prod.map, id_eq]
      _ = 𝒟[(J q).run (π s) >>= fun p => (simulateQ J (k p.1)).run p.2] := by
        rw [evalDist_bind, hstep, ← evalDist_bind]

/-- The ideal monitored handler projects to the previously proved lazy AES-key world. -/
theorem jointKeyWorld_false_projection (prims : Primitives) (D : C.Coalition) {α : Type}
    (game : OracleComp (WorldSpec C) α) (s : KeyJointState C) :
    𝒟[(simulateQ (jointKeyWorld prims D false) game).run' s] =
      𝒟[(simulateQ (lazyKeyWorld prims D) game).run' (keyJointIdealProjection s)] := by
  have h := evalDist_simulateQ_state_projection (jointKeyWorld prims D false) (lazyKeyWorld prims D)
    keyJointIdealProjection (jointKeyWorld_false_query_projection prims D) game s
  have hp := congrArg (fun d : SPMF (α × HashCache C × KeyCache C) => Prod.fst <$> d) h
  simpa only [StateT.run'_eq, evalDist_map, Functor.map_map, Function.comp_def, Prod.map, id_eq] using hp

end ThresholdLeanXmssSecurity
end KeyIdealProjection

section KeyRealProjection
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee}

/-- The real hash cache contains both the public and deferred private answers. -/
def KeyJointState.realCache (s : KeyJointState C) : HashCache C := fun q => match q with
  | .streamKey k => s.hash q <|> s.privateHash k
  | _ => s.hash q

/-- Names for one hidden key agree, and a public copy agrees with its private copy. -/
def KeyJointState.Coherent (s : KeyJointState C) : Prop :=
  (∀ x v, s.keys x = some v → s.privateHash x.2 = some v) ∧
  (∀ k v, s.privateHash k = some v → s.hash (.streamKey k) = none ∨ s.hash (.streamKey k) = some v) ∧
  (∀ k, (s.used k).isSome = (s.privateHash k).isSome)

/-- Register the first name of a key and its full private hash answer. -/
def keyJointInsert (s : KeyJointState C) (x : KeyName C × HashOutput) (v : HashOutput) : KeyJointState C :=
  { s with keys := s.keys.cacheQuery x v,
           used := if (s.used x.2).isSome then s.used else Function.update s.used x.2 (some x.1) }

theorem realCache_private (s : KeyJointState C) (hs : s.Coherent) (k : HashOutput) (v : HashOutput)
    (h : s.privateHash k = some v) : s.realCache (.streamKey k) = some v := by
  rcases hs.2.1 k v h with hh | hh <;> simp [KeyJointState.realCache, h, hh]

theorem realCache_keys (s : KeyJointState C) (hs : s.Coherent) (x : KeyName C × HashOutput) (v : HashOutput)
    (h : s.keys x = some v) : s.realCache (.streamKey x.2) = some v :=
  realCache_private s hs x.2 v (hs.1 x v h)

theorem privateHash_keyJointInsert (s : KeyJointState C) (hs : s.Coherent)
    (x : KeyName C × HashOutput) (v : HashOutput)
    (hv : s.realCache (.streamKey x.2) = none ∨ s.realCache (.streamKey x.2) = some v) :
    (keyJointInsert s x v).privateHash = Function.update s.privateHash x.2 (some v) := by
  have hp : s.privateHash x.2 = none ∨ s.privateHash x.2 = some v := by
    cases hc : s.privateHash x.2 with
    | none => exact Or.inl rfl
    | some w =>
      have hfull := realCache_private s hs x.2 w hc
      rcases hv with hv | hv
      · rw [hfull] at hv; contradiction
      · rw [hfull] at hv; cases hv; exact Or.inr rfl
  funext k
  by_cases hk : k = x.2
  · subst k
    cases hu : s.used x.2 with
    | none => simp [keyJointInsert, KeyJointState.privateHash, hu]
    | some name =>
      have hsome : (s.privateHash x.2).isSome = true := by simpa [hu] using (hs.2.2 x.2).symm
      have hpv : s.privateHash x.2 = some v := by
        rcases hp with hp | hp
        · simp [hp] at hsome
        · exact hp
      have hkey : s.keys (name, x.2) = some v := by
        simpa [KeyJointState.privateHash, hu] using hpv
      by_cases hn : name = x.1
      · subst name; simp [keyJointInsert, KeyJointState.privateHash, hu]
      · have hnx : (name, x.2) ≠ x := fun he => hn (congrArg Prod.fst he)
        simp [keyJointInsert, KeyJointState.privateHash, hu, QueryCache.cacheQuery_of_ne, hnx, hkey]
  · have hn : ∀ name, (name, k) ≠ x := by intro name h; exact hk (congrArg Prod.snd h)
    simp only [keyJointInsert, KeyJointState.privateHash]
    split_ifs
    · cases hu : s.used k <;> simp [Function.update_of_ne hk, QueryCache.cacheQuery_of_ne, hn, KeyJointState.privateHash, hu]
    · simp only [Function.update_of_ne hk]
      cases hu : s.used k <;> simp [QueryCache.cacheQuery_of_ne, hn, KeyJointState.privateHash, hu]

theorem realCache_keyJointInsert (s : KeyJointState C) (hs : s.Coherent)
    (x : KeyName C × HashOutput) (v : HashOutput)
    (hv : s.realCache (.streamKey x.2) = none ∨ s.realCache (.streamKey x.2) = some v) :
    (keyJointInsert s x v).realCache = s.realCache.cacheQuery (.streamKey x.2) v := by
  have hp := privateHash_keyJointInsert s hs x v hv
  have hh : s.hash (.streamKey x.2) = none ∨ s.hash (.streamKey x.2) = some v := by
    cases hc : s.hash (.streamKey x.2) with
    | none => exact Or.inl rfl
    | some w =>
      have hf : s.realCache (.streamKey x.2) = some w := by simp [KeyJointState.realCache, hc]
      rcases hv with hv | hv
      · rw [hf] at hv; contradiction
      · rw [hf] at hv; cases hv; exact Or.inr rfl
  funext q
  cases q <;> simp only [KeyJointState.realCache, keyJointInsert, QueryCache.cacheQuery, Function.update]
  case streamKey k =>
    change (s.hash (.streamKey k) <|> (keyJointInsert s x v).privateHash k) = _
    rw [hp]
    by_cases hk : k = x.2
    · subst k
      rcases hh with hh | hh <;> simp [hh]
    · simp [hk]
  all_goals simp

theorem coherent_keyJointInsert (s : KeyJointState C) (hs : s.Coherent)
    (x : KeyName C × HashOutput) (v : HashOutput)
    (hv : s.realCache (.streamKey x.2) = none ∨ s.realCache (.streamKey x.2) = some v) :
    (keyJointInsert s x v).Coherent := by
  have hp := privateHash_keyJointInsert s hs x v hv
  refine ⟨?_, ?_, ?_⟩
  · intro y w hw
    change (s.keys.cacheQuery x v) y = some w at hw
    rw [hp]
    by_cases hy : y = x
    · subst y; simp only [QueryCache.cacheQuery_self, Option.some.injEq] at hw
      subst w; simp
    · rw [QueryCache.cacheQuery_of_ne _ _ hy] at hw
      by_cases hk : y.2 = x.2
      · have hfull := realCache_keys s hs y w hw
        rw [hk] at hfull
        rcases hv with hv | hv
        · rw [hfull] at hv; contradiction
        · rw [hfull] at hv; cases hv; simp [hk]
      · simpa [Function.update_of_ne hk] using hs.1 y w hw
  · intro k w hw
    rw [hp] at hw
    by_cases hk : k = x.2
    · subst k; simp only [Function.update_self, Option.some.injEq] at hw
      subst w
      change s.hash (.streamKey x.2) = none ∨ s.hash (.streamKey x.2) = some v
      cases hh : s.hash (.streamKey x.2) with
      | none => exact Or.inl rfl
      | some a =>
        have hf : s.realCache (.streamKey x.2) = some a := by simp [KeyJointState.realCache, hh]
        rcases hv with hv | hv
        · rw [hf] at hv; contradiction
        · rw [hf] at hv; cases hv; exact Or.inr rfl
    · rw [Function.update_of_ne hk] at hw
      exact hs.2.1 k w hw
  · intro k
    rw [hp]
    change ((if (s.used x.2).isSome then s.used else Function.update s.used x.2 (some x.1)) k).isSome = _
    by_cases hk : k = x.2
    · subst k
      cases hu : s.used x.2 <;> simp [hu]
    · split_ifs
      · simpa [Function.update_of_ne hk] using hs.2.2 k
      · simpa [Function.update_of_ne hk] using hs.2.2 k

theorem coherent_hashInsert (s : KeyJointState C) (hs : s.Coherent) (q : Query C) (v : HashOutput)
    (hv : s.realCache q = none ∨ s.realCache q = some v) :
    ({ s with hash := s.hash.cacheQuery q v } : KeyJointState C).Coherent := by
  refine ⟨hs.1, ?_, hs.2.2⟩
  intro k w hw
  change s.privateHash k = some w at hw
  change (s.hash.cacheQuery q v) (.streamKey k) = none ∨ (s.hash.cacheQuery q v) (.streamKey k) = some w
  by_cases hk : .streamKey k = q
  · subst q
    have hf := realCache_private s hs k w hw
    rcases hv with hv | hv
    · rw [hf] at hv; contradiction
    · rw [hf] at hv; cases hv; simp
  · rw [QueryCache.cacheQuery_of_ne _ _ hk]
    exact hs.2.1 k w hw

theorem realCache_hashInsert (s : KeyJointState C) (q : Query C) (v : HashOutput) :
    ({ s with hash := s.hash.cacheQuery q v } : KeyJointState C).realCache =
      s.realCache.cacheQuery q v := by
  funext t
  by_cases ht : t = q
  · subst t
    cases q <;> simp [KeyJointState.realCache, QueryCache.cacheQuery_self]
  · cases t <;> simp [KeyJointState.realCache, QueryCache.cacheQuery_of_ne, ht, KeyJointState.privateHash]

theorem jointHidden_true_projection (x : KeyName C × HashOutput) (s : KeyJointState C) (hs : s.Coherent) :
    Prod.map id KeyJointState.realCache <$> (jointHidden true x).run s =
      (((Query C →ₒ HashOutput).randomOracle (.streamKey x.2)).run s.realCache) := by
  cases hk : s.keys x with
  | some v =>
    rw [QueryImpl.withCaching_run_some _ (realCache_keys s hs x v hk)]
    simp [jointHidden, hk, Prod.map]
  | none =>
    simp only [jointHidden, StateT.run_mk, hk, if_true, pure_bind]
    change Prod.map id KeyJointState.realCache <$>
      (match s.realCache (.streamKey x.2) with
        | some v => pure (v, keyJointInsert s x v)
        | none => ($ᵗ HashOutput : ProbComp HashOutput) >>= fun v => pure (v, keyJointInsert s x v)) = _
    cases hc : s.realCache (.streamKey x.2) with
    | some v =>
      rw [QueryImpl.withCaching_run_some _ hc]
      simp only [pure_bind, map_pure, Prod.map, id_eq]
      rw [realCache_keyJointInsert s hs x v (Or.inr hc)]
      congr 2
      funext q
      by_cases hq : q = .streamKey x.2
      · subst q; simp [hc]
      · simp [QueryCache.cacheQuery_of_ne, hq]
    | none =>
      rw [QueryImpl.withCaching_run_none _ hc]
      simp only [map_bind, map_pure, Prod.map, id_eq]
      apply bind_congr
      intro v
      rw [realCache_keyJointInsert s hs x v (Or.inl hc)]
      rfl

theorem jointHidden_true_coherent (x : KeyName C × HashOutput) (s : KeyJointState C) (hs : s.Coherent) :
    ∀ r ∈ support ((jointHidden true x).run s), r.2.Coherent := by
  cases hk : s.keys x with
  | some v => simpa [jointHidden, hk] using hs
  | none =>
    simp only [jointHidden, StateT.run_mk, hk, if_true, pure_bind]
    change ∀ r ∈ support (match s.realCache (.streamKey x.2) with
        | some v => pure (v, keyJointInsert s x v)
        | none => ($ᵗ HashOutput : ProbComp HashOutput) >>= fun v => pure (v, keyJointInsert s x v)), r.2.Coherent
    cases hc : s.realCache (.streamKey x.2) with
    | some v => simpa using coherent_keyJointInsert s hs x v (Or.inr hc)
    | none =>
      intro r hr
      simp only [support_bind, Set.mem_iUnion, exists_prop, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨v, _, rfl⟩ := hr
      exact coherent_keyJointInsert s hs x v (Or.inl hc)

theorem onJointHash_randomOracle_projection (q : Query C) (s : KeyJointState C)
    (heq : s.realCache q = s.hash q) :
    Prod.map id KeyJointState.realCache <$>
        (onJointHash ((Query C →ₒ HashOutput).randomOracle q)).run s =
      (((Query C →ₒ HashOutput).randomOracle q).run s.realCache) := by
  cases hc : s.hash q with
  | some v =>
    simp only [onJointHash, StateT.run_mk]
    rw [QueryImpl.withCaching_run_some _ hc, QueryImpl.withCaching_run_some _ (heq.trans hc)]
    simp
  | none =>
    simp only [onJointHash, StateT.run_mk]
    rw [QueryImpl.withCaching_run_none _ hc, QueryImpl.withCaching_run_none _ (heq.trans hc)]
    simp only [Functor.map_map]
    congr 1
    funext v
    simp only [Function.comp_def, Prod.map, id_eq]
    rw [realCache_hashInsert]

theorem onJointHash_randomOracle_coherent (q : Query C) (s : KeyJointState C) (hs : s.Coherent)
    (heq : s.realCache q = s.hash q) :
    ∀ r ∈ support ((onJointHash ((Query C →ₒ HashOutput).randomOracle q)).run s), r.2.Coherent := by
  cases hc : s.hash q with
  | some v =>
    simp only [onJointHash, StateT.run_mk]
    rw [QueryImpl.withCaching_run_some _ hc]
    simpa using hs
  | none =>
    simp only [onJointHash, StateT.run_mk]
    rw [QueryImpl.withCaching_run_none _ hc]
    intro r hr
    simp only [Functor.map_map, support_map, Set.mem_image] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact coherent_hashInsert s hs q v (Or.inl (heq.trans hc))

theorem jointHash_true_projection (prims : Primitives) (q : Query C) (s : KeyJointState C) :
    Prod.map id KeyJointState.realCache <$> (jointHash prims true q).run s =
      (hashAnswer prims q).run s.realCache := by
  cases q
  case hash input =>
    by_cases hm : MpcInput input
    · simp [jointHash, hashAnswer, hm, onJointHash]
    · simpa [jointHash, hashAnswer, hm] using onJointHash_randomOracle_projection (.hash input) s rfl
  case streamKey k =>
    cases hh : s.hash (.streamKey k) with
    | some v =>
      simp only [jointHash, StateT.run_mk, if_true, hh, hashAnswer, onJointHash]
      rw [QueryImpl.withCaching_run_some _ hh,
        QueryImpl.withCaching_run_some _ (show s.realCache (.streamKey k) = some v by simp [KeyJointState.realCache, hh])]
      simp
    | none =>
      cases hp : s.privateHash k with
      | none =>
        change Prod.map id KeyJointState.realCache <$> (jointHash prims true (.streamKey k)).run s = _
        simp only [jointHash, StateT.run_mk, if_true, hh, hp]
        exact onJointHash_randomOracle_projection (.streamKey k) s (by simp [KeyJointState.realCache, hh, hp])
      | some v =>
        simp only [jointHash, StateT.run_mk, if_true, hh, hp, map_pure, Prod.map, id_eq, hashAnswer]
        rw [QueryImpl.withCaching_run_some _ (show s.realCache (.streamKey k) = some v by simp [KeyJointState.realCache, hh, hp])]
        rw [realCache_hashInsert]
        congr 2
        funext q
        by_cases hq : q = .streamKey k
        · subst q; simp [KeyJointState.realCache, hh, hp]
        · simp [QueryCache.cacheQuery_of_ne, hq]
  all_goals exact onJointHash_randomOracle_projection _ s rfl

theorem jointHash_true_coherent (prims : Primitives) (q : Query C) (s : KeyJointState C) (hs : s.Coherent) :
    ∀ r ∈ support ((jointHash prims true q).run s), r.2.Coherent := by
  cases q
  case hash input =>
    by_cases hm : MpcInput input
    · simpa [jointHash, hashAnswer, hm, onJointHash] using hs
    · simpa [jointHash, hashAnswer, hm] using onJointHash_randomOracle_coherent (.hash input) s hs rfl
  case streamKey k =>
    cases hh : s.hash (.streamKey k) with
    | some v =>
      simp only [jointHash, StateT.run_mk, if_true, hh, hashAnswer, onJointHash]
      rw [QueryImpl.withCaching_run_some _ hh]
      simpa using hs
    | none =>
      cases hp : s.privateHash k with
      | none =>
        simp only [jointHash, StateT.run_mk, if_true, hh, hp]
        exact onJointHash_randomOracle_coherent (.streamKey k) s hs (by simp [KeyJointState.realCache, hh, hp])
      | some v =>
        simp only [jointHash, StateT.run_mk, if_true, hh, hp, support_pure, Set.mem_singleton_iff]
        intro r hr; subst r
        exact coherent_hashInsert s hs (.streamKey k) v (Or.inr (realCache_private s hs k v hp))
  all_goals exact onJointHash_randomOracle_coherent _ s hs rfl

theorem onJointHash_program_projection (x : Query C × HashOutput) (s : KeyJointState C)
    (heq : s.realCache x.1 = s.hash x.1) :
    Prod.map id KeyJointState.realCache <$> (onJointHash (programAnswer x)).run s =
      (programAnswer x).run s.realCache := by
  simp only [onJointHash, programAnswer, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind,
    heq, StateT.run_pure, StateT.run_set, map_pure]
  split_ifs
  · rfl
  · simp [Prod.map, realCache_hashInsert]

theorem onJointHash_program_coherent (x : Query C × HashOutput) (s : KeyJointState C) (hs : s.Coherent)
    (heq : s.realCache x.1 = s.hash x.1) :
    ∀ r ∈ support ((onJointHash (programAnswer x)).run s), r.2.Coherent := by
  simp only [onJointHash, programAnswer, StateT.run_mk, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_pure, StateT.run_set, map_pure]
  split_ifs with h
  · simpa using hs
  · have hc : s.hash x.1 = none := by simpa using (not_or.mp h).2
    simpa using coherent_hashInsert s hs x.1 x.2 (Or.inl (heq.trans hc))

theorem jointProgram_true_projection (x : Query C × HashOutput) (s : KeyJointState C) :
    Prod.map id KeyJointState.realCache <$> (jointProgram true x).run s =
      (programAnswer x).run s.realCache := by
  rcases x with ⟨q, v⟩
  cases q
  case streamKey k =>
    cases hp : s.privateHash k with
    | none =>
      simp only [jointProgram, StateT.run_mk, hp, Option.isSome_none, Bool.and_false, Bool.false_eq_true, if_false]
      exact onJointHash_program_projection (.streamKey k, v) s (by simp [KeyJointState.realCache, hp])
    | some w =>
      have hc : (s.realCache (.streamKey k)).isSome = true := by simp [KeyJointState.realCache, hp]
      simp [jointProgram, hp, programAnswer, hc]
  all_goals exact onJointHash_program_projection _ s rfl

theorem jointProgram_true_coherent (x : Query C × HashOutput) (s : KeyJointState C) (hs : s.Coherent) :
    ∀ r ∈ support ((jointProgram true x).run s), r.2.Coherent := by
  rcases x with ⟨q, v⟩
  cases q
  case streamKey k =>
    cases hp : s.privateHash k with
    | none =>
      simp only [jointProgram, StateT.run_mk, hp, Option.isSome_none, Bool.and_false, Bool.false_eq_true, if_false]
      exact onJointHash_program_coherent (.streamKey k, v) s hs (by simp [KeyJointState.realCache, hp])
    | some w => simpa [jointProgram, hp] using hs
  all_goals exact onJointHash_program_coherent _ s hs rfl

theorem jointLocal_true_projection (prims : Primitives) (q : (LocalSpec C).Domain) (s : KeyJointState C) :
    Prod.map id KeyJointState.realCache <$> (jointLocal prims true q).run s =
      (localAnswer prims q).run s.realCache := by
  rcases q with u | q | x
  · simp [jointLocal, localAnswer, onJointHash, unifFwdImpl, StateT.run_lift,
      Functor.map_map, Function.comp_def, Prod.map]
  · exact jointHash_true_projection prims q s
  · have h := congrArg (fun p => (fun r : HashOutput × HashCache C => (prims.aes.eval (truncateHash r.1) x.2.2, r.2)) <$> p)
      (jointHash_true_projection prims (.streamKey x.2.1) s)
    simpa [jointLocal, localAnswer, prgAnswer, bind_pure_comp, StateT.run_map,
      Functor.map_map, Function.comp_def, Prod.map] using h

theorem jointLocal_true_coherent (prims : Primitives) (q : (LocalSpec C).Domain)
    (s : KeyJointState C) (hs : s.Coherent) :
    ∀ r ∈ support ((jointLocal prims true q).run s), r.2.Coherent := by
  rcases q with u | q | x
  · simp [jointLocal, onJointHash, unifFwdImpl, StateT.run_lift, Functor.map_map, hs]
  · exact jointHash_true_coherent prims q s hs
  · intro r hr
    simp only [jointLocal, bind_pure_comp, StateT.run_map, support_map, Set.mem_image] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    exact jointHash_true_coherent prims (.streamKey x.2.1) s hs p hp

theorem jointKeyWorldCore_true_projection (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C) (hs : s.Coherent) :
    Prod.map id KeyJointState.realCache <$> (jointKeyWorldCore prims D true q).run s =
      (worldAnswer prims q).run s.realCache := by
  rcases q with ((u | q | x) | p) | (u | q | x)
  · exact jointLocal_true_projection prims (.inl u) s
  · exact jointLocal_true_projection prims (.inr (.inl q)) s
  · exact jointLocal_true_projection prims (.inr (.inr x)) s
  · exact jointProgram_true_projection p s
  · exact jointLocal_true_projection prims (.inl u) s
  · exact jointLocal_true_projection prims (.inr (.inl q)) s
  · by_cases hh : Hidden D x.1
    · simp only [jointKeyWorldCore, if_pos hh, bind_pure_comp, StateT.run_map, Functor.map_map]
      have h := congrArg (fun p => (fun r : HashOutput × HashCache C => (prims.aes.eval (truncateHash r.1) x.2.2, r.2)) <$> p)
        (jointHidden_true_projection (x.1, x.2.1) s hs)
      simpa [worldAnswer, localAnswer, prgAnswer, hashAnswer, bind_pure_comp, StateT.run_map,
        Functor.map_map, Function.comp_def, Prod.map] using h
    · simp only [jointKeyWorldCore, if_neg hh]
      exact jointLocal_true_projection prims (.inr (.inr x)) s

theorem jointKeyWorldCore_true_coherent (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C) (hs : s.Coherent) :
    ∀ r ∈ support ((jointKeyWorldCore prims D true q).run s), r.2.Coherent := by
  rcases q with ((u | q | x) | p) | (u | q | x)
  · exact jointLocal_true_coherent prims (.inl u) s hs
  · exact jointLocal_true_coherent prims (.inr (.inl q)) s hs
  · exact jointLocal_true_coherent prims (.inr (.inr x)) s hs
  · exact jointProgram_true_coherent p s hs
  · exact jointLocal_true_coherent prims (.inl u) s hs
  · exact jointLocal_true_coherent prims (.inr (.inl q)) s hs
  · by_cases hh : Hidden D x.1
    · intro r hr
      simp only [jointKeyWorldCore, if_pos hh, bind_pure_comp, StateT.run_map, support_map, Set.mem_image] at hr
      obtain ⟨p, hp, rfl⟩ := hr
      exact jointHidden_true_coherent (x.1, x.2.1) s hs p hp
    · simp only [jointKeyWorldCore, if_neg hh]
      exact jointLocal_true_coherent prims (.inr (.inr x)) s hs

theorem jointKeyWorld_true_query_projection (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C) (hs : s.Coherent) :
    Prod.map id KeyJointState.realCache <$> (jointKeyWorld prims D true q).run s =
      (worldAnswer prims q).run s.realCache := by
  rw [← jointKeyWorldCore_true_projection prims D q s hs]
  simp [jointKeyWorld, Functor.map_map, Function.comp_def, Prod.map, KeyJointState.realCache, KeyJointState.privateHash]
  rfl

theorem jointKeyWorld_true_coherent (prims : Primitives) (D : C.Coalition)
    (q : (WorldSpec C).Domain) (s : KeyJointState C) (hs : s.Coherent) :
    ∀ r ∈ support ((jointKeyWorld prims D true q).run s), r.2.Coherent := by
  intro r hr
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  exact jointKeyWorldCore_true_coherent prims D q s hs p hp

/-- Merging the public and private caches gives exactly the real world, including after bad. -/
theorem jointKeyWorld_true_projection (prims : Primitives) (D : C.Coalition) {α : Type}
    (game : OracleComp (WorldSpec C) α) (s : KeyJointState C) (hs : s.Coherent) :
    (simulateQ (jointKeyWorld prims D true) game).run' s =
      (simulateQ (worldAnswer prims) game).run' s.realCache :=
  run'_simulateQ_eq_of_query_map_eq_inv' _ _ KeyJointState.Coherent KeyJointState.realCache
    (jointKeyWorld_true_coherent prims D) (jointKeyWorld_true_query_projection prims D) game s hs

end ThresholdLeanXmssSecurity
end KeyRealProjection

section KeyWorldBound
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee}

/-- No hash queries, no used private keys, and no bad event at the start. -/
def keyJointInitial : KeyJointState C := ⟨∅, ∅, fun _ => none, false⟩

theorem keyJointInitial_coherent : (keyJointInitial (C := C)).Coherent := by
  simp [KeyJointState.Coherent, keyJointInitial, KeyJointState.privateHash]

theorem jointKeyWorld_true_accepts (prims : Primitives) (D : C.Coalition)
    (game : OracleComp (WorldSpec C) Bool) :
    (Pr[= true | (simulateQ (jointKeyWorld prims D true) game).run' keyJointInitial]).toReal =
      accepts prims game := by
  rw [jointKeyWorld_true_projection prims D game keyJointInitial keyJointInitial_coherent]
  have hi : (keyJointInitial (C := C)).realCache = ∅ := by
    funext q; cases q <;> rfl
  rw [hi]
  rw [← fst_map_runWorld prims game]
  simp [accepts, probOutput_map]

theorem jointKeyWorld_false_probability (prims : Primitives) (D : C.Coalition)
    (game : OracleComp (WorldSpec C) Bool) :
    Pr[= true | (simulateQ (jointKeyWorld prims D false) game).run' keyJointInitial] =
      Pr[= true | ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
        (simulateQ (keyWorld prims D keys) game).run' ∅] := by
  have h := jointKeyWorld_false_projection prims D game (keyJointInitial (C := C))
  have he : keyJointIdealProjection (keyJointInitial (C := C)) = (∅, ∅) := rfl
  rw [he] at h
  exact (OracleComp.probOutput_congr rfl h).trans (keyTableLazy prims D game).symm

/-- The monitored stream-key bad event in the original real world. -/
def probBad_streamKey (prims : Primitives) (D : C.Coalition)
    (game : OracleComp (WorldSpec C) Bool) : ℝ :=
  (Pr[fun r => r.2.bad = true | (simulateQ (jointKeyWorld prims D true) game).run keyJointInitial]).toReal

/-- The same bad-event probability can be bounded in the independent-key world. -/
theorem probBad_streamKey_eq_ideal (prims : Primitives) (D : C.Coalition)
    (game : OracleComp (WorldSpec C) Bool) :
    probBad_streamKey prims D game =
      (Pr[fun r => r.2.bad = true | (simulateQ (jointKeyWorld prims D false) game).run keyJointInitial]).toReal := by
  unfold probBad_streamKey
  congr 1
  refine simulateQ_probBad_eq _ _ (fun s => s.bad = true) ?_ ?_ ?_ game keyJointInitial
  · exact fun q s r hr => jointKeyWorld_good prims D q s r hr
  · intro q s hs r hr
    rw [jointKeyWorld_bad prims D true q s r hr, hs]
    rfl
  · intro q s hs r hr
    rw [jointKeyWorld_bad prims D false q s r hr, hs]
    rfl

/-- Replacing the real hidden keys by independently sampled AES keys costs at most the single
stream-key bad event. This applies to arbitrary adaptive games, without secrecy assumptions. -/
theorem keyWorld_coupling (prims : Primitives) (D : C.Coalition)
    (game : OracleComp (WorldSpec C) Bool) :
    |accepts prims game -
      (Pr[= true | ($ᵗ (KeyName C × HashOutput → Digest)) >>= fun keys =>
        (simulateQ (keyWorld prims D keys) game).run' ∅]).toReal| ≤ probBad_streamKey prims D game := by
  have h := (abs_probOutput_toReal_sub_le_tvDist
      ((simulateQ (jointKeyWorld prims D true) game).run' keyJointInitial)
      ((simulateQ (jointKeyWorld prims D false) game).run' keyJointInitial)).trans
    (jointKeyWorld_coupling prims D game keyJointInitial)
  rw [jointKeyWorld_true_accepts, jointKeyWorld_false_probability] at h
  exact h

end ThresholdLeanXmssSecurity
end KeyWorldBound

section PrssEchoSecrecy
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E : Type}

theorem prss_readReveal_term (parts : Parts C) (i j : C.Party) (T : C.Term)
    (hi : i ∈ C.holders T) (hj : j ∈ C.holders T) :
    (readReveal .prss (revealTo .prss parts j i) i j).term T = parts.term T := by
  have hT : T ∈ sharedTerms j i := by simp [sharedTerms, Committee.terms, hi, hj]
  have hlt := List.idxOf_lt_length_of_mem hT
  simp [readReveal, revealTo, List.getD_eq_getElem?_getD,
    List.getElem?_append_left, hlt, List.getElem_idxOf]

/-- The actual post-reveal view, without any assumption on corrupt messages. -/
def prssView (parts : C.Party → Parts C) (received : C.Party → Mail C E)
    (i j : C.Party) : Parts C :=
  if j = i then parts i else readReveal .prss (Msg.hashesOf (received i j)) i j

/-- Every hidden derivation has the same honest input at each holder, before the echo check. -/
theorem prss_hiddenTerm_input (D : C.Coalition) (parts : C.Party → Parts C)
    (received : C.Party → Mail C E)
    (hreceived : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i →
      Msg.hashesOf (received i j) = revealTo .prss (parts j) j i)
    (T : C.Term) (hT : Hidden D (.term T)) (i : C.Party) (hi : i ∈ C.holders T) :
    Query.derive (C := C) .prss .term
      ((C.parties.filter (· ∈ C.holders T)).map fun j => (prssView parts received i j).term T) =
      Query.derive .prss .term
        ((C.parties.filter (· ∈ C.holders T)).map fun j => (parts j).term T) := by
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjT : j ∈ C.holders T := of_decide_eq_true (List.mem_filter.mp hj).2
  by_cases hji : j = i
  · subst j; simp [prssView]
  · simp only [prssView, if_neg hji]
    rw [hreceived i j (hidden_term_holders D hT i hi) (hidden_term_holders D hT j hjT) hji]
    exact prss_readReveal_term (parts j) i j T hi hjT

/-- The digest of the keys shared by two parties in the PRSS echo round. -/
def prssEcho (h : Query C → HashOutput) (keys : C.Party → C.Term → HashOutput)
    (i j : C.Party) : HashOutput := h (.sharedKeys .prss ((sharedTerms i j).map (keys i)))

theorem prssEcho_eq_iff (h : Query C → HashOutput) (keys : C.Party → C.Term → HashOutput)
    (i j : C.Party)
    (hn : prssEcho h keys i j = prssEcho h keys j i →
      Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
      Query.sharedKeys .prss ((sharedTerms j i).map (keys j))) :
    prssEcho h keys i j = prssEcho h keys j i ↔
      ∀ T, i ∈ C.holders T → j ∈ C.holders T → keys i T = keys j T := by
  constructor
  · intro he T hi hj
    have hl := (Query.sharedKeys.inj (hn he)).2
    rw [sharedTerms_comm j i] at hl
    exact List.map_eq_map_iff.mp hl T (by simp [sharedTerms, Committee.terms, hi, hj])
  · intro hk
    unfold prssEcho
    rw [sharedTerms_comm j i]
    congr 2
    apply List.map_congr_left
    intro T hT
    have hmem := of_decide_eq_true (List.mem_filter.mp hT).2
    exact hk T hmem.1 hmem.2

/-- Coherent hidden keys cannot change the echo-equality decision outside a hash collision. -/
theorem prssEcho_hidden_invariant (D : C.Coalition) (h h' : Query C → HashOutput)
    (keys keys' : C.Party → C.Term → HashOutput) (i j : C.Party)
    (hk : ∀ T, KnownTo D.1 T → keys i T = keys' i T ∧ keys j T = keys' j T)
    (hh : ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → keys i T = keys j T)
    (hh' : ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → keys' i T = keys' j T)
    (hn : prssEcho h keys i j = prssEcho h keys j i →
      Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
      Query.sharedKeys .prss ((sharedTerms j i).map (keys j)))
    (hn' : prssEcho h' keys' i j = prssEcho h' keys' j i →
      Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys' i)) =
      Query.sharedKeys .prss ((sharedTerms j i).map (keys' j))) :
    prssEcho h keys i j = prssEcho h keys j i ↔ prssEcho h' keys' i j = prssEcho h' keys' j i := by
  rw [prssEcho_eq_iff h keys i j hn, prssEcho_eq_iff h' keys' i j hn']
  apply forall_congr'
  intro T
  apply forall_congr'
  intro hi
  apply forall_congr'
  intro hj
  by_cases hT : KnownTo D.1 T
  · rw [(hk T hT).1, (hk T hT).2]
  · simp only [hh T hT hi hj, hh' T hT hi hj]

/-- Echo delivery includes abort frames from parties that stopped before the echo. -/
def prssEchoInbox (D : C.Coalition) (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h : Query C → HashOutput) (keys : C.Party → C.Term → HashOutput) (i : C.Party) : Mail C E :=
  fun j => if j ∈ D.1 then sent j i else if active j then
    if i = j then none else some (.hashes [prssEcho h keys j i])
    else some .abort

def prssEchoCheck (h : Query C → HashOutput) (keys : C.Party → C.Term → HashOutput)
    (i : C.Party) (inbox : Mail C E) : Prop :=
  ∀ j, j ≠ i → Msg.hashesOf (inbox j) = [prssEcho h keys i j]

theorem prssEchoInbox_abort_invariant (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (h h' : Query C → HashOutput)
    (keys keys' : C.Party → C.Term → HashOutput) (i j : C.Party) :
    Msg.isAbort (prssEchoInbox D active sent h keys i j) =
      Msg.isAbort (prssEchoInbox D active sent h' keys' i j) := by
  unfold prssEchoInbox
  split_ifs <;> rfl

/-- Assuming the stated collision exclusions, replacing coherent hidden keys preserves the
final PRSS check, including selective abort and arbitrary corrupt messages. -/
theorem prssEchoCheck_hidden_invariant (D : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h h' : Query C → HashOutput) (keys keys' : C.Party → C.Term → HashOutput)
    (hk : ∀ i T, i ∉ D.1 → KnownTo D.1 T → keys i T = keys' i T)
    (hh : ∀ i j T, i ∉ D.1 → j ∉ D.1 → ¬ KnownTo D.1 T →
      i ∈ C.holders T → j ∈ C.holders T → keys i T = keys j T)
    (hh' : ∀ i j T, i ∉ D.1 → j ∉ D.1 → ¬ KnownTo D.1 T →
      i ∈ C.holders T → j ∈ C.holders T → keys' i T = keys' j T)
    (hc : ∀ i j, i ∉ D.1 → j ∈ D.1 → prssEcho h keys i j = prssEcho h' keys' i j)
    (hn : ∀ i j, i ∉ D.1 → j ∉ D.1 →
      prssEcho h keys i j = prssEcho h keys j i →
      Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys i)) =
      Query.sharedKeys .prss ((sharedTerms j i).map (keys j)))
    (hn' : ∀ i j, i ∉ D.1 → j ∉ D.1 →
      prssEcho h' keys' i j = prssEcho h' keys' j i →
      Query.sharedKeys (C := C) .prss ((sharedTerms i j).map (keys' i)) =
      Query.sharedKeys .prss ((sharedTerms j i).map (keys' j)))
    (i : C.Party) (hi : i ∉ D.1) :
    prssEchoCheck h keys i (prssEchoInbox D active sent h keys i) ↔
      prssEchoCheck h' keys' i (prssEchoInbox D active sent h' keys' i) := by
  unfold prssEchoCheck
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hji
  by_cases hj : j ∈ D.1
  · simp only [prssEchoInbox, if_pos hj, hc i j hi hj]
  · simp only [prssEchoInbox, if_neg hj]
    by_cases ha : active j
    · simp only [if_pos ha, if_neg (Ne.symm hji), Msg.hashesOf,
        List.cons.injEq, and_true]
      apply eq_comm.trans
      apply Iff.trans _ eq_comm
      exact prssEcho_hidden_invariant D h h' keys keys' i j
        (fun T hT => ⟨hk i T hi hT, hk j T hj hT⟩)
        (hh i j · hi hj) (hh' i j · hi hj) (hn i j hi hj) (hn' i j hi hj)
    · simp [ha, Msg.hashesOf]

/-- A local echo continuation with precomputed digests. The phase-connection lemmas below
identify it with the final continuation of the original PRSS setup. -/
def prssEchoResume (h : Query C → HashOutput) (keys : C.Party → C.Term → HashOutput)
    (i : C.Party) (inbox : Mail C E) (out : PrssKeys C) : PartyM C E RealSpec (PrssKeys C) := do
  if C.parties.any (fun j => Msg.isAbort (inbox j)) then failure else
  require (prssEchoCheck h keys i inbox)
  pure out

theorem advance_prssEchoResume (h : Query C → HashOutput)
    (keys : C.Party → C.Term → HashOutput) (i : C.Party) (inbox : Mail C E) (out : PrssKeys C) :
    advance (prssEchoResume h keys i inbox out).run =
      pure (.done (if C.parties.any (fun j => Msg.isAbort (inbox j)) then none else
        if prssEchoCheck h keys i inbox then some out else none)) := by
  unfold prssEchoResume require
  split_ifs <;> rfl

def prssEchoOutbox (h : Query C → HashOutput) (keys : C.Party → C.Term → HashOutput)
    (i : C.Party) : Mail C E := fun j =>
  if j = i then none else some (.hashes [prssEcho h keys i j])

def prssEchoStep (D : C.Coalition) (active : C.Party → Prop)
    (h : Query C → HashOutput) (out : C.Party → PrssKeys C) (i : C.Party) :
    Step C E RealSpec (PrssKeys C) :=
  if i ∈ D.1 then .done none else if active i then
    .wait (prssEchoOutbox h (fun j => (out j).term) i)
      (fun inbox => (prssEchoResume h (fun j => (out j).term) i inbox (out i)).run)
    else .done none

def prssEchoAccepted (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (h : Query C → HashOutput)
    (keys : C.Party → C.Term → HashOutput) (i : C.Party) : Prop :=
  i ∉ D.1 ∧ active i ∧
    ¬ C.parties.any (fun j => Msg.isAbort (prssEchoInbox D active sent h keys i j)) ∧
    prssEchoCheck h keys i (prssEchoInbox D active sent h keys i)

def prssEchoVisible (D : C.Coalition) (active : C.Party → Prop)
    (h : Query C → HashOutput) (keys : C.Party → C.Term → HashOutput) :
    C.Party → Mail C E := fun c i =>
  if c ∈ D.1 ∧ i ∉ D.1 then if active i then prssEchoOutbox h keys i c else none else none

theorem prssEchoStep_callInput (D : C.Coalition) (active : C.Party → Prop)
    (h : Query C → HashOutput) (out : C.Party → PrssKeys C) (i : C.Party) :
    (prssEchoStep (E := E) D active h out i).callInput = none := by
  unfold prssEchoStep
  split_ifs <;> rfl

theorem prssEchoStep_outbox (D : C.Coalition) (active : C.Party → Prop)
    (h : Query C → HashOutput) (out : C.Party → PrssKeys C) :
    (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then
      (prssEchoStep (E := E) D active h out i).outbox c else none) =
      prssEchoVisible D active h (fun i => (out i).term) := by
  funext c i
  unfold prssEchoStep prssEchoVisible
  split_ifs <;> simp_all [Step.outbox]

theorem prssEchoStep_inbox (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (h : Query C → HashOutput) (out : C.Party → PrssKeys C)
    (i : C.Party) :
    (fun j => if j ∈ D.1 then sent j i else (prssEchoStep D active h out j).delivered i) =
      prssEchoInbox D active sent h (fun j => (out j).term) i := by
  funext j
  unfold prssEchoStep prssEchoInbox prssEchoOutbox
  split_ifs <;> simp_all [Step.delivered]

theorem stepRound_prssEcho (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (active : C.Party → Prop) (h : Query C → HashOutput) (out : C.Party → PrssKeys C)
    (state : A.State) :
    stepRound worldRoles D A noFunctionality state (prssEchoStep D active h out) =
      (do
        let (state', sent) ← worldRoles.adversary (A.round state
          (prssEchoVisible D active h (fun i => (out i).term)))
        pure (state', (fun i => Step.done (C := C) (E := E) (G := RealSpec)
          (if prssEchoAccepted D active sent h (fun j => (out j).term) i then some (out i) else none)), sent)) := by
  simp only [stepRound, prssEchoStep_callInput, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, ↓reduceIte, prssEchoStep_outbox]
  apply bind_congr
  rintro ⟨state', sent⟩
  have hseq : (Concrete.sequenceFin fun j => match prssEchoStep D active h out j with
      | .done value => pure (Step.done value)
      | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
          worldRoles.honest (advance (resume fun k => if k ∈ D.1 then sent k j else
            (prssEchoStep D active h out k).delivered j))
      | .call _ _ => pure (Step.done none)) =
      pure (fun i => Step.done (C := C) (E := E) (G := RealSpec)
        (if prssEchoAccepted D active sent h (fun j => (out j).term) i then some (out i) else none)) := by
    trans Concrete.sequenceFin (fun i => pure (Step.done (C := C) (E := E) (G := RealSpec)
      (if prssEchoAccepted D active sent h (fun j => (out j).term) i then some (out i) else none)))
    · congr 1
      funext i
      by_cases hi : i ∈ D.1
      · simp [prssEchoStep, hi, prssEchoAccepted]
      · by_cases ha : active i
        · have hstep : prssEchoStep (E := E) D active h out i =
              .wait (prssEchoOutbox h (fun j => (out j).term) i)
                (fun inbox => (prssEchoResume h (fun j => (out j).term) i inbox (out i)).run) := by
              simp [prssEchoStep, hi, ha]
          simp only [hstep, if_neg hi]
          change worldRoles.honest (advance
            (prssEchoResume h (fun j => (out j).term) i
              (fun k => if k ∈ D.1 then sent k i else (prssEchoStep D active h out k).delivered i)
              (out i)).run) = _
          rw [prssEchoStep_inbox]
          rw [advance_prssEchoResume]
          simp only [worldRoles, free_pure]
          simp only [prssEchoAccepted, hi, not_false_eq_true, ha, true_and]
          split_ifs <;> simp_all
        · simp [prssEchoStep, hi, ha, prssEchoAccepted]
    · exact sequenceFin_pure _
  have heq := congrArg (fun (os : OracleComp (WorldSpec C) (C.Party → Step C E RealSpec (PrssKeys C))) =>
    os >>= fun steps => pure (state', steps, sent)) hseq
  simp only [pure_bind] at heq
  convert heq using 1
  congr 2
  funext j
  cases prssEchoStep (E := E) D active h out j <;> rfl

theorem prssEchoVisible_congr (D : C.Coalition) (active : C.Party → Prop)
    (h h' : Query C → HashOutput) (keys keys' : C.Party → C.Term → HashOutput)
    (hc : ∀ i j, i ∉ D.1 → j ∈ D.1 → prssEcho h keys i j = prssEcho h' keys' i j) :
    prssEchoVisible (E := E) D active h keys = prssEchoVisible D active h' keys' := by
  funext c i
  unfold prssEchoVisible prssEchoOutbox
  by_cases hd : c ∈ D.1 ∧ i ∉ D.1
  · simp only [if_pos hd, hc i c hd.2 hd.1]
  · simp only [if_neg hd]

theorem prssEchoAccepted_congr (D : C.Coalition) (active : C.Party → Prop)
    (sent : C.Party → Mail C E) (h h' : Query C → HashOutput)
    (keys keys' : C.Party → C.Term → HashOutput)
    (hc : ∀ i, i ∉ D.1 → (prssEchoCheck h keys i (prssEchoInbox D active sent h keys i) ↔
      prssEchoCheck h' keys' i (prssEchoInbox D active sent h' keys' i))) (i : C.Party) :
    prssEchoAccepted D active sent h keys i ↔ prssEchoAccepted D active sent h' keys' i := by
  by_cases hi : i ∈ D.1
  · simp [prssEchoAccepted, hi]
  · simp only [prssEchoAccepted, hi, not_false_eq_true, true_and]
    have hb : (fun j => Msg.isAbort (prssEchoInbox D active sent h keys i j)) =
        fun j => Msg.isAbort (prssEchoInbox D active sent h' keys' i j) := by
      funext j
      exact prssEchoInbox_abort_invariant D active sent h h' keys keys' i j
    rw [hb, hc i hi]

/-- Equal visible echoes give the same adaptive adversary computation. Under `hcheck`, the
projected round also returns the same nonaborting set and corrupt messages. -/
theorem prssEchoRound_observation_eq (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (active : C.Party → Prop) (h h' : Query C → HashOutput) (out out' : C.Party → PrssKeys C)
    (hc : ∀ i j, i ∉ D.1 → j ∈ D.1 →
      prssEcho h (fun k => (out k).term) i j = prssEcho h' (fun k => (out' k).term) i j)
    (hcheck : ∀ (sent : C.Party → Mail C E) i, i ∉ D.1 →
      (prssEchoCheck h (fun k => (out k).term) i
        (prssEchoInbox D active sent h (fun k => (out k).term) i) ↔
      prssEchoCheck h' (fun k => (out' k).term) i
        (prssEchoInbox D active sent h' (fun k => (out' k).term) i)))
    (state : A.State) :
    (fun r => (r.1, fun i => (r.2.1 i).output.isSome, r.2.2)) <$>
      stepRound worldRoles D A noFunctionality state (prssEchoStep D active h out) =
    (fun r => (r.1, fun i => (r.2.1 i).output.isSome, r.2.2)) <$>
      stepRound worldRoles D A noFunctionality state (prssEchoStep D active h' out') := by
  simp only [stepRound_prssEcho, map_bind, map_pure]
  rw [prssEchoVisible_congr D active h h' (fun i => (out i).term) (fun i => (out' i).term) hc]
  apply bind_congr
  rintro ⟨state', sent⟩
  congr 3
  funext i
  have he := prssEchoAccepted_congr D active sent h h' (fun i => (out i).term)
    (fun i => (out' i).term) (hcheck sent) i
  simp only [Step.output, apply_ite Option.isSome,
    Option.isSome_some, Option.isSome_none]
  rw [he]

open OracleComp.ProgramLogic.Relational

/-- The echo round couples with identical adversary state, sent messages, interpreter state and
abort flags. Only the adversary queries the interpreter during this round; the preceding setup
must establish consistency of the precomputed digests with its oracle state. -/
theorem prssEchoRound_rel {σ : Type} (I : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (active : C.Party → Prop) (h h' : Query C → HashOutput) (out out' : C.Party → PrssKeys C)
    (hc : ∀ i j, i ∉ D.1 → j ∈ D.1 →
      prssEcho h (fun k => (out k).term) i j = prssEcho h' (fun k => (out' k).term) i j)
    (hcheck : ∀ (sent : C.Party → Mail C E) i, i ∉ D.1 →
      (prssEchoCheck h (fun k => (out k).term) i
        (prssEchoInbox D active sent h (fun k => (out k).term) i) ↔
      prssEchoCheck h' (fun k => (out' k).term) i
        (prssEchoInbox D active sent h' (fun k => (out' k).term) i)))
    (state : A.State) (s : σ) :
    RelTriple
      ((simulateQ I (stepRound worldRoles D A noFunctionality state (prssEchoStep D active h out))).run s)
      ((simulateQ I (stepRound worldRoles D A noFunctionality state (prssEchoStep D active h' out'))).run s)
      (fun r r' => r.1.1 = r'.1.1 ∧ r.1.2.2 = r'.1.2.2 ∧ r.2 = r'.2 ∧
        ∀ i, (r.1.2.1 i).output.isSome = (r'.1.2.1 i).output.isSome) := by
  simp only [stepRound_prssEcho, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [prssEchoVisible_congr D active h h' (fun i => (out i).term) (fun i => (out' i).term) hc]
  apply relTriple_bind (relTriple_refl _)
  intro r r' hr
  cases hr
  apply relTriple_pure_pure
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i
  have he := prssEchoAccepted_congr D active r.1.2 h h' (fun i => (out i).term)
    (fun i => (out' i).term) (hcheck r.1.2) i
  simp only [Step.output, apply_ite Option.isSome, Option.isSome_some, Option.isSome_none]
  rw [he]

end ThresholdLeanXmssSecurity
end PrssEchoSecrecy

section PrssPhaseConnection
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E : Type}

/-- The two-round prefix of PRSS setup, through the computation of its echo messages. -/
def prssBeforeEcho (i : C.Party) : PartyM C E RealSpec (PrssKeys C × List HashOutput) := do
  let own ← localStep (liftComp (sampleParts : ProbComp (Parts C)) _)
  let commitments ← oracleStep (C.parties.mapM fun j => hashQuery (.commit .prss i j (revealTo .prss own i j)))
  let committed ← exchange fun j => if j = i then none else some (.hashes [commitments.getD j.val 0])
  let revealed ← exchange fun j => if j = i then none else some (.hashes (revealTo .prss own i j))
  let opens ← oracleStep (C.parties.mapM fun j => hashQuery (.commit .prss j i (Msg.hashesOf (revealed j))))
  require (∀ j, j ≠ i → (Msg.hashesOf (revealed j)).length = (revealTo .prss own j i).length ∧
    [opens.getD j.val 0] = Msg.hashesOf (committed j))
  let view := fun j => if j = i then own else readReveal .prss (Msg.hashesOf (revealed j)) i j
  let keys ← oracleStep (deriveKeys .prss i view)
  let shared ← oracleStep (C.parties.mapM fun j => hashQuery (C := C) (.sharedKeys .prss ((sharedTerms i j).map keys.2.1)))
  pure (⟨keys.2.1, keys.2.2⟩, shared)

/-- The last exchange and check of the original PRSS setup. -/
def prssEchoFinish (i : C.Party) (out : PrssKeys C) (shared : List HashOutput) :
    PartyM C E RealSpec (PrssKeys C) := do
  let received ← exchange fun j => if j = i then none else some (.hashes [shared.getD j.val 0])
  require (∀ j, j ≠ i → Msg.hashesOf (received j) = [shared.getD j.val 0])
  pure out

theorem prssSetup_eq_beforeEcho_bind (i : C.Party) :
    (prssSetup i : PartyM C E RealSpec (PrssKeys C)) =
      prssBeforeEcho i >>= fun (out, shared) => prssEchoFinish i out shared := by
  simp only [prssSetup, commitRevealEcho, prssBeforeEcho, prssEchoFinish,
    bind_assoc, pure_bind, reduceCtorEq, ↓reduceIte, List.nil_append]

/-- The original final exchange advances to exactly the echo step used by the coupling. -/
theorem advance_prssEchoFinish (h : Query C → HashOutput) (out : C.Party → PrssKeys C)
    (i : C.Party) (shared : List HashOutput)
    (hs : ∀ j, shared.getD j.val 0 = prssEcho h (fun k => (out k).term) i j) :
    advance (prssEchoFinish (E := E) i (out i) shared).run =
      pure (.wait (prssEchoOutbox h (fun k => (out k).term) i)
        (fun inbox => (prssEchoResume h (fun k => (out k).term) i inbox (out i)).run)) := by
  have hr : (prssEchoFinish (E := E) i (out i) shared).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
        (.inl (.inr (prssEchoOutbox h (fun k => (out k).term) i)))) >>=
          fun inbox => (prssEchoResume h (fun k => (out k).term) i inbox (out i)).run := by
    have ho : (fun j => if j = i then none else some (Msg.hashes (E := E) [shared.getD j.val 0])) =
        prssEchoOutbox h (fun k => (out k).term) i := by
      funext j
      simp only [prssEchoOutbox, hs]
    simp only [prssEchoFinish]
    rw [ho]
    simp only [exchange, OptionT.run_bind, OptionT.lift,
      bind_assoc, OptionT.run_mk, pure_bind, Option.elimM, hs]
    apply bind_congr
    intro inbox
    simp only [Option.elim, prssEchoResume, prssEchoCheck]
    split <;> simp_all [require] <;> split_ifs <;> rfl
  rw [hr]
  rfl

theorem prssEchoStep_of_setup (D : C.Coalition) (active : C.Party → Prop)
    (h : Query C → HashOutput) (out : C.Party → PrssKeys C)
    (shared : C.Party → List HashOutput)
    (hs : ∀ i j, (shared i).getD j.val 0 = prssEcho h (fun k => (out k).term) i j)
    (i : C.Party) :
    (if i ∈ D.1 then pure (.done none) else if active i then
      advance (prssEchoFinish (E := E) i (out i) (shared i)).run else pure (.done none)) =
      pure (prssEchoStep D active h out i) := by
  unfold prssEchoStep
  split_ifs
  · rfl
  · exact advance_prssEchoFinish h out i (shared i) (hs i)
  · rfl

/-- Every lazy-oracle answer is present in its successor cache. -/
theorem randomOracle_answer_cached {Dom R : Type} [DecidableEq Dom] [SampleableType R]
    (q : Dom) (s : (Dom →ₒ R).QueryCache) (r : R × (Dom →ₒ R).QueryCache)
    (hr : r ∈ support (((Dom →ₒ R).randomOracle q).run s)) : r.2 q = some r.1 := by
  cases hs : s q with
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs, support_map] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact QueryCache.cacheQuery_self _ _ _
  | some v =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs, support_pure,
      Set.mem_singleton_iff] at hr
    subst r
    exact hs

/-- Repeated inputs are allowed: a list of lazy-oracle answers agrees with the final cache. -/
theorem randomOracle_mapM_cached {Dom R α : Type} [DecidableEq Dom] [SampleableType R]
    (q : α → Dom) (xs : List α) (s : (Dom →ₒ R).QueryCache)
    (r : List R × (Dom →ₒ R).QueryCache)
    (hr : r ∈ support ((xs.mapM fun x => (Dom →ₒ R).randomOracle (q x)).run s)) :
    s ≤ r.2 ∧ List.Forall₂ (fun x v => r.2 (q x) = some v) xs r.1 := by
  induction xs generalizing s r with
  | nil =>
    simp only [List.mapM_nil, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact ⟨le_rfl, .nil⟩
  | cons x xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure, support_bind,
      support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hr
    obtain ⟨v, hv, rest, hrest, rfl⟩ := hr
    obtain ⟨hgrow, hlist⟩ := ih v.2 rest hrest
    exact ⟨(QueryImpl.withCaching_cache_le uniformSampleImpl (q x) s v hv).trans hgrow,
      .cons (hgrow (randomOracle_answer_cached (q x) s v hv)) hlist⟩

/-- The actual PRSS echo-hash computation leaves all its answers in the real hash cache. -/
theorem prss_sharedQueries_cached (prims : Primitives) (i : C.Party)
    (keys : C.Term → HashOutput) (s : HashCache C) (r : List HashOutput × HashCache C)
    (hr : r ∈ support ((C.parties.mapM fun j =>
      hashAnswer prims (.sharedKeys .prss ((sharedTerms i j).map keys))).run s)) :
    s ≤ r.2 ∧ ∀ j : C.Party,
      r.2 (.sharedKeys .prss ((sharedTerms i j).map keys)) = some (r.1.getD j.val 0) := by
  have hh := randomOracle_mapM_cached (fun j : C.Party =>
    Query.sharedKeys .prss ((sharedTerms i j).map keys)) C.parties s r hr
  refine ⟨hh.1, ?_⟩
  intro j
  have hlen : r.1.length = C.n := by simpa [Committee.parties] using hh.2.length_eq.symm
  have hj₁ : j.val < C.parties.length := by simpa [Committee.parties] using j.isLt
  have hj₂ : j.val < r.1.length := by simpa [hlen] using j.isLt
  have hp : C.parties.get ⟨j.val, hj₁⟩ = j := by simp [Committee.parties]
  have hget := hh.2.get hj₁ hj₂
  have hpQ := congrArg (fun j' : C.Party =>
    Query.sharedKeys (C := C) .prss ((sharedTerms i j').map keys)) hp
  let cache : Query C → Option HashOutput := r.2
  have hpCache := congrArg cache hpQ
  have hget' := hpCache.symm.trans hget
  simpa [List.getD_eq_getElem?_getD, hlen, j.isLt] using hget' 

/-- Choosing `h` from the successor cache discharges the digest hypothesis in the phase bridge. -/
theorem prssEcho_cached_table (prims : Primitives) (i : C.Party)
    (out : C.Party → PrssKeys C) (s : HashCache C) (r : List HashOutput × HashCache C)
    (hr : r ∈ support ((C.parties.mapM fun j =>
      hashAnswer prims (.sharedKeys .prss ((sharedTerms i j).map (out i).term))).run s)) :
    ∀ j, r.1.getD j.val 0 = prssEcho (fun q => (r.2 q).getD 0) (fun k => (out k).term) i j := by
  intro j
  exact (congrArg (fun v : Option HashOutput => v.getD 0)
    ((prss_sharedQueries_cached prims i (out i).term s r hr).2 j)).symm

theorem simulateQ_prss_sharedQueries (prims : Primitives) (i : C.Party)
    (keys : C.Term → HashOutput) :
    simulateQ (localAnswer prims) (liftComp
      (C.parties.mapM fun j => hashQuery (C := C) (.sharedKeys .prss ((sharedTerms i j).map keys)))
      (LocalSpec C)) = C.parties.mapM fun j =>
        hashAnswer prims (.sharedKeys .prss ((sharedTerms i j).map keys)) := by
  rw [localAnswer, QueryImpl.simulateQ_add_liftComp_right, simulateQ_list_mapM]
  congr 1
  funext j
  exact simulateQ_spec_query _ _

/-- The phase bridge uses any supported echo-hash run of the actual local oracle. -/
theorem advance_prssEchoFinish_of_run (prims : Primitives) (i : C.Party)
    (out : C.Party → PrssKeys C) (s : HashCache C) (r : List HashOutput × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) (liftComp
      (C.parties.mapM fun j => hashQuery (C := C) (.sharedKeys .prss ((sharedTerms i j).map (out i).term)))
      (LocalSpec C))).run s)) :
    advance (prssEchoFinish (E := E) i (out i) r.1).run =
      pure (.wait (prssEchoOutbox (fun q => (r.2 q).getD 0) (fun k => (out k).term) i)
        (fun inbox => (prssEchoResume (fun q => (r.2 q).getD 0)
          (fun k => (out k).term) i inbox (out i)).run)) := by
  rw [simulateQ_prss_sharedQueries] at hr
  exact advance_prssEchoFinish _ out i r.1 (prssEcho_cached_table prims i out s r hr)

/-- Attach the next ceremony phase to the pending final PRSS exchange. -/
def prssEchoStepWith {α : Type} (D : C.Coalition) (active : C.Party → Prop)
    (h : Query C → HashOutput) (out : C.Party → PrssKeys C)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec α) (i : C.Party) : Step C E RealSpec α :=
  if i ∈ D.1 then .done none else if active i then
    .wait (prssEchoOutbox h (fun j => (out j).term) i)
      (fun inbox => (prssEchoResume h (fun j => (out j).term) i inbox (out i) >>= k i).run)
    else .done none

theorem advance_prssEchoFinish_bind {α : Type} (h : Query C → HashOutput)
    (out : C.Party → PrssKeys C) (i : C.Party) (shared : List HashOutput)
    (hs : ∀ j, shared.getD j.val 0 = prssEcho h (fun k => (out k).term) i j)
    (k : PrssKeys C → PartyM C E RealSpec α) :
    advance (prssEchoFinish i (out i) shared >>= k).run =
      pure (.wait (prssEchoOutbox h (fun j => (out j).term) i)
        (fun inbox => (prssEchoResume h (fun j => (out j).term) i inbox (out i) >>= k).run)) := by
  rw [advance_bind, advance_prssEchoFinish h out i shared hs, pure_bind]
  rfl

theorem prssEchoStepWith_callInput {α : Type} (D : C.Coalition) (active : C.Party → Prop)
    (h : Query C → HashOutput) (out : C.Party → PrssKeys C)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec α) (i : C.Party) :
    (prssEchoStepWith D active h out k i).callInput = none := by
  unfold prssEchoStepWith
  split_ifs <;> rfl

theorem prssEchoStepWith_outbox {α : Type} (D : C.Coalition) (active : C.Party → Prop)
    (h : Query C → HashOutput) (out : C.Party → PrssKeys C)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec α) (i : C.Party) :
    (prssEchoStepWith D active h out k i).outbox = (prssEchoStep D active h out i).outbox := by
  unfold prssEchoStepWith prssEchoStep
  split_ifs <;> rfl

theorem prssEchoStepWith_delivered {α : Type} (D : C.Coalition) (active : C.Party → Prop)
    (h : Query C → HashOutput) (out : C.Party → PrssKeys C)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec α) (i : C.Party) :
    (prssEchoStepWith D active h out k i).delivered = (prssEchoStep D active h out i).delivered := by
  unfold prssEchoStepWith prssEchoStep
  split_ifs <;> rfl

/-- The last PRSS round splits exactly into the completed setup round and the start of all
continuations. Failed parties remain failed; no extra network round is inserted. -/
theorem stepRound_prssEchoWith_split {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (active : C.Party → Prop)
    (h : Query C → HashOutput) (out : C.Party → PrssKeys C)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec α) (state : A.State) :
    stepRound worldRoles D A noFunctionality state (prssEchoStepWith D active h out k) =
      (do
        let (state', steps, sent) ← stepRound worldRoles D A noFunctionality state (prssEchoStep D active h out)
        let next ← Concrete.sequenceFin fun i => free (continueStep (k i) (steps i))
        pure (state', next, sent)) := by
  rw [stepRound_prssEcho]
  simp only [bind_assoc, pure_bind]
  simp only [stepRound, prssEchoStepWith_callInput, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, ↓reduceIte, prssEchoStepWith_outbox, prssEchoStep_outbox]
  apply bind_congr
  rintro ⟨state', sent⟩
  congr 2
  funext i
  by_cases hi : i ∈ D.1
  · simp [prssEchoStepWith, hi, prssEchoAccepted, continueStep]
  · by_cases ha : active i
    · have hstep : prssEchoStepWith D active h out k i =
          .wait (prssEchoOutbox h (fun j => (out j).term) i)
            (fun inbox => (prssEchoResume h (fun j => (out j).term) i inbox (out i) >>= k i).run) := by
          simp [prssEchoStepWith, hi, ha]
      simp only [hstep, if_neg hi, prssEchoStepWith_delivered]
      rw [prssEchoStep_inbox, advance_bind, advance_prssEchoResume, pure_bind]
      simp only [worldRoles, prssEchoAccepted, hi, not_false_eq_true, ha, true_and]
      split_ifs <;> simp_all [continueStep]
    · simp [prssEchoStepWith, hi, ha, prssEchoAccepted, continueStep]

/-- Sequential local actions preserve every earlier monotone postcondition in their final state. -/
theorem sequenceFin_state_post {σ α : Type} [Preorder σ] : ∀ {n : ℕ}
    (f : Fin n → StateT σ ProbComp α) (P : Fin n → α → σ → Prop)
    (hf : ∀ i s r, r ∈ support ((f i).run s) → s ≤ r.2 ∧ P i r.1 r.2)
    (hm : ∀ i a s t, s ≤ t → P i a s → P i a t)
    (s : σ) (r : (Fin n → α) × σ),
    r ∈ support ((Concrete.sequenceFin f).run s) → s ≤ r.2 ∧ ∀ i, P i (r.1 i) r.2
  | 0, f, P, hf, hm, s, r, hr => by
    simp only [Concrete.sequenceFin, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact ⟨le_rfl, fun i => i.elim0⟩
  | n + 1, f, P, hf, hm, s, r, hr => by
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff, exists_prop] at hr
    obtain ⟨a, ha, tail, ht, rfl⟩ := hr
    have hfirst := hf 0 s a ha
    have htail := sequenceFin_state_post (fun i : Fin n => f i.succ)
      (fun i => P i.succ) (fun i => hf i.succ) (fun i => hm i.succ) a.2 tail ht
    refine ⟨hfirst.1.trans htail.1, ?_⟩
    intro i
    cases i using Fin.cases with
    | zero => exact hm 0 a.1 a.2 tail.2 htail.1 hfirst.2
    | succ i => exact htail.2 i

/-- All active parties' precomputed echoes live in one successor hash cache, even when different
parties query the same input. This is a joint statement for the sequential honest hash run. -/
theorem prss_sharedQueries_joint_cached (prims : Primitives) (active : C.Party → Prop)
    (out : C.Party → PrssKeys C) (s : HashCache C)
    (r : (C.Party → List HashOutput) × HashCache C)
    (hr : r ∈ support ((Concrete.sequenceFin fun i : C.Party =>
      if active i then C.parties.mapM fun j =>
        hashAnswer prims (.sharedKeys .prss ((sharedTerms i j).map (out i).term))
      else pure []).run s)) :
    s ≤ r.2 ∧ ∀ i, active i → ∀ j,
      r.2 (.sharedKeys .prss ((sharedTerms i j).map (out i).term)) = some ((r.1 i).getD j.val 0) := by
  apply sequenceFin_state_post
    (P := fun i (shared : List HashOutput) (cache : HashCache C) => active i → ∀ j,
      cache (.sharedKeys .prss ((sharedTerms i j).map (out i).term)) = some (shared.getD j.val 0))
    _ _ _ _ _ hr
  · intro i cache row hrow
    by_cases ha : active i
    · simp only [if_pos ha] at hrow
      have hh := prss_sharedQueries_cached prims i (out i).term cache row hrow
      exact ⟨hh.1, fun _ => hh.2⟩
    · simp only [if_neg ha, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrow
      subst row
      exact ⟨le_rfl, fun h => (ha h).elim⟩
  · intro i shared cache cache' hle hh ha j
    exact hle (hh ha j)

/-- One function read from the final cache witnesses the actual digest table of every active party. -/
theorem prssEcho_joint_cached_table (prims : Primitives) (active : C.Party → Prop)
    (out : C.Party → PrssKeys C) (s : HashCache C)
    (r : (C.Party → List HashOutput) × HashCache C)
    (hr : r ∈ support ((Concrete.sequenceFin fun i : C.Party =>
      if active i then C.parties.mapM fun j =>
        hashAnswer prims (.sharedKeys .prss ((sharedTerms i j).map (out i).term))
      else pure []).run s)) :
    ∀ i, active i → ∀ j, (r.1 i).getD j.val 0 =
      prssEcho (fun q => (r.2 q).getD 0) (fun k => (out k).term) i j := by
  intro i hi j
  exact (congrArg (fun v : Option HashOutput => v.getD 0)
    ((prss_sharedQueries_joint_cached prims active out s r hr).2 i hi j)).symm

end ThresholdLeanXmssSecurity
end PrssPhaseConnection

section PrssDerivationConnection
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E : Type}

theorem prss_readReveal_pair (parts : Parts C) (i j : C.Party) :
    (readReveal .prss (revealTo .prss parts j i) i j).pair i = parts.pair i := by
  simp [readReveal, revealTo, List.getD_eq_getElem?_getD]

/-- At a hidden pair, both endpoints read precisely the two honest contributions. -/
theorem prss_hiddenPair_input (D : C.Coalition) (parts : C.Party → Parts C)
    (received : C.Party → Mail C E)
    (hreceived : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i →
      Msg.hashesOf (received i j) = revealTo .prss (parts j) j i)
    (p : C.Pair) (hp : Hidden D (.pair p)) (i : C.Party)
    (hi : i = p.1.1 ∨ i = p.1.2) :
    Query.derive (C := C) .prss .pair
      [(prssView parts received i p.1.1).pair p.1.2,
       (prssView parts received i p.1.2).pair p.1.1] =
    Query.derive .prss .pair [(parts p.1.1).pair p.1.2, (parts p.1.2).pair p.1.1] := by
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  have hp' : p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 := hp
  rcases hi with rfl | rfl
  · simp only [prssView, ite_true, if_neg hne.symm]
    rw [hreceived _ _ hp'.1 hp'.2 hne.symm, prss_readReveal_pair]
  · simp only [prssView, ite_true, if_neg hne]
    rw [hreceived _ _ hp'.2 hp'.1 hne, prss_readReveal_pair]

/-- A conditional query list retains every executed query in the final cache. -/
theorem randomOracle_mapM_if_cached {Dom R α : Type} [DecidableEq Dom] [SampleableType R]
    (test : α → Prop) [DecidablePred test] (q : α → Dom) (default : R) (xs : List α)
    (s : (Dom →ₒ R).QueryCache) (r : List R × (Dom →ₒ R).QueryCache)
    (hr : r ∈ support ((xs.mapM fun x => if test x then
      (Dom →ₒ R).randomOracle (q x) else pure default).run s)) :
    s ≤ r.2 ∧ List.Forall₂ (fun x v => test x → r.2 (q x) = some v) xs r.1 := by
  induction xs generalizing s r with
  | nil =>
    simp only [List.mapM_nil, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact ⟨le_rfl, .nil⟩
  | cons x xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure, support_bind,
      support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hr
    obtain ⟨v, hv, rest, hrest, rfl⟩ := hr
    obtain ⟨hgrow, hlist⟩ := ih v.2 rest hrest
    by_cases hx : test x
    · simp only [if_pos hx] at hv
      exact ⟨(QueryImpl.withCaching_cache_le uniformSampleImpl (q x) s v hv).trans hgrow,
        .cons (fun _ => hgrow (randomOracle_answer_cached (q x) s v hv)) hlist⟩
    · simp only [if_neg hx, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hv
      subst v
      exact ⟨hgrow, .cons (fun h => (hx h).elim) hlist⟩

/-- Look up a conditional query list at a named input. -/
theorem forall₂_getD_idxOf {α β : Type} [BEq α] [LawfulBEq α] (R : α → β → Prop)
    (xs : List α) (ys : List β) (h : List.Forall₂ R xs ys) (a : α)
    (ha : a ∈ xs) (b : β) : R a (ys.getD (xs.idxOf a) b) := by
  have hx := List.idxOf_lt_length_of_mem ha
  have hy : xs.idxOf a < ys.length := h.length_eq ▸ hx
  have hh := h.get hx hy
  simpa [List.getD_eq_getElem?_getD, hy, List.getElem_idxOf] using hh

def prssTermQuery (view : C.Party → Parts C) (T : C.Term) : Query C :=
  .derive .prss .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T)

def prssPairQuery (i : C.Party) (view : C.Party → Parts C) (j : C.Party) : Query C :=
  if h : j = i then .derive .prss .pair [] else
    let p := C.pairOf i j (Ne.symm h)
    .derive .prss .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1]

/-- The actual PRSS derivation interpreted by the lazy hash oracle. -/
def prssDerive (i : C.Party) (view : C.Party → Parts C) : StateT (HashCache C) ProbComp (PrssKeys C) := do
  let term ← C.terms.mapM fun T => if i ∈ C.holders T then
    (Query C →ₒ HashOutput).randomOracle (prssTermQuery view T) else pure 0
  let pair ← C.parties.mapM fun j => if j ≠ i then
    (Query C →ₒ HashOutput).randomOracle (prssPairQuery i view j) else pure 0
  pure ⟨fun T => term.getD (C.terms.idxOf T) 0, fun j => pair.getD j.val 0⟩

theorem simulateQ_prssDerive (prims : Primitives) (i : C.Party) (view : C.Party → Parts C) :
    simulateQ (localAnswer prims) (liftComp
      ((fun keys => (⟨keys.2.1, keys.2.2⟩ : PrssKeys C)) <$> deriveKeys .prss i view)
      (LocalSpec C)) = prssDerive i view := by
  simp only [localAnswer, QueryImpl.simulateQ_add_liftComp_right, deriveKeys,
    reduceCtorEq, ↓reduceIte, pure_bind, simulateQ_bind,
    simulateQ_pure, simulateQ_list_mapM, map_bind, map_pure, prssDerive]
  congr 1
  · apply congrArg (fun f : C.Term → StateT (HashCache C) ProbComp HashOutput => C.terms.mapM f)
    funext T
    split_ifs with h
    · simp [hashQuery, prssTermQuery, hashAnswer]
    · simp
  · funext term
    congr 1
    · apply congrArg (fun f : C.Party → StateT (HashCache C) ProbComp HashOutput => C.parties.mapM f)
      funext j
      by_cases h : j = i
      · simp [h]
      · simp only [dif_neg h, if_pos h, prssPairQuery]
        rw [dif_neg h]
        exact simulateQ_spec_query _ _

def PrssDerivedCached (i : C.Party) (view : C.Party → Parts C) (out : PrssKeys C)
    (cache : HashCache C) : Prop :=
  (∀ T, i ∈ C.holders T → cache (prssTermQuery view T) = some (out.term T)) ∧
  (∀ j, j ≠ i → cache (prssPairQuery i view j) = some (out.pair j))

theorem prssDerive_cached (i : C.Party) (view : C.Party → Parts C)
    (s : HashCache C) (r : PrssKeys C × HashCache C)
    (hr : r ∈ support ((prssDerive i view).run s)) :
    s ≤ r.2 ∧ PrssDerivedCached i view r.1 r.2 := by
  simp only [prssDerive, StateT.run_bind, StateT.run_pure, support_bind,
    support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hr
  obtain ⟨term, hterm, pair, hpair, rfl⟩ := hr
  have ht := randomOracle_mapM_if_cached (fun T => i ∈ C.holders T)
    (prssTermQuery view) 0 C.terms s term hterm
  have hp := randomOracle_mapM_if_cached (fun j => j ≠ i)
    (prssPairQuery i view) 0 C.parties term.2 pair hpair
  refine ⟨ht.1.trans hp.1, ?_, ?_⟩
  · intro T hT
    simpa only using hp.1 (forall₂_getD_idxOf _ _ _ ht.2 T (by simp [Committee.terms]) 0 hT)
  · intro j hj
    have hh := forall₂_getD_idxOf _ _ _ hp.2 j (by simp [Committee.parties]) 0 hj
    simpa [Committee.parties] using hh

/-- Deriving keys and hashing their shared lists is one local computation. -/
def prssDeriveEcho (prims : Primitives) (i : C.Party) (view : C.Party → Parts C) :
    StateT (HashCache C) ProbComp (PrssKeys C × List HashOutput) := do
  let out ← prssDerive i view
  let shared ← C.parties.mapM fun j =>
    hashAnswer prims (.sharedKeys .prss ((sharedTerms i j).map out.term))
  pure (out, shared)

/-- This is exactly the two oracle computations between the reveal check and the echo exchange. -/
theorem simulateQ_prssDeriveEcho (prims : Primitives) (i : C.Party) (view : C.Party → Parts C) :
    simulateQ (localAnswer prims) (do
      let keys ← liftComp (deriveKeys .prss i view) (LocalSpec C)
      let shared ← liftComp (C.parties.mapM fun j =>
        hashQuery (C := C) (.sharedKeys .prss ((sharedTerms i j).map keys.2.1))) (LocalSpec C)
      pure ((⟨keys.2.1, keys.2.2⟩ : PrssKeys C), shared)) = prssDeriveEcho prims i view := by
  unfold prssDeriveEcho
  rw [← simulateQ_prssDerive prims i view]
  simp only [simulateQ_bind, simulateQ_pure, liftComp_map, simulateQ_map, bind_map_left]
  apply bind_congr
  intro keys
  rw [simulateQ_prss_sharedQueries]

def PrssDerivedEchoCached (i : C.Party) (view : C.Party → Parts C)
    (row : PrssKeys C × List HashOutput) (cache : HashCache C) : Prop :=
  PrssDerivedCached i view row.1 cache ∧ ∀ j,
    cache (.sharedKeys .prss ((sharedTerms i j).map row.1.term)) = some (row.2.getD j.val 0)

theorem prssDerivedCached_mono (i : C.Party) (view : C.Party → Parts C)
    (out : PrssKeys C) {s t : HashCache C} (hst : s ≤ t)
    (h : PrssDerivedCached i view out s) : PrssDerivedCached i view out t :=
  ⟨fun T hT => hst (h.1 T hT), fun j hj => hst (h.2 j hj)⟩

theorem prssDerivedEchoCached_mono (i : C.Party) (view : C.Party → Parts C)
    (row : PrssKeys C × List HashOutput) {s t : HashCache C} (hst : s ≤ t)
    (h : PrssDerivedEchoCached i view row s) : PrssDerivedEchoCached i view row t :=
  ⟨prssDerivedCached_mono i view row.1 hst h.1, fun j => hst (h.2 j)⟩

theorem prssDeriveEcho_cached (prims : Primitives) (i : C.Party) (view : C.Party → Parts C)
    (s : HashCache C) (r : (PrssKeys C × List HashOutput) × HashCache C)
    (hr : r ∈ support ((prssDeriveEcho prims i view).run s)) :
    s ≤ r.2 ∧ PrssDerivedEchoCached i view r.1 r.2 := by
  simp only [prssDeriveEcho, StateT.run_bind, StateT.run_pure, support_bind,
    support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hr
  obtain ⟨out, hout, shared, hshared, rfl⟩ := hr
  have ho := prssDerive_cached i view s out hout
  have hs := prss_sharedQueries_cached prims i out.1.term out.2 shared hshared
  exact ⟨ho.1.trans hs.1, prssDerivedCached_mono i view out.1 hs.1 ho.2, hs.2⟩

/-- The next party may derive its keys after the preceding party has already hashed its echoes.
The invariant retains both kinds of answers in the final joint cache. -/
theorem prssDeriveEcho_joint_cached (prims : Primitives) (active : C.Party → Prop)
    (view : C.Party → C.Party → Parts C) (s : HashCache C)
    (r : (C.Party → PrssKeys C × List HashOutput) × HashCache C)
    (hr : r ∈ support ((Concrete.sequenceFin fun i : C.Party =>
      if active i then prssDeriveEcho prims i (view i)
      else pure (⟨fun _ => 0, fun _ => 0⟩, [])).run s)) :
    s ≤ r.2 ∧ ∀ i, active i → PrssDerivedEchoCached i (view i) (r.1 i) r.2 := by
  apply sequenceFin_state_post
    (P := fun i row cache => active i → PrssDerivedEchoCached i (view i) row cache)
    _ _ _ _ _ hr
  · intro i cache row hrow
    by_cases ha : active i
    · simp only [if_pos ha] at hrow
      have hh := prssDeriveEcho_cached prims i (view i) cache row hrow
      exact ⟨hh.1, fun _ => hh.2⟩
    · simp only [if_neg ha, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hrow
      subst row
      exact ⟨le_rfl, fun h => (ha h).elim⟩
  · intro i row cache cache' hle hh ha
    exact prssDerivedEchoCached_mono i (view i) row hle (hh ha)

/-- A supported common-cache derivation gives one key for every hidden term at its active holders. -/
theorem prssDerived_hiddenTerm_coherent (D : C.Coalition) (parts : C.Party → Parts C)
    (received : C.Party → Mail C E)
    (hreceived : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i →
      Msg.hashesOf (received i j) = revealTo .prss (parts j) j i)
    (active : C.Party → Prop) (out : C.Party → PrssKeys C) (cache : HashCache C)
    (hc : ∀ i, active i → PrssDerivedCached i (prssView parts received i) (out i) cache)
    (T : C.Term) (hT : Hidden D (.term T)) (i j : C.Party)
    (hai : active i) (haj : active j) (hi : i ∈ C.holders T) (hj : j ∈ C.holders T) :
    (out i).term T = (out j).term T := by
  have hqi := prss_hiddenTerm_input D parts received hreceived T hT i hi
  have hqj := prss_hiddenTerm_input D parts received hreceived T hT j hj
  have hci := (hc i hai).1 T hi
  have hcj := (hc j haj).1 T hj
  change cache (Query.derive .prss .term _) = _ at hci hcj
  rw [hqi] at hci
  rw [hqj] at hcj
  exact Option.some.inj (hci.symm.trans hcj)

/-- The same cache argument gives agreement at both endpoints of a hidden pair. -/
theorem prssDerived_hiddenPair_coherent (D : C.Coalition) (parts : C.Party → Parts C)
    (received : C.Party → Mail C E)
    (hreceived : ∀ i j, i ∉ D.1 → j ∉ D.1 → j ≠ i →
      Msg.hashesOf (received i j) = revealTo .prss (parts j) j i)
    (active : C.Party → Prop) (out : C.Party → PrssKeys C) (cache : HashCache C)
    (hc : ∀ i, active i → PrssDerivedCached i (prssView parts received i) (out i) cache)
    (p : C.Pair) (hp : Hidden D (.pair p)) (ha : active p.1.1) (hb : active p.1.2) :
    (out p.1.1).pair p.1.2 = (out p.1.2).pair p.1.1 := by
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  have hci := (hc p.1.1 ha).2 p.1.2 hne.symm
  have hcj := (hc p.1.2 hb).2 p.1.1 hne
  have hpa : C.pairOf p.1.1 p.1.2 hne = p := by
    simp [Committee.pairOf, p.2]
  have hpb : C.pairOf p.1.2 p.1.1 hne.symm = p := by
    simp [Committee.pairOf, not_lt.mpr (le_of_lt p.2)]
  have hqi : prssPairQuery p.1.1 (prssView parts received p.1.1) p.1.2 =
      Query.derive .prss .pair [(parts p.1.1).pair p.1.2, (parts p.1.2).pair p.1.1] := by
    simp only [prssPairQuery, dif_neg hne.symm, hpa]
    exact prss_hiddenPair_input D parts received hreceived p hp _ (Or.inl rfl)
  have hqj : prssPairQuery p.1.2 (prssView parts received p.1.2) p.1.1 =
      Query.derive .prss .pair [(parts p.1.1).pair p.1.2, (parts p.1.2).pair p.1.1] := by
    simp only [prssPairQuery, dif_neg hne, hpb]
    exact prss_hiddenPair_input D parts received hreceived p hp _ (Or.inr rfl)
  rw [hqi] at hci
  rw [hqj] at hcj
  exact Option.some.inj (hci.symm.trans hcj)

end ThresholdLeanXmssSecurity

end PrssDerivationConnection

section PrssReachablePrefix
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

def prssOpenCheck (i : C.Party) (own : Parts C) (committed revealed : Mail C E)
    (opens : List HashOutput) : Prop :=
  ∀ j, j ≠ i → (Msg.hashesOf (revealed j)).length = (revealTo .prss own j i).length ∧
    [opens.getD j.val 0] = Msg.hashesOf (committed j)

/-- The actual party program after a successful reveal exchange. -/
def prssPostReveal (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    PartyM C E RealSpec (PrssKeys C) := do
  let opens ← oracleStep (C.parties.mapM fun j => hashQuery (.commit .prss j i (Msg.hashesOf (revealed j))))
  require (prssOpenCheck i own committed revealed opens)
  let view := fun j => if j = i then own else readReveal .prss (Msg.hashesOf (revealed j)) i j
  let keys ← oracleStep (deriveKeys .prss i view)
  let shared ← oracleStep (C.parties.mapM fun j =>
    hashQuery (C := C) (.sharedKeys .prss ((sharedTerms i j).map keys.2.1)))
  prssEchoFinish i ⟨keys.2.1, keys.2.2⟩ shared

/-- The local part of the reveal-round transition, keeping the actual derived keys and echo hashes. -/
def prssPostRevealData (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    OracleComp (LocalSpec C) (Option (PrssKeys C × List HashOutput)) := do
  let opens ← liftComp (C.parties.mapM fun j =>
    hashQuery (.commit .prss j i (Msg.hashesOf (revealed j)))) (LocalSpec C)
  if prssOpenCheck i own committed revealed opens then
    let view := fun j => if j = i then own else readReveal .prss (Msg.hashesOf (revealed j)) i j
    let keys ← liftComp (deriveKeys .prss i view) (LocalSpec C)
    let shared ← liftComp (C.parties.mapM fun j =>
      hashQuery (C := C) (.sharedKeys .prss ((sharedTerms i j).map keys.2.1))) (LocalSpec C)
    pure (some (⟨keys.2.1, keys.2.2⟩, shared))
  else pure none

theorem prssSetup_eq_reveal_prefix (i : C.Party) :
    (prssSetup i : PartyM C E RealSpec (PrssKeys C)) = (do
      let own ← localStep (liftComp (sampleParts : ProbComp (Parts C)) _)
      let commitments ← oracleStep (C.parties.mapM fun j =>
        hashQuery (.commit .prss i j (revealTo .prss own i j)))
      let committed ← exchange fun j => if j = i then none else some (.hashes [commitments.getD j.val 0])
      let revealed ← exchange fun j => if j = i then none else some (.hashes (revealTo .prss own i j))
      prssPostReveal i own committed revealed) := by
  simp only [prssSetup, commitRevealEcho, prssPostReveal, prssOpenCheck, prssEchoFinish,
    bind_assoc, pure_bind, reduceCtorEq, ↓reduceIte, List.nil_append]

theorem advance_prssPostReveal (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    advance (prssPostReveal i own committed revealed).run =
      prssPostRevealData i own committed revealed >>= fun row =>
        match row with
        | none => pure (.done none)
        | some row => advance (prssEchoFinish i row.1 row.2).run := by
  unfold prssPostReveal prssPostRevealData
  rw [advance_oracleStep_bind]
  simp only [bind_assoc]
  apply bind_congr
  intro opens
  rw [advance_require_bind]
  split_ifs
  · rw [advance_oracleStep_bind]
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro keys
    rw [advance_oracleStep_bind]
  · simp

/-- Interpret the actual local work as opening checks followed by the cached derivation stage. -/
theorem simulateQ_prssPostRevealData (prims : Primitives) (i : C.Party) (own : Parts C)
    (committed revealed : Mail C E) :
    simulateQ (localAnswer prims) (prssPostRevealData i own committed revealed) = (do
      let opens ← C.parties.mapM fun j =>
        hashAnswer prims (.commit .prss j i (Msg.hashesOf (revealed j)))
      if prssOpenCheck i own committed revealed opens then
        some <$> prssDeriveEcho prims i (fun j =>
          if j = i then own else readReveal .prss (Msg.hashesOf (revealed j)) i j)
      else pure none) := by
  have hopen : simulateQ (localAnswer prims) (liftComp (C.parties.mapM fun j =>
      hashQuery (.commit .prss j i (Msg.hashesOf (revealed j)))) (LocalSpec C)) =
      C.parties.mapM fun j => hashAnswer prims (.commit .prss j i (Msg.hashesOf (revealed j))) := by
    rw [localAnswer, QueryImpl.simulateQ_add_liftComp_right, simulateQ_list_mapM]
    congr 1
    funext j
    exact simulateQ_spec_query _ _
  simp only [prssPostRevealData, simulateQ_bind, hopen]
  apply bind_congr
  intro opens
  split_ifs
  · rw [← simulateQ_prssDeriveEcho prims i]
    simp only [simulateQ_bind, simulateQ_pure, map_bind, map_pure]
  · simp

/-- The actual opening check may fail. Every key returned by a successful local transition is
nevertheless the value of its derivation in the successor cache. -/
theorem prssPostRevealData_cached (prims : Primitives) (i : C.Party) (own : Parts C)
    (committed revealed : Mail C E) (s : HashCache C)
    (r : Option (PrssKeys C × List HashOutput) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssPostRevealData i own committed revealed)).run s)) :
    s ≤ r.2 ∧ ∀ row, r.1 = some row → PrssDerivedEchoCached i
      (fun j => if j = i then own else readReveal .prss (Msg.hashesOf (revealed j)) i j) row r.2 := by
  rw [simulateQ_prssPostRevealData] at hr
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hr
  obtain ⟨opens, hopens, hr⟩ := hr
  have ho := randomOracle_mapM_cached (fun j : C.Party =>
    Query.commit .prss j i (Msg.hashesOf (revealed j))) C.parties s opens hopens
  by_cases hc : prssOpenCheck i own committed revealed opens.1
  · simp only [if_pos hc, StateT.run_map, support_map] at hr
    obtain ⟨out, hout, rfl⟩ := hr
    have hd := prssDeriveEcho_cached prims i _ opens.2 out hout
    refine ⟨ho.1.trans hd.1, ?_⟩
    intro row he
    cases Option.some.inj he
    exact hd.2
  · simp only [if_neg hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact ⟨ho.1, fun _ h => (by cases h)⟩

def prssRevealData (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    OracleComp (LocalSpec C) (Option (PrssKeys C × List HashOutput)) :=
  if C.parties.any fun j => Msg.isAbort (revealed j) then pure none
  else prssPostRevealData i own committed revealed

def prssFinishStep (i : C.Party) (row : Option (PrssKeys C × List HashOutput)) :
    Step C E RealSpec (PrssKeys C) :=
  match row with
  | none => .done none
  | some (out, shared) => .wait
      (fun j => if j = i then none else some (.hashes [shared.getD j.val 0]))
      (exchangeResume fun received => do
        require (∀ j, j ≠ i → Msg.hashesOf (received j) = [shared.getD j.val 0])
        pure out)

theorem advance_prssEchoFinish_row (i : C.Party) (out : PrssKeys C) (shared : List HashOutput) :
    advance (prssEchoFinish (E := E) i out shared).run =
      pure (prssFinishStep i (some (out, shared))) := by
  exact advance_exchange_bind _ _

theorem advance_prssRevealResume (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    advance (exchangeResume (fun revealed => prssPostReveal i own committed revealed) revealed) =
      prssFinishStep i <$> prssRevealData i own committed revealed := by
  unfold exchangeResume prssRevealData
  split_ifs
  · rfl
  · rw [advance_prssPostReveal, map_eq_bind_pure_comp]
    apply bind_congr
    intro row
    cases row with
    | none => rfl
    | some row => exact advance_prssEchoFinish_row i row.1 row.2

/-- Receiving an abort frame prevents a returned row; successful rows also retain their cached keys. -/
theorem prssRevealData_cached (prims : Primitives) (i : C.Party) (own : Parts C)
    (committed revealed : Mail C E) (s : HashCache C)
    (r : Option (PrssKeys C × List HashOutput) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssRevealData i own committed revealed)).run s)) :
    s ≤ r.2 ∧ ∀ row, r.1 = some row →
      (C.parties.any fun j => Msg.isAbort (revealed j)) = false ∧
      PrssDerivedEchoCached i
        (fun j => if j = i then own else readReveal .prss (Msg.hashesOf (revealed j)) i j) row r.2 := by
  unfold prssRevealData at hr
  split_ifs at hr with ha
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact ⟨le_rfl, fun _ h => (by cases h)⟩
  · obtain ⟨hg, hc⟩ := prssPostRevealData_cached prims i own committed revealed s r hr
    exact ⟨hg, fun row he => ⟨Bool.eq_false_iff.mpr ha, hc row he⟩⟩

def prssRevealOutbox (own : Parts C) (i : C.Party) : Mail C E :=
  fun j => if j = i then none else some (.hashes (revealTo .prss own i j))

def prssRevealStep (D : C.Coalition) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) (i : C.Party) : Step C E RealSpec (PrssKeys C) :=
  if i ∈ D.1 then .done none else if active i then
    .wait (prssRevealOutbox (parts i) i) (exchangeResume fun revealed =>
      prssPostReveal i (parts i) (committed i) revealed)
  else .done none

def prssRevealInbox (D : C.Coalition) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (sent : C.Party → Mail C E) (i j : C.Party) : Option (Msg E) :=
  if j ∈ D.1 then sent j i else if active j then prssRevealOutbox (parts j) j i else some .abort

theorem prssRevealStep_inbox (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (sent : C.Party → Mail C E)
    (i : C.Party) :
    (fun j => if j ∈ D.1 then sent j i else (prssRevealStep D active parts committed j).delivered i) =
      prssRevealInbox D active parts sent i := by
  funext j
  by_cases hj : j ∈ D.1 <;> by_cases ha : active j <;>
    simp [prssRevealStep, prssRevealInbox, Step.delivered, hj, ha]

/-- One successful receiver implies that every honest sender supplied its actual reveal. -/
theorem prssRevealInbox_honest (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (sent : C.Party → Mail C E) (i : C.Party)
    (ha : (C.parties.any fun j => Msg.isAbort (prssRevealInbox D active parts sent i j)) = false)
    (j : C.Party) (hj : j ∉ D.1) (hji : j ≠ i) :
    Msg.hashesOf (prssRevealInbox D active parts sent i j) = revealTo .prss (parts j) j i := by
  have hn : Msg.isAbort (prssRevealInbox D active parts sent i j) = false :=
    Bool.eq_false_iff.mpr (List.any_eq_false.mp ha j (List.mem_finRange j))
  by_cases hac : active j
  · simp [prssRevealInbox, hj, hac, prssRevealOutbox, hji.symm, Msg.hashesOf]
  · simp [prssRevealInbox, hj, hac, Msg.isAbort] at hn

def prssRevealVisible (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (c i : C.Party) : Option (Msg E) :=
  if c ∈ D.1 ∧ i ∉ D.1 then if active i then prssRevealOutbox (parts i) i c else none else none

def prssRevealRows (D : C.Coalition) (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) :
    OracleComp (LocalSpec C) (C.Party → Option (PrssKeys C × List HashOutput)) :=
  Concrete.sequenceFin fun i => if i ∈ D.1 then pure none else if active i then
    prssRevealData i (parts i) (committed i) (prssRevealInbox D active parts sent i)
    else pure none

theorem prssRevealStep_callInput (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (i : C.Party) :
    (prssRevealStep D active parts committed i).callInput = none := by
  unfold prssRevealStep
  split_ifs <;> rfl

theorem prssRevealStep_outbox (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (prssRevealStep D active parts committed i).outbox c else none) =
      prssRevealVisible D active parts := by
  funext c i
  unfold prssRevealStep prssRevealVisible
  split_ifs <;> simp_all [Step.outbox]

/-- The reveal round of the actual waiting programs: adversarial messages first, then each
honest opening check, derivation and echo-hash computation in party order. -/
theorem stepRound_prssReveal (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (active : C.Party → Prop) (parts : C.Party → Parts C) (committed : C.Party → Mail C E)
    (state : A.State) :
    stepRound worldRoles D A noFunctionality state (prssRevealStep D active parts committed) =
      (do
        let (state', sent) ← worldRoles.adversary (A.round state (prssRevealVisible D active parts))
        let rows ← free (prssRevealRows D active parts committed sent)
        pure (state', (fun i => prssFinishStep i (rows i)), sent)) := by
  simp only [stepRound, prssRevealStep_callInput, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, ↓reduceIte, prssRevealStep_outbox]
  apply bind_congr
  rintro ⟨state', sent⟩
  have hseq : (Concrete.sequenceFin fun j => match prssRevealStep D active parts committed j with
      | .done value => pure (Step.done value)
      | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
          worldRoles.honest (advance (resume fun k => if k ∈ D.1 then sent k j else
            (prssRevealStep D active parts committed k).delivered j))
      | .call _ _ => pure (Step.done none)) =
      free (prssRevealRows D active parts committed sent) >>= fun rows =>
        pure (fun i => prssFinishStep i (rows i)) := by
    rw [prssRevealRows, free_sequenceFin]
    rw [← sequenceFin_bind_pure]
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp [prssRevealStep, hi, prssFinishStep]
    · by_cases ha : active i
      · have hstep : prssRevealStep (E := E) D active parts committed i =
            .wait (prssRevealOutbox (parts i) i) (exchangeResume fun revealed =>
              prssPostReveal i (parts i) (committed i) revealed) := by
            simp [prssRevealStep, hi, ha]
        simp only [hstep, if_neg hi, if_pos ha]
        rw [prssRevealStep_inbox, advance_prssRevealResume]
        simp only [worldRoles, map_eq_bind_pure_comp, free_bind, free_pure, Function.comp_def]
      · simp [prssRevealStep, hi, ha, prssFinishStep]
  have heq := congrArg (fun (os : OracleComp (WorldSpec C) (C.Party → Step C E RealSpec (PrssKeys C))) =>
    os >>= fun steps => pure (state', steps, sent)) hseq
  simp only [bind_assoc, pure_bind] at heq
  convert heq using 1
  congr 2
  funext j
  cases prssRevealStep (E := E) D active parts committed j <;> rfl

/-- A joint reveal-round run establishes the cache invariant for precisely its successful rows. -/
theorem prssRevealRows_cached (prims : Primitives) (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) (s : HashCache C)
    (r : (C.Party → Option (PrssKeys C × List HashOutput)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssRevealRows D active parts committed sent)).run s)) :
    s ≤ r.2 ∧ ∀ i row, r.1 i = some row → i ∉ D.1 ∧ active i ∧
      (C.parties.any fun j => Msg.isAbort (prssRevealInbox D active parts sent i j)) = false ∧
      PrssDerivedEchoCached i (prssView parts (prssRevealInbox D active parts sent) i) row r.2 := by
  rw [prssRevealRows, simulateQ_sequenceFin] at hr
  apply sequenceFin_state_post
    (P := fun i result cache => ∀ row, result = some row → i ∉ D.1 ∧ active i ∧
      (C.parties.any fun j => Msg.isAbort (prssRevealInbox D active parts sent i j)) = false ∧
      PrssDerivedEchoCached i (prssView parts (prssRevealInbox D active parts sent) i) row cache)
    _ _ _ _ _ hr
  · intro i cache result hresult
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨le_rfl, fun _ he => by cases he⟩
    · by_cases ha : active i
      · simp only [if_neg hi, if_pos ha] at hresult
        have hh := prssRevealData_cached prims i (parts i) (committed i) _ cache result hresult
        exact ⟨hh.1, fun row he => ⟨hi, ha, hh.2 row he⟩⟩
      · simp only [if_neg hi, if_neg ha, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hresult
        subst result
        exact ⟨le_rfl, fun _ he => by cases he⟩
  · intro i result cache cache' hle hh row he
    have h := hh row he
    exact ⟨h.1, h.2.1, h.2.2.1, prssDerivedEchoCached_mono i _ row hle h.2.2.2⟩

/-- At a successful reveal-round row, a hidden term's derivation input is fixed by honest parts. -/
theorem prssReveal_term_input (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (sent : C.Party → Mail C E) (i : C.Party)
    (ha : (C.parties.any fun j => Msg.isAbort (prssRevealInbox D active parts sent i j)) = false)
    (T : C.Term) (hT : Hidden D (.term T)) (hi : i ∈ C.holders T) :
    prssTermQuery (prssView parts (prssRevealInbox D active parts sent) i) T =
      Query.derive .prss .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (parts j).term T) := by
  unfold prssTermQuery
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjT : j ∈ C.holders T := of_decide_eq_true (List.mem_filter.mp hj).2
  by_cases hji : j = i
  · subst j
    simp [prssView]
  · simp only [prssView, if_neg hji]
    rw [prssRevealInbox_honest D active parts sent i ha j (hidden_term_holders D hT j hjT) hji]
    exact prss_readReveal_term (parts j) i j T hi hjT

/-- Hidden-term agreement follows for the outputs of the actual reveal-round local run. -/
theorem prssRevealRows_hiddenTerm (prims : Primitives) (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) (s : HashCache C)
    (r : (C.Party → Option (PrssKeys C × List HashOutput)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssRevealRows D active parts committed sent)).run s))
    (i j : C.Party) (a b : PrssKeys C × List HashOutput)
    (hi : r.1 i = some a) (hj : r.1 j = some b)
    (T : C.Term) (hT : Hidden D (.term T)) (hiT : i ∈ C.holders T) (hjT : j ∈ C.holders T) :
    a.1.term T = b.1.term T := by
  have hh := (prssRevealRows_cached prims D active parts committed sent s r hr).2
  have ha := hh i a hi
  have hb := hh j b hj
  have hca := ha.2.2.2.1.1 T hiT
  have hcb := hb.2.2.2.1.1 T hjT
  rw [prssReveal_term_input D active parts sent i ha.2.2.1 T hT hiT] at hca
  rw [prssReveal_term_input D active parts sent j hb.2.2.1 T hT hjT] at hcb
  exact Option.some.inj (hca.symm.trans hcb)

theorem prssReveal_pair_input (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (sent : C.Party → Mail C E) (i : C.Party)
    (ha : (C.parties.any fun j => Msg.isAbort (prssRevealInbox D active parts sent i j)) = false)
    (p : C.Pair) (hp : Hidden D (.pair p)) (hi : i = p.1.1 ∨ i = p.1.2) :
    Query.derive (C := C) .prss .pair
      [(prssView parts (prssRevealInbox D active parts sent) i p.1.1).pair p.1.2,
       (prssView parts (prssRevealInbox D active parts sent) i p.1.2).pair p.1.1] =
    Query.derive .prss .pair [(parts p.1.1).pair p.1.2, (parts p.1.2).pair p.1.1] := by
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  have hp' : p.1.1 ∉ D.1 ∧ p.1.2 ∉ D.1 := hp
  rcases hi with rfl | rfl
  · simp only [prssView, ite_true, if_neg hne.symm]
    rw [prssRevealInbox_honest D active parts sent _ ha _ hp'.2 hne.symm, prss_readReveal_pair]
  · simp only [prssView, ite_true, if_neg hne]
    rw [prssRevealInbox_honest D active parts sent _ ha _ hp'.1 hne, prss_readReveal_pair]

theorem prssRevealRows_hiddenPair (prims : Primitives) (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) (s : HashCache C)
    (r : (C.Party → Option (PrssKeys C × List HashOutput)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssRevealRows D active parts committed sent)).run s))
    (p : C.Pair) (hp : Hidden D (.pair p)) (a b : PrssKeys C × List HashOutput)
    (ha : r.1 p.1.1 = some a) (hb : r.1 p.1.2 = some b) :
    a.1.pair p.1.2 = b.1.pair p.1.1 := by
  have hh := (prssRevealRows_cached prims D active parts committed sent s r hr).2
  have hne : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  have hpa : C.pairOf p.1.1 p.1.2 hne = p := by simp [Committee.pairOf, p.2]
  have hpb : C.pairOf p.1.2 p.1.1 hne.symm = p := by
    simp [Committee.pairOf, not_lt.mpr (le_of_lt p.2)]
  have hci := (hh _ a ha).2.2.2.1.2 _ hne.symm
  have hcj := (hh _ b hb).2.2.2.1.2 _ hne
  have hqi : prssPairQuery p.1.1 (prssView parts (prssRevealInbox D active parts sent) p.1.1) p.1.2 =
      Query.derive .prss .pair [(parts p.1.1).pair p.1.2, (parts p.1.2).pair p.1.1] := by
    simp only [prssPairQuery, dif_neg hne.symm, hpa]
    exact prssReveal_pair_input D active parts sent _ (hh _ a ha).2.2.1 p hp (Or.inl rfl)
  have hqj : prssPairQuery p.1.2 (prssView parts (prssRevealInbox D active parts sent) p.1.2) p.1.1 =
      Query.derive .prss .pair [(parts p.1.1).pair p.1.2, (parts p.1.2).pair p.1.1] := by
    simp only [prssPairQuery, dif_neg hne, hpb]
    exact prssReveal_pair_input D active parts sent _ (hh _ b hb).2.2.1 p hp (Or.inr rfl)
  rw [hqi] at hci
  rw [hqj] at hcj
  exact Option.some.inj (hci.symm.trans hcj)

def prssRowsKeys (rows : C.Party → Option (PrssKeys C × List HashOutput)) (i : C.Party) : PrssKeys C :=
  ((rows i).map Prod.fst).getD ⟨fun _ => 0, fun _ => 0⟩

/-- The actual successful reveal rows supply the key table and active set of the echo coupling. -/
theorem prssRevealRows_echoStep (prims : Primitives) (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) (s : HashCache C)
    (r : (C.Party → Option (PrssKeys C × List HashOutput)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssRevealRows D active parts committed sent)).run s)) :
    (fun i => prssFinishStep (E := E) i (r.1 i)) =
      prssEchoStep D (fun i => (r.1 i).isSome)
        (fun q => (r.2 q).getD 0) (prssRowsKeys r.1) := by
  funext i
  cases hi : r.1 i with
  | none => simp [prssFinishStep, prssEchoStep, hi]
  | some row =>
    have hh := (prssRevealRows_cached prims D active parts committed sent s r hr).2 i row hi
    have hout : prssRowsKeys r.1 i = row.1 := by simp [prssRowsKeys, hi]
    have hs : ∀ j, row.2.getD j.val 0 = prssEcho (fun q => (r.2 q).getD 0)
        (fun k => (prssRowsKeys r.1 k).term) i j := by
      intro j
      unfold prssEcho
      let cache : Query C → Option HashOutput := r.2
      have hq := congrArg (fun out : PrssKeys C =>
        Query.sharedKeys (C := C) .prss ((sharedTerms i j).map out.term)) hout
      exact (congrArg (fun v : Option HashOutput => v.getD 0)
        ((congrArg cache hq).trans (hh.2.2.2.2 j))).symm
    have he := advance_prssEchoFinish (E := E) (fun q => (r.2 q).getD 0)
      (prssRowsKeys r.1) i row.2 hs
    rw [hout, advance_prssEchoFinish_row] at he
    simp only [prssEchoStep, if_neg hh.1, hi, Option.isSome_some, ↓reduceIte]
    rw [hout]
    exact (OracleComp.pure_inj _ _).mp he

def prssCommitStep (i : C.Party) (own : Parts C) (commitments : List HashOutput) :
    Step C E RealSpec (PrssKeys C) :=
  .wait (commitOutbox i commitments) (exchangeResume fun committed => do
    let revealed ← exchange (prssRevealOutbox own i)
    prssPostReveal i own committed revealed)

/-- The actual setup samples its parts and computes its commitments before its first wait. -/
theorem advance_prssSetup_run (i : C.Party) :
    advance (prssSetup i : PartyM C E RealSpec (PrssKeys C)).run = (do
      let own ← liftComp (sampleParts : ProbComp (Parts C)) (LocalSpec C)
      let commitments ← liftComp (C.parties.mapM fun j =>
        hashQuery (.commit .prss i j (revealTo .prss own i j))) (LocalSpec C)
      pure (prssCommitStep i own commitments)) := by
  rw [prssSetup_eq_reveal_prefix, advance_localStep_bind]
  apply bind_congr
  intro own
  rw [advance_oracleStep_bind]
  apply bind_congr
  intro commitments
  exact advance_exchange_bind _ _

def prssInitialData (D : C.Coalition) :
    OracleComp (LocalSpec C) (C.Party → Parts C × List HashOutput) :=
  Concrete.sequenceFin fun i => if i ∈ D.1 then pure (⟨0, fun _ => 0, fun _ => 0⟩, []) else do
    let own ← liftComp (sampleParts : ProbComp (Parts C)) (LocalSpec C)
    let commitments ← liftComp (C.parties.mapM fun j =>
      hashQuery (.commit .prss i j (revealTo .prss own i j))) (LocalSpec C)
    pure (own, commitments)

def prssInitialSteps (D : C.Coalition) (data : C.Party → Parts C × List HashOutput) :
    C.Party → Step C E RealSpec (PrssKeys C) :=
  fun i => if i ∈ D.1 then .done none else prssCommitStep i (data i).1 (data i).2

theorem startSteps_prssSetup (D : C.Coalition) :
    startSteps worldRoles D (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))) =
      prssInitialSteps D <$> free (prssInitialData D) := by
  unfold startSteps prssInitialData
  rw [free_sequenceFin, map_eq_bind_pure_comp]
  change _ = Concrete.sequenceFin _ >>= fun rows => pure (prssInitialSteps D rows)
  unfold prssInitialSteps
  rw [← sequenceFin_bind_pure _ (fun i (row : Parts C × List HashOutput) =>
    if i ∈ D.1 then Step.done (E := E) (G := RealSpec) (α := PrssKeys C) none
    else prssCommitStep i row.1 row.2)]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi]
  · simp only [if_neg hi, worldRoles, advance_prssSetup_run, free_bind, free_pure,
      bind_assoc, pure_bind]

def prssCommitInbox (D : C.Coalition) (data : C.Party → Parts C × List HashOutput)
    (sent : C.Party → Mail C E) (i j : C.Party) : Option (Msg E) :=
  if j ∈ D.1 then sent j i else commitOutbox j (data j).2 i

def prssCommitVisible (D : C.Coalition) (data : C.Party → Parts C × List HashOutput)
    (c i : C.Party) : Option (Msg E) :=
  if c ∈ D.1 ∧ i ∉ D.1 then commitOutbox i (data i).2 c else none

theorem prssInitialSteps_callInput (D : C.Coalition) (data : C.Party → Parts C × List HashOutput)
    (i : C.Party) : (prssInitialSteps (E := E) D data i).callInput = none := by
  unfold prssInitialSteps
  split_ifs <;> rfl

theorem prssInitialSteps_outbox (D : C.Coalition) (data : C.Party → Parts C × List HashOutput) :
    (fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (prssInitialSteps (E := E) D data i).outbox c else none) =
      prssCommitVisible D data := by
  funext c i
  unfold prssInitialSteps prssCommitVisible
  split_ifs <;> simp_all [prssCommitStep, Step.outbox]

theorem prssInitialSteps_inbox (D : C.Coalition) (data : C.Party → Parts C × List HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) :
    (fun j => if j ∈ D.1 then sent j i else (prssInitialSteps D data j).delivered i) =
      prssCommitInbox D data sent i := by
  funext j
  by_cases hj : j ∈ D.1 <;>
    simp [prssInitialSteps, prssCommitInbox, prssCommitStep, Step.delivered, hj]

/-- The first network round reaches exactly the reveal steps, with activity determined by the
received abort frames. No secret-dependent local computation occurs at this boundary. -/
theorem stepRound_prssCommit (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (data : C.Party → Parts C × List HashOutput) (state : A.State) :
    stepRound worldRoles D A noFunctionality state (prssInitialSteps D data) = (do
      let (state', sent) ← worldRoles.adversary (A.round state (prssCommitVisible D data))
      let committed := prssCommitInbox D data sent
      let active := fun i => (C.parties.any fun j => Msg.isAbort (committed i j)) = false
      pure (state', prssRevealStep D active (fun i => (data i).1) committed, sent)) := by
  simp only [stepRound, prssInitialSteps_callInput, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, ↓reduceIte, prssInitialSteps_outbox]
  apply bind_congr
  rintro ⟨state', sent⟩
  have hseq : (Concrete.sequenceFin fun j => match prssInitialSteps D data j with
      | .done value => pure (Step.done value)
      | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
          worldRoles.honest (advance (resume fun k => if k ∈ D.1 then sent k j else
            (prssInitialSteps D data k).delivered j))
      | .call _ _ => pure (Step.done none)) =
      pure (prssRevealStep D
        (fun i => (C.parties.any fun j => Msg.isAbort (prssCommitInbox D data sent i j)) = false)
        (fun i => (data i).1) (prssCommitInbox D data sent)) := by
    rw [← sequenceFin_pure]
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp [prssInitialSteps, prssRevealStep, hi]
    · have hstep : prssInitialSteps (E := E) D data i = prssCommitStep i (data i).1 (data i).2 := by
        simp [prssInitialSteps, hi]
      simp only [hstep, prssCommitStep, if_neg hi]
      rw [prssInitialSteps_inbox]
      unfold exchangeResume
      split_ifs with ha
      · simp [worldRoles, advance_pure, prssRevealStep, hi, ha]
      · rw [advance_exchange_bind]
        simp only [worldRoles, free_pure, prssRevealStep, if_neg hi, Bool.eq_false_iff.mpr ha, ↓reduceIte]
  have heq := congrArg (fun (os : OracleComp (WorldSpec C) (C.Party → Step C E RealSpec (PrssKeys C))) =>
    os >>= fun steps => pure (state', steps, sent)) hseq
  simp only [pure_bind] at heq
  convert heq using 1
  congr 2
  funext j
  cases prssInitialSteps (E := E) D data j <;> rfl

theorem prss_exists_honest (D : C.Coalition) : ∃ i : C.Party, i ∉ D.1 := by
  by_contra hn
  push Not at hn
  have heq : D.1 = Finset.univ := Finset.ext fun i => by simp [hn i]
  have hc := D.2
  rw [heq, Finset.card_univ, Fintype.card_fin] at hc
  have ht := C.one_le_t
  unfold Committee.n at hc
  omega

theorem prssInitialSteps_not_done (D : C.Coalition) (data : C.Party → Parts C × List HashOutput) :
    ¬ ∀ i, i ∉ D.1 → (prssInitialSteps (E := E) D data i).isDone := by
  intro hall
  obtain ⟨i, hi⟩ := prss_exists_honest D
  simpa [prssInitialSteps, hi, prssCommitStep, Step.isDone] using hall i hi

theorem prssRevealStep_all_done (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    (∀ i, i ∉ D.1 → (prssRevealStep D active parts committed i).isDone) ↔
      ∀ i, i ∉ D.1 → ¬ active i := by
  constructor <;> intro h i hi
  · have hh := h i hi
    by_contra ha
    simpa [prssRevealStep, hi, ha, Step.isDone] using hh
  · simp [prssRevealStep, hi, h i hi, Step.isDone]

theorem prssRevealStep_output (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (i : C.Party) :
    (prssRevealStep D active parts committed i).output = none := by
  unfold prssRevealStep
  split_ifs <;> rfl

/-- An exact expansion of the first two setup rounds. If all honest parties abort after the
commit exchange, the executor stops before calling the adversary for another round. -/
theorem executePhase_prssSetup_prefix (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (fuel : ℕ) :
    executePhase worldRoles D A noFunctionality (fuel + 2) state
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))) = (do
      let data ← free (prssInitialData D)
      let (state', sent) ← worldRoles.adversary (A.round state (prssCommitVisible D data))
      let committed := prssCommitInbox D data sent
      let parts := fun i => (data i).1
      let active := fun i => (C.parties.any fun j => Msg.isAbort (committed i j)) = false
      if ∀ i, i ∉ D.1 → ¬ active i then pure (state', fun _ => none) else do
        let (state'', sent') ← worldRoles.adversary (A.round state' (prssRevealVisible D active parts))
        let rows ← free (prssRevealRows D active parts committed sent')
        executeRounds worldRoles D A noFunctionality fuel state'' (fun i => prssFinishStep i (rows i))) := by
  rw [executePhase, startSteps_prssSetup]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply bind_congr
  intro data
  rw [executeRounds, if_neg (prssInitialSteps_not_done D data), stepRound_prssCommit]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨state', sent⟩
  rw [executeRounds]
  simp only [prssRevealStep_all_done]
  split_ifs
  · simp only [prssRevealStep_output]
  · rw [stepRound_prssReveal]
    simp only [bind_assoc, pure_bind]

/-- The same invariant holds after the actual world executes the adversary's reveal-round queries
and then the honest local computations. The witness uses the final world cache. -/
theorem stepRound_prssReveal_world (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed : C.Party → Mail C E) (state : A.State)
    (s : HashCache C)
    (r : (A.State × (C.Party → Step C E RealSpec (PrssKeys C)) × (C.Party → Mail C E)) × HashCache C)
    (hr : r ∈ support ((simulateQ (worldAnswer prims)
      (stepRound worldRoles D A noFunctionality state (prssRevealStep D active parts committed))).run s)) :
    ∃ rows : C.Party → Option (PrssKeys C × List HashOutput),
      r.1.2.1 = prssEchoStep D (fun i => (rows i).isSome)
        (fun q => (r.2 q).getD 0) (prssRowsKeys rows) ∧
      (∀ i row, rows i = some row → i ∉ D.1 ∧ active i ∧
        (C.parties.any fun j => Msg.isAbort (prssRevealInbox D active parts r.1.2.2 i j)) = false ∧
        PrssDerivedEchoCached i (prssView parts (prssRevealInbox D active parts r.1.2.2) i) row r.2) ∧
      (∀ i j a b, rows i = some a → rows j = some b → ∀ T, Hidden D (.term T) →
        i ∈ C.holders T → j ∈ C.holders T → a.1.term T = b.1.term T) ∧
      (∀ p : C.Pair, Hidden D (.pair p) → ∀ a b,
        rows p.1.1 = some a → rows p.1.2 = some b → a.1.pair p.1.2 = b.1.pair p.1.1) := by
  rw [stepRound_prssReveal] at hr
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hr
  obtain ⟨adv, hadv, rows, hrows, rfl⟩ := hr
  rw [worldAnswer, simulateQ_free] at hrows
  refine ⟨rows.1, prssRevealRows_echoStep prims D active parts committed adv.1.2 adv.2 rows hrows,
    (prssRevealRows_cached prims D active parts committed adv.1.2 adv.2 rows hrows).2, ?_, ?_⟩
  · intro i j a b hi hj T hT hiT hjT
    exact prssRevealRows_hiddenTerm prims D active parts committed adv.1.2 adv.2 rows hrows
      i j a b hi hj T hT hiT hjT
  · intro p hp a b ha hb
    exact prssRevealRows_hiddenPair prims D active parts committed adv.1.2 adv.2 rows hrows p hp a b ha hb

end ThresholdLeanXmssSecurity

end PrssReachablePrefix

section PrssOpeningConnection
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E : Type}

variable (prims : Primitives)

/-- Private sampling preserves the cache, including when it is not empty. -/
theorem simulateQ_local_sample {α : Type} (p : ProbComp α) (s : HashCache C) :
    (simulateQ (localAnswer prims) (liftComp p (LocalSpec C))).run s =
      (fun a => (a, s)) <$> p := by
  have he := congrArg (fun oa => (fun r => (r.1.1, r.2)) <$> oa)
    (world_free_liftComp prims p s)
  rw [simulateQ_world_free] at he
  simp only [Functor.map_map, Function.comp_def, Prod.eta] at he
  change id <$> (simulateQ (localAnswer prims) (liftComp p (LocalSpec C))).run s = _ at he
  simpa only [id_map] using he

theorem randomOracle_finRange_cached {Dom R : Type} [DecidableEq Dom] [SampleableType R]
    (n : ℕ) (q : Fin n → Dom) (s : (Dom →ₒ R).QueryCache) (r : List R × (Dom →ₒ R).QueryCache)
    (hr : r ∈ support (((List.finRange n).mapM fun i => (Dom →ₒ R).randomOracle (q i)).run s))
    (default : R) : s ≤ r.2 ∧ ∀ i, r.2 (q i) = some (r.1.getD i.val default) := by
  have hh := randomOracle_mapM_cached q (List.finRange n) s r hr
  refine ⟨hh.1, ?_⟩
  intro i
  have hi := forall₂_getD_idxOf _ _ _ hh.2 i (List.mem_finRange i) default
  simpa using hi

/-- The sampled initial parts and every commitment answer are retained in the final initial cache. -/
theorem prssInitialData_cached (D : C.Coalition) (s : HashCache C)
    (r : (C.Party → Parts C × List HashOutput) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) (prssInitialData D)).run s)) :
    s ≤ r.2 ∧ ∀ i, i ∉ D.1 → ∀ j,
      r.2 (.commit .prss i j (revealTo .prss (r.1 i).1 i j)) = some ((r.1 i).2.getD j.val 0) := by
  rw [prssInitialData, simulateQ_sequenceFin] at hr
  apply sequenceFin_state_post
    (P := fun i (data : Parts C × List HashOutput) cache => i ∉ D.1 → ∀ j,
      cache (.commit .prss i j (revealTo .prss data.1 i j)) = some (data.2.getD j.val 0))
    _ _ _ _ _ hr
  · intro i cache result hresult
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨le_rfl, fun h => (h hi).elim⟩
    · simp only [if_neg hi, simulateQ_bind, simulateQ_pure, StateT.run_bind,
        StateT.run_pure, simulateQ_local_sample, support_bind, support_map,
        support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hresult
      obtain ⟨v, ⟨own, hown, rfl⟩, commits, hcommits, rfl⟩ := hresult
      have he : simulateQ (localAnswer prims) (liftComp (C.parties.mapM fun j =>
          hashQuery (.commit .prss i j (revealTo .prss own i j))) (LocalSpec C)) =
          C.parties.mapM fun j => hashAnswer prims (.commit .prss i j (revealTo .prss own i j)) := by
        rw [localAnswer, QueryImpl.simulateQ_add_liftComp_right, simulateQ_list_mapM]
        congr 1
        funext j
        exact simulateQ_spec_query _ _
      rw [he] at hcommits
      have hh := randomOracle_finRange_cached C.n
        (fun j : C.Party => Query.commit .prss i j (revealTo .prss own i j)) cache commits hcommits 0
      exact ⟨hh.1, fun _ => hh.2⟩
  · intro i data cache cache' hle hh hi j
    exact hle (hh hi j)

variable {prims}

theorem revealTo_prss_length (a b : Parts C) (i j : C.Party) :
    (revealTo .prss a i j).length = (revealTo .prss b i j).length := by
  simp [revealTo]

/-- For honest senders the opening checks are identities. Only corrupt senders can cause a
commit-opening failure, once the authenticated honest messages and cached answers are accounted for. -/
theorem prssOpenCheck_iff_corrupt (D : C.Coalition) (i : C.Party) (own : Parts C)
    (committed revealed : Mail C E) (opens : List HashOutput)
    (hh : ∀ j, j ∉ D.1 → j ≠ i →
      (Msg.hashesOf (revealed j)).length = (revealTo .prss own j i).length ∧
      [opens.getD j.val 0] = Msg.hashesOf (committed j)) :
    prssOpenCheck i own committed revealed opens ↔
      ∀ j, j ∈ D.1 → j ≠ i →
        (Msg.hashesOf (revealed j)).length = (revealTo .prss own j i).length ∧
        [opens.getD j.val 0] = Msg.hashesOf (committed j) := by
  constructor
  · intro h j _ hji
    exact h j hji
  · intro h j hji
    by_cases hj : j ∈ D.1
    · exact h j hj hji
    · exact hh j hj hji

/-- A successful local reveal transition retains both the passed opening test and its hash answers. -/
theorem prssPostRevealData_opened (prims : Primitives) (i : C.Party) (own : Parts C)
    (committed revealed : Mail C E) (s : HashCache C)
    (r : Option (PrssKeys C × List HashOutput) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssPostRevealData i own committed revealed)).run s))
    (row : PrssKeys C × List HashOutput) (hout : r.1 = some row) :
    ∃ opens, prssOpenCheck i own committed revealed opens ∧ ∀ j,
      r.2 (.commit .prss j i (Msg.hashesOf (revealed j))) = some (opens.getD j.val 0) := by
  rw [simulateQ_prssPostRevealData] at hr
  simp only [StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hr
  obtain ⟨opens, hopens, hr⟩ := hr
  have ho := randomOracle_finRange_cached C.n (fun j : C.Party =>
    Query.commit .prss j i (Msg.hashesOf (revealed j))) s opens hopens 0
  by_cases hc : prssOpenCheck i own committed revealed opens.1
  · simp only [if_pos hc, StateT.run_map, support_map] at hr
    obtain ⟨out, hout', rfl⟩ := hr
    have hd := (prssDeriveEcho_cached prims i _ opens.2 out hout').1
    exact ⟨opens.1, hc, fun j => hd (ho.2 j)⟩
  · simp only [if_neg hc, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    cases hout

/-- The corrupt-sender predicate uses its chosen messages, public lengths and the opening hash answers. -/
def prssCorruptOpenCheck (D : C.Coalition) (i : C.Party)
    (sentCommit sentReveal : C.Party → Mail C E) (opens : List HashOutput) : Prop :=
  ∀ j, j ∈ D.1 → j ≠ i →
    (Msg.hashesOf (sentReveal j i)).length = (sharedTerms j i).length + 1 ∧
    [opens.getD j.val 0] = Msg.hashesOf (sentCommit j i)

/-- Once the initial commitments and the opening queries are in one cache, every honest
sender's check is an identity. The resulting predicate has no explicit part-table argument;
this does not assert that its messages or hash answers are statistically independent of that table. -/
theorem prssOpenCheck_from_cache (D : C.Coalition) (i : C.Party)
    (data : C.Party → Parts C × List HashOutput) (active : C.Party → Prop)
    (sentCommit sentReveal : C.Party → Mail C E) (opens : List HashOutput) (cache : HashCache C)
    (ha : (C.parties.any fun j => Msg.isAbort
      (prssRevealInbox D active (fun k => (data k).1) sentReveal i j)) = false)
    (hc : ∀ j, j ∉ D.1 → cache (.commit .prss j i (revealTo .prss (data j).1 j i)) =
      some ((data j).2.getD i.val 0))
    (ho : ∀ j, cache (.commit .prss j i (Msg.hashesOf
      (prssRevealInbox D active (fun k => (data k).1) sentReveal i j))) = some (opens.getD j.val 0)) :
    prssOpenCheck i (data i).1 (prssCommitInbox D data sentCommit i)
      (prssRevealInbox D active (fun k => (data k).1) sentReveal i) opens ↔
      prssCorruptOpenCheck D i sentCommit sentReveal opens := by
  have hhonest : ∀ j, j ∉ D.1 → j ≠ i →
      (Msg.hashesOf (prssRevealInbox D active (fun k => (data k).1) sentReveal i j)).length =
        (revealTo .prss (data i).1 j i).length ∧
      [opens.getD j.val 0] = Msg.hashesOf (prssCommitInbox D data sentCommit i j) := by
    intro j hj hji
    have hv := prssRevealInbox_honest D active (fun k => (data k).1) sentReveal i ha j hj hji
    refine ⟨?_, ?_⟩
    · rw [hv]
      exact revealTo_prss_length _ _ j i
    · let cf : Query C → Option HashOutput := cache
      have hq := congrArg (Query.commit (C := C) .prss j i) hv
      have he := (ho j).symm.trans ((congrArg cf hq).trans (hc j hj))
      have hv' := Option.some.inj he
      simp only [prssCommitInbox, if_neg hj, commitOutbox, if_neg hji.symm, Msg.hashesOf, hv']
  rw [prssOpenCheck_iff_corrupt D i _ _ _ _ hhonest]
  unfold prssCorruptOpenCheck
  apply forall_congr'
  intro j
  by_cases hj : j ∈ D.1
  · simp only [hj, true_implies, prssRevealInbox, if_pos hj, prssCommitInbox]
    simp [revealTo]
  · simp [hj]

/-- Equality of the corrupt opening answers suffices for the two checks to make the same decision. -/
theorem prssCorruptOpenCheck_congr (D : C.Coalition) (i : C.Party)
    (sentCommit sentReveal : C.Party → Mail C E) (opens opens' : List HashOutput)
    (h : ∀ j, j ∈ D.1 → opens.getD j.val 0 = opens'.getD j.val 0) :
    prssCorruptOpenCheck D i sentCommit sentReveal opens ↔
      prssCorruptOpenCheck D i sentCommit sentReveal opens' := by
  unfold prssCorruptOpenCheck
  constructor <;> intro hc j hj hji
  · simpa only [h j hj] using hc j hj hji
  · simpa only [← h j hj] using hc j hj hji

/-- Initial commitments survive every subsequent world computation, including adversarial queries.
The witness keeps the actually sampled parts, rather than an independently chosen table. -/
theorem prssInitialData_persistent (prims : Primitives) (D : C.Coalition) {α : Type}
    (k : (C.Party → Parts C × List HashOutput) → OracleComp (WorldSpec C) α)
    (s : HashCache C) (r : ((C.Party → Parts C × List HashOutput) × α) × HashCache C)
    (hr : r ∈ support ((simulateQ (worldAnswer prims) (do
      let data ← free (prssInitialData D)
      let out ← k data
      pure (data, out))).run s)) :
    s ≤ r.2 ∧ ∀ i, i ∉ D.1 → ∀ j,
      r.2 (.commit .prss i j (revealTo .prss (r.1.1 i).1 i j)) =
        some ((r.1.1 i).2.getD j.val 0) := by
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hr
  obtain ⟨initial, hinitial, out, hout, rfl⟩ := hr
  rw [worldAnswer, simulateQ_free] at hinitial
  have hi := prssInitialData_cached prims D s initial hinitial
  have hg := (grows_worldAnswer prims).simulateQ (k initial.1) initial.2 out hout
  exact ⟨hi.1.trans hg, fun i hh j => hg (hi.2 i hh j)⟩

/-- The joint reveal rows retain the passed tests and their opening answers after all later
parties have run. -/
theorem prssRevealRows_opened (prims : Primitives) (D : C.Coalition) (active : C.Party → Prop)
    (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) (s : HashCache C)
    (r : (C.Party → Option (PrssKeys C × List HashOutput)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssRevealRows D active parts committed sent)).run s)) :
    s ≤ r.2 ∧ ∀ i row, r.1 i = some row → ∃ opens,
      prssOpenCheck i (parts i) (committed i) (prssRevealInbox D active parts sent i) opens ∧
      ∀ j, r.2 (.commit .prss j i (Msg.hashesOf (prssRevealInbox D active parts sent i j))) =
        some (opens.getD j.val 0) := by
  rw [prssRevealRows, simulateQ_sequenceFin] at hr
  apply sequenceFin_state_post
    (P := fun i result cache => ∀ row, result = some row → ∃ opens,
      prssOpenCheck i (parts i) (committed i) (prssRevealInbox D active parts sent i) opens ∧
      ∀ j, cache (.commit .prss j i (Msg.hashesOf (prssRevealInbox D active parts sent i j))) =
        some (opens.getD j.val 0)) _ _ _ _ _ hr
  · intro i cache result hresult
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact ⟨le_rfl, fun _ he => by cases he⟩
    · by_cases ha : active i
      · simp only [if_neg hi, if_pos ha] at hresult
        have hg := (grows_localAnswer prims).simulateQ
          (prssRevealData i (parts i) (committed i) (prssRevealInbox D active parts sent i)) cache result hresult
        refine ⟨hg, ?_⟩
        intro row he
        unfold prssRevealData at hresult
        split_ifs at hresult with hab
        · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hresult
          subst result
          cases he
        · exact prssPostRevealData_opened prims i (parts i) (committed i) _ cache result hresult row he
      · simp only [if_neg hi, if_neg ha, simulateQ_pure, StateT.run_pure, support_pure,
          Set.mem_singleton_iff] at hresult
        subst result
        exact ⟨le_rfl, fun _ he => by cases he⟩
  · intro i result cache cache' hle hh row he
    obtain ⟨opens, hc, ho⟩ := hh row he
    exact ⟨opens, hc, fun j => hle (ho j)⟩

/-- For actual successful reveal rows, the retained initial commitments discharge the honest
checks, establishing the corrupt-message predicate and retaining the opening answers in the final cache. -/
theorem prssRevealRows_corruptOpenCheck (prims : Primitives) (D : C.Coalition)
    (data : C.Party → Parts C × List HashOutput) (active : C.Party → Prop)
    (sentCommit sentReveal : C.Party → Mail C E) (s : HashCache C)
    (hc : ∀ j, j ∉ D.1 → ∀ i, s (.commit .prss j i (revealTo .prss (data j).1 j i)) =
      some ((data j).2.getD i.val 0))
    (r : (C.Party → Option (PrssKeys C × List HashOutput)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssRevealRows D active (fun i => (data i).1) (prssCommitInbox D data sentCommit) sentReveal)).run s)) :
    ∀ i row, r.1 i = some row → ∃ opens,
      prssCorruptOpenCheck D i sentCommit sentReveal opens ∧
      ∀ j, r.2 (.commit .prss j i (Msg.hashesOf
        (prssRevealInbox D active (fun k => (data k).1) sentReveal i j))) = some (opens.getD j.val 0) := by
  intro i row he
  have hh := prssRevealRows_cached prims D active (fun i => (data i).1)
    (prssCommitInbox D data sentCommit) sentReveal s r hr
  obtain ⟨opens, hopen, ho⟩ := (prssRevealRows_opened prims D active (fun i => (data i).1)
    (prssCommitInbox D data sentCommit) sentReveal s r hr).2 i row he
  refine ⟨opens, ?_, ho⟩
  exact (prssOpenCheck_from_cache D i data active sentCommit sentReveal opens r.2
    (hh.2 i row he).2.2.1 (fun j hj => hh.1 (hc j hj i)) ho).mp hopen

end ThresholdLeanXmssSecurity

end PrssOpeningConnection

section PrssContributionEntropy
open OracleComp.DeferredSampling
open scoped ENNReal
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee}

/-- Resampling one term contribution preserves the full distribution of sampled parts. -/
theorem evalDist_sampleParts_resample_term {α : Type} (T : C.Term) (k : Parts C → ProbComp α) :
    𝒟[($ᵗ HashOutput) >>= fun u => (sampleParts : ProbComp (Parts C)) >>= fun parts =>
      k {parts with term := Function.update parts.term T u}] =
    𝒟[(sampleParts : ProbComp (Parts C)) >>= k] := by
  simp only [sampleParts, bind_assoc, pure_bind]
  rw [evalDist_bind_comm]
  apply evalDist_bind_congr_left
  intro parameter
  exact evalDist_update_bind T (fun term => ($ᵗ (C.Party → HashOutput)) >>= fun pair =>
    k ⟨parameter, term, pair⟩)

/-- Resampling one addressed pair contribution also preserves the full sampled-parts distribution. -/
theorem evalDist_sampleParts_resample_pair {α : Type} (j : C.Party) (k : Parts C → ProbComp α) :
    𝒟[($ᵗ HashOutput) >>= fun u => (sampleParts : ProbComp (Parts C)) >>= fun parts =>
      k {parts with pair := Function.update parts.pair j u}] =
    𝒟[(sampleParts : ProbComp (Parts C)) >>= k] := by
  simp only [sampleParts, bind_assoc, pure_bind]
  rw [evalDist_bind_comm]
  apply evalDist_bind_congr_left
  intro parameter
  rw [evalDist_bind_comm]
  apply evalDist_bind_congr_left
  intro term
  exact evalDist_update_bind j (fun pair => k ⟨parameter, term, pair⟩)

/-- An observation insensitive to one term coordinate is independent of that coordinate. -/
theorem sampleParts_hiddenTerm_independent {V : Type} (T : C.Term) (view : Parts C → V)
    (hv : ∀ parts u, view {parts with term := Function.update parts.term T u} = view parts) :
    𝒟[(sampleParts : ProbComp (Parts C)) >>= fun parts => pure (view parts, parts.term T)] =
      𝒟[(sampleParts : ProbComp (Parts C)) >>= fun parts =>
        ($ᵗ HashOutput) >>= fun u => pure (view parts, u)] := by
  rw [← evalDist_sampleParts_resample_term T (fun parts => pure (view parts, parts.term T))]
  simp only [hv, Function.update_self]
  exact evalDist_bind_comm _ _ _

/-- The independence statement applies to arbitrary randomized searches from the observation. -/
theorem sampleParts_hiddenTerm_search {V α : Type} (T : C.Term) (view : Parts C → V)
    (hv : ∀ parts u, view {parts with term := Function.update parts.term T u} = view parts)
    (search : V → ProbComp α) (test : HashOutput → α → Bool) :
    𝒟[(sampleParts : ProbComp (Parts C)) >>= fun parts =>
      search (view parts) >>= fun a => pure (test (parts.term T) a)] =
    𝒟[(sampleParts : ProbComp (Parts C)) >>= fun parts =>
      search (view parts) >>= fun a => ($ᵗ HashOutput) >>= fun u => pure (test u a)] := by
  rw [← evalDist_sampleParts_resample_term T (fun parts =>
    search (view parts) >>= fun a => pure (test (parts.term T) a))]
  simp only [hv, Function.update_self]
  rw [evalDist_bind_comm]
  apply evalDist_bind_congr_left
  intro parts
  exact evalDist_bind_comm _ _ _

/-- A search of at most `q` candidates from a coordinate-independent observation guesses one
sampled contribution with probability at most `q / 2^256`. -/
theorem prob_sampleParts_hiddenTerm_guess_le {V : Type} (T : C.Term) (view : Parts C → V)
    (hv : ∀ parts u, view {parts with term := Function.update parts.term T u} = view parts)
    (search : V → ProbComp (Finset HashOutput)) (q : ℕ)
    (hq : ∀ v s, s ∈ support (search v) → s.card ≤ q) :
    Pr[= true | (sampleParts : ProbComp (Parts C)) >>= fun parts =>
      search (view parts) >>= fun s => pure (decide (parts.term T ∈ s))] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  have he := sampleParts_hiddenTerm_search T view hv search (fun u s => decide (u ∈ s))
  have hp : Pr[(fun b : Bool => b = true) | (sampleParts : ProbComp (Parts C)) >>= fun parts =>
      search (view parts) >>= fun s => pure (decide (parts.term T ∈ s))] =
      Pr[(fun b : Bool => b = true) | (sampleParts : ProbComp (Parts C)) >>= fun parts =>
      search (view parts) >>= fun s => ($ᵗ HashOutput) >>= fun u => pure (decide (u ∈ s))] := by
    rw [probEvent_def, probEvent_def, he]
  rw [← probEvent_eq_eq_probOutput, hp]
  apply probEvent_bind_le_of_forall_le
  intro parts _
  apply probEvent_bind_le_of_forall_le
  intro candidates hc
  have hm : (($ᵗ HashOutput) >>= fun u => pure (decide (u ∈ candidates)) : ProbComp Bool) =
      (fun u : HashOutput => decide (u ∈ candidates)) <$> ($ᵗ HashOutput) := by
    rw [map_eq_bind_pure_comp]
    rfl
  rw [hm, probEvent_map]
  simp only [Function.comp_def, decide_eq_true_eq, probEvent_uniformSample]
  have hb := hq (view parts) candidates hc
  norm_num [HashOutput, hashOutputBits]
  gcongr

/-- The independence statement applies to arbitrary randomized searches from the observation. -/
theorem sampleParts_hiddenPair_search {V α : Type} (j : C.Party) (view : Parts C → V)
    (hv : ∀ parts u, view {parts with pair := Function.update parts.pair j u} = view parts)
    (search : V → ProbComp α) (test : HashOutput → α → Bool) :
    𝒟[(sampleParts : ProbComp (Parts C)) >>= fun parts =>
      search (view parts) >>= fun a => pure (test (parts.pair j) a)] =
    𝒟[(sampleParts : ProbComp (Parts C)) >>= fun parts =>
      search (view parts) >>= fun a => ($ᵗ HashOutput) >>= fun u => pure (test u a)] := by
  rw [← evalDist_sampleParts_resample_pair j (fun parts =>
    search (view parts) >>= fun a => pure (test (parts.pair j) a))]
  simp only [hv, Function.update_self]
  rw [evalDist_bind_comm]
  apply evalDist_bind_congr_left
  intro parts
  exact evalDist_bind_comm _ _ _

/-- A search of at most `q` candidates from a coordinate-independent observation guesses one
sampled contribution with probability at most `q / 2^256`. -/
theorem prob_sampleParts_hiddenPair_guess_le {V : Type} (j : C.Party) (view : Parts C → V)
    (hv : ∀ parts u, view {parts with pair := Function.update parts.pair j u} = view parts)
    (search : V → ProbComp (Finset HashOutput)) (q : ℕ)
    (hq : ∀ v s, s ∈ support (search v) → s.card ≤ q) :
    Pr[= true | (sampleParts : ProbComp (Parts C)) >>= fun parts =>
      search (view parts) >>= fun s => pure (decide (parts.pair j ∈ s))] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  have he := sampleParts_hiddenPair_search j view hv search (fun u s => decide (u ∈ s))
  have hp : Pr[(fun b : Bool => b = true) | (sampleParts : ProbComp (Parts C)) >>= fun parts =>
      search (view parts) >>= fun s => pure (decide (parts.pair j ∈ s))] =
      Pr[(fun b : Bool => b = true) | (sampleParts : ProbComp (Parts C)) >>= fun parts =>
      search (view parts) >>= fun s => ($ᵗ HashOutput) >>= fun u => pure (decide (u ∈ s))] := by
    rw [probEvent_def, probEvent_def, he]
  rw [← probEvent_eq_eq_probOutput, hp]
  apply probEvent_bind_le_of_forall_le
  intro parts _
  apply probEvent_bind_le_of_forall_le
  intro candidates hc
  have hm : (($ᵗ HashOutput) >>= fun u => pure (decide (u ∈ candidates)) : ProbComp Bool) =
      (fun u : HashOutput => decide (u ∈ candidates)) <$> ($ᵗ HashOutput) := by
    rw [map_eq_bind_pure_comp]
    rfl
  rw [hm, probEvent_map]
  simp only [Function.comp_def, decide_eq_true_eq, probEvent_uniformSample]
  have hb := hq (view parts) candidates hc
  norm_num [HashOutput, hashOutputBits]
  gcongr

/-- The commitment answer and reveal sent to each corrupt receiver, with a fixed hash function.
This is only the initial public setup data, not the complete adaptive transcript. -/
def prssPublicSetupView (D : C.Coalition) (i : C.Party) (h : Query C → HashOutput)
    (parts : Parts C) : C.Party → HashOutput × List HashOutput := fun j =>
  if j ∈ D.1 then
    let reveal := revealTo .prss parts i j
    (h (.commit .prss i j reveal), reveal)
  else (0, [])

theorem prssPublicSetupView_hiddenTerm (D : C.Coalition) (i : C.Party) (h : Query C → HashOutput)
    (T : C.Term) (hT : Hidden D (.term T)) (parts : Parts C) (u : HashOutput) :
    prssPublicSetupView D i h {parts with term := Function.update parts.term T u} =
      prssPublicSetupView D i h parts := by
  funext j
  unfold prssPublicSetupView
  by_cases hj : j ∈ D.1
  · simp only [if_pos hj, revealTo_prss_hidden_term D parts i j hj T hT u]
  · simp only [if_neg hj]

theorem prssPublicSetupView_hiddenPair (D : C.Coalition) (i : C.Party) (h : Query C → HashOutput)
    (j : C.Party) (hj : j ∉ D.1) (parts : Parts C) (u : HashOutput) :
    prssPublicSetupView D i h {parts with pair := Function.update parts.pair j u} =
      prssPublicSetupView D i h parts := by
  funext k
  unfold prssPublicSetupView
  by_cases hk : k ∈ D.1
  · simp only [if_pos hk, revealTo_prss_hidden_pair D parts i k j hk hj u]
  · simp only [if_neg hk]

/-- Initial public setup data gives no advantage in a bounded search for a hidden term contribution. -/
theorem prob_prssPublicSetupView_hiddenTerm_le (D : C.Coalition) (i : C.Party)
    (h : Query C → HashOutput) (T : C.Term) (hT : Hidden D (.term T))
    (search : (C.Party → HashOutput × List HashOutput) → ProbComp (Finset HashOutput)) (q : ℕ)
    (hq : ∀ v s, s ∈ support (search v) → s.card ≤ q) :
    Pr[= true | (sampleParts : ProbComp (Parts C)) >>= fun parts =>
      search (prssPublicSetupView D i h parts) >>= fun s => pure (decide (parts.term T ∈ s))] ≤
      (q : ℝ≥0∞) / 2 ^ 256 :=
  prob_sampleParts_hiddenTerm_guess_le T (prssPublicSetupView D i h)
    (prssPublicSetupView_hiddenTerm D i h T hT) search q hq

/-- The same bound holds for a pair contribution addressed to an honest receiver. -/
theorem prob_prssPublicSetupView_hiddenPair_le (D : C.Coalition) (i : C.Party)
    (h : Query C → HashOutput) (j : C.Party) (hj : j ∉ D.1)
    (search : (C.Party → HashOutput × List HashOutput) → ProbComp (Finset HashOutput)) (q : ℕ)
    (hq : ∀ v s, s ∈ support (search v) → s.card ≤ q) :
    Pr[= true | (sampleParts : ProbComp (Parts C)) >>= fun parts =>
      search (prssPublicSetupView D i h parts) >>= fun s => pure (decide (parts.pair j ∈ s))] ≤
      (q : ℝ≥0∞) / 2 ^ 256 :=
  prob_sampleParts_hiddenPair_guess_le j (prssPublicSetupView D i h)
    (prssPublicSetupView_hiddenPair D i h j hj) search q hq

end ThresholdLeanXmssSecurity

end PrssContributionEntropy

section PrssContinuationComposition
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E α β : Type}

/-- Attach a continuation to a pending step. The completed case is used only under
`step.output = none`, so an aborted operator stays aborted. -/
def suspendStep (k : α → PartyM C E RealSpec β) : Step C E RealSpec α → Step C E RealSpec β
  | .done _ => .done none
  | .wait out resume => .wait out (fun inbox => (OptionT.mk (resume inbox) >>= k).run)
  | .call input resume => .call input (fun response => (OptionT.mk (resume response) >>= k).run)

theorem continueStep_pending (k : α → PartyM C E RealSpec β) (step : Step C E RealSpec α)
    (hp : step.output = none) : continueStep k step = pure (suspendStep k step) := by
  cases step with
  | done out => cases out <;> simp_all [Step.output, continueStep, suspendStep]
  | wait out resume => rfl
  | call input resume => rfl

theorem suspendStep_outbox (k : α → PartyM C E RealSpec β) (step : Step C E RealSpec α) :
    (suspendStep k step).outbox = step.outbox := by cases step <;> rfl

theorem suspendStep_callInput (k : α → PartyM C E RealSpec β) (step : Step C E RealSpec α) :
    (suspendStep k step).callInput = step.callInput := by cases step <;> rfl

theorem suspendStep_isDone (k : α → PartyM C E RealSpec β) (step : Step C E RealSpec α) :
    (suspendStep k step).isDone ↔ step.isDone := by cases step <;> rfl

theorem suspendStep_delivered (k : α → PartyM C E RealSpec β) (step : Step C E RealSpec α)
    (hp : step.output = none) : (suspendStep k step).delivered = step.delivered := by
  cases step with
  | done out => cases out <;> simp_all [Step.output, Step.delivered, suspendStep]
  | wait out resume => rfl
  | call input resume => rfl

theorem suspendStep_output (k : α → PartyM C E RealSpec β) (step : Step C E RealSpec α) :
    (suspendStep k step).output = none := by cases step <;> rfl

/-- A network round commutes with attaching the next phase while every local transition
still has a pending result. The displayed local equality is the precise boundary condition. -/
theorem stepRound_suspend (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (k : C.Party → α → PartyM C E RealSpec β)
    (hp : ∀ i, (steps i).output = none)
    (hl : ∀ i out resume, steps i = .wait out resume → i ∉ D.1 → ∀ inbox,
      advance (resume inbox) >>= continueStep (k i) =
        (suspendStep (k i)) <$> advance (resume inbox)) :
    stepRound worldRoles D A noFunctionality state (fun i => suspendStep (k i) (steps i)) = (do
      let (state', next, sent) ← stepRound worldRoles D A noFunctionality state steps
      pure (state', (fun i => suspendStep (k i) (next i)), sent)) := by
  have hcall : ∀ i, (steps i).callInput = none := by
    intro i
    cases hs : steps i with
    | done out => rfl
    | wait out resume => rfl
    | call input resume => exact input.elim
  simp only [stepRound, suspendStep_callInput, hcall, Option.isSome_none,
    Bool.false_eq_true, and_false, exists_false, false_and, ↓reduceIte,
    suspendStep_outbox, bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨state', sent⟩
  let next : C.Party → OracleComp (WorldSpec C) (Step C E RealSpec α) := fun j =>
    match steps j with
    | .done out => pure (.done out)
    | .wait _ resume => if j ∈ D.1 then pure (.done none) else
        free (advance (resume fun t => if t ∈ D.1 then sent t j else (steps t).delivered j))
    | .call _ _ => pure (.done none)
  have hm := sequenceFin_bind_pure next (fun i step => suspendStep (k i) step)
  have he := congrArg (fun os : OracleComp (WorldSpec C) (C.Party → Step C E RealSpec β) =>
    os >>= fun ss => pure (state', ss, sent)) hm
  simp only [bind_assoc, pure_bind] at he
  trans (Concrete.sequenceFin next >>= fun ss => pure (state', (fun i => suspendStep (k i) (ss i)), sent))
  · rw [← he]
    apply congrArg (fun os : OracleComp (WorldSpec C) (C.Party → Step C E RealSpec β) =>
      os >>= fun next => pure (state', next, sent))
    congr 1
    funext i
    dsimp only [next]
    cases hs : steps i with
    | done out =>
      have ho := hp i
      simp only [hs, Step.output] at ho
      subst out
      simp [suspendStep]
    | call input resume => exact input.elim
    | wait out resume =>
      rw [suspendStep]
      by_cases hi : i ∈ D.1
      · simp [hi, suspendStep]
      · simp only [if_neg hi, worldRoles]
        have hin : (fun j => if j ∈ D.1 then sent j i else
            (suspendStep (k j) (steps j)).delivered i) =
            (fun j => if j ∈ D.1 then sent j i else (steps j).delivered i) := by
          funext j
          rw [suspendStep_delivered _ _ (hp j)]
        rw [hin, advance_bind]
        change free (advance (resume _) >>= continueStep (k i)) = _
        rw [hl i out resume hs hi]
        simp only [map_eq_bind_pure_comp, free_bind, free_pure, Function.comp_def]

  · congr 2
    funext j
    dsimp only [next]
    cases steps j <;> rfl

/-- The initial local computations commute with a still-pending continuation. -/
theorem startSteps_suspend (D : C.Coalition) (p : C.Party → PartyM C E RealSpec α)
    (k : C.Party → α → PartyM C E RealSpec β)
    (hl : ∀ i, advance (p i).run >>= continueStep (k i) =
      suspendStep (k i) <$> advance (p i).run) :
    startSteps worldRoles D (fun i => p i >>= k i) =
      (fun steps i => suspendStep (k i) (steps i)) <$> startSteps worldRoles D p := by
  unfold startSteps
  rw [map_eq_bind_pure_comp]
  change _ = Concrete.sequenceFin _ >>= fun steps => pure (fun i => suspendStep (k i) (steps i))
  rw [← sequenceFin_bind_pure]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi, suspendStep]
  · simp only [if_neg hi, worldRoles, advance_bind, hl i,
      map_eq_bind_pure_comp, free_bind, free_pure, Function.comp_def]

theorem startSteps_prssSetup_bind (D : C.Coalition)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec β) :
    startSteps worldRoles D (fun i => prssSetup i >>= k i) =
      (fun data i => suspendStep (k i) (prssInitialSteps D data i)) <$> free (prssInitialData D) := by
  rw [startSteps_suspend, startSteps_prssSetup, Functor.map_map]
  intro i
  rw [advance_prssSetup_run]
  simp only [bind_assoc, pure_bind, map_bind, map_pure, prssCommitStep, continueStep, suspendStep]

theorem prssInitialSteps_output (D : C.Coalition) (data : C.Party → Parts C × List HashOutput)
    (i : C.Party) : (prssInitialSteps (E := E) D data i).output = none := by
  unfold prssInitialSteps
  split_ifs <;> rfl

theorem stepRound_prssCommit_bind (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (data : C.Party → Parts C × List HashOutput)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec β) :
    stepRound worldRoles D A noFunctionality state
      (fun i => suspendStep (k i) (prssInitialSteps D data i)) = (do
      let (state', sent) ← worldRoles.adversary (A.round state (prssCommitVisible D data))
      let committed := prssCommitInbox D data sent
      let active := fun i => (C.parties.any fun j => Msg.isAbort (committed i j)) = false
      pure (state', (fun i => suspendStep (k i)
        (prssRevealStep D active (fun i => (data i).1) committed i)), sent)) := by
  rw [stepRound_suspend, stepRound_prssCommit]
  · simp only [bind_assoc, pure_bind]
  · exact prssInitialSteps_output D data
  · intro i out resume hs hi inbox
    simp only [prssInitialSteps, if_neg hi, prssCommitStep, Step.wait.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩
    unfold exchangeResume
    split_ifs
    · rfl
    · rw [advance_exchange_bind]
      rfl

theorem prssFinishStep_output (i : C.Party) (row : Option (PrssKeys C × List HashOutput)) :
    (prssFinishStep (E := E) i row).output = none := by cases row <;> rfl

theorem stepRound_prssReveal_bind (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (active : C.Party → Prop) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec β) :
    stepRound worldRoles D A noFunctionality state
      (fun i => suspendStep (k i) (prssRevealStep D active parts committed i)) = (do
      let (state', sent) ← worldRoles.adversary (A.round state (prssRevealVisible D active parts))
      let rows ← free (prssRevealRows D active parts committed sent)
      pure (state', (fun i => suspendStep (k i) (prssFinishStep i (rows i))), sent)) := by
  rw [stepRound_suspend, stepRound_prssReveal]
  · simp only [bind_assoc, pure_bind]
  · exact prssRevealStep_output D active parts committed
  · intro i out resume hs hi inbox
    by_cases ha : active i
    · simp only [prssRevealStep, if_neg hi, if_pos ha, Step.wait.injEq] at hs
      rcases hs with ⟨rfl, rfl⟩
      rw [advance_prssRevealResume, map_eq_bind_pure_comp]
      simp only [bind_assoc, pure_bind, map_bind, map_pure, Function.comp_def]
      apply bind_congr
      intro row
      exact continueStep_pending _ _ (prssFinishStep_output i row)
    · simp [prssRevealStep, hi, ha] at hs

/-- The actual two-round prefix also splits with arbitrary ceremony continuations attached.
The first continuation cannot run until the pending echo exchange completes. -/
theorem executePhase_prssSetup_bind_prefix (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (fuel : ℕ)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec β) :
    executePhase worldRoles D A noFunctionality (fuel + 2) state
      (fun i => prssSetup i >>= k i) = (do
      let data ← free (prssInitialData D)
      let (state', sent) ← worldRoles.adversary (A.round state (prssCommitVisible D data))
      let committed := prssCommitInbox D data sent
      let parts := fun i => (data i).1
      let active := fun i => (C.parties.any fun j => Msg.isAbort (committed i j)) = false
      if ∀ i, i ∉ D.1 → ¬ active i then pure (state', fun _ => none) else do
        let (state'', sent') ← worldRoles.adversary (A.round state' (prssRevealVisible D active parts))
        let rows ← free (prssRevealRows D active parts committed sent')
        executeRounds worldRoles D A noFunctionality fuel state''
          (fun i => suspendStep (k i) (prssFinishStep i (rows i)))) := by
  rw [executePhase, startSteps_prssSetup_bind]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply bind_congr
  intro data
  rw [executeRounds]
  simp only [suspendStep_isDone, if_neg (prssInitialSteps_not_done D data)]
  rw [stepRound_prssCommit_bind]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨state', sent⟩
  rw [executeRounds]
  simp only [suspendStep_isDone, prssRevealStep_all_done]
  split_ifs
  · simp only [suspendStep_output]
  · rw [stepRound_prssReveal_bind]
    simp only [bind_assoc, pure_bind]

/-- The local work performed by one network round of a real execution. -/
def roundLocal (D : C.Coalition) (steps : C.Party → Step C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) : OracleComp (LocalSpec C) (Step C E RealSpec α) :=
  match steps i with
  | .done out => pure (.done out)
  | .wait _ resume => if i ∈ D.1 then pure (.done none) else
      advance (resume fun j => if j ∈ D.1 then sent j i else (steps j).delivered i)
  | .call input _ => input.elim

theorem stepRound_real (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state steps = (do
      let (state', sent) ← worldRoles.adversary (A.round state fun c i =>
        if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none)
      let next ← free (Concrete.sequenceFin (roundLocal D steps sent))
      pure (state', next, sent)) := by
  have hc : ∀ i, (steps i).callInput = none := by
    intro i
    cases steps i with
    | done _ => rfl
    | wait _ _ => rfl
    | call input _ => exact input.elim
  simp only [stepRound, hc, Option.isSome_none, Bool.false_eq_true, and_false,
    exists_false, false_and, ↓reduceIte]
  apply bind_congr
  rintro ⟨state', sent⟩
  rw [free_sequenceFin]
  congr 2
  funext i
  unfold roundLocal
  cases steps i with
  | done out => rfl
  | call input _ => exact input.elim
  | wait out resume => split_ifs <;> rfl

/-- A pure local phase boundary remains pure before its attached continuation starts. -/
theorem roundLocal_suspend_finish (D : C.Coalition)
    (steps : C.Party → Step C E RealSpec α)
    (k : C.Party → α → PartyM C E RealSpec β)
    (hp : ∀ i, (steps i).output = none)
    (hl : ∀ i out resume, steps i = .wait out resume → i ∉ D.1 → ∀ inbox,
      ∃ result, advance (resume inbox) = pure (.done result))
    (sent : C.Party → Mail C E) (i : C.Party) :
    ∃ result, roundLocal D steps sent i = pure (.done result) ∧
      roundLocal D (fun j => suspendStep (k j) (steps j)) sent i = continueStep (k i) (.done result) := by
  have hin : (fun j => if j ∈ D.1 then sent j i else
      (suspendStep (k j) (steps j)).delivered i) =
      (fun j => if j ∈ D.1 then sent j i else (steps j).delivered i) := by
    funext j
    rw [suspendStep_delivered _ _ (hp j)]
  unfold roundLocal
  dsimp only
  cases hs : steps i with
  | done out =>
    have ho := hp i
    simp only [hs, Step.output] at ho
    subst out
    exact ⟨none, rfl, rfl⟩
  | call input _ => exact input.elim
  | wait out resume =>
    rw [suspendStep]
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi]
      exact ⟨none, rfl, rfl⟩
    · simp only [if_neg hi]
      obtain ⟨result, hr⟩ := hl i out resume hs hi
        (fun j => if j ∈ D.1 then sent j i else (steps j).delivered i)
      refine ⟨result, hr, ?_⟩
      rw [hin, advance_bind]
      change advance (resume _) >>= continueStep (k i) = _
      rw [hr, pure_bind]

/-- Pure completion of every local prefix lets the final network round run all suffixes
in exactly the same party order as the original executor. -/
theorem stepRound_suspend_finish (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (k : C.Party → α → PartyM C E RealSpec β)
    (hp : ∀ i, (steps i).output = none)
    (hl : ∀ i out resume, steps i = .wait out resume → i ∉ D.1 → ∀ inbox,
      ∃ result, advance (resume inbox) = pure (.done result)) :
    stepRound worldRoles D A noFunctionality state (fun i => suspendStep (k i) (steps i)) = (do
      let (state', next, sent) ← stepRound worldRoles D A noFunctionality state steps
      let next' ← free (Concrete.sequenceFin fun i => continueStep (k i) (next i))
      pure (state', next', sent)) := by
  rw [stepRound_real, stepRound_real]
  simp only [suspendStep_outbox, bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨state', sent⟩
  have hlocal := roundLocal_suspend_finish D steps k hp hl sent
  choose result hresult hnext using hlocal
  have hn : roundLocal D steps sent = fun i => pure (.done (result i)) := funext hresult
  have hn' : roundLocal D (fun j => suspendStep (k j) (steps j)) sent =
      fun i => continueStep (k i) (.done (result i)) := funext hnext
  rw [hn, hn', sequenceFin_pure, free_pure, pure_bind]

/-- Checking the final PRSS echo contains no local oracle calls. -/
theorem prssFinishStep_pure_resume (i : C.Party) (row : Option (PrssKeys C × List HashOutput))
    (out : Mail C E) (resume : Mail C E → OracleComp (PartySpec C E RealSpec) (Option (PrssKeys C)))
    (hs : prssFinishStep i row = .wait out resume) (inbox : Mail C E) :
    ∃ result, advance (resume inbox) = pure (.done result) := by
  cases row with
  | none => simp [prssFinishStep] at hs
  | some row =>
    simp only [prssFinishStep, Step.wait.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩
    unfold exchangeResume
    split_ifs
    · exact ⟨none, rfl⟩
    · rw [advance_require_bind]
      split_ifs
      · exact ⟨some row.1, rfl⟩
      · exact ⟨none, rfl⟩

theorem stepRound_prssFinish_bind (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (rows : C.Party → Option (PrssKeys C × List HashOutput))
    (k : C.Party → PrssKeys C → PartyM C E RealSpec β) :
    stepRound worldRoles D A noFunctionality state
      (fun i => suspendStep (k i) (prssFinishStep i (rows i))) = (do
      let (state', next, sent) ← stepRound worldRoles D A noFunctionality state
        (fun i => prssFinishStep i (rows i))
      let next' ← free (Concrete.sequenceFin fun i => continueStep (k i) (next i))
      pure (state', next', sent)) := by
  apply stepRound_suspend_finish D A state _ k (fun i => prssFinishStep_output i (rows i))
  intro i out resume hs hi inbox
  exact prssFinishStep_pure_resume i (rows i) out resume hs inbox

/-- A completed phase cannot cause an additional adversarial round after all operators abort. -/
theorem executeRounds_all_none (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State) :
    executeRounds worldRoles D A noFunctionality fuel state
      (fun _ => Step.done (C := C) (E := E) (G := RealSpec) (α := β) none) =
      pure (state, fun _ => none) := by
  cases fuel <;> simp [executeRounds, Step.isDone, Step.output]

/-- Sequential composition at a synchronous final round whose local checks are pure. -/
theorem executeRounds_suspend_finish (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α)
    (k : C.Party → α → PartyM C E RealSpec β)
    (hp : ∀ i, (steps i).output = none)
    (hl : ∀ i out resume, steps i = .wait out resume → i ∉ D.1 → ∀ inbox,
      ∃ result, advance (resume inbox) = pure (.done result)) :
    executeRounds worldRoles D A noFunctionality (fuel + 1) state
      (fun i => suspendStep (k i) (steps i)) = (do
      let (state', outputs) ← executeRounds worldRoles D A noFunctionality 1 state steps
      let next ← free (Concrete.sequenceFin fun i => continueStep (k i) (.done (outputs i)))
      executeRounds worldRoles D A noFunctionality fuel state' next) := by
  rw [executeRounds, executeRounds]
  simp only [suspendStep_isDone]
  split_ifs with hd
  · simp only [suspendStep_output, hp, pure_bind, continueStep, sequenceFin_pure,
      free_pure, executeRounds_all_none]
  · rw [stepRound_suspend_finish D A state steps k hp hl]
    simp only [bind_assoc, pure_bind, executeRounds]
    rw [stepRound_real]
    simp only [bind_assoc]
    apply bind_congr
    rintro ⟨state', sent⟩
    have hlocal := roundLocal_suspend_finish D steps k hp hl sent
    choose result hresult hnext using hlocal
    have hn : roundLocal D steps sent = fun i => pure (.done (result i)) := funext hresult
    rw [hn, sequenceFin_pure, free_pure, pure_bind]
    rfl

/-- Exact sequential composition of the actual three-round PRSS setup with any ceremony
continuation. Every aborted party stays aborted, and no additional adversarial round runs. -/
theorem executePhase_prssSetup_bind (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (fuel : ℕ)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec β) :
    executePhase worldRoles D A noFunctionality (fuel + 3) state
      (fun i => prssSetup i >>= k i) = (do
      let (state', outputs) ← executePhase worldRoles D A noFunctionality 3 state
        (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))
      let next ← free (Concrete.sequenceFin fun i => continueStep (k i) (.done (outputs i)))
      executeRounds worldRoles D A noFunctionality fuel state' next) := by
  have hf : fuel + 3 = (fuel + 1) + 2 := by omega
  rw [hf, executePhase_prssSetup_bind_prefix]
  change _ = (executePhase worldRoles D A noFunctionality (1 + 2) state _ >>= _)
  rw [executePhase_prssSetup_prefix]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro data
  apply bind_congr
  rintro ⟨state', sent⟩
  split_ifs
  · simp only [pure_bind, continueStep, sequenceFin_pure, free_pure, executeRounds_all_none]
  · simp only [bind_assoc]
    apply bind_congr
    rintro ⟨state'', sent'⟩
    apply bind_congr
    intro rows
    apply executeRounds_suspend_finish D A fuel state'' _ k
      (fun i => prssFinishStep_output i (rows i))
    intro i out resume hs hi inbox
    exact prssFinishStep_pure_resume i (rows i) out resume hs inbox

end ThresholdLeanXmssSecurity

end PrssContinuationComposition

section PrssEchoRelabeling
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E α : Type}

/-- Restrict an involution to a finite set and its image; all other points stay fixed. -/
def restrictInvolution {X : Type} [DecidableEq X] (f : X → X)
    (hf : Function.Involutive f) (s : Finset X) : Equiv.Perm X where
  toFun x := if x ∈ s ∨ f x ∈ s then f x else x
  invFun x := if x ∈ s ∨ f x ∈ s then f x else x
  left_inv x := by
    by_cases hx : x ∈ s ∨ f x ∈ s
    · have hfx : f x ∈ s ∨ f (f x) ∈ s := by simpa only [hf x, or_comm] using hx
      simp only [if_pos hx]
      rw [if_pos hfx, hf x]
    · simp only [if_neg hx]
  right_inv x := by
    by_cases hx : x ∈ s ∨ f x ∈ s
    · have hfx : f x ∈ s ∨ f (f x) ∈ s := by simpa only [hf x, or_comm] using hx
      simp only [if_pos hx]
      rw [if_pos hfx, hf x]
    · simp only [if_neg hx]

theorem restrictInvolution_mem {X : Type} [DecidableEq X] (f : X → X)
    (hf : Function.Involutive f) (s : Finset X) (x : X) (hx : x ∈ s) :
    restrictInvolution f hf s x = f x := by simp [restrictInvolution, hx]

theorem restrictInvolution_outside {X : Type} [DecidableEq X] (f : X → X)
    (hf : Function.Involutive f) (s : Finset X) (x : X) (hx : x ∉ s) (hfx : f x ∉ s) :
    restrictInvolution f hf s x = x := by simp [restrictInvolution, hx, hfx]

theorem restrictInvolution_fixed {X : Type} [DecidableEq X] (f : X → X)
    (hf : Function.Involutive f) (s : Finset X) (x : X) (hx : f x = x) :
    restrictInvolution f hf s x = x := by simp [restrictInvolution, hx]

theorem restrictInvolution_moved {X : Type} [DecidableEq X] (f : X → X)
    (hf : Function.Involutive f) (s : Finset X) (x : X)
    (hx : restrictInvolution f hf s x ≠ x) : x ∈ s ∪ s.image f := by
  by_cases hs : x ∈ s
  · exact Finset.mem_union_left _ hs
  · have hfs : f x ∈ s := by
      by_contra hn
      exact hx (restrictInvolution_outside f hf s x hs hn)
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f x, hfs, hf x⟩)

/-- Swap two key values only within the PRSS echo domain. -/
def prssEchoSwap (a b : HashOutput) : Query C → Query C
  | .sharedKeys .prss keys => .sharedKeys .prss (keys.map (Equiv.swap a b))
  | q => q

theorem prssEchoSwap_involutive (a b : HashOutput) :
    Function.Involutive (prssEchoSwap (C := C) a b) := by
  intro q
  cases q <;> try rfl
  rename_i phase keys
  cases phase <;> simp [prssEchoSwap, List.map_map, Function.comp_def]

/-- The actual echo query points at the active honest parties. -/
def prssEchoPoints (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) : Finset (Query C) :=
  (Finset.univ.filter (fun p : C.Party × C.Party => p.1 ∉ D.1 ∧ active p.1)).image
    fun p => .sharedKeys .prss ((sharedTerms p.1 p.2).map (keys p.1))

theorem prssEchoPoints_mem (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) (i j : C.Party) (hi : i ∉ D.1) (ha : active i) :
    Query.sharedKeys .prss ((sharedTerms i j).map (keys i)) ∈ prssEchoPoints D active keys := by
  exact Finset.mem_image.mpr ⟨(i,j), by simp [hi, ha], rfl⟩

theorem prssEchoPoints_card (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) : (prssEchoPoints D active keys).card ≤ C.n ^ 2 := by
  unfold prssEchoPoints
  calc
    _ ≤ (Finset.univ.filter (fun p : C.Party × C.Party => p.1 ∉ D.1 ∧ active p.1)).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (C.Party × C.Party)).card := Finset.card_filter_le _ _
    _ = C.n ^ 2 := by simp [pow_two]

/-- Renaming a lazy random-oracle input preserves its sampled answer and renames its cache.
No condition excludes hash-output collisions. -/
theorem randomOracle_relabel (e : Query C ≃ Query C) (q : Query C) (s : HashCache C) :
    Prod.map id (relabelHashCache e) <$>
      ((Query C →ₒ HashOutput).randomOracle q).run s =
      ((Query C →ₒ HashOutput).randomOracle (e q)).run (relabelHashCache e s) := by
  have hs : relabelHashCache e s (e q) = s q := by
    change s (e.symm (e q)) = s q
    rw [Equiv.symm_apply_apply]
  cases h : s q with
  | none =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ h,
      QueryImpl.withCaching_run_none _ (hs.trans h)]
    simp only [Functor.map_map, Prod.map, id_eq, relabelHashCache_query]
    rfl
  | some y =>
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ h,
      QueryImpl.withCaching_run_some _ (hs.trans h)]
    rfl

/-- The restricted echo renaming acts only on the actual points and their swapped images. -/
def prssEchoRelabel (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) (a b : HashOutput) : Query C ≃ Query C :=
  restrictInvolution (prssEchoSwap a b) (prssEchoSwap_involutive a b) (prssEchoPoints D active keys)

theorem prssEchoRelabel_at (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) (a b : HashOutput)
    (i j : C.Party) (hi : i ∉ D.1) (ha : active i) :
    prssEchoRelabel D active keys a b (.sharedKeys .prss ((sharedTerms i j).map (keys i))) =
      .sharedKeys .prss ((sharedTerms i j).map (fun T => Equiv.swap a b (keys i T))) := by
  rw [prssEchoRelabel, restrictInvolution_mem _ _ _ _ (prssEchoPoints_mem D active keys i j hi ha)]
  simp [prssEchoSwap, List.map_map, Function.comp_def]

/-- Every echo digest is preserved, including all equalities due to collisions, by the
corresponding relabeling of the hash function. -/
theorem prssEcho_relabel (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) (a b : HashOutput) (h : Query C → HashOutput)
    (i j : C.Party) (hi : i ∉ D.1) (ha : active i) :
    prssEcho (fun q => h ((prssEchoRelabel D active keys a b).symm q))
      (fun i T => Equiv.swap a b (keys i T)) i j = prssEcho h keys i j := by
  unfold prssEcho
  rw [← prssEchoRelabel_at D active keys a b i j hi ha]
  simp only [Equiv.symm_apply_apply]

/-- A counted query is changed only if it equals an actual echo input or its image,
not merely because its payload contains one of the swapped key values. -/
theorem prssEchoRelabel_moved (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) (a b : HashOutput) (q : Query C)
    (hq : prssEchoRelabel D active keys a b q ≠ q) :
    q ∈ prssEchoPoints D active keys ∪ (prssEchoPoints D active keys).image (prssEchoSwap a b) :=
  restrictInvolution_moved _ _ _ q hq

/-- On non-`Th` inputs the real hash handler is precisely its lazy random oracle. -/
theorem hashAnswer_nonhash (prims : Primitives) (q : Query C)
    (hq : ∀ input, q ≠ .hash input) :
    hashAnswer prims q = (Query C →ₒ HashOutput).randomOracle q := by
  cases q <;> try rfl
  exact (hq _ rfl).elim

/-- Oracle-input relabeling fixes every `Th` input, including its deterministic part. -/
theorem hashAnswer_relabel_of_hash (prims : Primitives) (e : Query C ≃ Query C)
    (hhash : ∀ input, e (.hash input) = .hash input) (q : Query C) (s : HashCache C) :
    Prod.map id (relabelHashCache e) <$> (hashAnswer prims q).run s =
      (hashAnswer prims (e q)).run (relabelHashCache e s) := by
  by_cases hq : ∃ input, q = .hash input
  · obtain ⟨input, rfl⟩ := hq
    rw [hhash]
    simp only [hashAnswer]
    split_ifs
    · rfl
    · let runRO : Query C → ProbComp (HashOutput × HashCache C) :=
        fun t => ((Query C →ₒ HashOutput).randomOracle t).run (relabelHashCache e s)
      have hr : runRO (e (.hash input)) = runRO (.hash input) := congrArg runRO (hhash input)
      exact (randomOracle_relabel e (.hash input) s).trans hr
  · have hn : ∀ input, q ≠ .hash input := by simpa only [not_exists] using hq
    have hn' : ∀ input, e q ≠ .hash input := by
      intro input he
      exact hn input (e.injective (he.trans (hhash input).symm))
    rw [hashAnswer_nonhash prims q hn, hashAnswer_nonhash prims (e q) hn']
    exact randomOracle_relabel e q s

theorem prssEchoRelabel_hash (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) (a b : HashOutput) (input : HashInput) :
    prssEchoRelabel D active keys a b (.hash input) = .hash input :=
  restrictInvolution_fixed _ _ _ _ rfl

/-- The cache symmetry also holds for arbitrary adaptive hash-only computations, when their
query handler is correspondingly relabeled. External queries still require the moved-point bound. -/
theorem evalDist_hashRun_relabel (prims : Primitives) (e : Query C ≃ Query C)
    (hhash : ∀ input, e (.hash input) = .hash input)
    (game : OracleComp (Query C →ₒ HashOutput) α) (s : HashCache C) :
    𝒟[Prod.map id (relabelHashCache e) <$> (simulateQ (hashAnswer prims) game).run s] =
      𝒟[(simulateQ (fun q => hashAnswer prims (e q)) game).run (relabelHashCache e s)] := by
  apply evalDist_simulateQ_state_projection
  intro q cache
  rw [hashAnswer_relabel_of_hash prims e hhash q cache]

theorem prssEchoInbox_relabel (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) (a b : HashOutput) (h : Query C → HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) :
    prssEchoInbox D active sent
      (fun q => h ((prssEchoRelabel D active keys a b).symm q))
      (fun i T => Equiv.swap a b (keys i T)) i = prssEchoInbox D active sent h keys i := by
  funext j
  unfold prssEchoInbox
  by_cases hj : j ∈ D.1
  · simp only [if_pos hj]
  · simp only [if_neg hj]
    by_cases ha : active j
    · rw [prssEcho_relabel D active keys a b h j i hj ha]
    · simp only [if_neg ha]

theorem prssEchoVisible_relabel (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) (a b : HashOutput) (h : Query C → HashOutput) :
    prssEchoVisible (E := E) D active
      (fun q => h ((prssEchoRelabel D active keys a b).symm q))
      (fun i T => Equiv.swap a b (keys i T)) = prssEchoVisible D active h keys := by
  funext c i
  unfold prssEchoVisible prssEchoOutbox
  by_cases hi : c ∈ D.1 ∧ i ∉ D.1
  · simp only [if_pos hi]
    by_cases ha : active i
    · rw [prssEcho_relabel D active keys a b h i c hi.2 ha]
    · simp only [if_neg ha]
  · simp only [if_neg hi]

/-- Exact preservation of the echo acceptance predicate, with collisions allowed. -/
theorem prssEchoAccepted_relabel (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) (a b : HashOutput) (h : Query C → HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) :
    prssEchoAccepted D active sent
      (fun q => h ((prssEchoRelabel D active keys a b).symm q))
      (fun i T => Equiv.swap a b (keys i T)) i ↔ prssEchoAccepted D active sent h keys i := by
  by_cases hi : i ∈ D.1
  · simp [prssEchoAccepted, hi]
  · by_cases ha : active i
    · simp only [prssEchoAccepted, prssEchoInbox_relabel, prssEchoCheck,
        prssEcho_relabel D active keys a b h i _ hi ha]
    · simp [prssEchoAccepted, ha]

/-- Projected final-round observations agree under the restricted relabeling. This exact
program identity assumes the given digest tables; the subsequent transformed-cache lemmas handle consistency, while setup-state weights remain open. -/
theorem prssEchoRound_relabel (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (active : C.Party → Prop) (h : Query C → HashOutput) (out : C.Party → PrssKeys C)
    (a b : HashOutput) (state : A.State) :
    (fun r => (r.1, fun i => (r.2.1 i).output.isSome, r.2.2)) <$>
      stepRound worldRoles D A noFunctionality state (prssEchoStep D active h out) =
    (fun r => (r.1, fun i => (r.2.1 i).output.isSome, r.2.2)) <$>
      stepRound worldRoles D A noFunctionality state (prssEchoStep D active
        (fun q => h ((prssEchoRelabel D active (fun i => (out i).term) a b).symm q))
        (fun i => ⟨fun T => Equiv.swap a b ((out i).term T), (out i).pair⟩)) := by
  simp only [stepRound_prssEcho, map_bind, map_pure, prssEchoVisible_relabel]
  apply bind_congr
  rintro ⟨state', sent⟩
  congr 3
  funext i
  simp only [Step.output, apply_ite Option.isSome, Option.isSome_some, Option.isSome_none]
  rw [prssEchoAccepted_relabel]

/-- Jointly rename hash inputs and permute the cached answers at selected inputs. -/
def transformHashCache (e : Query C ≃ Query C) (v : Query C → Equiv.Perm HashOutput)
    (s : HashCache C) : HashCache C :=
  fun q => (s (e.symm q)).map (v (e.symm q))

theorem transformHashCache_at (e : Query C ≃ Query C) (v : Query C → Equiv.Perm HashOutput)
    (s : HashCache C) (q : Query C) :
    transformHashCache e v s (e q) = (s q).map (v q) := by
  let cache : Query C → Option HashOutput := s
  change (cache (e.symm (e q))).map (v (e.symm (e q))) = (cache q).map (v q)
  rw [Equiv.symm_apply_apply]

theorem transformHashCache_query (e : Query C ≃ Query C) (v : Query C → Equiv.Perm HashOutput)
    (s : HashCache C) (q : Query C) (a : HashOutput) :
    transformHashCache e v (s.cacheQuery q a) =
      (transformHashCache e v s).cacheQuery (e q) (v q a) := by
  funext q'
  by_cases h : q' = e q
  · subst q'
    simp only [transformHashCache_at, QueryCache.cacheQuery_self, Option.map_some]
  · have h' : e.symm q' ≠ q := fun heq => h (by rw [← e.apply_symm_apply q', heq])
    simp only [transformHashCache, QueryCache.cacheQuery_of_ne _ _ h',
      QueryCache.cacheQuery_of_ne _ _ h]

/-- Input and per-input answer permutations preserve the lazy random-oracle transition law.
This includes changing a private derivation's answer and relabeling the later echo inputs. -/
theorem evalDist_randomOracle_transform (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput) (q : Query C) (s : HashCache C) :
    𝒟[Prod.map (v q) (transformHashCache e v) <$>
      ((Query C →ₒ HashOutput).randomOracle q).run s] =
      𝒟[((Query C →ₒ HashOutput).randomOracle (e q)).run (transformHashCache e v s)] := by
  cases hs : s q with
  | some a =>
    have ht : transformHashCache e v s (e q) = some (v q a) := by
      rw [transformHashCache_at, hs, Option.map_some]
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hs,
      QueryImpl.withCaching_run_some _ ht]
    rfl
  | none =>
    have ht : transformHashCache e v s (e q) = none := by
      rw [transformHashCache_at, hs, Option.map_none]
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hs,
      QueryImpl.withCaching_run_none _ ht]
    simp only [Functor.map_map, Prod.map, transformHashCache_query]
    let f : HashOutput → HashOutput × HashCache C :=
      fun a => (a, (transformHashCache e v s).cacheQuery (e q) a)
    change 𝒟[(fun a => f (v q a)) <$> ($ᵗ HashOutput)] = 𝒟[f <$> ($ᵗ HashOutput)]
    have hu := evalDist_map_bijective_uniform_cross (α := HashOutput) (v q) (v q).bijective
    have hm : (fun a => f (v q a)) <$> ($ᵗ HashOutput) = f <$> ((v q) <$> ($ᵗ HashOutput)) := by
      rw [Functor.map_map]
    rw [hm, evalDist_map, hu, ← evalDist_map]

/-- The real hash handler also respects the joint symmetry when both permutations fix `Th`. -/
theorem evalDist_hashAnswer_transform (prims : Primitives) (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput)
    (he : ∀ input, e (.hash input) = .hash input)
    (hv : ∀ input, v (.hash input) = Equiv.refl HashOutput)
    (q : Query C) (s : HashCache C) :
    𝒟[Prod.map (v q) (transformHashCache e v) <$> (hashAnswer prims q).run s] =
      𝒟[(hashAnswer prims (e q)).run (transformHashCache e v s)] := by
  by_cases hq : ∃ input, q = .hash input
  · obtain ⟨input, rfl⟩ := hq
    rw [he]
    simp only [hashAnswer]
    split_ifs
    · rw [hv]
      rfl
    · let runRO : Query C → ProbComp (HashOutput × HashCache C) :=
        fun t => ((Query C →ₒ HashOutput).randomOracle t).run (transformHashCache e v s)
      have hr : runRO (e (.hash input)) = runRO (.hash input) := congrArg runRO (he input)
      exact (evalDist_randomOracle_transform e v (.hash input) s).trans (congrArg evalDist hr)
  · have hn : ∀ input, q ≠ .hash input := by simpa only [not_exists] using hq
    have hn' : ∀ input, e q ≠ .hash input := by
      intro input h
      exact hn input (e.injective (h.trans (he input).symm))
    rw [hashAnswer_nonhash prims q hn, hashAnswer_nonhash prims (e q) hn']
    exact evalDist_randomOracle_transform e v q s

/-- The answer permutation for PRSS key derivations. Other hash domains retain their answers. -/
def prssDeriveSwap (a b : HashOutput) : Query C → Equiv.Perm HashOutput
  | .derive .prss .term _ => Equiv.swap a b
  | .derive .prss .pair _ => Equiv.swap a b
  | _ => Equiv.refl HashOutput

def prssSwapOutput (a b : HashOutput) (out : PrssKeys C) : PrssKeys C :=
  ⟨fun T => Equiv.swap a b (out.term T), fun j => Equiv.swap a b (out.pair j)⟩

theorem prssEchoRelabel_derive (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) (a b : HashOutput)
    (phase : Phase) (kind : KeyKind) (parts : List HashOutput) :
    prssEchoRelabel D active keys a b (.derive phase kind parts) = .derive phase kind parts :=
  restrictInvolution_fixed _ _ _ _ rfl

theorem transformHashCache_fixed (e : Query C ≃ Query C) (v : Query C → Equiv.Perm HashOutput)
    (s : HashCache C) (q : Query C) (he : e q = q) :
    transformHashCache e v s q = (s q).map (v q) := by
  let cache : Query C → Option HashOutput := transformHashCache e v s
  exact (congrArg cache he).symm.trans (transformHashCache_at e v s q)

/-- The simultaneous cache transformation retains both the newly permuted derivation values
and the old echo digests. This is a cache-consistency statement, not a transcript distribution law. -/
theorem prssDerivedEchoCached_transform (D : C.Coalition) (active : C.Party → Prop)
    (out : C.Party → PrssKeys C) (a b : HashOutput) (i : C.Party) (view : C.Party → Parts C)
    (shared : List HashOutput) (s : HashCache C) (hi : i ∉ D.1) (ha : active i)
    (hc : PrssDerivedEchoCached i view (out i, shared) s) :
    PrssDerivedEchoCached i view (prssSwapOutput a b (out i), shared)
      (transformHashCache (prssEchoRelabel D active (fun i => (out i).term) a b)
        (prssDeriveSwap a b) s) := by
  let e := prssEchoRelabel D active (fun i => (out i).term) a b
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro T hT
    have he : e (prssTermQuery view T) = prssTermQuery view T :=
      prssEchoRelabel_derive D active (fun i => (out i).term) a b _ _ _
    rw [transformHashCache_fixed _ _ _ _ he, hc.1.1 T hT]
    rfl
  · intro j hj
    have he : e (prssPairQuery i view j) = prssPairQuery i view j := by
      unfold prssPairQuery
      split_ifs <;> exact prssEchoRelabel_derive D active (fun i => (out i).term) a b _ _ _
    rw [transformHashCache_fixed _ _ _ _ he, hc.1.2 j hj]
    simp only [Option.map_some, prssSwapOutput, prssPairQuery]
    split_ifs <;> rfl
  · intro j
    have he := prssEchoRelabel_at D active (fun i => (out i).term) a b i j hi ha
    let cache : Query C → Option HashOutput := transformHashCache e (prssDeriveSwap a b) s
    have hlookup := transformHashCache_at e (prssDeriveSwap a b) s
      (.sharedKeys .prss ((sharedTerms i j).map (out i).term))
    have hr : (s (.sharedKeys .prss ((sharedTerms i j).map (out i).term))).map
        (prssDeriveSwap (C := C) a b (.sharedKeys .prss ((sharedTerms i j).map (out i).term))) =
        some (shared.getD j.val 0) := by rw [hc.2 j]; rfl
    exact (congrArg cache he).symm.trans (hlookup.trans hr)

/-- Every successful row of the actual reveal computation has a consistent transformed cache
for its permuted keys and unchanged precomputed echo list. -/
theorem prssRevealRows_transformed_cached (prims : Primitives) (D : C.Coalition)
    (active : C.Party → Prop) (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E)
    (s : HashCache C) (r : (C.Party → Option (PrssKeys C × List HashOutput)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssRevealRows D active parts committed sent)).run s)) (a b : HashOutput) :
    ∀ i row, r.1 i = some row →
      PrssDerivedEchoCached i (prssView parts (prssRevealInbox D active parts sent) i)
        (prssSwapOutput a b row.1, row.2)
        (transformHashCache
          (prssEchoRelabel D (fun i => (r.1 i).isSome) (fun i => (prssRowsKeys r.1 i).term) a b)
          (prssDeriveSwap a b) r.2) := by
  intro i row hi
  have hc := (prssRevealRows_cached prims D active parts committed sent s r hr).2 i row hi
  have hout : prssRowsKeys r.1 i = row.1 := by simp [prssRowsKeys, hi]
  have he := prssDerivedEchoCached_transform D (fun i => (r.1 i).isSome)
    (prssRowsKeys r.1) a b i (prssView parts (prssRevealInbox D active parts sent) i)
    row.2 r.2 hc.1 (by simp [hi]) (by rw [hout]; exact hc.2.2.2)
  simpa only [hout] using he

/-- The cache transformation is a random-oracle transition symmetry for any fixed parameters.
It changes the responses of the designated derivation domains as specified by `prssDeriveSwap`. -/
theorem prssEchoDerive_transition (prims : Primitives) (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) (a b : HashOutput) (q : Query C) (s : HashCache C) :
    𝒟[Prod.map (prssDeriveSwap a b q)
      (transformHashCache (prssEchoRelabel D active keys a b) (prssDeriveSwap a b)) <$>
        (hashAnswer prims q).run s] =
      𝒟[(hashAnswer prims (prssEchoRelabel D active keys a b q)).run
        (transformHashCache (prssEchoRelabel D active keys a b) (prssDeriveSwap a b) s)] :=
  evalDist_hashAnswer_transform prims _ _ (prssEchoRelabel_hash D active keys a b) (fun _ => rfl) q s

/-- Monitor an adaptive external hash computation in one common cache coordinate system.
A moved input or changed response sets a sticky bad flag. -/
def hashTransformMonitor (prims : Primitives) (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput) (transformed : Bool) :
    QueryImpl (Query C →ₒ HashOutput) (StateT (HashCache C × Bool) ProbComp) := fun q =>
  StateT.mk fun s =>
    let t := if transformed then e.symm q else q
    (fun r => (if transformed then v t r.1 else r.1,
      r.2, s.2 || decide (e q ≠ q) || decide (v t r.1 ≠ r.1))) <$>
      (hashAnswer prims t).run s.1

theorem hashTransformMonitor_bad (prims : Primitives) (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput) (b : Bool) (q : Query C)
    (s : HashCache C × Bool) (hs : s.2 = true)
    (r : HashOutput × (HashCache C × Bool))
    (hr : r ∈ support ((hashTransformMonitor prims e v b q).run s)) : r.2.2 = true := by
  simp only [hashTransformMonitor, StateT.run_mk, support_map] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  simp [hs]

/-- Both monitored handlers have exactly the same probability mass on every good output. -/
theorem hashTransformMonitor_good (prims : Primitives) (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput) (q : Query C) (s : HashCache C × Bool)
    (r : HashOutput × (HashCache C × Bool)) (hr : r.2.2 ≠ true) :
    Pr[= r | (hashTransformMonitor prims e v false q).run s] =
      Pr[= r | (hashTransformMonitor prims e v true q).run s] := by
  by_cases he : e q = q
  · have hes : e.symm q = q := by
      apply e.injective
      rw [Equiv.apply_symm_apply, he]
    let runHash : Query C → ProbComp (HashOutput × HashCache C) :=
      fun t => (hashAnswer prims t).run s.1
    change Pr[= r | (fun x : HashOutput × HashCache C =>
        (x.1, x.2, s.2 || decide (e q ≠ q) || decide (v q x.1 ≠ x.1))) <$> runHash q] =
      Pr[= r | (fun x : HashOutput × HashCache C =>
        (v (e.symm q) x.1, x.2, s.2 || decide (e q ≠ q) || decide (v (e.symm q) x.1 ≠ x.1))) <$>
        runHash (e.symm q)]
    rw [hes]
    simp only [he, ne_eq, not_true_eq_false, decide_false, Bool.or_false]
    rw [probOutput_map_eq_tsum_ite, probOutput_map_eq_tsum_ite]
    apply tsum_congr
    rintro ⟨a, cache⟩
    by_cases ha : v q a = a
    · simp only [ha]
    · have hn : (s.2 || decide (v q a ≠ a)) = true := by simp [ha]
      have h₁ : (a, cache, s.2 || decide (v q a ≠ a)) ≠ r := by
        intro h
        exact hr ((congrArg (fun x : HashOutput × (HashCache C × Bool) => x.2.2) h).symm.trans hn)
      have h₂ : (v q a, cache, s.2 || decide (v q a ≠ a)) ≠ r := by
        intro h
        exact hr ((congrArg (fun x : HashOutput × (HashCache C × Bool) => x.2.2) h).symm.trans hn)
      simp only [if_neg (Ne.symm h₁), if_neg (Ne.symm h₂)]
  · have hz : ∀ b, Pr[= r | (hashTransformMonitor prims e v b q).run s] = 0 := by
      intro b
      rw [probOutput_eq_zero_iff]
      intro h
      simp only [hashTransformMonitor, StateT.run_mk, support_map] at h
      obtain ⟨x, hx, rfl⟩ := h
      exact hr (by simp [he])
    rw [hz false, hz true]

/-- The original monitored handler projects to the original cache and oracle. -/
theorem hashTransformMonitor_original_step (prims : Primitives) (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput) (q : Query C) (s : HashCache C × Bool) :
    Prod.map id Prod.fst <$> (hashTransformMonitor prims e v false q).run s =
      (hashAnswer prims q).run s.1 := by
  simp [hashTransformMonitor, Functor.map_map, Prod.map]

/-- The transformed monitored handler projects to the actual transformed hash cache. -/
theorem hashTransformMonitor_transformed_step (prims : Primitives) (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput)
    (he : ∀ input, e (.hash input) = .hash input)
    (hv : ∀ input, v (.hash input) = Equiv.refl HashOutput)
    (q : Query C) (s : HashCache C × Bool) :
    𝒟[Prod.map id (fun s => transformHashCache e v s.1) <$>
      (hashTransformMonitor prims e v true q).run s] =
      𝒟[(hashAnswer prims q).run (transformHashCache e v s.1)] := by
  simp only [hashTransformMonitor, StateT.run_mk, if_true, Functor.map_map]
  change 𝒟[Prod.map (v (e.symm q)) (transformHashCache e v) <$>
    (hashAnswer prims (e.symm q)).run s.1] = _
  rw [evalDist_hashAnswer_transform prims e v he hv]
  let runHash : Query C → ProbComp (HashOutput × HashCache C) :=
    fun t => (hashAnswer prims t).run (transformHashCache e v s.1)
  exact congrArg (fun t => 𝒟[runHash t]) (e.apply_symm_apply q)

/-- The same adaptive hash program run from the two caches differs by at most the monitored
moved-input or changed-response event. The right side still needs a ceremony-specific bound. -/
theorem tvDist_hashRun_transform (prims : Primitives) (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput)
    (he : ∀ input, e (.hash input) = .hash input)
    (hv : ∀ input, v (.hash input) = Equiv.refl HashOutput)
    (game : OracleComp (Query C →ₒ HashOutput) α) (s : HashCache C) :
    tvDist ((simulateQ (hashAnswer prims) game).run' s)
      ((simulateQ (hashAnswer prims) game).run' (transformHashCache e v s)) ≤
      (Pr[fun r => r.2.2 = true |
        (simulateQ (hashTransformMonitor prims e v false) game).run (s, false)]).toReal := by
  have h₀ := evalDist_simulateQ_state_projection (hashTransformMonitor prims e v false)
    (hashAnswer prims) Prod.fst (fun q cache => by rw [hashTransformMonitor_original_step]) game (s, false)
  have h₁ := evalDist_simulateQ_state_projection (hashTransformMonitor prims e v true)
    (hashAnswer prims) (fun cache => transformHashCache e v cache.1)
    (hashTransformMonitor_transformed_step prims e v he hv) game (s, false)
  have p₀ : 𝒟[(simulateQ (hashTransformMonitor prims e v false) game).run' (s, false)] =
      𝒟[(simulateQ (hashAnswer prims) game).run' s] := by
    simp only [StateT.run'_eq, evalDist_map]
    simp only [evalDist_map] at h₀
    rw [← h₀, Functor.map_map]
    rfl
  have p₁ : 𝒟[(simulateQ (hashTransformMonitor prims e v true) game).run' (s, false)] =
      𝒟[(simulateQ (hashAnswer prims) game).run' (transformHashCache e v s)] := by
    simp only [StateT.run'_eq, evalDist_map]
    simp only [evalDist_map] at h₁
    rw [← h₁, Functor.map_map]
    rfl
  have ht := tvDist_simulateQ_le_probBad_of_good_outputs
    (hashTransformMonitor prims e v false) (hashTransformMonitor prims e v true)
    (fun cache => cache.2 = true)
    (hashTransformMonitor_good prims e v)
    (hashTransformMonitor_bad prims e v false)
    (hashTransformMonitor_bad prims e v true) game (s, false)
  simpa only [tvDist, p₀, p₁, Function.comp_def] using ht

/-- Lift a cache computation while retaining the monitor flag. -/
def withHashFlag {β : Type} (oa : StateT (HashCache C) ProbComp β) :
    StateT (HashCache C × Bool) ProbComp β := StateT.mk fun s =>
  (fun r => (r.1, r.2, s.2)) <$> oa.run s.1

def localTransformMonitor (prims : Primitives) (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput) (b : Bool) :
    QueryImpl (LocalSpec C) (StateT (HashCache C × Bool) ProbComp) :=
  (fun u => withHashFlag (unifFwdImpl (Query C →ₒ HashOutput) u)) +
    (hashTransformMonitor prims e v b + fun x : PrgInput C => withHashFlag (prgAnswer prims x))

theorem localTransformMonitor_bad (prims : Primitives) (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput) (b : Bool) (q : (LocalSpec C).Domain)
    (s : HashCache C × Bool) (hs : s.2 = true)
    (r : (LocalSpec C).Range q × (HashCache C × Bool))
    (hr : r ∈ support ((localTransformMonitor prims e v b q).run s)) : r.2.2 = true := by
  rcases q with u | q | x
  · simp only [localTransformMonitor, QueryImpl.add_apply_inl, withHashFlag, StateT.run_mk, support_map] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    exact hs
  · exact hashTransformMonitor_bad prims e v b q s hs r hr
  · simp only [localTransformMonitor, QueryImpl.add_apply_inr, withHashFlag, StateT.run_mk, support_map] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    exact hs

theorem localTransformMonitor_good (prims : Primitives) (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput) (q : (LocalSpec C).Domain)
    (s : HashCache C × Bool) (r : (LocalSpec C).Range q × (HashCache C × Bool))
    (hr : r.2.2 ≠ true) :
    Pr[= r | (localTransformMonitor prims e v false q).run s] =
      Pr[= r | (localTransformMonitor prims e v true q).run s] := by
  rcases q with u | q | x
  · rfl
  · exact hashTransformMonitor_good prims e v q s r hr
  · rfl

theorem withHashFlag_projection {β : Type} (oa : StateT (HashCache C) ProbComp β)
    (s : HashCache C × Bool) :
    Prod.map id Prod.fst <$> (withHashFlag oa).run s = oa.run s.1 := by
  simp [withHashFlag, Functor.map_map, Prod.map]

theorem localTransformMonitor_original_step (prims : Primitives) (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput) (q : (LocalSpec C).Domain) (s : HashCache C × Bool) :
    Prod.map id Prod.fst <$> (localTransformMonitor prims e v false q).run s =
      (localAnswer prims q).run s.1 := by
  rcases q with u | q | x
  · exact withHashFlag_projection _ s
  · exact hashTransformMonitor_original_step prims e v q s
  · exact withHashFlag_projection _ s

/-- Sampling and public AES calls respect the same cache transformation when stream-key
inputs and their answers are fixed. -/
theorem localTransformMonitor_transformed_step (prims : Primitives) (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput)
    (he : ∀ input, e (.hash input) = .hash input)
    (hv : ∀ input, v (.hash input) = Equiv.refl HashOutput)
    (hes : ∀ key, e (.streamKey key) = .streamKey key)
    (hvs : ∀ key, v (.streamKey key) = Equiv.refl HashOutput)
    (q : (LocalSpec C).Domain) (s : HashCache C × Bool) :
    𝒟[Prod.map id (fun s => transformHashCache e v s.1) <$>
      (localTransformMonitor prims e v true q).run s] =
      𝒟[(localAnswer prims q).run (transformHashCache e v s.1)] := by
  rcases q with u | q | x
  · simp [localTransformMonitor, withHashFlag, localAnswer, unifFwdImpl,
      Functor.map_map, Prod.map]
  · exact hashTransformMonitor_transformed_step prims e v he hv q s
  · have hh := evalDist_hashAnswer_transform prims e v he hv (.streamKey x.2.1) s.1
    rw [hvs] at hh
    let runHash : Query C → ProbComp (HashOutput × HashCache C) :=
      fun t => (hashAnswer prims t).run (transformHashCache e v s.1)
    have hr : runHash (e (.streamKey x.2.1)) = runHash (.streamKey x.2.1) :=
      congrArg runHash (hes x.2.1)
    have hq := hh.trans (congrArg evalDist hr)
    let f : HashOutput × HashCache C → Bit × HashCache C :=
      fun p => (prims.aes.eval (truncateHash p.1) x.2.2, p.2)
    have hm := congrArg (fun d => f <$> d) hq
    simpa only [localTransformMonitor, QueryImpl.add_apply_inr, withHashFlag, localAnswer,
      prgAnswer, StateT.run_mk, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map,
      Functor.map_map, ← evalDist_map, Function.comp_def, Prod.map, Equiv.refl_apply, id_eq, f, runHash] using hm

/-- Adaptive local adversaries may sample privately and call the public PRG as well as query `H`.
Their distinguishing distance is bounded by the same concrete monitor event. -/
theorem tvDist_localRun_transform (prims : Primitives) (e : Query C ≃ Query C)
    (v : Query C → Equiv.Perm HashOutput)
    (he : ∀ input, e (.hash input) = .hash input)
    (hv : ∀ input, v (.hash input) = Equiv.refl HashOutput)
    (hes : ∀ key, e (.streamKey key) = .streamKey key)
    (hvs : ∀ key, v (.streamKey key) = Equiv.refl HashOutput)
    (game : OracleComp (LocalSpec C) α) (s : HashCache C) :
    tvDist ((simulateQ (localAnswer prims) game).run' s)
      ((simulateQ (localAnswer prims) game).run' (transformHashCache e v s)) ≤
      (Pr[fun r => r.2.2 = true |
        (simulateQ (localTransformMonitor prims e v false) game).run (s, false)]).toReal := by
  have h₀ := evalDist_simulateQ_state_projection (localTransformMonitor prims e v false)
    (localAnswer prims) Prod.fst (fun q cache => by rw [localTransformMonitor_original_step]) game (s, false)
  have h₁ := evalDist_simulateQ_state_projection (localTransformMonitor prims e v true)
    (localAnswer prims) (fun cache => transformHashCache e v cache.1)
    (localTransformMonitor_transformed_step prims e v he hv hes hvs) game (s, false)
  have p₀ : 𝒟[(simulateQ (localTransformMonitor prims e v false) game).run' (s, false)] =
      𝒟[(simulateQ (localAnswer prims) game).run' s] := by
    simp only [StateT.run'_eq, evalDist_map]
    simp only [evalDist_map] at h₀
    rw [← h₀, Functor.map_map]
    rfl
  have p₁ : 𝒟[(simulateQ (localTransformMonitor prims e v true) game).run' (s, false)] =
      𝒟[(simulateQ (localAnswer prims) game).run' (transformHashCache e v s)] := by
    simp only [StateT.run'_eq, evalDist_map]
    simp only [evalDist_map] at h₁
    rw [← h₁, Functor.map_map]
    rfl
  have ht := tvDist_simulateQ_le_probBad_of_good_outputs
    (localTransformMonitor prims e v false) (localTransformMonitor prims e v true)
    (fun cache => cache.2 = true)
    (localTransformMonitor_good prims e v)
    (localTransformMonitor_bad prims e v false)
    (localTransformMonitor_bad prims e v true) game (s, false)
  simpa only [tvDist, p₀, p₁, Function.comp_def] using ht

/-- The finite set containing every moved echo input has at most twice the number of ordered
party pairs. This cardinality is not itself an adaptive hitting-probability bound. -/
theorem prssEchoRelabel_moved_card (D : C.Coalition) (active : C.Party → Prop)
    (keys : C.Party → C.Term → HashOutput) (a b : HashOutput) :
    (prssEchoPoints D active keys ∪
      (prssEchoPoints D active keys).image (prssEchoSwap a b)).card ≤ 2 * C.n ^ 2 := by
  have h := prssEchoPoints_card D active keys
  have hi := Finset.card_image_le (s := prssEchoPoints D active keys) (f := prssEchoSwap a b)
  have hu := Finset.card_union_le (prssEchoPoints D active keys)
    ((prssEchoPoints D active keys).image (prssEchoSwap a b))
  omega

theorem prssDeriveSwap_changed_value (a b u : HashOutput) (q : Query C)
    (h : prssDeriveSwap a b q u ≠ u) : u = a ∨ u = b := by
  cases q <;> try exact (h rfl).elim
  rename_i phase kind parts
  cases phase <;> cases kind <;> try exact (h rfl).elim
  all_goals exact Equiv.eq_or_eq_of_swap_apply_ne_self h

open scoped ENNReal

/-- A fresh PRSS derivation changes under the response swap with probability at most
`2 / 2^256`. The two swapped values are fixed before this fresh query. -/
theorem prob_prssDeriveSwap_fresh_le (prims : Primitives) (kind : KeyKind)
    (parts : List HashOutput) (s : HashCache C)
    (hs : s (.derive .prss kind parts) = none) (a b : HashOutput) :
    Pr[fun r => prssDeriveSwap (C := C) a b (.derive .prss kind parts) r.1 ≠ r.1 |
      (hashAnswer prims (.derive .prss kind parts)).run s] ≤ (2 : ℝ≥0∞) / 2 ^ 256 := by
  calc
    _ ≤ Pr[fun r => r.1 ∈ ({a,b} : Finset HashOutput) |
        (hashAnswer prims (.derive .prss kind parts)).run s] := by
      apply probEvent_mono
      intro r _ hr
      simpa only [Finset.mem_insert, Finset.mem_singleton] using prssDeriveSwap_changed_value a b r.1 _ hr
    _ = (({a,b} : Finset HashOutput).card : ℝ≥0∞) / 2 ^ 256 :=
      prob_hashAnswer_prss_mem prims kind parts s hs {a,b}
    _ ≤ (2 : ℝ≥0∞) / 2 ^ 256 := by
      apply ENNReal.div_le_div_right
      have hc : ({a,b} : Finset HashOutput).card ≤ 2 := by
        by_cases h : a = b <;> simp [h]
      exact_mod_cast hc

/-- The local-adversary coupling specialized to the simultaneous PRSS echo/derivation symmetry.
It is pointwise in the input cache and fixed relabeling. The actual setup weights, honest
hidden-stream transformation, and concrete bad-event probability remain additional obligations. -/
theorem tvDist_prssLocal_relabel (prims : Primitives) (D : C.Coalition)
    (active : C.Party → Prop) (keys : C.Party → C.Term → HashOutput)
    (a b : HashOutput) (game : OracleComp (LocalSpec C) α) (s : HashCache C) :
    tvDist ((simulateQ (localAnswer prims) game).run' s)
      ((simulateQ (localAnswer prims) game).run'
        (transformHashCache (prssEchoRelabel D active keys a b) (prssDeriveSwap a b) s)) ≤
      (Pr[fun r => r.2.2 = true |
        (simulateQ (localTransformMonitor prims (prssEchoRelabel D active keys a b)
          (prssDeriveSwap a b) false) game).run (s, false)]).toReal := by
  apply tvDist_localRun_transform prims _ _ (prssEchoRelabel_hash D active keys a b)
    (fun _ => rfl) _ (fun _ => rfl)
  intro key
  exact restrictInvolution_fixed _ _ _ _ rfl

end ThresholdLeanXmssSecurity

end PrssEchoRelabeling

section HiddenStreamRelabeling
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {α : Type}

/-- Rename a constant-range oracle cache by an involution of its inputs. -/
def involutionCache {X R : Type} (f : X → X) (c : (X →ₒ R).QueryCache) : (X →ₒ R).QueryCache :=
  fun x => c (f x)

theorem involutionCache_at {X R : Type} (f : X → X) (hf : Function.Involutive f)
    (c : (X →ₒ R).QueryCache) (x : X) : involutionCache f c (f x) = c x := by
  let cache : X → Option R := c
  change cache (f (f x)) = cache x
  rw [hf x]

theorem involutionCache_query {X R : Type} [DecidableEq X] (f : X → X) (hf : Function.Involutive f)
    (c : (X →ₒ R).QueryCache) (x : X) (y : R) :
    involutionCache f (c.cacheQuery x y) = (involutionCache f c).cacheQuery (f x) y := by
  funext t
  by_cases ht : t = f x
  · subst t
    rw [involutionCache_at f hf, QueryCache.cacheQuery_self, QueryCache.cacheQuery_self]
  · have ht' : f t ≠ x := by
      intro h
      exact ht ((hf t).symm.trans (congrArg f h))
    simp only [involutionCache, QueryCache.cacheQuery_of_ne _ _ ht', QueryCache.cacheQuery_of_ne _ _ ht]

theorem randomOracle_involution {X R : Type} [DecidableEq X] [SampleableType R]
    (f : X → X) (hf : Function.Involutive f) (x : X) (c : (X →ₒ R).QueryCache) :
    Prod.map id (involutionCache f) <$> ((X →ₒ R).randomOracle x).run c =
      ((X →ₒ R).randomOracle (f x)).run (involutionCache f c) := by
  cases hc : c x with
  | none =>
    have ht : involutionCache f c (f x) = none := (involutionCache_at f hf c x).trans hc
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hc,
      QueryImpl.withCaching_run_none _ ht]
    simp only [Functor.map_map, Prod.map, id_eq, involutionCache_query f hf]
    rfl
  | some y =>
    have ht : involutionCache f c (f x) = some y := (involutionCache_at f hf c x).trans hc
    rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_some _ hc,
      QueryImpl.withCaching_run_some _ ht]
    rfl

abbrev HiddenAddress (C : Committee) := (KeyName C × HashOutput) × ℕ × ℕ × ℕ

/-- Rename raw keys only at the hidden stream names. Labels and all position indices stay fixed. -/
def hiddenAddressSwap (D : C.Coalition) (a b : HashOutput) (x : HiddenAddress C) : HiddenAddress C :=
  ((x.1.1, if Hidden D x.1.1 then Equiv.swap a b x.1.2 else x.1.2), x.2)

theorem hiddenAddressSwap_involutive (D : C.Coalition) (a b : HashOutput) :
    Function.Involutive (hiddenAddressSwap D a b) := by
  rintro ⟨⟨name,key⟩,coords⟩
  by_cases hh : Hidden D name <;> simp [hiddenAddressSwap, hh]

theorem hiddenAddressSwap_known (D : C.Coalition) (a b : HashOutput)
    (x : HiddenAddress C) (hx : ¬ Hidden D x.1.1) : hiddenAddressSwap D a b x = x := by
  simp [hiddenAddressSwap, hx]

def hiddenCacheSwap (D : C.Coalition) (a b : HashOutput) (c : HiddenCache C) : HiddenCache C :=
  involutionCache (hiddenAddressSwap D a b) c

theorem hiddenCacheSwap_at (D : C.Coalition) (a b : HashOutput)
    (c : HiddenCache C) (x : HiddenAddress C) :
    hiddenCacheSwap D a b c (hiddenAddressSwap D a b x) = c x :=
  involutionCache_at _ (hiddenAddressSwap_involutive D a b) c x

theorem hiddenCacheSwap_query (D : C.Coalition) (a b : HashOutput)
    (c : HiddenCache C) (x : HiddenAddress C) (y : Bit) :
    hiddenCacheSwap D a b (c.cacheQuery x y) =
      (hiddenCacheSwap D a b c).cacheQuery (hiddenAddressSwap D a b x) y :=
  involutionCache_query _ (hiddenAddressSwap_involutive D a b) c x y

/-- The entire ideal-stream cache is transported, including previously used positions. -/
theorem hiddenOracle_swap (D : C.Coalition) (a b : HashOutput)
    (x : HiddenAddress C) (c : HiddenCache C) :
    Prod.map id (hiddenCacheSwap D a b) <$>
      ((HiddenAddress C →ₒ Bit).randomOracle x).run c =
      ((HiddenAddress C →ₒ Bit).randomOracle (hiddenAddressSwap D a b x)).run (hiddenCacheSwap D a b c) :=
  randomOracle_involution _ (hiddenAddressSwap_involutive D a b) x c

/-- The real `streamWorld` handler commutes with hidden-key renaming. Known names use their
unchanged public PRG input; hidden names use the correspondingly renamed ideal cache. -/
theorem streamWorld_stream_swap (prims : Primitives) (D : C.Coalition) (a b : HashOutput)
    (x : HiddenAddress C) (s : HashCache C) (c : HiddenCache C) :
    Prod.map id (fun st => (st.1, hiddenCacheSwap D a b st.2)) <$>
      (simulateQ (streamWorld prims D) (hiddenQuery x)).run (s,c) =
      (simulateQ (streamWorld prims D) (hiddenQuery (hiddenAddressSwap D a b x))).run
        (s,hiddenCacheSwap D a b c) := by
  by_cases hx : Hidden D x.1.1
  · have hx' : Hidden D (hiddenAddressSwap D a b x).1.1 := hx
    unfold hiddenQuery
    erw [simulateQ_spec_query, simulateQ_spec_query]
    simp only [streamWorld, hx, hx', if_true, StateT.run_mk]
    have hm := congrArg (fun p : ProbComp (Bit × HiddenCache C) =>
      (fun r => (r.1, (s, r.2))) <$> p) (hiddenOracle_swap D a b x c)
    simpa only [Functor.map_map, Function.comp_def, Prod.map, id_eq,
      hiddenAddressSwap, Prod.eta] using hm
  · rw [hiddenAddressSwap_known D a b x hx]
    unfold hiddenQuery
    erw [simulateQ_spec_query]
    simp only [streamWorld, hx, if_false, onHash, StateT.run_mk, Functor.map_map]
    rfl

/-- Adaptive programs of honest stream requests inherit the full cache relation. This is an
ideal-stream identity; it does not establish the real AES hop or setup-state uniformity. -/
theorem evalDist_streamRun_swap (prims : Primitives) (D : C.Coalition) (a b : HashOutput)
    (game : OracleComp (HiddenAddress C →ₒ Bit) α) (s : HashCache C) (c : HiddenCache C) :
    𝒟[Prod.map id (fun st => (st.1, hiddenCacheSwap D a b st.2)) <$>
      (simulateQ (fun x => simulateQ (streamWorld prims D) (hiddenQuery x)) game).run (s,c)] =
      𝒟[(simulateQ (fun x => simulateQ (streamWorld prims D)
        (hiddenQuery (hiddenAddressSwap D a b x))) game).run (s,hiddenCacheSwap D a b c)] := by
  apply evalDist_simulateQ_state_projection
  intro x st
  rw [streamWorld_stream_swap]

/-- The same key renaming on the names of the lazily sampled independent AES keys. -/
def hiddenKeySwap (D : C.Coalition) (a b : HashOutput) (x : KeyName C × HashOutput) :
    KeyName C × HashOutput :=
  (x.1, if Hidden D x.1 then Equiv.swap a b x.2 else x.2)

theorem hiddenKeySwap_involutive (D : C.Coalition) (a b : HashOutput) :
    Function.Involutive (hiddenKeySwap D a b) := by
  rintro ⟨name,key⟩
  by_cases hh : Hidden D name <;> simp [hiddenKeySwap, hh]

def keyCacheSwap (D : C.Coalition) (a b : HashOutput) (c : KeyCache C) : KeyCache C :=
  involutionCache (hiddenKeySwap D a b) c

/-- Independent AES keys are relabeled as a full cache, so stream outputs remain equal even
when many positions reuse a previously sampled AES key. -/
theorem keyOracle_swap (D : C.Coalition) (a b : HashOutput)
    (x : KeyName C × HashOutput) (c : KeyCache C) :
    Prod.map id (keyCacheSwap D a b) <$>
      (((KeyName C × HashOutput) →ₒ Digest).randomOracle x).run c =
      (((KeyName C × HashOutput) →ₒ Digest).randomOracle (hiddenKeySwap D a b x)).run
        (keyCacheSwap D a b c) :=
  randomOracle_involution _ (hiddenKeySwap_involutive D a b) x c

/-- Hidden raw-key renaming preserves honest streams also in the independent-AES-key world.
This uses no pseudorandomness assumption on AES: its underlying key is transported unchanged. -/
theorem lazyKeyWorld_stream_swap (prims : Primitives) (D : C.Coalition) (a b : HashOutput)
    (x : HiddenAddress C) (s : HashCache C) (c : KeyCache C) :
    Prod.map id (fun st => (st.1, keyCacheSwap D a b st.2)) <$>
      (simulateQ (lazyKeyWorld prims D) (hiddenQuery x)).run (s,c) =
      (simulateQ (lazyKeyWorld prims D) (hiddenQuery (hiddenAddressSwap D a b x))).run
        (s,keyCacheSwap D a b c) := by
  by_cases hx : Hidden D x.1.1
  · have hx' : Hidden D (hiddenAddressSwap D a b x).1.1 := hx
    unfold hiddenQuery
    erw [simulateQ_spec_query, simulateQ_spec_query]
    simp only [lazyKeyWorld, hx, hx', if_true, StateT.run_mk]
    have hm := congrArg (fun p : ProbComp (Digest × KeyCache C) =>
      (fun r => (prims.aes.eval r.1 x.2, (s, r.2))) <$> p) (keyOracle_swap D a b x.1 c)
    simpa only [Functor.map_map, Function.comp_def, Prod.map, id_eq,
      hiddenAddressSwap, hiddenKeySwap, Prod.eta] using hm
  · rw [hiddenAddressSwap_known D a b x hx]
    unfold hiddenQuery
    erw [simulateQ_spec_query]
    simp only [lazyKeyWorld, hx, if_false, StateT.run_mk, Functor.map_map]
    rfl

/-- The independent-key cache identity composes over arbitrary adaptive sequences of honest
stream requests, transporting previously sampled key entries. -/
theorem evalDist_lazyKeyRun_swap (prims : Primitives) (D : C.Coalition) (a b : HashOutput)
    (game : OracleComp (HiddenAddress C →ₒ Bit) α) (s : HashCache C) (c : KeyCache C) :
    𝒟[Prod.map id (fun st => (st.1, keyCacheSwap D a b st.2)) <$>
      (simulateQ (fun x => simulateQ (lazyKeyWorld prims D) (hiddenQuery x)) game).run (s,c)] =
      𝒟[(simulateQ (fun x => simulateQ (lazyKeyWorld prims D)
        (hiddenQuery (hiddenAddressSwap D a b x))) game).run (s,keyCacheSwap D a b c)] := by
  apply evalDist_simulateQ_state_projection
  intro x st
  rw [lazyKeyWorld_stream_swap]

/-- Change only the raw-key labels of honest hidden stream requests. Counted requests, hash
requests, programming requests and private sampling are forwarded unchanged. -/
def worldStreamRename (D : C.Coalition) (a b : HashOutput) :
    QueryImpl (WorldSpec C) (OracleComp (WorldSpec C)) := fun q => match q with
  | .inr (.inr (.inr x)) => hiddenQuery (hiddenAddressSwap D a b ((x.1,x.2.1),x.2.2))
  | q => OracleComp.lift (OracleSpec.query q)

theorem streamWorld_query_rename (prims : Primitives) (D : C.Coalition) (a b : HashOutput)
    (q : (WorldSpec C).Domain) (st : HashCache C × HiddenCache C) :
    Prod.map id (fun st => (st.1, hiddenCacheSwap D a b st.2)) <$>
      (streamWorld prims D q).run st =
      (simulateQ (streamWorld prims D) (worldStreamRename D a b q)).run
        (st.1,hiddenCacheSwap D a b st.2) := by
  rcases q with ((u | q | x) | p) | (u | q | x)
  all_goals try (simp [worldStreamRename, simulateQ_spec_query, streamWorld, onHash,
    Functor.map_map, Prod.map] <;> rfl)
  simpa only [hiddenQuery, worldStreamRename, simulateQ_spec_query, Prod.eta] using
    streamWorld_stream_swap prims D a b ((x.1,x.2.1),x.2.2) st.1 st.2

theorem lazyKeyWorld_query_rename (prims : Primitives) (D : C.Coalition) (a b : HashOutput)
    (q : (WorldSpec C).Domain) (st : HashCache C × KeyCache C) :
    Prod.map id (fun st => (st.1, keyCacheSwap D a b st.2)) <$>
      (lazyKeyWorld prims D q).run st =
      (simulateQ (lazyKeyWorld prims D) (worldStreamRename D a b q)).run
        (st.1,keyCacheSwap D a b st.2) := by
  rcases q with ((u | q | x) | p) | (u | q | x)
  all_goals try (simp [worldStreamRename, simulateQ_spec_query, lazyKeyWorld,
    Functor.map_map, Prod.map] <;> rfl)
  simpa only [hiddenQuery, worldStreamRename, simulateQ_spec_query, Prod.eta] using
    lazyKeyWorld_stream_swap prims D a b ((x.1,x.2.1),x.2.2) st.1 st.2

/-- The ideal-stream cache relation survives arbitrary adaptive interleavings of honest and
counted world queries. The honest stream query labels are explicitly renamed in the program. -/
theorem evalDist_streamWorld_rename (prims : Primitives) (D : C.Coalition) (a b : HashOutput)
    (game : OracleComp (WorldSpec C) α) (st : HashCache C × HiddenCache C) :
    𝒟[Prod.map id (fun st => (st.1, hiddenCacheSwap D a b st.2)) <$>
      (simulateQ (streamWorld prims D) game).run st] =
      𝒟[(simulateQ (streamWorld prims D) (simulateQ (worldStreamRename D a b) game)).run
        (st.1,hiddenCacheSwap D a b st.2)] := by
  rw [← QueryImpl.simulateQ_compose]
  apply evalDist_simulateQ_state_projection
  intro q state
  rw [QueryImpl.apply_compose, streamWorld_query_rename]

/-- The same adaptive world identity holds in the independently keyed AES world, with all
existing AES-key cache entries retained. It gives no bound for the original shared-key world. -/
theorem evalDist_lazyKeyWorld_rename (prims : Primitives) (D : C.Coalition) (a b : HashOutput)
    (game : OracleComp (WorldSpec C) α) (st : HashCache C × KeyCache C) :
    𝒟[Prod.map id (fun st => (st.1, keyCacheSwap D a b st.2)) <$>
      (simulateQ (lazyKeyWorld prims D) game).run st] =
      𝒟[(simulateQ (lazyKeyWorld prims D) (simulateQ (worldStreamRename D a b) game)).run
        (st.1,keyCacheSwap D a b st.2)] := by
  rw [← QueryImpl.simulateQ_compose]
  apply evalDist_simulateQ_state_projection
  intro q state
  rw [QueryImpl.apply_compose, lazyKeyWorld_query_rename]

theorem involutionCache_empty {X R : Type} (f : X → X) :
    involutionCache f (∅ : (X →ₒ R).QueryCache) = ∅ := rfl

/-- From an empty ideal-stream cache, honest key-label renaming preserves the output law.
The supplied hash cache is the same on both sides. -/
theorem evalDist_streamWorld_empty_rename (prims : Primitives) (D : C.Coalition) (a b : HashOutput)
    (game : OracleComp (WorldSpec C) α) (s : HashCache C) :
    𝒟[(simulateQ (streamWorld prims D) game).run' (s,∅)] =
      𝒟[(simulateQ (streamWorld prims D) (simulateQ (worldStreamRename D a b) game)).run' (s,∅)] := by
  have h := evalDist_streamWorld_rename prims D a b game (s,∅)
  have he : hiddenCacheSwap D a b (∅ : HiddenCache C) = ∅ := rfl
  simp only [he, evalDist_map] at h
  simp only [StateT.run'_eq, evalDist_map]
  rw [← h, Functor.map_map]
  rfl

/-- The analogous output-law identity for independent AES keys, without a PRF assumption. -/
theorem evalDist_lazyKeyWorld_empty_rename (prims : Primitives) (D : C.Coalition) (a b : HashOutput)
    (game : OracleComp (WorldSpec C) α) (s : HashCache C) :
    𝒟[(simulateQ (lazyKeyWorld prims D) game).run' (s,∅)] =
      𝒟[(simulateQ (lazyKeyWorld prims D) (simulateQ (worldStreamRename D a b) game)).run' (s,∅)] := by
  have h := evalDist_lazyKeyWorld_rename prims D a b game (s,∅)
  have he : keyCacheSwap D a b (∅ : KeyCache C) = ∅ := rfl
  simp only [he, evalDist_map] at h
  simp only [StateT.run'_eq, evalDist_map]
  rw [← h, Functor.map_map]
  rfl

end ThresholdLeanXmssSecurity

end HiddenStreamRelabeling

section HonestProgramRelabeling
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E α β : Type} {ι : Type} {G : OracleSpec ι}

def roStreamRename (D : C.Coalition) (a b : HashOutput) :
    QueryImpl (RoSpec C) (OracleComp (RoSpec C)) := fun q => match q with
  | .inl q => hashQuery q
  | .inr x => query (spec := RoSpec C) (.inr
      (x.1, (if Hidden D x.1 then Equiv.swap a b x.2.1 else x.2.1), x.2.2))

def localStreamRename (D : C.Coalition) (a b : HashOutput) :
    QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)) := fun q => match q with
  | .inl u => OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inl u))
  | .inr q => liftComp (roStreamRename D a b q) _

def partyStreamRename (D : C.Coalition) (a b : HashOutput) :
    QueryImpl (PartySpec C E G) (OracleComp (PartySpec C E G)) := fun q => match q with
  | .inl (.inl q) => liftComp (localStreamRename D a b q) _
  | .inl (.inr outbox) => OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (.inl (.inr outbox)))
  | .inr input => OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (.inr input))

def renameParty (D : C.Coalition) (a b : HashOutput) (p : PartyM C E G α) : PartyM C E G α :=
  OptionT.mk (simulateQ (partyStreamRename D a b) p.run)

def renameRun (D : C.Coalition) (a b : HashOutput) (p : RunM C E G α) : RunM C E G α :=
  fun s => renameParty D a b (p s)

theorem renameParty_pure (D : C.Coalition) (a b : HashOutput) (x : α) :
    renameParty (E := E) (G := G) D a b (pure x) = pure x := rfl

theorem renameParty_failure (D : C.Coalition) (a b : HashOutput) :
    renameParty (E := E) (G := G) D a b (failure : PartyM C E G α) = failure := rfl

theorem renameParty_bind (D : C.Coalition) (a b : HashOutput)
    (p : PartyM C E G α) (k : α → PartyM C E G β) :
    renameParty D a b (p >>= k) = (renameParty D a b p >>= fun x => renameParty D a b (k x)) := by
  unfold renameParty
  apply OptionT.ext
  simp only [OptionT.run_bind, OptionT.run_mk, Option.elimM, simulateQ_bind]
  congr 1
  funext x
  cases x <;> simp

theorem partyStreamRename_local (D : C.Coalition) (a b : HashOutput)
    (p : OracleComp (LocalSpec C) α) :
    simulateQ (partyStreamRename (E := E) (G := G) D a b) (liftComp p _) =
      liftComp (simulateQ (localStreamRename D a b) p) _ := by
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind q k ih =>
    simp only [liftComp_bind, simulateQ_bind, ih]
    congr 1
    rw [liftComp_query]
    simp only [OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rw [liftM_query_local, simulateQ_spec_query, simulateQ_spec_query]
    rfl

theorem renameParty_localStep (D : C.Coalition) (a b : HashOutput)
    (p : OracleComp (LocalSpec C) α) :
    renameParty (E := E) (G := G) D a b (localStep p) =
      localStep (simulateQ (localStreamRename D a b) p) := by
  apply OptionT.ext
  change simulateQ (partyStreamRename D a b) (some <$> liftComp p _) =
    some <$> liftComp (simulateQ (localStreamRename D a b) p) _
  rw [simulateQ_map, partyStreamRename_local]

theorem localStreamRename_ro (D : C.Coalition) (a b : HashOutput)
    (p : OracleComp (RoSpec C) α) :
    simulateQ (localStreamRename D a b) (liftComp p (LocalSpec C)) =
      liftComp (simulateQ (roStreamRename D a b) p) (LocalSpec C) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind q k ih =>
    simp only [liftComp_bind, simulateQ_bind, ih]
    congr 1
    change simulateQ (localStreamRename D a b)
      (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr q))) =
      liftComp (simulateQ (roStreamRename D a b) (OracleComp.lift (OracleSpec.query q))) _
    rw [simulateQ_spec_query, simulateQ_spec_query]
    rfl

theorem renameParty_oracleStep (D : C.Coalition) (a b : HashOutput)
    (p : OracleComp (RoSpec C) α) :
    renameParty (E := E) (G := G) D a b (oracleStep p) =
      oracleStep (simulateQ (roStreamRename D a b) p) := by
  rw [oracleStep, renameParty_localStep, localStreamRename_ro]
  rfl

theorem renameParty_exchange (D : C.Coalition) (a b : HashOutput) (outbox : Mail C E) :
    renameParty (G := G) D a b (exchange outbox) = exchange outbox := by
  apply OptionT.ext
  simp only [renameParty, exchange, OptionT.run_mk, OptionT.run_bind, OptionT.run_lift, Option.elimM,
    simulateQ_bind, simulateQ_map, simulateQ_spec_query, partyStreamRename]
  congr 1
  funext inbox
  cases inbox with
  | none => rfl
  | some inbox => simp only [Option.elim_some]; split <;> rfl

theorem renameParty_require (D : C.Coalition) (a b : HashOutput) (p : Prop) :
    renameParty (E := E) (G := G) D a b (require p) = require p := by
  unfold require
  split <;> rfl

theorem renameRun_bind (D : C.Coalition) (a b : HashOutput)
    (p : RunM C E G α) (k : α → RunM C E G β) :
    renameRun D a b (p >>= k) = (renameRun D a b p >>= fun x => renameRun D a b (k x)) := by
  funext s
  exact renameParty_bind D a b _ _

theorem renameRun_pure (D : C.Coalition) (a b : HashOutput) (x : α) :
    renameRun (E := E) (G := G) D a b (pure x) = pure x := rfl

theorem renameRun_lift (D : C.Coalition) (a b : HashOutput) (p : PartyM C E G α) :
    renameRun D a b (StateT.lift p) = StateT.lift (renameParty D a b p) := by
  funext s
  change renameParty D a b (p >>= fun x => pure (x,s)) = _
  rw [renameParty_bind]
  rfl

theorem renameRun_freshLabel (D : C.Coalition) (a b : HashOutput) :
    renameRun (E := E) (G := G) D a b freshLabel = freshLabel := rfl

/-- The context transformation changes only PRSS keys at hidden names. The dealer keys and the
operator's identity stay fixed. Self pair keys are unused and stay fixed as well. -/
def hiddenContextSwap (D : C.Coalition) (a b : HashOutput) (ctx : Context C) : Context C :=
  { ctx with prss := {
    term := fun T => if Hidden D (.term T) then Equiv.swap a b (ctx.prss.term T) else ctx.prss.term T
    pair := fun j => if h : j = ctx.self then ctx.prss.pair j else
      if Hidden D (.pair (C.pairOf ctx.self j (Ne.symm h))) then Equiv.swap a b (ctx.prss.pair j)
      else ctx.prss.pair j } }

theorem roStreamRename_prgBits (D : C.Coalition) (a b : HashOutput)
    (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    simulateQ (roStreamRename D a b) (prgBits name key ρ idx count) =
      prgBits name (if Hidden D name then Equiv.swap a b key else key) ρ idx count := by
  simp [prgBits, roStreamRename, simulateQ_list_mapM]

theorem roStreamRename_bitCodec (D : C.Coalition) (a b : HashOutput)
    (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    simulateQ (roStreamRename D a b) ((bitCodec (E := E)).draw name key ρ idx count) =
      (bitCodec (E := E)).draw name (if Hidden D name then Equiv.swap a b key else key) ρ idx count :=
  roStreamRename_prgBits D a b name key ρ idx count

theorem roStreamRename_elementCodec [Field E] [Algebra Bit E] (K : Constants C E)
    (D : C.Coalition) (a b : HashOutput) (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    simulateQ (roStreamRename D a b) ((elementCodec K).draw name key ρ idx count) =
      (elementCodec K).draw name (if Hidden D name then Equiv.swap a b key else key) ρ idx count := by
  simp only [elementCodec, simulateQ_bind, simulateQ_pure, roStreamRename_prgBits]

attribute [local simp] renameParty_bind renameParty_pure renameParty_failure
  renameParty_localStep renameParty_oracleStep renameParty_exchange renameParty_require
  renameRun_bind renameRun_pure renameRun_lift renameRun_freshLabel

theorem renameRun_prssRandomness {R : Type} [Zero R] (codec : Codec C E R)
    (D : C.Coalition) (a b : HashOutput)
    (hcodec : ∀ name key ρ idx count, simulateQ (roStreamRename D a b) (codec.draw name key ρ idx count) =
      codec.draw name (if Hidden D name then Equiv.swap a b key else key) ρ idx count)
    (ctx : Context C) (idx count : ℕ) :
    renameRun (G := G) D a b (prssRandomness ctx codec idx count) =
      prssRandomness (hiddenContextSwap D a b ctx) codec idx count := by
  simp only [prssRandomness, renameRun_bind, renameRun_freshLabel]
  congr 1
  funext ρ
  simp only [renameRun_bind, renameRun_lift, renameParty_oracleStep, simulateQ_list_mapM,
    simulateQ_ite, simulateQ_dite, simulateQ_pure, hcodec, renameRun_pure]
  congr 1
  funext r
  congr 1
  congr 1
  apply congrArg (fun f => oracleStep (C.parties.mapM f))
  funext j
  by_cases hj : j = ctx.self <;> simp [hiddenContextSwap, hj]

theorem renameParty_ite (D : C.Coalition) (a b : HashOutput) (p : Prop) [Decidable p]
    (x y : PartyM C E G α) :
    renameParty D a b (if p then x else y) = if p then renameParty D a b x else renameParty D a b y := by
  split <;> rfl

theorem renameRun_ite (D : C.Coalition) (a b : HashOutput) (p : Prop) [Decidable p]
    (x y : RunM C E G α) :
    renameRun D a b (if p then x else y) = if p then renameRun D a b x else renameRun D a b y := by
  split <;> rfl

theorem renameRun_get (D : C.Coalition) (a b : HashOutput) :
    renameRun (E := E) (G := G) D a b get = get := rfl

theorem renameRun_set (D : C.Coalition) (a b : HashOutput) (s : RunState C) :
    renameRun (E := E) (G := G) D a b (set s) = set s := rfl

theorem renameRun_modify (D : C.Coalition) (a b : HashOutput) (f : RunState C → RunState C) :
    renameRun (E := E) (G := G) D a b (modify f) = modify f := rfl

theorem renameRun_foldlM (D : C.Coalition) (a b : HashOutput)
    (f : β → α → RunM C E G β) (xs : List α) (init : β) :
    renameRun D a b (xs.foldlM f init) = xs.foldlM (fun x y => renameRun D a b (f x y)) init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih => simp [List.foldlM_cons, ih]

theorem roStreamRename_hash (D : C.Coalition) (a b : HashOutput) (q : Query C) :
    simulateQ (roStreamRename D a b) (hashQuery q) = hashQuery q := by
  simp [hashQuery, roStreamRename]

theorem roStreamRename_findChallenge [Field E] [Algebra Bit E] (K : Constants C E)
    (D : C.Coalition) (a b key : HashOutput) (tries index : ℕ) :
    simulateQ (roStreamRename D a b) (findChallenge K key tries index) = findChallenge K key tries index := by
  induction tries generalizing index with
  | zero => rfl
  | succ tries ih =>
    simp only [findChallenge, simulateQ_bind, roStreamRename_hash]
    congr 1
    funext h
    split <;> simp [ih]

attribute [local simp] renameParty_ite renameRun_ite renameRun_get renameRun_set renameRun_modify
  renameRun_foldlM roStreamRename_hash roStreamRename_findChallenge

@[local simp] theorem renameParty_map (D : C.Coalition) (a b : HashOutput)
    (f : α → β) (p : PartyM C E G α) :
    renameParty D a b (f <$> p) = f <$> renameParty D a b p := by
  simp only [map_eq_pure_bind, renameParty_bind, renameParty_pure]

@[local simp] theorem renameRun_map (D : C.Coalition) (a b : HashOutput)
    (f : α → β) (p : RunM C E G α) :
    renameRun D a b (f <$> p) = f <$> renameRun D a b p := by
  simp only [map_eq_pure_bind, renameRun_bind, renameRun_pure]

section Protocol
variable [Field E] [Algebra Bit E] (K : Constants C E) (D : C.Coalition) (a b : HashOutput)

theorem renameRun_reshare {R : Type} [Field R] (ctx : Context C) (codec : Codec C E R)
    (randomness : PrssOutput C R) (v : ℕ → R) (count : ℕ) :
    renameRun (G := G) D a b (reshare K ctx codec randomness v count) =
      reshare K (hiddenContextSwap D a b ctx) codec randomness v count := by
  simp [reshare, record, hiddenContextSwap]

theorem renameRun_reshareCollector (ctx : Context C) (randomness : PrssOutput C Bit)
    (v : ℕ → Bit) (count : ℕ) :
    renameRun (G := G) D a b (reshareCollector K ctx randomness v count) =
      reshareCollector K (hiddenContextSwap D a b ctx) randomness v count := by
  simp [reshareCollector, record, hiddenContextSwap]

theorem renameRun_reshareWith (ctx : Context C) (mode : ReshareMode)
    (randomness : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    renameRun (G := G) D a b (reshareWith K ctx mode randomness v count) =
      reshareWith K (hiddenContextSwap D a b ctx) mode randomness v count := by
  cases mode <;> simp [reshareWith, renameRun_reshare, renameRun_reshareCollector]

theorem renameParty_openRep (ctx : Context C) (v : Shares C Bit) (count : ℕ) :
    renameParty (G := G) D a b (openRep K ctx v count) =
      openRep K (hiddenContextSwap D a b ctx) v count := by
  simp [openRep, hiddenContextSwap, simulateQ_list_mapM]

theorem renameParty_openSh (ctx : Context C) (v : ℕ → E) (count : ℕ) :
    renameParty (G := G) D a b (openSh K ctx v count) =
      openSh K (hiddenContextSwap D a b ctx) v count := by
  simp [openSh, hiddenContextSwap]

theorem renameRun_coinWith (ctx : Context C) (randomness : PrssOutput C E) (count : ℕ) :
    renameRun (G := G) D a b (coinWith K ctx randomness count) =
      coinWith K (hiddenContextSwap D a b ctx) randomness count := by
  simp only [coinWith, renameRun_bind, renameRun_lift, renameRun_pure, renameParty_openSh]
  rfl

theorem renameRun_compareDigests (ctx : Context C) (salts : Shares C Bit) :
    renameRun (E := E) (G := G) D a b (compareDigests ctx salts) =
      compareDigests (hiddenContextSwap D a b ctx) salts := by
  simp [compareDigests, hiddenContextSwap, simulateQ_list_mapM]

/-- Rename every primitive gadget of a check, while retaining its data and schedule. -/
def renameCheckGadgets (gadgets : CheckGadgets C E G) : CheckGadgets C E G where
  coin n := renameRun D a b (gadgets.coin n)
  extendMult xs := renameRun D a b (gadgets.extendMult xs)
  randElements n := renameRun D a b (gadgets.randElements n)
  randBits n := renameRun D a b (gadgets.randBits n)

theorem renameRun_coinKey (gadgets : CheckGadgets C E G) :
    renameRun D a b (coinKey K gadgets) = coinKey K (renameCheckGadgets D a b gadgets) := by
  simp only [coinKey, renameRun_bind, renameRun_get, renameRun_lift, renameParty_oracleStep,
    roStreamRename_hash]
  rfl

theorem renameRun_expand (key : HashOutput) (count : ℕ) :
    renameRun (G := G) D a b (ThresholdLeanXmss.expand K key count) =
      ThresholdLeanXmss.expand K key count := by
  simp [ThresholdLeanXmss.expand, simulateQ_list_mapM]

theorem renameRun_challenge (gadgets : CheckGadgets C E G) :
    renameRun D a b (challenge K gadgets) = challenge K (renameCheckGadgets D a b gadgets) := by
  unfold challenge
  rw [renameRun_bind, renameRun_coinKey]
  congr 1
  funext key
  simp only [renameRun_bind, renameRun_lift, renameParty_oracleStep, roStreamRename_findChallenge]
  congr 1
  funext out
  cases out <;> simp

theorem renameRun_check (ctx : Context C) (gadgets : CheckGadgets C E G) (tuples : List (Tuple C)) :
    renameRun D a b (check K ctx gadgets tuples) =
      check K (hiddenContextSwap D a b ctx) (renameCheckGadgets D a b gadgets) tuples := by
  simp only [check, renameRun_ite, renameRun_pure, renameRun_bind, renameRun_lift,
    renameParty_require, renameRun_expand, renameRun_coinKey, renameRun_foldlM,
    renameRun_challenge, renameRun_compareDigests, renameParty_openSh]
  rfl

theorem rename_realCheckGadgets (ctx : Context C) :
    renameCheckGadgets (G := G) D a b (realCheckGadgets K ctx) =
      realCheckGadgets K (hiddenContextSwap D a b ctx) := by
  unfold renameCheckGadgets realCheckGadgets
  congr 1
  · funext count
    rw [renameRun_bind, renameRun_prssRandomness _ D a b (roStreamRename_elementCodec K D a b)]
    congr 1
    funext randomness
    exact renameRun_coinWith K D a b ctx randomness count
  · funext products
    rw [renameRun_bind, renameRun_prssRandomness _ D a b (roStreamRename_elementCodec K D a b)]
    congr 1
    funext randomness
    rw [renameRun_reshare]
    rfl
  · funext count
    exact renameRun_prssRandomness _ D a b (roStreamRename_elementCodec K D a b) _ _ _
  · funext count
    exact renameRun_prssRandomness _ D a b (roStreamRename_bitCodec D a b) _ _ _

def renameRunGadgets (gadgets : RunGadgets C E G) : RunGadgets C E G where
  mode := gadgets.mode
  mult x y n := renameRun D a b (gadgets.mult x y n)
  rerand x n := renameRun D a b (gadgets.rerand x n)
  verify xs := renameRun D a b (gadgets.verify xs)
  output x n := renameRun D a b (gadgets.output x n)

theorem rename_realRunGadgets (ctx : Context C) (mode : ReshareMode) :
    renameRunGadgets (G := G) D a b (realRunGadgets K ctx mode) =
      realRunGadgets K (hiddenContextSwap D a b ctx) mode := by
  unfold renameRunGadgets realRunGadgets
  congr 1
  · funext x y count
    rw [renameRun_bind, renameRun_prssRandomness _ D a b (roStreamRename_bitCodec D a b)]
    congr 1
    funext randomness
    rw [renameRun_reshareWith]
    rfl
  · funext v count
    rw [renameRun_bind, renameRun_prssRandomness _ D a b (roStreamRename_bitCodec D a b)]
    congr 1
    funext randomness
    rw [renameRun_reshare]
    rfl
  · funext tuples
    rw [renameRun_check, rename_realCheckGadgets]
  · funext v count
    rw [renameRun_lift, renameParty_openRep]

theorem renameRun_runJobs (gadgets : RunGadgets C E G)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    renameRun D a b (runJobs K gadgets jobs inputs) =
      runJobs K (renameRunGadgets D a b gadgets) jobs inputs := by
  simp only [runJobs, renameRun_bind, renameRun_foldlM, renameRun_pure]
  rfl

/-- A complete real batch with transformed hidden PRSS keys is exactly the program obtained by
renaming its honest stream requests. This includes the check and the final opening. -/
theorem renameRun_realRunJobs (ctx : Context C) (mode : ReshareMode)
    (jobs : List Circuit) (inputs : List (C.Term → List Bit)) :
    renameRun (G := G) D a b (runJobs K (realRunGadgets K ctx mode) jobs inputs) =
      runJobs K (realRunGadgets K (hiddenContextSwap D a b ctx) mode) jobs inputs := by
  rw [renameRun_runJobs, rename_realRunGadgets]

end Protocol
/-- The pending network interface is retained; only later honest stream queries are renamed. -/
def renameStep (D : C.Coalition) (a b : HashOutput) : Step C E G α → Step C E G α
  | .done out => .done out
  | .wait out resume => .wait out (fun inbox => simulateQ (partyStreamRename D a b) (resume inbox))
  | .call input resume => .call input (fun r => simulateQ (partyStreamRename D a b) (resume r))

@[local simp] theorem renameStep_outbox (D : C.Coalition) (a b : HashOutput) (s : Step C E G α) :
    (renameStep D a b s).outbox = s.outbox := by cases s <;> rfl

@[local simp] theorem renameStep_delivered (D : C.Coalition) (a b : HashOutput) (s : Step C E G α) :
    (renameStep D a b s).delivered = s.delivered := by cases s with
    | done out => cases out <;> rfl
    | wait _ _ => rfl
    | call _ _ => rfl

@[local simp] theorem renameStep_output (D : C.Coalition) (a b : HashOutput) (s : Step C E G α) :
    (renameStep D a b s).output = s.output := by cases s <;> rfl

@[local simp] theorem renameStep_isDone (D : C.Coalition) (a b : HashOutput) (s : Step C E G α) :
    (renameStep D a b s).isDone = s.isDone := by cases s <;> rfl

/-- Local advancement commutes with the query renaming, including arbitrary waits and aborts. -/
theorem advance_rename (D : C.Coalition) (a b : HashOutput)
    (p : OracleComp (PartySpec C E G) (Option α)) :
    advance (simulateQ (partyStreamRename D a b) p) =
      renameStep D a b <$> simulateQ (localStreamRename D a b) (advance p) := by
  induction p using OracleComp.inductionOn with
  | pure out => rfl
  | query_bind q k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases q with (q | outbox) | input
    · change advance (liftComp (localStreamRename D a b q) _ >>= _) = _
      rw [advance_liftComp_bind]
      change _ = renameStep D a b <$> simulateQ (localStreamRename D a b)
        (OracleComp.lift (OracleSpec.query q) >>= fun x => advance (k x))
      simp only [simulateQ_bind, simulateQ_spec_query, map_bind, ih, bind_map]
    · simp only [partyStreamRename]
      change pure (Step.wait outbox (fun x => simulateQ (partyStreamRename D a b) (k x))) = _
      rfl
    · simp only [partyStreamRename]
      change pure (Step.call input (fun x => simulateQ (partyStreamRename D a b) (k x))) = _
      rfl

theorem worldStreamRename_free (D : C.Coalition) (a b : HashOutput)
    (p : OracleComp (LocalSpec C) α) :
    simulateQ (worldStreamRename D a b) (free p) = free (simulateQ (localStreamRename D a b) p) := by
  induction p using OracleComp.inductionOn with
  | pure out => simp
  | query_bind q k ih =>
    simp only [free_bind, simulateQ_bind, ih]
    congr 1
    rcases q with u | q | x
    all_goals change simulateQ (worldStreamRename D a b) (OracleComp.lift (OracleSpec.query _)) = _
    all_goals rw [simulateQ_spec_query, simulateQ_spec_query]
    all_goals rfl

theorem worldStreamRename_adversary (D : C.Coalition) (a b : HashOutput)
    (p : OracleComp (LocalSpec C) α) :
    simulateQ (worldStreamRename D a b) (worldRoles.adversary p) = worldRoles.adversary p := by
  induction p using OracleComp.inductionOn with
  | pure out => simp [worldRoles, counted]
  | query_bind q k ih =>
    change simulateQ (worldStreamRename D a b) (worldRoles.adversary (OracleComp.lift (OracleSpec.query q)) >>=
      fun x => worldRoles.adversary (k x)) = _
    rw [simulateQ_bind, adversary_query, simulateQ_spec_query]
    simp only [worldStreamRename, ih]
    simp only [worldRoles, liftComp_bind, counted_bind]
    congr 1
    rcases q with u | q | x <;> rfl

theorem roundLocal_rename (D : C.Coalition) (a b : HashOutput)
    (steps : C.Party → Step C E RealSpec α) (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (fun j => renameStep D a b (steps j)) sent i =
      renameStep D a b <$> simulateQ (localStreamRename D a b) (roundLocal D steps sent i) := by
  unfold roundLocal
  dsimp only
  cases hs : steps i with
  | done out => rfl
  | call input resume => exact input.elim
  | wait out resume =>
    rw [renameStep]
    dsimp only
    split_ifs with hi
    · rfl
    · simp only [renameStep_delivered]
      exact advance_rename D a b _

/-- An entire real-network round transports the renamed honest continuations while leaving the
rushing adversary, its state, and its messages unchanged. -/
theorem stepRound_rename (D : C.Coalition) (a b : HashOutput)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state (fun i => renameStep D a b (steps i)) =
      (fun r => (r.1, (fun i => renameStep D a b (r.2.1 i)), r.2.2)) <$>
        simulateQ (worldStreamRename D a b) (stepRound worldRoles D A noFunctionality state steps) := by
  rw [stepRound_real, stepRound_real]
  simp only [renameStep_outbox, simulateQ_bind, worldStreamRename_adversary, worldStreamRename_free,
    simulateQ_pure, map_bind, map_pure]
  apply bind_congr
  rintro ⟨state',sent⟩
  rw [simulateQ_sequenceFin]
  have hs : Concrete.sequenceFin (roundLocal D (fun i => renameStep D a b (steps i)) sent) =
      (fun row i => renameStep D a b (row i)) <$>
        Concrete.sequenceFin (fun i => simulateQ (localStreamRename D a b) (roundLocal D steps sent i)) := by
    change Concrete.sequenceFin (fun i => roundLocal D (fun j => renameStep D a b (steps j)) sent i) = _
    simp only [roundLocal_rename, map_eq_bind_pure_comp, Function.comp_def, sequenceFin_bind_pure]
  rw [hs]
  simp only [map_eq_bind_pure_comp, free_bind, free_pure, bind_assoc, pure_bind]
  rfl

theorem executeRounds_rename (D : C.Coalition) (a b : HashOutput)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) :
    executeRounds worldRoles D A noFunctionality fuel state (fun i => renameStep D a b (steps i)) =
      simulateQ (worldStreamRename D a b) (executeRounds worldRoles D A noFunctionality fuel state steps) := by
  induction fuel generalizing state steps with
  | zero => simp only [executeRounds, renameStep_output, simulateQ_pure]
  | succ fuel ih =>
    simp only [executeRounds, renameStep_isDone, simulateQ_ite]
    split_ifs
    · simp only [renameStep_output, simulateQ_pure]
    · rw [stepRound_rename, simulateQ_bind]
      simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
      exact bind_congr fun r => ih r.1 r.2.1

theorem startSteps_rename (D : C.Coalition) (a b : HashOutput)
    (program : C.Party → PartyM C E RealSpec α) :
    startSteps worldRoles D (fun i => renameParty D a b (program i)) =
      (fun steps i => renameStep D a b (steps i)) <$>
        simulateQ (worldStreamRename D a b) (startSteps worldRoles D program) := by
  simp only [startSteps, simulateQ_sequenceFin]
  have hl : ∀ i, (if i ∈ D.1 then pure (Step.done none) else
        worldRoles.honest (advance (renameParty D a b (program i)).run)) =
      renameStep D a b <$> simulateQ (worldStreamRename D a b)
        (if i ∈ D.1 then pure (Step.done none) else worldRoles.honest (advance (program i).run)) := by
    intro i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, simulateQ_pure, map_pure, renameStep]
    · simp only [if_neg hi, renameParty, OptionT.run_mk, advance_rename, worldRoles,
        worldStreamRename_free]
      simp only [free, simulateQ_map]
  simp_rw [hl]
  simp only [map_eq_bind_pure_comp, Function.comp_def, sequenceFin_bind_pure]

/-- The complete execution, with arbitrary rushing adversary and arbitrary fuel, commutes with
honest stream renaming. Early abort and fuel exhaustion are retained exactly. -/
theorem executePhase_rename (D : C.Coalition) (a b : HashOutput)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) :
    executePhase worldRoles D A noFunctionality fuel state (fun i => renameParty D a b (program i)) =
      simulateQ (worldStreamRename D a b) (executePhase worldRoles D A noFunctionality fuel state program) := by
  rw [executePhase, executePhase, startSteps_rename, simulateQ_bind]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  exact bind_congr fun steps => executeRounds_rename D a b A fuel state steps

/-- From an empty independent-key cache, the original and renamed honest programs have identical
output distributions, even when the rushing adversary interleaves arbitrary oracle queries. -/
theorem evalDist_lazyKeyPhase_rename (prims : Primitives) (D : C.Coalition) (a b : HashOutput)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) (s : HashCache C) :
    𝒟[(simulateQ (lazyKeyWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state program)).run' (s,∅)] =
      𝒟[(simulateQ (lazyKeyWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state
          (fun i => renameParty D a b (program i)))).run' (s,∅)] := by
  rw [executePhase_rename]
  exact evalDist_lazyKeyWorld_empty_rename prims D a b _ s

theorem evalDist_streamPhase_rename (prims : Primitives) (D : C.Coalition) (a b : HashOutput)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) (s : HashCache C) :
    𝒟[(simulateQ (streamWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state program)).run' (s,∅)] =
      𝒟[(simulateQ (streamWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state
          (fun i => renameParty D a b (program i)))).run' (s,∅)] := by
  rw [executePhase_rename]
  exact evalDist_streamWorld_empty_rename prims D a b _ s

theorem renameParty_runRun (D : C.Coalition) (a b : HashOutput) (p : RunM C E G α) (s : RunState C) :
    renameParty D a b (p.run s) = (renameRun D a b p).run s := rfl

/-- A full concrete MPC batch satisfies the network renaming law, including the adversary state
and the run state returned by each successful honest operator. Aborted or unfinished operators
return `none`; the final oracle caches are discarded. -/
theorem evalDist_lazyKey_realRunJobs_swap [Field E] [Algebra Bit E] (K : Constants C E)
    (prims : Primitives) (D : C.Coalition) (a b : HashOutput)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : C.Party → List (C.Term → List Bit)) (rs : C.Party → RunState C) (s : HashCache C) :
    𝒟[(simulateQ (lazyKeyWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => (runJobs K (realRunGadgets K (ctx i) mode) jobs (inputs i)).run (rs i)))).run' (s,∅)] =
      𝒟[(simulateQ (lazyKeyWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state
          (fun i => (runJobs K (realRunGadgets K (hiddenContextSwap D a b (ctx i)) mode)
            jobs (inputs i)).run (rs i)))).run' (s,∅)] := by
  rw [evalDist_lazyKeyPhase_rename prims D a b A fuel state]
  simp only [renameParty_runRun, renameRun_realRunJobs]

section CeremonyHom
variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]

theorem monadHom_list_mapM (h : m →ᵐ n) (f : α → m β) (xs : List α) :
    h (xs.mapM f) = xs.mapM (fun x => h (f x)) := by
  induction xs with
  | nil => exact h.toFun_pure' _
  | cons x xs ih => simp only [List.mapM_cons, MonadHom.mmap_bind, MonadHom.mmap_pure, ih]

theorem monadHom_batched (h : m →ᵐ n) (size : ℕ) (run : List Job → m (Option (List (List Bit))))
    (jobs : List Job) :
    h (batched size run jobs) = batched size (fun js => h (run js)) jobs := by
  simp only [batched, MonadHom.mmap_bind, MonadHom.mmap_pure, monadHom_list_mapM]

/-- The tree assembly only composes its hash computations and its batch interface. -/
theorem monadHom_ceremonyOutput (h : m →ᵐ n) (lift : ∀ {α : Type}, OracleComp HashSpec α → m α)
    (parameter : PublicParameter) (run : List Job → m (Option (List (List Bit))))
    (top : TopTree) (tree : Tree) :
    h (ceremonyOutput lift parameter run top tree) =
      ceremonyOutput (fun oa => h (lift oa)) parameter (fun js => h (run js)) top tree := by
  cases tree with
  | top =>
    simp only [ceremonyOutput, MonadHom.mmap_bind]
    congr 1
    funext out
    cases out <;> simp only [MonadHom.mmap_pure, MonadHom.mmap_bind]
  | bottom b =>
    simp only [ceremonyOutput, MonadHom.mmap_bind]
    congr 1
    funext out
    cases out with
    | none => exact h.toFun_pure' _
    | some outputs =>
      simp only [MonadHom.mmap_bind]
      congr 1
      funext root
      congr 1
      funext base
      congr 1
      funext result
      cases result with
      | none => exact h.toFun_pure' _
      | some pair =>
        rcases pair with ⟨randomness,encoding⟩
        simp only [MonadHom.mmap_bind]
        congr 1
        funext values
        cases values with
        | none => exact h.toFun_pure' _
        | some vals =>
          simp only [MonadHom.mmap_bind]
          congr 1
          funext path
          congr 1
          funext topRoot
          split <;> exact h.toFun_pure' _

end CeremonyHom

def renamePartyHom (D : C.Coalition) (a b : HashOutput) : PartyM C E G →ᵐ PartyM C E G where
  toFun _ := renameParty D a b
  toFun_pure' := renameParty_pure D a b
  toFun_bind' := renameParty_bind D a b

def renameStateHom (σ : Type) (D : C.Coalition) (a b : HashOutput) :
    StateT σ (PartyM C E G) →ᵐ StateT σ (PartyM C E G) where
  toFun _ p := fun s => renameParty D a b (p.run s)
  toFun_pure' _ := rfl
  toFun_bind' p k := by funext s; exact renameParty_bind D a b _ _

@[local simp] theorem renameStateHom_lift {σ : Type} (D : C.Coalition) (a b : HashOutput)
    (p : PartyM C E G α) :
    renameStateHom σ D a b (StateT.lift p) = StateT.lift (renameParty D a b p) := by
  funext s
  change renameParty D a b (p >>= fun x => pure (x,s)) = _
  rw [renameParty_bind]
  rfl

@[local simp] theorem renameStateHom_get {σ : Type} (D : C.Coalition) (a b : HashOutput) :
    renameStateHom (E := E) (G := G) σ D a b get = get := rfl

@[local simp] theorem renameStateHom_set {σ : Type} (D : C.Coalition) (a b : HashOutput) (s : σ) :
    renameStateHom (E := E) (G := G) σ D a b (set s) = set s := rfl

@[local simp] theorem renameParty_runState {σ : Type} (D : C.Coalition) (a b : HashOutput)
    (p : StateT σ (PartyM C E G) α) (s : σ) :
    renameParty D a b (p.run' s) = (renameStateHom σ D a b p).run' s := by
  simp only [StateT.run'_eq, renameParty_map]
  rfl

theorem roStreamRename_tweakable (D : C.Coalition) (a b : HashOutput) (p : OracleComp HashSpec α) :
    simulateQ (roStreamRename D a b) (tweakable p) = tweakable p := by
  unfold tweakable
  rw [← QueryImpl.simulateQ_compose]
  apply congrArg (fun impl : QueryImpl HashSpec (OracleComp (RoSpec C)) => simulateQ impl p)
  funext q
  exact roStreamRename_hash D a b _

theorem roStreamRename_flatMapM (D : C.Coalition) (a b : HashOutput)
    (f : α → OracleComp (RoSpec C) (List β)) (xs : List α) :
    simulateQ (roStreamRename D a b) (xs.flatMapM f) =
      xs.flatMapM (fun x => simulateQ (roStreamRename D a b) (f x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMapM_cons, simulateQ_bind, simulateQ_pure, ih]

theorem renameParty_inputShares (D : C.Coalition) (a b : HashOutput) (ctx : Context C) (job : Job) :
    renameParty (E := E) (G := G) D a b (inputShares ctx job) =
      inputShares (hiddenContextSwap D a b ctx) job := by
  simp [inputShares, simulateQ_list_mapM, roStreamRename_flatMapM, prf, hiddenContextSwap]

theorem renameParty_list_mapM (D : C.Coalition) (a b : HashOutput)
    (f : α → PartyM C E G β) (xs : List α) :
    renameParty D a b (xs.mapM f) = xs.mapM (fun x => renameParty D a b (f x)) :=
  monadHom_list_mapM (renamePartyHom D a b) f xs

section ActualCeremony
variable [Field E] [Algebra Bit E] (K : Constants C E)

/-- The batch body of `ceremonyWith` specialized to `realRunGadgets`, with its label and batch counter state. -/
def ceremonyBatch (circuits : Circuits) (settings : Settings) (ctx : Context C) (jobs : List Job) :
    StateT (ℕ × ℕ) (PartyM C E G) (Option (List (List Bit))) := do
  let (label,k) ← get
  let inputs ← StateT.lift (jobs.mapM (inputShares ctx))
  let (outputs,state) ← StateT.lift ((runJobs K (realRunGadgets K ctx settings.mode)
    (jobs.map (circuits ctx.keys.parameter ·.kind)) inputs).run ⟨fun _ => [],label,k⟩)
  set (state.label,k+1)
  pure (some outputs)

/-- The exact suffix of the real ceremony after its PRSS setup. -/
def ceremonyAfterSetup (circuits : Circuits) (settings : Settings) (ctx : Context C)
    (top : TopTree) (tree : Tree) : PartyM C E G TreeOutput := do
  let some output ← (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E G))
    (fun oa => StateT.lift (oracleStep (tweakable oa))) ctx.keys.parameter
    (batched settings.batchSize (ceremonyBatch K circuits settings ctx)) top tree).run' (0,0) | failure
  pure output

theorem ceremony_eq_prssSetup_bind (circuits : Circuits) (settings : Settings)
    (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    (ceremony K circuits settings i keys top tree : PartyM C E G TreeOutput) =
      prssSetup i >>= fun prss => ceremonyAfterSetup K circuits settings ⟨i,keys,prss⟩ top tree := rfl

theorem rename_ceremonyBatch (D : C.Coalition) (a b : HashOutput) (circuits : Circuits)
    (settings : Settings) (ctx : Context C) (jobs : List Job) :
    renameStateHom (G := G) (ℕ × ℕ) D a b (ceremonyBatch K circuits settings ctx jobs) =
      ceremonyBatch K circuits settings (hiddenContextSwap D a b ctx) jobs := by
  simp only [ceremonyBatch, MonadHom.mmap_bind, renameStateHom_get, renameStateHom_lift,
    renameParty_list_mapM, renameParty_inputShares, renameParty_runRun, renameRun_realRunJobs,
    renameStateHom_set, MonadHom.mmap_pure]
  rfl

/-- Every batch and the adaptive second run of a bottom tree obey the same hidden-key renaming.
The public tree computation and all dealer keys are retained. -/
theorem rename_ceremonyAfterSetup (D : C.Coalition) (a b : HashOutput) (circuits : Circuits)
    (settings : Settings) (ctx : Context C) (top : TopTree) (tree : Tree) :
    renameParty (G := G) D a b (ceremonyAfterSetup K circuits settings ctx top tree) =
      ceremonyAfterSetup K circuits settings (hiddenContextSwap D a b ctx) top tree := by
  have hbody : renameStateHom (G := G) (ℕ × ℕ) D a b
      (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E G)) (fun oa => StateT.lift (oracleStep (tweakable oa))) ctx.keys.parameter
        (batched settings.batchSize (ceremonyBatch K circuits settings ctx)) top tree) =
      ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E G)) (fun oa => StateT.lift (oracleStep (tweakable oa))) ctx.keys.parameter
        (batched settings.batchSize (ceremonyBatch K circuits settings (hiddenContextSwap D a b ctx))) top tree := by
    simp only [monadHom_ceremonyOutput, renameStateHom_lift, renameParty_oracleStep,
      roStreamRename_tweakable, monadHom_batched, rename_ceremonyBatch]
  unfold ceremonyAfterSetup
  rw [renameParty_bind, renameParty_runState, hbody]
  congr 1
  funext out
  cases out <;> rfl

/-- The actual post-setup ceremony has the same observable law under a simultaneous swap of
hidden PRSS keys in the independently keyed world, from an empty key cache. The contexts and
hash cache are fixed here; this does not assert their setup distribution. -/
theorem evalDist_lazyKey_ceremonyAfterSetup_swap (prims : Primitives) (D : C.Coalition)
    (a b : HashOutput) (circuits : Circuits) (settings : Settings)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (top : TopTree) (tree : Tree) (s : HashCache C) :
    𝒟[(simulateQ (lazyKeyWorld prims D)
      (executePhase worldRoles D A noFunctionality fuel state
        (fun i => ceremonyAfterSetup K circuits settings (ctx i) top tree))).run' (s,∅)] =
      𝒟[(simulateQ (lazyKeyWorld prims D)
        (executePhase worldRoles D A noFunctionality fuel state
          (fun i => ceremonyAfterSetup K circuits settings (hiddenContextSwap D a b (ctx i)) top tree))).run' (s,∅)] := by
  rw [evalDist_lazyKeyPhase_rename prims D a b A fuel state]
  simp only [rename_ceremonyAfterSetup]

/-- The phase identity also holds with a subsequent external observer. The observer retains the
same oracle cache through the bind and may make adaptive counted queries. -/
theorem evalDist_lazyKeyPhase_rename_observe (prims : Primitives) (D : C.Coalition)
    (a b : HashOutput) (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α)
    (observe : A.State × (C.Party → Option α) → OracleComp (LocalSpec C) β) (s : HashCache C) :
    𝒟[(simulateQ (lazyKeyWorld prims D) (do
      let out ← executePhase worldRoles D A noFunctionality fuel state program
      worldRoles.adversary (observe out))).run' (s,∅)] =
      𝒟[(simulateQ (lazyKeyWorld prims D) (do
        let out ← executePhase worldRoles D A noFunctionality fuel state
          (fun i => renameParty D a b (program i))
        worldRoles.adversary (observe out))).run' (s,∅)] := by
  rw [evalDist_lazyKeyWorld_empty_rename prims D a b]
  simp only [simulateQ_bind, worldStreamRename_adversary, ← executePhase_rename]

/-- The exact post-setup ceremony law includes any subsequent local observer in the same world.
This is a fixed-context identity, not a statement of how setup samples those contexts. -/
theorem evalDist_lazyKey_ceremonyAfterSetup_swap_observe (prims : Primitives) (D : C.Coalition)
    (a b : HashOutput) (circuits : Circuits) (settings : Settings)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (ctx : C.Party → Context C) (top : TopTree) (tree : Tree)
    (observe : A.State × (C.Party → Option TreeOutput) → OracleComp (LocalSpec C) β) (s : HashCache C) :
    𝒟[(simulateQ (lazyKeyWorld prims D) (do
      let out ← executePhase worldRoles D A noFunctionality fuel state
        (fun i => ceremonyAfterSetup K circuits settings (ctx i) top tree)
      worldRoles.adversary (observe out))).run' (s,∅)] =
      𝒟[(simulateQ (lazyKeyWorld prims D) (do
        let out ← executePhase worldRoles D A noFunctionality fuel state
          (fun i => ceremonyAfterSetup K circuits settings (hiddenContextSwap D a b (ctx i)) top tree)
        worldRoles.adversary (observe out))).run' (s,∅)] := by
  rw [evalDist_lazyKeyPhase_rename_observe prims D a b A fuel state]
  simp only [rename_ceremonyAfterSetup]

end ActualCeremony
end ThresholdLeanXmssSecurity
end HonestProgramRelabeling

section FullCeremonyRelabeling
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E α : Type} {ι : Type} {G : OracleSpec ι}
attribute [local simp] renameParty_bind renameParty_pure renameParty_failure renameParty_map
  renameParty_localStep renameParty_oracleStep renameParty_exchange renameParty_require
  roStreamRename_hash

/-- The stream renaming fixes all private sampling, not just `sampleParts`. -/
theorem localStreamRename_sampling (D : C.Coalition) (a b : HashOutput) (p : ProbComp α) :
    simulateQ (localStreamRename D a b) (liftComp p (LocalSpec C)) = liftComp p (LocalSpec C) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp
  | query_bind q k ih =>
    simp only [liftComp_bind, simulateQ_bind, ih]
    congr 1

theorem roStreamRename_deriveKeys (D : C.Coalition) (a b : HashOutput) (phase : Phase)
    (i : C.Party) (view : C.Party → Parts C) :
    simulateQ (roStreamRename D a b) (deriveKeys phase i view) = deriveKeys phase i view := by
  simp [deriveKeys, simulateQ_list_mapM]

theorem renameParty_commitRevealEcho (D : C.Coalition) (a b : HashOutput) (phase : Phase)
    (i : C.Party) (own : Parts C) :
    renameParty (E := E) (G := G) D a b (commitRevealEcho phase i own) =
      commitRevealEcho phase i own := by
  simp [commitRevealEcho, simulateQ_list_mapM, roStreamRename_deriveKeys]

/-- Setup itself makes no PRG calls. The raw key values it derives are unchanged by this syntax
transformation; only the subsequent honest consumption of those keys is renamed. -/
theorem renameParty_prssSetup (D : C.Coalition) (a b : HashOutput) (i : C.Party) :
    renameParty (E := E) (G := G) D a b (prssSetup i) = prssSetup i := by
  have hs := localStreamRename_sampling D a b (sampleParts (C := C))
  simp only [liftComp_eq_liftM] at hs
  simp [prssSetup, hs, renameParty_commitRevealEcho]

theorem rename_ceremony [Field E] [Algebra Bit E] (K : Constants C E)
    (D : C.Coalition) (a b : HashOutput) (circuits : Circuits) (settings : Settings)
    (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    renameParty (G := G) D a b (ceremony K circuits settings i keys top tree) =
      prssSetup i >>= fun prss => ceremonyAfterSetup K circuits settings
        (hiddenContextSwap D a b ⟨i,keys,prss⟩) top tree := by
  rw [ceremony_eq_prssSetup_bind, renameParty_bind, renameParty_prssSetup]
  congr 1
  funext prss
  exact rename_ceremonyAfterSetup K D a b circuits settings _ top tree

theorem worldStreamRename_realExecution (D : C.Coalition) (a b : HashOutput)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ)
    (program : C.Party → Keys C → PartyM C E RealSpec α) (x : C.Party → Keys C) (z : Aux) :
    simulateQ (worldStreamRename D a b) (realExecution D A noFunctionality fuel program x z) =
      realExecution D A noFunctionality fuel (fun i keys => renameParty D a b (program i keys)) x z := by
  simp only [realExecution, simulateQ_bind, worldStreamRename_adversary, ← executePhase_rename]

theorem worldStreamRename_distinguish (D : C.Coalition) (a b : HashOutput)
    {σ O : Type} (game : OracleComp (WorldSpec C) (σ × (C.Party → Option O)))
    (Z : Distinguisher C σ O) :
    simulateQ (worldStreamRename D a b) (distinguish game Z) =
      distinguish (simulateQ (worldStreamRename D a b) game) Z := by
  simp only [distinguish, simulateQ_bind, worldStreamRename_adversary]

/-- Full real execution, including setup, adversary start and final distinguisher, is invariant
under renaming the honest consumption of its hidden PRSS keys in the independent-key world.
Setup's raw keys and hash cache are not changed; this is not setup entropy or the original-world hop. -/
theorem evalDist_lazyKey_ceremony_swap [Field E] [Algebra Bit E] (K : Constants C E)
    (prims : Primitives) (D : C.Coalition) (a b : HashOutput) (circuits : Circuits) (settings : Settings)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (top : TopTree) (tree : Tree) (s : HashCache C) :
    𝒟[(simulateQ (lazyKeyWorld prims D)
      (distinguish (realExecution D A noFunctionality (ceremonyFuel circuits settings)
        (fun i keys => ceremony K circuits settings i keys top tree) x z) Z)).run' (s,∅)] =
      𝒟[(simulateQ (lazyKeyWorld prims D)
        (distinguish (realExecution D A noFunctionality (ceremonyFuel circuits settings)
          (fun i keys => prssSetup i >>= fun prss => ceremonyAfterSetup K circuits settings
            (hiddenContextSwap D a b ⟨i,keys,prss⟩) top tree) x z) Z)).run' (s,∅)] := by
  rw [evalDist_lazyKeyWorld_empty_rename prims D a b]
  simp only [worldStreamRename_distinguish, worldStreamRename_realExecution, rename_ceremony]

/-- The same full-game identity in the ideal hidden-stream world. It retains the actual setup
and changes only the subsequent honest PRSS-key consumption. -/
theorem evalDist_stream_ceremony_swap [Field E] [Algebra Bit E] (K : Constants C E)
    (prims : Primitives) (D : C.Coalition) (a b : HashOutput) (circuits : Circuits) (settings : Settings)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (top : TopTree) (tree : Tree) (s : HashCache C) :
    𝒟[(simulateQ (streamWorld prims D)
      (distinguish (realExecution D A noFunctionality (ceremonyFuel circuits settings)
        (fun i keys => ceremony K circuits settings i keys top tree) x z) Z)).run' (s,∅)] =
      𝒟[(simulateQ (streamWorld prims D)
        (distinguish (realExecution D A noFunctionality (ceremonyFuel circuits settings)
          (fun i keys => prssSetup i >>= fun prss => ceremonyAfterSetup K circuits settings
            (hiddenContextSwap D a b ⟨i,keys,prss⟩) top tree) x z) Z)).run' (s,∅)] := by
  rw [evalDist_streamWorld_empty_rename prims D a b]
  simp only [worldStreamRename_distinguish, worldStreamRename_realExecution, rename_ceremony]

end ThresholdLeanXmssSecurity
end FullCeremonyRelabeling

/-! ## Adaptive setup prequeries -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

abbrev PrssFiniteSpec (Ω : Type) := unifSpec + (Ω →ₒ HashOutput)

def prssFiniteEager {Ω : Type} [DecidableEq Ω] (h : Ω → HashOutput) :
    QueryImpl (PrssFiniteSpec Ω) (StateT (KeygenFiniteCache Ω) ProbComp) :=
  unifFwdImpl (Ω →ₒ HashOutput) + QueryImpl.withCaching (fun q => pure (h q) : QueryImpl (Ω →ₒ HashOutput) ProbComp)

def prssFiniteLazy {Ω : Type} [DecidableEq Ω] :
    QueryImpl (PrssFiniteSpec Ω) (StateT (KeygenFiniteCache Ω) ProbComp) :=
  unifFwdImpl (Ω →ₒ HashOutput) + (Ω →ₒ HashOutput).randomOracle

/-- Once a cell is cached, its unused eager-table value cannot affect any future computation,
including private sampling. -/
theorem prssFiniteEager_congr {Ω α : Type} [DecidableEq Ω]
    (oa : OracleComp (PrssFiniteSpec Ω) α) (h g : Ω → HashOutput) :
    ∀ cache : KeygenFiniteCache Ω, (∀ q, cache q = none → h q = g q) →
      (simulateQ (prssFiniteEager h) oa).run cache =
        (simulateQ (prssFiniteEager g) oa).run cache := by
  induction oa using OracleComp.inductionOn with
  | pure a => intros; rfl
  | query_bind t k ih =>
    intro cache he
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with n | q
    · change (((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        fun p : unifSpec.Range n × KeygenFiniteCache Ω => (simulateQ (prssFiniteEager h) (k p.1)).run p.2) =
        (((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        fun p : unifSpec.Range n × KeygenFiniteCache Ω => (simulateQ (prssFiniteEager g) (k p.1)).run p.2)
      simp only [bind_map_left]
      exact bind_congr fun y => ih y cache he
    · change (QueryImpl.withCaching (fun q => pure (h q) : QueryImpl (Ω →ₒ HashOutput) ProbComp) q).run cache >>= _ =
        (QueryImpl.withCaching (fun q => pure (g q) : QueryImpl (Ω →ₒ HashOutput) ProbComp) q).run cache >>= _
      cases hc : cache q with
      | none =>
        rw [QueryImpl.withCaching_run_none _ hc, QueryImpl.withCaching_run_none _ hc]
        simp only [map_pure, pure_bind, he q hc]
        apply ih
        intro q' hq'
        by_cases hn : q' = q
        · subst q'; simp at hq'
        · exact he q' (by simpa [QueryCache.cacheQuery, hn] using hq')
      | some y =>
        rw [QueryImpl.withCaching_run_some _ hc, QueryImpl.withCaching_run_some _ hc, pure_bind, pure_bind]
        exact ih y cache he

/-- Finite lazy and eager hash oracles have the same joint result/cache distribution. -/
theorem evalDist_prssFiniteEager {Ω α : Type} [Finite Ω] [DecidableEq Ω]
    [SampleableType (Ω → HashOutput)] (oa : OracleComp (PrssFiniteSpec Ω) α) :
    ∀ cache : KeygenFiniteCache Ω,
      𝒟[(simulateQ prssFiniteLazy oa).run cache] =
        𝒟[do let h ← $ᵗ (Ω → HashOutput); (simulateQ (prssFiniteEager h) oa).run cache] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro cache; apply evalDist_ext; intro x; simp
  | query_bind t k ih =>
    intro cache
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with n | q
    · change 𝒟[((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        fun p : unifSpec.Range n × KeygenFiniteCache Ω => (simulateQ prssFiniteLazy (k p.1)).run p.2] =
        𝒟[do let h ← $ᵗ (Ω → HashOutput);
              ((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
                fun p : unifSpec.Range n × KeygenFiniteCache Ω => (simulateQ (prssFiniteEager h) (k p.1)).run p.2]
      simp only [bind_map_left]
      conv_lhs => rw [evalDist_bind]; arg 2; ext y; rw [ih y cache]
      rw [← evalDist_bind]
      exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    · change 𝒟[((Ω →ₒ HashOutput).randomOracle q).run cache >>= _] =
        𝒟[do let h ← $ᵗ (Ω → HashOutput);
              (QueryImpl.withCaching (fun q => pure (h q) : QueryImpl (Ω →ₒ HashOutput) ProbComp) q).run cache >>= _]
      cases hc : cache q with
      | some y =>
        simp only [randomOracle, QueryImpl.withCaching_run_some _ hc, pure_bind]
        exact ih y cache
      | none =>
        simp only [randomOracle, QueryImpl.withCaching_run_none _ hc, bind_map_left, map_pure, pure_bind]
        change 𝒟[($ᵗ HashOutput) >>= fun y => (simulateQ prssFiniteLazy (k y)).run (cache.cacheQuery q y)] = _
        conv_lhs => rw [evalDist_bind]; arg 2; ext y; rw [ih y (cache.cacheQuery q y)]
        rw [← evalDist_bind]
        let cont := fun h : Ω → HashOutput =>
          (simulateQ (prssFiniteEager h) (k (h q))).run (cache.cacheQuery q (h q))
        have he (y : HashOutput) (h : Ω → HashOutput) :
            (simulateQ (prssFiniteEager h) (k y)).run (cache.cacheQuery q y) =
              cont (Function.update h q y) := by
          dsimp only [cont]
          rw [Function.update_self]
          apply prssFiniteEager_congr
          intro q' hq'
          by_cases hn : q' = q
          · subst q'; simp at hq'
          · simp [Function.update_of_ne hn]
        simp_rw [he, Function.update_eq_self]
        exact keygenUniform_update_bind q cont

variable {C : Committee}

/-- Underlying hash calls of a local query, including the internal hash of a PRG call. -/
def prssLocalHashInputs : (LocalSpec C).Domain → Finset (Query C)
  | .inl _ => ∅
  | .inr (.inl q) => {q}
  | .inr (.inr x) => {.streamKey x.2.1}

theorem prssHashAnswer_fixed (prims : Primitives) {input : HashInput} (h : MpcInput input) :
    hashAnswer (C := C) prims (.hash input) = pure (prims.Th input) := by
  simp [hashAnswer, h]

theorem prssHashAnswer_not_fixed (prims : Primitives) {q : Query C} (h : ¬ IsFixed q) :
    hashAnswer prims q = (Query C →ₒ HashOutput).randomOracle q := by
  cases q with
  | hash input =>
    have : ¬ MpcInput input := fun hm => h ⟨input, rfl, hm⟩
    simp [hashAnswer, this]
  | _ => rfl

/-- Syntactic coverage of every possible branch by a finite hash-input domain. -/
inductive PrssLocalCovered (S : Finset (Query C)) {α : Type} : OracleComp (LocalSpec C) α → Prop
  | pure (a : α) : PrssLocalCovered S (pure a)
  | query_bind (t : (LocalSpec C).Domain) (k : (LocalSpec C).Range t → OracleComp (LocalSpec C) α)
      (ht : prssLocalHashInputs t ⊆ S) (hk : ∀ y, PrssLocalCovered S (k y)) :
      PrssLocalCovered S (OracleComp.lift (OracleSpec.query t) >>= k)

theorem PrssLocalCovered.mono {S T : Finset (Query C)} {α : Type}
    {oa : OracleComp (LocalSpec C) α} (h : PrssLocalCovered S oa) (hst : S ⊆ T) :
    PrssLocalCovered T oa := by
  induction h with
  | pure a => exact .pure a
  | query_bind t k ht hk ih => exact .query_bind t k (ht.trans hst) ih

/-- Finite answer ranges give a finite envelope even for an arbitrarily adaptive local program. -/
theorem prssLocalCovered_exists {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∃ S : Finset (Query C), PrssLocalCovered S oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact ⟨∅, .pure a⟩
  | query_bind t k ih =>
    have hi : Finite ((LocalSpec C).Range t) := by
      rcases t with n | q | x <;> infer_instance
    letI := Fintype.ofFinite ((LocalSpec C).Range t)
    choose S hS using ih
    refine ⟨prssLocalHashInputs t ∪ Finset.univ.biUnion S, .query_bind t k ?_ ?_⟩
    · exact Finset.subset_union_left
    · intro y
      apply (hS y).mono
      intro q hq
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ _, hq⟩)

/-- Translation to a finite domain keeps fixed `Th` calls deterministic. -/
def prssFiniteHash (prims : Primitives) (S : Finset (Query C)) (q : Query C) :
    OracleComp (PrssFiniteSpec S) HashOutput :=
  match q with
  | .hash input => if MpcInput input then pure (prims.Th input) else
      if hq : q ∈ S then OracleComp.lift ((PrssFiniteSpec S).query (.inr ⟨q, hq⟩)) else pure 0
  | _ => if hq : q ∈ S then OracleComp.lift ((PrssFiniteSpec S).query (.inr ⟨q, hq⟩)) else pure 0

def prssFiniteLocal (prims : Primitives) (S : Finset (Query C)) :
    QueryImpl (LocalSpec C) (OracleComp (PrssFiniteSpec S)) :=
  (fun n : ℕ => OracleComp.lift ((PrssFiniteSpec S).query (.inl n)) : QueryImpl unifSpec (OracleComp (PrssFiniteSpec S))) +
    (prssFiniteHash prims S + fun x : PrgInput C => do
      let y ← prssFiniteHash prims S (.streamKey x.2.1)
      pure (prims.aes.eval (truncateHash y) x.2.2))

/-- A hash call's exact joint answer/cache law survives restriction to its finite domain. -/
theorem prssFiniteHash_run (prims : Primitives) (S : Finset (Query C))
    (q : Query C) (hq : q ∈ S) (cache : HashCache C) :
    (fun r : HashOutput × HashCache C => (r.1, keygenRestrictCache S r.2)) <$>
        (hashAnswer prims q).run cache =
      (simulateQ prssFiniteLazy (prssFiniteHash prims S q)).run (keygenRestrictCache S cache) := by
  by_cases hf : IsFixed q
  · obtain ⟨input, rfl, hi⟩ := hf
    rw [prssHashAnswer_fixed prims hi]
    simp [prssFiniteHash, hi, keygenRestrictCache]
  · have ht : prssFiniteHash prims S q = OracleComp.lift ((PrssFiniteSpec S).query (.inr ⟨q, hq⟩)) := by
      cases q <;> simp_all [prssFiniteHash, IsFixed]
    rw [ht, prssHashAnswer_not_fixed prims hf]
    erw [simulateQ_spec_query]
    change _ <$> ((Query C →ₒ HashOutput).randomOracle q).run cache =
      ((S →ₒ HashOutput).randomOracle ⟨q, hq⟩).run (keygenRestrictCache S cache)
    cases hc : cache q with
    | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc,
        QueryImpl.withCaching_run_none _ (show keygenRestrictCache S cache ⟨q, hq⟩ = none from hc)]
      simp only [Functor.map_map, keygenRestrictCache_update S cache q hq]
      rfl
    | some y =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hc,
        QueryImpl.withCaching_run_some _ (show keygenRestrictCache S cache ⟨q, hq⟩ = some y from hc)]
      rfl

/-- The finite translation also preserves private sampling and internal PRG hashes. -/
theorem prssFiniteLocal_run (prims : Primitives) (S : Finset (Query C))
    (t : (LocalSpec C).Domain) (ht : prssLocalHashInputs t ⊆ S) (cache : HashCache C) :
    (fun r : (LocalSpec C).Range t × HashCache C => (r.1, keygenRestrictCache S r.2)) <$>
        (localAnswer prims t).run cache =
      (simulateQ prssFiniteLazy (prssFiniteLocal prims S t)).run (keygenRestrictCache S cache) := by
  rcases t with n | q | x
  · change _ <$> (fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _) = _
    simp only [Functor.map_map]
    rfl
  · exact prssFiniteHash_run prims S q (ht (by simp [prssLocalHashInputs])) cache
  · change _ <$> (prgAnswer prims x).run cache =
      (simulateQ prssFiniteLazy (prssFiniteHash prims S (.streamKey x.2.1) >>=
        fun y => pure (prims.aes.eval (truncateHash y) x.2.2))).run _
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, map_bind, map_pure,
      simulateQ_bind, simulateQ_pure]
    rw [← prssFiniteHash_run prims S (.streamKey x.2.1)
      (ht (by simp [prssLocalHashInputs])) cache, bind_map_left]
    rfl

/-- The finite translation preserves complete executions, not just individual oracle calls. -/
theorem prssFiniteLocal_simulate_run (prims : Primitives) (S : Finset (Query C))
    {α : Type} (oa : OracleComp (LocalSpec C) α) (hc : PrssLocalCovered S oa) :
    ∀ cache : HashCache C,
      (fun r : α × HashCache C => (r.1, keygenRestrictCache S r.2)) <$>
          (simulateQ (localAnswer prims) oa).run cache =
        (simulateQ prssFiniteLazy (simulateQ (prssFiniteLocal prims S) oa)).run
          (keygenRestrictCache S cache) := by
  induction hc with
  | pure a => intro cache; rfl
  | query_bind t k ht hk ih =>
    intro cache
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← prssFiniteLocal_run prims S t ht cache, bind_map_left]
    exact bind_congr fun p => ih p.1 p.2

/-- Full lazy-to-eager conversion for a local oracle, from every initial cache. -/
theorem evalDist_prssLocal_eager (prims : Primitives) (S : Finset (Query C))
    {α : Type} (oa : OracleComp (LocalSpec C) α) (hc : PrssLocalCovered S oa)
    (cache : HashCache C) :
    𝒟[(simulateQ (localAnswer prims) oa).run' cache] =
      𝒟[do let h ← $ᵗ (S → HashOutput);
            (simulateQ (prssFiniteEager h) (simulateQ (prssFiniteLocal prims S) oa)).run'
              (keygenRestrictCache S cache)] := by
  have he := congrArg (Functor.map Prod.fst) (prssFiniteLocal_simulate_run prims S oa hc cache)
  simp only [Functor.map_map] at he
  change (simulateQ (localAnswer prims) oa).run' cache =
    (simulateQ prssFiniteLazy (simulateQ (prssFiniteLocal prims S) oa)).run'
      (keygenRestrictCache S cache) at he
  rw [he, StateT.run'_eq, evalDist_map, evalDist_prssFiniteEager]
  simp only [StateT.run'_eq]
  rw [← evalDist_map, map_bind]

/-- Every complete local program has a finite eager representation. This applies without any
query-budget or freshness hypothesis to a local computation. -/
theorem prssLocal_eager_exists (prims : Primitives) {α : Type}
    (oa : OracleComp (LocalSpec C) α) :
    ∃ S : Finset (Query C), ∀ cache : HashCache C,
      𝒟[(simulateQ (localAnswer prims) oa).run' cache] =
        𝒟[do let h ← $ᵗ (S → HashOutput);
              (simulateQ (prssFiniteEager h) (simulateQ (prssFiniteLocal prims S) oa)).run'
                (keygenRestrictCache S cache)] := by
  obtain ⟨S, hS⟩ := prssLocalCovered_exists oa
  exact ⟨S, evalDist_prssLocal_eager prims S oa hS⟩

/-- The eager finite oracle without its redundant occupancy cache. -/
def prssFiniteAt {Ω : Type} (h : Ω → HashOutput) : QueryImpl (PrssFiniteSpec Ω) ProbComp :=
  fun | .inl n => OracleComp.lift (query (spec := unifSpec) n)
      | .inr q => pure (h q)

/-- A cache consistent with a fixed table does not affect any returned value, even in an
adaptive computation. No programming occurs in the local oracle. -/
theorem prssFiniteEager_run'_eq {Ω α : Type} [DecidableEq Ω]
    (h : Ω → HashOutput) (oa : OracleComp (PrssFiniteSpec Ω) α) :
    ∀ cache : KeygenFiniteCache Ω, (∀ q y, cache q = some y → y = h q) →
      (simulateQ (prssFiniteEager h) oa).run' cache = simulateQ (prssFiniteAt h) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => intros; rfl
  | query_bind t k ih =>
    intro cache hc
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    rcases t with n | q
    · change (((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        fun p : unifSpec.Range n × KeygenFiniteCache Ω =>
          (simulateQ (prssFiniteEager h) (k p.1)).run' p.2) =
        ((query (spec := unifSpec) n : ProbComp _) >>= fun y => simulateQ (prssFiniteAt h) (k y))
      rw [bind_map_left]
      exact bind_congr fun y => ih y cache hc
    · change ((QueryImpl.withCaching (fun q => pure (h q) : QueryImpl (Ω →ₒ HashOutput) ProbComp) q).run cache >>=
        fun p => (simulateQ (prssFiniteEager h) (k p.1)).run' p.2) =
        (pure (h q) >>= fun y => simulateQ (prssFiniteAt h) (k y))
      cases he : cache q with
      | none =>
        rw [QueryImpl.withCaching_run_none _ he]
        simp only [map_pure, pure_bind]
        apply ih
        intro q' y hy
        by_cases hh : q' = q
        · subst q'
          simpa using hy.symm
        · exact hc q' y (by simpa [QueryCache.cacheQuery, hh] using hy)
      | some y =>
        rw [QueryImpl.withCaching_run_some _ he]
        simp only [pure_bind, hc q y he]
        exact ih (h q) cache hc

/-- Extend the finite random table outside the covered domain with zero. -/
def prssExtend (S : Finset (Query C)) (h : S → HashOutput) (q : Query C) : HashOutput :=
  if hq : q ∈ S then h ⟨q, hq⟩ else 0

/-- The total hash function with the fixed MPC domain kept intact. -/
def prssHashAt (prims : Primitives) (h : Query C → HashOutput) : Query C → HashOutput
  | .hash input => if MpcInput input then prims.Th input else h (.hash input)
  | q => h q

def prssLocalAt (prims : Primitives) (h : Query C → HashOutput) : QueryImpl (LocalSpec C) ProbComp :=
  fun | .inl n => OracleComp.lift (query (spec := unifSpec) n)
      | .inr (.inl q) => pure (prssHashAt prims h q)
      | .inr (.inr x) => pure (prims.aes.eval (truncateHash (h (.streamKey x.2.1))) x.2.2)

theorem prssFiniteHash_at (prims : Primitives) (S : Finset (Query C)) (h : S → HashOutput)
    (q : Query C) :
    simulateQ (prssFiniteAt h) (prssFiniteHash prims S q) =
      pure (prssHashAt prims (prssExtend S h) q) := by
  cases q <;> simp [prssFiniteHash, prssHashAt, prssExtend, prssFiniteAt] <;> split_ifs <;> rfl

theorem prssFiniteLocal_at (prims : Primitives) (S : Finset (Query C)) (h : S → HashOutput)
    (t : (LocalSpec C).Domain) :
    simulateQ (prssFiniteAt h) (prssFiniteLocal prims S t) =
      prssLocalAt prims (prssExtend S h) t := by
  rcases t with n | q | x
  · rfl
  · exact prssFiniteHash_at prims S h q
  · change simulateQ (prssFiniteAt h) (prssFiniteHash prims S (.streamKey x.2.1) >>=
      fun y => pure (prims.aes.eval (truncateHash y) x.2.2)) = _
    rw [simulateQ_bind, prssFiniteHash_at]
    rfl

theorem prssFiniteLocal_at_simulate (prims : Primitives) (S : Finset (Query C))
    (h : S → HashOutput) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (prssFiniteAt h) (simulateQ (prssFiniteLocal prims S) oa) =
      simulateQ (prssLocalAt prims (prssExtend S h)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, prssFiniteLocal_at]
    exact bind_congr ih

/-- Finite eager conversion with the entire cache removed, valid from the empty cache. The
honest private cache footprint therefore need not be assumed independent of sampled parts. -/
theorem evalDist_prssLocal_at (prims : Primitives) (S : Finset (Query C))
    {α : Type} (oa : OracleComp (LocalSpec C) α) (hc : PrssLocalCovered S oa) :
    𝒟[(simulateQ (localAnswer prims) oa).run' ∅] =
      𝒟[do let h ← $ᵗ (S → HashOutput); simulateQ (prssLocalAt prims (prssExtend S h)) oa] := by
  rw [evalDist_prssLocal_eager prims S oa hc ∅]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro h
  rw [prssFiniteEager_run'_eq h _ _ (by intro q y he; cases he), prssFiniteLocal_at_simulate]

end ThresholdLeanXmssSecurity
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E α : Type}

/-- A party remains active after the first exchange exactly when no corrupt sender aborts.
Every honest commitment message is a hash list or the prescribed missing self message. -/
def prssCommitActive (D : C.Coalition) (sent : C.Party → Mail C E) (i : C.Party) : Prop :=
  (C.parties.any fun j => if j ∈ D.1 then Msg.isAbort (sent j i) else false) = false

theorem prssCommitInbox_active (D : C.Coalition) (data : C.Party → Parts C × List HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) :
    ((C.parties.any fun j => Msg.isAbort (prssCommitInbox D data sent i j)) = false) =
      prssCommitActive D sent i := by
  unfold prssCommitActive
  congr 2
  funext j
  by_cases hj : j ∈ D.1
  · simp [prssCommitInbox, hj]
  · simp only [prssCommitInbox, if_neg hj, commitOutbox]
    split <;> rfl

/-- The deterministic commitment data for a specified hash function. Corrupt rows are ignored by
both visible-message functions, so their dummy entries need not be represented here. -/
def prssDataAt (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    C.Party → Parts C × List HashOutput := fun i =>
  (parts i, C.parties.map fun j => h (.commit .prss i j (revealTo .prss (parts i) i j)))

theorem prssDataAt_commit (h : Query C → HashOutput) (parts : C.Party → Parts C) (i j : C.Party) :
    ((prssDataAt h parts i).2).getD j.val 0 = h (.commit .prss i j (revealTo .prss (parts i) i j)) := by
  simp [prssDataAt, Committee.parties, List.getD_eq_getElem?_getD]

/-- Equality of reveals to corrupt receivers suffices for the complete first-round visible view. -/
theorem prssCommitVisible_at_congr (D : C.Coalition) (h : Query C → HashOutput)
    (parts parts' : C.Party → Parts C)
    (hv : ∀ i c, i ∉ D.1 → c ∈ D.1 → revealTo .prss (parts i) i c = revealTo .prss (parts' i) i c) :
    prssCommitVisible (E := E) D (prssDataAt h parts) = prssCommitVisible D (prssDataAt h parts') := by
  funext c i
  unfold prssCommitVisible
  by_cases hc : c ∈ D.1 ∧ i ∉ D.1
  · simp only [if_pos hc, commitOutbox, prssDataAt_commit, hv i c hc.2 hc.1]
  · simp only [if_neg hc]

theorem prssRevealVisible_congr (D : C.Coalition) (active : C.Party → Prop)
    (parts parts' : C.Party → Parts C)
    (hv : ∀ i c, i ∉ D.1 → c ∈ D.1 → revealTo .prss (parts i) i c = revealTo .prss (parts' i) i c) :
    prssRevealVisible (E := E) D active parts = prssRevealVisible D active parts' := by
  funext c i
  unfold prssRevealVisible
  by_cases hc : c ∈ D.1 ∧ i ∉ D.1
  · simp only [if_pos hc, prssRevealOutbox, hv i c hc.2 hc.1]
  · simp only [if_neg hc]

/-- Exactly the first two adversarial round calls from the setup prefix, including its early
all-abort branch. Hash answers used for honest commitments are supplied by `h`. Adversarial
oracle calls remain in the program and can be interpreted or logged without changing this syntax. -/
def prssEarlyRounds (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) := do
  let (state',sent) ← A.round state (prssCommitVisible D (prssDataAt h parts))
  if ∀ i, i ∉ D.1 → ¬ prssCommitActive D sent i then return (state',sent,none)
  let (state'',sent') ← A.round state' (prssRevealVisible D (prssCommitActive D sent) parts)
  pure (state'',sent,some sent')

/-- Adaptive oracle queries and malicious messages are equal as programs when the initial public
reveals agree. In particular, the equality does not assume an honest adversary. -/
theorem prssEarlyRounds_congr (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (h : Query C → HashOutput) (parts parts' : C.Party → Parts C)
    (hv : ∀ i c, i ∉ D.1 → c ∈ D.1 → revealTo .prss (parts i) i c = revealTo .prss (parts' i) i c) :
    prssEarlyRounds D A state h parts = prssEarlyRounds D A state h parts' := by
  unfold prssEarlyRounds
  rw [prssCommitVisible_at_congr D h parts parts' hv]
  congr 1
  funext r
  rcases r with ⟨state',sent⟩
  dsimp only
  rw [prssRevealVisible_congr D _ parts parts' hv]

theorem prssEarlyRounds_hiddenTerm (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (i : C.Party) (T : C.Term) (hT : Hidden D (.term T)) (u : HashOutput) :
    prssEarlyRounds D A state h
      (Function.update parts i {(parts i) with term := Function.update (parts i).term T u}) =
      prssEarlyRounds D A state h parts := by
  apply prssEarlyRounds_congr
  intro j c hj hc
  by_cases he : j = i
  · subst j
    simp only [Function.update_self]
    exact revealTo_prss_hidden_term D (parts i) i c hc T hT u
  · simp only [Function.update_of_ne he]

theorem prssEarlyRounds_hiddenPair (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (i j : C.Party) (hj : j ∉ D.1) (u : HashOutput) :
    prssEarlyRounds D A state h
      (Function.update parts i {(parts i) with pair := Function.update (parts i).pair j u}) =
      prssEarlyRounds D A state h parts := by
  apply prssEarlyRounds_congr
  intro k c hk hc
  by_cases he : k = i
  · subst k
    simp only [Function.update_self]
    exact revealTo_prss_hidden_pair D (parts i) i c j hc hj u
  · simp only [Function.update_of_ne he]

/-- An arbitrary interpretation and bounded query search of the first two adaptive rounds cannot
guess a hidden term contribution. The interpreter is fixed independently of that contribution. -/
theorem prob_prssEarlyRounds_hiddenTerm_le (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (i : C.Party)
    (T : C.Term) (hT : Hidden D (.term T))
    (search : OracleComp (LocalSpec C)
      (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) → ProbComp (Finset HashOutput))
    (q : ℕ) (hq : ∀ oa candidates, candidates ∈ support (search oa) → candidates.card ≤ q) :
    Pr[= true | (sampleParts : ProbComp (Parts C)) >>= fun p =>
      search (prssEarlyRounds D A state h (Function.update parts i p)) >>= fun candidates =>
        pure (decide (p.term T ∈ candidates))] ≤ (q : ℝ≥0∞) / 2 ^ 256 := by
  apply prob_sampleParts_hiddenTerm_guess_le T _ _ search q hq
  intro p u
  simpa only [Function.update_self, Function.update_idem] using
    prssEarlyRounds_hiddenTerm D A state h (Function.update parts i p) i T hT u

theorem prob_prssEarlyRounds_hiddenPair_le (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (i j : C.Party) (hj : j ∉ D.1)
    (search : OracleComp (LocalSpec C)
      (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) → ProbComp (Finset HashOutput))
    (q : ℕ) (hq : ∀ oa candidates, candidates ∈ support (search oa) → candidates.card ≤ q) :
    Pr[= true | (sampleParts : ProbComp (Parts C)) >>= fun p =>
      search (prssEarlyRounds D A state h (Function.update parts i p)) >>= fun candidates =>
        pure (decide (p.pair j ∈ candidates))] ≤ (q : ℝ≥0∞) / 2 ^ 256 := by
  apply prob_sampleParts_hiddenPair_guess_le j _ _ search q hq
  intro p u
  simpa only [Function.update_self, Function.update_idem] using
    prssEarlyRounds_hiddenPair D A state h (Function.update parts i p) i j hj u

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E α : Type}

/-- The adversary's first two setup round calls on the actual sampled commitment data. -/
def prssEarlyDataRounds (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (data : C.Party → Parts C × List HashOutput) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) := do
  let (state',sent) ← A.round state (prssCommitVisible D data)
  if ∀ i, i ∉ D.1 → ¬ prssCommitActive D sent i then return (state',sent,none)
  let (state'',sent') ← A.round state'
    (prssRevealVisible D (prssCommitActive D sent) (fun i => (data i).1))
  pure (state'',sent,some sent')

theorem prssEarlyDataRounds_at (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    prssEarlyDataRounds D A state (prssDataAt h parts) = prssEarlyRounds D A state h parts := rfl

def prssSampleParts (D : C.Coalition) : ProbComp (C.Party → Parts C) :=
  Concrete.sequenceFin fun i => if i ∈ D.1 then pure ⟨0, fun _ => 0, fun _ => 0⟩ else sampleParts

def prssDataMask (D : C.Coalition) (data : C.Party → Parts C × List HashOutput) :
    C.Party → Parts C × List HashOutput :=
  fun i => if i ∈ D.1 then (⟨0, fun _ => 0, fun _ => 0⟩, []) else data i

theorem prssEarlyDataRounds_mask (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (data : C.Party → Parts C × List HashOutput) :
    prssEarlyDataRounds D A state (prssDataMask D data) = prssEarlyDataRounds D A state data := by
  have hc : prssCommitVisible (E := E) D (prssDataMask D data) = prssCommitVisible D data := by
    funext c i
    unfold prssCommitVisible
    by_cases he : c ∈ D.1 ∧ i ∉ D.1
    · simp [he, prssDataMask]
    · simp only [if_neg he]
  have hr (active : C.Party → Prop) :
      prssRevealVisible (E := E) D active (fun i => (prssDataMask D data i).1) =
        prssRevealVisible D active (fun i => (data i).1) := by
    funext c i
    unfold prssRevealVisible
    by_cases he : c ∈ D.1 ∧ i ∉ D.1
    · simp [he, prssDataMask]
    · simp only [if_neg he]
  unfold prssEarlyDataRounds
  rw [hc]
  congr 1
  funext r
  rcases r with ⟨state',sent⟩
  dsimp only
  rw [hr]

theorem simulateQ_prssLocalAt_sampling (prims : Primitives) (h : Query C → HashOutput)
    (oa : ProbComp α) : simulateQ (prssLocalAt prims h) (liftComp oa (LocalSpec C)) = oa := by
  let ro : QueryImpl (RoSpec C) ProbComp := fun
    | .inl q => pure (prssHashAt prims h q)
    | .inr x => pure (prims.aes.eval (truncateHash (h (.streamKey x.2.1))) x.2.2)
  have he : prssLocalAt prims h = QueryImpl.id' unifSpec + ro := by
    funext t
    rcases t with n | q | x <;> rfl
  rw [he, QueryImpl.simulateQ_add_liftComp_left, simulateQ_id']

theorem simulateQ_prssLocalAt_hash (prims : Primitives) (h : Query C → HashOutput) (q : Query C) :
    simulateQ (prssLocalAt prims h) (liftComp (hashQuery q) (LocalSpec C)) =
      pure (prssHashAt prims h q) := rfl

theorem simulateQ_prssLocalAt_hashes (prims : Primitives) (h : Query C → HashOutput)
    (qs : List (Query C)) :
    simulateQ (prssLocalAt prims h) (liftComp (qs.mapM hashQuery) (LocalSpec C)) =
      pure (qs.map (prssHashAt prims h)) := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [List.mapM_cons, liftComp_bind, simulateQ_bind, simulateQ_prssLocalAt_hash, pure_bind]
    simp only [liftComp_pure, simulateQ_pure, ih]
    rfl

theorem prssInitialData_at (prims : Primitives) (D : C.Coalition) (h : Query C → HashOutput) :
    simulateQ (prssLocalAt prims h) (prssInitialData D) =
      (prssSampleParts D >>= fun parts => pure (prssDataMask D (prssDataAt h parts))) := by
  rw [prssInitialData, simulateQ_sequenceFin]
  trans Concrete.sequenceFin (fun i =>
    (if i ∈ D.1 then pure ⟨0, fun _ => 0, fun _ => 0⟩ else (sampleParts : ProbComp (Parts C))) >>=
      fun own => pure (if i ∈ D.1 then (⟨0, fun _ => 0, fun _ => 0⟩, []) else
        (own, C.parties.map fun j => h (.commit .prss i j (revealTo .prss own i j)))))
  · congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp [hi]
    · simp only [if_neg hi, simulateQ_bind, simulateQ_pure, simulateQ_prssLocalAt_sampling]
      apply bind_congr
      intro own
      have he : (C.parties.mapM fun j => hashQuery (.commit .prss i j (revealTo .prss own i j))) =
          (C.parties.map fun j => Query.commit .prss i j (revealTo .prss own i j)).mapM hashQuery := by
        rw [List.mapM_map]
        rfl
      rw [he, simulateQ_prssLocalAt_hashes]
      simp [prssHashAt]
  · rw [sequenceFin_bind_pure]
    rfl

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {E α β : Type}

/-- Factor the exact real setup prefix through its two adversarial calls. Both oracle copies
remain in their original positions, and the remaining reveal work still uses the shared world. -/
theorem executePhase_prssSetup_early (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (fuel : ℕ)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec β) :
    executePhase worldRoles D A noFunctionality (fuel + 2) state
      (fun i => prssSetup i >>= k i) = (do
      let data ← free (prssInitialData D)
      let (state', sent, revealed) ← worldRoles.adversary (prssEarlyDataRounds D A state data)
      match revealed with
      | none => pure (state', fun _ => none)
      | some sent' => do
        let rows ← free (prssRevealRows D (prssCommitActive D sent)
          (fun i => (data i).1) (prssCommitInbox D data sent) sent')
        executeRounds worldRoles D A noFunctionality fuel state'
          (fun i => suspendStep (k i) (prssFinishStep i (rows i)))) := by
  rw [executePhase_prssSetup_bind_prefix]
  simp only [prssCommitInbox_active]
  apply bind_congr
  intro data
  simp only [prssEarlyDataRounds, worldRoles, counted, liftComp_bind, liftComp_pure,
    simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨state',sent⟩
  dsimp only
  split_ifs <;> simp only [liftComp_bind, liftComp_pure, simulateQ_bind, simulateQ_pure,
    pure_bind, bind_assoc]

/-- The actual local setup prefix, including arbitrary earlier adversarial oracle work. -/
def prssEarlyObserve (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (start : OracleComp (LocalSpec C) A.State) (i : C.Party)
    (out : Parts C → (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) → α) :
    OracleComp (LocalSpec C) α := do
  let state ← start
  let data ← prssInitialData D
  let r ← prssEarlyDataRounds D A state data
  pure (out (data i).1 r)

theorem prssEarlyObserve_at (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (i : C.Party) (hi : i ∉ D.1)
    (out : Parts C → (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) → α)
    (h : Query C → HashOutput) :
    simulateQ (prssLocalAt prims h) (prssEarlyObserve D A start i out) = (do
      let state ← simulateQ (prssLocalAt prims h) start
      let parts ← prssSampleParts D
      let r ← simulateQ (prssLocalAt prims h) (prssEarlyRounds D A state h parts)
      pure (out (parts i) r)) := by
  simp only [prssEarlyObserve, simulateQ_bind, simulateQ_pure, prssInitialData_at,
    bind_assoc, pure_bind, prssEarlyDataRounds_mask, prssEarlyDataRounds_at]
  simp only [prssDataMask, if_neg hi, prssDataAt]

/-- The finite hash domain is chosen for the entire experiment, before any honest part is sampled.
This is an equality with the actual lazy local oracle, not an assumption on a private cache. -/
theorem evalDist_prssEarlyObserve_eager (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (i : C.Party) (hi : i ∉ D.1)
    (out : Parts C → (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) → α) :
    ∃ S : Finset (Query C),
      𝒟[(simulateQ (localAnswer prims) (prssEarlyObserve D A start i out)).run' ∅] =
        𝒟[do let h ← $ᵗ (S → HashOutput)
              let state ← simulateQ (prssLocalAt prims (prssExtend S h)) start
              let parts ← prssSampleParts D
              let r ← simulateQ (prssLocalAt prims (prssExtend S h))
                (prssEarlyRounds D A state (prssExtend S h) parts)
              pure (out (parts i) r)] := by
  obtain ⟨S,hS⟩ := prssLocalCovered_exists (prssEarlyObserve D A start i out)
  refine ⟨S, ?_⟩
  rw [evalDist_prssLocal_at prims S _ hS]
  apply OracleComp.DeferredSampling.evalDist_bind_congr_left
  intro h
  rw [prssEarlyObserve_at prims D A start i hi out]

end ThresholdLeanXmssSecurity
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.DeferredSampling
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

/-- Sample one coordinate last without changing the joint distribution. -/
theorem evalDist_sequenceFin_split {α β : Type} :
    ∀ {n : ℕ} (f : Fin n → ProbComp α) (i : Fin n) (a₀ : α) (k : (Fin n → α) → ProbComp β),
      𝒟[Concrete.sequenceFin f >>= k] =
        𝒟[(Concrete.sequenceFin fun j => if j = i then pure a₀ else f j) >>= fun xs =>
          f i >>= fun a => k (Function.update xs i a)] := by
  intro n
  induction n with
  | zero => intro f i; exact i.elim0
  | succ n ih =>
    intro f i a₀ k
    have hz (a b : α) (xs : Fin n → α) :
        Function.update (fun j : Fin (n + 1) => Fin.cases (motive := fun _ => α) a xs j) 0 b = (fun j : Fin (n + 1) => Fin.cases (motive := fun _ => α) b xs j) :=
      by
        funext j
        cases j using Fin.cases <;> simp
    have hs (a b : α) (xs : Fin n → α) (j : Fin n) :
        Function.update (fun k : Fin (n + 1) => Fin.cases (motive := fun _ => α) a xs k) j.succ b =
          (fun k : Fin (n + 1) => Fin.cases (motive := fun _ => α) a (Function.update xs j b) k) :=
      by
        funext k
        cases k using Fin.cases <;> simp [Function.update_apply, (Fin.succ_ne_zero j).symm]
    cases i using Fin.cases with
    | zero =>
      simp only [Concrete.sequenceFin, Fin.succ_ne_zero, if_false, if_true, pure_bind, bind_assoc, hz]
      exact evalDist_bind_comm _ _ _
    | succ i =>
      simp only [Concrete.sequenceFin, (Fin.succ_ne_zero i).symm, if_false, Fin.succ_inj, bind_assoc, pure_bind, hs]
      apply evalDist_bind_congr_left
      intro a
      exact ih (fun j => f j.succ) i a₀ (fun xs => k (fun j => Fin.cases (motive := fun _ => α) a xs j))

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
open scoped ENNReal
open OracleComp.DeferredSampling
variable {C : Committee} {E : Type}

/-- The bound survives sampling every honest contribution table; the selected honest row can
be sampled last, with all other rows fixed before applying coordinate independence. -/
theorem prob_prssSampleParts_early_hiddenTerm_le (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (h : Query C → HashOutput) (i : C.Party) (hi : i ∉ D.1)
    (T : C.Term) (hT : Hidden D (.term T))
    (search : OracleComp (LocalSpec C)
      (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) → ProbComp (Finset HashOutput))
    (q : ℕ) (hq : ∀ oa candidates, candidates ∈ support (search oa) → candidates.card ≤ q) :
    Pr[= true | prssSampleParts D >>= fun parts =>
      search (prssEarlyRounds D A state h parts) >>= fun candidates =>
        pure (decide ((parts i).term T ∈ candidates))] ≤ (q : ℝ≥0∞) / 2 ^ 256 := by
  unfold prssSampleParts
  rw [← probEvent_eq_eq_probOutput, probEvent_def,
    evalDist_sequenceFin_split _ i (⟨0, fun _ => 0, fun _ => 0⟩ : Parts C), ← probEvent_def]
  apply probEvent_bind_le_of_forall_le
  intro parts _
  simp only [if_neg hi, Function.update_self]
  rw [probEvent_eq_eq_probOutput]
  exact prob_prssEarlyRounds_hiddenTerm_le D A state h parts i T hT search q hq

theorem prob_prssSampleParts_early_hiddenPair_le (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (h : Query C → HashOutput) (i : C.Party) (hi : i ∉ D.1) (j : C.Party) (hj : j ∉ D.1)
    (search : OracleComp (LocalSpec C)
      (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) → ProbComp (Finset HashOutput))
    (q : ℕ) (hq : ∀ oa candidates, candidates ∈ support (search oa) → candidates.card ≤ q) :
    Pr[= true | prssSampleParts D >>= fun parts =>
      search (prssEarlyRounds D A state h parts) >>= fun candidates =>
        pure (decide ((parts i).pair j ∈ candidates))] ≤ (q : ℝ≥0∞) / 2 ^ 256 := by
  unfold prssSampleParts
  rw [← probEvent_eq_eq_probOutput, probEvent_def,
    evalDist_sequenceFin_split _ i (⟨0, fun _ => 0, fun _ => 0⟩ : Parts C), ← probEvent_def]
  apply probEvent_bind_le_of_forall_le
  intro parts _
  simp only [if_neg hi, Function.update_self]
  rw [probEvent_eq_eq_probOutput]
  exact prob_prssEarlyRounds_hiddenPair_le D A state h parts i j hj search q hq

/-- Concrete early-setup guessing bound in the actual lazy local oracle, including an arbitrary
adversarial start program and both adaptive rounds. The candidate count is bounded by `q`. -/
theorem prob_prssEarlyObserve_hiddenTerm_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (i : C.Party) (hi : i ∉ D.1) (T : C.Term) (hT : Hidden D (.term T))
    (candidates : (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) → Finset HashOutput)
    (q : ℕ) (hq : ∀ r, (candidates r).card ≤ q) :
    Pr[= true | (simulateQ (localAnswer prims)
      (prssEarlyObserve D A start i (fun parts r => decide (parts.term T ∈ candidates r)))).run' ∅] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  obtain ⟨S,he⟩ := evalDist_prssEarlyObserve_eager prims D A start i hi
    (fun parts r => decide (parts.term T ∈ candidates r))
  rw [← probEvent_eq_eq_probOutput, probEvent_def, he, ← probEvent_def]
  apply probEvent_bind_le_of_forall_le
  intro h _
  apply probEvent_bind_le_of_forall_le
  intro state _
  have hp := prob_prssSampleParts_early_hiddenTerm_le D A state (prssExtend S h) i hi T hT
    (fun oa => candidates <$> simulateQ (prssLocalAt prims (prssExtend S h)) oa) q
    (by intro oa c hc; rw [support_map, Set.mem_image] at hc
        obtain ⟨r, _, rfl⟩ := hc; exact hq r)
  simpa only [bind_map_left, probEvent_eq_eq_probOutput] using hp

theorem prob_prssEarlyObserve_hiddenPair_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (i : C.Party) (hi : i ∉ D.1) (j : C.Party) (hj : j ∉ D.1)
    (candidates : (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) → Finset HashOutput)
    (q : ℕ) (hq : ∀ r, (candidates r).card ≤ q) :
    Pr[= true | (simulateQ (localAnswer prims)
      (prssEarlyObserve D A start i (fun parts r => decide (parts.pair j ∈ candidates r)))).run' ∅] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  obtain ⟨S,he⟩ := evalDist_prssEarlyObserve_eager prims D A start i hi
    (fun parts r => decide (parts.pair j ∈ candidates r))
  rw [← probEvent_eq_eq_probOutput, probEvent_def, he, ← probEvent_def]
  apply probEvent_bind_le_of_forall_le
  intro h _
  apply probEvent_bind_le_of_forall_le
  intro state _
  have hp := prob_prssSampleParts_early_hiddenPair_le D A state (prssExtend S h) i hi j hj
    (fun oa => candidates <$> simulateQ (prssLocalAt prims (prssExtend S h)) oa) q
    (by intro oa c hc; rw [support_map, Set.mem_image] at hc
        obtain ⟨r, _, rfl⟩ := hc; exact hq r)
  simpa only [bind_map_left, probEvent_eq_eq_probOutput] using hp

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal
variable {C : Committee} {E α β : Type}

/-- One hash input for each counted query, including the internal hash of a PRG call. -/
def prssCountedHashInputs : (LocalSpec C).Domain → List (Query C)
  | .inl _ => []
  | .inr (.inl q) => if Counted (Sum.inr (Sum.inl q)) then [q] else []
  | .inr (.inr x) => [.streamKey x.2.1]

theorem prssCountedHashInputs_length (t : (LocalSpec C).Domain) :
    (prssCountedHashInputs t).length = if Counted t then 1 else 0 := by
  rcases t with n | q | x
  · simp [prssCountedHashInputs, Counted]
  · simp only [prssCountedHashInputs]; split_ifs <;> rfl
  · simp [prssCountedHashInputs, Counted]

/-- Logging forwards every call unchanged. Only counted hash inputs enter the trace. -/
def prssHashLog (oa : OracleComp (LocalSpec C) α) :
    OracleComp (LocalSpec C) (α × List (Query C)) :=
  (simulateQ ((QueryImpl.id' (LocalSpec C)).withTraceAppend
    (fun t _ => prssCountedHashInputs t)) oa).run

theorem prssHashLog_fst (oa : OracleComp (LocalSpec C) α) :
    Prod.fst <$> prssHashLog oa = oa := by
  rw [prssHashLog, QueryImpl.fst_map_run_withTraceAppend, simulateQ_id']

theorem prssHashLog_pure (a : α) : prssHashLog (C := C) (pure a) = pure (a, []) := rfl

theorem prssHashLog_bind (oa : OracleComp (LocalSpec C) α) (k : α → OracleComp (LocalSpec C) β) :
    prssHashLog (oa >>= k) = (do
      let (a,first) ← prssHashLog oa
      let (b,last) ← prssHashLog (k a)
      pure (b,first ++ last)) := by
  simp [prssHashLog, simulateQ_bind, WriterT.run_bind]

theorem prssHashLog_query (t : (LocalSpec C).Domain) :
    prssHashLog (OracleComp.lift (OracleSpec.query t)) = (do
      let y ← OracleComp.lift (OracleSpec.query t)
      pure (y, prssCountedHashInputs t)) := by
  simp [prssHashLog, QueryImpl.withTraceAppend_apply, WriterT.run_bind]

/-- The trace length is bounded by the model's predicate-targeted query budget. -/
theorem prssHashLog_length (oa : OracleComp (LocalSpec C) α) :
    ∀ n, IsQueryBoundP oa Counted n →
      ∀ r ∈ support (prssHashLog oa), r.2.length ≤ n := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n hn r hr
    simpa only [prssHashLog_pure, support_pure, Set.mem_singleton_iff] using hr ▸ Nat.zero_le n
  | query_bind t k ih =>
    intro n hn r hr
    rw [isQueryBoundP_query_bind_iff] at hn
    simp only [prssHashLog_bind, prssHashLog_query, bind_assoc, pure_bind, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨y, _, z, hz, rfl⟩ := hr
    have hb := ih y _ (hn.2 y) z hz
    rw [List.length_append, prssCountedHashInputs_length]
    by_cases ht : Counted t <;> simp_all <;> omega

/-- Keep the original adversary state and append the counted oracle trace. -/
def prssLoggedAdversary (A : Adversary C E (Keys C) PEmpty PEmpty) :
    Adversary C E (Keys C) PEmpty PEmpty where
  State := A.State × List (Query C)
  start x z := prssHashLog (A.start x z)
  round state visible := do
    let ((state',sent),more) ← prssHashLog (A.round state.1 visible)
    pure ((state',state.2 ++ more),sent)
  answer _ input := input.elim

theorem prssLoggedAdversary_round_length (A : Adversary C E (Keys C) PEmpty PEmpty)
    (step : ℕ) (hb : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (state : (prssLoggedAdversary A).State) (visible : C.Party → Mail C E)
    (r : (prssLoggedAdversary A).State × (C.Party → Mail C E))
    (hr : r ∈ support ((prssLoggedAdversary A).round state visible)) :
    r.1.2.length ≤ state.2.length + step := by
  simp only [prssLoggedAdversary, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨z,hz,rfl⟩ := hr
  simpa only [List.length_append] using Nat.add_le_add_left
    (prssHashLog_length (A.round state.1 visible) step (hb _ _) z hz) state.2.length

/-- At most two round calls occur before derivation; early all-abort runs make only one. -/
theorem prssEarlyDataRounds_log_length (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (step : ℕ) (hb : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (state : (prssLoggedAdversary A).State) (data : C.Party → Parts C × List HashOutput)
    (r : (prssLoggedAdversary A).State × (C.Party → Mail C E) × Option (C.Party → Mail C E))
    (hr : r ∈ support (prssEarlyDataRounds D (prssLoggedAdversary A) state data)) :
    r.1.2.length ≤ state.2.length + 2 * step := by
  unfold prssEarlyDataRounds at hr
  simp only [support_bind, Set.mem_iUnion] at hr
  obtain ⟨⟨state',sent⟩,hfirst,hr⟩ := hr
  have h₁ := prssLoggedAdversary_round_length A step hb state _ _ hfirst
  dsimp only at h₁
  dsimp only at hr
  split_ifs at hr with hall
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst r
    dsimp only
    omega
  · simp only [pure_bind, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨⟨state'',sent'⟩,hlast,rfl⟩ := hr
    have h₂ := prssLoggedAdversary_round_length A step hb state' _ _ hlast
    dsimp only at h₂
    dsimp only
    omega

/-- Taking at most `q` trace entries gives at most `q` guesses under any extraction function. -/
def prssTraceCandidates (q : ℕ) (pick : Query C → HashOutput) (trace : List (Query C)) : Finset HashOutput :=
  ((trace.take q).map pick).toFinset

theorem prssTraceCandidates_card (q : ℕ) (pick : Query C → HashOutput) (trace : List (Query C)) :
    (prssTraceCandidates q pick trace).card ≤ q := by
  exact (List.toFinset_card_le _).trans (by simp [List.length_take])

theorem prssTraceCandidates_all (q : ℕ) (pick : Query C → HashOutput) (trace : List (Query C))
    (hq : trace.length ≤ q) : prssTraceCandidates q pick trace = (trace.map pick).toFinset := by
  simp [prssTraceCandidates, List.take_of_length_le hq]

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal
variable {C : Committee} {E α : Type}

/-- For the model's query-bounded adversary, truncating the trace does not remove any candidate. -/
theorem prssEarlyObserve_trace_take (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (initial step q : ℕ) (hstart : IsQueryBoundP start Counted initial)
    (hstep : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (hq : initial + 2 * step ≤ q) (i : C.Party) (pick : Query C → HashOutput)
    (out : Parts C → Finset HashOutput → α) :
    prssEarlyObserve D (prssLoggedAdversary A) (prssHashLog start) i
        (fun parts r => out parts ((r.1.2.map pick).toFinset)) =
      prssEarlyObserve D (prssLoggedAdversary A) (prssHashLog start) i
        (fun parts r => out parts (prssTraceCandidates q pick r.1.2)) := by
  unfold prssEarlyObserve
  apply bind_congr_of_forall_mem_support
  intro state hs
  have hs' := prssHashLog_length start initial hstart state hs
  apply bind_congr
  intro data
  apply bind_congr_of_forall_mem_support
  intro r hr
  have hb := prssEarlyDataRounds_log_length D A step hstep state data r hr
  dsimp only
  rw [prssTraceCandidates_all q pick r.1.2 (by omega)]

/-- Every counted pre-derivation query yields at most one guess of a selected hidden term
contribution, even with arbitrary earlier adversarial oracle work. -/
theorem prob_prssEarlyTrace_hiddenTerm_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (initial step q : ℕ) (hstart : IsQueryBoundP start Counted initial)
    (hstep : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (hq : initial + 2 * step ≤ q) (i : C.Party) (hi : i ∉ D.1)
    (T : C.Term) (hT : Hidden D (.term T)) (pick : Query C → HashOutput) :
    Pr[= true | (simulateQ (localAnswer prims)
      (prssEarlyObserve D (prssLoggedAdversary A) (prssHashLog start) i
        (fun parts r => decide (parts.term T ∈ (r.1.2.map pick).toFinset)))).run' ∅] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  rw [prssEarlyObserve_trace_take D A start initial step q hstart hstep hq i pick
    (fun parts guesses => decide (parts.term T ∈ guesses))]
  exact prob_prssEarlyObserve_hiddenTerm_le prims D (prssLoggedAdversary A) (prssHashLog start)
    i hi T hT (fun r => prssTraceCandidates q pick r.1.2) q
    (fun r => prssTraceCandidates_card q pick r.1.2)

theorem prob_prssEarlyTrace_hiddenPair_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (initial step q : ℕ) (hstart : IsQueryBoundP start Counted initial)
    (hstep : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (hq : initial + 2 * step ≤ q) (i : C.Party) (hi : i ∉ D.1)
    (j : C.Party) (hj : j ∉ D.1) (pick : Query C → HashOutput) :
    Pr[= true | (simulateQ (localAnswer prims)
      (prssEarlyObserve D (prssLoggedAdversary A) (prssHashLog start) i
        (fun parts r => decide (parts.pair j ∈ (r.1.2.map pick).toFinset)))).run' ∅] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  rw [prssEarlyObserve_trace_take D A start initial step q hstart hstep hq i pick
    (fun parts guesses => decide (parts.pair j ∈ guesses))]
  exact prob_prssEarlyObserve_hiddenPair_le prims D (prssLoggedAdversary A) (prssHashLog start)
    i hi j hj (fun r => prssTraceCandidates q pick r.1.2) q
    (fun r => prssTraceCandidates_card q pick r.1.2)

/-- The same observed prefix with the original counted/free oracle placement. -/
def prssEarlyWorldObserve (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (start : OracleComp (LocalSpec C) A.State) (i : C.Party)
    (out : Parts C → (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) → α) :
    OracleComp (WorldSpec C) α := do
  let state ← worldRoles.adversary start
  let data ← free (prssInitialData D)
  let r ← worldRoles.adversary (prssEarlyDataRounds D A state data)
  pure (out (data i).1 r)

theorem simulateQ_prssEarlyWorldObserve (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (i : C.Party)
    (out : Parts C → (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) → α) :
    simulateQ (worldAnswer prims) (prssEarlyWorldObserve D A start i out) =
      simulateQ (localAnswer prims) (prssEarlyObserve D A start i out) := by
  have ha {β : Type} (oa : OracleComp (LocalSpec C) β) :
      simulateQ (worldAnswer prims) (worldRoles.adversary oa) = simulateQ (localAnswer prims) oa := by
    induction oa using OracleComp.inductionOn with
    | pure a => rfl
    | query_bind t k ih =>
      change simulateQ (worldAnswer prims) (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
        fun x => worldRoles.adversary (k x)) = _
      rw [simulateQ_bind, adversary_query, simulateQ_spec_query]
      simp only [simulateQ_bind, simulateQ_spec_query, ih]
      rfl
  simp only [prssEarlyWorldObserve, prssEarlyObserve, simulateQ_bind, simulateQ_pure, ha]
  rw [show simulateQ (worldAnswer prims) (free (prssInitialData D)) =
    simulateQ (localAnswer prims) (prssInitialData D) from simulateQ_free _ _ _]

/-- Pre-derivation term guessing in the shared real world, with the actual query budget. -/
theorem prob_prssEarlyWorldTrace_hiddenTerm_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (initial step q : ℕ) (hstart : IsQueryBoundP start Counted initial)
    (hstep : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (hq : initial + 2 * step ≤ q) (i : C.Party) (hi : i ∉ D.1)
    (T : C.Term) (hT : Hidden D (.term T)) (pick : Query C → HashOutput) :
    Pr[= true | (simulateQ (worldAnswer prims)
      (prssEarlyWorldObserve D (prssLoggedAdversary A) (prssHashLog start) i
        (fun parts r => decide (parts.term T ∈ (r.1.2.map pick).toFinset)))).run' ∅] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  rw [simulateQ_prssEarlyWorldObserve]
  exact prob_prssEarlyTrace_hiddenTerm_le prims D A start initial step q hstart hstep hq i hi T hT pick

theorem prob_prssEarlyWorldTrace_hiddenPair_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (initial step q : ℕ) (hstart : IsQueryBoundP start Counted initial)
    (hstep : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (hq : initial + 2 * step ≤ q) (i : C.Party) (hi : i ∉ D.1)
    (j : C.Party) (hj : j ∉ D.1) (pick : Query C → HashOutput) :
    Pr[= true | (simulateQ (worldAnswer prims)
      (prssEarlyWorldObserve D (prssLoggedAdversary A) (prssHashLog start) i
        (fun parts r => decide (parts.pair j ∈ (r.1.2.map pick).toFinset)))).run' ∅] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  rw [simulateQ_prssEarlyWorldObserve]
  exact prob_prssEarlyTrace_hiddenPair_le prims D A start initial step q hstart hstep hq i hi j hj pick

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
open scoped ENNReal
variable {C : Committee} {E α : Type}

/-- The joint sampled-parts and adversarial state at the boundary before honest derivation. -/
def prssEarlyTable (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (start : OracleComp (LocalSpec C) A.State) :
    OracleComp (LocalSpec C)
      ((C.Party → Parts C) × A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) := do
  let state ← start
  let data ← prssInitialData D
  let r ← prssEarlyDataRounds D A state data
  pure ((fun i => (data i).1),r)

theorem prssEarlyObserve_eq_map (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (start : OracleComp (LocalSpec C) A.State) (i : C.Party)
    (out : Parts C → (A.State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) → α) :
    prssEarlyObserve D A start i out = (fun r => out (r.1 i) r.2) <$> prssEarlyTable D A start := by
  simp only [prssEarlyObserve, prssEarlyTable, map_bind, map_pure]

/-- A candidate derivation query determines one candidate value at any fixed input position. -/
def prssDerivePick (n : ℕ) : Query C → HashOutput
  | .derive _ _ values => values.getD n 0
  | _ => 0

def prssTermInput (parts : C.Party → Parts C) (T : C.Term) : Query C :=
  .derive .prss .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (parts j).term T)

def prssPairInput (parts : C.Party → Parts C) (p : C.Pair) : Query C :=
  .derive .prss .pair [(parts p.1.1).pair p.1.2, (parts p.1.2).pair p.1.1]

theorem prssTermInput_pick (parts : C.Party → Parts C) (T : C.Term) (i : C.Party)
    (hi : i ∈ C.holders T) :
    prssDerivePick ((C.parties.filter (· ∈ C.holders T)).idxOf i) (prssTermInput parts T) =
      (parts i).term T := by
  have hm : i ∈ C.parties.filter (· ∈ C.holders T) := by simp [Committee.parties, hi]
  simp only [prssDerivePick, prssTermInput, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf hm, Option.map_some, Option.getD_some]

theorem prssPairInput_pick (parts : C.Party → Parts C) (p : C.Pair) :
    prssDerivePick 0 (prssPairInput parts p) = (parts p.1.1).pair p.1.2 := rfl

/-- The probability bound is on exact canonical derivation prequeries, not merely on guessed
stream keys. The selected holder contributes a uniform coordinate hidden from the first two rounds. -/
theorem prob_prssEarly_termInput_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (initial step q : ℕ) (hstart : IsQueryBoundP start Counted initial)
    (hstep : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (hq : initial + 2 * step ≤ q) (T : C.Term) (hT : Hidden D (.term T))
    (i : C.Party) (hi : i ∈ C.holders T) :
    Pr[fun r => prssTermInput r.1 T ∈ r.2.1.2 |
      (simulateQ (localAnswer prims)
        (prssEarlyTable D (prssLoggedAdversary A) (prssHashLog start))).run' ∅] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  let pick : Query C → HashOutput := prssDerivePick ((C.parties.filter (· ∈ C.holders T)).idxOf i)
  have hb := prob_prssEarlyTrace_hiddenTerm_le prims D A start initial step q hstart hstep hq
    i (hidden_term_holders D hT i hi) T hT pick
  rw [prssEarlyObserve_eq_map] at hb
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] at hb
  rw [← probEvent_eq_eq_probOutput, probEvent_map] at hb
  rw [StateT.run'_eq, probEvent_map]
  refine le_trans (probEvent_mono ?_) hb
  rintro ⟨r,cache⟩ _ hr
  dsimp only [Function.comp_def] at hr
  simp only [Function.comp_def, decide_eq_true_eq, List.mem_toFinset, List.mem_map]
  exact ⟨prssTermInput r.1 T, hr, prssTermInput_pick r.1 T i hi⟩

theorem prob_prssEarly_pairInput_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (initial step q : ℕ) (hstart : IsQueryBoundP start Counted initial)
    (hstep : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (hq : initial + 2 * step ≤ q) (p : C.Pair) (hp : Hidden D (.pair p)) :
    Pr[fun r => prssPairInput r.1 p ∈ r.2.1.2 |
      (simulateQ (localAnswer prims)
        (prssEarlyTable D (prssLoggedAdversary A) (prssHashLog start))).run' ∅] ≤
      (q : ℝ≥0∞) / 2 ^ 256 := by
  have hb := prob_prssEarlyTrace_hiddenPair_le prims D A start initial step q hstart hstep hq
    p.1.1 hp.1 p.1.2 hp.2 (prssDerivePick 0)
  rw [prssEarlyObserve_eq_map] at hb
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map] at hb
  rw [← probEvent_eq_eq_probOutput, probEvent_map] at hb
  rw [StateT.run'_eq, probEvent_map]
  refine le_trans (probEvent_mono ?_) hb
  rintro ⟨r,cache⟩ _ hr
  dsimp only [Function.comp_def] at hr
  simp only [Function.comp_def, decide_eq_true_eq, List.mem_toFinset, List.mem_map]
  exact ⟨prssPairInput r.1 p, hr, prssPairInput_pick r.1 p⟩

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
open scoped ENNReal
variable {C : Committee} {E : Type}

/-- Each threshold term has a holder. -/
theorem prss_exists_holder (T : C.Term) : ∃ i, i ∈ C.holders T := by
  have hc : (C.holders T).card = C.t := by
    simp only [Committee.holders, Finset.card_compl, Fintype.card_fin, T.2]
    have ht := C.one_le_t
    unfold Committee.n
    omega
  apply Finset.card_pos.mp
  rw [hc]
  exact C.one_le_t

/-- One union of all hidden canonical derivation prequeries. -/
def prssEarlyInputBad (D : C.Coalition) (parts : C.Party → Parts C) (trace : List (Query C)) : Prop :=
  (∃ T : C.Term, Hidden D (.term T) ∧ prssTermInput parts T ∈ trace) ∨
    (∃ p : C.Pair, Hidden D (.pair p) ∧ prssPairInput parts p ∈ trace)

/-- A single union bound over term names and pair names gives the
`q*(choose(n,t-1)+choose(n,2))/2^256` prequery term. It includes the adversary start and both pre-derivation round calls. -/
theorem prob_prssEarlyInputBad_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (initial step q : ℕ) (hstart : IsQueryBoundP start Counted initial)
    (hstep : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (hq : initial + 2 * step ≤ q) :
    Pr[fun r => prssEarlyInputBad D r.1 r.2.1.2 |
      (simulateQ (localAnswer prims)
        (prssEarlyTable D (prssLoggedAdversary A) (prssHashLog start))).run' ∅] ≤
      (q : ℝ≥0∞) * (C.n.choose (C.t - 1) + C.n.choose 2) / 2 ^ 256 := by
  let run := (simulateQ (localAnswer prims)
    (prssEarlyTable D (prssLoggedAdversary A) (prssHashLog start))).run' ∅
  let Result := (C.Party → Parts C) × (prssLoggedAdversary A).State ×
    (C.Party → Mail C E) × Option (C.Party → Mail C E)
  let event : C.Term ⊕ C.Pair → Result → Prop := fun name r => match name with
    | .inl T => Hidden D (.term T) ∧ prssTermInput r.1 T ∈ r.2.1.2
    | .inr p => Hidden D (.pair p) ∧ prssPairInput r.1 p ∈ r.2.1.2
  have hb (name : C.Term ⊕ C.Pair) : Pr[event name | run] ≤ (q : ℝ≥0∞) / 2 ^ 256 := by
    cases name with
    | inl T =>
      by_cases hh : Hidden D (.term T)
      · obtain ⟨i,hi⟩ := prss_exists_holder T
        simpa only [event, hh, true_and] using
          prob_prssEarly_termInput_le prims D A start initial step q hstart hstep hq T hh i hi
      · simp [event, hh, probEvent_def]
    | inr p =>
      by_cases hh : Hidden D (.pair p)
      · simpa only [event, hh, true_and] using
          prob_prssEarly_pairInput_le prims D A start initial step q hstart hstep hq p hh
      · simp [event, hh, probEvent_def]
  have he (r : Result) : prssEarlyInputBad D r.1 r.2.1.2 ↔ ∃ name ∈ (Finset.univ : Finset (C.Term ⊕ C.Pair)), event name r := by
    simp only [Finset.mem_univ, true_and, Sum.exists, event, prssEarlyInputBad]
  change Pr[fun r => prssEarlyInputBad D r.1 r.2.1.2 | run] ≤ _
  calc
    _ = Pr[fun r => ∃ name ∈ (Finset.univ : Finset (C.Term ⊕ C.Pair)), event name r | run] :=
      probEvent_ext fun r _ => he r
    _ ≤ ∑ name : C.Term ⊕ C.Pair, Pr[event name | run] := probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _name : C.Term ⊕ C.Pair, (q : ℝ≥0∞) / 2 ^ 256 := Finset.sum_le_sum fun name _ => hb name
    _ = (q : ℝ≥0∞) * (Fintype.card C.Term + Fintype.card C.Pair) / 2 ^ 256 := by
      simp [Fintype.card_sum, nsmul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ _ := by
      rw [card_term]
      gcongr
      exact card_pair_le C

end ThresholdLeanXmssSecurity

/-! ## Fresh derivation inputs at the setup boundary -/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {C : Committee} {α : Type}

/-- A random-oracle call only changes the cache at its queried address. -/
theorem prssRandomOracle_other (q target : Query C) (hne : target ≠ q)
    (cache : HashCache C) (r : HashOutput × HashCache C)
    (hr : r ∈ support (((Query C →ₒ HashOutput).randomOracle q).run cache)) :
    r.2 target = cache target := by
  cases hc : cache q with
  | none =>
    rw [randomOracle, QueryImpl.withCaching_run_none _ hc, support_map, Set.mem_image] at hr
    obtain ⟨y,_,rfl⟩ := hr
    simp [QueryCache.cacheQuery, hne]
  | some y =>
    rw [randomOracle, QueryImpl.withCaching_run_some _ hc, support_pure, Set.mem_singleton_iff] at hr
    subst r
    rfl

theorem prssHashAnswer_other (prims : Primitives) (q target : Query C) (hne : target ≠ q)
    (cache : HashCache C) (r : HashOutput × HashCache C)
    (hr : r ∈ support ((hashAnswer prims q).run cache)) : r.2 target = cache target := by
  by_cases hf : IsFixed q
  · obtain ⟨input,rfl,hi⟩ := hf
    rw [prssHashAnswer_fixed prims hi, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    rfl
  · rw [prssHashAnswer_not_fixed prims hf] at hr
    exact prssRandomOracle_other q target hne cache r hr

/-- Any cache address absent from this call's counted trace is unchanged. Fixed `Th` calls have
an empty trace and change no random-oracle cache address. -/
theorem prssLocalAnswer_other (prims : Primitives) (t : (LocalSpec C).Domain) (target : Query C)
    (ht : target ∉ prssCountedHashInputs t) (cache : HashCache C)
    (r : (LocalSpec C).Range t × HashCache C)
    (hr : r ∈ support ((localAnswer prims t).run cache)) : r.2 target = cache target := by
  rcases t with n | q | x
  · change r ∈ support ((fun y => (y, cache)) <$>
      (OracleComp.lift (OracleSpec.query n) : ProbComp _)) at hr
    rw [support_map, Set.mem_image] at hr
    obtain ⟨y,_,rfl⟩ := hr
    rfl
  · by_cases hc : Counted (C := C) (.inr (.inl q))
    · have hn : target ≠ q := by simpa [prssCountedHashInputs, hc] using ht
      exact prssHashAnswer_other prims q target hn cache r hr
    · have hf : IsFixed q := by
        cases q <;> simp_all [Counted, IsFixed]
      obtain ⟨input,rfl,hi⟩ := hf
      change r ∈ support ((hashAnswer prims (.hash input)).run cache) at hr
      rw [prssHashAnswer_fixed prims hi, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
      subst r
      rfl
  · have hn : target ≠ .streamKey x.2.1 := by simpa [prssCountedHashInputs] using ht
    change r ∈ support ((prgAnswer prims x).run cache) at hr
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion,
      support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨p,hp,rfl⟩ := hr
    exact prssHashAnswer_other prims _ target hn cache p hp

/-- Absence from the accumulated counted trace preserves the address throughout an adaptive
local computation. This is pointwise in its initial cache. -/
theorem prssHashLog_cache_other (prims : Primitives) (oa : OracleComp (LocalSpec C) α) :
    ∀ (cache : HashCache C) (r : (α × List (Query C)) × HashCache C),
      r ∈ support ((simulateQ (localAnswer prims) (prssHashLog oa)).run cache) →
      ∀ target, target ∉ r.1.2 → r.2 target = cache target := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro cache r hr target ht
    simp only [prssHashLog_pure, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    rfl
  | query_bind t k ih =>
    intro cache r hr target ht
    simp only [prssHashLog_bind, prssHashLog_query, bind_assoc, pure_bind, simulateQ_bind,
      simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure, pure_bind,
      support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨p,hp,z,hz,rfl⟩ := hr
    have ht' : target ∉ prssCountedHashInputs t ∧ target ∉ z.1.2 := by
      simpa only [List.mem_append, not_or] using ht
    exact (ih p.1 p.2 z hz target ht'.2).trans
      (prssLocalAnswer_other prims t target ht'.1 cache p hp)

/-- A finite sequence preserves an address when each component does so from every cache. -/
theorem prssSequenceFin_cache_other (target : Query C) :
    ∀ {n : ℕ} (f : Fin n → StateT (HashCache C) ProbComp α),
      (∀ i cache r, r ∈ support ((f i).run cache) → r.2 target = cache target) →
      ∀ cache r, r ∈ support ((Concrete.sequenceFin f).run cache) → r.2 target = cache target := by
  intro n
  induction n with
  | zero =>
    intro f hf cache r hr
    simp only [Concrete.sequenceFin, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    rfl
  | succ n ih =>
    intro f hf cache r hr
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨p,hp,z,hz,rfl⟩ := hr
    exact (ih (fun i => f i.succ) (fun i => hf i.succ) p.2 z hz).trans (hf 0 cache p hp)

theorem prssMapM_cache_other {β : Type} (target : Query C) (xs : List β)
    (f : β → StateT (HashCache C) ProbComp α)
    (hf : ∀ x ∈ xs, ∀ cache r, r ∈ support ((f x).run cache) → r.2 target = cache target) :
    ∀ cache r, r ∈ support ((xs.mapM f).run cache) → r.2 target = cache target := by
  induction xs with
  | nil =>
    intro cache r hr
    simp only [List.mapM_nil, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    rfl
  | cons x xs ih =>
    intro cache r hr
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨p,hp,z,hz,rfl⟩ := hr
    exact (ih (fun y hy => hf y (List.mem_cons_of_mem _ hy)) p.2 z hz).trans
      (hf x (List.mem_cons_self ..) cache p hp)

/-- Initial honest sampling and commitment hashes cannot populate any derivation address. -/
theorem prssInitialData_cache_other (prims : Primitives) (D : C.Coalition) (target : Query C)
    (hn : ∀ i j values, target ≠ .commit .prss i j values)
    (cache : HashCache C) (r : (C.Party → Parts C × List HashOutput) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims) (prssInitialData D)).run cache)) :
    r.2 target = cache target := by
  rw [prssInitialData, simulateQ_sequenceFin] at hr
  apply prssSequenceFin_cache_other target _ _ cache r hr
  intro i s z hz
  by_cases hi : i ∈ D.1
  · simp only [if_pos hi, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst z
    rfl
  · simp only [if_neg hi, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, simulateQ_local_sample, support_bind, support_map,
      support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨v, ⟨own, hown, rfl⟩, commits, hcommits, rfl⟩ := hz
    have he : simulateQ (localAnswer prims) (liftComp (C.parties.mapM fun j =>
        hashQuery (.commit .prss i j (revealTo .prss own i j))) (LocalSpec C)) =
        C.parties.mapM fun j => hashAnswer prims (.commit .prss i j (revealTo .prss own i j)) := by
      rw [localAnswer, QueryImpl.simulateQ_add_liftComp_right, simulateQ_list_mapM]
      congr 1
      funext j
      exact simulateQ_spec_query _ _
    rw [he] at hcommits
    exact prssMapM_cache_other target C.parties _
      (fun j _ s r hr => prssHashAnswer_other prims _ target (hn i j _) s r hr) s commits hcommits

variable {E : Type}

/-- One logged adversarial round extends the trace and preserves addresses absent from it. -/
theorem prssLoggedRound_cache_other (prims : Primitives)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : (prssLoggedAdversary A).State)
    (visible : C.Party → Mail C E) (cache : HashCache C)
    (r : ((prssLoggedAdversary A).State × (C.Party → Mail C E)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      ((prssLoggedAdversary A).round state visible)).run cache)) :
    (∀ target ∈ state.2, target ∈ r.1.1.2) ∧
      ∀ target, target ∉ r.1.1.2 → r.2 target = cache target := by
  simp only [prssLoggedAdversary, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨z,hz,rfl⟩ := hr
  constructor
  · intro target ht
    exact List.mem_append_left _ ht
  · intro target ht
    exact prssHashLog_cache_other prims (A.round state.1 visible) cache z hz target
      (fun hm => ht (List.mem_append_right _ hm))

/-- Through both adaptive rounds, every derivation address absent from the accumulated trace
is preserved, and no earlier trace entry is lost. -/
theorem prssEarlyDataRounds_cache_other (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : (prssLoggedAdversary A).State)
    (data : C.Party → Parts C × List HashOutput) (cache : HashCache C)
    (r : ((prssLoggedAdversary A).State × (C.Party → Mail C E) × Option (C.Party → Mail C E)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssEarlyDataRounds D (prssLoggedAdversary A) state data)).run cache)) :
    (∀ target ∈ state.2, target ∈ r.1.1.2) ∧
      ∀ target, target ∉ r.1.1.2 → r.2 target = cache target := by
  unfold prssEarlyDataRounds at hr
  simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hr
  obtain ⟨⟨⟨state',sent⟩,cache'⟩,hfirst,hr⟩ := hr
  have h₁ := prssLoggedRound_cache_other prims A state _ cache _ hfirst
  dsimp only at hr h₁
  split_ifs at hr with hall
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact h₁
  · simp only [pure_bind, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨⟨⟨state'',sent'⟩,cache''⟩,hlast,rfl⟩ := hr
    have h₂ := prssLoggedRound_cache_other prims A state' _ cache' _ hlast
    dsimp only at h₂
    exact ⟨fun target ht => h₂.1 target (h₁.1 target ht),
      fun target ht => (h₂.2 target ht).trans (h₁.2 target (fun hm => ht (h₂.1 target hm)))⟩

/-- At the actual boundary before derivation, an unqueried derivation address is still fresh.
The address may depend on the sampled parts; this is a pointwise cache statement. -/
theorem prssEarlyTable_derive_fresh (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (r : ((C.Party → Parts C) × (prssLoggedAdversary A).State ×
      (C.Party → Mail C E) × Option (C.Party → Mail C E)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (prssEarlyTable D (prssLoggedAdversary A) (prssHashLog start))).run ∅)) :
    ∀ phase kind values, Query.derive phase kind values ∉ r.1.2.1.2 →
      r.2 (.derive phase kind values) = none := by
  simp only [prssEarlyTable, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨state,hs,data,hd,rounds,hh,rfl⟩ := hr
  intro phase kind values hnot
  have hrounds := prssEarlyDataRounds_cache_other prims D A state.1 data.1 data.2 rounds hh
  have hdata := prssInitialData_cache_other prims D (.derive phase kind values)
    (by intros; simp) state.2 data hd
  have hstart := prssHashLog_cache_other prims start ∅ state hs (.derive phase kind values)
    (fun hm => hnot (hrounds.1 _ hm))
  exact (hrounds.2 _ hnot).trans (hdata.trans hstart)

open scoped ENNReal

/-- The actual shared cache contains any hidden canonical derivation input before derivation
with probability at most the single prequery union bound. -/
theorem prob_prssEarlyCachedInput_le (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (start : OracleComp (LocalSpec C) A.State)
    (initial step q : ℕ) (hstart : IsQueryBoundP start Counted initial)
    (hstep : ∀ state visible, IsQueryBoundP (A.round state visible) Counted step)
    (hq : initial + 2 * step ≤ q) :
    Pr[fun r =>
      (∃ T : C.Term, Hidden D (.term T) ∧ r.2 (prssTermInput r.1.1 T) ≠ none) ∨
      (∃ p : C.Pair, Hidden D (.pair p) ∧ r.2 (prssPairInput r.1.1 p) ≠ none) |
      (simulateQ (localAnswer prims)
        (prssEarlyTable D (prssLoggedAdversary A) (prssHashLog start))).run ∅] ≤
      (q : ℝ≥0∞) * (C.n.choose (C.t - 1) + C.n.choose 2) / 2 ^ 256 := by
  have hb := prob_prssEarlyInputBad_le prims D A start initial step q hstart hstep hq
  rw [StateT.run'_eq, probEvent_map] at hb
  refine le_trans (probEvent_mono ?_) hb
  intro r hr hbad
  have hf := prssEarlyTable_derive_fresh prims D A start r hr
  rcases hbad with ⟨T,hT,hcached⟩ | ⟨p,hp,hcached⟩
  · left
    refine ⟨T,hT,?_⟩
    by_contra hnot
    exact hcached (hf .prss .term _ hnot)
  · right
    refine ⟨p,hp,?_⟩
    by_contra hnot
    exact hcached (hf .prss .pair _ hnot)

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (prims : Primitives) (K : Constants C E) (circuits : Circuits)
  (settings : Settings)

end ThresholdLeanXmssSecurity
