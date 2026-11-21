import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.PartsStepCommitShift

/-!
# The pad of the honest pair cells does not change the suffix

`suffixAt_padCells` states that the pad `padCells (pairFamily D commitAt) π` does not change
`suffixAt x commitAt termAt`.

* The commitments of an honest sender `i` to an honest receiver carry the pad of their cell
  (`commitDrawsAt_padCells`). The mail to a corrupt receiver has no pad.
* After round 2 an honest receiver `j` opens the commitment of an honest sender `k ≠ j` at the same cell,
  so the open answer carries the same pad, and the test compares two padded answers. The open cell of
  `j` for itself goes into no test (`revealNextAt_padCells`).
* The rest of the game asks no commit cell (`noCall_secRest_seedGenCell`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## The pad on the local oracles -/

section Local

variable {ι : Type} (cell : ι → Query C) (π : ι → HashOutput)

/-- The answer of a call of `H` at the cell `q` with the pad of its cell. -/
def padAdjF (q : Query C) (a : HashOutput) : HashOutput := if h : InFamily cell q then a ^^^ π h.choose else a

/-- The local oracles with the pad. -/
def localPadF : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)) := fun t =>
  match t with
  | .inr (.inl q) =>
      padAdjF cell π q <$> (liftM (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q))) :
        OracleComp (LocalSpec C) HashOutput)
  | t => liftM (OracleSpec.query t)

/-- The random oracles with the pad. -/
def roPadF : QueryImpl (RoSpec C) (OracleComp (RoSpec C)) := fun t =>
  match t with
  | .inl q => padAdjF cell π q <$> (liftM (OracleSpec.query (spec := RoSpec C) (.inl q)) : OracleComp (RoSpec C) HashOutput)
  | t => liftM (OracleSpec.query t)

theorem padAdjF_of_not {q : Query C} (hq : ¬ InFamily cell q) : padAdjF cell π q = fun a => a := by
  funext a
  simp [padAdjF, hq]

theorem padAdjF_inj (q : Query C) (a b : HashOutput) : padAdjF cell π q a = padAdjF cell π q b ↔ a = b := by
  unfold padAdjF
  split_ifs with hf
  · constructor
    · intro h
      have := congrArg (· ^^^ π hf.choose) h
      simpa [BitVec.xor_assoc] using this
    · rintro rfl
      rfl
  · exact Iff.rfl

theorem padCells_hash (q : Query C) :
    padCells cell π (.inr (.inr (.inl q))) =
      padAdjF cell π q <$> (liftM (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inl q)))) :
        OracleComp (WorldSpec C) HashOutput) := by
  unfold padCells padAdjF
  by_cases h : InFamily cell q
  · simp only [h, dite_true]
  · simp only [h, dite_false, id_map']

theorem padCells_counted {α : Type} (oa : OracleComp (SimulatorSpec C) α) :
    simulateQ (padCells cell π) (counted oa) = counted oa :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => by simp [padCells]) oa

theorem padCells_free {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (padCells cell π) (free oa) = free (simulateQ (localPadF cell π) oa) := by
  unfold free
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with n | q | x
  · simp [padCells, localPadF]
  · simp [padCells_hash, localPadF]
  · simp [padCells, localPadF]

theorem localPadF_liftComp {α : Type} (oa : OracleComp (RoSpec C) α) :
    simulateQ (localPadF cell π) (liftComp oa (LocalSpec C)) = liftComp (simulateQ (roPadF cell π) oa) (LocalSpec C) := by
  rw [liftComp_def, liftComp_def, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with q | x
  · change simulateQ (localPadF cell π) (liftM (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q)))) =
      simulateQ (fun t => liftM (OracleSpec.query (spec := RoSpec C) t)) (roPadF cell π (.inl q))
    simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, localPadF, roPadF,
      simulateQ_map]
    rfl
  · change simulateQ (localPadF cell π) (liftM (OracleSpec.query (spec := LocalSpec C) (.inr (.inr x)))) =
      simulateQ (fun t => liftM (OracleSpec.query (spec := RoSpec C) t)) (roPadF cell π (.inr x))
    simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, localPadF, roPadF]
    rfl

theorem localPadF_liftComp_prob {α : Type} (oa : ProbComp α) :
    simulateQ (localPadF cell π) (liftComp oa (LocalSpec C)) = liftComp oa (LocalSpec C) := by
  rw [liftComp_def]
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  change simulateQ (localPadF cell π) (liftM (OracleSpec.query (spec := LocalSpec C) (.inl t))) = _
  simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, localPadF]
  rfl

theorem roPadF_hashQuery (q : Query C) :
    simulateQ (roPadF cell π) (hashQuery q) = padAdjF cell π q <$> hashQuery q := by
  simp [hashQuery, roPadF]

theorem roPadF_mapM {α : Type} (l : List α) (addr : α → Query C) :
    simulateQ (roPadF cell π) (l.mapM fun x => hashQuery (addr x)) =
      (fun r => List.zipWith (fun x a => padAdjF cell π (addr x) a) l r) <$> l.mapM fun x => hashQuery (addr x) := by
  rw [simulateQ_list_mapM]
  simp only [roPadF_hashQuery]
  exact mapM_map_zipWith _ _ l

theorem roPadF_hashQuery_of_not (q : Query C) (hq : ¬ InFamily cell q) :
    simulateQ (roPadF cell π) (hashQuery q) = hashQuery q := by
  rw [roPadF_hashQuery, padAdjF_of_not cell π hq, id_map']

end Local

/-! ## The walk through the suffix -/

section Walk

variable (D : C.Coalition) (commitAt : C.Party → C.Party → Query C) (π : PairIndex C D → HashOutput)

theorem levelRound_padCells (net : Adversary C E Unit PEmpty PEmpty) {X Y β : Type} (fuel : ℕ) (state : net.State)
    (d : C.Party → Option X) (out : C.Party → X → Mail C E)
    (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β))) :
    simulateQ (padCells (pairFamily D commitAt) π) (levelRound D net fuel state d out next cont) =
      levelRound D net fuel state d out
        (fun j x inbox => simulateQ (localPadF (pairFamily D commitAt) π) (next j x inbox))
        (fun f s d' => simulateQ (padCells (pairFamily D commitAt) π) (cont f s d')) := by
  cases fuel with
  | zero => simp [levelRound]
  | succ fuel =>
    rw [levelRound, levelRound]
    by_cases hall : ∀ i, i ∉ D.1 → d i = none
    · rw [ite_eq_left hall, ite_eq_left hall, simulateQ_pure]
    rw [ite_eq_right hall, ite_eq_right hall, simulateQ_bind, padCells_counted]
    refine bind_congr fun r => ?_
    by_cases hpart : ∃ i, i ∉ D.1 ∧ d i = none
    · rw [ite_eq_left hpart, ite_eq_left hpart, simulateQ_pure]
    rw [ite_eq_right hpart, ite_eq_right hpart, simulateQ_bind, simulateQ_sequenceFin]
    congr 1
    congr 1
    funext j
    by_cases hj : j ∈ D.1
    · simp [hj]
    · simp only [hj, ite_false]
      rcases d j with _ | x
      · simp
      · dsimp only
        split_ifs
        · simp
        · rw [padCells_free]

/-- The commitments with the pad of their cells. -/
def padCF (c : C.Party → List HashOutput) : C.Party → List HashOutput :=
  fun i => List.zipWith (fun j a => padAdjF (pairFamily D commitAt) π (commitAt i j) a) C.parties (c i)

theorem commitDrawsAt_padCells :
    simulateQ (padCells (pairFamily D commitAt) π) (commitDrawsAt D commitAt) =
      padCF D commitAt π <$> commitDrawsAt D commitAt := by
  unfold commitDrawsAt
  rw [simulateQ_sequenceFin, map_eq_bind_pure_comp,
    show (pure ∘ padCF D commitAt π : (C.Party → List HashOutput) → OracleComp (WorldSpec C) _) =
      fun rs => pure fun i => (fun i r => List.zipWith (fun j a => padAdjF (pairFamily D commitAt) π (commitAt i j) a)
        C.parties r) i (rs i) from rfl, ← sequenceFin_bind_pure]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi]
  · simp only [hi, ite_false, padCells_free, localPadF_liftComp, roPadF_mapM, liftComp_map]
    unfold free
    rw [simulateQ_map, map_eq_bind_pure_comp]
    rfl

theorem length_commitDrawsAt (c : C.Party → List HashOutput) (hc : c ∈ support (commitDrawsAt D commitAt)) (i : C.Party)
    (hi : i ∉ D.1) : (c i).length = C.parties.length := by
  have h := mem_support_sequenceFin_oc _ c hc i
  simp only [hi, ite_false] at h
  have h1 := support_simulateQ_subset _ _ h
  rw [support_liftComp] at h1
  exact length_of_mem_support_mapM _ _ _ h1

theorem not_family_corrupt (hshape : CommitShape commitAt) {q : Query C} (hq : InFamily (pairFamily D commitAt) q)
    {i j : C.Party} {r : List HashOutput} (e : q = .commit .seedGen i j r) : i ∉ D.1 ∧ j ∉ D.1 := by
  obtain ⟨p, rfl⟩ := hq
  obtain ⟨i', j', r', hi, hj, e'⟩ := pairFamily_pairCell D commitAt hshape p
  rw [e'] at e
  simp only [Query.commit.injEq, true_and] at e
  obtain ⟨rfl, rfl, -⟩ := e
  exact ⟨hi, hj⟩

theorem deriveAt_roPadF (hshape : CommitShape commitAt) (parts : C.Party → Parts C)
    (termAt : C.Party → Mail C E → C.Term → Query C) (hterm : ∀ i inbox T, ¬ InFamily (pairFamily D commitAt) (termAt i inbox T))
    (i : C.Party) (inbox : Mail C E) :
    simulateQ (roPadF (pairFamily D commitAt) π) (deriveAt D parts termAt i inbox) = deriveAt D parts termAt i inbox := by
  have hd : ∀ kind l, ¬ InFamily (pairFamily D commitAt) (Query.derive .seedGen kind l) := fun kind l =>
    not_family_of_not_commit D hshape fun _ _ _ h => by cases h
  unfold deriveAt
  simp only [simulateQ_bind, simulateQ_pure, roPadF_hashQuery_of_not _ _ _ (hd _ _), simulateQ_list_mapM,
    apply_ite (simulateQ (roPadF (pairFamily D commitAt) π)), apply_dite (simulateQ (roPadF (pairFamily D commitAt) π)),
    roPadF_hashQuery_of_not _ _ _ (hterm _ _ _)]

theorem revealNextAt_padCells (hshape : CommitShape commitAt) (parts : C.Party → Parts C)
    (termAt : C.Party → Mail C E → C.Term → Query C) (hterm : ∀ i inbox T, ¬ InFamily (pairFamily D commitAt) (termAt i inbox T))
    (c : C.Party → List HashOutput) (hc : ∀ k, k ∉ D.1 → (c k).length = C.parties.length)
    (sent : C.Party → C.Party → Option (Msg E)) (j : C.Party) (inbox : Mail C E) :
    simulateQ (localPadF (pairFamily D commitAt) π)
        (revealNextAt D parts commitAt termAt (commitInbox D (padCF D commitAt π c) sent) j inbox) =
      revealNextAt D parts commitAt termAt (commitInbox D c sent) j inbox := by
  unfold revealNextAt
  rw [simulateQ_bind, localPadF_liftComp, roPadF_mapM, liftComp_map, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun opens hopens => ?_
  rw [support_liftComp] at hopens
  have hlen := length_of_mem_support_mapM _ _ _ hopens
  have hcheck : openCheck .seedGen j (parts j) (commitInbox D (padCF D commitAt π c) sent j)
      (normRevealed D parts j inbox)
      (List.zipWith (fun k a => padAdjF (pairFamily D commitAt) π
        (if k ∈ D.1 ∨ k = j then openAddress D parts j inbox k else commitAt k j) a) C.parties opens) ↔
      openCheck .seedGen j (parts j) (commitInbox D c sent j) (normRevealed D parts j inbox) opens := by
    unfold openCheck
    refine forall_congr' fun k => imp_congr_right fun hkj => and_congr_right fun _ => ?_
    rw [getD_zipWith_parties _ _ hlen]
    by_cases hk : k ∈ D.1
    · have hnf : ¬ InFamily (pairFamily D commitAt) (openAddress D parts j inbox k) := fun hf =>
        (not_family_corrupt D commitAt hshape hf (openAddress_corrupt D parts j k inbox hk)).1 hk
      simp only [hk, true_or, ite_true, padAdjF_of_not _ _ hnf, commitInbox]
    · have hck := hc k hk
      simp only [hk, false_or, Ne.symm hkj, ite_false, commitInbox, commitOutbox, hkj, Msg.hashesOf, padCF,
        getD_zipWith_parties _ _ hck, List.cons.injEq, and_true]
      exact padAdjF_inj _ _ _ _ _
  by_cases h : openCheck .seedGen j (parts j) (commitInbox D c sent j) (normRevealed D parts j inbox) opens
  · rw [ite_eq_left (hcheck.2 h), ite_eq_left h]
    have hsk : ∀ l, ¬ InFamily (pairFamily D commitAt) (Query.sharedKeys .seedGen l) := fun l =>
      not_family_of_not_commit D hshape fun _ _ _ h => by cases h
    simp only [simulateQ_bind, simulateQ_pure, localPadF_liftComp,
      deriveAt_roPadF D commitAt π hshape parts termAt hterm, simulateQ_list_mapM, sharedAddress,
      roPadF_hashQuery_of_not _ _ _ (hsk _)]
  · rw [ite_eq_right (fun h' => h (hcheck.1 h')), ite_eq_right h]
    simp

theorem programBlock_padCells (log : CallLog C) (sent : C.Party → C.Party → Option (Msg E))
    (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    simulateQ (padCells (pairFamily D commitAt) π) (programBlock D log sent parameter dealt parts) =
      programBlock D log sent parameter dealt parts := by
  have hprog : ∀ (q : Query C) (v : HashOutput), simulateQ (padCells (pairFamily D commitAt) π) (program q v) =
      program q v := fun q v => padCells_counted _ π _
  rw [programBlock_eq_view]
  simp only [programBlockView, simulateQ_bind, simulateQ_pure, simulateQ_list_mapM, padCells_free,
    localPadF_liftComp_prob, hprog, apply_dite (simulateQ (padCells (pairFamily D commitAt) π))]
  refine bind_congr fun high => bind_congr fun _ => ?_
  congr 1
  congr 1
  funext T
  split <;> simp [hprog]

/-- The pad of the honest pair cells does not change the seed generation with the commit cells
`commitAt`. -/
theorem seedGenAt_padCells (hshape : CommitShape commitAt) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (termAt : C.Party → Mail C E → C.Term → Query C) (hterm : ∀ i inbox T, ¬ InFamily (pairFamily D commitAt) (termAt i inbox T)) :
    simulateQ (padCells (pairFamily D commitAt) π) (seedGenAt D net state early parameter dealt parts commitAt termAt) =
      seedGenAt D net state early parameter dealt parts commitAt termAt := by
  unfold seedGenAt
  simp only [simulateQ_bind]
  rw [commitDrawsAt_padCells, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun c hc => ?_
  have hlen := length_commitDrawsAt D commitAt c hc
  have hmail : commitMail (E := E) D (padCF D commitAt π c) = commitMail D c := by
    funext x i
    unfold commitMail
    split_ifs with h
    · have hxi : x ≠ i := fun e => h.2 (e ▸ h.1)
      obtain ⟨r, -, hcr⟩ := hshape i x
      have hnf : ¬ InFamily (pairFamily D commitAt) (commitAt i x) := fun hf =>
        (not_family_corrupt D commitAt hshape hf hcr).2 h.1
      simp only [commitOutbox, hxi, ite_false, padCF, getD_zipWith_parties _ _ (hlen i h.2), padAdjF_of_not _ _ hnf]
    · rfl
  have hready : ∀ sent : C.Party → C.Party → Option (Msg E),
      revealReady (commitInbox D (padCF D commitAt π c) sent) = revealReady (commitInbox D c sent) := by
    intro sent
    funext i
    have hk : ∀ k, Msg.isAbort (commitInbox D (padCF D commitAt π c) sent i k) =
        Msg.isAbort (commitInbox D c sent i k) := by
      intro k
      unfold commitInbox
      split_ifs
      · rfl
      · unfold commitOutbox
        split_ifs <;> rfl
    unfold revealReady anyAbort
    simp only [hk]
  rw [hmail, observe_eq, show simulateQ (padCells (pairFamily D commitAt) π)
      (worldRoles.adversary (logged (net.round state (commitMail D c)))) =
    worldRoles.adversary (logged (net.round state (commitMail D c))) from padCells_counted _ π _]
  refine bind_congr fun r => ?_
  rw [programBlock_padCells]
  refine bind_congr fun _ => ?_
  rw [levelRound_padCells, hready]
  refine (levelRound_congr_next D net _ _ _ _ _ _ _ fun sent j x hj _ _ _ =>
    revealNextAt_padCells D commitAt π hshape parts termAt hterm c hlen _ j _).trans ?_
  refine levelRound_congr D net _ _ _ _ _ _ _ fun f2 s2 d2 => ?_
  rw [levelRound_padCells]
  simp only [echoNext, simulateQ_pure]
  rfl

theorem padCells_of_noCall (hshape : CommitShape commitAt) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (h : NoCall SeedGenCell oa) : simulateQ (padCells (pairFamily D commitAt) π) oa = oa := by
  rw [noCall_iff] at h
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    obtain ⟨ht, hk⟩ := h
    have ht' : ¬ SeedGenCell t := by simpa using ht
    have e : padCells (pairFamily D commitAt) π t = query (spec := WorldSpec C) t := by
      rcases t with ((n | q | x) | p) | (n | q | x)
      all_goals try rfl
      have hq : ¬ InFamily (pairFamily D commitAt) q := fun hf => by
        obtain ⟨p, rfl⟩ := hf
        obtain ⟨i, j, r, -, -, e⟩ := pairFamily_pairCell D commitAt hshape p
        exact ht' ⟨_, rfl, by rw [e]; rfl⟩
      simp only [padCells, hq, dite_false]
      rfl
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, e]
    refine bind_congr fun u => ih u ?_
    simpa [ht'] using hk u

end Walk

section Suffix

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
/-- The pad of the honest pair cells does not change the suffix with the commit cells `commitAt`. -/
theorem suffixAt_padCells (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State)
    (commitAt : C.Party → C.Party → Query C) (hshape : CommitShape commitAt)
    (termAt : C.Party → Mail C E → C.Term → Query C) (hterm : ∀ i inbox T, ¬ InFamily (pairFamily D commitAt) (termAt i inbox T))
    (π : PairIndex C D → HashOutput) :
    simulateQ (padCells (pairFamily D commitAt) π) (suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x commitAt termAt) =
      suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x commitAt termAt := by
  unfold suffixAt
  simp only [simulateQ_bind]
  rw [seedGenAt_padCells D commitAt π hshape A.net _ _ _ _ _ termAt hterm]
  refine bind_congr fun y => ?_
  rcases y with ⟨state, emu⟩
  dsimp only
  rw [padCells_of_noCall D commitAt π hshape _ (noCall_secRest_seedGenCell K circuits settings runLimit D
    ⟨true, fun _ => 0⟩ (fun _ => rfl) A _ _ _ _ _)]
  simp

omit [Fintype E] [DecidableEq E] in
/-- The proof of `ShiftPad`. -/
theorem shiftPad : ShiftPad K circuits settings runLimit := by
  intro D A x T δ hT π
  exact suffixAt_padCells K circuits settings runLimit D A x _ (commitShape_commitAddress _) _
    (fun _ _ _ => not_family_of_not_commit D (commitShape_commitAddress _) fun _ _ _ h => by cases h) π

omit [Fintype E] [DecidableEq E] in
/-- The proof of `PartsStep`. -/
theorem partsStep : PartsStep prims K circuits settings runLimit :=
  partsStep_of_sides prims K circuits settings runLimit
    (commitSide_of_shift prims K circuits settings runLimit
      (commitShift_of_pad prims K circuits settings runLimit (shiftPad K circuits settings runLimit)))
    (deriveSide prims K circuits settings runLimit)

end Suffix

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.shiftPad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.shiftPad

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.partsStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.partsStep
