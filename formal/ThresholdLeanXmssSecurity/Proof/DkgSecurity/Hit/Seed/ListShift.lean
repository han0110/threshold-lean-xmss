import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.CompHit
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.RestEmu

/-!
# The common shift of the hidden seeds in the list program

`listShift` proves `ListShift`. The free calls of `H` at a hidden cell in the list program are only
the derive calls of the held terms whose derive address is a hidden cell. So `shiftFreeHidden`
changes no counted call, no commit or open call, no derive call of `P` or of a pair and no shared key
call. It shifts the seed of each held term whose derive address is a hidden cell, and this is
`shiftKeysHidden`. The rest of the game asks no free cell of the seed generation.

* `localShiftP P δ` and `roShiftP P δ` shift the answer of each call of `H` at a cell in `P` by `δ`,
  on the local oracles and on the random oracles of one operator. They shift a set of cells in the
  place of one cell.
* `simulateQ_eq_self_of_noCall` states that a change of the calls in a set `P` does not change a
  program with no call in `P`.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## A change of the calls outside a program -/

/-- A change of the calls in the set `P` does not change a program with no call in `P`. -/
theorem simulateQ_eq_self_of_noCall {ι : Type} {spec : OracleSpec ι} (P : ι → Prop)
    (impl : QueryImpl spec (OracleComp spec)) (himpl : ∀ t, ¬ P t → impl t = liftM (OracleSpec.query t))
    {α : Type} (X : OracleComp spec α) (h : NoCall P X) : simulateQ impl X = X := by
  rw [noCall_iff] at h
  induction X using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ P t := h.1.resolve_right (by omega)
    rw [simulateQ_bind, simulateQ_spec_query, himpl t ht]
    exact bind_congr fun u => ih u (by simpa [ht] using h.2 u)

/-! ## The shift on a set of cells -/

section Local

variable (P : Query C → Prop) (δ : HashOutput)

/-- The local oracles with the answer of each call of `H` at a cell in `P` shifted by `δ`. -/
def localShiftP : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)) := fun t =>
  match t with
  | .inr (.inl q') =>
      if P q' then
        (fun a => a ^^^ δ) <$> (liftM (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q'))) :
          OracleComp (LocalSpec C) HashOutput)
      else liftM (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q')))
  | t => liftM (OracleSpec.query t)

/-- The random oracles with the answer of each call of `H` at a cell in `P` shifted by `δ`. -/
def roShiftP : QueryImpl (RoSpec C) (OracleComp (RoSpec C)) := fun t =>
  match t with
  | .inl q' =>
      if P q' then
        (fun a => a ^^^ δ) <$> (liftM (OracleSpec.query (spec := RoSpec C) (.inl q')) : OracleComp (RoSpec C) HashOutput)
      else liftM (OracleSpec.query (spec := RoSpec C) (.inl q'))
  | t => liftM (OracleSpec.query t)

theorem localShiftP_liftComp {α : Type} (oa : OracleComp (RoSpec C) α) :
    simulateQ (localShiftP P δ) (liftComp oa (LocalSpec C)) = liftComp (simulateQ (roShiftP P δ) oa) (LocalSpec C) := by
  rw [liftComp_def, liftComp_def, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with q' | x
  · change simulateQ (localShiftP P δ) (liftM (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q')))) =
      simulateQ (fun t => liftM (OracleSpec.query (spec := RoSpec C) t)) (roShiftP P δ (.inl q'))
    by_cases h : P q'
    · simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, localShiftP, roShiftP, h,
        ite_true, simulateQ_map]
      rfl
    · simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, localShiftP, roShiftP, h,
        ite_false]
      rfl
  · change simulateQ (localShiftP P δ) (liftM (OracleSpec.query (spec := LocalSpec C) (.inr (.inr x)))) =
      simulateQ (fun t => liftM (OracleSpec.query (spec := RoSpec C) t)) (roShiftP P δ (.inr x))
    simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, localShiftP, roShiftP]
    rfl

theorem localShiftP_liftComp_prob {α : Type} (oa : ProbComp α) :
    simulateQ (localShiftP P δ) (liftComp oa (LocalSpec C)) = liftComp oa (LocalSpec C) := by
  rw [liftComp_def]
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  change simulateQ (localShiftP P δ) (liftM (OracleSpec.query (spec := LocalSpec C) (.inl t))) = _
  simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, localShiftP]
  rfl

theorem roShiftP_hashQuery_ne (q : Query C) (h : ¬ P q) : simulateQ (roShiftP P δ) (hashQuery q) = hashQuery q := by
  simp [hashQuery, roShiftP, h]

theorem roShiftP_hashQuery_eq (q : Query C) (h : P q) :
    simulateQ (roShiftP P δ) (hashQuery q) = (fun a => a ^^^ δ) <$> hashQuery q := by
  simp [hashQuery, roShiftP, h]

theorem roShiftP_mapM_ne {α : Type} (l : List α) (addr : α → Query C) (h : ∀ x, ¬ P (addr x)) :
    simulateQ (roShiftP P δ) (l.mapM fun x => hashQuery (addr x)) = l.mapM fun x => hashQuery (addr x) := by
  rw [simulateQ_list_mapM]
  congr 1
  funext x
  exact roShiftP_hashQuery_ne P δ (addr x) (h x)

end Local

/-! ## The world shift on the copies -/

section World

variable (D : C.Coalition) (parts : C.Party → Parts C) (δ : HashOutput)

theorem hiddenCell_derive {q : Query C} (h : HiddenCell D parts q) : ∃ L, q = .derive .seedGen .term L := by
  obtain ⟨T, -, rfl⟩ := h
  exact ⟨_, rfl⟩

theorem not_hiddenCell_commit (k i : C.Party) (L : List HashOutput) : ¬ HiddenCell D parts (.commit .seedGen k i L) :=
  fun h => by obtain ⟨_, e⟩ := hiddenCell_derive D parts h; cases e

theorem not_hiddenCell_shared (L : List HashOutput) : ¬ HiddenCell D parts (.sharedKeys .seedGen L) :=
  fun h => by obtain ⟨_, e⟩ := hiddenCell_derive D parts h; cases e

theorem not_hiddenCell_parameter (L : List HashOutput) : ¬ HiddenCell D parts (.derive .seedGen .parameter L) :=
  fun h => by obtain ⟨_, e⟩ := hiddenCell_derive D parts h; cases e

theorem not_hiddenCell_pair (L : List HashOutput) : ¬ HiddenCell D parts (.derive .seedGen .pair L) :=
  fun h => by obtain ⟨_, e⟩ := hiddenCell_derive D parts h; cases e

theorem shiftFreeHidden_counted {α : Type} (oa : OracleComp (SimulatorSpec C) α) :
    simulateQ (shiftFreeHidden D parts δ) (counted oa) = counted oa :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => by simp [shiftFreeHidden]) oa

theorem shiftFreeHidden_free {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (shiftFreeHidden D parts δ) (free oa) = free (simulateQ (localShiftP (HiddenCell D parts) δ) oa) := by
  unfold free
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with n | q' | x
  · simp [shiftFreeHidden, localShiftP]
  · by_cases h : HiddenCell D parts q' <;> simp [shiftFreeHidden, localShiftP, h]
  · simp [shiftFreeHidden, localShiftP]

theorem shiftFreeHidden_observe {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (shiftFreeHidden D parts δ) (observe oa) = observe oa := by
  rw [observe_eq]
  exact shiftFreeHidden_counted D parts δ _

/-- `shiftFreeHidden` changes only free calls at a cell of the seed generation. -/
theorem shiftFreeHidden_of_not_seedGenCell (t : (WorldSpec C).Domain) (ht : ¬ SeedGenCell t) :
    shiftFreeHidden D parts δ t = liftM (OracleSpec.query t) := by
  rcases t with ((n | q | x) | p) | (n | q | x)
  rotate_left 5
  · have hq : ¬ HiddenCell D parts q := fun h => by
      obtain ⟨L, rfl⟩ := hiddenCell_derive D parts h
      exact ht ⟨_, rfl, rfl⟩
    simp only [shiftFreeHidden, hq, ↓reduceIte]
  all_goals rfl

theorem levelRound_shiftFreeHidden (net : Adversary C E Unit PEmpty PEmpty) {X Y β : Type}
    (fuel : ℕ) (state : net.State) (d : C.Party → Option X)
    (out : C.Party → X → Mail C E) (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β))) :
    simulateQ (shiftFreeHidden D parts δ) (levelRound D net fuel state d out next cont) =
      levelRound D net fuel state d out (fun j x inbox => simulateQ (localShiftP (HiddenCell D parts) δ) (next j x inbox))
        (fun f s d' => simulateQ (shiftFreeHidden D parts δ) (cont f s d')) := by
  cases fuel with
  | zero => simp [levelRound]
  | succ fuel =>
    rw [levelRound, levelRound]
    by_cases hall : ∀ i, i ∉ D.1 → d i = none
    · rw [ite_eq_left hall, ite_eq_left hall, simulateQ_pure]
    rw [ite_eq_right hall, ite_eq_right hall, simulateQ_bind, shiftFreeHidden_counted]
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
        · rw [shiftFreeHidden_free]

theorem commitDraws_shiftFreeHidden (parts' : C.Party → Parts C) :
    simulateQ (shiftFreeHidden D parts δ) (commitDraws D parts') = commitDraws D parts' := by
  unfold commitDraws
  rw [simulateQ_sequenceFin]
  congr 1
  funext i
  split_ifs
  · simp
  · rw [shiftFreeHidden_free, localShiftP_liftComp,
      roShiftP_mapM_ne _ _ _ (fun j => commitAddress parts' i j) fun j => not_hiddenCell_commit D parts _ _ _]

theorem programBlock_shiftFreeHidden (log : CallLog C) (sent : C.Party → C.Party → Option (Msg E))
    (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts' : C.Party → Parts C) :
    simulateQ (shiftFreeHidden D parts δ) (programBlock D log sent parameter dealt parts') =
      programBlock D log sent parameter dealt parts' := by
  have hprog : ∀ (q' : Query C) (v : HashOutput),
      simulateQ (shiftFreeHidden D parts δ) (program q' v) = program q' v :=
    fun _ _ => shiftFreeHidden_counted D parts δ _
  rw [programBlock_eq_view]
  simp only [programBlockView, simulateQ_bind, simulateQ_pure, simulateQ_list_mapM, shiftFreeHidden_free,
    localShiftP_liftComp_prob, hprog, apply_dite (simulateQ (shiftFreeHidden D parts δ))]
  refine bind_congr fun high => bind_congr fun _ => ?_
  congr 1
  congr 1
  funext T
  split <;> simp [hprog]

end World

/-! ## The derive calls and the local steps -/

section Steps

variable (D : C.Coalition) (parts : C.Party → Parts C) (δ : HashOutput)

/-- The derive calls of operator `i` under `roShiftP (HiddenCell D parts) δ` give the keys with the
seed of each held term whose derive address is a hidden cell shifted. -/
theorem deriveKeys_roShiftHidden (i : C.Party) (inbox : Mail C E) :
    simulateQ (roShiftP (HiddenCell D parts) δ) (deriveKeys .seedGen i (normView D parts i inbox)) =
      shiftKeysHidden D parts δ i inbox <$> deriveKeys .seedGen i (normView D parts i inbox) := by
  set P : Query C → Prop := HiddenCell D parts
  let adj : C.Term → HashOutput → HashOutput := fun T a =>
    if i ∈ C.holders T ∧ P (termAddress D parts i inbox T) then a ^^^ δ else a
  let g : C.Term → OracleComp (RoSpec C) HashOutput := fun T =>
    if i ∈ C.holders T then hashQuery (termAddress D parts i inbox T) else pure 0
  have hterm : (fun T => simulateQ (roShiftP P δ) (g T)) = fun T => adj T <$> g T := by
    funext T
    by_cases hiT : i ∈ C.holders T
    · by_cases hq : P (termAddress D parts i inbox T)
      · simp only [g, adj, hiT, hq, ite_true, and_self]
        rw [roShiftP_hashQuery_eq _ _ _ hq]
      · simp only [g, adj, hiT, hq, ite_true, and_false, ite_false, id_map']
        rw [roShiftP_hashQuery_ne _ _ _ hq]
    · simp [g, adj, hiT]
  have hpar : simulateQ (roShiftP P δ) (hashQuery (C := C) (.derive .seedGen .parameter
      (C.parties.map fun k => (normView D parts i inbox k).parameter))) =
      hashQuery (.derive .seedGen .parameter (C.parties.map fun k => (normView D parts i inbox k).parameter)) :=
    roShiftP_hashQuery_ne _ _ _ (not_hiddenCell_parameter D parts _)
  rw [deriveKeys_normView]
  simp only [simulateQ_bind, simulateQ_pure, map_bind, map_pure]
  rw [hpar]
  refine bind_congr fun parameter => ?_
  change simulateQ (roShiftP P δ) (C.terms.mapM g) >>= _ = C.terms.mapM g >>= _
  rw [simulateQ_list_mapM, hterm, mapM_map_zipWith, bind_map_left]
  refine bind_congr_of_forall_mem_support _ fun r hr => ?_
  have hlen := length_of_mem_support_mapM g C.terms r hr
  rw [simulateQ_list_mapM]
  have hpairs : (fun j => simulateQ (roShiftP P δ) (if h : j = i then (pure 0 : OracleComp (RoSpec C) HashOutput) else
      hashQuery (.derive .seedGen .pair
        [(normView D parts i inbox (C.pairOf i j (Ne.symm h)).1.1).pair (C.pairOf i j (Ne.symm h)).1.2,
          (normView D parts i inbox (C.pairOf i j (Ne.symm h)).1.2).pair (C.pairOf i j (Ne.symm h)).1.1]))) =
      fun j => if h : j = i then pure 0 else
      hashQuery (.derive .seedGen .pair
        [(normView D parts i inbox (C.pairOf i j (Ne.symm h)).1.1).pair (C.pairOf i j (Ne.symm h)).1.2,
          (normView D parts i inbox (C.pairOf i j (Ne.symm h)).1.2).pair (C.pairOf i j (Ne.symm h)).1.1]) := by
    funext j
    split_ifs with h
    · simp
    · exact roShiftP_hashQuery_ne _ _ _ (not_hiddenCell_pair D parts _)
  rw [hpairs]
  refine bind_congr fun pair => ?_
  congr 1
  unfold shiftKeysHidden
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  funext T
  have hT : T ∈ C.terms := by simp [Committee.terms]
  exact getD_zipWith_idxOf adj C.terms r 0 hlen T hT

/-- The local step after round 2 of the list program under the shift. -/
theorem revealNextList_shift (committed : C.Party → Mail C E) (i : C.Party) (inbox : Mail C E) :
    simulateQ (localShiftP (HiddenCell D parts) δ) (revealNextList D parts (fun _ _ keys => keys) committed i inbox) =
      revealNextList D parts (shiftKeysHidden D parts δ) committed i inbox := by
  unfold revealNextList
  rw [simulateQ_bind, localShiftP_liftComp,
    roShiftP_mapM_ne _ _ _ _ fun k => by simp only [openAddress]; exact not_hiddenCell_commit D parts _ _ _]
  refine bind_congr fun opens => ?_
  split_ifs
  · simp only [simulateQ_bind, simulateQ_pure, localShiftP_liftComp, deriveKeys_roShiftHidden]
    rw [liftComp_map, bind_map_left]
    refine bind_congr fun keys => ?_
    have hs : simulateQ (roShiftP (HiddenCell D parts) δ) (C.parties.mapM fun j =>
        if SharesHidden D i j then (pure 0 : OracleComp (RoSpec C) HashOutput) else
          hashQuery (sharedAddress i j (shiftKeysHidden D parts δ i inbox keys).2.1)) =
        C.parties.mapM fun j => if SharesHidden D i j then (pure 0 : OracleComp (RoSpec C) HashOutput) else
          hashQuery (sharedAddress i j (shiftKeysHidden D parts δ i inbox keys).2.1) := by
      rw [simulateQ_list_mapM]
      congr 1
      funext j
      split_ifs
      · simp
      · exact roShiftP_hashQuery_ne _ _ _ (not_hiddenCell_shared D parts _)
    rw [hs]
  · simp

end Steps

/-! ## The statement -/

section Statement

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The seed generation of the list program under the shift. -/
theorem seedGenList_shift (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (δ : HashOutput) :
    simulateQ (shiftFreeHidden D parts δ) (seedGenList D net state early parameter dealt parts (fun _ _ keys => keys)) =
      seedGenList D net state early parameter dealt parts (shiftKeysHidden D parts δ) := by
  unfold seedGenList
  simp only [simulateQ_bind]
  rw [commitDraws_shiftFreeHidden]
  refine bind_congr fun commitments => ?_
  rw [shiftFreeHidden_observe]
  refine bind_congr fun r => ?_
  rw [programBlock_shiftFreeHidden]
  refine bind_congr fun _ => ?_
  rw [levelRound_shiftFreeHidden]
  congr 1
  · funext j x inbox
    exact revealNextList_shift D parts δ _ j inbox
  · funext f2 s2 d2
    rw [levelRound_shiftFreeHidden]
    congr 1

omit [Fintype E] [DecidableEq E] in
/-- The proof of `ListShift`. -/
theorem listShift : ListShift K circuits settings runLimit := by
  intro D A x δ
  unfold listSuffix
  rw [simulateQ_bind, seedGenList_shift]
  refine bind_congr fun p => ?_
  rcases p with ⟨state, emu⟩
  dsimp only
  rw [simulateQ_bind, simulateQ_eq_self_of_noCall SeedGenCell _ (shiftFreeHidden_of_not_seedGenCell D x.2.2 δ) _
    (noCall_secRest_seedGenCell K circuits settings runLimit D ⟨true, fun _ => 0⟩ (fun _ => rfl) A _ _ _ _ _)]
  refine bind_congr fun win => ?_
  simp

end Statement

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.listShift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.listShift
