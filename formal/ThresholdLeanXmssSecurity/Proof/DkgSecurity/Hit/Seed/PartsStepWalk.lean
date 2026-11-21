import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.PartsStep

/-!
# A rewrite of the cells of the free calls through `suffixAt`

`cellRw f` is the rewrite of a run where each free call of `H` at a cell `q` asks the cell `f q`.

* `suffixAt_cellRw` states that the rewrite of `suffixAt` with the commit addresses `commitAt` and the
  derive addresses `termAt` is `suffixAt` with `f ∘ commitAt` and `f ∘ termAt`, when `f` keeps the open
  cells of the corrupt senders and of the operator itself, the derive cells of `P` and of the pairs,
  the shared key cells and each cell out of the class of the seed generation.
* `markTo X` sends `markCell` to `X` and keeps each other cell. `suffixAt_markTo` states that the rewrite
  by `markTo` of the shifted hidden cell sends the suffix of `partsRef` to the suffix of `pairRun`.
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

/-! ## The rewrite on the three oracle sets -/

section Rewrite

variable (f : Query C → Query C)

/-- Each free call of `H` at the cell `q` asks the cell `f q`. Each other call goes on as it is. -/
def cellRw : QueryImpl (WorldSpec C) (OracleComp (WorldSpec C)) := fun t =>
  match t with
  | .inr (.inr (.inl q)) =>
      (liftM (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inl (f q))))) : OracleComp (WorldSpec C) HashOutput)
  | t => liftM (OracleSpec.query t)

/-- The rewrite on the local oracles. -/
def localRw : QueryImpl (LocalSpec C) (OracleComp (LocalSpec C)) := fun t =>
  match t with
  | .inr (.inl q) =>
      (liftM (OracleSpec.query (spec := LocalSpec C) (.inr (.inl (f q)))) : OracleComp (LocalSpec C) HashOutput)
  | t => liftM (OracleSpec.query t)

/-- The rewrite on the random oracles. -/
def roRw : QueryImpl (RoSpec C) (OracleComp (RoSpec C)) := fun t =>
  match t with
  | .inl q => (liftM (OracleSpec.query (spec := RoSpec C) (.inl (f q))) : OracleComp (RoSpec C) HashOutput)
  | t => liftM (OracleSpec.query t)

theorem cellRw_counted {α : Type} (oa : OracleComp (SimulatorSpec C) α) :
    simulateQ (cellRw f) (counted oa) = counted oa :=
  QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => by simp [cellRw]) oa

theorem cellRw_free {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (cellRw f) (free oa) = free (simulateQ (localRw f) oa) := by
  unfold free
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with n | q | x
  · simp [cellRw, localRw]
  · simp [cellRw, localRw]
  · simp [cellRw, localRw]

theorem localRw_liftComp {α : Type} (oa : OracleComp (RoSpec C) α) :
    simulateQ (localRw f) (liftComp oa (LocalSpec C)) = liftComp (simulateQ (roRw f) oa) (LocalSpec C) := by
  rw [liftComp_def, liftComp_def, ← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  congr 1
  funext t
  rcases t with q | x
  · change simulateQ (localRw f) (liftM (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q)))) =
      simulateQ (fun t => liftM (OracleSpec.query (spec := RoSpec C) t)) (roRw f (.inl q))
    simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, localRw, roRw]
    rfl
  · change simulateQ (localRw f) (liftM (OracleSpec.query (spec := LocalSpec C) (.inr (.inr x)))) =
      simulateQ (fun t => liftM (OracleSpec.query (spec := RoSpec C) t)) (roRw f (.inr x))
    simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, localRw, roRw]
    rfl

theorem localRw_liftComp_prob {α : Type} (oa : ProbComp α) :
    simulateQ (localRw f) (liftComp oa (LocalSpec C)) = liftComp oa (LocalSpec C) := by
  rw [liftComp_def]
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun t => ?_) oa
  change simulateQ (localRw f) (liftM (OracleSpec.query (spec := LocalSpec C) (.inl t))) = _
  simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, localRw]
  rfl

theorem roRw_hashQuery (q : Query C) : simulateQ (roRw f) (hashQuery q) = hashQuery (f q) := by
  simp [hashQuery, roRw]

theorem roRw_mapM {α : Type} (l : List α) (addr : α → Query C) :
    simulateQ (roRw f) (l.mapM fun x => hashQuery (addr x)) = l.mapM fun x => hashQuery (f (addr x)) := by
  rw [simulateQ_list_mapM]
  simp only [roRw_hashQuery]

/-- The rewrite does not change a program with no free call in the class of the seed generation, when
`f` keeps each cell out of this class. -/
theorem cellRw_of_noCall (hrest : ∀ q, isSeedGenQuery q = false → f q = q) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (h : NoCall SeedGenCell oa) : simulateQ (cellRw f) oa = oa := by
  rw [noCall_iff] at h
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    obtain ⟨ht, hk⟩ := h
    have ht' : ¬ SeedGenCell t := by simpa using ht
    have e : cellRw f t = query (spec := WorldSpec C) t := by
      rcases t with ((n | q | x) | p) | (n | q | x)
      all_goals try rfl
      have hq : isSeedGenQuery q = false := by
        cases hq : isSeedGenQuery q
        · rfl
        · exact absurd ⟨q, rfl, hq⟩ ht'
      change (liftM (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inl (f q))))) :
        OracleComp (WorldSpec C) HashOutput) = _
      rw [hrest q hq]
      rfl
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map, e]
    refine bind_congr fun u => ih u ?_
    simpa [ht'] using hk u

end Rewrite

/-! ## The rewrite through the seed generation -/

section Walk

variable (f : Query C → Query C) (D : C.Coalition)

theorem levelRound_cellRw (net : Adversary C E Unit PEmpty PEmpty) {X Y β : Type} (fuel : ℕ) (state : net.State)
    (d : C.Party → Option X) (out : C.Party → X → Mail C E)
    (next : C.Party → X → Mail C E → OracleComp (LocalSpec C) (Option Y))
    (cont : ℕ → net.State → (C.Party → Option Y) → OracleComp (WorldSpec C) (net.State × (C.Party → Option β))) :
    simulateQ (cellRw f) (levelRound D net fuel state d out next cont) =
      levelRound D net fuel state d out (fun j x inbox => simulateQ (localRw f) (next j x inbox))
        (fun f' s d' => simulateQ (cellRw f) (cont f' s d')) := by
  cases fuel with
  | zero => simp [levelRound]
  | succ fuel =>
    rw [levelRound, levelRound]
    by_cases hall : ∀ i, i ∉ D.1 → d i = none
    · rw [ite_eq_left hall, ite_eq_left hall, simulateQ_pure]
    rw [ite_eq_right hall, ite_eq_right hall, simulateQ_bind, cellRw_counted]
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
        · rw [cellRw_free]

theorem commitDrawsAt_cellRw (commitAt : C.Party → C.Party → Query C) :
    simulateQ (cellRw f) (commitDrawsAt D commitAt) = commitDrawsAt D fun i j => f (commitAt i j) := by
  unfold commitDrawsAt
  rw [simulateQ_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi]
  · simp only [hi, ite_false, cellRw_free, localRw_liftComp, roRw_mapM]

theorem programBlock_cellRw (log : CallLog C) (sent : C.Party → C.Party → Option (Msg E))
    (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C) :
    simulateQ (cellRw f) (programBlock D log sent parameter dealt parts) = programBlock D log sent parameter dealt parts := by
  have hprog : ∀ (q : Query C) (v : HashOutput), simulateQ (cellRw f) (program q v) = program q v :=
    fun q v => cellRw_counted f _
  rw [programBlock_eq_view]
  simp only [programBlockView, simulateQ_bind, simulateQ_pure, simulateQ_list_mapM, cellRw_free,
    localRw_liftComp_prob, hprog, apply_dite (simulateQ (cellRw f))]
  refine bind_congr fun high => bind_congr fun _ => ?_
  congr 1
  congr 1
  funext T
  split <;> simp [hprog]

theorem deriveAt_roRw (parts : C.Party → Parts C) (termAt : C.Party → Mail C E → C.Term → Query C) (i : C.Party)
    (inbox : Mail C E) (hparam : ∀ l, f (.derive .seedGen .parameter l) = .derive .seedGen .parameter l)
    (hpair : ∀ l, f (.derive .seedGen .pair l) = .derive .seedGen .pair l) :
    simulateQ (roRw f) (deriveAt D parts termAt i inbox) = deriveAt D parts (fun i inbox T => f (termAt i inbox T)) i inbox := by
  unfold deriveAt
  simp only [simulateQ_bind, simulateQ_pure, roRw_hashQuery, hparam, simulateQ_list_mapM, apply_ite (simulateQ (roRw f)),
    apply_dite (simulateQ (roRw f)), hpair]

theorem revealNextAt_localRw (parts : C.Party → Parts C) (commitAt : C.Party → C.Party → Query C)
    (termAt : C.Party → Mail C E → C.Term → Query C) (committed : C.Party → Mail C E) (i : C.Party) (inbox : Mail C E)
    (hopen : ∀ k, k ∈ D.1 ∨ k = i → f (openAddress D parts i inbox k) = openAddress D parts i inbox k)
    (hparam : ∀ l, f (.derive .seedGen .parameter l) = .derive .seedGen .parameter l)
    (hpair : ∀ l, f (.derive .seedGen .pair l) = .derive .seedGen .pair l)
    (hshared : ∀ l, f (.sharedKeys .seedGen l) = .sharedKeys .seedGen l) :
    simulateQ (localRw f) (revealNextAt D parts commitAt termAt committed i inbox) =
      revealNextAt D parts (fun a b => f (commitAt a b)) (fun i inbox T => f (termAt i inbox T)) committed i inbox := by
  have ho : ∀ k, hashQuery (C := C) (f (if k ∈ D.1 ∨ k = i then openAddress D parts i inbox k else commitAt k i)) =
      hashQuery (if k ∈ D.1 ∨ k = i then openAddress D parts i inbox k else (fun a b => f (commitAt a b)) k i) := by
    intro k
    split_ifs with h
    · rw [hopen k h]
    · rfl
  unfold revealNextAt
  rw [simulateQ_bind, localRw_liftComp, roRw_mapM]
  simp only [ho]
  refine bind_congr fun opens => ?_
  split_ifs
  · simp only [simulateQ_bind, simulateQ_pure, localRw_liftComp, deriveAt_roRw f D parts termAt i inbox hparam hpair,
      roRw_mapM, sharedAddress, hshared]
  · simp

/-- The rewrite of the seed generation with the addresses `commitAt` and `termAt`. -/
theorem seedGenAt_cellRw (net : Adversary C E Unit PEmpty PEmpty) (state : net.State) (early : CallLog C)
    (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (commitAt : C.Party → C.Party → Query C) (termAt : C.Party → Mail C E → C.Term → Query C)
    (hopen : ∀ i inbox k, k ∈ D.1 ∨ k = i → f (openAddress D parts i inbox k) = openAddress (E := E) D parts i inbox k)
    (hparam : ∀ l, f (.derive .seedGen .parameter l) = .derive .seedGen .parameter l)
    (hpair : ∀ l, f (.derive .seedGen .pair l) = .derive .seedGen .pair l)
    (hshared : ∀ l, f (.sharedKeys .seedGen l) = .sharedKeys .seedGen l) :
    simulateQ (cellRw f) (seedGenAt D net state early parameter dealt parts commitAt termAt) =
      seedGenAt D net state early parameter dealt parts (fun a b => f (commitAt a b)) (fun i inbox T => f (termAt i inbox T)) := by
  unfold seedGenAt
  simp only [simulateQ_bind]
  rw [commitDrawsAt_cellRw]
  refine bind_congr fun c => ?_
  rw [observe_eq, show simulateQ (cellRw f) (worldRoles.adversary (logged (net.round state (commitMail D c)))) =
    worldRoles.adversary (logged (net.round state (commitMail D c))) from cellRw_counted f _]
  refine bind_congr fun r => ?_
  rw [programBlock_cellRw]
  refine bind_congr fun _ => ?_
  rw [levelRound_cellRw]
  have hnext : (fun j (_ : Unit) inbox => simulateQ (localRw f)
      (revealNextAt D parts commitAt termAt (commitInbox D c r.1.2) j inbox)) =
      fun j _ inbox => revealNextAt D parts (fun a b => f (commitAt a b)) (fun i inbox T => f (termAt i inbox T))
        (commitInbox D c r.1.2) j inbox := by
    funext j u inbox
    exact revealNextAt_localRw f D parts commitAt termAt _ j inbox (hopen j inbox) hparam hpair hshared
  rw [hnext]
  refine levelRound_congr D net _ _ _ _ _ _ _ fun f2 s2 d2 => ?_
  rw [levelRound_cellRw]
  simp only [echoNext, simulateQ_pure]
  rfl

end Walk

/-! ## The rewrite through the suffix -/

section Suffix

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (f : Query C → Query C)

omit [Fintype E] [DecidableEq E] in
/-- The rewrite of `suffixAt` with the addresses `commitAt` and `termAt`. -/
theorem suffixAt_cellRw (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State)
    (commitAt : C.Party → C.Party → Query C) (termAt : C.Party → Mail C E → C.Term → Query C)
    (hopen : ∀ i inbox k, k ∈ D.1 ∨ k = i →
      f (openAddress D x.2.2 i inbox k) = openAddress (E := E) D x.2.2 i inbox k)
    (hparam : ∀ l, f (.derive .seedGen .parameter l) = .derive .seedGen .parameter l)
    (hpair : ∀ l, f (.derive .seedGen .pair l) = .derive .seedGen .pair l)
    (hshared : ∀ l, f (.sharedKeys .seedGen l) = .sharedKeys .seedGen l)
    (hrest : ∀ q, isSeedGenQuery q = false → f q = q) :
    simulateQ (cellRw f) (suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x commitAt termAt) =
      suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x (fun a b => f (commitAt a b))
        (fun i inbox T => f (termAt i inbox T)) := by
  unfold suffixAt
  simp only [simulateQ_bind]
  rw [seedGenAt_cellRw f D A.net _ _ _ _ _ _ _ hopen hparam hpair hshared]
  refine bind_congr fun y => ?_
  rcases y with ⟨state, emu⟩
  dsimp only
  rw [cellRw_of_noCall f hrest _ (noCall_secRest_seedGenCell K circuits settings runLimit D
    ⟨true, fun _ => 0⟩ (fun _ => rfl) A _ _ _ _ _)]
  simp

/-- The cell `X` in the place of `markCell`. -/
def markTo (X : Query C) (q : Query C) : Query C := if q = markCell then X else q

theorem holdersList_ne_nil (T : C.Term) : holdersList T ≠ [] := by
  intro h
  have hc := card_holders T
  have hpos : 0 < (C.holders T).card := by
    rw [Fintype.card_coe] at hc
    have := C.one_le_t
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.1 hpos
  have : k ∈ holdersList T := by simp [holdersList, hk, Committee.parties]
  rw [h] at this
  exact List.not_mem_nil this

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem termAddress_ne_markCell (D : C.Coalition) (parts : C.Party → Parts C) (i : C.Party) (inbox : Mail C E)
    (T : C.Term) : termAddress D parts i inbox T ≠ markCell := by
  intro h
  simp only [termAddress, markCell, Query.derive.injEq, true_and, List.map_eq_nil_iff] at h
  exact holdersList_ne_nil T h

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The derive addresses of the shifted parts are `termMark` with `markCell` sent to the shifted hidden
cell. -/
theorem termAddress_shift_eq (D : C.Coalition) (parts : C.Party → Parts C) (T : C.Term)
    (δ : {k // k ∈ C.holders T} → HashOutput) (hT : ¬ KnownTo D.1 T) :
    termAddress (E := E) D (shiftBy T δ parts) =
      fun i inbox T' => markTo (hiddenInput (shiftBy T δ parts) T) (termMark D parts T i inbox T') := by
  funext i inbox T'
  unfold termMark markTo
  by_cases hT' : T' = T
  · subst hT'
    simp only [ite_true]
    exact termAddress_hidden D _ i inbox T' hT
  · simp only [hT', ite_false, termAddress_ne_markCell]
    exact termAddress_congr D _ _ i inbox T' fun k _ _ => shiftAll_term_ne T T' _ parts k hT'

omit [Fintype E] [DecidableEq E] in
/-- The rewrite by `markTo` of the shifted hidden cell sends the suffix of `partsRef` to the suffix of
`pairRun`. -/
theorem suffixAt_markTo (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State) (T : C.Term)
    (δ : {k // k ∈ C.holders T} → HashOutput) (hT : ¬ KnownTo D.1 T) :
    simulateQ (cellRw (markTo (hiddenInput (shiftBy T δ x.2.2) T)))
      (suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x (commitAddress x.2.2) (termMark D x.2.2 T)) =
      suffixAt K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x (commitAddress x.2.2)
        (termAddress D (shiftBy T δ x.2.2)) := by
  rw [suffixAt_cellRw K circuits settings runLimit _ D A x _ _ (fun i inbox k _ => ?_) (fun l => ?_) (fun l => ?_)
    (fun l => ?_) (fun q hq => ?_), termAddress_shift_eq D x.2.2 T δ hT]
  · congr 1
  · simp [markTo, openAddress, markCell]
  · simp [markTo, markCell]
  · simp [markTo, markCell]
  · simp [markTo, markCell]
  · have hne : q ≠ markCell := fun e => by subst e; simp [markCell, isSeedGenQuery] at hq
    simp [markTo, hne]

end Suffix

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.suffixAt_markTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.suffixAt_markTo
