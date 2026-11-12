import ThresholdLeanXmssSecurity.Proof.Execution
import ThresholdLeanXmssSecurity.Proof.Lemmas
import VCVio.EvalDist.List
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# The keygen

`KeygenCompletenessStatement` follows from the honest run of `keygen`. `KeygenSecurityStatement`
reduces to `KeygenCoupling`. `keygenSimulator_queryBound` gives the query half. The
supporting lemmas concern `KeygenCoupling` (CDG+18).
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

/-! ## The keygen and the setup of a ceremony -/

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Setup

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-- The commitments of operator `i`. -/
def commitQueries (phase : Phase) (i : C.Party) (own : Parts C) : OracleComp (RoSpec C) (List HashOutput) :=
  C.parties.mapM fun j => hashQuery (.commit phase i j (revealTo phase own i j))

/-- The commit message of operator `i`. -/
def commitOutbox (i : C.Party) (commitments : List HashOutput) : Mail C E :=
  fun j => if j = i then none else some (.hashes [commitments.getD j.val 0])

/-- The reveal message of operator `i`. -/
def revealOutbox (phase : Phase) (i : C.Party) (own : Parts C) : Mail C E :=
  fun j => if j = i then none else some (.hashes (revealTo phase own i j))

/-- The commitments that operator `i` opens. -/
def openQueries (phase : Phase) (i : C.Party) (revealed : Mail C E) : OracleComp (RoSpec C) (List HashOutput) :=
  C.parties.mapM fun j => hashQuery (.commit phase j i (Msg.hashesOf (revealed j)))

/-- The first check of operator `i`. -/
def openCheck (phase : Phase) (i : C.Party) (own : Parts C) (committed revealed : Mail C E)
    (opens : List HashOutput) : Prop :=
  ∀ j, j ≠ i → (Msg.hashesOf (revealed j)).length = (revealTo phase own j i).length ∧
    [opens.getD j.val 0] = Msg.hashesOf (committed j)

/-- The view of operator `i`. -/
def setupView (phase : Phase) (i : C.Party) (own : Parts C) (revealed : Mail C E) : C.Party → Parts C :=
  fun j => if j = i then own else readReveal phase (Msg.hashesOf (revealed j)) i j

/-- The hashes of the shared keys of operator `i`. -/
def sharedQueries (phase : Phase) (i : C.Party) (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    OracleComp (RoSpec C) (List HashOutput) :=
  C.parties.mapM fun j => hashQuery (.sharedKeys phase ((sharedTerms i j).map keys.2.1))

/-- The echo of operator `i` to `j`. -/
def echoOf (phase : Phase) (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (shared : List HashOutput) (j : C.Party) : List HashOutput :=
  (if phase = .keygen then [keys.1] else []) ++ [shared.getD j.val 0]

/-- The echo message of operator `i`. -/
def echoOutbox (phase : Phase) (i : C.Party) (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (shared : List HashOutput) : Mail C E :=
  fun j => if j = i then none else some (.hashes (echoOf phase keys shared j))

/-- The second check of operator `i`. -/
def echoCheck (phase : Phase) (i : C.Party) (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (shared : List HashOutput) (received : Mail C E) : Prop :=
  ∀ j, j ≠ i → Msg.hashesOf (received j) = echoOf phase keys shared j

theorem commitRevealEcho_eq (phase : Phase) (i : C.Party) (own : Parts C) :
    (commitRevealEcho phase i own : PartyM C E G _) = (do
      let commitments ← oracleStep (commitQueries phase i own)
      let committed ← exchange (commitOutbox i commitments)
      let revealed ← exchange (revealOutbox phase i own)
      let opens ← oracleStep (openQueries phase i revealed)
      require (openCheck phase i own committed revealed opens)
      let keys ← oracleStep (deriveKeys phase i (setupView phase i own revealed))
      let shared ← oracleStep (sharedQueries phase i keys)
      let received ← exchange (echoOutbox phase i keys shared)
      require (echoCheck phase i keys shared received)
      pure keys) := rfl

/-- A setup after the reveal round. -/
def setupRest (phase : Phase) (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    PartyM C E G (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) := do
  let opens ← oracleStep (openQueries phase i revealed)
  require (openCheck phase i own committed revealed opens)
  let keys ← oracleStep (deriveKeys phase i (setupView phase i own revealed))
  let shared ← oracleStep (sharedQueries phase i keys)
  let received ← exchange (echoOutbox phase i keys shared)
  require (echoCheck phase i keys shared received)
  pure keys

theorem advance_setup_start {α : Type} (phase : Phase) (i : C.Party) (own : Parts C)
    (f : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput) → PartyM C E G α) :
    advance (commitRevealEcho phase i own >>= f).run =
      liftComp (commitQueries phase i own) (LocalSpec C) >>= fun commitments =>
        pure (.wait (commitOutbox i commitments) (exchangeResume fun committed =>
          exchange (revealOutbox phase i own) >>= fun revealed => setupRest phase i own committed revealed >>= f)) := by
  rw [commitRevealEcho_eq]
  simp only [bind_assoc]
  rw [advance_oracleStep_bind]
  refine bind_congr fun commitments => ?_
  rw [advance_exchange_bind]
  simp only [setupRest, bind_assoc]

theorem advance_setup_reveal {α : Type} (phase : Phase) (i : C.Party) (own : Parts C)
    (g : Mail C E → PartyM C E G α) :
    advance (exchange (revealOutbox phase i own) >>= g).run = pure (.wait (revealOutbox phase i own) (exchangeResume g)) :=
  advance_exchange_bind _ g

theorem advance_setupRest {α : Type} (phase : Phase) (i : C.Party) (own : Parts C) (committed revealed : Mail C E)
    (f : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput) → PartyM C E G α) :
    advance (setupRest phase i own committed revealed >>= f).run =
      liftComp (openQueries phase i revealed) (LocalSpec C) >>= fun opens =>
        if openCheck phase i own committed revealed opens then
          liftComp (deriveKeys phase i (setupView phase i own revealed)) (LocalSpec C) >>= fun keys =>
            liftComp (sharedQueries phase i keys) (LocalSpec C) >>= fun shared =>
              pure (.wait (echoOutbox phase i keys shared) (exchangeResume fun received =>
                require (echoCheck phase i keys shared received) >>= fun _ => f keys))
        else pure (.done none) := by
  simp only [setupRest, bind_assoc]
  rw [advance_oracleStep_bind]
  refine bind_congr fun opens => ?_
  rw [advance_require_bind]
  split_ifs
  · rw [advance_oracleStep_bind]
    refine bind_congr fun keys => ?_
    rw [advance_oracleStep_bind]
    refine bind_congr fun shared => ?_
    rw [advance_exchange_bind]
    simp only [pure_bind]
  · rfl

end Setup

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section HonestSetup

variable {C : Committee} {E : Type} (prims : Primitives)

theorem getD_terms_idxOf {β : Type} (g : C.Term → β) (d : β) (T : C.Term) :
    (C.terms.map g).getD (C.terms.idxOf T) d = g T := by
  have hT : T ∈ C.terms := Finset.mem_toList.mpr (Finset.mem_univ T)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hT)]
  simp [List.getElem_idxOf]

theorem getD_parties {β : Type} (g : C.Party → β) (d : β) (j : C.Party) :
    (C.parties.map g).getD j.val d = g j := by
  simp [Committee.parties, List.getD_eq_getElem?_getD]

theorem sharedTerms_comm (i j : C.Party) : sharedTerms i j = sharedTerms j i := by
  unfold sharedTerms
  congr 1
  funext T
  simp [and_comm]

/-- The reveals that operator `x` receives in an honest setup. -/
def honestReveals (phase : Phase) (parts : C.Party → Parts C) (x : C.Party) : Mail C E :=
  fun k => revealOutbox phase k (parts k) x

/-- The view of operator `x` in an honest setup. -/
def honestView (phase : Phase) (parts : C.Party → Parts C) (x : C.Party) : C.Party → Parts C :=
  setupView phase x (parts x) (honestReveals (E := E) phase parts x)

theorem hashesOf_honestReveals (phase : Phase) (parts : C.Party → Parts C) {x k : C.Party} (hk : k ≠ x) :
    Msg.hashesOf (honestReveals (E := E) phase parts x k) = revealTo phase (parts k) k x := by
  simp [honestReveals, revealOutbox, Ne.symm hk, Msg.hashesOf]

theorem honestView_ne (phase : Phase) (parts : C.Party → Parts C) {x k : C.Party} (hk : k ≠ x) :
    honestView (E := E) phase parts x k = readReveal phase (revealTo phase (parts k) k x) x k := by
  simp [honestView, setupView, hk, hashesOf_honestReveals phase parts hk]

theorem honestView_self (phase : Phase) (parts : C.Party → Parts C) (x : C.Party) :
    honestView (E := E) phase parts x x = parts x := by
  simp [honestView, setupView]

theorem honestView_parameter (parts : C.Party → Parts C) (x k : C.Party) :
    (honestView (E := E) .keygen parts x k).parameter = (parts k).parameter := by
  by_cases hk : k = x
  · subst hk; rw [honestView_self]
  · rw [honestView_ne _ _ hk]
    simp [readReveal, revealTo]

theorem honestView_term (phase : Phase) (parts : C.Party → Parts C) {x k : C.Party} {T : C.Term}
    (hk : k ∈ C.holders T) (hx : x ∈ C.holders T) :
    (honestView (E := E) phase parts x k).term T = (parts k).term T := by
  by_cases hkx : k = x
  · subst hkx; rw [honestView_self]
  · rw [honestView_ne _ _ hkx]
    have hT : T ∈ sharedTerms k x := by simp [sharedTerms, hk, hx, Committee.terms]
    have hlt := List.idxOf_lt_length_of_mem hT
    cases phase <;>
      simp [readReveal, revealTo, List.getD_eq_getElem?_getD, List.getElem?_append_left, List.getElem?_append_right,
        hlt, List.getElem_idxOf, Nat.add_comm 1]

theorem honestView_pair (phase : Phase) (parts : C.Party → Parts C) {x a b : C.Party} (h : a = x ∨ b = x) :
    (honestView (E := E) phase parts x a).pair b = (parts a).pair b := by
  by_cases hax : a = x
  · subst hax; rw [honestView_self]
  · have hb : b = x := h.resolve_left hax
    subst hb
    rw [honestView_ne _ _ hax]
    cases phase <;>
      simp [readReveal, revealTo, List.getD_eq_getElem?_getD, List.getElem?_append_right, Nat.add_comm 1]

theorem pairOf_left_or_right (i j : C.Party) (h : i ≠ j) : (C.pairOf i j h).1.1 = i ∨ (C.pairOf i j h).1.2 = i := by
  unfold Committee.pairOf
  split_ifs <;> simp

theorem D_deriveKeys (h : Query C → HashOutput) (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    D prims h (deriveKeys phase i view) =
      (if phase = .keygen then h (.derive phase .parameter (C.parties.map fun j => (view j).parameter)) else 0,
        fun T => if i ∈ C.holders T then
          h (.derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (view j).term T)) else 0,
        fun j => if hj : j = i then 0 else
          h (.derive phase .pair [(view (C.pairOf i j (Ne.symm hj)).1.1).pair (C.pairOf i j (Ne.symm hj)).1.2,
            (view (C.pairOf i j (Ne.symm hj)).1.2).pair (C.pairOf i j (Ne.symm hj)).1.1])) := by
  unfold deriveKeys
  split_ifs with hp <;> simp only [D_bind, D_pure, D_hashQuery, D_mapM] <;>
    refine Prod.ext rfl (Prod.ext ?_ ?_) <;> funext x
  all_goals first
    | (show (List.map _ C.terms).getD (C.terms.idxOf x) 0 = _
       rw [getD_terms_idxOf (fun T => D prims h (if i ∈ C.holders T then hashQuery _ else pure 0))]
       split_ifs with hc <;> simp [hc, D_hashQuery, D_pure])
    | (show (List.map _ C.parties).getD x.val 0 = _
       rw [getD_parties (fun j => D prims h (if hj : j = i then pure 0 else hashQuery _))]
       split_ifs with hc <;> simp [hc, D_hashQuery, D_pure])

/-- The input of the derivation of `P` in an honest keygen. -/
def parameterInput (parts : C.Party → Parts C) : Query C :=
  .derive .keygen .parameter (C.parties.map fun j => (parts j).parameter)

/-- The input of the derivation of the key of term `T` in an honest setup. -/
def termInput (phase : Phase) (parts : C.Party → Parts C) (T : C.Term) : Query C :=
  .derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (parts j).term T)

/-- The input of the derivation of the key of pair `p` in an honest setup. -/
def pairInput (phase : Phase) (parts : C.Party → Parts C) (p : C.Pair) : Query C :=
  .derive phase .pair [(parts p.1.1).pair p.1.2, (parts p.1.2).pair p.1.1]

theorem D_deriveKeys_honest (h : Query C → HashOutput) (phase : Phase) (parts : C.Party → Parts C) (i : C.Party) :
    D prims h (deriveKeys phase i (honestView (E := E) phase parts i)) =
      (if phase = .keygen then h (parameterInput parts) else 0,
        fun T => if i ∈ C.holders T then h (termInput phase parts T) else 0,
        fun j => if hj : j = i then 0 else h (pairInput phase parts (C.pairOf i j (Ne.symm hj)))) := by
  rw [D_deriveKeys]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · split_ifs with hp
    · subst hp
      simp [parameterInput, honestView_parameter]
    · rfl
  · funext T
    simp only
    split_ifs with hi
    · unfold termInput
      refine congrArg (fun l => h (.derive phase .term l)) (List.map_congr_left fun k hk => ?_)
      exact honestView_term phase parts (by simpa using List.of_mem_filter hk) hi
    · rfl
  · funext j
    simp only
    split_ifs with hj
    · rfl
    · have hp := pairOf_left_or_right i j (Ne.symm hj)
      unfold pairInput
      rw [honestView_pair phase parts hp, honestView_pair phase parts hp.symm]

theorem isAbort_commitOutbox (k : C.Party) (commitments : List HashOutput) (j : C.Party) :
    Msg.isAbort (commitOutbox (E := E) k commitments j) = false := by
  unfold commitOutbox; split_ifs <;> rfl

theorem isAbort_revealOutbox (phase : Phase) (k : C.Party) (own : Parts C) (j : C.Party) :
    Msg.isAbort (revealOutbox (E := E) phase k own j) = false := by
  unfold revealOutbox; split_ifs <;> rfl

theorem isAbort_echoOutbox (phase : Phase) (k : C.Party) (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (shared : List HashOutput) (j : C.Party) : Msg.isAbort (echoOutbox (E := E) phase k keys shared j) = false := by
  unfold echoOutbox; split_ifs <;> rfl

theorem D_commitQueries (h : Query C → HashOutput) (phase : Phase) (k : C.Party) (own : Parts C) :
    D prims h (commitQueries phase k own) = C.parties.map fun j => h (.commit phase k j (revealTo phase own k j)) := by
  simp [commitQueries, D_mapM, D_hashQuery]

theorem openCheck_honest (h : Query C → HashOutput) (phase : Phase) (parts : C.Party → Parts C) (i : C.Party) :
    openCheck phase i (parts i) (fun k => commitOutbox (E := E) k (D prims h (commitQueries phase k (parts k))) i)
      (honestReveals phase parts i) (D prims h (openQueries phase i (honestReveals (E := E) phase parts i))) := by
  intro j hj
  rw [hashesOf_honestReveals phase parts hj]
  refine ⟨by cases phase <;> simp [revealTo], ?_⟩
  simp only [openQueries, D_mapM, D_hashQuery, getD_parties]
  rw [hashesOf_honestReveals phase parts hj]
  simp only [commitOutbox, Ne.symm hj, if_false, Msg.hashesOf, D_commitQueries, getD_parties]

theorem echoCheck_honest (h : Query C → HashOutput) (phase : Phase) (parts : C.Party → Parts C) (i : C.Party) :
    let keys := fun x => D prims h (deriveKeys phase x (honestView (E := E) phase parts x))
    let shared := fun x => D prims h (sharedQueries phase x (keys x))
    echoCheck phase i (keys i) (shared i) (fun k => echoOutbox (E := E) phase k (keys k) (shared k) i) := by
  intro keys shared j hj
  simp only [echoOutbox, Ne.symm hj, if_false, Msg.hashesOf]
  have hshared : ∀ x y, (shared x).getD y.val 0 =
      h (.sharedKeys phase ((sharedTerms x y).map fun T =>
        if x ∈ C.holders T then h (termInput phase parts T) else 0)) := by
    intro x y
    simp only [shared, keys, sharedQueries, D_mapM, D_hashQuery, getD_parties, D_deriveKeys_honest]
  unfold echoOf
  rw [hshared, hshared, sharedTerms_comm j i]
  have hmap : ((sharedTerms i j).map fun T => if j ∈ C.holders T then h (termInput phase parts T) else 0) =
      ((sharedTerms i j).map fun T => if i ∈ C.holders T then h (termInput phase parts T) else 0) := by
    refine List.map_congr_left fun T hT => ?_
    simp only [sharedTerms, List.mem_filter, decide_eq_true_eq] at hT
    simp [hT.2.1, hT.2.2]
  rw [hmap]
  simp only [keys, D_deriveKeys_honest]

end HonestSetup

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section KeygenRun

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The keys of an operator from the keys that its keygen derives. -/
def keysOf (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) : Keys C :=
  ⟨truncateHash keys.1, keys.2.1, keys.2.2⟩

/-- The keygen of operator `i` after the commit round. -/
def keygenRound1 (i : C.Party) (own : Parts C) : Mail C E → PartyM C E RealSpec (Keys C) := fun committed =>
  exchange (revealOutbox .keygen i own) >>= fun revealed =>
    setupRest .keygen i own committed revealed >>= fun keys => pure (keysOf keys)

/-- The step of operator `i` after the start of its keygen. -/
def keygenStart (i : C.Party) (own : Parts C) (commitments : List HashOutput) : Step C E RealSpec (Keys C) :=
  .wait (commitOutbox i commitments) (exchangeResume (keygenRound1 i own))

theorem advance_keygen (i : C.Party) :
    advance (keygen i : PartyM C E RealSpec (Keys C)).run =
      liftComp sampleParts (LocalSpec C) >>= fun own =>
        liftComp (commitQueries .keygen i own) (LocalSpec C) >>= fun commitments =>
          pure (keygenStart i own commitments) := by
  have : (keygen i : PartyM C E RealSpec (Keys C)) =
      localStep (liftComp sampleParts _) >>= fun own =>
        commitRevealEcho .keygen i own >>= fun keys => pure (keysOf keys) := rfl
  rw [this, advance_localStep_bind]
  refine bind_congr fun own => ?_
  rw [advance_setup_start]
  rfl

/-- The keygen after the parts, from the commitments on. -/
def keygenRest (parts : C.Party → Parts C) : OracleComp (LocalSpec C) (C.Party → Option (Keys C)) := do
  let commitments ← Concrete.sequenceFin fun j => liftComp (commitQueries .keygen j (parts j)) (LocalSpec C)
  honestRounds noFunctionality (fun l => l.elim) setupRounds fun j => keygenStart (E := E) j (parts j) (commitments j)

/-- The honest keygen samples all parts first. -/
theorem sameRun_keygen :
    SameRun prims (honestStart (fun i => (keygen i : PartyM C E RealSpec (Keys C))) >>=
        honestRounds noFunctionality (fun l => l.elim) setupRounds)
      (Concrete.sequenceFin (fun _ => liftComp sampleParts (LocalSpec C)) >>= keygenRest (E := E)) := by
  unfold honestStart keygenRest
  simp only [advance_keygen]
  refine (sameRun_sequenceFin_dep prims _ _ (fun j own commitments => keygenStart (E := E) j own commitments)).bind
    (fun steps => SameRun.refl prims _) |>.trans ?_
  simp only [bind_assoc, pure_bind]
  exact SameRun.refl prims _

/-- The keys of operator `i` in an honest keygen with `H` fixed to `h`. -/
def honestKeys (h : Query C → HashOutput) (parts : C.Party → Parts C) (i : C.Party) : Keys C :=
  ⟨truncateHash (h (parameterInput parts)), fun T => if i ∈ C.holders T then h (termInput .keygen parts T) else 0,
    fun j => if hj : j = i then 0 else h (pairInput .keygen parts (C.pairOf i j (Ne.symm hj)))⟩

theorem honestRounds_wait {I O L R α : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (outbox : C.Party → Mail C E) (f : C.Party → Mail C E → PartyM C E (CallSpec I O) α) :
    honestRounds F reply (fuel + 1) (fun i => .wait (outbox i) (exchangeResume (f i))) =
      Concrete.sequenceFin (fun j => advance (exchangeResume (f j) fun k => outbox k j)) >>=
        honestRounds F reply fuel := by
  rw [honestRounds_succ, honestStep_exchange]
  exact fun h => (h (firstParty C) : False)

theorem keysOf_honest (h : Query C → HashOutput) (parts : C.Party → Parts C) (i : C.Party) :
    keysOf (D prims h (deriveKeys .keygen i (honestView (E := E) .keygen parts i))) = honestKeys h parts i := by
  rw [D_deriveKeys_honest]
  rfl

/-- The keygen with `H` fixed gives the honest keys to every operator. -/
theorem simulateQ_fixedLocal_keygenRest (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    simulateQ (fixedLocal prims h) (keygenRest (E := E) parts) = pure fun i => some (honestKeys h parts i) := by
  set keys := fun x => D prims h (deriveKeys .keygen x (honestView (E := E) .keygen parts x)) with hk
  set shared := fun x => D prims h (sharedQueries .keygen x (keys x)) with hs
  have h1 : ∀ j, advance (exchangeResume (keygenRound1 (E := E) j (parts j)) fun k => commitOutbox k (D prims h (commitQueries .keygen k (parts k))) j) =
      pure (.wait (revealOutbox .keygen j (parts j)) (exchangeResume fun revealed =>
        setupRest .keygen j (parts j) (fun k => commitOutbox k (D prims h (commitQueries .keygen k (parts k))) j) revealed >>=
          fun keys => pure (keysOf keys))) := by
    intro j
    rw [exchangeResume_of_no_abort _ _ fun k => isAbort_commitOutbox k _ j]
    exact advance_setup_reveal _ _ _ _
  have h2 : ∀ j, simulateQ (fixedLocal prims h) (advance (exchangeResume (fun revealed =>
        setupRest (G := RealSpec) .keygen j (parts j) (fun k => commitOutbox (E := E) k (D prims h (commitQueries .keygen k (parts k))) j) revealed >>=
          fun keys => pure (keysOf keys)) fun k => revealOutbox .keygen k (parts k) j)) =
      pure (Step.wait (G := RealSpec) (echoOutbox .keygen j (keys j) (shared j)) (exchangeResume fun received =>
        require (echoCheck .keygen j (keys j) (shared j) received) >>= fun _ => pure (keysOf (keys j)))) := by
    intro j
    rw [exchangeResume_of_no_abort _ _ fun k => isAbort_revealOutbox _ k _ j, advance_setupRest, simulateQ_bind,
      simulateQ_fixedLocal_liftComp, pure_bind]
    split_ifs with hcheck
    · rw [simulateQ_bind, simulateQ_fixedLocal_liftComp, pure_bind,
        simulateQ_bind, simulateQ_fixedLocal_liftComp, pure_bind, simulateQ_pure]
      rfl
    · exact absurd (openCheck_honest prims h .keygen parts j) hcheck
  have h3 : ∀ j, simulateQ (fixedLocal prims h) (advance (exchangeResume (fun received =>
        require (echoCheck .keygen j (keys j) (shared j) received) >>= fun _ => pure (keysOf (keys j)))
          fun k => echoOutbox (E := E) .keygen k (keys k) (shared k) j)) =
      pure (Step.done (G := RealSpec) (some (honestKeys h parts j))) := by
    intro j
    rw [exchangeResume_of_no_abort _ _ fun k => isAbort_echoOutbox _ k _ _ j, advance_require_bind]
    split_ifs with hcheck
    · rw [advance_run_pure, simulateQ_pure, hk, keysOf_honest]
    · exact absurd (echoCheck_honest prims h .keygen parts j) hcheck
  unfold keygenRest
  rw [simulateQ_bind, simulateQ_sequenceFin]
  simp only [simulateQ_fixedLocal_liftComp]
  rw [sequenceFin_pure, pure_bind]
  show simulateQ _ (honestRounds _ _ (2 + 1) _) = _
  unfold keygenStart
  rw [honestRounds_wait]
  simp only [h1]
  rw [sequenceFin_pure, pure_bind, honestRounds_wait, simulateQ_bind, simulateQ_sequenceFin]
  simp only [h2]
  rw [sequenceFin_pure, pure_bind, honestRounds_wait, simulateQ_bind, simulateQ_sequenceFin]
  simp only [h3]
  rw [sequenceFin_pure, pure_bind]
  rfl

/-- A computation in front of another one, whose result is dropped, keeps the output of the other
one (lazy sampling). -/
theorem evalDist_run'_prepend {α β : Type} (W : OracleComp (LocalSpec C) β) (X : OracleComp (LocalSpec C) α)
    (s : HashCache C) :
    𝒟[(simulateQ (localAnswer prims) (W >>= fun _ => X)).run' s] = 𝒟[(simulateQ (localAnswer prims) X).run' s] := by
  have hswap := sameRun_swap prims W X (fun _ x => pure x) s
  simp only [bind_pure] at hswap
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, hswap, ← evalDist_map]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  rw [← StateT.run'_eq, StateT.run'_eq, map_eq_bind_pure_comp]
  refine evalDist_bind_congr fun p _ => ?_
  exact evalDist_eq_pure_of_support _ _ fun y hy => by
    simp at hy
    exact hy.2.symm

/-- The bind of local computations from a cache, with continuations of the same output on every
reachable result and cache. -/
theorem evalDist_run'_bind_congr {α β : Type} (m : OracleComp (LocalSpec C) β) (f g : β → OracleComp (LocalSpec C) α)
    (s : HashCache C)
    (h : ∀ p ∈ support ((simulateQ (localAnswer prims) m).run s),
      𝒟[(simulateQ (localAnswer prims) (f p.1)).run' p.2] = 𝒟[(simulateQ (localAnswer prims) (g p.1)).run' p.2]) :
    𝒟[(simulateQ (localAnswer prims) (m >>= f)).run' s] = 𝒟[(simulateQ (localAnswer prims) (m >>= g)).run' s] := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  exact evalDist_bind_congr fun p hp => by simpa [StateT.run'_eq] using h p hp

/-- All pairs, in one fixed order. -/
def pairList (C : Committee) : List C.Pair := (Finset.univ : Finset C.Pair).toList

/-- The derivations of an honest keygen, namely `P`, the key of each term and the key of each pair. -/
def keygenInputs (parts : C.Party → Parts C) : List (Query C) :=
  parameterInput parts :: (C.terms.map (termInput .keygen parts) ++ (pairList C).map (pairInput .keygen parts))

/-- The derivations of an honest keygen, queried in a fixed order. -/
def keygenDerivations (parts : C.Party → Parts C) : OracleComp (LocalSpec C) (List HashOutput) :=
  liftComp ((keygenInputs parts).mapM hashQuery) (LocalSpec C)

/-- The keys of operator `i` from the values of the derivations. -/
def keysFromValues (values : List HashOutput) (i : C.Party) : Keys C :=
  ⟨truncateHash (values.getD 0 0), fun T => if i ∈ C.holders T then values.getD (1 + C.terms.idxOf T) 0 else 0,
    fun j => if hj : j = i then 0 else
      values.getD (1 + C.terms.length + (pairList C).idxOf (C.pairOf i j (Ne.symm hj))) 0⟩

theorem getD_pairList_idxOf {β : Type} (g : C.Pair → β) (d : β) (p : C.Pair) :
    ((pairList C).map g).getD ((pairList C).idxOf p) d = g p := by
  have hp : p ∈ pairList C := Finset.mem_toList.mpr (Finset.mem_univ p)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem hp)]
  simp [List.getElem_idxOf]

theorem keysFromValues_map (h : Query C → HashOutput) (parts : C.Party → Parts C) (i : C.Party) :
    keysFromValues ((keygenInputs parts).map h) i = honestKeys h parts i := by
  have hT : ∀ T, (C.terms.map (h ∘ termInput .keygen parts) ++ (pairList C).map (h ∘ pairInput .keygen parts)).getD
      (C.terms.idxOf T) 0 = h (termInput .keygen parts T) := by
    intro T
    have hT : T ∈ C.terms := Finset.mem_toList.mpr (Finset.mem_univ T)
    have hlt := List.idxOf_lt_length_of_mem hT
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hlt), ← List.getD_eq_getElem?_getD]
    exact getD_terms_idxOf (h ∘ termInput .keygen parts) 0 T
  have hp : ∀ p, (C.terms.map (h ∘ termInput .keygen parts) ++ (pairList C).map (h ∘ pairInput .keygen parts)).getD
      (C.terms.length + (pairList C).idxOf p) 0 = h (pairInput .keygen parts p) := by
    intro p
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp only [List.length_map, Nat.add_sub_cancel_left]
    rw [← List.getD_eq_getElem?_getD]
    exact getD_pairList_idxOf (h ∘ pairInput .keygen parts) 0 p
  unfold keysFromValues honestKeys keygenInputs
  simp only [List.map_cons, List.map_append, List.map_map]
  congr 1
  · funext T
    split_ifs
    · rw [Nat.add_comm, List.getD_cons_succ, hT]
    · rfl
  · funext j
    split_ifs
    · rfl
    · rw [Nat.add_assoc, Nat.add_comm, List.getD_cons_succ, hp]

theorem simulateQ_fixedLocal_keygenDerivations (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    simulateQ (fixedLocal prims h) (keygenDerivations parts) = pure ((keygenInputs parts).map h) := by
  rw [keygenDerivations, simulateQ_fixedLocal_liftComp, D_mapM]
  simp [D_hashQuery]

/-- The honest keygen gives the keys from fresh derivations. -/
theorem evalDist_keygen_derivations :
    𝒟[(simulateQ (localAnswer prims) (Concrete.sequenceFin (fun _ => liftComp sampleParts (LocalSpec C)) >>=
        keygenRest (E := E))).run' ∅] =
      𝒟[(simulateQ (localAnswer prims) (Concrete.sequenceFin (fun _ => liftComp sampleParts (LocalSpec C)) >>=
        fun parts => keygenDerivations parts >>= fun values => pure fun i => some (keysFromValues values i))).run' ∅] := by
  refine (evalDist_run'_bind_congr prims _ (keygenRest (E := E))
    (fun parts => keygenDerivations parts >>= fun _ => keygenRest (E := E) parts) ∅
    fun p _ => (evalDist_run'_prepend prims (keygenDerivations p.1) _ _).symm).trans ?_
  refine evalDist_run'_bind_congr prims _ (fun parts => keygenDerivations parts >>= fun _ => keygenRest (E := E) parts)
    (fun parts => keygenDerivations parts >>= fun values => pure fun i => some (keysFromValues values i)) ∅
    fun p hp => ?_
  refine evalDist_run'_bind_congr prims (keygenDerivations p.1) (fun _ => keygenRest (E := E) p.1)
    (fun values => pure fun i => some (keysFromValues values i)) p.2 fun q hq => ?_
  have hp0 := (localRun_support _ ∅ p hp).2.1 (noMpc_empty)
  obtain ⟨_, hq0, hqv⟩ := localRun_support _ p.2 q hq
  rw [simulateQ_pure, StateT.run'_eq, StateT.run'_eq]
  erw [StateT.run_pure, map_pure]
  refine evalDist_eq_pure_of_support _ _ fun y hy => ?_
  rw [support_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨hle, hz0, hzv⟩ := localRun_support _ q.2 z hz
  have hnz := hz0 (hq0 hp0)
  have hagree := agrees_hashOf prims hnz
  have hk := hzv _ (good_hashOf prims z.2) hagree
  have hv := hqv _ (good_hashOf prims z.2) (hagree.mono hle)
  rw [simulateQ_fixedLocal_keygenRest, support_pure, Set.mem_singleton_iff] at hk
  rw [simulateQ_fixedLocal_keygenDerivations, support_pure, Set.mem_singleton_iff] at hv
  show z.1 = fun i => some (keysFromValues q.1 i)
  rw [hk, hv]
  funext i
  rw [keysFromValues_map]

/-- Distinct fresh inputs of `H` give independent uniform outputs. -/
theorem evalDist_fresh_mapM (qs : List (Query C)) :
    ∀ (s : HashCache C), qs.Nodup → (∀ q ∈ qs, s q = none) → (∀ q ∈ qs, ¬ IsFixed q) →
      𝒟[(simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (qs.mapM hashQuery)).run' s] =
        𝒟[qs.mapM fun _ => $ᵗ HashOutput] := by
  induction qs with
  | nil => intro s _ _ _; simp
  | cons q qs ih =>
    intro s hnd hfresh hfix
    have hq : (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (hashQuery q)) = hashAnswer prims q :=
      (simulateQ_query _ _).trans (id_map _)
    rw [List.nodup_cons] at hnd
    simp only [List.mapM_cons, simulateQ_bind, simulateQ_pure, hq, StateT.run'_eq, StateT.run_bind, map_bind]
    rw [hashAnswer_of_not_isFixed prims (hfix q (List.mem_cons_self ..)), OracleSpec.randomOracle,
      QueryImpl.withCaching_run_none _ (hfresh q (List.mem_cons_self ..)), bind_map_left]
    refine evalDist_bind_congr' _ fun u => ?_
    simp only [StateT.run_bind, map_bind, StateT.run_pure, map_pure]
    have hne : ∀ q' ∈ qs, q' ≠ q := fun q' hq' e => hnd.1 (e ▸ hq')
    have := ih (s.cacheQuery q u) hnd.2 (fun q' hq' => by
        rw [QueryCache.cacheQuery_of_ne _ _ (hne q' hq')]
        exact hfresh q' (List.mem_cons_of_mem _ hq'))
      fun q' hq' => hfix q' (List.mem_cons_of_mem _ hq')
    rw [StateT.run'_eq, evalDist_map] at this
    have e1 : ((simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (qs.mapM hashQuery)).run
        (s.cacheQuery q u) >>= fun p => pure (u :: p.1)) = (fun l => u :: l) <$> ((fun p => p.1) <$>
          (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (qs.mapM hashQuery)).run
            (s.cacheQuery q u)) := by
      rw [Functor.map_map, map_eq_bind_pure_comp]; rfl
    have e2 : (qs.mapM (fun _ => $ᵗ HashOutput) >>= fun l => pure (u :: l)) =
        (fun l => u :: l) <$> qs.mapM (fun _ => $ᵗ HashOutput) := by
      rw [map_eq_bind_pure_comp]; rfl
    rw [e1, e2, evalDist_map, evalDist_map, evalDist_map, this]

theorem run'_localAnswer_liftComp {α : Type} (p : ProbComp α) (s : HashCache C) :
    (simulateQ (localAnswer prims) (liftComp p (LocalSpec C))).run' s = p := by
  rw [show simulateQ (localAnswer prims) (liftComp p (LocalSpec C)) =
      simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p from
    QueryImpl.simulateQ_add_liftComp_left (unifFwdImpl (Query C →ₒ HashOutput)) _ p]
  rw [StateT.run'_eq, unifFwdImpl.simulateQ_run, Functor.map_map]
  simp

/-- The ideal keygen with the honest replies gives the keys of `KeyGen'` to every operator. -/
theorem keygen_ideal :
    (simulateQ (localAnswer prims) (simulateQ (replyImpl (fun _ => (Finset.univ : Finset C.Party)))
        ((Fkeygen (C := C)).run noCoalition fun _ => some ()))).run' ∅ =
      (fun r i => some (r.2.2 i)) <$> prawnsKeyGen (C := C) := by
  have : simulateQ (replyImpl (C := C) (fun _ => (Finset.univ : Finset C.Party)))
      ((Fkeygen (C := C)).run noCoalition fun _ => some ()) =
        liftComp ((fun r i => some (r.2.2 i)) <$> prawnsKeyGen (C := C)) (LocalSpec C) := by
    unfold Fkeygen
    simp only [simulateQ_bind, simulateQ_replyImpl_liftComp_prob, liftComp_map]
    rw [map_eq_bind_pure_comp]
    refine bind_congr fun r => ?_
    rcases r with ⟨parameter, seeds, keys⟩
    simp only [simulateQ_bind, simulateQ_replyImpl_leak, pure_bind, simulateQ_pure, Function.comp]
    congr 1
    funext i
    simp [noCoalition]
  rw [this, run'_localAnswer_liftComp]

theorem liftComp_sequenceFin {α : Type} {n : ℕ} (f : Fin n → ProbComp α) :
    liftComp (Concrete.sequenceFin f) (LocalSpec C) = Concrete.sequenceFin fun i => liftComp (f i) (LocalSpec C) :=
  simulateQ_sequenceFin _ f

theorem run'_localAnswer_liftComp_bind {α β : Type} (p : ProbComp α) (k : α → OracleComp (LocalSpec C) β)
    (s : HashCache C) :
    (simulateQ (localAnswer prims) (liftComp p (LocalSpec C) >>= k)).run' s =
      p >>= fun a => (simulateQ (localAnswer prims) (k a)).run' s := by
  have hl : simulateQ (localAnswer prims) (liftComp p (LocalSpec C)) =
      simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p :=
    QueryImpl.simulateQ_add_liftComp_left (unifFwdImpl (Query C →ₒ HashOutput)) _ p
  rw [simulateQ_bind, hl]
  rw [StateT.run'_eq, StateT.run_bind, unifFwdImpl.simulateQ_run, bind_map_left, map_bind]
  rfl

/-- The real keygen as a computation that samples the parts and then queries the derivations. -/
theorem keygen_real :
    (simulateQ (localAnswer prims) (Concrete.sequenceFin (fun _ => liftComp sampleParts (LocalSpec C)) >>=
        fun parts => keygenDerivations parts >>= fun values => pure fun i => some (keysFromValues values i))).run' ∅ =
      Concrete.sequenceFin (fun _ => sampleParts (C := C)) >>= fun parts =>
        (fun values (i : C.Party) => some (keysFromValues (C := C) values i)) <$>
          (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) ((keygenInputs parts).mapM hashQuery)).run' ∅ := by
  rw [← liftComp_sequenceFin, run'_localAnswer_liftComp_bind]
  refine bind_congr fun parts => ?_
  rw [keygenDerivations, simulateQ_bind, simulateQ_localAnswer_liftComp, StateT.run'_eq, StateT.run'_eq,
    StateT.run_bind, map_bind, Functor.map_map]
  simp only [simulateQ_pure, StateT.run_pure, map_pure]
  rw [map_eq_bind_pure_comp]
  rfl

end KeygenRun

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

section Uniform

/-- A computation whose outputs all have one probability is uniform. -/
theorem evalDist_eq_uniform_of_probOutput_eq {β : Type} [Fintype β] [SampleableType β] (mx : ProbComp β)
    (h : ∀ x y, Pr[= x | mx] = Pr[= y | mx]) : 𝒟[mx] = 𝒟[$ᵗ β] := by
  refine evalDist_ext fun x => ?_
  rw [probOutput_uniformSample]
  have hsum := sum_probOutput_eq_one (mx := mx) (by simp)
  rw [Finset.sum_congr rfl (fun y _ => h y x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum)

theorem xor_bijective {n : ℕ} (c : BitVec n) : Function.Bijective fun y : BitVec n => y ^^^ c :=
  Function.Involutive.bijective (fun y => by simp [BitVec.xor_assoc])

theorem truncateHash_xor (y : HashOutput) (c : Digest) :
    truncateHash (y ^^^ c.setWidth hashOutputBits) = truncateHash y ^^^ c := by
  unfold truncateHash
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
  simp [hi, show i < hashOutputBits by unfold hashOutputBits; unfold digestBits at hi; omega]

/-- The first 128 bits of a uniform hash output are uniform. -/
theorem evalDist_truncateHash :
    𝒟[(truncateHash <$> ($ᵗ HashOutput) : ProbComp Digest)] = 𝒟[$ᵗ Digest] := by
  refine evalDist_eq_uniform_of_probOutput_eq _ fun x y => ?_
  have hU : 𝒟[(fun z => z ^^^ (x ^^^ y).setWidth hashOutputBits) <$> ($ᵗ HashOutput)] = 𝒟[$ᵗ HashOutput] :=
    evalDist_map_bijective_uniform_cross HashOutput _ (xor_bijective _)
  have hshift : 𝒟[(truncateHash <$> ($ᵗ HashOutput) : ProbComp Digest)] =
      𝒟[(fun d => d ^^^ (x ^^^ y)) <$> (truncateHash <$> ($ᵗ HashOutput) : ProbComp Digest)] :=
    calc 𝒟[(truncateHash <$> ($ᵗ HashOutput) : ProbComp Digest)]
        = 𝒟[truncateHash <$> ((fun z => z ^^^ (x ^^^ y).setWidth hashOutputBits) <$> ($ᵗ HashOutput))] := by
          rw [evalDist_map, evalDist_map, hU]
      _ = _ := by
          rw [Functor.map_map, Functor.map_map]
          congr 2
          funext z
          exact truncateHash_xor z _
  have hx : x = y ^^^ (x ^^^ y) := by
    rw [BitVec.xor_comm x y, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  have key := probOutput_map_injective (truncateHash <$> ($ᵗ HashOutput) : ProbComp Digest)
    (xor_bijective (x ^^^ y)).1 y
  rw [← hx] at key
  rw [probOutput_def, hshift, ← probOutput_def]
  exact key

/-- A list of uniform values, read as a function through an index, is a uniform function. -/
theorem evalDist_listFunction {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [SampleableType β] [SampleableType (α → β)]
    (L : List α) (idx : α → ℕ) (d : β) (hlen : L.length = Fintype.card α)
    (h1 : ∀ f : α → β, (fun a => (L.map f).getD (idx a) d) = f)
    (h2 : ∀ l : List β, l.length = L.length → L.map (fun a => l.getD (idx a) d) = l) :
    𝒟[(fun l a => l.getD (idx a) d) <$> L.mapM (fun _ => $ᵗ β)] = 𝒟[$ᵗ (α → β)] := by
  refine evalDist_ext fun f => ?_
  rw [probOutput_map, probOutput_uniformSample, Fintype.card_fun, ← hlen]
  have hlen' : ∀ l ∈ support (L.mapM fun _ => $ᵗ β), l.length = L.length := by
    intro l hl
    by_contra hne
    exact probOutput_ne_zero_of_mem_support hl (by rw [probOutput_list_mapM, if_neg hne])
  rw [show Pr[fun l => (fun a => l.getD (idx a) d) = f | L.mapM fun _ => $ᵗ β] =
      Pr[fun l => l = L.map f | L.mapM fun _ => $ᵗ β] from probEvent_ext fun l hl => ⟨fun e => by
        rw [← h2 l (hlen' l hl), e], fun e => by rw [e, h1]⟩, probEvent_eq_eq_probOutput,
    probOutput_list_mapM, if_pos (by simp)]
  rw [Nat.cast_pow, ENNReal.inv_pow]
  clear hlen hlen' h1 h2
  simp only [probOutput_uniformSample]
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, List.prod_cons, ih, List.length_cons, pow_succ]
    rw [mul_comm]

end Uniform

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Collision

open scoped ENNReal

variable {C : Committee}

theorem evalDist_sequenceFin_congr {α : Type} :
    ∀ {n : ℕ} (f g : Fin n → ProbComp α), (∀ i, 𝒟[f i] = 𝒟[g i]) →
      𝒟[Concrete.sequenceFin f] = 𝒟[Concrete.sequenceFin g]
  | 0, f, g, _ => by simp only [Concrete.sequenceFin]
  | n + 1, f, g, h => by
    simp only [Concrete.sequenceFin, evalDist_bind, h 0]
    congr 1
    funext a
    rw [← evalDist_bind, ← evalDist_bind, bind_pure_comp, bind_pure_comp, evalDist_map, evalDist_map,
      evalDist_sequenceFin_congr _ _ fun i => h i.succ]

/-- The parts of one operator with one coordinate shifted. -/
def shiftParts (own : Parts C) (term : Option C.Term) (pair : Option C.Party) (c : HashOutput) : Parts C :=
  ⟨own.parameter, fun T => if term = some T then own.term T ^^^ c else own.term T,
    fun j => if pair = some j then own.pair j ^^^ c else own.pair j⟩

theorem evalDist_shift_sampleParts (term : Option C.Term) (pair : Option C.Party) (c : HashOutput) :
    𝒟[(fun own => shiftParts own term pair c) <$> sampleParts (C := C)] = 𝒟[sampleParts (C := C)] := by
  have hterm : 𝒟[(fun t (T : C.Term) => if term = some T then t T ^^^ c else t T) <$> ($ᵗ (C.Term → HashOutput))] =
      𝒟[$ᵗ (C.Term → HashOutput)] :=
    evalDist_map_bijective_uniform_cross _ _ (Function.Involutive.bijective fun t => by
      funext T; by_cases hT : term = some T <;> simp [hT, BitVec.xor_assoc])
  have hpair : 𝒟[(fun p (j : C.Party) => if pair = some j then p j ^^^ c else p j) <$> ($ᵗ (C.Party → HashOutput))] =
      𝒟[$ᵗ (C.Party → HashOutput)] :=
    evalDist_map_bijective_uniform_cross _ _ (Function.Involutive.bijective fun p => by
      funext j; by_cases hj : pair = some j <;> simp [hj, BitVec.xor_assoc])
  have e : (fun own => shiftParts own term pair c) <$> sampleParts (C := C) = (do
      let parameter ← $ᵗ HashOutput
      let t ← (fun t (T : C.Term) => if term = some T then t T ^^^ c else t T) <$> ($ᵗ (C.Term → HashOutput))
      let q ← (fun p (j : C.Party) => if pair = some j then p j ^^^ c else p j) <$> ($ᵗ (C.Party → HashOutput))
      pure (⟨parameter, t, q⟩ : Parts C)) := by
    simp only [sampleParts, map_bind, map_pure, bind_map_left]
    rfl
  rw [e]
  unfold sampleParts
  refine evalDist_bind_congr' _ fun parameter => ?_
  rw [evalDist_bind, hterm, ← evalDist_bind]
  refine evalDist_bind_congr' _ fun t => ?_
  rw [evalDist_bind, hpair, ← evalDist_bind]

/-- The parts of all operators with one coordinate of operator `a` shifted. -/
def shiftAt (a : C.Party) (term : Option C.Term) (pair : Option C.Party) (c : HashOutput)
    (parts : C.Party → Parts C) : C.Party → Parts C :=
  fun i => if i = a then shiftParts (parts i) term pair c else parts i

theorem evalDist_shiftAt (a : C.Party) (term : Option C.Term) (pair : Option C.Party) (c : HashOutput) :
    𝒟[shiftAt a term pair c <$> Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] =
      𝒟[Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
  have h := sequenceFin_bind_pure (m := ProbComp) (fun _ : C.Party => sampleParts (C := C))
    (fun i own => if i = a then shiftParts own term pair c else own)
  rw [map_eq_bind_pure_comp]
  have : (pure ∘ shiftAt a term pair c : (C.Party → Parts C) → ProbComp (C.Party → Parts C)) =
      fun rs => pure fun i => if i = a then shiftParts (rs i) term pair c else rs i := rfl
  rw [this, ← h]
  refine evalDist_sequenceFin_congr _ _ fun i => ?_
  by_cases hi : i = a
  · simp only [hi, if_true]
    rw [bind_pure_comp, evalDist_shift_sampleParts]
  · simp only [hi, if_false, bind_pure]

/-- Two different coordinates of the parts collide with probability `2^-256`. -/
theorem probEvent_parts_collision (X Y : (C.Party → Parts C) → HashOutput) (a : C.Party) (term : Option C.Term)
    (pair : Option C.Party) (hX : ∀ c parts, X (shiftAt a term pair c parts) = X parts ^^^ c)
    (hY : ∀ c parts, Y (shiftAt a term pair c parts) = Y parts) :
    Pr[fun parts => X parts = Y parts | Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] =
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have huniform : 𝒟[(fun parts => X parts ^^^ Y parts) <$>
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] = 𝒟[$ᵗ HashOutput] := by
    refine evalDist_eq_uniform_of_probOutput_eq _ fun u v => ?_
    have hshift : 𝒟[(fun parts => X parts ^^^ Y parts) <$>
          Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] =
        𝒟[(fun d => d ^^^ (u ^^^ v)) <$> ((fun parts => X parts ^^^ Y parts) <$>
          Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C)))] :=
      calc _ = 𝒟[(fun parts => X parts ^^^ Y parts) <$> (shiftAt a term pair (u ^^^ v) <$>
              Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C)))] := by
            rw [evalDist_map, evalDist_map, evalDist_shiftAt]
        _ = _ := by
            rw [Functor.map_map, Functor.map_map]
            congr 2
            funext parts
            simp only [hX, hY, BitVec.xor_assoc, BitVec.xor_comm (u ^^^ v) (Y parts)]
    have hu : u = v ^^^ (u ^^^ v) := by
      rw [BitVec.xor_comm u v, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    have key := probOutput_map_injective ((fun parts => X parts ^^^ Y parts) <$>
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))) (xor_bijective (u ^^^ v)).1 v
    rw [← hu] at key
    rw [probOutput_def, hshift, ← probOutput_def]
    exact key
  have : Pr[fun parts => X parts = Y parts | Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] =
      Pr[= 0 | (fun parts => X parts ^^^ Y parts) <$> Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
    rw [probOutput_map]
    exact probEvent_ext fun parts _ => BitVec.xor_eq_zero_iff.symm
  rw [this, probOutput_def, huniform, ← probOutput_def, probOutput_uniformSample]

theorem card_term (C : Committee) : Fintype.card C.Term = C.n.choose (C.t - 1) := by
  convert Fintype.card_finset_len (α := C.Party) (C.t - 1)
  simp

theorem card_pair_le (C : Committee) : Fintype.card C.Pair ≤ C.n.choose 2 := by
  have hinj : Function.Injective fun p : C.Pair =>
      (⟨{p.1.1, p.1.2}, Finset.card_pair (ne_of_lt p.2)⟩ : {s : Finset C.Party // s.card = 2}) := by
    rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ h
    simp only [Subtype.mk.injEq] at h
    have ha : a ∈ ({a', b'} : Finset C.Party) := h ▸ by simp
    have hb : b ∈ ({a', b'} : Finset C.Party) := h ▸ by simp
    have ha' : a' ∈ ({a, b} : Finset C.Party) := h.symm ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb ha'
    simp only at hab hab'
    have : a = a' ∧ b = b' := by
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases ha' with h1 | h1 <;>
        first | exact ⟨rfl, rfl⟩ | (exfalso; subst_vars; exact lt_asymm hab hab') |
          (exfalso; exact lt_irrefl _ hab) | (exfalso; exact lt_irrefl _ hab') |
          (exfalso; subst_vars; exact lt_irrefl _ (hab.trans hab'))
    obtain ⟨rfl, rfl⟩ := this
    rfl
  calc Fintype.card C.Pair ≤ Fintype.card {s : Finset C.Party // s.card = 2} := Fintype.card_le_of_injective _ hinj
    _ = C.n.choose 2 := by rw [Fintype.card_finset_len, Fintype.card_fin]

theorem nodup_keygenInputs (parts : C.Party → Parts C)
    (hT : ∀ T T', termInput .keygen parts T = termInput .keygen parts T' → T = T')
    (hp : ∀ p p', pairInput .keygen parts p = pairInput .keygen parts p' → p = p') : (keygenInputs parts).Nodup := by
  unfold keygenInputs
  rw [List.nodup_cons, List.nodup_append]
  refine ⟨?_, (Finset.nodup_toList _).map hT, (Finset.nodup_toList _).map hp, ?_⟩
  · simp [parameterInput, termInput, pairInput]
  · intro a ha b hb e
    simp only [List.mem_map] at ha hb
    obtain ⟨T, -, rfl⟩ := ha
    obtain ⟨p, -, rfl⟩ := hb
    simp [termInput, pairInput] at e

theorem exists_first_holder (T : C.Term) : ∃ a rest, C.parties.filter (· ∈ C.holders T) = a :: rest := by
  have hcard : 0 < (C.holders T).card := by
    rw [Committee.holders, Finset.card_compl, Fintype.card_fin, T.2]
    unfold Committee.n
    have := C.one_le_t
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hcard
  rcases h : C.parties.filter (· ∈ C.holders T) with _ | ⟨a, rest⟩
  · have : j ∈ C.parties.filter (· ∈ C.holders T) := by simp [Committee.parties, hj]
    rw [h] at this
    cases this
  · exact ⟨a, rest, rfl⟩

theorem probEvent_termInput_eq (T T' : C.Term) :
    Pr[fun parts => T ≠ T' ∧ termInput .keygen parts T = termInput .keygen parts T' |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  by_cases hTT : T = T'
  · simp [hTT]
  obtain ⟨a, rest, ha⟩ := exists_first_holder T
  obtain ⟨b, rest', hb⟩ := exists_first_holder T'
  calc _ ≤ Pr[fun parts => (parts a).term T = (parts b).term T' |
        Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
        refine probEvent_mono fun parts _ h => ?_
        have := h.2
        simp only [termInput, ha, hb, List.map_cons, Query.derive.injEq, true_and, List.cons.injEq] at this
        exact this.1
    _ = _ := probEvent_parts_collision (fun parts => (parts a).term T) (fun parts => (parts b).term T') a (some T)
        none (fun c parts => by simp [shiftAt, shiftParts]) (fun c parts => by
          by_cases hba : b = a <;> simp [shiftAt, shiftParts, hba, hTT])

theorem probEvent_pairInput_eq (p p' : C.Pair) :
    Pr[fun parts => p ≠ p' ∧ pairInput .keygen parts p = pairInput .keygen parts p' |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  by_cases hpp : p = p'
  · simp [hpp]
  calc _ ≤ Pr[fun parts => (parts p.1.1).pair p.1.2 = (parts p'.1.1).pair p'.1.2 |
        Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
        refine probEvent_mono fun parts _ h => ?_
        have := h.2
        simp only [pairInput, Query.derive.injEq, true_and, List.cons.injEq] at this
        exact this.1
    _ = _ := probEvent_parts_collision (fun parts => (parts p.1.1).pair p.1.2)
        (fun parts => (parts p'.1.1).pair p'.1.2) p.1.1 none (some p.1.2)
        (fun c parts => by simp [shiftAt, shiftParts]) (fun c parts => by
          have hne : ¬ (p'.1.1 = p.1.1 ∧ p'.1.2 = p.1.2) := fun ⟨h1, h2⟩ =>
            hpp (Subtype.ext (Prod.ext h1.symm h2.symm))
          by_cases h1 : p'.1.1 = p.1.1
          · have h2 : p'.1.2 ≠ p.1.2 := fun h2 => hne ⟨h1, h2⟩
            simp [shiftAt, shiftParts, h1, Ne.symm h2]
          · simp [shiftAt, shiftParts, h1])

/-- Two derivations of one kind collide with probability at most `derivedKeyCollision`. -/
theorem probEvent_keygen_collision :
    Pr[fun parts => ¬ (keygenInputs parts).Nodup | Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      ((Fintype.card C.Term ^ 2 + Fintype.card C.Pair ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  calc _ ≤ Pr[fun parts => (∃ T ∈ Finset.univ, ∃ T' ∈ Finset.univ,
          T ≠ T' ∧ termInput .keygen parts T = termInput .keygen parts T') ∨
        (∃ p ∈ Finset.univ, ∃ p' ∈ Finset.univ, p ≠ p' ∧ pairInput .keygen parts p = pairInput .keygen parts p') |
        Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
        refine probEvent_mono fun parts _ hbad => ?_
        by_contra hgood
        push_neg at hgood
        exact hbad (nodup_keygenInputs parts (fun T T' h => by_contra fun hne => hgood.1 T (by simp) T' (by simp) hne h)
          fun p p' h => by_contra fun hne => hgood.2 p (by simp) p' (by simp) hne h)
    _ ≤ _ := probEvent_or_le _ _ _
    _ ≤ (∑ T : C.Term, ∑ T' : C.Term, (Fintype.card HashOutput : ℝ≥0∞)⁻¹) +
        ∑ p : C.Pair, ∑ p' : C.Pair, (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
        gcongr
        · refine (probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun T _ => ?_)
          exact (probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun T' _ => probEvent_termInput_eq T T')
        · refine (probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun p _ => ?_)
          exact (probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun p' _ => probEvent_pairInput_eq p p')
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

end Collision

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section KeygenCompleteness

open scoped ENNReal

variable {C : Committee} {E : Type}

theorem map_getD_idxOf {α : Type} [BEq α] [LawfulBEq α] (L : List α) (hL : L.Nodup) (l : List HashOutput)
    (hl : l.length = L.length) : L.map (fun a => l.getD (L.idxOf a) 0) = l := by
  refine List.ext_getElem (by simp [hl]) fun k hk _ => ?_
  simp only [List.getElem_map, hL.idxOf_getElem k (by simpa using hk), List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa [hl] using hk)]
  rfl

/-- Uniform values of the derivations give the keys of `KeyGen'`. -/
theorem evalDist_keysFromValues (parts : C.Party → Parts C) :
    𝒟[(fun values (i : C.Party) => some (keysFromValues values i)) <$>
        (keygenInputs parts).mapM (fun _ => $ᵗ HashOutput)] =
      𝒟[(fun r (i : C.Party) => some (r.2.2 i)) <$> prawnsKeyGen (C := C)] := by
  have hterms : 𝒟[(fun (l : List HashOutput) (T : C.Term) => l.getD (C.terms.idxOf T) 0) <$>
      C.terms.mapM (fun _ => $ᵗ HashOutput)] = 𝒟[$ᵗ (C.Term → HashOutput)] :=
    evalDist_listFunction C.terms (C.terms.idxOf ·) 0 (by simp [Committee.terms])
      (fun f => funext fun T => getD_terms_idxOf f 0 T) (map_getD_idxOf C.terms (Finset.nodup_toList _))
  have hpairs : 𝒟[(fun (l : List HashOutput) (p : C.Pair) => l.getD ((pairList C).idxOf p) 0) <$>
      (pairList C).mapM (fun _ => $ᵗ HashOutput)] = 𝒟[$ᵗ (C.Pair → HashOutput)] :=
    evalDist_listFunction (pairList C) ((pairList C).idxOf ·) 0 (by simp [pairList])
      (fun f => funext fun p => getD_pairList_idxOf f 0 p) (map_getD_idxOf (pairList C) (Finset.nodup_toList _))
  have hlen1 : ∀ l ∈ support (C.terms.mapM fun _ => $ᵗ HashOutput), l.length = C.terms.length := fun l hl => by
    by_contra hne
    exact probOutput_ne_zero_of_mem_support hl (by rw [probOutput_list_mapM, if_neg hne])
  have hlen2 : ∀ l ∈ support ((pairList C).mapM fun _ => $ᵗ HashOutput), l.length = (pairList C).length :=
    fun l hl => by
      by_contra hne
      exact probOutput_ne_zero_of_mem_support hl (by rw [probOutput_list_mapM, if_neg hne])
  have hmapM : (keygenInputs parts).mapM (fun _ => $ᵗ HashOutput) = (do
      let a ← $ᵗ HashOutput
      let l₁ ← C.terms.mapM (fun _ => $ᵗ HashOutput)
      let l₂ ← (pairList C).mapM (fun _ => $ᵗ HashOutput)
      pure (a :: (l₁ ++ l₂))) := by
    simp only [keygenInputs, List.mapM_cons, List.mapM_append, List.mapM_map, bind_assoc, pure_bind]
    rfl
  have htrunc : 𝒟[(truncateHash <$> ($ᵗ HashOutput) : ProbComp PublicParameter)] = 𝒟[$ᵗ PublicParameter] :=
    evalDist_truncateHash
  have hkeys : ∀ a (l₁ l₂ : List HashOutput), l₁.length = C.terms.length → ∀ i,
      keysFromValues (a :: (l₁ ++ l₂)) i = dealtKeys (truncateHash a) (fun T => l₁.getD (C.terms.idxOf T) 0)
        (fun p => l₂.getD ((pairList C).idxOf p) 0) i := by
    intro a l₁ l₂ hl i
    have hT : ∀ T : C.Term, C.terms.idxOf T < l₁.length := fun T => hl ▸
      List.idxOf_lt_length_of_mem (Finset.mem_toList.mpr (Finset.mem_univ T))
    unfold keysFromValues dealtKeys
    congr 1
    · funext T
      split_ifs
      · rw [Nat.add_comm, List.getD_cons_succ, List.getD_eq_getElem?_getD, List.getElem?_append_left (hT T),
          ← List.getD_eq_getElem?_getD]
      · rfl
    · funext j
      split_ifs
      · rfl
      · rw [Nat.add_assoc, Nat.add_comm, List.getD_cons_succ, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by omega), ← hl, Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  rw [hmapM]
  simp only [map_bind, map_pure]
  unfold prawnsKeyGen
  simp only [map_bind, map_pure]
  calc _ = 𝒟[do
        let a ← $ᵗ HashOutput
        let l₁ ← C.terms.mapM (fun _ => $ᵗ HashOutput)
        let l₂ ← (pairList C).mapM (fun _ => $ᵗ HashOutput)
        pure fun i => some (dealtKeys (truncateHash a) (fun T => l₁.getD (C.terms.idxOf T) 0)
          (fun p => l₂.getD ((pairList C).idxOf p) 0) i)] := by
        refine evalDist_bind_congr' _ fun a => evalDist_bind_congr fun l₁ hl₁ => evalDist_bind_congr' _ fun l₂ => ?_
        simp only [hkeys a l₁ l₂ (hlen1 l₁ hl₁)]
    _ = 𝒟[do
        let parameter ← (truncateHash <$> ($ᵗ HashOutput) : ProbComp PublicParameter)
        let seeds ← (fun (l : List HashOutput) (T : C.Term) => l.getD (C.terms.idxOf T) 0) <$>
          C.terms.mapM (fun _ => $ᵗ HashOutput)
        let pairKeys ← (fun (l : List HashOutput) (p : C.Pair) => l.getD ((pairList C).idxOf p) 0) <$>
          (pairList C).mapM (fun _ => $ᵗ HashOutput)
        pure fun i => some (dealtKeys parameter seeds pairKeys i)] := by
        simp only [bind_map_left]
    _ = _ := by
        rw [evalDist_bind, htrunc, ← evalDist_bind]
        refine evalDist_bind_congr' _ fun parameter => ?_
        rw [evalDist_bind, hterms, ← evalDist_bind]
        refine evalDist_bind_congr' _ fun seeds => ?_
        rw [evalDist_bind, hpairs, ← evalDist_bind]

/-- `KeygenCompletenessStatement`. An honest keygen gives the keys of `F_keygen`, except when two
derived keys of one kind have the same parts. -/
theorem keygenCompleteness (prims : Primitives) : KeygenCompletenessStatement (C := C) (E := E) prims := by
  unfold KeygenCompletenessStatement
  rw [completes_iff]
  intro x _
  set P := Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))
  set F := fun parts => (fun values (i : C.Party) => some (keysFromValues values i)) <$>
    (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) ((keygenInputs parts).mapM hashQuery)).run' ∅
  set G := (fun r (i : C.Party) => some (r.2.2 i)) <$> prawnsKeyGen (C := C)
  have hreal : 𝒟[(simulateQ (localAnswer prims) (honestStart (fun i => (fun i (_ : Unit) =>
      (keygen i : PartyM C E RealSpec (Keys C))) i (x i)) >>=
        honestRounds noFunctionality (fun l => l.elim) setupRounds)).run' ∅] = 𝒟[P >>= F] := by
    rw [(sameRun_keygen (E := E) prims).run'_eq, evalDist_keygen_derivations, keygen_real]
  have hideal : 𝒟[(simulateQ (localAnswer prims) (simulateQ (replyImpl (fun _ => (Finset.univ : Finset C.Party)))
      ((Fkeygen (C := C)).run noCoalition fun i => some (x i)))).run' ∅] = 𝒟[P >>= fun _ => G] := by
    rw [keygen_ideal]
    refine evalDist_ext fun y => ?_
    rw [probOutput_bind_const]
    simp [G]
  have hgood : ∀ parts, ¬ ¬ (keygenInputs parts).Nodup → 𝒟[F parts] = 𝒟[G] := by
    intro parts hnd
    rw [not_not] at hnd
    simp only [F, G]
    rw [evalDist_map, evalDist_fresh_mapM prims _ ∅ hnd (fun _ _ => rfl)
      (fun q hq => by
        simp only [keygenInputs, List.mem_cons, List.mem_append, List.mem_map] at hq
        rcases hq with rfl | ⟨T, -, rfl⟩ | ⟨p, -, rfl⟩ <;> rintro ⟨_, h, _⟩ <;> cases h),
      ← evalDist_map, evalDist_keysFromValues]
  have hbound := probEvent_keygen_collision (C := C)
  rw [card_bitVec] at hbound
  calc tvDist _ _ = tvDist (P >>= F) (P >>= fun _ => G) := by
        unfold tvDist
        rw [hreal, hideal]
    _ ≤ (Pr[fun parts => ¬ (keygenInputs parts).Nodup | P]).toReal :=
        tvDist_bind_left_event_le P F (fun _ => G) _ hgood
    _ ≤ ((((Fintype.card C.Term ^ 2 + Fintype.card C.Pair ^ 2 : ℕ) : ℝ≥0∞) *
          ((2 ^ hashOutputBits : ℕ) : ℝ≥0∞)⁻¹)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (by simp)) hbound
    _ = ((Fintype.card C.Term ^ 2 + Fintype.card C.Pair ^ 2 : ℕ) : ℝ) / 2 ^ 256 := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast, div_eq_mul_inv]
        norm_num [hashOutputBits]
    _ ≤ derivedKeyCollision C := by
        unfold derivedKeyCollision termCount
        gcongr
        · rw [card_term]
        · exact card_pair_le C

end KeygenCompleteness

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section KeygenSecurity

variable {C : Committee} {E : Type} (prims : Primitives)

/-- A simulation into the state of the ideal run whose local queries go to the free copy costs
nothing on a lifted sampling. -/
theorem costLe_stateT_liftComp {σ L R α : Type}
    (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ (OracleComp (WorldSpec C))))
    (himpl : ∀ (t : (LocalSpec C).Domain) st,
      (impl (.inl t)).run st = (fun a => (a, st)) <$> free (OracleComp.lift (OracleSpec.query t)))
    (p : ProbComp α) : ∀ st, CostLe prims ((simulateQ impl (liftComp p (LocalSpec C + (L →ₒ R)))).run st) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => intro st; exact CostLe.pure prims _
  | query_bind t k ih =>
    intro st
    rw [liftComp_bind, simulateQ_bind, StateT.run_bind]
    have : simulateQ impl (liftComp (liftM (OracleSpec.query t) : ProbComp _) (LocalSpec C + (L →ₒ R))) =
        impl (.inl (.inl t)) := by
      rw [liftComp_query]
      exact (simulateQ_query _ _).trans (id_map _)
    rw [this]
    erw [himpl (.inl t) st]
    exact ((CostLe.map prims _ (CostLe.free prims _)).bind prims
      fun (p : unifSpec.Range t × σ) => ih p.1 p.2).mono prims (by simp)

theorem costLe_simulateQ_leak {σ L R : Type}
    (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ (OracleComp (WorldSpec C)))) (l : L) (st : σ) {n : ℕ}
    (h : CostLe prims ((impl (.inr l)).run st) n) :
    CostLe prims ((simulateQ impl (leak (C := C) (R := R) l)).run st) n := by
  unfold leak
  erw [simulateQ_query]
  simpa using h

/-- One answer of `keygenSimulator` costs one round of the adversary, the programming queries, and two
more rounds. -/
theorem costLe_keygenSimulator_answer (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) (st : (keygenSimulator D A).State)
    (l : PublicParameter × (C.Party → Option (Keys C))) :
    CostLe prims ((keygenSimulator D A).answer st l)
      (step + (1 + (C.terms.length * 1 + (C.parties.length * (C.parties.length * 1) + (setupRounds - 1) * step)))) := by
  rcases l with ⟨parameter, corrupt⟩
  unfold keygenSimulator
  dsimp only
  refine ((CostLe.free prims _).bind prims fun parts => ?_).mono prims (Nat.zero_add _).le
  refine ((CostLe.sequenceFin prims _ fun i => ?_).bind prims fun steps => ?_).mono prims (Nat.zero_add _).le
  · split_ifs
    · exact CostLe.pure prims _
    · exact CostLe.free prims _
  refine (CostLe.stepRound_observed prims D A step hround _ _).bind prims fun r => ?_
  rcases r with ⟨⟨state, steps, sent⟩, calls⟩
  dsimp only
  refine ((CostLe.free prims _).bind prims fun high => ?_).mono prims (Nat.zero_add _).le
  refine (CostLe.program prims _ _).bind prims fun _ => ?_
  refine (CostLe.mapM prims _ 1 C.terms fun T _ => ?_).bind prims fun _ => ?_
  · split
    · exact CostLe.program prims _ _
    · exact (CostLe.pure prims _).mono prims (Nat.zero_le _)
  refine (CostLe.mapM prims _ (C.parties.length * 1) C.parties fun j _ =>
    CostLe.mapM prims _ 1 C.parties fun i _ => ?_).bind prims fun _ => ?_
  · by_cases hji : j ∈ D.1 ∧ i ∉ D.1
    · rw [dif_pos hji]; exact CostLe.program prims _ _
    · rw [dif_neg hji]; exact (CostLe.pure prims _).mono prims (Nat.zero_le _)
  refine ((CostLe.executeRounds_observed prims D A step hround (setupRounds - 1) _ _).bind prims fun r => ?_).mono
    prims (Nat.add_zero _).le
  rcases r with ⟨⟨state, keys⟩, rest⟩
  exact CostLe.pure prims _

theorem keygenSimulator_queryBound (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit)
    (z : Aux) (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    HasHashQueryBound (runWorld prims (distinguish (idealExecution (fun oa => oa) D Fkeygen
      (keygenSimulator D A) x z) Z)) (q + keygenOverhead C) := by
  obtain ⟨start, step, final, hsum, hs, hr, ha, hz⟩ := hq
  apply hasHashQueryBound_of_costLe
  unfold distinguish idealExecution
  simp only [bind_assoc]
  have hstart : CostLe prims ((keygenSimulator D A).start (corruptInputs D x) z) start :=
    ((CostLe.observe prims _ start (hs _ _)).bind prims fun _ => CostLe.pure prims _).mono prims (by simp)
  have hanswer := costLe_keygenSimulator_answer prims D A step hr
  set M := step + (1 + (C.terms.length * 1 + (C.parties.length * (C.parties.length * 1) +
    (setupRounds - 1) * step))) with hM
  refine CostLe.mono prims (CostLe.bind prims hstart (m := 0 + ((M + 0) + (0 + (0 + (0 + final))))) fun st => ?_) ?_
  · unfold Fkeygen
    simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
    refine (costLe_stateT_liftComp prims _ ?himpl _ st).bind prims fun p => ?_
    case himpl => intro t st; rfl
    refine (costLe_simulateQ_leak prims _ _ _ ?hl).bind prims fun r => ?_
    case hl => exact (hanswer _ _).bind prims fun _ => CostLe.pure prims _
    refine (CostLe.pure prims _).bind prims fun out => ?_
    refine (CostLe.pure prims _).bind prims fun o => ?_
    refine (CostLe.pure prims _).bind prims fun r' => ?_
    exact CostLe.of_counted prims _ _ (hz _)
  · have hterms : C.terms.length = C.n.choose (C.t - 1) := by
      rw [Committee.terms, Finset.length_toList, Finset.card_univ, card_term]
    have hparties : C.parties.length = C.n := by simp [Committee.parties]
    rw [hM, hterms, hparties]
    unfold keygenOverhead termCount
    simp only [setupRounds] at hsum ⊢
    nlinarith [hsum]

/-- The distance half of `KeygenSecurityStatement`. -/
def KeygenSecurityDistance (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    |accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) Z) -
      accepts prims (distinguish (idealExecution (fun oa => oa) D Fkeygen (keygenSimulator D A) x z) Z)| ≤
        keygenHashError C q

/-- `KeygenSecurityStatement` from its distance half. The query half is `keygenSimulator_queryBound`. -/
theorem keygenSecurity_of_distance (h : KeygenSecurityDistance (C := C) (E := E) prims) :
    KeygenSecurityStatement (C := C) (E := E) prims :=
  fun D A x z Z q _ hq => ⟨keygenSimulator_queryBound prims D A x z Z q hq, h D A x z Z q hq⟩

/-- The coupling of the keygen run and the ideal run of `keygenSimulator`, identical until bad. -/
def KeygenCoupling : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    ∃ oa ob : OracleComp (WorldSpec C) (Bool × Bool),
      accepts prims (Prod.fst <$> oa) = accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) Z) ∧
      accepts prims (Prod.fst <$> ob) =
        accepts prims (distinguish (idealExecution (fun oa => oa) D Fkeygen (keygenSimulator D A) x z) Z) ∧
      Pr[fun r => r.1 = (true, false) | runWorld prims oa] = Pr[fun r => r.1 = (true, false) | runWorld prims ob] ∧
      Pr[fun r => r.1.2 = true | runWorld prims oa].toReal ≤ keygenHashError C q ∧
      Pr[fun r => r.1.2 = true | runWorld prims ob].toReal ≤ keygenHashError C q

/-- `KeygenSecurityDistance` from the coupling. -/
theorem keygenDistance_of_coupling (h : KeygenCoupling (C := C) (E := E) prims) :
    KeygenSecurityDistance (C := C) (E := E) prims := by
  intro D A x z Z q hq
  obtain ⟨oa, ob, hoa, hob, heq, hbad₁, hbad₂⟩ := h D A x z Z q hq
  have hdist := abs_accepts_sub_le_of_eq_until_bad prims oa ob heq
  rw [hoa, hob] at hdist
  exact hdist.trans (max_le hbad₁ hbad₂)

/-- `keygenHashError` covers `q · S / 2^256` for a counted call at one of the `S` honest points and
`(q + S)² / 2^257` for a collision of two of the `q + S` points. -/
theorem guess_add_collision_le_keygenHashError (q : ℕ) :
    ((q * keygenSecrets C : ℕ) : ℝ) / 2 ^ 256 + ((q + keygenSecrets C) ^ 2 : ℕ) / 2 ^ 257 ≤ keygenHashError C q := by
  unfold keygenHashError
  set S := keygenSecrets C
  have h257 : (2 : ℝ) ^ 257 = 2 * 2 ^ 256 := by rw [pow_succ]; ring
  rw [h257, div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  have hq : (0 : ℝ) ≤ q := q.cast_nonneg
  have hS : (0 : ℝ) ≤ S := S.cast_nonneg
  have key : (q : ℝ) * S * (2 * 2 ^ 256) + 2 ^ 256 * (q + S) ^ 2 ≤ (q + S) ^ 2 * (2 * 2 ^ 256) := by
    nlinarith [sq_nonneg ((q : ℝ) - S), mul_nonneg hq hS, sq_nonneg (q : ℝ), sq_nonneg (S : ℝ),
      (by positivity : (0 : ℝ) < 2 ^ 256)]
  nlinarith [key, (by positivity : (0 : ℝ) < 2 ^ 256)]

/-- `KeygenSecurityStatement` from the coupling. -/
theorem keygenSecurity_of_coupling (h : KeygenCoupling (C := C) (E := E) prims) :
    KeygenSecurityStatement (C := C) (E := E) prims :=
  keygenSecurity_of_distance prims (keygenDistance_of_coupling prims h)

end KeygenSecurity

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The complete private transcript of one round, used only to define bad events. -/
structure KeygenRoundTrace (C : Committee) (E : Type) where
  queries : (WorldSpec C).QueryLog
  outgoing : C.Party → Mail C E
  sent : C.Party → Mail C E

/-- Recording each round separately preserves the boundary before honest reveals. -/
def keygenTraceRounds (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    ℕ → A.State → (C.Party → Step C E RealSpec (Keys C)) →
      OracleComp (WorldSpec C) ((A.State × (C.Party → Option (Keys C))) × List (KeygenRoundTrace C E))
  | 0, state, steps => pure ((state, fun i => (steps i).output), [])
  | fuel + 1, state, steps =>
    if ∀ i, i ∉ D.1 → (steps i).isDone then pure ((state, fun i => (steps i).output), []) else do
      let (r, log) ← (simulateQ loggingOracle (stepRound worldRoles D A noFunctionality state steps)).run
      let (out, rest) ← keygenTraceRounds D A fuel r.1 r.2.1
      pure (out, ⟨log, fun i => (steps i).outbox, r.2.2⟩ :: rest)

theorem fst_keygenTraceRounds (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    ∀ fuel state steps, Prod.fst <$> keygenTraceRounds D A fuel state steps =
      executeRounds worldRoles D A noFunctionality fuel state steps
  | 0, state, steps => by simp [keygenTraceRounds, executeRounds]
  | fuel + 1, state, steps => by
    simp only [keygenTraceRounds, executeRounds]
    split_ifs
    · simp
    · simp only [map_bind, map_pure]
      have h : ∀ r : A.State × (C.Party → Step C E RealSpec (Keys C)) × (C.Party → Mail C E),
          (keygenTraceRounds D A fuel r.1 r.2.1 >>= fun p => pure p.1) =
            executeRounds worldRoles D A noFunctionality fuel r.1 r.2.1 := by
        intro r
        simpa only [map_eq_bind_pure_comp, Function.comp_def] using
          fst_keygenTraceRounds D A fuel r.1 r.2.1
      simp only [h]
      exact loggingOracle.run_simulateQ_bind_fst
        (stepRound worldRoles D A noFunctionality state steps) (fun r =>
        executeRounds worldRoles D A noFunctionality fuel r.1 r.2.1)

structure KeygenRealTrace (C : Committee) (E : Type) where
  start : (WorldSpec C).QueryLog
  honestStart : (WorldSpec C).QueryLog
  rounds : List (KeygenRoundTrace C E)
  final : (WorldSpec C).QueryLog

/-- The real game with private logs, including one log for each synchronous round. -/
def keygenRealTrace (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    OracleComp (WorldSpec C) (Bool × KeygenRealTrace C E) := do
  let (state, startLog) ← (simulateQ loggingOracle (worldRoles.adversary (A.start (corruptInputs D x) z))).run
  let (steps, honestLog) ← (simulateQ loggingOracle (startSteps worldRoles D fun i =>
    (keygen i : PartyM C E RealSpec (Keys C)))).run
  let (out, rounds) ← keygenTraceRounds D A setupRounds state steps
  let (accept, finalLog) ← (simulateQ loggingOracle (worldRoles.adversary (Z out))).run
  pure (accept, ⟨startLog, honestLog, rounds, finalLog⟩)

theorem fst_keygenRealTrace (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    Prod.fst <$> keygenRealTrace D A x z Z =
      distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) Z := by
  unfold keygenRealTrace distinguish realExecution executePhase
  simp only [map_bind, map_pure, bind_assoc]
  simp only [loggingOracle.run_simulateQ_bind_fst]
  simp only [bind_pure]
  conv_rhs =>
    rw [← loggingOracle.fst_map_run_simulateQ (worldRoles.adversary (A.start (corruptInputs D x) z)), bind_map_left]
  refine bind_congr fun start => ?_
  conv_rhs =>
    rw [← loggingOracle.fst_map_run_simulateQ (startSteps worldRoles D fun i =>
      (keygen i : PartyM C E RealSpec (Keys C))), bind_map_left]
  refine bind_congr fun initial => ?_
  rw [← fst_keygenTraceRounds D A setupRounds start.1 initial.1, bind_map_left]

/-- A private bad flag may inspect round boundaries without changing real acceptance. -/
def keygenFlaggedReal (bad : KeygenRealTrace C E → Bool) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) : OracleComp (WorldSpec C) (Bool × Bool) :=
  (fun r => (r.1, bad r.2)) <$> keygenRealTrace D A x z Z

theorem keygenFlaggedReal_accepts (prims : Primitives) (bad : KeygenRealTrace C E → Bool)
    (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    accepts prims (Prod.fst <$> keygenFlaggedReal bad D A x z Z) =
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) Z) := by
  simp only [keygenFlaggedReal, Functor.map_map]
  rw [fst_keygenRealTrace]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The programming query separates pre-reveal queries in this log from subsequent queries. -/
def keygenFlaggedIdeal (bad : (WorldSpec C).QueryLog → Bool) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) : OracleComp (WorldSpec C) (Bool × Bool) :=
  (fun r => (r.1, bad r.2)) <$> (simulateQ loggingOracle
    (distinguish (idealExecution (fun oa => oa) D Fkeygen (keygenSimulator D A) x z) Z)).run

theorem keygenFlaggedIdeal_accepts (prims : Primitives) (bad : (WorldSpec C).QueryLog → Bool)
    (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    accepts prims (Prod.fst <$> keygenFlaggedIdeal bad D A x z Z) =
      accepts prims (distinguish (idealExecution (fun oa => oa) D Fkeygen (keygenSimulator D A) x z) Z) := by
  simp only [keygenFlaggedIdeal, Functor.map_map]
  rw [loggingOracle.fst_map_run_simulateQ]

/-- Programming a fresh random-oracle input inserts the prescribed answer. -/
theorem programAnswer_run_fresh {q : Query C} (hfixed : ¬ IsFixed q)
    (s : HashCache C) (hfresh : s q = none) (y : HashOutput) :
    (programAnswer (q, y)).run s = pure (true, s.cacheQuery q y) := by
  change ¬ (∃ input, q = .hash input ∧ MpcInput input) at hfixed
  simp [programAnswer, StateT.run_bind, StateT.run_get, hfixed, hfresh, StateT.run_set]

/-- At a fresh point, first sampling an answer and then programming is exactly a lazy read,
including the final cache. -/
theorem sample_program_eq_hashAnswer (prims : Primitives) {q : Query C} (hfixed : ¬ IsFixed q)
    (s : HashCache C) (hfresh : s q = none) :
    ((do
      let y ← StateT.lift ($ᵗ HashOutput)
      let _ ← programAnswer (q, y)
      pure y : StateT (HashCache C) ProbComp HashOutput).run s) =
        (hashAnswer prims q).run s := by
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  simp only [programAnswer_run_fresh hfixed s hfresh, pure_bind, StateT.run_pure]
  rw [hashAnswer_of_not_isFixed prims hfixed, OracleSpec.randomOracle,
    QueryImpl.withCaching_run_none _ hfresh]
  rfl

/-- The local swap remains valid under an arbitrary cache-dependent continuation. -/
theorem sample_program_bind_eq_hashAnswer (prims : Primitives) {α : Type} {q : Query C}
    (hfixed : ¬ IsFixed q) (s : HashCache C) (hfresh : s q = none)
    (k : HashOutput → StateT (HashCache C) ProbComp α) :
    ((do
      let y ← StateT.lift ($ᵗ HashOutput)
      let _ ← programAnswer (q, y)
      k y : StateT (HashCache C) ProbComp α).run s) =
        (hashAnswer prims q >>= k).run s := by
  have h := sample_program_eq_hashAnswer prims hfixed s hfresh
  have heq : (do
      let y ← StateT.lift ($ᵗ HashOutput)
      let _ ← programAnswer (q, y)
      k y : StateT (HashCache C) ProbComp α) =
      (do
        let y ← StateT.lift ($ᵗ HashOutput)
        let _ ← programAnswer (q, y)
        pure y : StateT (HashCache C) ProbComp HashOutput) >>= k := by
    simp only [bind_assoc, pure_bind]
  rw [heq, StateT.run_bind, h, StateT.run_bind]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- A search returning a unique value finds it as soon as any matching entry is present. -/
theorem findSome_eq_of_unique {α β : Type} (f : α → Option β) (l : List α) (b : β)
    (hex : ∃ a ∈ l, f a = some b)
    (hunique : ∀ a ∈ l, ∀ b', f a = some b' → b' = b) : l.findSome? f = some b := by
  cases h : l.findSome? f with
  | none =>
    obtain ⟨a, ha, hf⟩ := hex
    have hn := List.findSome?_eq_none_iff.mp h a ha
    rw [hf] at hn
    contradiction
  | some b' =>
    obtain ⟨a, ha, hf⟩ := List.exists_of_findSome?_eq_some h
    rw [hunique a ha b' hf]

/-- If the actual opening was observed before the commitment was sent, and no other observed
opening has the same commitment, extraction returns exactly that opening. -/
theorem extractReveal_eq_of_unique (calls : CallLog C) (sent : C.Party → Mail C E)
    (j i : C.Party) (reveal : List HashOutput) (value : HashOutput)
    (hcall : (.commit .keygen j i reveal, value) ∈ calls)
    (hsent : [value] = Msg.hashesOf (sent j i))
    (hunique : ∀ reveal' value', (.commit .keygen j i reveal', value') ∈ calls →
      [value'] = Msg.hashesOf (sent j i) → reveal' = reveal) :
    extractReveal calls sent j i = reveal := by
  unfold extractReveal
  have h := findSome_eq_of_unique
    (fun (q, out) => match q with
      | .commit .keygen j' i' opening =>
          if j' = j ∧ i' = i ∧ [out] = Msg.hashesOf (sent j i) then some opening else none
      | _ => none) calls reveal
    (by exact ⟨(.commit .keygen j i reveal, value), hcall, by simp [hsent]⟩)
    (by
      rintro ⟨q, out⟩ hmem opening hmatch
      cases q <;> simp only at hmatch
      all_goals try contradiction
      rename_i phase j' i' opening'
      cases phase <;> simp only at hmatch
      · split_ifs at hmatch with hm
        obtain ⟨rfl, rfl, hout⟩ := hm
        exact (Option.some.inj hmatch).symm.trans (hunique opening' out hmem hout)
      · contradiction)
  exact congrArg (fun o : Option (List HashOutput) => o.getD []) h

/-- The uniqueness premise of extraction follows from collision-freedom on the observed inputs. -/
theorem extractReveal_eq_of_no_collision (calls : CallLog C) (sent : C.Party → Mail C E)
    (j i : C.Party) (reveal : List HashOutput) (value : HashOutput)
    (hcall : (.commit .keygen j i reveal, value) ∈ calls)
    (hsent : [value] = Msg.hashesOf (sent j i))
    (hnocollision : ∀ q y q' y', (q, y) ∈ calls → (q', y') ∈ calls → y = y' → q = q') :
    extractReveal calls sent j i = reveal := by
  apply extractReveal_eq_of_unique calls sent j i reveal value hcall hsent
  intro reveal' value' hcall' hsent'
  have hv : value' = value := by simpa using hsent'.trans hsent.symm
  have hq := hnocollision _ _ _ _ hcall' hcall hv
  exact Query.commit.inj hq |>.2.2.2

/-- The number of terms grows enough to cover the small-committee slack in the query count. -/
theorem threshold_le_term_count (C : Committee) : C.t ≤ C.n.choose (C.t - 1) := by
  have hn : C.t ≤ C.n := by have := C.one_le_t; unfold Committee.n; omega
  have h := Nat.choose_le_choose (C.t - 1) hn
  have ht : C.t = (C.t - 1) + 1 := by have := C.one_le_t; omega
  have heq : C.t.choose (C.t - 1) = C.t := by
    calc C.t.choose (C.t - 1) = ((C.t - 1) + 1).choose (C.t - 1) := congrArg (fun n => n.choose (C.t - 1)) ht
      _ = C.t - 1 + 1 := Nat.choose_succ_self_right _
      _ = C.t := ht.symm
  rwa [heq] at h

/-- A counting envelope for distinct free inputs. Commitments and shared-key hashes contribute
`honest * n` each; fresh opening checks contribute `honest * (corrupt + 1)`; parameter derivations
contribute `honest`; term derivations contribute at most `t * choose n (t - 1)`; pair derivations
contribute at most `choose n 2`. -/
theorem keygen_freeInput_envelope_le_secrets (C : Committee) (honest corrupt : ℕ)
    (hpartition : honest + corrupt = C.n) :
    honest * (2 * C.n + corrupt + 2) + C.t * C.n.choose (C.t - 1) + C.n.choose 2 ≤
      keygenSecrets C := by
  have ht := C.one_le_t
  have hterms := threshold_le_term_count C
  have hbudget : honest * (2 * C.n + corrupt + 2) ≤ C.n * (2 * C.n + 2) := by
    nlinarith [sq_nonneg corrupt]
  have hn : C.n + 1 = 2 * C.t := by unfold Committee.n; omega
  have hsmall : 2 * C.t ≤ C.t * C.n.choose (C.t - 1) + 2 := by
    by_cases ht1 : C.t = 1
    · simp [ht1]
    · have ht2 : 2 ≤ C.t := by omega
      nlinarith
  have hnT : (C.n + 1) * C.n.choose (C.t - 1) = 2 * (C.t * C.n.choose (C.t - 1)) := by
    rw [hn, mul_assoc]
  unfold keygenSecrets termCount
  nlinarith [hnT]

/-- Every term has exactly `t` holders. -/
theorem keygen_card_holders (C : Committee) (T : C.Term) : (C.holders T).card = C.t := by
  rw [Committee.holders, Finset.card_compl, Fintype.card_fin, T.2]
  have := C.one_le_t
  unfold Committee.n
  omega

/-- A finite cover of the free inputs, grouped by the six places where keygen hashes.
The opening family contains only corrupt senders and the unused self opening; honest openings
reuse a commitment input. The pair family has one input for each unordered pair. -/
def keygenFreeInputCover (D : C.Coalition)
    (commit opening shared : C.Party → C.Party → Query C)
    (parameter : C.Party → Query C) (term : C.Party → C.Term → Query C)
    (pair : C.Pair → Query C) : List (Query C) :=
  let honest := D.1ᶜ.toList
  honest.flatMap (fun i => C.parties.map (commit i)) ++
    honest.flatMap (fun i => (i :: D.1.toList).map (opening i)) ++
    honest.map parameter ++
    C.terms.flatMap (fun T => (C.holders T).toList.map (fun i => term i T)) ++
    (pairList C).map pair ++
    honest.flatMap (fun i => C.parties.map (shared i))

theorem keygenFreeInputCover_length_le (D : C.Coalition)
    (commit opening shared : C.Party → C.Party → Query C)
    (parameter : C.Party → Query C) (term : C.Party → C.Term → Query C)
    (pair : C.Pair → Query C) :
    (keygenFreeInputCover D commit opening shared parameter term pair).length ≤ keygenSecrets C := by
  have hp : C.parties.length = C.n := by simp [Committee.parties]
  have ht : C.terms.length = C.n.choose (C.t - 1) := by
    simp [Committee.terms]
  have hpair : (pairList C).length ≤ C.n.choose 2 := by
    simpa [pairList] using card_pair_le C
  have hpartition : D.1ᶜ.card + D.1.card = C.n := by
    simpa only [Fintype.card_fin] using Finset.card_compl_add_card D.1
  have h := keygen_freeInput_envelope_le_secrets C D.1ᶜ.card D.1.card hpartition
  simp only [keygenFreeInputCover, List.length_append, List.length_flatMap,
    List.length_map, List.length_cons, Finset.length_toList, keygen_card_holders, hp,
    List.map_const', List.sum_replicate, smul_eq_mul, ht]
  nlinarith

/-- A set covered by the list is bounded by the fixed statement's `keygenSecrets`. -/
theorem keygenFreeInputCover_card_le (D : C.Coalition)
    (commit opening shared : C.Party → C.Party → Query C)
    (parameter : C.Party → Query C) (term : C.Party → C.Term → Query C)
    (pair : C.Pair → Query C) (inputs : Finset (Query C))
    (hcover : ∀ q ∈ inputs, q ∈ keygenFreeInputCover D commit opening shared parameter term pair) :
    inputs.card ≤ keygenSecrets C := by
  calc inputs.card ≤ (keygenFreeInputCover D commit opening shared parameter term pair).toFinset.card :=
      Finset.card_le_card (fun q hq => List.mem_toFinset.mpr (hcover q hq))
    _ ≤ (keygenFreeInputCover D commit opening shared parameter term pair).length := List.toFinset_card_le _
    _ ≤ keygenSecrets C := keygenFreeInputCover_length_le D commit opening shared parameter term pair

/-- The honest sender's fields in a received reveal agree with the sampled fields. -/
theorem setupView_honest_sender (D : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ D.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .keygen (parts j) j i)
    (i j : C.Party) (hj : j ∉ D.1) :
    setupView .keygen i (parts i) (revealed i) j = honestView (E := E) .keygen parts i j := by
  by_cases hji : j = i
  · subst j; simp [setupView, honestView]
  · rw [honestView_ne _ _ hji]
    simp only [setupView, if_neg hji, hreceived i j hj hji]

def keygenPairViewInput (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (i : C.Party) (p : C.Pair) : Query C :=
  let view := setupView .keygen i (parts i) (revealed i)
  .derive .keygen .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1]

/-- One representative per unordered pair suffices, even when corrupt parties equivocate. -/
def keygenPairRepresentative (D : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (p : C.Pair) : Query C :=
  keygenPairViewInput parts revealed (if p.1.1 ∈ D.1 then p.1.2 else p.1.1) p

theorem keygenPairViewInput_eq_representative (D : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ D.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .keygen (parts j) j i)
    (i : C.Party) (hi : i ∉ D.1) (p : C.Pair) (hip : p.1.1 = i ∨ p.1.2 = i) :
    keygenPairViewInput parts revealed i p = keygenPairRepresentative D parts revealed p := by
  rcases hip with hleft | hright
  · simp only [keygenPairRepresentative, hleft, if_neg hi]
  · by_cases hleft : p.1.1 ∈ D.1
    · simp only [keygenPairRepresentative, if_pos hleft, hright]
    · have hright' : p.1.2 ∉ D.1 := hright ▸ hi
      unfold keygenPairRepresentative
      rw [if_neg hleft]
      unfold keygenPairViewInput
      dsimp only
      rw [setupView_honest_sender D parts revealed hreceived i p.1.1 hleft,
        setupView_honest_sender D parts revealed hreceived i p.1.2 hright',
        setupView_honest_sender D parts revealed hreceived p.1.1 p.1.1 hleft,
        setupView_honest_sender D parts revealed hreceived p.1.1 p.1.2 hright']
      rw [honestView_pair .keygen parts (Or.inr hright),
        honestView_pair .keygen parts (Or.inl hright),
        honestView_pair .keygen parts (Or.inl rfl),
        honestView_pair .keygen parts (Or.inr rfl)]

/-- An honest opening check either reuses the honest sender's commitment input or belongs
to the family of corrupt/self openings. -/
theorem keygen_openInput_covered (D : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ D.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .keygen (parts j) j i)
    (shared : C.Party → C.Party → Query C) (parameter : C.Party → Query C)
    (term : C.Party → C.Term → Query C) (pair : C.Pair → Query C)
    (i j : C.Party) (hi : i ∉ D.1) :
    Query.commit .keygen j i (Msg.hashesOf (revealed i j)) ∈
      keygenFreeInputCover D
        (fun i j => .commit .keygen i j (revealTo .keygen (parts i) i j))
        (fun i j => .commit .keygen j i (Msg.hashesOf (revealed i j)))
        shared parameter term pair := by
  simp only [keygenFreeInputCover, List.mem_append, List.mem_flatMap, List.mem_map,
    Finset.mem_toList, Finset.mem_compl, Committee.parties, List.mem_finRange, true_and,
    List.mem_cons] 
  by_cases hj : j ∈ D.1
  · aesop
  · by_cases hji : j = i
    · subst j; aesop
    · have hq := hreceived i j hj hji
      aesop

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

theorem relabelHashCache_query (e : Query C ≃ Query C) (s : HashCache C)
    (q : Query C) (y : HashOutput) :
    relabelHashCache e (s.cacheQuery q y) = (relabelHashCache e s).cacheQuery (e q) y := by
  funext q'
  simp only [relabelHashCache, QueryCache.cacheQuery]
  by_cases h : q' = e q
  · subst q'; rw [Equiv.symm_apply_apply]; simp
  · have h' : e.symm q' ≠ q := fun heq => h (by rw [← e.apply_symm_apply q', heq])
    simp [h, h', relabelHashCache]

/-- A lazy random-oracle answer is invariant under a bijective renaming of its input,
with the same renaming applied to the final cache. -/
theorem hashAnswer_relabel (prims : Primitives) (e : Query C ≃ Query C) (q : Query C)
    (hfixed : ¬ IsFixed q) (hfixed' : ¬ IsFixed (e q)) (s : HashCache C) :
    (fun p : HashOutput × HashCache C => (p.1, relabelHashCache e p.2)) <$>
        (hashAnswer prims q).run s =
      (hashAnswer prims (e q)).run (relabelHashCache e s) := by
  rw [hashAnswer_of_not_isFixed prims hfixed, hashAnswer_of_not_isFixed prims hfixed',
    OracleSpec.randomOracle]
  have hs : relabelHashCache e s (e q) = s q := by change s (e.symm (e q)) = s q; rw [Equiv.symm_apply_apply]
  cases h : s q with
  | none =>
    rw [QueryImpl.withCaching_run_none _ h, QueryImpl.withCaching_run_none _ (hs.trans h)]
    simp only [Functor.map_map, relabelHashCache_query]
    rfl
  | some y =>
    rw [QueryImpl.withCaching_run_some _ h, QueryImpl.withCaching_run_some _ (hs.trans h)]
    rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem D_sharedQueries_at (prims : Primitives) (h : Query C → HashOutput)
    (phase : Phase) (i j : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    (D prims h (sharedQueries phase i keys)).getD j.val 0 =
      h (.sharedKeys phase ((sharedTerms i j).map keys.2.1)) := by
  simp only [sharedQueries, D_mapM, D_hashQuery]
  exact getD_parties _ _ j

/-- Equal honest echoes force equal parameters and all their shared seeds, outside a collision
at the two shared-key inputs. This does not require the echo sender to receive an output. -/
theorem keygen_echo_agreement (prims : Primitives) (h : Query C → HashOutput)
    (i j : C.Party)
    (ki kj : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hecho : echoOf .keygen ki (D prims h (sharedQueries .keygen i ki)) j =
      echoOf .keygen kj (D prims h (sharedQueries .keygen j kj)) i)
    (hnocollision :
      h (.sharedKeys .keygen ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys .keygen ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys (C := C) .keygen ((sharedTerms j i).map kj.2.1)) :
    ki.1 = kj.1 ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.2.1 T = kj.2.1 T := by
  simp only [echoOf, ite_true, List.singleton_append, List.cons.injEq,
    and_true, D_sharedQueries_at] at hecho
  refine ⟨hecho.1, ?_⟩
  have hqs := hnocollision hecho.2
  have hlists := (Query.sharedKeys.inj hqs).2
  rw [sharedTerms_comm j i] at hlists
  intro T hi hj
  apply List.map_eq_map_iff.mp hlists T
  simp [sharedTerms, Committee.terms, hi, hj]

/-- The accepting party's echo check compares it with every honest sender, including a sender
that aborts only after sending the echo. -/
theorem keygen_echoCheck_agreement (prims : Primitives) (h : Query C → HashOutput)
    (i j : C.Party) (hji : j ≠ i)
    (ki kj : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (received : Mail C E)
    (hsender : received j = some (.hashes (echoOf .keygen kj
      (D prims h (sharedQueries .keygen j kj)) i)))
    (hcheck : echoCheck .keygen i ki (D prims h (sharedQueries .keygen i ki)) received)
    (hnocollision :
      h (.sharedKeys .keygen ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys .keygen ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys (C := C) .keygen ((sharedTerms j i).map kj.2.1)) :
    ki.1 = kj.1 ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.2.1 T = kj.2.1 T := by
  apply keygen_echo_agreement prims h i j ki kj _ hnocollision
  have heq := hcheck j hji
  simpa only [hsender, Msg.hashesOf] using heq.symm

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- An echo to a corrupt recipient contains only terms known to the coalition. -/
theorem keygen_sharedTerms_known (D : C.Coalition) (i j : C.Party) (hj : j ∈ D.1)
    (T : C.Term) (hT : T ∈ sharedTerms i j) : KnownTo D.1 T := by
  have hm := (List.mem_filter.mp hT).2
  exact ⟨j, hj, (of_decide_eq_true hm).2⟩

/-- Changing only hidden seeds preserves every echo input sent to a corrupt recipient. -/
theorem keygen_sharedInput_known (D : C.Coalition) (i j : C.Party) (hj : j ∈ D.1)
    (s s' : C.Term → HashOutput) (hs : ∀ T, KnownTo D.1 T → s T = s' T) :
    Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map s) =
      Query.sharedKeys .keygen ((sharedTerms i j).map s') := by
  congr 1
  exact List.map_congr_left fun T hT => hs T (keygen_sharedTerms_known D i j hj T hT)

/-- On two honest endpoints, the complete seed comparison reduces to known seeds when hidden
terms are internally consistent. This allows the dealer's hidden seeds to replace emulated ones. -/
theorem keygen_sharedAgreement_iff_known (D : C.Coalition) (i j : C.Party)
    (s s' : C.Term → HashOutput)
    (hhidden : ∀ T, ¬ KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → s T = s' T) :
    (∀ T, i ∈ C.holders T → j ∈ C.holders T → s T = s' T) ↔
      (∀ T, KnownTo D.1 T → i ∈ C.holders T → j ∈ C.holders T → s T = s' T) := by
  constructor
  · exact fun h T _ => h T
  · intro h T hi hj
    by_cases hknown : KnownTo D.1 T
    · exact h T hknown hi hj
    · exact hhidden T hknown hi hj

/-- Outside a collision, equality of honest echoes is exactly equality of the full parameter
and of the seeds shared by the endpoints. -/
theorem keygen_echo_eq_iff (prims : Primitives) (h : Query C → HashOutput)
    (i j : C.Party)
    (ki kj : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hnocollision :
      h (.sharedKeys .keygen ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys .keygen ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys .keygen ((sharedTerms j i).map kj.2.1)) :
    (echoOf .keygen ki (D prims h (sharedQueries .keygen i ki)) j =
      echoOf .keygen kj (D prims h (sharedQueries .keygen j kj)) i) ↔
    (ki.1 = kj.1 ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.2.1 T = kj.2.1 T) := by
  constructor
  · exact fun heq => keygen_echo_agreement prims h i j ki kj heq hnocollision
  · rintro ⟨hp, hs⟩
    simp only [echoOf, ite_true, List.singleton_append, List.cons.injEq, and_true,
      D_sharedQueries_at, hp, true_and]
    rw [sharedTerms_comm j i]
    congr 2
    exact List.map_congr_left fun T hT => by
      have hm := of_decide_eq_true (List.mem_filter.mp hT).2
      exact hs T hm.1 hm.2

/-- Replacing coherent hidden seeds preserves the equality of two honest echoes. -/
theorem keygen_echo_eq_hidden_invariant (prims : Primitives) (coalition : C.Coalition)
    (h h' : Query C → HashOutput) (i j : C.Party)
    (ki kj ki' kj' : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hpi : ki.1 = ki'.1) (hpj : kj.1 = kj'.1)
    (hki : ∀ T, KnownTo coalition.1 T → ki.2.1 T = ki'.2.1 T)
    (hkj : ∀ T, KnownTo coalition.1 T → kj.2.1 T = kj'.2.1 T)
    (hhidden : ∀ T, ¬ KnownTo coalition.1 T → i ∈ C.holders T → j ∈ C.holders T → ki.2.1 T = kj.2.1 T)
    (hhidden' : ∀ T, ¬ KnownTo coalition.1 T → i ∈ C.holders T → j ∈ C.holders T → ki'.2.1 T = kj'.2.1 T)
    (hnocollision :
      h (.sharedKeys .keygen ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys .keygen ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys .keygen ((sharedTerms j i).map kj.2.1))
    (hnocollision' :
      h' (.sharedKeys .keygen ((sharedTerms i j).map ki'.2.1)) =
        h' (.sharedKeys .keygen ((sharedTerms j i).map kj'.2.1)) →
      Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map ki'.2.1) =
        Query.sharedKeys .keygen ((sharedTerms j i).map kj'.2.1)) :
    (echoOf .keygen ki (D prims h (sharedQueries .keygen i ki)) j =
      echoOf .keygen kj (D prims h (sharedQueries .keygen j kj)) i) ↔
    (echoOf .keygen ki' (D prims h' (sharedQueries .keygen i ki')) j =
      echoOf .keygen kj' (D prims h' (sharedQueries .keygen j kj')) i) := by
  rw [keygen_echo_eq_iff prims h i j ki kj hnocollision,
    keygen_echo_eq_iff prims h' i j ki' kj' hnocollision',
    keygen_sharedAgreement_iff_known coalition i j ki.2.1 kj.2.1 hhidden,
    keygen_sharedAgreement_iff_known coalition i j ki'.2.1 kj'.2.1 hhidden', hpi, hpj]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro T
  apply forall_congr'
  intro hT
  rw [hki T hT, hkj T hT]

/-- Every hidden term uses the honest parts, in every holder's view, even when the corrupt
operators send inconsistent openings for other terms. -/
theorem keygen_hiddenTerm_input (coalition : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .keygen (parts j) j i)
    (T : C.Term) (hhidden : ¬ KnownTo coalition.1 T) (i : C.Party) (hi : i ∈ C.holders T) :
    Query.derive (C := C) .keygen .term
      ((C.parties.filter (· ∈ C.holders T)).map fun j =>
        (setupView .keygen i (parts i) (revealed i) j).term T) =
      termInput .keygen parts T := by
  unfold termInput
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjT : j ∈ C.holders T := of_decide_eq_true (List.mem_filter.mp hj).2
  have hjhonest : j ∉ coalition.1 := fun hc => hhidden ⟨j, hc, hjT⟩
  rw [setupView_honest_sender coalition parts revealed hreceived i j hjhonest]
  exact honestView_term .keygen parts hjT hi

/-- The actual derived hidden seed is common to all its honest holders. -/
theorem keygen_hiddenTerm_derived (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .keygen (parts j) j i)
    (T : C.Term) (hhidden : ¬ KnownTo coalition.1 T) (i : C.Party) (hi : i ∈ C.holders T) :
    (D prims h (deriveKeys .keygen i (setupView .keygen i (parts i) (revealed i)))).2.1 T =
      h (termInput .keygen parts T) := by
  rw [D_deriveKeys]
  simp only [hi, if_true]
  rw [keygen_hiddenTerm_input coalition parts revealed hreceived T hhidden i hi]

/-- The echo-round inbox, including the abort frame of any honest operator that failed earlier. -/
def keygenEchoInbox (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (i : C.Party) : Mail C E := fun j =>
  if j ∈ coalition.1 then sent j i else
  if active j then echoOutbox .keygen j (keys j) (D prims h (sharedQueries .keygen j (keys j))) i
  else some .abort

/-- Changing coherent hidden seeds leaves the complete final check unchanged, including selective
abort. Honest echo collisions are the only excluded cases; corrupt messages are arbitrary. -/
theorem keygen_echoCheck_hidden_invariant (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h h' : Query C → HashOutput)
    (keys keys' : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hp : ∀ i, i ∉ coalition.1 → (keys i).1 = (keys' i).1)
    (hk : ∀ i T, i ∉ coalition.1 → KnownTo coalition.1 T → (keys i).2.1 T = (keys' i).2.1 T)
    (hh : ∀ i j T, i ∉ coalition.1 → j ∉ coalition.1 → ¬ KnownTo coalition.1 T →
      i ∈ C.holders T → j ∈ C.holders T → (keys i).2.1 T = (keys j).2.1 T)
    (hh' : ∀ i j T, i ∉ coalition.1 → j ∉ coalition.1 → ¬ KnownTo coalition.1 T →
      i ∈ C.holders T → j ∈ C.holders T → (keys' i).2.1 T = (keys' j).2.1 T)
    (hc : ∀ i j, i ∉ coalition.1 → j ∈ coalition.1 →
      h (.sharedKeys .keygen ((sharedTerms i j).map (keys i).2.1)) =
        h' (.sharedKeys .keygen ((sharedTerms i j).map (keys' i).2.1)))
    (hn : ∀ i j, i ∉ coalition.1 → j ∉ coalition.1 →
      h (.sharedKeys .keygen ((sharedTerms i j).map (keys i).2.1)) =
        h (.sharedKeys .keygen ((sharedTerms j i).map (keys j).2.1)) →
      Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map (keys i).2.1) =
        Query.sharedKeys .keygen ((sharedTerms j i).map (keys j).2.1))
    (hn' : ∀ i j, i ∉ coalition.1 → j ∉ coalition.1 →
      h' (.sharedKeys .keygen ((sharedTerms i j).map (keys' i).2.1)) =
        h' (.sharedKeys .keygen ((sharedTerms j i).map (keys' j).2.1)) →
      Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map (keys' i).2.1) =
        Query.sharedKeys .keygen ((sharedTerms j i).map (keys' j).2.1))
    (i : C.Party) (hi : i ∉ coalition.1) :
    echoCheck .keygen i (keys i) (D prims h (sharedQueries .keygen i (keys i)))
      (keygenEchoInbox prims coalition active sent h keys i) ↔
    echoCheck .keygen i (keys' i) (D prims h' (sharedQueries .keygen i (keys' i)))
      (keygenEchoInbox prims coalition active sent h' keys' i) := by
  unfold echoCheck
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hji
  by_cases hj : j ∈ coalition.1
  · simp only [keygenEchoInbox, if_pos hj]
    have he : echoOf .keygen (keys i) (D prims h (sharedQueries .keygen i (keys i))) j =
        echoOf .keygen (keys' i) (D prims h' (sharedQueries .keygen i (keys' i))) j := by
      simp only [echoOf, ite_true, List.singleton_append, List.cons.injEq, and_true,
        D_sharedQueries_at]
      exact ⟨hp i hi, hc i j hi hj⟩
    rw [he]
  · simp only [keygenEchoInbox, if_neg hj]
    by_cases ha : active j
    · simp only [if_pos ha, echoOutbox, if_neg (Ne.symm hji), Msg.hashesOf]
      apply eq_comm.trans
      apply Iff.trans _ eq_comm
      exact keygen_echo_eq_hidden_invariant prims coalition h h' i j
        (keys i) (keys j) (keys' i) (keys' j) (hp i hi) (hp j hj)
        (fun T hT => hk i T hi hT) (fun T hT => hk j T hj hT)
        (fun T hT => hh i j T hi hj hT) (fun T hT => hh' i j T hi hj hT)
        (hn i j hi hj) (hn' i j hi hj)
    · simp [ha, Msg.hashesOf, echoOf]

/-- The last local continuation of keygen makes no oracle calls. -/
theorem advance_keygenEchoResume (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (shared : List HashOutput) (received : Mail C E) :
    advance (exchangeResume (G := RealSpec) (fun inbox =>
      require (echoCheck .keygen i keys shared inbox) >>= fun _ => pure (keysOf keys)) received) =
      pure (Step.done (if (C.parties.any fun j => Msg.isAbort (received j)) then none else
        if echoCheck .keygen i keys shared received then some (keysOf keys) else none)) := by
  unfold exchangeResume
  split_ifs with ha hc
  · rfl
  · rw [advance_require_bind, if_pos hc, advance_run_pure]
  · rw [advance_require_bind, if_neg hc]

/-- Aborts in the last inbox do not depend on the keys or the oracle table. -/
theorem keygenEchoInbox_isAbort (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h h' : Query C → HashOutput)
    (keys keys' : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (i j : C.Party) :
    Msg.isAbort (keygenEchoInbox prims coalition active sent h keys i j) =
      Msg.isAbort (keygenEchoInbox prims coalition active sent h' keys' i j) := by
  unfold keygenEchoInbox
  split_ifs <;> simp only [isAbort_echoOutbox]

/-- A keygen step waiting for the echo, or the persistent abort of an earlier round. -/
def keygenEchoStep (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (i : C.Party) : Step C E RealSpec (Keys C) :=
  if i ∈ coalition.1 ∨ ¬ active i then .done none else
    .wait (echoOutbox .keygen i (keys i) (D prims h (sharedQueries .keygen i (keys i))))
      (exchangeResume fun inbox => require
        (echoCheck .keygen i (keys i) (D prims h (sharedQueries .keygen i (keys i))) inbox) >>=
        fun _ => pure (keysOf (keys i)))

/-- The concrete inbox used by `stepRound` is the echo inbox above. -/
theorem roundInbox_keygenEchoStep (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (i : C.Party) :
    roundInbox coalition sent (keygenEchoStep prims coalition active h keys) i =
      keygenEchoInbox prims coalition active sent h keys i := by
  funext j
  unfold roundInbox keygenEchoStep keygenEchoInbox
  by_cases hj : j ∈ coalition.1
  · simp only [hj, if_true]
  · simp only [hj, false_or, if_false]
    by_cases ha : active j <;> simp [ha, Step.delivered]

/-- The possible output of the final local step. -/
def keygenEchoOutput (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (i : C.Party) : Option (Keys C) :=
  if i ∈ coalition.1 ∨ ¬ active i then none else
    let inbox := keygenEchoInbox prims coalition active sent h keys i
    if C.parties.any fun j => Msg.isAbort (inbox j) then none else
      if echoCheck .keygen i (keys i) (D prims h (sharedQueries .keygen i (keys i))) inbox
      then some (keysOf (keys i)) else none

/-- One concrete echo round, with all honest local continuations reduced to pure outputs. -/
theorem stepRound_keygenEchoStep (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    stepRound worldRoles coalition A noFunctionality state (keygenEchoStep prims coalition active h keys) =
      (do
        let (state, sent) ← worldRoles.adversary (A.round state fun c i =>
          if c ∈ coalition.1 ∧ i ∉ coalition.1 then
            (keygenEchoStep prims coalition active h keys i).outbox c else none)
        pure (state, (fun i => Step.done (keygenEchoOutput prims coalition active sent h keys i)), sent)) := by
  unfold stepRound
  have hc : ¬ (∃ i, i ∉ coalition.1 ∧
      (keygenEchoStep prims coalition active h keys (E := E) i).callInput.isSome) := by
    simp only [callInput_real, Option.isSome_none, Bool.false_eq_true, and_false, exists_false, not_false_eq_true]
  rw [if_neg (fun h => hc h.1)]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only
  trans (Concrete.sequenceFin (fun i =>
    (pure (Step.done (keygenEchoOutput prims coalition active sent h keys i)) :
      OracleComp (WorldSpec C) (Step C E RealSpec (Keys C)))) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext i
    by_cases hi : i ∈ coalition.1 ∨ ¬ active i
    · simp only [keygenEchoStep, if_pos hi, keygenEchoOutput]
    · have hih : i ∉ coalition.1 := fun hh => hi (Or.inl hh)
      rw [show keygenEchoStep prims coalition active h keys (E := E) i = _ from if_neg hi]
      simp only [if_neg hih]
      change worldRoles.honest (advance (exchangeResume _
        (roundInbox coalition sent (keygenEchoStep prims coalition active h keys) i))) = _
      rw [roundInbox_keygenEchoStep, advance_keygenEchoResume]
      simp only [worldRoles, free, keygenEchoOutput, if_neg hi]
      exact simulateQ_pure _ _
  · rw [sequenceFin_pure, pure_bind]

/-- The entire last execution round, with its early-exit rule. -/
theorem executeRounds_keygenEchoStep_one (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    executeRounds worldRoles coalition A noFunctionality 1 state
      (keygenEchoStep prims coalition active h keys) =
      (if ∀ i, i ∉ coalition.1 → ¬ active i then pure (state, fun _ => none) else do
        let (state, sent) ← worldRoles.adversary (A.round state fun c i =>
          if c ∈ coalition.1 ∧ i ∉ coalition.1 then
            (keygenEchoStep prims coalition active h keys i).outbox c else none)
        pure (state, keygenEchoOutput prims coalition active sent h keys)) := by
  have hd : (∀ i, i ∉ coalition.1 →
      (keygenEchoStep prims coalition active h keys (E := E) i).isDone) ↔
      ∀ i, i ∉ coalition.1 → ¬ active i := by
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    simp only [keygenEchoStep, hi, false_or]
    by_cases ha : active i <;> simp [ha, Step.isDone]
  rw [executeRounds]
  simp only [hd]
  split_ifs with hd'
  · congr 1
    apply congrArg (fun f => (state, f))
    funext i
    have hi : i ∈ coalition.1 ∨ ¬ active i := by
      by_cases hc : i ∈ coalition.1
      · exact Or.inl hc
      · exact Or.inr (hd' i hc)
    simp only [keygenEchoStep, if_pos hi, Step.output]
  · rw [stepRound_keygenEchoStep]
    simp only [bind_assoc, pure_bind, executeRounds, Step.output]

/-- The final receiver set is unchanged whenever visible echoes and final checks are unchanged.
This is an equality of the actual `executeRounds` computations, for an arbitrary adversary. -/
theorem executeRounds_keygenEchoStep_receivers_congr (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (h h' : Query C → HashOutput)
    (keys keys' : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hvisible : ∀ i c, i ∉ coalition.1 → c ∈ coalition.1 →
      echoOf .keygen (keys i) (D prims h (sharedQueries .keygen i (keys i))) c =
        echoOf .keygen (keys' i) (D prims h' (sharedQueries .keygen i (keys' i))) c)
    (hchecks : ∀ (sent : C.Party → Mail C E) (i : C.Party) (_ : i ∉ coalition.1),
      echoCheck .keygen i (keys i) (D prims h (sharedQueries .keygen i (keys i)))
        (keygenEchoInbox prims coalition active sent h keys i) ↔
      echoCheck .keygen i (keys' i) (D prims h' (sharedQueries .keygen i (keys' i)))
        (keygenEchoInbox prims coalition active sent h' keys' i)) :
    (fun r => (r.1, fun i => (r.2 i).isSome)) <$>
      executeRounds worldRoles coalition A noFunctionality 1 state
        (keygenEchoStep prims coalition active h keys) =
    (fun r => (r.1, fun i => (r.2 i).isSome)) <$>
      executeRounds worldRoles coalition A noFunctionality 1 state
        (keygenEchoStep prims coalition active h' keys') := by
  rw [executeRounds_keygenEchoStep_one, executeRounds_keygenEchoStep_one]
  split_ifs with hd
  · rfl
  · have hmsg : (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        (keygenEchoStep prims coalition active h keys (E := E) i).outbox c else none) =
        (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        (keygenEchoStep prims coalition active h' keys' (E := E) i).outbox c else none) := by
      funext c i
      split_ifs with hci
      · unfold keygenEchoStep
        split_ifs
        · rfl
        · simp only [Step.outbox, echoOutbox]
          rw [hvisible i c hci.2 hci.1]
      · rfl
    rw [hmsg]
    simp only [map_bind, map_pure]
    refine bind_congr fun r => ?_
    apply congrArg pure
    apply congrArg (fun f => (r.1, f))
    funext i
    unfold keygenEchoOutput
    by_cases hi : i ∈ coalition.1 ∨ ¬ active i
    · simp only [if_pos hi]
    · simp only [if_neg hi]
      have hih : i ∉ coalition.1 := fun hc => hi (Or.inl hc)
      have habort : (fun j => Msg.isAbort (keygenEchoInbox prims coalition active r.2 h keys i j)) =
          (fun j => Msg.isAbort (keygenEchoInbox prims coalition active r.2 h' keys' i j)) :=
        funext fun j => keygenEchoInbox_isAbort prims coalition active r.2 h h' keys keys' i j
      simp only [habort, hchecks r.2 i hih]
      split_ifs <;> rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- A programming attempt at an already cached input leaves the cache unchanged. -/
theorem programAnswer_run_cached (q : Query C) (s : HashCache C) (y v : HashOutput)
    (hs : s q = some v) : (programAnswer (q, y)).run s = pure (false, s) := by
  simp [programAnswer, StateT.run_bind, StateT.run_get, hs, StateT.run_pure]

/-- A uniformly programmed value that is not retained. -/
def uniformProgram (q : Query C) : StateT (HashCache C) ProbComp Unit := do
  let y ← StateT.lift ($ᵗ HashOutput)
  let _ ← programAnswer (q, y)
  pure ()

/-- Even at a cached input, an unused uniform programming attempt has the same cache distribution
as an unused ordinary hash query. Freshness is needed only when the sampled value is retained. -/
theorem evalDist_uniformProgram (prims : Primitives) (q : Query C) (hq : ¬ IsFixed q)
    (s : HashCache C) :
    𝒟[(uniformProgram q).run s] =
      𝒟[(hashAnswer prims q >>= fun _ => pure ()).run s] := by
  cases hs : s q with
  | none =>
    simp only [uniformProgram, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
      programAnswer_run_fresh hq s hs, StateT.run_pure]
    rw [hashAnswer_of_not_isFixed prims hq, OracleSpec.randomOracle,
      QueryImpl.withCaching_run_none _ hs]
    rfl
  | some v =>
    simp only [uniformProgram, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
      programAnswer_run_cached q s _ v hs, StateT.run_pure,
      hashAnswer_run_cached prims hq hs]
    exact DeferredSampling.evalDist_bind_const_neverFails ($ᵗ HashOutput) (by simp) _

/-- The discarded programming swap is valid before every cache-dependent continuation. -/
theorem evalDist_uniformProgram_bind (prims : Primitives) (q : Query C) (hq : ¬ IsFixed q)
    {α : Type} (k : StateT (HashCache C) ProbComp α) (s : HashCache C) :
    𝒟[(uniformProgram q >>= fun _ => k).run s] =
      𝒟[(hashAnswer prims q >>= fun _ => k).run s] := by
  have h := evalDist_run_bind_of_eq (fun _ : Unit => k) s (evalDist_uniformProgram prims q hq s)
  simpa only [bind_assoc, pure_bind] using h

/-- A block of independent programming values. -/
def uniformPrograms : List (Query C) → StateT (HashCache C) ProbComp Unit
  | [] => pure ()
  | q :: qs => uniformProgram q >>= fun _ => uniformPrograms qs

/-- The uniform programming block is distributionally the corresponding block of discarded
ordinary queries, including the cache and every continuation. Inputs need not be distinct. -/
theorem evalDist_uniformPrograms_bind (prims : Primitives) (qs : List (Query C))
    (hq : ∀ q ∈ qs, ¬ IsFixed q) {α : Type} (k : StateT (HashCache C) ProbComp α)
    (s : HashCache C) :
    𝒟[(uniformPrograms qs >>= fun _ => k).run s] =
      𝒟[((qs.mapM (hashAnswer prims)) >>= fun _ => k).run s] := by
  induction qs generalizing s with
  | nil => simp [uniformPrograms]
  | cons q qs ih =>
    simp only [uniformPrograms, List.mapM_cons, bind_assoc, pure_bind]
    refine (evalDist_uniformProgram_bind prims q (hq q (List.mem_cons_self ..)) _ s).trans ?_
    apply evalDist_run_bind_congr
    intro _ s'
    exact ih (fun r hr => hq r (List.mem_cons_of_mem q hr)) s'

/-- The free random-oracle computations represented by a list of inputs. -/
theorem simulateQ_localAnswer_hashes (prims : Primitives) (qs : List (Query C)) :
    simulateQ (localAnswer prims) (liftComp (qs.mapM hashQuery) (LocalSpec C)) =
      qs.mapM (hashAnswer prims) := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, simulateQ_bind,
      simulateQ_pure, simulateQ_localAnswer_hash, ih]

/-- With no retained programming values, the entire block can be removed before any local
continuation. This includes arbitrary future counted adversary and distinguisher computations
once their counted/free wrappers have been erased. -/
theorem evalDist_uniformPrograms_prepend (prims : Primitives) (qs : List (Query C))
    (hq : ∀ q ∈ qs, ¬ IsFixed q) {α : Type} (k : OracleComp (LocalSpec C) α)
    (s : HashCache C) :
    𝒟[(uniformPrograms qs >>= fun _ => simulateQ (localAnswer prims) k).run' s] =
      𝒟[(simulateQ (localAnswer prims) k).run' s] := by
  have h := evalDist_uniformPrograms_bind prims qs hq (simulateQ (localAnswer prims) k) s
  have hm := congrArg (fun d : SPMF (α × HashCache C) => Prod.fst <$> d) h
  simp only [← evalDist_map, ← StateT.run'_eq] at hm
  refine hm.trans ?_
  rw [← simulateQ_localAnswer_hashes]
  rw [← simulateQ_bind]
  exact evalDist_run'_prepend prims _ k s

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity

def keygenFullParameter (high : HashOutput) (parameter : PublicParameter) : HashOutput :=
  high >>> digestBits <<< digestBits ||| parameter.setWidth hashOutputBits

theorem keygenFullParameter_getLsbD (high : HashOutput) (parameter : PublicParameter)
    (i : ℕ) (hi : i < hashOutputBits) :
    (keygenFullParameter high parameter).getLsbD i =
      if i < digestBits then parameter.getLsbD i else high.getLsbD i := by
  simp only [keygenFullParameter, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  by_cases h : i < digestBits
  · simp [h, hi]
  · have hp : parameter.getLsbD i = false := BitVec.getLsbD_of_ge parameter i (by exact Nat.le_of_not_gt h)
    simp [h, hp, hi, Nat.le_of_not_gt h]

theorem truncate_keygenFullParameter (high : HashOutput) (parameter : PublicParameter) :
    truncateHash (keygenFullParameter high parameter) = parameter := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [truncateHash, BitVec.getLsbD_extractLsb', Nat.zero_add]
  rw [keygenFullParameter_getLsbD high parameter i (by
    unfold hashOutputBits; unfold digestBits at hi; omega)]
  simp only [hi, if_pos, decide_true, Bool.true_and]
  rfl

theorem keygenFullParameter_restore (high : HashOutput) (parameter : PublicParameter) :
    keygenFullParameter (keygenFullParameter high parameter) (truncateHash high) = high := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [keygenFullParameter_getLsbD _ _ i hi]
  by_cases hl : i < digestBits
  · rw [if_pos hl]
    change (BitVec.extractLsb' 0 digestBits high).getLsbD i = high.getLsbD i
    simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hl, decide_true, Bool.true_and]
  · rw [if_neg hl, keygenFullParameter_getLsbD high parameter i hi, if_neg hl]

/-- The parameter encoding swaps the low halves of a pair of uniform samples. -/
def keygenParameterSwap (p : HashOutput × PublicParameter) : HashOutput × PublicParameter :=
  (keygenFullParameter p.1 p.2, truncateHash p.1)

theorem keygenParameterSwap_involutive : Function.Involutive keygenParameterSwap := by
  intro p
  exact Prod.ext (keygenFullParameter_restore p.1 p.2) (truncate_keygenFullParameter p.1 p.2)

theorem evalDist_keygenFullParameter_pair :
    𝒟[(fun p : HashOutput × PublicParameter => keygenFullParameter p.1 p.2) <$>
        ($ᵗ (HashOutput × PublicParameter))] = 𝒟[$ᵗ HashOutput] := by
  have h := evalDist_map_bijective_uniform_cross (HashOutput × PublicParameter)
    keygenParameterSwap keygenParameterSwap_involutive.bijective
  calc
    _ = 𝒟[Prod.fst <$> (keygenParameterSwap <$> ($ᵗ (HashOutput × PublicParameter)))] := by
      rw [Functor.map_map]; rfl
    _ = 𝒟[Prod.fst <$> ($ᵗ (HashOutput × PublicParameter))] := by
      rw [evalDist_map, h, ← evalDist_map]
    _ = _ := evalDist_map_fst_uniformSample_prod

/-- The exact full-width parameter programmed by `keygenSimulator` is uniform. -/
theorem evalDist_keygenFullParameter :
    𝒟[(do
      let parameter ← $ᵗ PublicParameter
      let high ← $ᵗ HashOutput
      pure (high >>> digestBits <<< digestBits ||| parameter.setWidth hashOutputBits) : ProbComp HashOutput)] =
      𝒟[$ᵗ HashOutput] := by
  change 𝒟[($ᵗ PublicParameter) >>= fun p => ($ᵗ HashOutput) >>= fun h => pure (keygenFullParameter h p)] = _
  rw [DeferredSampling.evalDist_bind_comm]
  have he : ((fun p : HashOutput × PublicParameter => keygenFullParameter p.1 p.2) <$>
      ($ᵗ (HashOutput × PublicParameter))) =
      (($ᵗ HashOutput) >>= fun h => ($ᵗ PublicParameter) >>= fun p => pure (keygenFullParameter h p)) := by
    change ((fun p : HashOutput × PublicParameter => keygenFullParameter p.1 p.2) <$>
      (Prod.mk <$> ($ᵗ HashOutput) <*> ($ᵗ PublicParameter))) = _
    simp only [seq_eq_bind_map, map_eq_bind_pure_comp]
    rfl
  rw [← he]
  exact evalDist_keygenFullParameter_pair

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

/-- Distinct coordinates of the dealer's uniform table may be sampled separately. -/
theorem evalDist_uniform_table_list {ι R : Type} [Finite ι] [DecidableEq ι]
    [Finite R] [Nonempty R] [SampleableType R] [SampleableType (ι → R)]
    (indices : List ι) (hnd : indices.Nodup) :
    𝒟[(fun f : ι → R => indices.map f) <$> ($ᵗ (ι → R))] =
      𝒟[indices.mapM fun _ => $ᵗ R] := by
  induction indices with
  | nil =>
    simp only [List.map_nil, List.mapM_nil, map_eq_bind_pure_comp]
    exact DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _
  | cons i indices ih =>
    have hn := List.nodup_cons.mp hnd
    have hs := evalDist_uniformSample_bind_update_map (R := R) i
      (fun f : ι → R => (i :: indices).map f)
    have hmap : ∀ (f : ι → R) (r : R), indices.map (Function.update f i r) = indices.map f := by
      intro f r
      apply List.map_congr_left
      intro j hj
      have hji : j ≠ i := fun h => hn.1 (h ▸ hj)
      simp [hji]
    simp only [List.map_cons, Function.update_self, hmap] at hs
    simp only [List.map_cons, map_eq_bind_pure_comp, Function.comp_def]
    rw [← hs]
    simp only [List.mapM_cons]
    apply DeferredSampling.evalDist_bind_congr_left
    intro r
    change 𝒟[(fun f : ι → R => r :: indices.map f) <$> ($ᵗ (ι → R))] = _
    calc
      _ = 𝒟[List.cons r <$> ((fun f : ι → R => indices.map f) <$> ($ᵗ (ι → R)))] := by
        rw [Functor.map_map]
      _ = 𝒟[List.cons r <$> (indices.mapM fun _ => $ᵗ R)] := by
        rw [evalDist_map, ih hn.2, ← evalDist_map]
      _ = _ := by simp only [map_eq_bind_pure_comp, Function.comp_def]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Interpret both network roles through the same oracle implementation. -/
def keygenMapRoles {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec)) : Roles C m :=
  ⟨fun oa => simulateQ impl (roles.adversary oa), fun oa => simulateQ impl (roles.honest oa)⟩

theorem simulateQ_stepRound_real {ι : Type} {spec : OracleSpec ι} {m : Type → Type}
    [Monad m] [LawfulMonad m] (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec))
    (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec (Keys C)) :
    simulateQ impl (stepRound roles coalition A noFunctionality state steps) =
      stepRound (keygenMapRoles impl roles) coalition A noFunctionality state steps := by
  simp only [stepRound, callInput_real, Option.isSome_none, Bool.false_eq_true, and_false,
    exists_false, false_and, if_false]
  rw [simulateQ_bind]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only
  rw [simulateQ_bind, simulateQ_sequenceFin]
  simp only [simulateQ_pure]
  congr 1
  congr 1
  funext i
  cases hs : steps i with
  | done out => simp
  | wait outbox resume =>
    by_cases hi : i ∈ coalition.1 <;> simp [hi, keygenMapRoles]
  | call input resume => exact input.elim

theorem simulateQ_executeRounds_real {ι : Type} {spec : OracleSpec ι} {m : Type → Type}
    [Monad m] [LawfulMonad m] (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec))
    (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    ∀ fuel state (steps : C.Party → Step C E RealSpec (Keys C)),
    simulateQ impl (executeRounds roles coalition A noFunctionality fuel state steps) =
      executeRounds (keygenMapRoles impl roles) coalition A noFunctionality fuel state steps
  | 0, state, steps => by simp [executeRounds]
  | fuel + 1, state, steps => by
    simp only [executeRounds]
    split_ifs
    · simp
    · rw [simulateQ_bind, simulateQ_stepRound_real]
      refine bind_congr fun r => ?_
      exact simulateQ_executeRounds_real impl roles coalition A fuel r.1 r.2.1

/-- Counted and free local computations have the same cache semantics after the counter is erased. -/
theorem keygenMapRoles_world (prims : Primitives) :
    keygenMapRoles (worldAnswer (C := C) prims) worldRoles =
      keygenMapRoles (localAnswer prims) localRoles := by
  unfold keygenMapRoles
  congr 1
  · funext β oa
    change simulateQ (worldAnswer prims) (counted (liftComp oa (SimulatorSpec C))) =
      simulateQ (localAnswer prims) oa
    rw [simulateQ_counted]
    unfold liftComp
    rw [← QueryImpl.simulateQ_compose]
    congr 1
    funext t
    rcases t with t | (q | q) <;> exact (simulateQ_query _ _).trans (id_map _)
  · funext β oa
    exact simulateQ_free _ _ oa

/-- The real network's rounds may be studied on the single shared local cache. -/
theorem simulateQ_world_executeRounds (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (steps : C.Party → Step C E RealSpec (Keys C)) :
    simulateQ (worldAnswer prims) (executeRounds worldRoles coalition A noFunctionality fuel state steps) =
      simulateQ (localAnswer prims) (executeRounds localRoles coalition A noFunctionality fuel state steps) := by
  rw [simulateQ_executeRounds_real, keygenMapRoles_world, ← simulateQ_executeRounds_real]

theorem simulateQ_startSteps_real {ι : Type} {spec : OracleSpec ι} {m : Type → Type}
    [Monad m] [LawfulMonad m] (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec))
    (coalition : C.Coalition) (program : C.Party → PartyM C E RealSpec (Keys C)) :
    simulateQ impl (startSteps roles coalition program) =
      startSteps (keygenMapRoles impl roles) coalition program := by
  unfold startSteps
  rw [simulateQ_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ coalition.1 <;> simp [hi, keygenMapRoles]

theorem simulateQ_world_adversary (prims : Primitives) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (worldAnswer prims) (worldRoles.adversary oa) = simulateQ (localAnswer prims) oa :=
  congrArg (fun roles : Roles C (StateT (HashCache C) ProbComp) => roles.adversary oa)
    (keygenMapRoles_world prims)

/-- The real keygen game after removing only the counted/free wrappers. -/
def keygenLocalGame (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    OracleComp (LocalSpec C) Bool := do
  let state ← A.start (corruptInputs coalition x) z
  let steps ← startSteps localRoles coalition fun i => (keygen i : PartyM C E RealSpec (Keys C))
  let out ← executeRounds localRoles coalition A noFunctionality setupRounds state steps
  Z out

/-- The complete real game, including the distinguisher, runs on the one shared cache. -/
theorem simulateQ_keygenReal_eq_local (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    simulateQ (worldAnswer prims)
      (distinguish (realExecution coalition A noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) Z) =
      simulateQ (localAnswer prims) (keygenLocalGame coalition A x z Z) := by
  unfold distinguish realExecution executePhase keygenLocalGame
  simp only [simulateQ_bind, simulateQ_world_adversary, simulateQ_startSteps_real,
    simulateQ_executeRounds_real, keygenMapRoles_world, bind_assoc]

/-- In particular, the local game has exactly the acceptance probability of the real game. -/
theorem keygenLocalGame_accepts (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    (Pr[= true | (simulateQ (localAnswer prims) (keygenLocalGame coalition A x z Z)).run' ∅]).toReal =
      accepts prims (distinguish (realExecution coalition A noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) Z) := by
  unfold accepts
  rw [← simulateQ_keygenReal_eq_local, ← fst_map_runWorld, probOutput_map]

/-- An unused private draw changes neither an output nor the cache. -/
theorem sameRun_private_unused (prims : Primitives) {α β : Type} (p : ProbComp α) (b : β) :
    SameRun (C := C) prims (liftComp p (LocalSpec C) >>= fun _ => pure b) (pure b) := by
  intro s
  have hl : simulateQ (localAnswer prims) (liftComp p (LocalSpec C)) =
      simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p :=
    QueryImpl.simulateQ_add_liftComp_left (unifFwdImpl (Query C →ₒ HashOutput)) _ p
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, hl,
    unifFwdImpl.simulateQ_run, bind_map_left]
  exact DeferredSampling.evalDist_bind_const_neverFails p (by simp) _

theorem SameRun.sequenceFin (prims : Primitives) {α : Type} {n : ℕ}
    (f g : Fin n → OracleComp (LocalSpec C) α) (h : ∀ i, SameRun prims (f i) (g i)) :
    SameRun prims (Concrete.sequenceFin f) (Concrete.sequenceFin g) := by
  induction n with
  | zero => exact SameRun.refl prims _
  | succ n ih =>
    simp only [Concrete.sequenceFin]
    apply (h 0).bind
    intro a
    apply (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)).bind
    intro rest
    exact SameRun.refl prims _

theorem advance_keygen_sampling (i : C.Party) :
    advance (keygen i : PartyM C E RealSpec (Keys C)).run =
      liftComp sampleParts (LocalSpec C) >>= fun parts =>
        advance (keygenWith i parts : PartyM C E RealSpec (Keys C)).run :=
  advance_localStep_bind _ _

/-- Moving all private parts before the first commitments is valid for any coalition. The unused
parts of corrupt operators can be sampled too, as the explicit simulator does. -/
theorem sameRun_startSteps_keygen_parts (prims : Primitives) (coalition : C.Coalition) :
    SameRun prims
      (startSteps localRoles coalition fun i => (keygen i : PartyM C E RealSpec (Keys C)))
      (do
        let parts ← Concrete.sequenceFin fun (_ : C.Party) => liftComp (sampleParts (C := C)) (LocalSpec C)
        startSteps localRoles coalition fun i => (keygenWith i (parts i) : PartyM C E RealSpec (Keys C))) := by
  let draws : C.Party → OracleComp (LocalSpec C) (Parts C) := fun _ => liftComp sampleParts (LocalSpec C)
  let next : C.Party → Parts C → OracleComp (LocalSpec C) (Step C E RealSpec (Keys C)) := fun i parts =>
    if i ∈ coalition.1 then pure (.done none) else advance (keygenWith i parts : PartyM C E RealSpec (Keys C)).run
  have hlocal : ∀ i, SameRun prims
      (if i ∈ coalition.1 then pure (.done none) else advance (keygen i : PartyM C E RealSpec (Keys C)).run)
      (draws i >>= next i) := by
    intro i
    by_cases hi : i ∈ coalition.1
    · simpa only [draws, next, if_pos hi] using
        (sameRun_private_unused prims (sampleParts (C := C)) (Step.done (C := C) (E := E) (G := RealSpec) (none : Option (Keys C)))).symm
    · simp only [draws, next, if_neg hi, advance_keygen_sampling]
      exact SameRun.refl prims _
  have hseq := SameRun.sequenceFin prims _ _ hlocal
  change SameRun prims (Concrete.sequenceFin _) _
  refine hseq.trans ?_
  have hmove := sameRun_sequenceFin_dep prims draws next (fun _ _ step => step)
  simp only [bind_pure] at hmove
  change SameRun prims (Concrete.sequenceFin fun i => draws i >>= next i)
    (Concrete.sequenceFin draws >>= fun parts =>
      (Concrete.sequenceFin fun i => next i (parts i)) >>= pure) at hmove
  simpa only [bind_pure, draws, next, startSteps, localRoles] using hmove

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The commitment computation of the honest operators, with an empty entry for each corrupt one. -/
def keygenInitialCommitments (coalition : C.Coalition) (parts : C.Party → Parts C) :
    OracleComp (LocalSpec C) (C.Party → List HashOutput) :=
  Concrete.sequenceFin fun i => if i ∈ coalition.1 then pure [] else
    liftComp (commitQueries .keygen i (parts i)) (LocalSpec C)

def keygenInitialSteps (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) : C.Party → Step C E RealSpec (Keys C) := fun i =>
  if i ∈ coalition.1 then .done none else keygenStart i (parts i) (commitments i)

theorem advance_keygenWith (i : C.Party) (parts : Parts C) :
    advance (keygenWith i parts : PartyM C E RealSpec (Keys C)).run =
      liftComp (commitQueries .keygen i parts) (LocalSpec C) >>= fun commitments =>
        pure (keygenStart i parts commitments) := by
  change advance (commitRevealEcho .keygen i parts >>= fun keys => pure (keysOf keys)).run = _
  rw [advance_setup_start]
  rfl

/-- The initial network state consists of waiting commit senders and corrupt dummy steps. -/
theorem startSteps_keygenWith (coalition : C.Coalition) (parts : C.Party → Parts C) :
    startSteps localRoles coalition (fun i => (keygenWith i (parts i) : PartyM C E RealSpec (Keys C))) =
      keygenInitialSteps coalition parts <$> keygenInitialCommitments coalition parts := by
  unfold startSteps keygenInitialCommitments
  have hl : (fun i => if i ∈ coalition.1 then pure (Step.done none) else
      localRoles.honest (advance (keygenWith i (parts i) : PartyM C E RealSpec (Keys C)).run)) =
      (fun i => (if i ∈ coalition.1 then pure [] else
        liftComp (commitQueries .keygen i (parts i)) (LocalSpec C)) >>= fun commits =>
        pure (if i ∈ coalition.1 then Step.done none else keygenStart i (parts i) commits)) := by
    funext i
    by_cases hi : i ∈ coalition.1 <;> simp [hi, localRoles, advance_keygenWith]
  rw [hl]
  rw [sequenceFin_bind_pure]
  rw [map_eq_bind_pure_comp]
  rfl

/-- Every allowed coalition has an honest operator. -/
theorem keygen_exists_honest (coalition : C.Coalition) : ∃ i : C.Party, i ∉ coalition.1 := by
  by_contra hn
  push Not at hn
  have heq : coalition.1 = Finset.univ := Finset.ext fun i => by simp [hn i]
  have hc := coalition.2
  rw [heq, Finset.card_univ, Fintype.card_fin] at hc
  have ht := C.one_le_t
  unfold Committee.n at hc
  omega

/-- At the commit boundary the early-exit condition is false, so the real run takes exactly one
commit round before the remaining two rounds. -/
theorem executeRounds_keygenInitialSteps (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) :
    executeRounds localRoles coalition A noFunctionality setupRounds state
      (keygenInitialSteps coalition parts commitments) =
    (do
      let (state, steps, _) ← stepRound localRoles coalition A noFunctionality state
        (keygenInitialSteps coalition parts commitments)
      executeRounds localRoles coalition A noFunctionality (setupRounds - 1) state steps) := by
  change executeRounds localRoles coalition A noFunctionality (2 + 1) state _ = _
  rw [executeRounds, if_neg]
  · rfl
  · intro hd
    obtain ⟨i, hi⟩ := keygen_exists_honest coalition
    have hh := hd i hi
    simpa only [keygenInitialSteps, if_neg hi, keygenStart, Step.isDone] using hh

/-- The real prefix through the commit round, retaining its private parts and corrupt messages. -/
def keygenLocalCommitPrefix (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    OracleComp (LocalSpec C)
      ((C.Party → Parts C) × A.State × (C.Party → Step C E RealSpec (Keys C)) × (C.Party → Mail C E)) := do
  let state ← A.start (corruptInputs coalition x) z
  let parts ← Concrete.sequenceFin fun (_ : C.Party) => liftComp (sampleParts (C := C)) (LocalSpec C)
  let commitments ← keygenInitialCommitments coalition parts
  let (state, steps, sent) ← stepRound localRoles coalition A noFunctionality state
    (keygenInitialSteps coalition parts commitments)
  pure (parts, state, steps, sent)

/-- The continuation after the commit round includes the final distinguisher. -/
def keygenLocalPostCommit (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C))
    (r : (C.Party → Parts C) × A.State × (C.Party → Step C E RealSpec (Keys C)) × (C.Party → Mail C E)) :
    OracleComp (LocalSpec C) Bool := do
  let out ← executeRounds localRoles coalition A noFunctionality (setupRounds - 1) r.2.1 r.2.2.1
  Z out

/-- The complete real game split at the simulator's programming boundary. -/
theorem sameRun_keygenLocal_split (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    SameRun prims (keygenLocalGame coalition A x z Z)
      (keygenLocalCommitPrefix coalition A x z >>= keygenLocalPostCommit coalition A Z) := by
  unfold keygenLocalGame keygenLocalCommitPrefix keygenLocalPostCommit
  simp only [bind_assoc, pure_bind]
  apply SameRun.bind_right
  intro state
  refine ((sameRun_startSteps_keygen_parts prims coalition).bind fun steps =>
    SameRun.refl prims (executeRounds localRoles coalition A noFunctionality setupRounds state steps >>= Z)).trans ?_
  simp only [bind_assoc]
  apply SameRun.bind_right
  intro parts
  rw [startSteps_keygenWith, bind_map_left]
  apply SameRun.bind_right
  intro commitments
  rw [executeRounds_keygenInitialSteps]
  simp only [bind_assoc]
  exact SameRun.refl prims _

/-- Insert independent unused programming at the commit boundary. Its inputs may depend on all
prefix data, including the private parts and the corrupt commit messages. -/
def keygenProgrammedReal (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C))
    (inputs : ((C.Party → Parts C) × A.State × (C.Party → Step C E RealSpec (Keys C)) ×
      (C.Party → Mail C E)) → List (Query C)) : ProbComp Bool := do
  let (r, cache) ← (simulateQ (localAnswer prims) (keygenLocalCommitPrefix coalition A x z)).run ∅
  (uniformPrograms (inputs r) >>= fun _ =>
    simulateQ (localAnswer prims) (keygenLocalPostCommit coalition A Z r)).run' cache

/-- The programming block can be removed from this complete game, without freshness or
collision assumptions. This is the real marginal needed by the coupling route. -/
theorem evalDist_keygenProgrammedReal (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C))
    (inputs : ((C.Party → Parts C) × A.State × (C.Party → Step C E RealSpec (Keys C)) ×
      (C.Party → Mail C E)) → List (Query C))
    (hinputs : ∀ r q, q ∈ inputs r → ¬ IsFixed q) :
    𝒟[keygenProgrammedReal prims coalition A x z Z inputs] =
      𝒟[(simulateQ (localAnswer prims)
        (keygenLocalCommitPrefix coalition A x z >>= keygenLocalPostCommit coalition A Z)).run' ∅] := by
  unfold keygenProgrammedReal
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  apply DeferredSampling.evalDist_bind_congr_left
  rintro ⟨r, cache⟩
  exact evalDist_uniformPrograms_prepend prims (inputs r) (hinputs r)
    (keygenLocalPostCommit coalition A Z r) cache

/-- The programmed real game has exactly the original real acceptance probability. -/
theorem keygenProgrammedReal_accepts (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C))
    (inputs : ((C.Party → Parts C) × A.State × (C.Party → Step C E RealSpec (Keys C)) ×
      (C.Party → Mail C E)) → List (Query C))
    (hinputs : ∀ r q, q ∈ inputs r → ¬ IsFixed q) :
    (Pr[= true | keygenProgrammedReal prims coalition A x z Z inputs]).toReal =
      accepts prims (distinguish (realExecution coalition A noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) Z) := by
  have heq := (evalDist_keygenProgrammedReal prims coalition A x z Z inputs hinputs).trans
    (sameRun_keygenLocal_split prims coalition A x z Z).run'_eq.symm
  exact (congrArg ENNReal.toReal (probOutput_congr rfl heq)).trans
    (keygenLocalGame_accepts prims coalition A x z Z)

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem simulateQ_stateT_free_sampling {σ L R α : Type}
    (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ (OracleComp (WorldSpec C))))
    (himpl : ∀ (t : (LocalSpec C).Domain) st,
      (impl (.inl t)).run st = (fun a => (a, st)) <$> free (OracleComp.lift (OracleSpec.query t)))
    (p : ProbComp α) (st : σ) :
    (simulateQ impl (liftComp p (LocalSpec C + (L →ₒ R)))).run st =
      (fun a => (a, st)) <$> free (liftComp p (LocalSpec C)) := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, simulateQ_bind, StateT.run_bind]
    have hq : simulateQ impl (liftComp (liftM (OracleSpec.query t) : ProbComp _)
        (LocalSpec C + (L →ₒ R))) = impl (.inl (.inl t)) := by
      rw [liftComp_query]
      exact (simulateQ_query _ _).trans (id_map _)
    rw [hq]
    erw [himpl (.inl t) st]
    simp only [bind_map_left, ih, liftComp_bind, free_bind, map_bind]
    rfl

theorem idealExecution_Fkeygen (D : C.Coalition)
    (S : Simulator (C := C) (WorldSpec C) Unit
      (PublicParameter × (C.Party → Option (Keys C))) (Finset C.Party) σ)
    (x : C.Party → Unit) (z : Aux) :
    idealExecution (fun oa => oa) D Fkeygen S x z = (do
      let st ← S.start (corruptInputs D x) z
      let (parameter, _, keys) ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
      let (st, receivers) ← S.answer st (parameter, fun i => if i ∈ D.1 then some (keys i) else none)
      let out ← S.output st
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ receivers then some (keys i) else none)) := by
  unfold idealExecution Fkeygen
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc]
  apply bind_congr
  intro st
  rw [simulateQ_stateT_free_sampling _ (by intros; rfl)]
  simp only [bind_map_left]
  apply bind_congr
  rintro ⟨parameter, seeds, keys⟩
  have hleak {σ' L R : Type}
      (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ' (OracleComp (WorldSpec C))))
      (l : L) : simulateQ impl (leak (C := C) (R := R) l) = impl (.inr l) := by
    unfold leak
    exact (simulateQ_query _ _).trans (id_map _)
  rw [hleak]
  simp only [simulateQ_pure, StateT.run_pure, pure_bind]
  change ((S.answer st (parameter, fun i => if i ∈ D.1 then some (keys i) else none) >>=
    fun p => pure (p.2, p.1)) >>= fun p => S.output p.2 >>= fun out =>
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ p.1 then some (keys i) else none)) = _
  simp only [bind_assoc, pure_bind]

def keygenProgramView (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) (i j : C.Party) : Parts C :=
  if j ∈ D.1 then readReveal .keygen (extractReveal log sent j i) i j else parts j

def keygenFirstHonest (D : C.Coalition) (S : Finset C.Party) : C.Party :=
  (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)

/-- The simulator's complete programming block, including failed attempts. -/
def keygenProgramBlock (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) (parameter : PublicParameter)
    (corrupt : C.Party → Option (Keys C)) (high : HashOutput) : OracleComp (WorldSpec C) Unit := do
  let view := keygenProgramView D parts log sent
  let _ ← program (.derive .keygen .parameter
    (C.parties.map fun j => (view (keygenFirstHonest D Finset.univ) j).parameter))
    (keygenFullParameter high parameter)
  let _ ← C.terms.mapM fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
    | some j =>
      let i := keygenFirstHonest D (C.holders T)
      program (.derive .keygen .term
        ((C.parties.filter (· ∈ C.holders T)).map fun k => (view i k).term T))
        (((corrupt j).map (·.seed T)).getD 0)
    | none => pure true
  let _ ← C.parties.mapM fun j => C.parties.mapM fun i =>
    if h : j ∈ D.1 ∧ i ∉ D.1 then
      let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
      program (.derive .keygen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1])
        (((corrupt j).map (·.pairKey i)).getD 0)
    else pure true
  pure ()

/-- The actual simulator with its emulated key values retained. -/
def keygenEmulation (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (st : SimulatorState C Unit A.State) (parameter : PublicParameter)
    (corrupt : C.Party → Option (Keys C)) :
    OracleComp (WorldSpec C) (SimulatorState C Unit A.State × (C.Party → Option (Keys C))) := do
  let parts ← free (liftComp (Concrete.sequenceFin fun (_ : C.Party) =>
    (sampleParts : ProbComp (Parts C))) _)
  let steps ← startSteps worldRoles D fun i => (keygenWith i (parts i) : PartyM C E RealSpec (Keys C))
  let ((state, steps, sent), calls) ← (stepRound observedRoles D A noFunctionality st.adversary steps).run
  let log := st.log ++ calls
  let high ← free (liftComp ($ᵗ HashOutput) _)
  keygenProgramBlock D parts log sent parameter corrupt high
  let ((state, keys), rest) ← (executeRounds observedRoles D A noFunctionality
    (setupRounds - 1) state steps).run
  pure (⟨state, log ++ rest, st.corrupt⟩, keys)

theorem keygenSimulator_answer_emulation (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (st : SimulatorState C Unit A.State)
    (parameter : PublicParameter) (corrupt : C.Party → Option (Keys C)) :
    (keygenSimulator D A).answer st (parameter, corrupt) =
      (fun r => (r.1, Finset.univ.filter fun i => (r.2 i).isSome)) <$>
        keygenEmulation D A st parameter corrupt := by
  simp only [keygenSimulator, keygenEmulation, keygenProgramBlock, keygenProgramView,
    keygenFirstHonest, keygenFullParameter, map_bind, map_pure, bind_assoc, pure_bind]
  rfl

/-- One common game retains both the emulated outputs and the dealer's keys. -/
def keygenCommonGame (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    OracleComp (WorldSpec C) (A.State × (C.Party → Option (Keys C)) × (C.Party → Keys C)) := do
  let st ← (keygenSimulator D A).start (corruptInputs D x) z
  let (parameter, _, keys) ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
  let (st, emulated) ← keygenEmulation D A st parameter fun i =>
    if i ∈ D.1 then some (keys i) else none
  pure (st.adversary, emulated, keys)

def keygenIdealProjection (D : C.Coalition)
    (r : σ × (C.Party → Option (Keys C)) × (C.Party → Keys C)) :
    σ × (C.Party → Option (Keys C)) :=
  (r.1, fun i => if i ∉ D.1 ∧ (r.2.1 i).isSome then some (r.2.2 i) else none)

/-- The ideal marginal is exactly the specified functionality and simulator, for every run. -/
theorem keygenCommonGame_ideal (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    keygenIdealProjection D <$> keygenCommonGame D A x z =
      idealExecution (fun oa => oa) D Fkeygen (keygenSimulator D A) x z := by
  rw [idealExecution_Fkeygen]
  unfold keygenCommonGame
  simp only [map_bind, map_pure, keygenSimulator_answer_emulation, bind_map_left]
  apply bind_congr
  intro st
  apply bind_congr
  rintro ⟨parameter, seeds, keys⟩
  erw [bind_map_left]
  apply bind_congr
  rintro ⟨st, emulated⟩
  change pure (keygenIdealProjection D (st.adversary, emulated, keys)) =
    (pure st.adversary >>= fun out => pure (out, fun i =>
      if i ∉ D.1 ∧ i ∈ Finset.univ.filter (fun i => (emulated i).isSome)
      then some (keys i) else none))
  simp only [pure_bind, keygenIdealProjection, Finset.mem_filter, Finset.mem_univ, true_and]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Equality of unordered pairs preserves their endpoints, up to swapping. -/
theorem pairOf_eq_endpoints (i j i' j' : C.Party) (hij : i ≠ j) (hij' : i' ≠ j')
    (h : C.pairOf i j hij = C.pairOf i' j' hij') :
    (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') := by
  have hv := congrArg Subtype.val h
  unfold Committee.pairOf at hv
  split_ifs at hv <;> simp only [Prod.mk.injEq] at hv
  · exact Or.inl hv
  · exact Or.inr hv
  · exact Or.inr ⟨hv.2, hv.1⟩
  · exact Or.inl ⟨hv.2, hv.1⟩

/-- A corrupt--honest pair has only one orientation in the simulator's nested loop. -/
theorem pairOf_cross_injective (D : C.Coalition) (i j i' j' : C.Party)
    (hj : j ∈ D.1) (hi : i ∉ D.1) (hj' : j' ∈ D.1) (hi' : i' ∉ D.1)
    (h : C.pairOf i j (fun e => hi (e ▸ hj)) =
      C.pairOf i' j' (fun e => hi' (e ▸ hj'))) : i = i' ∧ j = j' := by
  rcases pairOf_eq_endpoints i j i' j' _ _ h with he | he
  · exact he
  · exact (hi (he.1 ▸ hj')).elim

/-- The corrupt--honest ordered pairs, in exactly the order of the simulator's loops. -/
def keygenCrossList (D : C.Coalition) : List (C.Party × C.Party) :=
  (C.parties.product C.parties).filter fun p => p.1 ∈ D.1 ∧ p.2 ∉ D.1

theorem keygenCrossList_mem (D : C.Coalition) (p : C.Party × C.Party) :
    p ∈ keygenCrossList D ↔ p.1 ∈ D.1 ∧ p.2 ∉ D.1 := by
  rcases p with ⟨j, i⟩
  simp [keygenCrossList, Committee.parties, List.mem_product, List.mem_finRange]

def keygenCrossPair (D : C.Coalition) (p : {p // p ∈ keygenCrossList D}) : C.Pair :=
  C.pairOf p.1.2 p.1.1 (fun e => (keygenCrossList_mem D p.1).mp p.2 |>.2
    (e ▸ ((keygenCrossList_mem D p.1).mp p.2).1))

theorem keygenCrossPair_injective (D : C.Coalition) : Function.Injective (keygenCrossPair D) := by
  intro p q h
  apply Subtype.ext
  have hp := (keygenCrossList_mem D p.1).mp p.2
  have hq := (keygenCrossList_mem D q.1).mp q.2
  have he := pairOf_cross_injective D p.1.2 p.1.1 q.1.2 q.1.1 hp.1 hp.2 hq.1 hq.2 h
  exact Prod.ext he.2 he.1

def keygenCrossCoordinates (D : C.Coalition) : List C.Pair :=
  (keygenCrossList D).attach.map (keygenCrossPair D)

theorem keygenCrossCoordinates_nodup (D : C.Coalition) : (keygenCrossCoordinates D).Nodup := by
  apply List.Nodup.map (keygenCrossPair_injective D)
  apply List.Nodup.attach
  apply List.Nodup.filter
  exact List.Nodup.product (List.nodup_finRange _) (List.nodup_finRange _)

def keygenKnownCoordinates (D : C.Coalition) : List C.Term :=
  C.terms.filter fun T => KnownTo D.1 T

theorem keygenKnownCoordinates_nodup (D : C.Coalition) : (keygenKnownCoordinates D).Nodup := by
  apply List.Nodup.filter
  exact Finset.nodup_toList _

theorem keygenDealer_known_value (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (T : C.Term) (j : C.Party)
    (hj : j ∈ D.1) (hT : j ∈ C.holders T) :
    (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.seed T)).getD 0) = seeds T := by
  simp [hj, dealtKeys, hT]

theorem keygenDealer_cross_value (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (i j : C.Party)
    (h : j ∈ D.1 ∧ i ∉ D.1) :
    (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.pairKey i)).getD 0) =
      pairs (C.pairOf i j (fun e => h.2 (e ▸ h.1))) := by
  have hij : i ≠ j := fun e => h.2 (e ▸ h.1)
  simp only [if_pos h.1, Option.map_some, Option.getD_some, dealtKeys, dif_neg hij]
  congr 1
  unfold Committee.pairOf
  split_ifs with hji hijlt hijlt
  · exact (not_lt_of_ge (le_of_lt hji) hijlt).elim
  · rfl
  · rfl
  · exact (hij (le_antisymm (not_lt.mp hji) (not_lt.mp hijlt))).elim

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- The cache after a programming attempt, whether or not it succeeds. -/
def programCache (q : Query C) (y : HashOutput) (s : HashCache C) : HashCache C :=
  if IsFixed q ∨ (s q).isSome then s else s.cacheQuery q y

theorem programAnswer_run_cache (q : Query C) (y : HashOutput) (s : HashCache C) :
    (programAnswer (q, y)).run s =
      pure (!(decide (IsFixed q ∨ (s q).isSome)), programCache q y s) := by
  unfold programAnswer programCache IsFixed
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  split_ifs <;> simp_all

def programValues : List (Query C) → List HashOutput → StateT (HashCache C) ProbComp Unit
  | q :: qs, y :: ys => programAnswer (q, y) >>= fun _ => programValues qs ys
  | _, _ => pure ()

theorem programValues_run_cons (q : Query C) (qs : List (Query C))
    (y : HashOutput) (ys : List HashOutput) (s : HashCache C) :
    (programValues (q :: qs) (y :: ys)).run s =
      (programValues qs ys).run (programCache q y s) := by
  simp only [programValues, StateT.run_bind, programAnswer_run_cache, pure_bind]

theorem sample_programValues_run (qs : List (Query C)) (s : HashCache C) :
    (qs.mapM (fun _ => ($ᵗ HashOutput : ProbComp HashOutput)) >>= fun ys =>
      (programValues qs ys).run s) = (uniformPrograms qs).run s := by
  induction qs generalizing s with
  | nil => simp [programValues, uniformPrograms]
  | cons q qs ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind, programValues_run_cons,
      uniformPrograms, StateT.run_bind, uniformProgram, StateT.run_lift,
      programAnswer_run_cache]
    apply bind_congr
    intro y
    exact ih _

/-- Sampling the dealer coordinates used by a block gives exactly independent programming values.
No condition is placed on the target inputs: they may repeat or already be cached. -/
theorem evalDist_table_programValues {ι : Type} [Finite ι] [DecidableEq ι]
    [SampleableType (ι → HashOutput)] (indices : List ι) (hnd : indices.Nodup)
    (inputs : ι → Query C) (s : HashCache C) :
    𝒟[do let table ← $ᵗ (ι → HashOutput)
         (programValues (indices.map inputs) (indices.map table)).run s] =
      𝒟[(uniformPrograms (indices.map inputs)).run s] := by
  have h := evalDist_uniform_table_list (R := HashOutput) indices hnd
  calc
    _ = 𝒟[((fun table : ι → HashOutput => indices.map table) <$> ($ᵗ (ι → HashOutput))) >>=
      fun ys => (programValues (indices.map inputs) ys).run s] := by rw [bind_map_left]
    _ = 𝒟[(indices.mapM fun _ => $ᵗ HashOutput) >>= fun ys =>
      (programValues (indices.map inputs) ys).run s] := by rw [evalDist_bind, h, ← evalDist_bind]
    _ = _ := by
      have hm : (indices.map inputs).mapM (fun _ => ($ᵗ HashOutput : ProbComp HashOutput)) =
          indices.mapM (fun _ => ($ᵗ HashOutput : ProbComp HashOutput)) := by
        rw [List.mapM_map]; rfl
      rw [← hm, sample_programValues_run]

def tablePrograms {ι : Type} [SampleableType (ι → HashOutput)] (indices : List ι)
    (inputs : ι → Query C) : StateT (HashCache C) ProbComp Unit := do
  let table ← StateT.lift ($ᵗ (ι → HashOutput))
  programValues (indices.map inputs) (indices.map table)

theorem evalDist_tablePrograms {ι : Type} [Finite ι] [DecidableEq ι]
    [SampleableType (ι → HashOutput)] (indices : List ι) (hnd : indices.Nodup)
    (inputs : ι → Query C) (s : HashCache C) :
    𝒟[(tablePrograms indices inputs).run s] =
      𝒟[(uniformPrograms (indices.map inputs)).run s] := by
  simp only [tablePrograms, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  exact evalDist_table_programValues indices hnd inputs s

/-- The full dealer-table programming block disappears before any local continuation, including
its future adversary and distinguisher queries. -/
theorem evalDist_tablePrograms_prepend (prims : Primitives) {ι : Type} [Finite ι] [DecidableEq ι]
    [SampleableType (ι → HashOutput)] (indices : List ι) (hnd : indices.Nodup)
    (inputs : ι → Query C) (hinputs : ∀ i ∈ indices, ¬ IsFixed (inputs i))
    {α : Type} (k : OracleComp (LocalSpec C) α) (s : HashCache C) :
    𝒟[(tablePrograms indices inputs >>= fun _ => simulateQ (localAnswer prims) k).run' s] =
      𝒟[(simulateQ (localAnswer prims) k).run' s] := by
  have he := evalDist_run_bind_of_eq (fun _ : Unit => simulateQ (localAnswer prims) k)
    s (evalDist_tablePrograms indices hnd inputs s)
  have hm := congrArg (fun d : SPMF (α × HashCache C) => Prod.fst <$> d) he
  simp only [StateT.run'_eq, evalDist_map]
  rw [hm]
  simpa only [StateT.run'_eq, evalDist_map] using
    evalDist_uniformPrograms_prepend prims (indices.map inputs)
    (by
      intro q hq
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hq
      exact hinputs i hi) k s

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

def keygenEraseLog {α : Type} (p : WriterT (CallLog C) (OracleComp (WorldSpec C)) α) :
    OracleComp (WorldSpec C) α := Prod.fst <$> p.run

theorem keygenEraseLog_pure {α : Type} (a : α) : keygenEraseLog (C := C) (pure a) = pure a := by
  simp [keygenEraseLog]

theorem keygenEraseLog_bind {α β : Type}
    (p : WriterT (CallLog C) (OracleComp (WorldSpec C)) α)
    (k : α → WriterT (CallLog C) (OracleComp (WorldSpec C)) β) :
    keygenEraseLog (p >>= k) = keygenEraseLog p >>= fun a => keygenEraseLog (k a) := by
  simp [keygenEraseLog, WriterT.run_bind, map_bind, Functor.map_map, bind_map_left]

theorem keygenEraseLog_lift {α : Type} (p : OracleComp (WorldSpec C) α) :
    keygenEraseLog (liftM p) = p := by
  simp [keygenEraseLog, WriterT.run_liftM, Functor.map_map]

theorem keygenEraseLog_sequenceFin {α : Type} : ∀ {n : ℕ}
    (p : Fin n → WriterT (CallLog C) (OracleComp (WorldSpec C)) α),
    keygenEraseLog (Concrete.sequenceFin p) = Concrete.sequenceFin fun i => keygenEraseLog (p i)
  | 0, p => by simp [Concrete.sequenceFin, keygenEraseLog_pure]
  | n + 1, p => by
    simp only [Concrete.sequenceFin, keygenEraseLog_bind, keygenEraseLog_pure,
      keygenEraseLog_sequenceFin]

theorem fst_observe {α : Type} (p : OracleComp (LocalSpec C) α) :
    Prod.fst <$> observe p = worldRoles.adversary p := by
  change keygenEraseLog (simulateQ _ p) = _
  induction p using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure, keygenEraseLog_pure, worldRoles_adversary_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, keygenEraseLog_bind, ih]
    rw [show worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
      worldRoles.adversary (liftM (OracleSpec.query t)) >>= fun a => worldRoles.adversary (k a) by
        change counted (liftComp (liftM (OracleSpec.query t) >>= k) (SimulatorSpec C)) = _
        rw [liftComp_bind, counted_bind]
        rfl]
    congr 1
    rcases t with t | (q | x)
    · simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      exact keygenEraseLog_lift _
    · simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      simp only [keygenEraseLog_bind, keygenEraseLog_lift, keygenEraseLog_pure]
      simp [keygenEraseLog, WriterT.run_tell, map_pure]
      rfl
    · simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      exact keygenEraseLog_lift _

theorem keygenEraseLog_adversary {α : Type} (p : OracleComp (LocalSpec C) α) :
    keygenEraseLog (observedRoles.adversary p) = worldRoles.adversary p := fst_observe p

theorem keygenEraseLog_honest {α : Type} (p : OracleComp (LocalSpec C) α) :
    keygenEraseLog (observedRoles.honest p) = worldRoles.honest p := keygenEraseLog_lift _

theorem keygenEraseLog_stepRound (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec (Keys C)) :
    keygenEraseLog (stepRound observedRoles D A noFunctionality state steps) =
      stepRound worldRoles D A noFunctionality state steps := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real]), if_neg (by simp [callInput_real])]
  simp only [keygenEraseLog_bind, keygenEraseLog_adversary, keygenEraseLog_pure,
    keygenEraseLog_sequenceFin]
  apply bind_congr
  intro r
  congr 1
  congr 1
  funext j
  cases hs : steps j with
  | done out => exact keygenEraseLog_pure _
  | wait outbox resume =>
    by_cases hj : j ∈ D.1
    · simp [hj, keygenEraseLog_pure]
    · simp [hj, keygenEraseLog_honest]
  | call input resume => exact input.elim

theorem keygenEraseLog_executeRounds (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    ∀ fuel state (steps : C.Party → Step C E RealSpec (Keys C)),
      keygenEraseLog (executeRounds observedRoles D A noFunctionality fuel state steps) =
        executeRounds worldRoles D A noFunctionality fuel state steps
  | 0, state, steps => by simp [executeRounds, keygenEraseLog_pure]
  | fuel + 1, state, steps => by
    simp only [executeRounds]
    split_ifs
    · exact keygenEraseLog_pure _
    · simp only [keygenEraseLog_bind, keygenEraseLog_stepRound, keygenEraseLog_executeRounds]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem discard_mapM_filter {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (xs : List α) (p : α → Bool) (f : α → m β) (b : β)
    (h : ∀ x ∈ xs, p x = false → f x = pure b) :
    (xs.mapM f >>= fun _ => pure ()) = ((xs.filter p).mapM f >>= fun _ => pure ()) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    cases hp : p x with
    | false =>
      rw [h x (List.mem_cons_self ..) hp]
      simp only [pure_bind, List.filter_cons, hp, Bool.false_eq_true, ↓reduceIte]
      exact ih (fun a ha => h a (List.mem_cons_of_mem x ha))
    | true =>
      simp only [List.filter_cons, hp, ↓reduceIte, List.mapM_cons, bind_assoc, pure_bind]
      apply bind_congr
      intro _
      exact ih (fun a ha => h a (List.mem_cons_of_mem x ha))

theorem discard_mapM_product {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β γ : Type} (xs : List α) (ys : List β) (f : α → β → m γ) :
    (xs.mapM (fun x => ys.mapM (f x)) >>= fun _ => pure ()) =
      ((xs.product ys).mapM (fun p => f p.1 p.2) >>= fun _ => pure ()) := by
  induction xs with
  | nil => simp [List.product]
  | cons x xs ih =>
    rw [show (x :: xs).product ys = ys.map (fun y => (x, y)) ++ xs.product ys from rfl]
    simp only [ List.mapM_append, List.mapM_map,
      List.mapM_cons, bind_assoc, pure_bind, Function.comp_def]
    apply bind_congr
    intro _
    exact ih

theorem keygen_mapM_congr {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (xs : List α) (f g : α → m β) (h : ∀ x ∈ xs, f x = g x) :
    xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.mapM_cons, h x (List.mem_cons_self ..),
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

def keygenTermProgrammingInput (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (T : C.Term) : Query C :=
  .derive .keygen .term ((C.parties.filter (· ∈ C.holders T)).map fun k =>
    (view (keygenFirstHonest D (C.holders T)) k).term T)

def keygenPairProgrammingInput (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (p : C.Pair) : Query C :=
  let i := if p.1.1 ∈ D.1 then p.1.2 else p.1.1
  .derive .keygen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1]

theorem keygenPairProgrammingInput_cross (D : C.Coalition)
    (view : C.Party → C.Party → Parts C) (i j : C.Party) (h : j ∈ D.1 ∧ i ∉ D.1) :
    keygenPairProgrammingInput D view (C.pairOf i j (fun e => h.2 (e ▸ h.1))) =
      .derive .keygen .pair
        [(view i (C.pairOf i j (fun e => h.2 (e ▸ h.1))).1.1).pair
            (C.pairOf i j (fun e => h.2 (e ▸ h.1))).1.2,
          (view i (C.pairOf i j (fun e => h.2 (e ▸ h.1))).1.2).pair
            (C.pairOf i j (fun e => h.2 (e ▸ h.1))).1.1] := by
  unfold keygenPairProgrammingInput Committee.pairOf
  split_ifs <;> simp_all

theorem keygenKnown_find (D : C.Coalition) (T : C.Term) :
    (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T).isSome ↔ KnownTo D.1 T := by
  simp [List.find?_isSome, Committee.parties, List.mem_finRange, KnownTo]

theorem keygenProgramTerms_dealt (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) :
    (C.terms.mapM (fun T => match C.parties.find? (fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
      | some j => program (keygenTermProgrammingInput D view T)
          (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.seed T)).getD 0)
      | none => pure true) >>= fun _ => pure ()) =
    ((keygenKnownCoordinates D).mapM (fun T =>
      program (keygenTermProgrammingInput D view T) (seeds T)) >>= fun _ => pure ()) := by
  have he : (fun T => match C.parties.find? (fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
      | some j => program (keygenTermProgrammingInput D view T)
          (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.seed T)).getD 0)
      | none => pure true) = (fun T => if KnownTo D.1 T then
        program (keygenTermProgrammingInput D view T) (seeds T) else pure true) := by
    funext T
    cases hf : C.parties.find? (fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
    | none =>
      have hn : ¬ KnownTo D.1 T := by rw [← keygenKnown_find, hf]; simp
      simp [hn]
    | some j =>
      have hj : j ∈ D.1 ∧ j ∈ C.holders T := by
        simpa only [decide_eq_true_eq] using List.find?_some hf
      simp only [if_pos (show KnownTo D.1 T from ⟨j, hj⟩),
        keygenDealer_known_value D parameter seeds pairs T j hj.1 hj.2]
  rw [he, discard_mapM_filter C.terms (fun T => decide (KnownTo D.1 T)) _ true
    (by intro T _ h; simp_all)]
  congr 1
  apply keygen_mapM_congr
  intro T hT
  exact if_pos (by simpa only [List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hT).2)

theorem keygenProgramPairs_coordinates (D : C.Coalition)
    (view : C.Party → C.Party → Parts C) (pairs : C.Pair → HashOutput) :
    (C.parties.mapM (fun j => C.parties.mapM (fun i =>
      if h : j ∈ D.1 ∧ i ∉ D.1 then
        program (keygenPairProgrammingInput D view (C.pairOf i j (fun e => h.2 (e ▸ h.1))))
          (pairs (C.pairOf i j (fun e => h.2 (e ▸ h.1))))
      else pure true)) >>= fun _ => pure ()) =
    ((keygenCrossCoordinates D).mapM (fun p =>
      program (keygenPairProgrammingInput D view p) (pairs p)) >>= fun _ => pure ()) := by
  rw [discard_mapM_product]
  let f : C.Party × C.Party → OracleComp (WorldSpec C) Bool := fun p =>
    if h : p.1 ∈ D.1 ∧ p.2 ∉ D.1 then
      program (keygenPairProgrammingInput D view (C.pairOf p.2 p.1 (fun e => h.2 (e ▸ h.1))))
        (pairs (C.pairOf p.2 p.1 (fun e => h.2 (e ▸ h.1))))
    else pure true
  change ((C.parties.product C.parties).mapM f >>= fun _ => pure ()) = _
  rw [discard_mapM_filter _ (fun p => decide (p.1 ∈ D.1 ∧ p.2 ∉ D.1)) f true
    (by intro p _ h; simp_all [f])]
  unfold keygenCrossCoordinates
  rw [List.mapM_map]
  have hm : ((keygenCrossList D).attach.mapM (fun p =>
        program (keygenPairProgrammingInput D view (keygenCrossPair D p))
          (pairs (keygenCrossPair D p)))) = (keygenCrossList D).mapM f := by
    rw [List.mapM_subtype (g := f) (by
      intro p hp
      have hd := (keygenCrossList_mem D p).mp hp
      simp only [f, dif_pos hd, keygenCrossPair])]
    simp
  change ((keygenCrossList D).mapM f >>= fun _ => pure ()) = _
  simpa only [Function.comp_def] using congrArg (fun p : OracleComp (WorldSpec C) (List Bool) => p >>= fun _ => pure ()) hm.symm

/-- The full actual programming block on a dealer leak is a parameter attempt, followed by
one attempt per known term and one per corrupt--honest pair. -/
theorem keygenProgramBlock_dealt (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (high : HashOutput) :
    keygenProgramBlock D parts log sent parameter
      (fun j => if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none) high = (do
      let view := keygenProgramView D parts log sent
      let _ ← program (.derive .keygen .parameter
        (C.parties.map fun j => (view (keygenFirstHonest D Finset.univ) j).parameter))
        (keygenFullParameter high parameter)
      let _ ← (keygenKnownCoordinates D).mapM fun T =>
        program (keygenTermProgrammingInput D view T) (seeds T)
      let _ ← (keygenCrossCoordinates D).mapM fun p =>
        program (keygenPairProgrammingInput D view p) (pairs p)
      pure ()) := by
  unfold keygenProgramBlock
  apply bind_congr
  intro _
  let view := keygenProgramView D parts log sent
  have hp := keygenProgramPairs_coordinates D view pairs
  have hpair : (C.parties.mapM (fun j => C.parties.mapM (fun i =>
      if h : j ∈ D.1 ∧ i ∉ D.1 then
        let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
        program (.derive .keygen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1])
          (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.pairKey i)).getD 0)
      else pure true)) >>= fun _ => pure ()) =
      ((keygenCrossCoordinates D).mapM (fun p =>
        program (keygenPairProgrammingInput D view p) (pairs p)) >>= fun _ => pure ()) := by
    rw [← hp]
    congr 1
    apply keygen_mapM_congr
    intro j _
    apply keygen_mapM_congr
    intro i _
    by_cases h : j ∈ D.1 ∧ i ∉ D.1
    · simp only [dif_pos h, keygenDealer_cross_value D parameter seeds pairs i j h,
        keygenPairProgrammingInput_cross D view i j h]
    · simp only [dif_neg h]
  change (_ >>= fun _ => _ ) = (_ >>= fun _ => _)
  conv_lhs => arg 2; ext; rw [hpair]
  have ht := keygenProgramTerms_dealt D view parameter seeds pairs
  have he := congrArg (fun p : OracleComp (WorldSpec C) Unit => p >>= fun _ =>
    (keygenCrossCoordinates D).mapM (fun p => program (keygenPairProgrammingInput D view p) (pairs p))
      >>= fun _ => pure ()) ht
  simp only [bind_assoc, pure_bind] at he
  convert he using 1 <;> rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Private sampling commutes with any independent computation on the oracle cache. -/
theorem commutes_private_stateT {σ α β : Type} (p : ProbComp α) (m : StateT σ ProbComp β) :
    Commutes (StateT.lift p) m := by
  intro s
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  exact DeferredSampling.evalDist_bind_comm _ _ _

theorem simulateQ_world_program (prims : Primitives) (q : Query C) (y : HashOutput) :
    simulateQ (worldAnswer prims) (program q y) = programAnswer (q, y) := by
  unfold program
  rw [simulateQ_counted]
  exact (simulateQ_query _ _).trans (id_map _)

theorem simulateQ_programValues (prims : Primitives) {ι : Type}
    (indices : List ι) (inputs : ι → Query C) (values : ι → HashOutput) :
    simulateQ (worldAnswer prims)
      (indices.mapM (fun i => program (inputs i) (values i)) >>= fun _ => pure ()) =
      programValues (indices.map inputs) (indices.map values) := by
  induction indices with
  | nil => simp [programValues, simulateQ_pure]
  | cons i indices ih =>
    simp only [List.mapM_cons, List.map_cons, bind_assoc, pure_bind, simulateQ_bind,
      simulateQ_world_program, programValues, ih]

/-- The simulator's high/low parameter encoding is a uniform programming value, with its cache. -/
theorem evalDist_parameterProgramming (q : Query C) (s : HashCache C) :
    𝒟[((do
      let parameter ← StateT.lift ($ᵗ PublicParameter)
      let high ← StateT.lift ($ᵗ HashOutput)
      let _ ← programAnswer (q, keygenFullParameter high parameter)
      pure () : StateT (HashCache C) ProbComp Unit)).run s] =
      𝒟[(uniformProgram q).run s] := by
  let p : ProbComp HashOutput := do
    let parameter ← $ᵗ PublicParameter
    let high ← $ᵗ HashOutput
    pure (keygenFullParameter high parameter)
  have hp : 𝒟[p] = 𝒟[$ᵗ HashOutput] := evalDist_keygenFullParameter
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
    uniformProgram, StateT.run_pure]
  change 𝒟[(p >>= fun y => (programAnswer (q, y)).run s >>= fun r => pure ((), r.2))] = _
  rw [evalDist_bind, hp, ← evalDist_bind]

/-- The actual independent dealer samples followed by the simulator's programming block. -/
def keygenDealerPrograms (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E) :
    StateT (HashCache C) ProbComp Unit := do
  let parameter ← StateT.lift ($ᵗ PublicParameter)
  let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
  let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
  let high ← StateT.lift ($ᵗ HashOutput)
  simulateQ (worldAnswer prims) (keygenProgramBlock D parts log sent parameter
    (fun j => if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none) high)

def keygenParameterProgrammingInput (D : C.Coalition) (view : C.Party → C.Party → Parts C) : Query C :=
  .derive .keygen .parameter (C.parties.map fun j => (view (keygenFirstHonest D Finset.univ) j).parameter)

def parameterProgram (q : Query C) (parameter : PublicParameter) : StateT (HashCache C) ProbComp Unit := do
  let high ← StateT.lift ($ᵗ HashOutput)
  let _ ← programAnswer (q, keygenFullParameter high parameter)
  pure ()

theorem keygenDealerPrograms_expand (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E) :
    keygenDealerPrograms prims D parts log sent = (do
      let parameter ← StateT.lift ($ᵗ PublicParameter)
      let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
      let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
      let view := keygenProgramView D parts log sent
      parameterProgram (keygenParameterProgrammingInput D view) parameter
      programValues ((keygenKnownCoordinates D).map (keygenTermProgrammingInput D view))
        ((keygenKnownCoordinates D).map seeds)
      programValues ((keygenCrossCoordinates D).map (keygenPairProgrammingInput D view))
        ((keygenCrossCoordinates D).map pairs)) := by
  unfold keygenDealerPrograms
  simp only [keygenProgramBlock_dealt]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro seeds
  apply bind_congr
  intro pairs
  simp only [parameterProgram, keygenParameterProgrammingInput, bind_assoc, pure_bind,
    simulateQ_bind, simulateQ_world_program, simulateQ_pure]
  apply bind_congr
  intro high
  apply bind_congr
  intro _
  rw [← simulateQ_programValues prims (keygenKnownCoordinates D),
    ← simulateQ_programValues prims (keygenCrossCoordinates D)]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]

/-- The dealer tables can be delayed until their own programming blocks. -/
theorem evalDist_keygenDealerPrograms_reorder (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E) (s : HashCache C) :
    𝒟[(keygenDealerPrograms prims D parts log sent).run s] =
    𝒟[((do
      let parameter ← StateT.lift ($ᵗ PublicParameter)
      let view := keygenProgramView D parts log sent
      parameterProgram (keygenParameterProgrammingInput D view) parameter
      tablePrograms (keygenKnownCoordinates D) (keygenTermProgrammingInput D view)
      tablePrograms (keygenCrossCoordinates D) (keygenPairProgrammingInput D view)
      : StateT (HashCache C) ProbComp Unit)).run s] := by
  rw [keygenDealerPrograms_expand]
  apply evalDist_run_bind_congr
  intro parameter s'
  let view := keygenProgramView D parts log sent
  let pp := parameterProgram (keygenParameterProgrammingInput D view) parameter
  let kt := (keygenKnownCoordinates D).map (keygenTermProgrammingInput D view)
  let kp := (keygenCrossCoordinates D).map (keygenPairProgrammingInput D view)
  let ts (seeds : C.Term → HashOutput) := programValues kt ((keygenKnownCoordinates D).map seeds)
  let ps (pairs : C.Pair → HashOutput) := programValues kp ((keygenCrossCoordinates D).map pairs)
  change 𝒟[((do
    let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
    let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
    pp
    ts seeds
    ps pairs) : StateT (HashCache C) ProbComp Unit).run s'] = _
  trans 𝒟[((do
    let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
    pp
    ts seeds
    let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
    ps pairs) : StateT (HashCache C) ProbComp Unit).run s']
  · apply evalDist_run_bind_congr
    intro seeds s''
    simpa only [bind_assoc] using
      (commutes_private_stateT ($ᵗ (C.Pair → HashOutput)) (pp >>= fun _ => ts seeds)).bind
        (fun pairs _ => ps pairs) s''
  · simpa only [tablePrograms, bind_assoc, pp, ts, ps, kt, kp, view] using
      (commutes_private_stateT ($ᵗ (C.Term → HashOutput)) pp).bind
        (fun seeds _ => ts seeds >>= fun _ => StateT.lift ($ᵗ (C.Pair → HashOutput)) >>= ps) s'

theorem uniformPrograms_append (xs ys : List (Query C)) :
    uniformPrograms (xs ++ ys) = (uniformPrograms xs >>= fun _ => uniformPrograms ys) := by
  induction xs with
  | nil => simp [uniformPrograms]
  | cons x xs ih => simp [uniformPrograms, ih, bind_assoc]

def keygenProgrammingInputs (D : C.Coalition) (view : C.Party → C.Party → Parts C) : List (Query C) :=
  keygenParameterProgrammingInput D view ::
    (keygenKnownCoordinates D).map (keygenTermProgrammingInput D view) ++
    (keygenCrossCoordinates D).map (keygenPairProgrammingInput D view)

theorem keygenProgrammingInputs_not_fixed (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (q : Query C) (hq : q ∈ keygenProgrammingInputs D view) : ¬ IsFixed q := by
  simp only [keygenProgrammingInputs, List.mem_cons, List.mem_append, List.mem_map] at hq
  rcases hq with (rfl | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩ <;>
    simp [IsFixed, keygenParameterProgrammingInput, keygenTermProgrammingInput, keygenPairProgrammingInput]

/-- After forgetting the dealer values, the exact simulator block has the cache distribution
of independent uniform programming at its actual inputs. -/
theorem evalDist_keygenDealerPrograms (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E) (s : HashCache C) :
    𝒟[(keygenDealerPrograms prims D parts log sent).run s] =
      𝒟[(uniformPrograms (keygenProgrammingInputs D (keygenProgramView D parts log sent))).run s] := by
  rw [evalDist_keygenDealerPrograms_reorder]
  let view := keygenProgramView D parts log sent
  let kt := (keygenKnownCoordinates D).map (keygenTermProgrammingInput D view)
  let kp := (keygenCrossCoordinates D).map (keygenPairProgrammingInput D view)
  trans 𝒟[((do
    let parameter ← StateT.lift ($ᵗ PublicParameter)
    parameterProgram (keygenParameterProgrammingInput D view) parameter
    uniformPrograms kt
    uniformPrograms kp) : StateT (HashCache C) ProbComp Unit).run s]
  · apply evalDist_run_bind_congr
    intro parameter s'
    apply evalDist_run_bind_congr
    intro _ s''
    refine (evalDist_run_bind_of_eq
      (fun _ : Unit => tablePrograms (keygenCrossCoordinates D) (keygenPairProgrammingInput D view)) s''
      (evalDist_tablePrograms (keygenKnownCoordinates D) (keygenKnownCoordinates_nodup D)
        (keygenTermProgrammingInput D view) s'')).trans ?_
    apply evalDist_run_bind_congr
    intro _ s'''
    exact evalDist_tablePrograms (keygenCrossCoordinates D) (keygenCrossCoordinates_nodup D)
      (keygenPairProgrammingInput D view) s'''
  · have he := evalDist_run_bind_of_eq
      (fun _ : Unit => uniformPrograms kt >>= fun _ => uniformPrograms kp) s
      (evalDist_parameterProgramming (keygenParameterProgrammingInput D view) s)
    simpa only [parameterProgram, keygenProgrammingInputs, uniformPrograms, uniformPrograms_append,
      bind_assoc, pure_bind, view, kt, kp] using he

/-- Exact erasure of the specified simulator's dealer programming, before any local continuation.
It is valid for every cache and extracted view, including failed extraction or programming. -/
theorem evalDist_keygenDealerPrograms_prepend (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E)
    {α : Type} (k : OracleComp (LocalSpec C) α) (s : HashCache C) :
    𝒟[(keygenDealerPrograms prims D parts log sent >>= fun _ =>
      simulateQ (localAnswer prims) k).run' s] =
      𝒟[(simulateQ (localAnswer prims) k).run' s] := by
  have he := evalDist_run_bind_of_eq (fun _ : Unit => simulateQ (localAnswer prims) k) s
    (evalDist_keygenDealerPrograms prims D parts log sent s)
  have hm := congrArg (fun d : SPMF (α × HashCache C) => Prod.fst <$> d) he
  simp only [StateT.run'_eq, evalDist_map]
  rw [hm]
  simpa only [StateT.run'_eq, evalDist_map] using evalDist_uniformPrograms_prepend prims
    (keygenProgrammingInputs D (keygenProgramView D parts log sent))
    (keygenProgrammingInputs_not_fixed D _) k s

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem simulateQ_world_sample (prims : Primitives) {α : Type} (p : ProbComp α) :
    simulateQ (worldAnswer prims) (free (C := C) (liftComp p (LocalSpec C))) = StateT.lift p := by
  rw [simulateQ_free]
  change simulateQ (unifFwdImpl (Query C →ₒ HashOutput) + _) (liftComp p (LocalSpec C)) = _
  rw [QueryImpl.simulateQ_add_liftComp_left]
  funext s
  change (simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p).run s =
    p >>= fun a => pure (a, s)
  rw [unifFwdImpl.simulateQ_run]
  rfl

/-- The unobserved real execution with all private parts sampled before the commits. -/
def keygenPartsWorldGame (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    OracleComp (WorldSpec C) Bool := do
  let state ← worldRoles.adversary (A.start (corruptInputs D x) z)
  let parts ← free (liftComp (Concrete.sequenceFin fun (_ : C.Party) =>
    (sampleParts : ProbComp (Parts C))) (LocalSpec C))
  let steps ← startSteps worldRoles D fun i => (keygenWith i (parts i) : PartyM C E RealSpec (Keys C))
  let (state, steps, _) ← stepRound worldRoles D A noFunctionality state steps
  let out ← executeRounds worldRoles D A noFunctionality (setupRounds - 1) state steps
  worldRoles.adversary (Z out)

theorem simulateQ_keygenPartsWorldGame (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    simulateQ (worldAnswer prims) (keygenPartsWorldGame D A x z Z) =
      simulateQ (localAnswer prims)
        (keygenLocalCommitPrefix D A x z >>= keygenLocalPostCommit D A Z) := by
  unfold keygenPartsWorldGame keygenLocalCommitPrefix keygenLocalPostCommit
  simp only [simulateQ_bind, bind_assoc, pure_bind, simulateQ_world_adversary,
    simulateQ_world_executeRounds]
  apply bind_congr
  intro state
  rw [simulateQ_free, liftComp_sequenceFin]
  apply bind_congr
  intro parts
  rw [simulateQ_startSteps_real, keygenMapRoles_world, ← simulateQ_startSteps_real,
    startSteps_keygenWith, simulateQ_map, bind_map_left]
  apply bind_congr
  intro commitments
  rw [simulateQ_stepRound_real, keygenMapRoles_world, ← simulateQ_stepRound_real]

/-- The parts-first game has exactly the real acceptance probability. -/
theorem keygenPartsWorldGame_accepts (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    accepts prims (keygenPartsWorldGame D A x z Z) =
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) Z) := by
  have hp : accepts prims (keygenPartsWorldGame D A x z Z) =
      (Pr[= true | (simulateQ (worldAnswer prims) (keygenPartsWorldGame D A x z Z)).run' ∅]).toReal := by
    rw [← fst_map_runWorld]
    unfold accepts
    rw [probOutput_map]
  rw [hp, simulateQ_keygenPartsWorldGame]
  have he := (sameRun_keygenLocal_split prims D A x z Z).run'_eq
  rw [probOutput_congr rfl he.symm]
  exact keygenLocalGame_accepts prims D A x z Z

abbrev KeygenObservedCommitData (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :=
  (C.Party → Parts C) × A.State × (C.Party → Step C E RealSpec (Keys C)) × (C.Party → Mail C E) × CallLog C

def keygenObservedCommit (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) :
    OracleComp (WorldSpec C) (KeygenObservedCommitData D A) := do
  let parts ← free (liftComp (Concrete.sequenceFin fun (_ : C.Party) =>
    (sampleParts : ProbComp (Parts C))) _)
  let steps ← startSteps worldRoles D fun i => (keygenWith i (parts i) : PartyM C E RealSpec (Keys C))
  let (r, calls) ← (stepRound observedRoles D A noFunctionality state steps).run
  pure (parts, r.1, r.2.1, r.2.2, calls)

def keygenObservedPost (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C)) (state : A.State)
    (steps : C.Party → Step C E RealSpec (Keys C)) : OracleComp (WorldSpec C) Bool := do
  let (out, _) ← (executeRounds observedRoles D A noFunctionality (setupRounds - 1) state steps).run
  worldRoles.adversary (Z out)

theorem keygenObservedPost_eq (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C)) (state : A.State)
    (steps : C.Party → Step C E RealSpec (Keys C)) :
    keygenObservedPost D A Z state steps = (do
      let out ← executeRounds worldRoles D A noFunctionality (setupRounds - 1) state steps
      worldRoles.adversary (Z out)) := by
  unfold keygenObservedPost
  rw [← keygenEraseLog_executeRounds D A (setupRounds - 1) state steps]
  simp only [keygenEraseLog, bind_map_left]

theorem simulateQ_keygenObservedPost (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (Z : Distinguisher C A.State (Keys C))
    (state : A.State) (steps : C.Party → Step C E RealSpec (Keys C)) :
    simulateQ (worldAnswer prims) (keygenObservedPost D A Z state steps) =
      simulateQ (localAnswer prims) (do
        let out ← executeRounds localRoles D A noFunctionality (setupRounds - 1) state steps
        Z out) := by
  rw [keygenObservedPost_eq]
  simp only [simulateQ_bind, simulateQ_world_executeRounds, simulateQ_world_adversary]

def keygenObservedPartsGame (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    OracleComp (WorldSpec C) Bool := do
  let (state, _) ← observe (A.start (corruptInputs D x) z)
  let r ← keygenObservedCommit D A state
  keygenObservedPost D A Z r.2.1 r.2.2.1

theorem keygenObservedPartsGame_eq (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    keygenObservedPartsGame D A x z Z = keygenPartsWorldGame D A x z Z := by
  unfold keygenObservedPartsGame keygenPartsWorldGame keygenObservedCommit
  simp only [bind_assoc, pure_bind, keygenObservedPost_eq]
  rw [← fst_observe (A.start (corruptInputs D x) z), bind_map_left]
  apply bind_congr
  intro st
  apply bind_congr
  intro parts
  apply bind_congr
  intro steps
  rw [← keygenEraseLog_stepRound D A st.1 steps]
  simp only [keygenEraseLog, bind_map_left]

def keygenDealerSamples : ProbComp (PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput)) := do
  let parameter ← $ᵗ PublicParameter
  let seeds ← $ᵗ (C.Term → HashOutput)
  let pairs ← $ᵗ (C.Pair → HashOutput)
  pure (parameter, seeds, pairs)

def keygenEmulatedProjection (r : σ × (C.Party → Option (Keys C)) × (C.Party → Keys C)) := (r.1, r.2.1)

def keygenCommonEmulatedGame (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) : OracleComp (WorldSpec C) Bool :=
  distinguish (keygenEmulatedProjection <$> keygenCommonGame D A x z) Z

/-- Exact normal form of the common game's emulated-output marginal. -/
theorem keygenCommonEmulatedGame_expand (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    keygenCommonEmulatedGame D A x z Z = (do
      let (state, log) ← observe (A.start (corruptInputs D x) z)
      let (parameter, seeds, pairs) ← free (liftComp (keygenDealerSamples (C := C)) (LocalSpec C))
      let r ← keygenObservedCommit D A state
      let high ← free (liftComp ($ᵗ HashOutput) (LocalSpec C))
      keygenProgramBlock D r.1 (log ++ r.2.2.2.2) r.2.2.2.1 parameter
        (fun j => if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none) high
      keygenObservedPost D A Z r.2.1 r.2.2.1) := by
  unfold keygenCommonEmulatedGame distinguish keygenCommonGame keygenEmulation
    keygenObservedCommit keygenObservedPost keygenDealerSamples prawnsKeyGen
  simp only [map_bind, map_pure, bind_map_left, bind_assoc, pure_bind,
    liftComp_bind, liftComp_pure, free_bind, free_pure, keygenEmulatedProjection]
  simp only [keygenSimulator, bind_assoc, pure_bind]

/-- Congruence for output distributions under an arbitrary cache-state prefix. -/
theorem evalDist_stateT_run'_bind_congr {σ α β : Type} (p : StateT σ ProbComp α)
    (f g : α → StateT σ ProbComp β)
    (h : ∀ a s, 𝒟[(f a).run' s] = 𝒟[(g a).run' s]) (s : σ) :
    𝒟[(p >>= f).run' s] = 𝒟[(p >>= g).run' s] := by
  simp only [StateT.run'_eq, StateT.run_bind, map_bind]
  apply DeferredSampling.evalDist_bind_congr_left
  intro r
  exact h r.1 r.2

/-- The common game's emulated-output marginal is exactly the real game, including the final
oracle-aided distinguisher. This statement does not require a good-event assumption. -/
theorem evalDist_keygenCommonEmulatedGame (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (s : HashCache C) :
    𝒟[(simulateQ (worldAnswer prims) (keygenCommonEmulatedGame D A x z Z)).run' s] =
      𝒟[(simulateQ (worldAnswer prims) (keygenPartsWorldGame D A x z Z)).run' s] := by
  rw [keygenCommonEmulatedGame_expand, ← keygenObservedPartsGame_eq]
  unfold keygenObservedPartsGame
  simp only [simulateQ_bind, simulateQ_world_sample]
  apply evalDist_stateT_run'_bind_congr
  rintro ⟨state, log⟩ s₁
  let stageRun := simulateQ (worldAnswer prims) (keygenObservedCommit D A state)
  let afterProgram := fun (dealer : PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput))
      (r : KeygenObservedCommitData D A) => (do
    let high ← StateT.lift ($ᵗ HashOutput)
    simulateQ (worldAnswer prims) (keygenProgramBlock D r.1 (log ++ r.2.2.2.2) r.2.2.2.1 dealer.1
      (fun j => if j ∈ D.1 then some (dealtKeys dealer.1 dealer.2.1 dealer.2.2 j) else none) high)
    simulateQ (worldAnswer prims) (keygenObservedPost D A Z r.2.1 r.2.2.1))
  have hs := (commutes_private_stateT (keygenDealerSamples (C := C)) stageRun).bind afterProgram s₁
  have hs' := congrArg (fun d : SPMF (Bool × HashCache C) => Prod.fst <$> d) hs
  rw [← evalDist_map, ← StateT.run'_eq, ← evalDist_map, ← StateT.run'_eq] at hs'
  refine hs'.trans ?_
  apply evalDist_stateT_run'_bind_congr
  intro r s₂
  dsimp only [afterProgram]
  simp only [simulateQ_keygenObservedPost]
  simpa only [keygenDealerPrograms, keygenDealerSamples, StateT.run'_eq, StateT.run_bind,
    StateT.run_lift, bind_assoc, pure_bind, map_bind] using
    evalDist_keygenDealerPrograms_prepend prims D r.1 (log ++ r.2.2.2.2) r.2.2.2.1
      (do
        let out ← executeRounds localRoles D A noFunctionality (setupRounds - 1) r.2.1 r.2.2.1
        Z out) s₂

/-- Exact real acceptance of the common game's emulated-output projection. -/
theorem keygenCommonGame_real_accepts (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    accepts prims (keygenCommonEmulatedGame D A x z Z) =
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) Z) := by
  rw [← keygenPartsWorldGame_accepts prims D A x z Z]
  have he := congrArg (fun d : SPMF Bool => (d true).toReal)
    (evalDist_keygenCommonEmulatedGame prims D A x z Z ∅)
  simpa only [← probOutput_def, ← fst_map_runWorld, probOutput_map, accepts] using he

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem keygenFirstHonest_spec (coalition : C.Coalition) (S : Finset C.Party)
    (hex : ∃ i ∈ S, i ∉ coalition.1) : keygenFirstHonest coalition S ∈ S ∧ keygenFirstHonest coalition S ∉ coalition.1 := by
  have hs : (C.parties.find? fun i => i ∈ S ∧ i ∉ coalition.1).isSome := by
    simpa only [List.find?_isSome, Committee.parties, List.mem_finRange, true_and, decide_eq_true_eq] using hex
  unfold keygenFirstHonest
  cases hf : C.parties.find? (fun i => i ∈ S ∧ i ∉ coalition.1) with
  | none => rw [hf] at hs; contradiction
  | some i =>
    simpa only [Option.getD_some, decide_eq_true_eq] using List.find?_some hf

theorem keygen_honest_holder (coalition : C.Coalition) (T : C.Term) : ∃ i ∈ C.holders T, i ∉ coalition.1 := by
  by_contra hn
  have hs : C.holders T ⊆ coalition.1 := by
    intro i hi
    by_contra hd
    exact hn ⟨i, hi, hd⟩
  have hc := Finset.card_le_card hs
  rw [keygen_card_holders] at hc
  have hd := coalition.2
  have ht := C.one_le_t
  omega

theorem keygenFirstHonest_univ (coalition : C.Coalition) : keygenFirstHonest coalition Finset.univ ∉ coalition.1 :=
  (keygenFirstHonest_spec coalition Finset.univ (by
    obtain ⟨i, hi⟩ := keygen_exists_honest coalition
    exact ⟨i, Finset.mem_univ _, hi⟩)).2

theorem keygenFirstHonest_holder (coalition : C.Coalition) (T : C.Term) :
    keygenFirstHonest coalition (C.holders T) ∈ C.holders T ∧
      keygenFirstHonest coalition (C.holders T) ∉ coalition.1 :=
  keygenFirstHonest_spec coalition _ (keygen_honest_holder coalition T)

/-- When extraction matches the actual corrupt openings, all fields used in an honest derivation
match the simulator's extracted view. The unused fields need not match. -/
theorem keygen_derived_programView (prims : Primitives) (coalition : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E)
    (revealed : C.Party → Mail C E) (i : C.Party) (hi : i ∉ coalition.1)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .keygen (parts j) j i)
    (hextract : ∀ j, j ∈ coalition.1 → extractReveal log sent j i = Msg.hashesOf (revealed i j))
    (h : Query C → HashOutput) :
    D prims h (deriveKeys .keygen i (setupView .keygen i (parts i) (revealed i))) =
      D prims h (deriveKeys .keygen i (keygenProgramView coalition parts log sent i)) := by
  have corrupt (j : C.Party) (hj : j ∈ coalition.1) :
      setupView .keygen i (parts i) (revealed i) j = keygenProgramView coalition parts log sent i j := by
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simp only [setupView, if_neg hji, keygenProgramView, if_pos hj, hextract j hj]
  have parameter (j : C.Party) :
      (setupView .keygen i (parts i) (revealed i) j).parameter =
        (keygenProgramView coalition parts log sent i j).parameter := by
    by_cases hj : j ∈ coalition.1
    · rw [corrupt j hj]
    · rw [setupView_honest_sender coalition parts revealed hreceived i j hj, honestView_parameter]
      simp [keygenProgramView, hj]
  have term (T : C.Term) (hiT : i ∈ C.holders T) (j : C.Party) (hjT : j ∈ C.holders T) :
      (setupView .keygen i (parts i) (revealed i) j).term T =
        (keygenProgramView coalition parts log sent i j).term T := by
    by_cases hj : j ∈ coalition.1
    · rw [corrupt j hj]
    · rw [setupView_honest_sender coalition parts revealed hreceived i j hj,
        honestView_term .keygen parts hjT hiT]
      simp [keygenProgramView, hj]
  have pair (a b : C.Party) (hab : a = i ∨ b = i) :
      (setupView .keygen i (parts i) (revealed i) a).pair b =
        (keygenProgramView coalition parts log sent i a).pair b := by
    by_cases ha : a ∈ coalition.1
    · rw [corrupt a ha]
    · rw [setupView_honest_sender coalition parts revealed hreceived i a ha,
        honestView_pair .keygen parts hab]
      simp [keygenProgramView, ha]
  rw [D_deriveKeys, D_deriveKeys]
  simp only [ite_true]
  apply Prod.ext
  · apply congrArg h
    apply congrArg (Query.derive .keygen .parameter)
    apply List.map_congr_left
    intro j _
    exact parameter j
  · apply Prod.ext
    · funext T
      by_cases hiT : i ∈ C.holders T
      · simp only [if_pos hiT]
        apply congrArg h
        apply congrArg (Query.derive .keygen .term)
        apply List.map_congr_left
        intro j hj
        exact term T hiT j (by simpa using (List.mem_filter.mp hj).2)
      · simp [hiT]
    · funext j
      by_cases hji : j = i
      · simp [hji]
      · simp only [dif_neg hji]
        have hp := pairOf_left_or_right i j (Ne.symm hji)
        apply congrArg h
        apply congrArg (Query.derive .keygen .pair)
        exact congrArg₂ List.cons (pair _ _ hp)
          (congrArg (fun y => [y]) (pair _ _ hp.symm))

theorem keygenCrossCoordinates_cross_mem (coalition : C.Coalition) (i j : C.Party)
    (hj : j ∈ coalition.1) (hi : i ∉ coalition.1) :
    C.pairOf i j (fun e => hi (e ▸ hj)) ∈ keygenCrossCoordinates coalition := by
  apply List.mem_map.mpr
  have hm : (j, i) ∈ keygenCrossList coalition := (keygenCrossList_mem coalition (j, i)).mpr ⟨hj, hi⟩
  exact ⟨⟨(j, i), hm⟩, List.mem_attach _ _, rfl⟩

/-- Successful programming plus the accepting party's honest echo agreements fixes every
parameter, known term and corrupt--honest pair key to the dealer's value. -/
theorem keygen_known_outputs_of_programmed (prims : Primitives) (coalition : C.Coalition)
    (view : C.Party → C.Party → Parts C) (h : Query C → HashOutput)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (high : HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hderive : ∀ j, j ∉ coalition.1 → keys j = D prims h (deriveKeys .keygen j (view j)))
    (hparameter : h (keygenParameterProgrammingInput coalition view) = keygenFullParameter high parameter)
    (hterm : ∀ T, KnownTo coalition.1 T → h (keygenTermProgrammingInput coalition view T) = seeds T)
    (hpair : ∀ p ∈ keygenCrossCoordinates coalition, h (keygenPairProgrammingInput coalition view p) = pairs p)
    (i : C.Party) (hi : i ∉ coalition.1)
    (hagree : ∀ j, j ∉ coalition.1 →
      (keys i).1 = (keys j).1 ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T →
        (keys i).2.1 T = (keys j).2.1 T) :
    (keysOf (keys i)).parameter = parameter ∧
      (∀ T, KnownTo coalition.1 T → (keysOf (keys i)).seed T = (dealtKeys parameter seeds pairs i).seed T) ∧
      (∀ j, j ∈ coalition.1 → (keysOf (keys i)).pairKey j = (dealtKeys parameter seeds pairs i).pairKey j) := by
  constructor
  · have he := (hagree (keygenFirstHonest coalition Finset.univ) (keygenFirstHonest_univ coalition)).1
    change truncateHash (keys i).1 = parameter
    rw [he, hderive _ (keygenFirstHonest_univ coalition), D_deriveKeys]
    change truncateHash (h (keygenParameterProgrammingInput coalition view)) = parameter
    rw [hparameter, truncate_keygenFullParameter]
  constructor
  · intro T hT
    by_cases hiT : i ∈ C.holders T
    · have href := keygenFirstHonest_holder coalition T
      have he := (hagree (keygenFirstHonest coalition (C.holders T)) href.2).2 T hiT href.1
      change (keys i).2.1 T = (if i ∈ C.holders T then seeds T else 0)
      rw [if_pos hiT, he, hderive _ href.2, D_deriveKeys]
      simp only [if_pos href.1]
      exact hterm T hT
    · change (keys i).2.1 T = (if i ∈ C.holders T then seeds T else 0)
      rw [hderive i hi, D_deriveKeys]
      simp [hiT]
  · intro j hj
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    have hm := keygenCrossCoordinates_cross_mem coalition i j hj hi
    have hp := hpair (C.pairOf i j (Ne.symm hji)) hm
    rw [keygenPairProgrammingInput_cross coalition view i j ⟨hj, hi⟩] at hp
    change (keys i).2.2 j = (if h : j = i then 0 else pairs (C.pairOf i j (Ne.symm h)))
    rw [hderive i hi, D_deriveKeys]
    simp only [dif_neg hji]
    exact hp

/-- The derivation input of a pair of honest operators uses just their original pair parts. -/
theorem keygen_hiddenPair_input (coalition : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .keygen (parts j) j i)
    (p : C.Pair) (hp : p.1.1 ∉ coalition.1 ∧ p.1.2 ∉ coalition.1)
    (i : C.Party) (hi : p.1.1 = i ∨ p.1.2 = i) :
    keygenPairViewInput parts revealed i p = pairInput .keygen parts p := by
  unfold keygenPairViewInput pairInput
  dsimp only
  rw [setupView_honest_sender coalition parts revealed hreceived i p.1.1 hp.1,
    setupView_honest_sender coalition parts revealed hreceived i p.1.2 hp.2,
    honestView_pair .keygen parts hi, honestView_pair .keygen parts hi.symm]

/-- The actual hidden pair key is the oracle value at its canonical raw-parts input. -/
theorem keygen_hiddenPair_derived (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .keygen (parts j) j i)
    (i j : C.Party) (hi : i ∉ coalition.1) (hj : j ∉ coalition.1) (hji : j ≠ i) :
    (D prims h (deriveKeys .keygen i (setupView .keygen i (parts i) (revealed i)))).2.2 j =
      h (pairInput .keygen parts (C.pairOf i j (Ne.symm hji))) := by
  rw [D_deriveKeys]
  simp only [dif_neg hji]
  change h (keygenPairViewInput parts revealed i (C.pairOf i j (Ne.symm hji))) = _
  apply congrArg h
  apply keygen_hiddenPair_input coalition parts revealed hreceived
  · unfold Committee.pairOf
    split_ifs <;> exact ⟨by assumption, by assumption⟩
  · exact pairOf_left_or_right i j (Ne.symm hji)

def keygenHybridSeeds (coalition : C.Coalition) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (seeds : C.Term → HashOutput) : C.Term → HashOutput :=
  fun T => if KnownTo coalition.1 T then seeds T else h (termInput .keygen parts T)

def keygenHybridPairs (coalition : C.Coalition) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (pairs : C.Pair → HashOutput) : C.Pair → HashOutput :=
  fun p => if p.1.1 ∉ coalition.1 ∧ p.1.2 ∉ coalition.1 then h (pairInput .keygen parts p) else pairs p

/-- Under extraction, successful programming, and the accepting party's honest agreements,
its entire key is one dealing. Only the hidden seeds and honest--honest pairs still use raw oracle
values; every exposed coordinate is the dealer's value. -/
theorem keygen_output_eq_hybrid_dealing (prims : Primitives) (coalition : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent revealed : C.Party → Mail C E)
    (h : Query C → HashOutput) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (high : HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .keygen (parts j) j i)
    (hextract : ∀ i j, i ∉ coalition.1 → j ∈ coalition.1 →
      extractReveal log sent j i = Msg.hashesOf (revealed i j))
    (hderive : ∀ i, i ∉ coalition.1 →
      keys i = D prims h (deriveKeys .keygen i (setupView .keygen i (parts i) (revealed i))))
    (hparameter : h (keygenParameterProgrammingInput coalition (keygenProgramView coalition parts log sent)) =
      keygenFullParameter high parameter)
    (hterm : ∀ T, KnownTo coalition.1 T →
      h (keygenTermProgrammingInput coalition (keygenProgramView coalition parts log sent) T) = seeds T)
    (hpair : ∀ p ∈ keygenCrossCoordinates coalition,
      h (keygenPairProgrammingInput coalition (keygenProgramView coalition parts log sent) p) = pairs p)
    (i : C.Party) (hi : i ∉ coalition.1)
    (hagree : ∀ j, j ∉ coalition.1 →
      (keys i).1 = (keys j).1 ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T →
        (keys i).2.1 T = (keys j).2.1 T) :
    keysOf (keys i) = dealtKeys parameter (keygenHybridSeeds coalition h parts seeds)
      (keygenHybridPairs coalition h parts pairs) i := by
  have hprogramView : ∀ j, j ∉ coalition.1 →
      keys j = D prims h (deriveKeys .keygen j (keygenProgramView coalition parts log sent j)) := by
    intro j hj
    exact (hderive j hj).trans (keygen_derived_programView prims coalition parts log sent revealed j hj
      hreceived (fun k hk => hextract j k hj hk) h)
  have hk := keygen_known_outputs_of_programmed prims coalition _ h parameter seeds pairs high keys
    hprogramView hparameter hterm hpair i hi hagree
  unfold keysOf dealtKeys
  congr 1
  · exact hk.1
  · funext T
    by_cases hiT : i ∈ C.holders T
    · simp only [if_pos hiT]
      by_cases hT : KnownTo coalition.1 T
      · rw [keygenHybridSeeds, if_pos hT]
        simpa only [keysOf, dealtKeys, if_pos hiT] using hk.2.1 T hT
      · rw [keygenHybridSeeds, if_neg hT, hderive i hi]
        exact keygen_hiddenTerm_derived prims coalition h parts revealed hreceived T hT i hiT
    · rw [if_neg hiT, hderive i hi, D_deriveKeys]
      simp [hiT]
  · funext j
    by_cases hji : j = i
    · rw [hderive i hi, D_deriveKeys]
      simp [hji]
    · simp only [dif_neg hji]
      by_cases hj : j ∈ coalition.1
      · have hn : ¬ ((C.pairOf i j (Ne.symm hji)).1.1 ∉ coalition.1 ∧
            (C.pairOf i j (Ne.symm hji)).1.2 ∉ coalition.1) := by
          unfold Committee.pairOf
          split_ifs <;> simp_all
        rw [keygenHybridPairs, if_neg hn]
        simpa only [keysOf, dealtKeys, dif_neg hji] using hk.2.2 j hj
      · have hh : (C.pairOf i j (Ne.symm hji)).1.1 ∉ coalition.1 ∧
            (C.pairOf i j (Ne.symm hji)).1.2 ∉ coalition.1 := by
          unfold Committee.pairOf
          split_ifs <;> exact ⟨by assumption, by assumption⟩
        rw [keygenHybridPairs, if_pos hh, hderive i hi]
        exact keygen_hiddenPair_derived prims coalition h parts revealed hreceived i j hi hj hji

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

/-- Replace the selected table cells by the corresponding dealer keys. -/
def keygenExchangeTable {ι Ω R : Type} (points : ι → Ω) (table : Ω → R) (keys : ι → R) : Ω → R :=
  fun q => @dite R (∃ i, points i = q) (Classical.propDecidable _)
    (fun h => keys (Classical.choose h)) (fun _ => table q)

theorem keygenExchangeTable_at {ι Ω R : Type} (points : ι → Ω) (hinj : Function.Injective points)
    (table : Ω → R) (keys : ι → R) (i : ι) :
    keygenExchangeTable points table keys (points i) = keys i := by
  classical
  unfold keygenExchangeTable
  rw [dif_pos ⟨i, rfl⟩]
  exact congrArg keys (hinj (Classical.choose_spec (show ∃ j, points j = points i from ⟨i, rfl⟩)))

theorem keygenExchangeTable_outside {ι Ω R : Type} (points : ι → Ω)
    (table : Ω → R) (keys : ι → R) (q : Ω) (hq : ∀ i, points i ≠ q) :
    keygenExchangeTable points table keys q = table q := by
  classical
  simp [keygenExchangeTable, not_exists.mpr hq]

/-- Exchange the selected oracle cells with the independent hidden dealer keys. -/
def keygenTableKeyExchange {ι Ω R : Type} (points : ι → Ω)
    (p : (Ω → R) × (ι → R)) : (Ω → R) × (ι → R) :=
  (keygenExchangeTable points p.1 p.2, fun i => p.1 (points i))

theorem keygenTableKeyExchange_involutive {ι Ω R : Type} (points : ι → Ω)
    (hinj : Function.Injective points) : Function.Involutive (keygenTableKeyExchange (R := R) points) := by
  classical
  intro p
  apply Prod.ext
  · funext q
    change keygenExchangeTable points (keygenExchangeTable points p.1 p.2) (fun i => p.1 (points i)) q = p.1 q
    rcases Classical.em (∃ i, points i = q) with hq | hq
    · obtain ⟨i, rfl⟩ := hq
      exact keygenExchangeTable_at points hinj _ _ i
    · have hn : ∀ i, points i ≠ q := not_exists.mp hq
      rw [keygenExchangeTable_outside points _ _ q hn, keygenExchangeTable_outside points _ _ q hn]
  · funext i
    exact keygenExchangeTable_at points hinj p.1 p.2 i

/-- The joint distribution is preserved, not merely the marginal distribution of the hidden keys. -/
theorem evalDist_keygenTableKeyExchange {ι Ω R : Type} [Finite ι] [Finite Ω] [Finite R] [Nonempty R]
    [SampleableType (Ω → R)] [SampleableType (ι → R)]
    (points : ι → Ω) (hinj : Function.Injective points) :
    𝒟[keygenTableKeyExchange (R := R) points <$> ($ᵗ ((Ω → R) × (ι → R)))] =
      𝒟[$ᵗ ((Ω → R) × (ι → R))] :=
  evalDist_map_bijective_uniform_cross _ _ (keygenTableKeyExchange_involutive points hinj).bijective

/-- The exchange remains valid under every continuation using both tables. -/
theorem evalDist_keygenTableKeyExchange_bind {ι Ω R α : Type}
    [Finite ι] [Finite Ω] [Finite R] [Nonempty R]
    [SampleableType (Ω → R)] [SampleableType (ι → R)]
    (points : ι → Ω) (hinj : Function.Injective points)
    (k : (Ω → R) → (ι → R) → ProbComp α) :
    𝒟[do
      let table ← $ᵗ (Ω → R)
      let keys ← $ᵗ (ι → R)
      let p := keygenTableKeyExchange points (table, keys)
      k p.1 p.2] =
    𝒟[do
      let table ← $ᵗ (Ω → R)
      let keys ← $ᵗ (ι → R)
      k table keys] := by
  classical
  have he := evalDist_keygenTableKeyExchange (R := R) points hinj
  have hb : 𝒟[(keygenTableKeyExchange (R := R) points <$> ($ᵗ ((Ω → R) × (ι → R)))) >>= fun p => k p.1 p.2] =
      𝒟[($ᵗ ((Ω → R) × (ι → R))) >>= fun p => k p.1 p.2] := by
    rw [evalDist_bind, he, ← evalDist_bind]
  rw [bind_map_left] at hb
  change 𝒟[((Prod.mk <$> ($ᵗ (Ω → R)) <*> ($ᵗ (ι → R))) >>= fun p =>
    k (keygenTableKeyExchange points p).1 (keygenTableKeyExchange points p).2)] =
    𝒟[((Prod.mk <$> ($ᵗ (Ω → R)) <*> ($ᵗ (ι → R))) >>= fun p => k p.1 p.2)] at hb
  simpa only [seq_eq_bind_map, bind_map_left, bind_assoc] using hb

/-- Cached cells outside the selected fresh positions remain unchanged. -/
theorem keygenExchangeTable_overlay {ι Ω R : Type} (points : ι → Ω)
    (table : Ω → R) (keys : ι → R) (cache : Ω → Option R)
    (hfresh : ∀ i, cache (points i) = none) :
    (fun q => (cache q).getD (keygenExchangeTable points table keys q)) =
      keygenExchangeTable points (fun q => (cache q).getD (table q)) keys := by
  classical
  funext q
  rcases Classical.em (∃ i, points i = q) with hq | hq
  · obtain ⟨i, rfl⟩ := hq
    letI : Decidable (∃ j, points j = points i) := Classical.propDecidable _
    simp only [hfresh, Option.getD_none, keygenExchangeTable]
  · have hn : ∀ i, points i ≠ q := not_exists.mp hq
    rw [keygenExchangeTable_outside points table keys q hn,
      keygenExchangeTable_outside points (fun q => (cache q).getD (table q)) keys q hn]

variable {C : Committee}

/-- Canonical raw-parts derivation inputs, indexed by the model's existing key names. -/
def keygenNamedInput (parts : C.Party → Parts C) : KeyName C → Query C
  | .parameter => parameterInput parts
  | .term T => termInput .keygen parts T
  | .pair p => pairInput .keygen parts p

def keygenNames (C : Committee) : List (KeyName C) := (Finset.univ : Finset (KeyName C)).toList

theorem keygenNamedInput_not_fixed (parts : C.Party → Parts C) (name : KeyName C) :
    ¬ IsFixed (keygenNamedInput parts name) := by
  cases name <;> simp [keygenNamedInput, parameterInput, termInput, pairInput, IsFixed]

/-- The complete canonical table may be sampled after the simulator's programming boundary.
Its insertion before the local continuation preserves that continuation's output distribution. -/
theorem evalDist_keygenNamedTable_prepend (prims : Primitives) (parts : C.Party → Parts C)
    {α : Type} (k : OracleComp (LocalSpec C) α) (s : HashCache C) :
    𝒟[(tablePrograms (keygenNames C) (keygenNamedInput parts) >>= fun _ =>
      simulateQ (localAnswer prims) k).run' s] =
      𝒟[(simulateQ (localAnswer prims) k).run' s] :=
  evalDist_tablePrograms_prepend prims _ (Finset.nodup_toList _) _
    (fun name _ => keygenNamedInput_not_fixed parts name) k s

/-- Exchange only hidden named coordinates, leaving the dealer's public and corrupt coordinates
unchanged. This uses the same `Hidden` predicate as the stated model. -/
def keygenHiddenNamedSwap (coalition : C.Coalition)
    (p : (KeyName C → HashOutput) × (KeyName C → HashOutput)) :
    (KeyName C → HashOutput) × (KeyName C → HashOutput) :=
  (fun name => if Hidden coalition name then p.2 name else p.1 name,
   fun name => if Hidden coalition name then p.1 name else p.2 name)

theorem keygenHiddenNamedSwap_involutive (coalition : C.Coalition) :
    Function.Involutive (keygenHiddenNamedSwap coalition) := by
  intro p
  apply Prod.ext <;> funext name <;>
    by_cases hh : Hidden coalition name <;> simp [keygenHiddenNamedSwap, hh]

theorem keygenHiddenNamedSwap_known (coalition : C.Coalition)
    (p : (KeyName C → HashOutput) × (KeyName C → HashOutput))
    (name : KeyName C) (hknown : ¬ Hidden coalition name) :
    (keygenHiddenNamedSwap coalition p).1 name = p.1 name ∧
      (keygenHiddenNamedSwap coalition p).2 name = p.2 name := by
  simp [keygenHiddenNamedSwap, hknown]

theorem evalDist_keygenHiddenNamedSwap (coalition : C.Coalition) :
    𝒟[keygenHiddenNamedSwap coalition <$>
      ($ᵗ ((KeyName C → HashOutput) × (KeyName C → HashOutput)))] =
    𝒟[$ᵗ ((KeyName C → HashOutput) × (KeyName C → HashOutput))] :=
  evalDist_map_bijective_uniform_cross _ _ (keygenHiddenNamedSwap_involutive coalition).bijective

theorem keygenNamedInput_injective (parts : C.Party → Parts C) (hnd : (keygenInputs parts).Nodup) :
    Function.Injective (keygenNamedInput parts) := by
  have hs := List.nodup_append.mp (List.nodup_cons.mp hnd).2
  have ht : Function.Injective (termInput .keygen parts) := by
    intro T T' he
    exact List.inj_on_of_nodup_map hs.1 (by simp [Committee.terms]) (by simp [Committee.terms]) he
  have hp : Function.Injective (pairInput .keygen parts) := by
    intro p p' he
    exact List.inj_on_of_nodup_map hs.2.1 (by simp [pairList]) (by simp [pairList]) he
  intro a b he
  cases a <;> cases b <;> try rfl
  all_goals first
    | (apply congrArg KeyName.term; exact ht he)
    | (apply congrArg KeyName.pair; exact hp he)
    | (simp [keygenNamedInput, parameterInput, termInput, pairInput] at he)

/-- Noninjective raw derivation positions are already covered by the proved input-collision bound. -/
theorem probEvent_keygenNamedInput_collision :
    Pr[fun parts => ¬ Function.Injective (keygenNamedInput parts) |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      ((Fintype.card C.Term ^ 2 + Fintype.card C.Pair ^ 2 : ℕ) : ℝ≥0∞) *
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  refine (probEvent_mono (fun parts _ hn hnd => hn (keygenNamedInput_injective parts hnd))).trans ?_
  exact probEvent_keygen_collision

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The commit-round continuation only checks abort frames and prepares the reveal. -/
theorem advance_keygenCommitResume (i : C.Party) (own : Parts C) (committed : Mail C E) :
    advance (exchangeResume (keygenRound1 i own) committed) =
      pure (if C.parties.any (fun j => Msg.isAbort (committed j)) then .done none else
        .wait (revealOutbox .keygen i own) (exchangeResume fun revealed =>
          setupRest .keygen i own committed revealed >>= fun keys => pure (keysOf keys))) := by
  unfold exchangeResume
  split_ifs
  · rfl
  · exact advance_exchange_bind _ _

/-- The inboxes at the commit boundary, including all corrupt abort frames. -/
def keygenCommitInbox (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) (sent : C.Party → Mail C E) : C.Party → Mail C E :=
  roundInbox coalition sent (keygenInitialSteps coalition parts commitments)

/-- The actual network state after the commit round. -/
def keygenRevealSteps (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) : C.Party → Step C E RealSpec (Keys C) := fun i =>
  if i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j)) then .done none else
    .wait (revealOutbox .keygen i (parts i)) (exchangeResume fun revealed =>
      setupRest .keygen i (parts i) (committed i) revealed >>= fun keys => pure (keysOf keys))

/-- The first network step computes no hashes after the adversary's commit messages. -/
theorem stepRound_keygenInitialSteps (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) :
    stepRound localRoles coalition A noFunctionality state
        (keygenInitialSteps coalition parts commitments) = (do
      let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        commitOutbox i (commitments i) c else none
      pure (st, keygenRevealSteps coalition parts (keygenCommitInbox coalition parts commitments sent), sent)) := by
  unfold stepRound
  rw [if_neg (by simp only [callInput_real, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, not_false_eq_true])]
  have hmsg : (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (keygenInitialSteps coalition parts commitments (E := E) i).outbox c else none) =
      (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then commitOutbox i (commitments i) c else none) := by
    funext c i
    split_ifs with hc
    · simp only [keygenInitialSteps, if_neg hc.2, keygenStart, Step.outbox]
    · rfl
  rw [hmsg]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only [localRoles]
  trans (Concrete.sequenceFin (fun j =>
    (pure (keygenRevealSteps coalition parts (keygenCommitInbox coalition parts commitments sent) j) :
      OracleComp (LocalSpec C) _)) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext j
    by_cases hj : j ∈ coalition.1
    · simp [keygenInitialSteps, keygenRevealSteps, hj]
    · simp only [keygenInitialSteps, if_neg hj, keygenStart]
      rw [advance_keygenCommitResume]
      simp only [keygenRevealSteps, hj, false_or, keygenCommitInbox, roundInbox]
      rfl
  · rw [sequenceFin_pure, pure_bind]

/-- The inbox before the honest opening checks. -/
def keygenRevealInbox (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) (sent : C.Party → Mail C E) : C.Party → Mail C E :=
  roundInbox coalition sent (keygenRevealSteps coalition parts committed)

/-- Every surviving reveal inbox contains all the honest openings. -/
theorem keygenRevealInbox_honest (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (i : C.Party)
    (ha : (C.parties.any fun j => Msg.isAbort (keygenRevealInbox coalition parts committed sent i j)) = false)
    (j : C.Party) (hj : j ∉ coalition.1) (hji : j ≠ i) :
    Msg.hashesOf (keygenRevealInbox coalition parts committed sent i j) =
      revealTo .keygen (parts j) j i := by
  have hno := List.any_eq_false.mp ha j (List.mem_finRange j)
  by_cases hb : (C.parties.any fun l => Msg.isAbort (committed j l)) = true
  · have hstep : keygenRevealSteps coalition parts committed j = .done none := by
      simp only [keygenRevealSteps, hb, or_true, if_true]
    have hr := roundInbox_abort coalition sent (keygenRevealSteps coalition parts committed) i j hj hstep
    change ¬ Msg.isAbort (roundInbox coalition sent (keygenRevealSteps coalition parts committed) i j) = true at hno
    rw [hr] at hno
    exact (hno rfl).elim
  · simp only [keygenRevealInbox, roundInbox, keygenRevealSteps,
      hj, hb, Bool.false_eq_true, false_or, if_false, Step.delivered, revealOutbox, if_neg (Ne.symm hji), Msg.hashesOf]

/-- If one honest operator passed the abort-frame check at reveal, all honest operators sent
reveals in that round. This includes senders that fail their own opening checks afterwards. -/
theorem keygenRevealInbox_all_honest (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (i : C.Party)
    (ha : (C.parties.any fun j => Msg.isAbort (keygenRevealInbox coalition parts committed sent i j)) = false) :
    ∀ k j, j ∉ coalition.1 → j ≠ k →
      Msg.hashesOf (keygenRevealInbox coalition parts committed sent k j) = revealTo .keygen (parts j) j k := by
  intro k j hj hjk
  have hno := List.any_eq_false.mp ha j (List.mem_finRange j)
  by_cases hb : (C.parties.any fun l => Msg.isAbort (committed j l)) = true
  · have hstep : keygenRevealSteps coalition parts committed j = .done none := by
      simp only [keygenRevealSteps, hb, or_true, if_true]
    have hr := roundInbox_abort coalition sent (keygenRevealSteps coalition parts committed) i j hj hstep
    change ¬ Msg.isAbort (roundInbox coalition sent (keygenRevealSteps coalition parts committed) i j) = true at hno
    rw [hr] at hno
    exact (hno rfl).elim
  · simp only [keygenRevealInbox, roundInbox, keygenRevealSteps,
      hj, hb, Bool.false_eq_true, false_or, if_false, Step.delivered, revealOutbox, if_neg (Ne.symm hjk), Msg.hashesOf]

abbrev KeygenEchoData (C : Committee) :=
  (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) × List HashOutput

/-- Everything the honest reveal continuation computes, before waiting for the echo round. -/
def keygenRevealCompute (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    OracleComp (LocalSpec C) (Option (KeygenEchoData C)) := do
  if C.parties.any (fun j => Msg.isAbort (revealed j)) then return none
  let opens ← liftComp (openQueries .keygen i revealed) (LocalSpec C)
  if ¬ openCheck .keygen i own committed revealed opens then return none
  let keys ← liftComp (deriveKeys .keygen i (setupView .keygen i own revealed)) (LocalSpec C)
  let shared ← liftComp (sharedQueries .keygen i keys) (LocalSpec C)
  pure (some (keys, shared))

/-- An echo step carrying the actual values and the actual shared-key hash answers. -/
def keygenEchoDataStep (i : C.Party) : Option (KeygenEchoData C) → Step C E RealSpec (Keys C)
  | none => .done none
  | some (keys, shared) => .wait (echoOutbox .keygen i keys shared) (exchangeResume fun received =>
      require (echoCheck .keygen i keys shared received) >>= fun _ => pure (keysOf keys))

/-- Exact expansion of the honest reveal continuation, with both abort tests. -/
theorem advance_keygenRevealResume (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    advance (exchangeResume (G := RealSpec) (fun revealed =>
      setupRest .keygen i own committed revealed >>= fun keys => pure (keysOf keys)) revealed) =
      keygenEchoDataStep i <$> keygenRevealCompute i own committed revealed := by
  unfold exchangeResume keygenRevealCompute
  split_ifs with ha
  · rfl
  · rw [advance_setupRest]
    simp only [map_bind]
    refine bind_congr fun opens => ?_
    split_ifs with ho
    · simp only [map_bind, map_pure, keygenEchoDataStep, pure_bind]
    · rfl

/-- All honest computations between the reveal and echo boundaries. -/
def keygenRevealComputations (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) : OracleComp (LocalSpec C) (C.Party → Option (KeygenEchoData C)) :=
  Concrete.sequenceFin fun i =>
    if i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j)) then pure none else
      keygenRevealCompute i (parts i) (committed i) (keygenRevealInbox coalition parts committed sent i)

/-- Exact reduction of the second round, retaining all honest echo data. -/
theorem stepRound_keygenRevealSteps (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) :
    stepRound localRoles coalition A noFunctionality state (keygenRevealSteps coalition parts committed) =
    (do
      let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        (keygenRevealSteps coalition parts committed i).outbox c else none
      let data ← keygenRevealComputations coalition parts committed sent
      pure (st, (fun i => keygenEchoDataStep i (data i)), sent)) := by
  unfold stepRound
  rw [if_neg (by simp only [callInput_real, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, not_false_eq_true])]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only [localRoles]
  trans (Concrete.sequenceFin (fun i =>
    (if i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j)) then pure none else
      keygenRevealCompute i (parts i) (committed i) (keygenRevealInbox coalition parts committed sent i)) >>=
      fun v => pure (keygenEchoDataStep i v)) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext i
    by_cases hi : i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j))
    · simp only [keygenRevealSteps, if_pos hi, pure_bind, keygenEchoDataStep]
    · have hc : i ∉ coalition.1 := fun hh => hi (Or.inl hh)
      rw [show keygenRevealSteps coalition parts committed i = _ from if_neg hi]
      simp only [if_neg hi, if_neg hc]
      change advance (exchangeResume _ (keygenRevealInbox coalition parts committed sent i)) = _
      rw [advance_keygenRevealResume, map_eq_bind_pure_comp]
      rfl
  · rw [sequenceFin_bind_pure]
    simp only [bind_assoc, pure_bind, keygenRevealComputations]

/-- The echo continuation has no free hash queries, even when some operators aborted. -/
theorem stepRound_keygenEchoDataSteps (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (data : C.Party → Option (KeygenEchoData C)) :
    stepRound localRoles coalition A noFunctionality state (fun i => keygenEchoDataStep i (data i)) =
    (do
      let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        (keygenEchoDataStep i (data i)).outbox c else none
      pure (st, (fun i => Step.done (match data i with
        | none => none
        | some (keys, shared) => if i ∈ coalition.1 then none else
          let inbox := roundInbox coalition sent (fun j => keygenEchoDataStep j (data j)) i
          if C.parties.any (fun j => Msg.isAbort (inbox j)) then none else
            if echoCheck .keygen i keys shared inbox then some (keysOf keys) else none)), sent)) := by
  unfold stepRound
  rw [if_neg (by simp only [callInput_real, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, not_false_eq_true])]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only [localRoles]
  trans (Concrete.sequenceFin (fun i => (pure (Step.done (match data i with
        | none => none
        | some (keys, shared) => if i ∈ coalition.1 then none else
          let inbox := roundInbox coalition sent (fun j => keygenEchoDataStep j (data j)) i
          if C.parties.any (fun j => Msg.isAbort (inbox j)) then none else
            if echoCheck .keygen i keys shared inbox then some (keysOf keys) else none)) :
      OracleComp (LocalSpec C) _)) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext i
    cases hd : data i with
    | none => rfl
    | some v =>
      rcases v with ⟨keys, shared⟩
      by_cases hi : i ∈ coalition.1
      · simp only [keygenEchoDataStep, if_pos hi]
      · simp only [keygenEchoDataStep, if_neg hi]
        exact advance_keygenEchoResume i keys shared _
  · rw [sequenceFin_pure, pure_bind]

def keygenEchoDataOutput (coalition : C.Coalition) (data : C.Party → Option (KeygenEchoData C))
    (sent : C.Party → Mail C E) (i : C.Party) : Option (Keys C) :=
  match data i with
  | none => none
  | some (keys, shared) => if i ∈ coalition.1 then none else
      let inbox := roundInbox coalition sent (fun j => keygenEchoDataStep j (data j)) i
      if C.parties.any (fun j => Msg.isAbort (inbox j)) then none else
        if echoCheck .keygen i keys shared inbox then some (keysOf keys) else none

/-- The complete last round after its honest work has already been computed. -/
def keygenFinishLocal (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (data : C.Party → Option (KeygenEchoData C)) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (Keys C))) :=
  if ∀ i, i ∉ coalition.1 → data i = none then pure (state, fun _ => none) else do
    let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (keygenEchoDataStep i (data i)).outbox c else none
    pure (st, keygenEchoDataOutput coalition data sent)

theorem executeRounds_keygenEchoDataSteps_one (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (data : C.Party → Option (KeygenEchoData C)) :
    executeRounds localRoles coalition A noFunctionality 1 state (fun i => keygenEchoDataStep i (data i)) =
      keygenFinishLocal coalition A state data := by
  have hd : (∀ i, i ∉ coalition.1 → (keygenEchoDataStep (E := E) i (data i)).isDone) ↔
      ∀ i, i ∉ coalition.1 → data i = none := by
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    cases data i <;> simp [keygenEchoDataStep, Step.isDone]
  rw [executeRounds]
  simp only [hd, keygenFinishLocal]
  split_ifs with ha
  · congr 1
    apply congrArg (fun f => (state, f))
    funext i
    cases data i <;> rfl
  · rw [stepRound_keygenEchoDataSteps]
    simp only [bind_assoc, pure_bind, executeRounds, Step.output]
    rfl

/-- The remaining two rounds, with every early-exit and abort test explicit. -/
def keygenPostCommitLocal (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (Keys C))) :=
  if ∀ i, i ∉ coalition.1 → (C.parties.any fun j => Msg.isAbort (committed i j)) = true then
    pure (state, fun _ => none)
  else do
    let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (keygenRevealSteps coalition parts committed i).outbox c else none
    let data ← keygenRevealComputations coalition parts committed sent
    keygenFinishLocal coalition A st data

theorem executeRounds_keygenRevealSteps_two (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) :
    executeRounds localRoles coalition A noFunctionality 2 state (keygenRevealSteps coalition parts committed) =
      keygenPostCommitLocal coalition A state parts committed := by
  have hd : (∀ i, i ∉ coalition.1 → (keygenRevealSteps coalition parts committed i).isDone) ↔
      ∀ i, i ∉ coalition.1 → (C.parties.any fun j => Msg.isAbort (committed i j)) = true := by
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    simp only [keygenRevealSteps, hi, false_or]
    split_ifs <;> simp_all [Step.isDone]
  rw [executeRounds]
  simp only [hd, keygenPostCommitLocal]
  split_ifs with ha
  · congr 1
    apply congrArg (fun f => (state, f))
    funext i
    unfold keygenRevealSteps
    split_ifs <;> rfl
  · rw [stepRound_keygenRevealSteps]
    simp only [bind_assoc, pure_bind, executeRounds_keygenEchoDataSteps_one]

/-- A fully split local game: start, commit, reveal, echo and final distinguish. -/
def keygenNormalizedLocalGame (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) : OracleComp (LocalSpec C) Bool := do
  let state ← A.start (corruptInputs coalition x) z
  let parts ← Concrete.sequenceFin fun (_ : C.Party) => liftComp (sampleParts (C := C)) (LocalSpec C)
  let commitments ← keygenInitialCommitments coalition parts
  let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
    commitOutbox i (commitments i) c else none
  let r ← keygenPostCommitLocal coalition A st parts (keygenCommitInbox coalition parts commitments sent)
  Z r

/-- The complete real game has the explicit three-round normal form, including arbitrary aborts. -/
theorem sameRun_keygenLocal_normalized (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    SameRun prims (keygenLocalGame coalition A x z Z) (keygenNormalizedLocalGame coalition A x z Z) := by
  refine (sameRun_keygenLocal_split prims coalition A x z Z).trans (SameRun.of_eq ?_)
  simp only [keygenLocalCommitPrefix, keygenLocalPostCommit, keygenNormalizedLocalGame,
    stepRound_keygenInitialSteps, bind_assoc, pure_bind]
  change _ = _
  simp only [setupRounds, Nat.reduceSub, executeRounds_keygenRevealSteps_two]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- All random-oracle inputs of one local query; a PRG call includes its internal hash. -/
def keygenLocalHashInputs : (LocalSpec C).Domain → List (Query C)
  | .inl _ => []
  | .inr (.inl q) => [q]
  | .inr (.inr x) => [.streamKey x.2.1]

/-- Instrument a local computation without changing any of its oracle answers. -/
def keygenHashLog {α : Type} (oa : OracleComp (LocalSpec C) α) :
    OracleComp (LocalSpec C) (α × List (Query C)) :=
  (simulateQ ((QueryImpl.id' (LocalSpec C)).withTraceAppend (fun t _ => keygenLocalHashInputs t)) oa).run

@[simp] theorem keygenHashLog_pure {α : Type} (a : α) :
    keygenHashLog (C := C) (pure a) = pure (a, []) := rfl

theorem keygenHashLog_fst {α : Type} (oa : OracleComp (LocalSpec C) α) :
    Prod.fst <$> keygenHashLog oa = oa := by
  unfold keygenHashLog
  rw [QueryImpl.fst_map_run_withTraceAppend]
  simp

theorem keygenHashLog_bind {α β : Type} (oa : OracleComp (LocalSpec C) α)
    (k : α → OracleComp (LocalSpec C) β) :
    keygenHashLog (oa >>= k) = (do
      let (a, l) ← keygenHashLog oa
      let (b, r) ← keygenHashLog (k a)
      pure (b, l ++ r)) := by
  simp [keygenHashLog, simulateQ_bind, WriterT.run_bind]

theorem keygenHashLog_hash (q : Query C) :
    keygenHashLog (liftComp (hashQuery q) (LocalSpec C)) =
      (fun y => (y, [q])) <$> liftComp (hashQuery q) (LocalSpec C) := by
  change (simulateQ ((QueryImpl.id' (LocalSpec C)).withTraceAppend
    (fun t _ => keygenLocalHashInputs t))
    (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q))))).run = _
  simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
  rfl

/-- Syntactic support of an instrumented computation, including arbitrary oracle answers. -/
def KeygenUsesOnly {α : Type} (Q : Query C → Prop) (oa : OracleComp (LocalSpec C) α) : Prop :=
  ∀ r ∈ support (keygenHashLog oa), ∀ q ∈ r.2, Q q

theorem KeygenUsesOnly.pure {α : Type} (Q : Query C → Prop) (a : α) :
    KeygenUsesOnly Q (pure a) := by
  simp [KeygenUsesOnly]

theorem KeygenUsesOnly.mono {α : Type} {P Q : Query C → Prop} {oa : OracleComp (LocalSpec C) α}
    (h : KeygenUsesOnly P oa) (hp : ∀ q, P q → Q q) : KeygenUsesOnly Q oa :=
  fun r hr q hq => hp q (h r hr q hq)

theorem KeygenUsesOnly.bind {α β : Type} {Q : Query C → Prop} {oa : OracleComp (LocalSpec C) α}
    {k : α → OracleComp (LocalSpec C) β} (h : KeygenUsesOnly Q oa)
    (hk : ∀ a, KeygenUsesOnly Q (k a)) : KeygenUsesOnly Q (oa >>= k) := by
  intro r hr q hq
  rw [keygenHashLog_bind] at hr
  simp only [support_bind, Set.mem_iUnion, Prod.exists, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨a, l, hal, b, t, hbt, rfl⟩ := hr
  rcases List.mem_append.mp hq with hq | hq
  · exact h (a, l) hal q hq
  · exact hk a (b, t) hbt q hq

theorem KeygenUsesOnly.map {α β : Type} {Q : Query C → Prop} {oa : OracleComp (LocalSpec C) α}
    (h : KeygenUsesOnly Q oa) (f : α → β) : KeygenUsesOnly Q (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind fun a => KeygenUsesOnly.pure Q (f a)

theorem KeygenUsesOnly.hash {Q : Query C → Prop} (q : Query C) (hq : Q q) :
    KeygenUsesOnly Q (liftComp (hashQuery q) (LocalSpec C)) := by
  intro r hr q' hq'
  rw [keygenHashLog_hash] at hr
  rw [support_map, Set.mem_image] at hr
  rcases hr with ⟨y, _, rfl⟩
  simpa using List.mem_singleton.mp hq' ▸ hq

theorem KeygenUsesOnly.list_mapM {α β : Type} {Q : Query C → Prop} (l : List α)
    (f : α → OracleComp (LocalSpec C) β) (hf : ∀ a ∈ l, KeygenUsesOnly Q (f a)) :
    KeygenUsesOnly Q (l.mapM f) := by
  induction l with
  | nil => exact KeygenUsesOnly.pure Q []
  | cons a l ih =>
    simp only [List.mapM_cons]
    exact (hf a (by simp)).bind fun x =>
      ((ih (fun b hb => hf b (by simp [hb]))).map (List.cons x))

theorem keygen_liftComp_mapM {α β : Type} (f : α → OracleComp (RoSpec C) β) (l : List α) :
    liftComp (l.mapM f) (LocalSpec C) = l.mapM (fun a => liftComp (f a) (LocalSpec C)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.mapM_cons, liftComp_bind, liftComp_pure, ih]

def keygenParameterViewInput (i : C.Party) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) : Query C :=
  .derive .keygen .parameter (C.parties.map fun j => (setupView .keygen i (parts i) (revealed i) j).parameter)

def keygenTermViewInput (i : C.Party) (T : C.Term) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) : Query C :=
  .derive .keygen .term ((C.parties.filter (· ∈ C.holders T)).map fun j =>
    (setupView .keygen i (parts i) (revealed i) j).term T)

/-- Every derivation query is a parameter input, a held-term input, or an endpoint-pair input. -/
theorem keygen_deriveKeys_usesOnly (i : C.Party) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) :
    KeygenUsesOnly (fun q => q = keygenParameterViewInput i parts revealed ∨
      (∃ T, i ∈ C.holders T ∧ q = keygenTermViewInput i T parts revealed) ∨
      (∃ p : C.Pair, (p.1.1 = i ∨ p.1.2 = i) ∧ q = keygenPairViewInput parts revealed i p))
      (liftComp (deriveKeys .keygen i (setupView .keygen i (parts i) (revealed i))) (LocalSpec C)) := by
  unfold deriveKeys
  simp only [ite_true, liftComp_bind, liftComp_pure]
  apply KeygenUsesOnly.bind
  · exact KeygenUsesOnly.hash _ (Or.inl rfl)
  intro parameter
  apply KeygenUsesOnly.bind
  · rw [keygen_liftComp_mapM]
    apply KeygenUsesOnly.list_mapM
    intro T hT
    split_ifs with hi
    · exact KeygenUsesOnly.hash _ (Or.inr (Or.inl ⟨T, hi, rfl⟩))
    · exact KeygenUsesOnly.pure _ 0
  · intro terms
    apply KeygenUsesOnly.bind
    · rw [keygen_liftComp_mapM]
      apply KeygenUsesOnly.list_mapM
      intro j hj
      split_ifs with hji
      · exact KeygenUsesOnly.pure _ 0
      · apply KeygenUsesOnly.hash
        right; right
        refine ⟨C.pairOf i j (Ne.symm hji), ?_, rfl⟩
        unfold Committee.pairOf
        split <;> simp
    · intro pairs
      exact KeygenUsesOnly.pure _ _

theorem keygen_commitQueries_usesOnly (i : C.Party) (own : Parts C) :
    KeygenUsesOnly (fun q => ∃ j, q = .commit .keygen i j (revealTo .keygen own i j))
      (liftComp (commitQueries .keygen i own) (LocalSpec C)) := by
  rw [commitQueries, keygen_liftComp_mapM]
  exact KeygenUsesOnly.list_mapM _ _ fun j _ => KeygenUsesOnly.hash _ ⟨j, rfl⟩

theorem keygen_openQueries_usesOnly (i : C.Party) (revealed : Mail C E) :
    KeygenUsesOnly (fun q => ∃ j, q = .commit .keygen j i (Msg.hashesOf (revealed j)))
      (liftComp (openQueries .keygen i revealed) (LocalSpec C)) := by
  rw [openQueries, keygen_liftComp_mapM]
  exact KeygenUsesOnly.list_mapM _ _ fun j _ => KeygenUsesOnly.hash _ ⟨j, rfl⟩

theorem keygen_sharedQueries_usesOnly (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    KeygenUsesOnly (fun q => ∃ j, q = .sharedKeys .keygen ((sharedTerms i j).map keys.2.1))
      (liftComp (sharedQueries .keygen i keys) (LocalSpec C)) := by
  rw [sharedQueries, keygen_liftComp_mapM]
  exact KeygenUsesOnly.list_mapM _ _ fun j _ => KeygenUsesOnly.hash _ ⟨j, rfl⟩

def keygenEchoDataKeys (data : Option (KeygenEchoData C)) :
    HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput) :=
  data.map Prod.fst |>.getD (0, fun _ => 0, fun _ => 0)

/-- The complete query footprint of one actual reveal computation. The shared inputs use its
returned keys, so they are not chosen independently of the trace. -/
def KeygenRevealInput (i : C.Party) (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (data : Option (KeygenEchoData C)) (q : Query C) : Prop :=
  (∃ j, q = .commit .keygen j i (Msg.hashesOf (revealed i j))) ∨
  q = keygenParameterViewInput i parts revealed ∨
  (∃ T, i ∈ C.holders T ∧ q = keygenTermViewInput i T parts revealed) ∨
  (∃ p : C.Pair, (p.1.1 = i ∨ p.1.2 = i) ∧ q = keygenPairViewInput parts revealed i p) ∨
  (∃ j, q = .sharedKeys .keygen ((sharedTerms i j).map (keygenEchoDataKeys data).2.1))

theorem keygenRevealCompute_hash_inputs (i : C.Party) (parts : C.Party → Parts C)
    (committed : Mail C E) (revealed : C.Party → Mail C E)
    (r : Option (KeygenEchoData C) × List (Query C))
    (hr : r ∈ support (keygenHashLog (keygenRevealCompute i (parts i) committed (revealed i)))) :
    ∀ q ∈ r.2, KeygenRevealInput i parts revealed r.1 q := by
  unfold keygenRevealCompute at hr
  split_ifs at hr with ha
  · simp only [keygenHashLog_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp
  · simp only [pure_bind] at hr
    rw [keygenHashLog_bind] at hr
    simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨⟨opens, lo⟩, hlo, ⟨out, lt⟩, hlt, rfl⟩ := hr
    by_cases ho : openCheck .keygen i (parts i) committed (revealed i) opens
    · simp only [ho, not_true_eq_false, if_false, pure_bind] at hlt
      rw [keygenHashLog_bind] at hlt
      simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hlt
      obtain ⟨⟨keys, lk⟩, hlk, ⟨out', ls⟩, hls, heq⟩ := hlt
      rw [keygenHashLog_bind] at hls
      simp only [support_bind, Set.mem_iUnion, keygenHashLog_pure,
        support_pure, Set.mem_singleton_iff] at hls
      obtain ⟨⟨shared, ls'⟩, hls', ⟨o, le⟩, he, he'⟩ := hls
      cases he
      cases he'
      cases heq
      intro q hq
      simp only [List.mem_append, List.append_nil] at hq
      rcases hq with hq | hq | hq
      · exact Or.inl (keygen_openQueries_usesOnly i (revealed i) (opens, lo) hlo q hq)
      · rcases keygen_deriveKeys_usesOnly i parts revealed (keys, lk) hlk q hq with hp | ht | hp
        · exact Or.inr (Or.inl hp)
        · exact Or.inr (Or.inr (Or.inl ht))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hp)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (keygen_sharedQueries_usesOnly i keys (shared, ls') hls' q hq))))
    · simp only [ho, not_false_eq_true, if_true, keygenHashLog_pure, support_pure,
        Set.mem_singleton_iff] at hlt
      cases hlt
      intro q hq
      exact Or.inl (keygen_openQueries_usesOnly i (revealed i) (opens, lo) hlo q (by simpa using hq))

set_option maxHeartbeats 1000000 in
/-- Each executed reveal input belongs to the six-family cover once honest reveals are present. -/
theorem keygenRevealInput_mem_cover (coalition : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (data : C.Party → Option (KeygenEchoData C))
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .keygen (parts j) j i)
    (i : C.Party) (hi : i ∉ coalition.1) (q : Query C)
    (hq : KeygenRevealInput i parts revealed (data i) q) :
    q ∈ keygenFreeInputCover coalition
      (fun i j => .commit .keygen i j (revealTo .keygen (parts i) i j))
      (fun i j => .commit .keygen j i (Msg.hashesOf (revealed i j)))
      (fun i j => .sharedKeys .keygen ((sharedTerms i j).map (keygenEchoDataKeys (data i)).2.1))
      (fun i => keygenParameterViewInput i parts revealed)
      (fun i T => keygenTermViewInput i T parts revealed)
      (keygenPairRepresentative coalition parts revealed) := by
  rcases hq with ⟨j, rfl⟩ | rfl | ⟨T, hT, rfl⟩ | ⟨p, hip, rfl⟩ | ⟨j, rfl⟩
  · exact keygen_openInput_covered coalition parts revealed hreceived _ _ _ _ i j hi
  all_goals simp only [keygenFreeInputCover, List.mem_append, List.mem_flatMap,
    List.mem_map, Finset.mem_toList, Finset.mem_compl, Committee.parties, List.mem_finRange,
    true_and, List.mem_cons]
  · aesop
  · have hTm : T ∈ C.terms := by simp [Committee.terms]
    aesop
  · have hp := keygenPairViewInput_eq_representative coalition parts revealed hreceived i hi p hip
    have hpm : p ∈ pairList C := by simp [pairList]
    aesop
  · aesop

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Every logged query of a sequence belongs to one actual component run with the returned value. -/
theorem keygenHashLog_sequenceFin_support {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp (LocalSpec C) α)
      (r : (Fin n → α) × List (Query C)), r ∈ support (keygenHashLog (Concrete.sequenceFin f)) →
      ∀ q ∈ r.2, ∃ i, ∃ s : α × List (Query C),
        s ∈ support (keygenHashLog (f i)) ∧ s.1 = r.1 i ∧ q ∈ s.2
  | 0, f, r, hr => by
      simp only [Concrete.sequenceFin, keygenHashLog_pure, support_pure, Set.mem_singleton_iff] at hr
      subst hr
      simp
  | n + 1, f, r, hr => by
      simp only [Concrete.sequenceFin, keygenHashLog_bind, keygenHashLog_pure,
        support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨⟨a, la⟩, ha, ⟨out, lb⟩, hb, rfl⟩ := hr
      obtain ⟨⟨tail, lt⟩, ht, ⟨v, lv⟩, hv, he⟩ := hb
      cases hv
      cases he
      intro q hq
      simp only [List.append_nil, List.mem_append] at hq
      rcases hq with hq | hq
      · exact ⟨0, (a, la), ha, rfl, hq⟩
      · obtain ⟨i, s, hs, he, hq⟩ := keygenHashLog_sequenceFin_support
          (fun j : Fin n => f j.succ) (tail, lt) ht q hq
        exact ⟨i.succ, s, hs, he, hq⟩

/-- A reveal trace that has any query necessarily passed the abort-frame test. -/
theorem keygenRevealCompute_nonempty (i : C.Party) (own : Parts C) (committed revealed : Mail C E)
    (r : Option (KeygenEchoData C) × List (Query C))
    (hr : r ∈ support (keygenHashLog (keygenRevealCompute i own committed revealed)))
    (q : Query C) (hq : q ∈ r.2) :
    (C.parties.any fun j => Msg.isAbort (revealed j)) = false := by
  by_contra ha
  have ha' : (C.parties.any fun j => Msg.isAbort (revealed j)) = true := by
    cases he : (C.parties.any fun j => Msg.isAbort (revealed j)) <;> simp_all
  simp only [keygenRevealCompute, ha', if_true, keygenHashLog_pure, support_pure,
    Set.mem_singleton_iff] at hr
  cases hr
  cases hq

/-- Every query in the actual second-round trace belongs to its returned party's footprint. -/
theorem keygenRevealComputations_hash_inputs (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E)
    (r : (C.Party → Option (KeygenEchoData C)) × List (Query C))
    (hr : r ∈ support (keygenHashLog (keygenRevealComputations coalition parts committed sent)))
    (q : Query C) (hq : q ∈ r.2) :
    (∀ k j, j ∉ coalition.1 → j ≠ k →
      Msg.hashesOf (keygenRevealInbox coalition parts committed sent k j) = revealTo .keygen (parts j) j k) ∧
    ∃ i, i ∉ coalition.1 ∧ KeygenRevealInput i parts
      (keygenRevealInbox coalition parts committed sent) (r.1 i) q := by
  obtain ⟨i, s, hs, he, hq⟩ := keygenHashLog_sequenceFin_support _ r hr q hq
  by_cases hi : i ∈ coalition.1 ∨ (C.parties.any fun j => Msg.isAbort (committed i j)) = true
  · simp only [if_pos hi, keygenHashLog_pure, support_pure, Set.mem_singleton_iff] at hs
    cases hs
    cases hq
  · simp only [if_neg hi] at hs
    have ha := keygenRevealCompute_nonempty i (parts i) (committed i)
      (keygenRevealInbox coalition parts committed sent i) s hs q hq
    refine ⟨keygenRevealInbox_all_honest coalition parts committed sent i ha, i,
      (fun hc => hi (Or.inl hc)), ?_⟩
    rw [← he]
    exact keygenRevealCompute_hash_inputs i parts (committed i)
      (keygenRevealInbox coalition parts committed sent) s hs q hq

/-- The initial trace contains exactly the honest commitment family. -/
theorem keygenInitialCommitments_hash_inputs (coalition : C.Coalition) (parts : C.Party → Parts C)
    (r : (C.Party → List HashOutput) × List (Query C))
    (hr : r ∈ support (keygenHashLog (keygenInitialCommitments coalition parts)))
    (q : Query C) (hq : q ∈ r.2) :
    ∃ i, i ∉ coalition.1 ∧ ∃ j, q = .commit .keygen i j (revealTo .keygen (parts i) i j) := by
  obtain ⟨i, s, hs, _, hq⟩ := keygenHashLog_sequenceFin_support _ r hr q hq
  by_cases hi : i ∈ coalition.1
  · simp only [if_pos hi, keygenHashLog_pure, support_pure, Set.mem_singleton_iff] at hs
    cases hs
    cases hq
  · simp only [if_neg hi] at hs
    exact ⟨i, hi, keygen_commitQueries_usesOnly i (parts i) s hs q hq⟩

/-- The first- and second-round traces cover all free hash work in the split real execution. -/
theorem keygen_all_free_inputs_card_le (coalition : C.Coalition) (parts : C.Party → Parts C)
    (initial : (C.Party → List HashOutput) × List (Query C))
    (hi : initial ∈ support (keygenHashLog (keygenInitialCommitments coalition parts)))
    (committed sent : C.Party → Mail C E)
    (reveal : (C.Party → Option (KeygenEchoData C)) × List (Query C))
    (hr : reveal ∈ support (keygenHashLog (keygenRevealComputations coalition parts committed sent))) :
    (initial.2 ++ reveal.2).toFinset.card ≤ keygenSecrets C := by
  apply keygenFreeInputCover_card_le coalition
    (fun i j => .commit .keygen i j (revealTo .keygen (parts i) i j))
    (fun i j => .commit .keygen j i (Msg.hashesOf (keygenRevealInbox coalition parts committed sent i j)))
    (fun i j => .sharedKeys .keygen ((sharedTerms i j).map (keygenEchoDataKeys (reveal.1 i)).2.1))
    (fun i => keygenParameterViewInput i parts (keygenRevealInbox coalition parts committed sent))
    (fun i T => keygenTermViewInput i T parts (keygenRevealInbox coalition parts committed sent))
    (keygenPairRepresentative coalition parts (keygenRevealInbox coalition parts committed sent))
  intro q hq
  rcases List.mem_append.mp (List.mem_toFinset.mp hq) with hq | hq
  · obtain ⟨i, hih, j, rfl⟩ := keygenInitialCommitments_hash_inputs coalition parts initial hi q hq
    simp only [keygenFreeInputCover, List.mem_append, List.mem_flatMap, List.mem_map,
      Finset.mem_toList, Finset.mem_compl, Committee.parties, List.mem_finRange, true_and]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, hih, j, rfl⟩))))
  · obtain ⟨hreceived, i, hih, hqi⟩ := keygenRevealComputations_hash_inputs coalition parts committed sent reveal hr q hq
    exact keygenRevealInput_mem_cover coalition parts _ reveal.1 hreceived i hih q hqi

/-- Log the free computations after the commit boundary and keep the actual echo output. -/
def keygenFreeTracePostCommit (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    OracleComp (LocalSpec C) ((A.State × (C.Party → Option (Keys C))) × List (Query C)) :=
  if ∀ i, i ∉ coalition.1 → (C.parties.any fun j => Msg.isAbort (committed i j)) = true then
    pure ((state, fun _ => none), [])
  else do
    let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (keygenRevealSteps coalition parts committed i).outbox c else none
    let (data, inputs) ← keygenHashLog (keygenRevealComputations coalition parts committed sent)
    let out ← keygenFinishLocal coalition A st data
    pure (out, inputs)

theorem fst_keygenFreeTracePostCommit (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    Prod.fst <$> keygenFreeTracePostCommit coalition A state parts committed =
      keygenPostCommitLocal coalition A state parts committed := by
  unfold keygenFreeTracePostCommit keygenPostCommitLocal
  split_ifs
  · rfl
  · simp only [map_bind]
    refine bind_congr fun r => ?_
    rcases r with ⟨st, sent⟩
    dsimp only
    conv_rhs => rw [← keygenHashLog_fst (keygenRevealComputations coalition parts committed sent), bind_map_left]
    refine bind_congr fun data => ?_
    simp only [map_bind, map_pure, bind_pure_comp, bind_pure, id_map]

/-- A complete real execution instrumented only on the honest hash computations. -/
def keygenFreeTraceLocalGame (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    OracleComp (LocalSpec C) (Bool × List (Query C)) := do
  let state ← A.start (corruptInputs coalition x) z
  let parts ← Concrete.sequenceFin fun (_ : C.Party) => liftComp (sampleParts (C := C)) (LocalSpec C)
  let (commitments, initial) ← keygenHashLog (keygenInitialCommitments coalition parts)
  let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
    commitOutbox i (commitments i) c else none
  let (r, rest) ← keygenFreeTracePostCommit coalition A st parts (keygenCommitInbox coalition parts commitments sent)
  let out ← Z r
  pure (out, initial ++ rest)

theorem fst_keygenFreeTraceLocalGame (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    Prod.fst <$> keygenFreeTraceLocalGame coalition A x z Z = keygenNormalizedLocalGame coalition A x z Z := by
  unfold keygenFreeTraceLocalGame keygenNormalizedLocalGame
  simp only [map_bind]
  refine bind_congr fun state => bind_congr fun parts => ?_
  conv_rhs => rw [← keygenHashLog_fst (keygenInitialCommitments coalition parts), bind_map_left]
  refine bind_congr fun initial => ?_
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only
  conv_rhs => rw [← fst_keygenFreeTracePostCommit coalition A st parts _, bind_map_left]
  refine bind_congr fun rest => ?_
  simp only [map_bind, map_pure, bind_pure_comp, bind_pure, id_map]

/-- Prefix commitments alone are also covered when the execution stops before reveal. -/
theorem keygen_initial_free_inputs_card_le (coalition : C.Coalition) (parts : C.Party → Parts C)
    (initial : (C.Party → List HashOutput) × List (Query C))
    (hi : initial ∈ support (keygenHashLog (keygenInitialCommitments coalition parts))) :
    initial.2.toFinset.card ≤ keygenSecrets C := by
  apply keygenFreeInputCover_card_le coalition
    (fun i j => .commit .keygen i j (revealTo .keygen (parts i) i j))
    (fun _ _ => .sharedKeys .keygen []) (fun _ _ => .sharedKeys .keygen [])
    (fun _ => .sharedKeys .keygen []) (fun _ _ => .sharedKeys .keygen []) (fun _ => .sharedKeys .keygen [])
  intro q hq
  obtain ⟨i, hih, j, rfl⟩ := keygenInitialCommitments_hash_inputs coalition parts initial hi q (List.mem_toFinset.mp hq)
  simp only [keygenFreeInputCover, List.mem_append, List.mem_flatMap, List.mem_map,
    Finset.mem_toList, Finset.mem_compl, Committee.parties, List.mem_finRange, true_and]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨i, hih, j, rfl⟩))))

/-- `keygenSecrets` bounds every distinct free hash input in every complete instrumented run.
No extraction, freshness, collision, successful-output or query-bound hypothesis is assumed. -/
theorem keygenFreeTraceLocalGame_card_le (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C))
    (r : Bool × List (Query C)) (hr : r ∈ support (keygenFreeTraceLocalGame coalition A x z Z)) :
    r.2.toFinset.card ≤ keygenSecrets C := by
  unfold keygenFreeTraceLocalGame at hr
  simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨state, _, parts, _, ⟨commitments, initial⟩, hi, ⟨st, sent⟩, _, ⟨out, rest⟩, hrest,
    b, _, rfl⟩ := hr
  unfold keygenFreeTracePostCommit at hrest
  split_ifs at hrest with ha
  · simp only [support_pure, Set.mem_singleton_iff] at hrest
    cases hrest
    simp only [List.append_nil]
    exact keygen_initial_free_inputs_card_le coalition parts (commitments, initial) hi
  · simp only [support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hrest
    obtain ⟨⟨st', sent'⟩, _, ⟨data, inputs⟩, hd, out', _, he⟩ := hrest
    cases he
    exact keygen_all_free_inputs_card_le coalition parts (commitments, initial) hi _ sent' (data, inputs) hd

/-- The bound holds in the actual lazy oracle semantics, starting from every cache. -/
theorem keygenFreeTraceLocalGame_run_card_le (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (cache : HashCache C)
    (r : Bool × List (Query C))
    (hr : r ∈ support ((simulateQ (localAnswer prims) (keygenFreeTraceLocalGame coalition A x z Z)).run' cache)) :
    r.2.toFinset.card ≤ keygenSecrets C :=
  keygenFreeTraceLocalGame_card_le coalition A x z Z r
    (support_simulateQ_run'_subset (localAnswer prims) _ cache hr)

/-- Instrumentation preserves the complete real-game result distribution. -/
theorem evalDist_keygenFreeTraceLocalGame (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (cache : HashCache C) :
    evalDist (Prod.fst <$> (simulateQ (localAnswer prims) (keygenFreeTraceLocalGame coalition A x z Z)).run' cache) =
      evalDist ((simulateQ (localAnswer prims) (keygenLocalGame coalition A x z Z)).run' cache) := by
  have he : Prod.fst <$> (simulateQ (localAnswer prims) (keygenFreeTraceLocalGame coalition A x z Z)).run' cache =
      (simulateQ (localAnswer prims) (Prod.fst <$> keygenFreeTraceLocalGame coalition A x z Z)).run' cache := by
    simp [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  rw [he, fst_keygenFreeTraceLocalGame]
  simp only [StateT.run'_eq, evalDist_map, sameRun_keygenLocal_normalized prims coalition A x z Z cache]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- Erase only the points cells; all other random-oracle cells are retained. -/
def keygenStripCache (points : Query C → Prop) (cache : HashCache C) : HashCache C :=
  fun q => if points q then none else cache q

theorem keygenStripCache_query (points : Query C → Prop) (q : Query C)
    (hq : ¬ points q) (y : HashOutput) (cache : HashCache C) :
    keygenStripCache points (cache.cacheQuery q y) = (keygenStripCache points cache).cacheQuery q y := by
  funext q'
  by_cases hp : points q'
  · have hne : q' ≠ q := fun he => hq (he ▸ hp)
    simp [keygenStripCache, hp, QueryCache.cacheQuery, hne]
  · by_cases he : q' = q
    · subst q'; simp [keygenStripCache, hq]
    · simp [keygenStripCache, hp, QueryCache.cacheQuery, Function.update_apply, he]

/-- An unprotected hash query commutes with erasure of the points cache cells. -/
theorem hashAnswer_keygenStripCache (prims : Primitives) (points : Query C → Prop)
    (q : Query C) (hq : ¬ points q) (cache : HashCache C) :
    (fun r : HashOutput × HashCache C => (r.1, keygenStripCache points r.2)) <$>
        (hashAnswer prims q).run cache =
      (hashAnswer prims q).run (keygenStripCache points cache) := by
  by_cases hf : IsFixed q
  · obtain ⟨input, rfl, hinput⟩ := hf
    rw [hashAnswer_of_isFixed prims hinput]
    rfl
  · rw [hashAnswer_of_not_isFixed prims hf, OracleSpec.randomOracle]
    have hs : keygenStripCache points cache q = cache q := by simp [keygenStripCache, hq]
    cases he : cache q with
    | none =>
      rw [QueryImpl.withCaching_run_none _ he, QueryImpl.withCaching_run_none _ (hs.trans he)]
      simp only [Functor.map_map, keygenStripCache_query points q hq]
    | some y =>
      rw [QueryImpl.withCaching_run_some _ he, QueryImpl.withCaching_run_some _ (hs.trans he)]
      rfl

/-- The points query test includes the internal hash of a counted PRG call. -/
def KeygenTouches (points : Query C → Prop) (t : (LocalSpec C).Domain) : Prop :=
  ∃ q ∈ keygenLocalHashInputs t, points q

/-- All unprotected local queries commute with cache erasure, including private sampling and PRG. -/
theorem localAnswer_keygenStripCache (prims : Primitives) (points : Query C → Prop)
    (t : (LocalSpec C).Domain) (ht : ¬ KeygenTouches points t) (cache : HashCache C) :
    (fun r : (LocalSpec C).Range t × HashCache C => (r.1, keygenStripCache points r.2)) <$>
        (localAnswer prims t).run cache =
      (localAnswer prims t).run (keygenStripCache points cache) := by
  rcases t with n | q | x
  · change _ <$> (fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _) =
      (fun y => (y, keygenStripCache points cache)) <$> (query (spec := unifSpec) n : ProbComp _)
    simp only [Functor.map_map]
    rfl
  · exact hashAnswer_keygenStripCache prims points q
      (fun hq => ht ⟨q, by simp [keygenLocalHashInputs], hq⟩) cache
  · have hp : ¬ points (.streamKey x.2.1) :=
      fun hq => ht ⟨_, by simp [keygenLocalHashInputs], hq⟩
    change _ <$> (prgAnswer prims x).run cache = (prgAnswer prims x).run _
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
    conv_rhs => rw [← hashAnswer_keygenStripCache prims points (.streamKey x.2.1) hp cache,
      bind_map_left]
    rfl

/-- Stop a local computation immediately before its first points query. -/
def keygenAvoid (points : Query C → Prop) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    OracleComp (LocalSpec C) (Option α) :=
  (simulateQ (fun t => (if KeygenTouches points t then failure else
    OptionT.lift (OracleComp.lift (OracleSpec.query t)) : OptionT (OracleComp (LocalSpec C)) _)) oa).run

@[simp] theorem keygenAvoid_pure (points : Query C → Prop) {α : Type} (a : α) :
    keygenAvoid points (pure a) = pure (some a) := rfl

theorem keygenAvoid_query_bind (points : Query C → Prop) {α : Type} (t : (LocalSpec C).Domain)
    (k : (LocalSpec C).Range t → OracleComp (LocalSpec C) α) :
    keygenAvoid points (OracleComp.lift (OracleSpec.query t) >>= k) =
      if KeygenTouches points t then pure none else
        OracleComp.lift (OracleSpec.query t) >>= fun a => keygenAvoid points (k a) := by
  unfold keygenAvoid
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
  split_ifs <;> simp [OptionT.run_bind, OptionT.run_lift]

/-- An adaptive computation stopped before a points query cannot distinguish the points
cache contents. The equality preserves its result and the entire unprotected final cache. -/
theorem keygenAvoid_run_strip (prims : Primitives) (points : Query C → Prop) {α : Type}
    (oa : OracleComp (LocalSpec C) α) :
    ∀ cache : HashCache C,
      (fun r : Option α × HashCache C => (r.1, keygenStripCache points r.2)) <$>
          (simulateQ (localAnswer prims) (keygenAvoid points oa)).run cache =
        (simulateQ (localAnswer prims) (keygenAvoid points oa)).run (keygenStripCache points cache) := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro cache; rfl
  | query_bind t k ih =>
    intro cache
    rw [keygenAvoid_query_bind]
    split_ifs with ht
    · rfl
    · simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
        id_map, StateT.run_bind, map_bind]
      conv_rhs => rw [← localAnswer_keygenStripCache prims points t ht cache, bind_map_left]
      exact bind_congr fun r => ih r.1 r.2

/-- Arbitrary initial caches with the same unprotected cells give the same stopped output law. -/
theorem keygenAvoid_run'_eq (prims : Primitives) (points : Query C → Prop) {α : Type}
    (oa : OracleComp (LocalSpec C) α) (s t : HashCache C)
    (hst : ∀ q, ¬ points q → s q = t q) :
    (simulateQ (localAnswer prims) (keygenAvoid points oa)).run' s =
      (simulateQ (localAnswer prims) (keygenAvoid points oa)).run' t := by
  have he : keygenStripCache points s = keygenStripCache points t := by
    funext q
    unfold keygenStripCache
    split_ifs with hq
    · rfl
    · exact hst q hq
  have hs := congrArg (Functor.map Prod.fst) (keygenAvoid_run_strip prims points oa s)
  have ht := congrArg (Functor.map Prod.fst) (keygenAvoid_run_strip prims points oa t)
  simp only [Functor.map_map] at hs ht
  simp only [StateT.run'_eq]
  exact hs.trans ((congrArg (fun cache => Prod.fst <$>
    (simulateQ (localAnswer prims) (keygenAvoid points oa)).run cache) he).trans ht.symm)

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

def KeygenGoodLog (points : Query C → Prop) (l : List (Query C)) : Prop := ∀ q ∈ l, ¬ points q

@[simp] theorem keygenGoodLog_append (points : Query C → Prop) (l r : List (Query C)) :
    KeygenGoodLog points (l ++ r) ↔ KeygenGoodLog points l ∧ KeygenGoodLog points r := by
  simp [KeygenGoodLog, List.mem_append, or_imp, forall_and]

@[simp] theorem keygenGoodLog_local (points : Query C → Prop) (t : (LocalSpec C).Domain) :
    KeygenGoodLog points (keygenLocalHashInputs t) ↔ ¬ KeygenTouches points t := by
  simp [KeygenGoodLog, KeygenTouches]

theorem keygenHashLog_query_bind {α : Type} (t : (LocalSpec C).Domain)
    (k : (LocalSpec C).Range t → OracleComp (LocalSpec C) α) :
    keygenHashLog (OracleComp.lift (OracleSpec.query t) >>= k) = (do
      let u ← OracleComp.lift (OracleSpec.query t)
      let (a, l) ← keygenHashLog (k u)
      pure (a, keygenLocalHashInputs t ++ l)) := by
  rw [keygenHashLog_bind]
  have he : keygenHashLog (OracleComp.lift (OracleSpec.query t)) =
      (fun u => (u, keygenLocalHashInputs t)) <$> OracleComp.lift (OracleSpec.query t) := by
    simp only [keygenHashLog, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
    rcases t with n | q | x <;> rfl
  rw [he, bind_map_left]

theorem keygenHashLog_run_query_bind (prims : Primitives) {α : Type} (t : (LocalSpec C).Domain)
    (k : (LocalSpec C).Range t → OracleComp (LocalSpec C) α) (cache : HashCache C) :
    (simulateQ (localAnswer prims) (keygenHashLog (OracleComp.lift (OracleSpec.query t) >>= k))).run cache =
      (do
        let p ← (localAnswer prims t).run cache
        (fun r : (α × List (Query C)) × HashCache C =>
          ((r.1.1, keygenLocalHashInputs t ++ r.1.2), r.2)) <$>
            (simulateQ (localAnswer prims) (keygenHashLog (k p.1))).run p.2) := by
  rw [keygenHashLog_query_bind]
  simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
    StateT.run_bind, simulateQ_pure, StateT.run_pure]
  refine bind_congr fun p => ?_
  rw [map_eq_bind_pure_comp]
  rfl

/-- Rejecting at the first protected query gives exactly the original accepting mass with no hit. -/
theorem probEvent_keygenHashLog_good_eq_avoid (prims : Primitives) (points : Query C → Prop)
    {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∀ (cache : HashCache C) (a : α),
      Pr[fun r => r.1.1 = a ∧ KeygenGoodLog points r.1.2 |
        (simulateQ (localAnswer prims) (keygenHashLog oa)).run cache] =
      Pr[fun r => r.1 = some a | (simulateQ (localAnswer prims) (keygenAvoid points oa)).run cache] := by
  induction oa using OracleComp.inductionOn with
  | pure b =>
    intro cache a
    letI : DecidableEq α := Classical.decEq α
    have hg : KeygenGoodLog points [] := by simp [KeygenGoodLog]
    simp only [keygenHashLog_pure, keygenAvoid_pure, simulateQ_pure, StateT.run_pure,
      probEvent_pure, hg, and_true, Option.some.injEq]
  | query_bind t k ih =>
    intro cache a
    rw [keygenHashLog_run_query_bind, keygenAvoid_query_bind]
    by_cases ht : KeygenTouches points t
    · rw [if_pos ht]
      have hn : (none : Option α) ≠ some a := by intro h; cases h
      simp only [simulateQ_pure, StateT.run_pure, probEvent_pure, if_neg hn]
      rw [probEvent_bind_eq_tsum]
      simp only [probEvent_map, Function.comp_def, keygenGoodLog_append, keygenGoodLog_local,
        ht, not_true_eq_false, false_and, and_false, probEvent_False, mul_zero, tsum_zero]
    · rw [if_neg ht]
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
        id_map, StateT.run_bind]
      rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      apply tsum_congr
      intro p
      congr 1
      simp only [probEvent_map, Function.comp_def, keygenGoodLog_append, keygenGoodLog_local,
        ht, not_false_eq_true, true_and]
      exact ih p.1 p.2 a

/-- Exact equality of accepting-and-no-hit mass after changing any protected cache values.
The local computation is arbitrary and adaptive; legitimate queries outside `points` are unrestricted. -/
theorem probEvent_keygenHashLog_good_eq (prims : Primitives) (points : Query C → Prop)
    {α : Type} (oa : OracleComp (LocalSpec C) α) (s t : HashCache C)
    (hst : ∀ q, ¬ points q → s q = t q) (a : α) :
    Pr[fun r => r.1.1 = a ∧ KeygenGoodLog points r.1.2 |
      (simulateQ (localAnswer prims) (keygenHashLog oa)).run s] =
    Pr[fun r => r.1.1 = a ∧ KeygenGoodLog points r.1.2 |
      (simulateQ (localAnswer prims) (keygenHashLog oa)).run t] := by
  rw [probEvent_keygenHashLog_good_eq_avoid, probEvent_keygenHashLog_good_eq_avoid]
  have he := keygenAvoid_run'_eq prims points oa s t hst
  have hp := congrArg (fun m : ProbComp (Option α) => Pr[= some a | m]) he
  simpa only [StateT.run'_eq, probOutput_map, Function.comp_def] using hp

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

def keygenInstallValues {ι : Type} (indices : List ι) (inputs : ι → Query C)
    (values : ι → HashOutput) (cache : HashCache C) : HashCache C :=
  indices.foldl (fun s i => programCache (inputs i) (values i) s) cache

/-- The deterministic install is exactly the model's sequence of programming attempts. -/
theorem programValues_run_install {ι : Type} (indices : List ι) (inputs : ι → Query C)
    (values : ι → HashOutput) (cache : HashCache C) :
    (programValues (indices.map inputs) (indices.map values)).run cache =
      pure ((), keygenInstallValues indices inputs values cache) := by
  induction indices generalizing cache with
  | nil => rfl
  | cons i l ih =>
    simp only [List.map_cons, programValues_run_cons, keygenInstallValues, List.foldl_cons]
    exact ih _

theorem programCache_agrees_off (points : Query C → Prop) (q : Query C) (x y : HashOutput)
    (s t : HashCache C) (hst : ∀ z, ¬ points z → s z = t z) (hxy : ¬ points q → x = y) :
    ∀ z, ¬ points z → programCache q x s z = programCache q y t z := by
  intro z hz
  by_cases he : z = q
  · subst z
    have hs := hst q hz
    have hv := hxy hz
    subst y
    unfold programCache
    rw [hs]
    split_ifs
    · exact hs
    · simp
  · unfold programCache
    split_ifs <;> simpa only [QueryCache.cacheQuery_of_ne _ _ he] using hst z hz

/-- Installing two tables that differ only at protected inputs preserves every other cell. -/
theorem keygenInstallValues_agrees_off {ι : Type} (points : Query C → Prop)
    (indices : List ι) (inputs : ι → Query C) (left right : ι → HashOutput)
    (s t : HashCache C) (hst : ∀ q, ¬ points q → s q = t q)
    (hvalues : ∀ i ∈ indices, ¬ points (inputs i) → left i = right i) :
    ∀ q, ¬ points q → keygenInstallValues indices inputs left s q =
      keygenInstallValues indices inputs right t q := by
  induction indices generalizing s t with
  | nil => exact hst
  | cons i l ih =>
    simp only [keygenInstallValues, List.foldl_cons]
    exact ih _ _ (programCache_agrees_off points (inputs i) (left i) (right i) s t hst
      (hvalues i (by simp))) (fun j hj => hvalues j (by simp [hj]))

/-- Only raw derivation inputs of hidden names are excluded. Echo inputs remain unrestricted. -/
def KeygenHiddenInput (coalition : C.Coalition) (parts : C.Party → Parts C) (q : Query C) : Prop :=
  ∃ name, Hidden coalition name ∧ keygenNamedInput parts name = q

def keygenNamedInstall (parts : C.Party → Parts C) (table : KeyName C → HashOutput)
    (cache : HashCache C) : HashCache C :=
  keygenInstallValues (keygenNames C) (keygenNamedInput parts) table cache

/-- The actual named programming block respects the hidden-coordinate exchange, even with
pre-existing cache cells, repeated inputs or unsuccessful programming attempts. -/
theorem keygenNamedInstall_swap_agrees (coalition : C.Coalition) (parts : C.Party → Parts C)
    (p : (KeyName C → HashOutput) × (KeyName C → HashOutput)) (s t : HashCache C)
    (hst : ∀ q, ¬ KeygenHiddenInput coalition parts q → s q = t q) :
    ∀ q, ¬ KeygenHiddenInput coalition parts q →
      keygenNamedInstall parts p.1 s q =
        keygenNamedInstall parts (keygenHiddenNamedSwap coalition p).1 t q := by
  apply keygenInstallValues_agrees_off _ _ _ _ _ _ _ hst
  intro name _ hn
  have hk : ¬ Hidden coalition name := fun hh => hn ⟨name, hh, rfl⟩
  exact (keygenHiddenNamedSwap_known coalition p name hk).1.symm

/-- A cache established before the hidden exchange may depend on every exposed dealer coordinate. -/
def KeygenBaseKnown (coalition : C.Coalition)
    (base : (KeyName C → HashOutput) → HashCache C) : Prop :=
  ∀ d d', (∀ name, ¬ Hidden coalition name → d name = d' name) → base d = base d'

/-- Export either the hidden oracle-table coordinates or the independent hidden dealer coordinates,
then run an arbitrary adaptive continuation, stopping only at hidden raw derivation inputs. -/
def keygenHiddenExport (prims : Primitives) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (base : (KeyName C → HashOutput) → HashCache C) {α : Type}
    (k : (KeyName C → HashOutput) → OracleComp (LocalSpec C) α) (useOracle : Bool) : ProbComp (Option α) := do
  let p ← $ᵗ ((KeyName C → HashOutput) × (KeyName C → HashOutput))
  let out := if useOracle then (keygenHiddenNamedSwap coalition p).2 else p.2
  (simulateQ (localAnswer prims) (keygenAvoid (KeygenHiddenInput coalition parts) (k out))).run'
    (keygenNamedInstall parts p.1 (base p.2))

/-- The full hidden-key export comparison, including its oracle continuation. Uniform dealer keys
may replace the hidden derived values without changing any accepting-and-no-hit mass. -/
theorem evalDist_keygenHiddenExport (prims : Primitives) (coalition : C.Coalition)
    (parts : C.Party → Parts C) (base : (KeyName C → HashOutput) → HashCache C)
    (hbase : KeygenBaseKnown coalition base) {α : Type}
    (k : (KeyName C → HashOutput) → OracleComp (LocalSpec C) α) :
    𝒟[keygenHiddenExport prims coalition parts base k true] =
      𝒟[keygenHiddenExport prims coalition parts base k false] := by
  let finish := fun p : (KeyName C → HashOutput) × (KeyName C → HashOutput) =>
    (simulateQ (localAnswer prims) (keygenAvoid (KeygenHiddenInput coalition parts) (k p.2))).run'
      (keygenNamedInstall parts p.1 (base p.2))
  have hpoint (p : (KeyName C → HashOutput) × (KeyName C → HashOutput)) :
      (simulateQ (localAnswer prims) (keygenAvoid (KeygenHiddenInput coalition parts)
        (k (keygenHiddenNamedSwap coalition p).2))).run' (keygenNamedInstall parts p.1 (base p.2)) =
      finish (keygenHiddenNamedSwap coalition p) := by
    apply keygenAvoid_run'_eq
    apply keygenNamedInstall_swap_agrees
    have hb : base p.2 = base (keygenHiddenNamedSwap coalition p).2 :=
      hbase _ _ (fun name hn => (keygenHiddenNamedSwap_known coalition p name hn).2.symm)
    intro q _
    rw [hb]
  change 𝒟[($ᵗ ((KeyName C → HashOutput) × (KeyName C → HashOutput))) >>= _] =
    𝒟[($ᵗ ((KeyName C → HashOutput) × (KeyName C → HashOutput))) >>= finish]
  simp only [Bool.true_eq, Bool.false_eq, if_true, if_false]
  conv_lhs => arg 1; arg 2; ext p; rw [hpoint p]
  rw [← bind_map_left, evalDist_bind, evalDist_keygenHiddenNamedSwap coalition, ← evalDist_bind]

/-- The complete continuation, retaining its query log and never stopping early. -/
def keygenHiddenExportLogged (prims : Primitives) (coalition : C.Coalition) (parts : C.Party → Parts C)
    (base : (KeyName C → HashOutput) → HashCache C) {α : Type}
    (k : (KeyName C → HashOutput) → OracleComp (LocalSpec C) α) (useOracle : Bool) :
    ProbComp (α × List (Query C)) := do
  let p ← $ᵗ ((KeyName C → HashOutput) × (KeyName C → HashOutput))
  let out := if useOracle then (keygenHiddenNamedSwap coalition p).2 else p.2
  (simulateQ (localAnswer prims) (keygenHashLog (k out))).run'
    (keygenNamedInstall parts p.1 (base p.2))

theorem probEvent_keygenHiddenExportLogged_good (prims : Primitives) (coalition : C.Coalition)
    (parts : C.Party → Parts C) (base : (KeyName C → HashOutput) → HashCache C)
    {α : Type} (k : (KeyName C → HashOutput) → OracleComp (LocalSpec C) α)
    (useOracle : Bool) (a : α) :
    Pr[fun r => r.1 = a ∧ KeygenGoodLog (KeygenHiddenInput coalition parts) r.2 |
      keygenHiddenExportLogged prims coalition parts base k useOracle] =
    Pr[= some a | keygenHiddenExport prims coalition parts base k useOracle] := by
  unfold keygenHiddenExportLogged keygenHiddenExport
  rw [probEvent_bind_eq_tsum, probOutput_bind_eq_tsum]
  apply tsum_congr
  intro p
  congr 1
  simp only [StateT.run'_eq, probEvent_map, probOutput_map, Function.comp_def]
  exact probEvent_keygenHashLog_good_eq_avoid prims (KeygenHiddenInput coalition parts) _ _ a

/-- Equal accepting-and-not-bad probabilities for the two actual, nonstopping hidden export games. -/
theorem keygenHiddenExport_accept_and_not_bad (prims : Primitives) (coalition : C.Coalition)
    (parts : C.Party → Parts C) (base : (KeyName C → HashOutput) → HashCache C)
    (hbase : KeygenBaseKnown coalition base)
    (k : (KeyName C → HashOutput) → OracleComp (LocalSpec C) Bool) :
    Pr[fun r => r.1 = true ∧ KeygenGoodLog (KeygenHiddenInput coalition parts) r.2 |
      keygenHiddenExportLogged prims coalition parts base k true] =
    Pr[fun r => r.1 = true ∧ KeygenGoodLog (KeygenHiddenInput coalition parts) r.2 |
      keygenHiddenExportLogged prims coalition parts base k false] := by
  rw [probEvent_keygenHiddenExportLogged_good, probEvent_keygenHiddenExportLogged_good]
  simp only [probOutput_def, evalDist_keygenHiddenExport prims coalition parts base hbase k]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The deterministic reveal result under a fixed oracle, with both actual abort tests. -/
def keygenRevealDataFixed (prims : Primitives) (h : Query C → HashOutput) (i : C.Party)
    (own : Parts C) (committed revealed : Mail C E) : Option (KeygenEchoData C) :=
  if C.parties.any (fun j => Msg.isAbort (revealed j)) then none else
    if openCheck .keygen i own committed revealed (D prims h (openQueries .keygen i revealed)) then
      let keys := D prims h (deriveKeys .keygen i (setupView .keygen i own revealed))
      some (keys, D prims h (sharedQueries .keygen i keys))
    else none

theorem simulateQ_fixedLocal_keygenRevealCompute (prims : Primitives) (h : Query C → HashOutput)
    (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    simulateQ (fixedLocal prims h) (keygenRevealCompute i own committed revealed) =
      pure (keygenRevealDataFixed prims h i own committed revealed) := by
  unfold keygenRevealCompute keygenRevealDataFixed
  by_cases ha : (C.parties.any fun j => Msg.isAbort (revealed j)) = true
  · simp only [if_pos ha, simulateQ_pure]
  · simp only [if_neg ha, pure_bind, simulateQ_bind, simulateQ_fixedLocal_liftComp, pure_bind]
    by_cases ho : openCheck .keygen i own committed revealed (D prims h (openQueries .keygen i revealed))
    · simp only [ho, not_true_eq_false, if_false, if_true, pure_bind, simulateQ_bind,
        simulateQ_fixedLocal_liftComp, simulateQ_pure]
    · simp only [ho, not_false_eq_true, if_true, if_false, simulateQ_pure]

def keygenRevealAllFixed (prims : Primitives) (coalition : C.Coalition) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) :
    C.Party → Option (KeygenEchoData C) := fun i =>
  if i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j)) then none else
    keygenRevealDataFixed prims h i (parts i) (committed i) (keygenRevealInbox coalition parts committed sent i)

theorem simulateQ_fixedLocal_keygenRevealComputations (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) :
    simulateQ (fixedLocal prims h) (keygenRevealComputations coalition parts committed sent) =
      pure (keygenRevealAllFixed prims coalition h parts committed sent) := by
  rw [keygenRevealComputations, simulateQ_sequenceFin]
  trans Concrete.sequenceFin (fun i => (pure (keygenRevealAllFixed prims coalition h parts committed sent i) : ProbComp _))
  · congr 1
    funext i
    unfold keygenRevealAllFixed
    split_ifs
    · rfl
    · exact simulateQ_fixedLocal_keygenRevealCompute prims h i (parts i) (committed i) _
  · exact sequenceFin_pure _

/-- Any actual lazy-oracle reveal result is the fixed-oracle result for its final cache. -/
theorem keygenRevealComputations_run_fixed (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E)
    (cache : HashCache C) (r : (C.Party → Option (KeygenEchoData C)) × HashCache C)
    (hr : r ∈ support ((simulateQ (localAnswer prims)
      (keygenRevealComputations coalition parts committed sent)).run cache))
    (hg : Good prims h) (ha : Agrees h r.2) :
    r.1 = keygenRevealAllFixed prims coalition h parts committed sent := by
  have hs := (localRun_support (prims := prims) _ cache r hr).2.2 h hg ha
  rw [simulateQ_fixedLocal_keygenRevealComputations] at hs
  exact hs

/-- A successful echo output supplies the actual inbox checks and its honest key value. -/
theorem keygenEchoDataOutput_some (coalition : C.Coalition) (data : C.Party → Option (KeygenEchoData C))
    (sent : C.Party → Mail C E) (i : C.Party) (key : Keys C)
    (ho : keygenEchoDataOutput coalition data sent i = some key) :
    i ∉ coalition.1 ∧ ∃ keys shared,
      data i = some (keys, shared) ∧ key = keysOf keys ∧
      (C.parties.any fun j => Msg.isAbort (roundInbox coalition sent (fun j => keygenEchoDataStep j (data j)) i j)) = false ∧
      echoCheck .keygen i keys shared (roundInbox coalition sent (fun j => keygenEchoDataStep j (data j)) i) := by
  unfold keygenEchoDataOutput at ho
  cases hd : data i with
  | none => simp only [hd] at ho; contradiction
  | some v =>
    rcases v with ⟨keys, shared⟩
    simp only [hd] at ho
    split_ifs at ho with hi hb hc <;> try contradiction
    refine ⟨hi, keys, shared, rfl, (Option.some.inj ho).symm, ?_, hc⟩
    exact Bool.eq_false_iff.mpr hb

/-- Every honest operator reached its echo step if any honest output survives. -/
theorem keygenEchoDataOutput_all_some (coalition : C.Coalition)
    (data : C.Party → Option (KeygenEchoData C)) (sent : C.Party → Mail C E)
    (i : C.Party) (key : Keys C) (ho : keygenEchoDataOutput coalition data sent i = some key) :
    ∀ j, j ∉ coalition.1 → (data j).isSome := by
  obtain ⟨_, keys, shared, _, _, ha, _⟩ := keygenEchoDataOutput_some coalition data sent i key ho
  intro j hj
  cases hd : data j with
  | some v => rfl
  | none =>
    have hn := List.any_eq_false.mp ha j (List.mem_finRange j)
    simp only [roundInbox, if_neg hj, hd, keygenEchoDataStep, Step.delivered, Msg.isAbort] at hn
    exact (hn trivial).elim

/-- A non-aborting deterministic reveal supplies its actual derived keys and shared hashes. -/
theorem keygenRevealAllFixed_some (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E)
    (i : C.Party) (ha : (keygenRevealAllFixed prims coalition h parts committed sent i).isSome) :
    let revealed := keygenRevealInbox coalition parts committed sent
    let keys := D prims h (deriveKeys .keygen i (setupView .keygen i (parts i) (revealed i)))
    keygenRevealAllFixed prims coalition h parts committed sent i =
      some (keys, D prims h (sharedQueries .keygen i keys)) ∧
    (C.parties.any fun j => Msg.isAbort (revealed i j)) = false := by
  unfold keygenRevealAllFixed keygenRevealDataFixed at ha ⊢
  dsimp only
  split_ifs with hi hr hc <;> simp_all

/-- Outside the stated shared-hash collision event, acceptance gives the honest agreements
required by output identification. -/
theorem keygenRevealAllFixed_output_agreement (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (committed sent echoSent : C.Party → Mail C E)
    (i : C.Party) (key : Keys C)
    (ho : keygenEchoDataOutput coalition (keygenRevealAllFixed prims coalition h parts committed sent) echoSent i = some key)
    (hn : ∀ j, j ∉ coalition.1 →
      let revealed := keygenRevealInbox coalition parts committed sent
      let ki := D prims h (deriveKeys .keygen i (setupView .keygen i (parts i) (revealed i)))
      let kj := D prims h (deriveKeys .keygen j (setupView .keygen j (parts j) (revealed j)))
      h (.sharedKeys .keygen ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys .keygen ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys .keygen ((sharedTerms j i).map kj.2.1)) :
    let revealed := keygenRevealInbox coalition parts committed sent
    let keys := fun j => D prims h (deriveKeys .keygen j (setupView .keygen j (parts j) (revealed j)))
    i ∉ coalition.1 ∧ key = keysOf (keys i) ∧
    (∀ k j, j ∉ coalition.1 → j ≠ k → Msg.hashesOf (revealed k j) = revealTo .keygen (parts j) j k) ∧
    ∀ j, j ∉ coalition.1 → (keys i).1 = (keys j).1 ∧
      ∀ T, i ∈ C.holders T → j ∈ C.holders T → (keys i).2.1 T = (keys j).2.1 T := by
  let data := keygenRevealAllFixed prims coalition h parts committed sent
  let revealed := keygenRevealInbox coalition parts committed sent
  let keys := fun j => D prims h (deriveKeys .keygen j (setupView .keygen j (parts j) (revealed j)))
  have hall := keygenEchoDataOutput_all_some coalition data echoSent i key ho
  obtain ⟨hi, ki, si, hdi, hkey, _, hcheck⟩ := keygenEchoDataOutput_some coalition data echoSent i key ho
  have hdf (j : C.Party) (hj : j ∉ coalition.1) :
      data j = some (keys j, D prims h (sharedQueries .keygen j (keys j))) :=
    (keygenRevealAllFixed_some prims coalition h parts committed sent j (hall j hj)).1
  have he := Option.some.inj (hdi.symm.trans (hdf i hi))
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp he
  refine ⟨hi, hkey, keygenRevealInbox_all_honest coalition parts committed sent i
    (keygenRevealAllFixed_some prims coalition h parts committed sent i (hall i hi)).2, ?_⟩
  intro j hj
  by_cases hji : j = i
  · subst j
    exact ⟨rfl, fun _ _ _ => rfl⟩
  · apply keygen_echoCheck_agreement prims h i j hji (keys i) (keys j) _ _ hcheck (hn j hj)
    simp only [roundInbox, if_neg hj, hdf j hj, keygenEchoDataStep, Step.delivered,
      echoOutbox, if_neg (Ne.symm hji)]

/-- Complete output identification for the concrete reveal and echo execution. The protocol's
successful output supplies honest delivery, derivation and agreement facts automatically. -/
theorem keygenRevealEcho_output_eq_hybrid (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (committed sent echoSent commitSent : C.Party → Mail C E) (log : CallLog C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (high : HashOutput)
    (hextract : ∀ i j, i ∉ coalition.1 → j ∈ coalition.1 →
      extractReveal log commitSent j i = Msg.hashesOf (keygenRevealInbox coalition parts committed sent i j))
    (hparameter : h (keygenParameterProgrammingInput coalition (keygenProgramView coalition parts log commitSent)) =
      keygenFullParameter high parameter)
    (hterm : ∀ T, KnownTo coalition.1 T →
      h (keygenTermProgrammingInput coalition (keygenProgramView coalition parts log commitSent) T) = seeds T)
    (hpair : ∀ p ∈ keygenCrossCoordinates coalition,
      h (keygenPairProgrammingInput coalition (keygenProgramView coalition parts log commitSent) p) = pairs p)
    (i : C.Party) (key : Keys C)
    (ho : keygenEchoDataOutput coalition (keygenRevealAllFixed prims coalition h parts committed sent) echoSent i = some key)
    (hn : ∀ j, j ∉ coalition.1 →
      let revealed := keygenRevealInbox coalition parts committed sent
      let ki := D prims h (deriveKeys .keygen i (setupView .keygen i (parts i) (revealed i)))
      let kj := D prims h (deriveKeys .keygen j (setupView .keygen j (parts j) (revealed j)))
      h (.sharedKeys .keygen ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys .keygen ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys .keygen ((sharedTerms j i).map kj.2.1)) :
    key = dealtKeys parameter (keygenHybridSeeds coalition h parts seeds)
      (keygenHybridPairs coalition h parts pairs) i := by
  obtain ⟨hi, hkey, hreceived, hagree⟩ :=
    keygenRevealAllFixed_output_agreement prims coalition h parts committed sent echoSent i key ho hn
  rw [hkey]
  exact keygen_output_eq_hybrid_dealing prims coalition parts log commitSent _ h parameter seeds pairs high
    (fun j => D prims h (deriveKeys .keygen j
      (setupView .keygen j (parts j) (keygenRevealInbox coalition parts committed sent j))))
    hreceived hextract (fun _ _ => rfl) hparameter hterm hpair i hi hagree

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- A transcript whose queries are unchanged by any shift of a hidden private coordinate. -/
def KeygenPrivateInvariant {α : Type} (coalition : C.Coalition) (f : (C.Party → Parts C) → α) : Prop :=
  (∀ a T, ¬ KnownTo coalition.1 T → ∀ c parts,
    f (shiftAt a (some T) none c parts) = f parts) ∧
  (∀ p : C.Pair, p.1.1 ∉ coalition.1 → p.1.2 ∉ coalition.1 → ∀ c parts,
    f (shiftAt p.1.1 none (some p.1.2) c parts) = f parts)

def keygenDeriveHead : Query C → HashOutput
  | .derive _ _ values => values.headD 0
  | _ => 0

/-- Guessing a canonical hidden term input costs one uniform 256-bit private coordinate,
even when the proposed input depends on all the other private coordinates. -/
theorem probEvent_keygenHiddenTerm_guess (coalition : C.Coalition)
    (target : (C.Party → Parts C) → Query C) (hinv : KeygenPrivateInvariant coalition target)
    (T : C.Term) (hh : ¬ KnownTo coalition.1 T) :
    Pr[fun parts => termInput .keygen parts T = target parts |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  obtain ⟨a, rest, ha⟩ := exists_first_holder T
  calc
    _ ≤ Pr[fun parts => (parts a).term T = keygenDeriveHead (target parts) |
        Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
      apply probEvent_mono
      intro parts _ he
      rw [← he]
      simp [termInput, ha, keygenDeriveHead]
    _ = _ := probEvent_parts_collision (fun parts => (parts a).term T)
      (fun parts => keygenDeriveHead (target parts)) a (some T) none
      (fun c parts => by simp [shiftAt, shiftParts])
      (fun c parts => by rw [hinv.1 a T hh c parts])

/-- The same bound for a hidden honest--honest pair uses the first endpoint's private part. -/
theorem probEvent_keygenHiddenPair_guess (coalition : C.Coalition)
    (target : (C.Party → Parts C) → Query C) (hinv : KeygenPrivateInvariant coalition target)
    (p : C.Pair) (hp : p.1.1 ∉ coalition.1 ∧ p.1.2 ∉ coalition.1) :
    Pr[fun parts => pairInput .keygen parts p = target parts |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  calc
    _ ≤ Pr[fun parts => (parts p.1.1).pair p.1.2 = keygenDeriveHead (target parts) |
        Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by
      apply probEvent_mono
      intro parts _ he
      rw [← he]
      simp [pairInput, keygenDeriveHead]
    _ = _ := probEvent_parts_collision (fun parts => (parts p.1.1).pair p.1.2)
      (fun parts => keygenDeriveHead (target parts)) p.1.1 none (some p.1.2)
      (fun c parts => by simp [shiftAt, shiftParts])
      (fun c parts => by rw [hinv.2 p hp.1 hp.2 c parts])

/-- Union bound for one private-invariant query at any hidden raw derivation input. -/
theorem probEvent_keygenHiddenInput_guess (coalition : C.Coalition)
    (target : (C.Party → Parts C) → Query C) (hinv : KeygenPrivateInvariant coalition target) :
    Pr[fun parts => KeygenHiddenInput coalition parts (target parts) |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      ((Fintype.card C.Term + Fintype.card C.Pair : ℕ) : ℝ≥0∞) *
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have hm : ∀ parts, KeygenHiddenInput coalition parts (target parts) →
      (∃ T ∈ (Finset.univ : Finset C.Term), ¬ KnownTo coalition.1 T ∧ termInput .keygen parts T = target parts) ∨
      (∃ p ∈ (Finset.univ : Finset C.Pair), p.1.1 ∉ coalition.1 ∧ p.1.2 ∉ coalition.1 ∧
        pairInput .keygen parts p = target parts) := by
    rintro parts ⟨name, hn, he⟩
    cases name with
    | parameter => exact hn.elim
    | term T => exact Or.inl ⟨T, Finset.mem_univ _, hn, he⟩
    | pair p => exact Or.inr ⟨p, Finset.mem_univ _, hn.1, hn.2, he⟩
  refine (probEvent_mono (fun parts _ => hm parts)).trans ((probEvent_or_le _ _ _).trans ?_)
  have ht : ∀ T : C.Term,
      Pr[fun parts => ¬ KnownTo coalition.1 T ∧ termInput .keygen parts T = target parts |
        Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    intro T
    by_cases hh : ¬ KnownTo coalition.1 T
    · simpa only [hh, not_false_eq_true, true_and] using probEvent_keygenHiddenTerm_guess coalition target hinv T hh
    · simp [hh]
  have hp : ∀ p : C.Pair,
      Pr[fun parts => p.1.1 ∉ coalition.1 ∧ p.1.2 ∉ coalition.1 ∧ pairInput .keygen parts p = target parts |
        Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    intro p
    by_cases hh : p.1.1 ∉ coalition.1 ∧ p.1.2 ∉ coalition.1
    · simpa only [hh.1, hh.2, not_false_eq_true, true_and] using probEvent_keygenHiddenPair_guess coalition target hinv p hh
    · have he : ∀ parts, ¬ (p.1.1 ∉ coalition.1 ∧ p.1.2 ∉ coalition.1 ∧ pairInput .keygen parts p = target parts) :=
        fun _ h => hh ⟨h.1, h.2.1⟩
      simp only [he, probEvent_False, zero_le]
  calc
    _ ≤ (∑ T : C.Term, (Fintype.card HashOutput : ℝ≥0∞)⁻¹) +
        (∑ p : C.Pair, (Fintype.card HashOutput : ℝ≥0∞)⁻¹) :=
      add_le_add ((probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun T _ => ht T))
        ((probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun p _ => hp p))
    _ = _ := by simp [add_mul]

/-- All proposed queries may depend on the other coordinates; only invariance of hidden
coordinates is required. This is the guessing bound consumed after the trace normalization. -/
theorem probEvent_keygenHiddenInput_queries (coalition : C.Coalition) (m : ℕ)
    (queries : (C.Party → Parts C) → Fin m → Query C) (hinv : KeygenPrivateInvariant coalition queries) :
    Pr[fun parts => ∃ i : Fin m, KeygenHiddenInput coalition parts (queries parts i) |
      Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] ≤
      ((m * keygenSecrets C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have hi (i : Fin m) : KeygenPrivateInvariant coalition (fun parts => queries parts i) := by
    constructor
    · intro a T hh c parts
      exact congrFun (hinv.1 a T hh c parts) i
    · intro p ha hb c parts
      exact congrFun (hinv.2 p ha hb c parts) i
  have hc : Fintype.card C.Term + Fintype.card C.Pair ≤ keygenSecrets C := by
    have hp := card_pair_le C
    rw [card_term]
    unfold keygenSecrets termCount
    omega
  calc _ = Pr[fun parts => ∃ i ∈ (Finset.univ : Finset (Fin m)),
        KeygenHiddenInput coalition parts (queries parts i) |
        Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := by simp
    _ ≤ ∑ i : Fin m, Pr[fun parts => KeygenHiddenInput coalition parts (queries parts i) |
        Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))] := probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _i : Fin m, ((Fintype.card C.Term + Fintype.card C.Pair : ℕ) : ℝ≥0∞) *
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ :=
      Finset.sum_le_sum fun i _ => probEvent_keygenHiddenInput_guess coalition _ (hi i)
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      rw [← mul_assoc]
      apply mul_le_mul_right'
      apply mul_le_mul_left'
      exact_mod_cast hc

/-- Hidden term coordinates never occur in an honest reveal addressed to a corrupt operator. -/
theorem keygen_reveal_hiddenTerm_shift (coalition : C.Coalition) (T : C.Term)
    (hh : ¬ KnownTo coalition.1 T) (a i j : C.Party) (hj : j ∈ coalition.1)
    (c : HashOutput) (parts : C.Party → Parts C) :
    revealTo .keygen (shiftAt a (some T) none c parts i) i j = revealTo .keygen (parts i) i j := by
  by_cases hi : i = a
  · subst i
    simp only [shiftAt, if_pos rfl, revealTo, shiftParts]
    congr 2
    apply List.map_congr_left
    intro U hU
    have hne : T ≠ U := fun he => hh (he ▸ keygen_sharedTerms_known coalition a j hj U hU)
    simp [hne]
  · simp [shiftAt, hi]

/-- Hidden honest--honest pair parts likewise never occur in a corrupt-facing reveal. -/
theorem keygen_reveal_hiddenPair_shift (coalition : C.Coalition) (p : C.Pair)
    (hp : p.1.1 ∉ coalition.1 ∧ p.1.2 ∉ coalition.1) (i j : C.Party) (hj : j ∈ coalition.1)
    (c : HashOutput) (parts : C.Party → Parts C) :
    revealTo .keygen (shiftAt p.1.1 none (some p.1.2) c parts i) i j = revealTo .keygen (parts i) i j := by
  have hne : p.1.2 ≠ j := fun he => hp.2 (he ▸ hj)
  by_cases hi : i = p.1.1
  · subst i
    simp [shiftAt, shiftParts, revealTo, hne]
  · simp [shiftAt, hi]

/-- Sample the private parts and then an arbitrary randomized transcript. -/
def keygenPartsKernel {α : Type} (K : (C.Party → Parts C) → ProbComp α) :
    ProbComp ((C.Party → Parts C) × α) := do
  let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
  let out ← K parts
  pure (parts, out)

/-- Private-coordinate shifts preserve the complete joint law of the parts and invariant transcript. -/
theorem evalDist_keygenPartsKernel_shift {α : Type} (K : (C.Party → Parts C) → ProbComp α)
    (a : C.Party) (term : Option C.Term) (pair : Option C.Party) (c : HashOutput)
    (hK : ∀ parts, K (shiftAt a term pair c parts) = K parts) :
    𝒟[(fun p => (shiftAt a term pair c p.1, p.2)) <$> keygenPartsKernel K] = 𝒟[keygenPartsKernel K] := by
  have he : (fun p => (shiftAt a term pair c p.1, p.2)) <$> keygenPartsKernel K =
      (do let parts ← shiftAt a term pair c <$> Concrete.sequenceFin (fun _ : C.Party => sampleParts (C := C))
          let out ← K parts
          pure (parts, out)) := by
    simp only [keygenPartsKernel, map_bind, map_pure, bind_map_left, hK]
  rw [he, evalDist_bind, evalDist_shiftAt, ← evalDist_bind]
  rfl

/-- A transcript that is invariant under one hidden coordinate has exactly the uniform guessing
probability at that coordinate. This includes arbitrarily adaptive randomized computations. -/
theorem probEvent_keygenPartsKernel_coordinate {α : Type}
    (K : (C.Party → Parts C) → ProbComp α) (X : (C.Party → Parts C) → HashOutput)
    (Y : α → HashOutput) (a : C.Party) (term : Option C.Term) (pair : Option C.Party)
    (hX : ∀ c parts, X (shiftAt a term pair c parts) = X parts ^^^ c)
    (hK : ∀ c parts, K (shiftAt a term pair c parts) = K parts) :
    Pr[fun p => X p.1 = Y p.2 | keygenPartsKernel K] = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have huniform : 𝒟[(fun p => X p.1 ^^^ Y p.2) <$> keygenPartsKernel K] = 𝒟[$ᵗ HashOutput] := by
    apply evalDist_eq_uniform_of_probOutput_eq
    intro u v
    have hshift : 𝒟[(fun p => X p.1 ^^^ Y p.2) <$> keygenPartsKernel K] =
        𝒟[(fun d => d ^^^ (u ^^^ v)) <$> ((fun p => X p.1 ^^^ Y p.2) <$> keygenPartsKernel K)] := by
      calc
        _ = 𝒟[(fun p => X p.1 ^^^ Y p.2) <$>
          ((fun p => (shiftAt a term pair (u ^^^ v) p.1, p.2)) <$> keygenPartsKernel K)] := by
            rw [evalDist_map, evalDist_map, evalDist_keygenPartsKernel_shift K a term pair (u ^^^ v) (hK _)]
        _ = _ := by
          rw [Functor.map_map, Functor.map_map]
          congr 2
          funext p
          simp only [hX, BitVec.xor_assoc, BitVec.xor_comm (u ^^^ v) (Y p.2)]
    have hu : u = v ^^^ (u ^^^ v) := by
      rw [BitVec.xor_comm u v, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    have he := probOutput_map_injective ((fun p => X p.1 ^^^ Y p.2) <$> keygenPartsKernel K)
      (xor_bijective (u ^^^ v)).1 v
    rw [← hu] at he
    rw [probOutput_def, hshift, ← probOutput_def]
    exact he
  have he : Pr[fun p => X p.1 = Y p.2 | keygenPartsKernel K] =
      Pr[= 0 | (fun p => X p.1 ^^^ Y p.2) <$> keygenPartsKernel K] := by
    rw [probOutput_map]
    exact probEvent_ext fun _ _ => BitVec.xor_eq_zero_iff.symm
  rw [he, probOutput_def, huniform, ← probOutput_def, probOutput_uniformSample]

/-- The one-point bound for a transcript sampled adaptively, rather than a fixed proposed query. -/
theorem probEvent_keygenHiddenInput_kernel_one {α : Type} (coalition : C.Coalition)
    (K : (C.Party → Parts C) → ProbComp α) (hinv : KeygenPrivateInvariant coalition K)
    (target : α → Query C) :
    Pr[fun p => KeygenHiddenInput coalition p.1 (target p.2) | keygenPartsKernel K] ≤
      ((Fintype.card C.Term + Fintype.card C.Pair : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have ht (T : C.Term) :
      Pr[fun p => ¬ KnownTo coalition.1 T ∧ termInput .keygen p.1 T = target p.2 | keygenPartsKernel K] ≤
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    by_cases hh : ¬ KnownTo coalition.1 T
    · obtain ⟨a, rest, ha⟩ := exists_first_holder T
      calc
        _ ≤ Pr[fun p => (p.1 a).term T = keygenDeriveHead (target p.2) | keygenPartsKernel K] := by
          apply probEvent_mono
          intro p _ hp
          rw [← hp.2]
          simp [termInput, ha, keygenDeriveHead]
        _ = _ := probEvent_keygenPartsKernel_coordinate K (fun parts => (parts a).term T)
          (fun r => keygenDeriveHead (target r)) a (some T) none
          (fun c parts => by simp [shiftAt, shiftParts]) (hinv.1 a T hh)
    · simp [hh]
  have hp (pair : C.Pair) :
      Pr[fun p => pair.1.1 ∉ coalition.1 ∧ pair.1.2 ∉ coalition.1 ∧
        pairInput .keygen p.1 pair = target p.2 | keygenPartsKernel K] ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    by_cases hh : pair.1.1 ∉ coalition.1 ∧ pair.1.2 ∉ coalition.1
    · calc
        _ ≤ Pr[fun p => (p.1 pair.1.1).pair pair.1.2 = keygenDeriveHead (target p.2) | keygenPartsKernel K] := by
          apply probEvent_mono
          intro p _ hp
          rw [← hp.2.2]
          simp [pairInput, keygenDeriveHead]
        _ = _ := probEvent_keygenPartsKernel_coordinate K (fun parts => (parts pair.1.1).pair pair.1.2)
          (fun r => keygenDeriveHead (target r)) pair.1.1 none (some pair.1.2)
          (fun c parts => by simp [shiftAt, shiftParts]) (hinv.2 pair hh.1 hh.2)
    · have he : ∀ p : (C.Party → Parts C) × α, ¬ (pair.1.1 ∉ coalition.1 ∧ pair.1.2 ∉ coalition.1 ∧ pairInput .keygen p.1 pair = target p.2) :=
        fun _ h => hh ⟨h.1, h.2.1⟩
      simp only [he, probEvent_False, zero_le]
  have hm : ∀ p : (C.Party → Parts C) × α, KeygenHiddenInput coalition p.1 (target p.2) →
      (∃ T ∈ (Finset.univ : Finset C.Term), ¬ KnownTo coalition.1 T ∧ termInput .keygen p.1 T = target p.2) ∨
      (∃ pair ∈ (Finset.univ : Finset C.Pair), pair.1.1 ∉ coalition.1 ∧ pair.1.2 ∉ coalition.1 ∧
        pairInput .keygen p.1 pair = target p.2) := by
    rintro p ⟨name, hn, he⟩
    cases name with
    | parameter => exact hn.elim
    | term T => exact Or.inl ⟨T, Finset.mem_univ _, hn, he⟩
    | pair pair => exact Or.inr ⟨pair, Finset.mem_univ _, hn.1, hn.2, he⟩
  refine (probEvent_mono (fun p _ => hm p)).trans ((probEvent_or_le _ _ _).trans ?_)
  calc
    _ ≤ (∑ _T : C.Term, (Fintype.card HashOutput : ℝ≥0∞)⁻¹) +
        (∑ _p : C.Pair, (Fintype.card HashOutput : ℝ≥0∞)⁻¹) :=
      add_le_add ((probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun T _ => ht T))
        ((probEvent_exists_finset_le_sum _ _ _).trans (Finset.sum_le_sum fun p _ => hp p))
    _ = _ := by simp [add_mul]

/-- The complete guessing bound for an adaptive randomized private-invariant transcript. -/
theorem probEvent_keygenHiddenInput_kernel (coalition : C.Coalition) (m : ℕ)
    (K : (C.Party → Parts C) → ProbComp (Fin m → Query C)) (hinv : KeygenPrivateInvariant coalition K) :
    Pr[fun p => ∃ i : Fin m, KeygenHiddenInput coalition p.1 (p.2 i) | keygenPartsKernel K] ≤
      ((m * keygenSecrets C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have hc : Fintype.card C.Term + Fintype.card C.Pair ≤ keygenSecrets C := by
    have hp := card_pair_le C
    rw [card_term]
    unfold keygenSecrets termCount
    omega
  calc
    _ = Pr[fun p => ∃ i ∈ (Finset.univ : Finset (Fin m)), KeygenHiddenInput coalition p.1 (p.2 i) |
        keygenPartsKernel K] := by simp
    _ ≤ ∑ i : Fin m, Pr[fun p => KeygenHiddenInput coalition p.1 (p.2 i) | keygenPartsKernel K] :=
      probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _i : Fin m, ((Fintype.card C.Term + Fintype.card C.Pair : ℕ) : ℝ≥0∞) *
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ :=
      Finset.sum_le_sum fun i _ => probEvent_keygenHiddenInput_kernel_one coalition K hinv (fun r => r i)
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      rw [← mul_assoc]
      apply mul_le_mul_right'
      apply mul_le_mul_left'
      exact_mod_cast hc

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

abbrev KeygenFiniteSpec (Ω : Type) := unifSpec + ((Ω →ₒ HashOutput) + ((Ω × HashOutput) →ₒ Bool))
abbrev KeygenFiniteCache (Ω : Type) := (Ω →ₒ HashOutput).QueryCache

def keygenFiniteProgram {Ω : Type} [DecidableEq Ω] (x : Ω × HashOutput) :
    StateT (KeygenFiniteCache Ω) ProbComp Bool := fun cache =>
  if (cache x.1).isSome then pure (false, cache)
  else pure (true, cache.cacheQuery x.1 x.2)

def keygenFiniteEager {Ω : Type} [DecidableEq Ω] (h : Ω → HashOutput) :
    QueryImpl (KeygenFiniteSpec Ω) (StateT (KeygenFiniteCache Ω) ProbComp) :=
  unifFwdImpl (Ω →ₒ HashOutput) + ((QueryImpl.withCaching (fun q => pure (h q) : QueryImpl (Ω →ₒ HashOutput) ProbComp)) + keygenFiniteProgram (Ω := Ω))

def keygenFiniteLazy {Ω : Type} [DecidableEq Ω] :
    QueryImpl (KeygenFiniteSpec Ω) (StateT (KeygenFiniteCache Ω) ProbComp) :=
  unifFwdImpl (Ω →ₒ HashOutput) + ((Ω →ₒ HashOutput).randomOracle + keygenFiniteProgram (Ω := Ω))

/-- Once a cell is cached, its unused eager-table value cannot affect any future computation,
including an adaptive programming attempt. -/
theorem keygenFiniteEager_congr {Ω α : Type} [DecidableEq Ω]
    (oa : OracleComp (KeygenFiniteSpec Ω) α) (h g : Ω → HashOutput) :
    ∀ cache : KeygenFiniteCache Ω, (∀ q, cache q = none → h q = g q) →
      (simulateQ (keygenFiniteEager h) oa).run cache =
        (simulateQ (keygenFiniteEager g) oa).run cache := by
  induction oa using OracleComp.inductionOn with
  | pure a => intros; rfl
  | query_bind t k ih =>
    intro cache he
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with n | q | x
    · change (((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        fun p : unifSpec.Range n × KeygenFiniteCache Ω => (simulateQ (keygenFiniteEager h) (k p.1)).run p.2) =
        (((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        fun p : unifSpec.Range n × KeygenFiniteCache Ω => (simulateQ (keygenFiniteEager g) (k p.1)).run p.2)
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
    · change keygenFiniteProgram x cache >>= _ = keygenFiniteProgram x cache >>= _
      unfold keygenFiniteProgram
      split_ifs
      · simp only [pure_bind]; exact ih false cache he
      · simp only [pure_bind]
        apply ih
        intro q' hq'
        by_cases hn : q' = x.1
        · subst q'; simp at hq'
        · exact he q' (by simpa [QueryCache.cacheQuery, hn] using hq')

/-- Marginalization remains valid for a randomized continuation, not just a deterministic map. -/
theorem keygenUniform_update_bind {Ω α : Type} [Finite Ω] [DecidableEq Ω]
    [SampleableType (Ω → HashOutput)] (q : Ω) (k : (Ω → HashOutput) → ProbComp α) :
    𝒟[do let y ← $ᵗ HashOutput; let h ← $ᵗ (Ω → HashOutput); k (Function.update h q y)] =
      𝒟[do let h ← $ᵗ (Ω → HashOutput); k h] := by
  have he := evalDist_uniformSample_bind_update (R := HashOutput) q
  have hb : 𝒟[(do let y ← $ᵗ HashOutput; let h ← $ᵗ (Ω → HashOutput); pure (Function.update h q y)) >>= k] =
      𝒟[($ᵗ (Ω → HashOutput)) >>= k] := by
    rw [evalDist_bind, he, ← evalDist_bind]
  simpa only [bind_assoc, pure_bind] using hb

/-- The eager and lazy programmable worlds have exactly the same joint result/cache law.
The occupancy cache is kept separately, so eager sampling does not make programming fail. -/
theorem evalDist_keygenFiniteEager {Ω α : Type} [Finite Ω] [DecidableEq Ω]
    [SampleableType (Ω → HashOutput)] (oa : OracleComp (KeygenFiniteSpec Ω) α) :
    ∀ cache : KeygenFiniteCache Ω,
      𝒟[(simulateQ keygenFiniteLazy oa).run cache] =
        𝒟[do let h ← $ᵗ (Ω → HashOutput); (simulateQ (keygenFiniteEager h) oa).run cache] := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro cache; apply evalDist_ext; intro x; simp
  | query_bind t k ih =>
    intro cache
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with n | q | x
    · change 𝒟[((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        fun p : unifSpec.Range n × KeygenFiniteCache Ω => (simulateQ keygenFiniteLazy (k p.1)).run p.2] =
        𝒟[do let h ← $ᵗ (Ω → HashOutput);
              ((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
                fun p : unifSpec.Range n × KeygenFiniteCache Ω => (simulateQ (keygenFiniteEager h) (k p.1)).run p.2]
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
        change 𝒟[($ᵗ HashOutput) >>= fun y => (simulateQ keygenFiniteLazy (k y)).run (cache.cacheQuery q y)] = _
        conv_lhs => rw [evalDist_bind]; arg 2; ext y; rw [ih y (cache.cacheQuery q y)]
        rw [← evalDist_bind]
        let cont := fun h : Ω → HashOutput =>
          (simulateQ (keygenFiniteEager h) (k (h q))).run (cache.cacheQuery q (h q))
        have he (y : HashOutput) (h : Ω → HashOutput) :
            (simulateQ (keygenFiniteEager h) (k y)).run (cache.cacheQuery q y) =
              cont (Function.update h q y) := by
          dsimp only [cont]
          rw [Function.update_self]
          apply keygenFiniteEager_congr
          intro q' hq'
          by_cases hn : q' = q
          · subst q'; simp at hq'
          · simp [Function.update_of_ne hn]
        simp_rw [he, Function.update_eq_self]
        exact keygenUniform_update_bind q cont
    · change 𝒟[keygenFiniteProgram x cache >>= _] =
        𝒟[do let h ← $ᵗ (Ω → HashOutput); keygenFiniteProgram x cache >>= _]
      unfold keygenFiniteProgram
      split_ifs
      · simp only [pure_bind]; exact ih false cache
      · simp only [pure_bind]; exact ih true (cache.cacheQuery x.1 x.2)

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- Every underlying hash input, including a PRG's hash and a programming attempt. -/
def keygenWorldHashInputs : (WorldSpec C).Domain → Finset (Query C)
  | .inl (.inl t) => (keygenLocalHashInputs t).toFinset
  | .inl (.inr x) => {x.1}
  | .inr t => (keygenLocalHashInputs t).toFinset

/-- Syntactic coverage of every possible branch by a finite hash-input domain. -/
inductive KeygenWorldCovered (S : Finset (Query C)) {α : Type} : OracleComp (WorldSpec C) α → Prop
  | pure (a : α) : KeygenWorldCovered S (pure a)
  | query_bind (t : (WorldSpec C).Domain) (k : (WorldSpec C).Range t → OracleComp (WorldSpec C) α)
      (ht : keygenWorldHashInputs t ⊆ S) (hk : ∀ y, KeygenWorldCovered S (k y)) :
      KeygenWorldCovered S (OracleComp.lift (OracleSpec.query t) >>= k)

theorem KeygenWorldCovered.mono {S T : Finset (Query C)} {α : Type}
    {oa : OracleComp (WorldSpec C) α} (h : KeygenWorldCovered S oa) (hst : S ⊆ T) :
    KeygenWorldCovered T oa := by
  induction h with
  | pure a => exact .pure a
  | query_bind t k ht hk ih => exact .query_bind t k (ht.trans hst) ih

/-- Finite answer ranges give a finite envelope even for an arbitrarily adaptive world program. -/
theorem keygenWorldCovered_exists {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∃ S : Finset (Query C), KeygenWorldCovered S oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact ⟨∅, .pure a⟩
  | query_bind t k ih =>
    have hi : Finite ((WorldSpec C).Range t) := by
      rcases t with (n | q | x) | x | (n | q | x) <;> infer_instance
    letI := Fintype.ofFinite ((WorldSpec C).Range t)
    choose S hS using ih
    refine ⟨keygenWorldHashInputs t ∪ Finset.univ.biUnion S, .query_bind t k ?_ ?_⟩
    · exact Finset.subset_union_left
    · intro y
      apply (hS y).mono
      intro q hq
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ _, hq⟩)

def keygenRestrictCache (S : Finset (Query C)) (cache : HashCache C) : KeygenFiniteCache S :=
  fun q => cache q.1

theorem keygenRestrictCache_update (S : Finset (Query C)) (cache : HashCache C)
    (q : Query C) (hq : q ∈ S) (y : HashOutput) :
    keygenRestrictCache S (cache.cacheQuery q y) =
      (keygenRestrictCache S cache).cacheQuery ⟨q, hq⟩ y := by
  funext q'
  by_cases he : q'.1 = q
  · have he' : q' = ⟨q, hq⟩ := Subtype.ext he
    subst q'
    simp [keygenRestrictCache]
  · have he' : q' ≠ ⟨q, hq⟩ := fun h => he (congrArg Subtype.val h)
    simp [keygenRestrictCache, QueryCache.cacheQuery, he, he']

/-- Translation to a finite domain keeps fixed `Th` calls deterministic. -/
def keygenFiniteHash (prims : Primitives) (S : Finset (Query C)) (q : Query C) :
    OracleComp (KeygenFiniteSpec S) HashOutput :=
  match q with
  | .hash input => if MpcInput input then pure (prims.Th input) else
      if hq : q ∈ S then OracleComp.lift ((KeygenFiniteSpec S).query (.inr (.inl ⟨q, hq⟩))) else pure 0
  | _ => if hq : q ∈ S then OracleComp.lift ((KeygenFiniteSpec S).query (.inr (.inl ⟨q, hq⟩))) else pure 0

def keygenFiniteLocal (prims : Primitives) (S : Finset (Query C)) :
    QueryImpl (LocalSpec C) (OracleComp (KeygenFiniteSpec S)) :=
  (fun n : ℕ => OracleComp.lift ((KeygenFiniteSpec S).query (.inl n)) : QueryImpl unifSpec (OracleComp (KeygenFiniteSpec S))) +
    (keygenFiniteHash prims S + fun x : PrgInput C => do
      let y ← keygenFiniteHash prims S (.streamKey x.2.1)
      pure (prims.aes.eval (truncateHash y) x.2.2))

def keygenFiniteProgramming (S : Finset (Query C)) (x : Query C × HashOutput) :
    OracleComp (KeygenFiniteSpec S) Bool :=
  if IsFixed x.1 then pure false else
    if hx : x.1 ∈ S then OracleComp.lift ((KeygenFiniteSpec S).query (.inr (.inr (⟨x.1, hx⟩, x.2)))) else pure false

def keygenFiniteWorld (prims : Primitives) (S : Finset (Query C)) :
    QueryImpl (WorldSpec C) (OracleComp (KeygenFiniteSpec S)) :=
  keygenFiniteLocal prims S + keygenFiniteProgramming S + keygenFiniteLocal prims S

/-- A hash call's exact joint answer/cache law survives restriction to its finite domain. -/
theorem keygenFiniteHash_run (prims : Primitives) (S : Finset (Query C))
    (q : Query C) (hq : q ∈ S) (cache : HashCache C) :
    (fun r : HashOutput × HashCache C => (r.1, keygenRestrictCache S r.2)) <$>
        (hashAnswer prims q).run cache =
      (simulateQ keygenFiniteLazy (keygenFiniteHash prims S q)).run (keygenRestrictCache S cache) := by
  by_cases hf : IsFixed q
  · obtain ⟨input, rfl, hi⟩ := hf
    rw [hashAnswer_of_isFixed prims hi]
    simp [keygenFiniteHash, hi, keygenRestrictCache]
  · have ht : keygenFiniteHash prims S q = OracleComp.lift ((KeygenFiniteSpec S).query (.inr (.inl ⟨q, hq⟩))) := by
      cases q <;> simp_all [keygenFiniteHash, IsFixed]
    rw [ht, hashAnswer_of_not_isFixed prims hf]
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
theorem keygenFiniteLocal_run (prims : Primitives) (S : Finset (Query C))
    (t : (LocalSpec C).Domain) (ht : ∀ q ∈ keygenLocalHashInputs t, q ∈ S) (cache : HashCache C) :
    (fun r : (LocalSpec C).Range t × HashCache C => (r.1, keygenRestrictCache S r.2)) <$>
        (localAnswer prims t).run cache =
      (simulateQ keygenFiniteLazy (keygenFiniteLocal prims S t)).run (keygenRestrictCache S cache) := by
  rcases t with n | q | x
  · change _ <$> (fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _) = _
    simp only [Functor.map_map]
    rfl
  · exact keygenFiniteHash_run prims S q (ht q (by simp [keygenLocalHashInputs])) cache
  · change _ <$> (prgAnswer prims x).run cache =
      (simulateQ keygenFiniteLazy (keygenFiniteHash prims S (.streamKey x.2.1) >>=
        fun y => pure (prims.aes.eval (truncateHash y) x.2.2))).run _
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, map_bind, map_pure,
      simulateQ_bind, simulateQ_pure]
    rw [← keygenFiniteHash_run prims S (.streamKey x.2.1)
      (ht _ (by simp [keygenLocalHashInputs])) cache, bind_map_left]
    rfl

/-- Fresh-only programming, including its returned success bit, is preserved. -/
theorem keygenFiniteProgramming_run (S : Finset (Query C))
    (x : Query C × HashOutput) (hx : x.1 ∈ S) (cache : HashCache C) :
    (fun r : Bool × HashCache C => (r.1, keygenRestrictCache S r.2)) <$>
        (programAnswer x).run cache =
      (simulateQ keygenFiniteLazy (keygenFiniteProgramming S x)).run (keygenRestrictCache S cache) := by
  rw [programAnswer_run_cache]
  unfold keygenFiniteProgramming programCache
  by_cases hf : IsFixed x.1
  · simp [hf]
  · simp only [hf, false_or, if_false, dif_pos hx]
    erw [simulateQ_spec_query]
    change _ = keygenFiniteProgram (⟨x.1, hx⟩, x.2) (keygenRestrictCache S cache)
    unfold keygenFiniteProgram
    by_cases hc : (cache x.1).isSome
    · simp [keygenRestrictCache, hc]
    · simp [keygenRestrictCache, hc, keygenRestrictCache_update S cache x.1 hx]

/-- Both oracle copies and programming use the same restricted cache. -/
theorem keygenFiniteWorld_run (prims : Primitives) (S : Finset (Query C))
    (t : (WorldSpec C).Domain) (ht : keygenWorldHashInputs t ⊆ S) (cache : HashCache C) :
    (fun r : (WorldSpec C).Range t × HashCache C => (r.1, keygenRestrictCache S r.2)) <$>
        (worldAnswer prims t).run cache =
      (simulateQ keygenFiniteLazy (keygenFiniteWorld prims S t)).run (keygenRestrictCache S cache) := by
  rcases t with t | t
  · rcases t with t | x
    · exact keygenFiniteLocal_run prims S t (fun q hq => ht (by simpa [keygenWorldHashInputs] using hq)) cache
    · exact keygenFiniteProgramming_run S x (ht (by simp [keygenWorldHashInputs])) cache
  · exact keygenFiniteLocal_run prims S t (fun q hq => ht (by simpa [keygenWorldHashInputs] using hq)) cache

/-- The finite translation preserves complete executions, not just individual oracle calls. -/
theorem keygenFiniteWorld_simulate_run (prims : Primitives) (S : Finset (Query C))
    {α : Type} (oa : OracleComp (WorldSpec C) α) (hc : KeygenWorldCovered S oa) :
    ∀ cache : HashCache C,
      (fun r : α × HashCache C => (r.1, keygenRestrictCache S r.2)) <$>
          (simulateQ (worldAnswer prims) oa).run cache =
        (simulateQ keygenFiniteLazy (simulateQ (keygenFiniteWorld prims S) oa)).run
          (keygenRestrictCache S cache) := by
  induction hc with
  | pure a => intro cache; rfl
  | query_bind t k ht hk ih =>
    intro cache
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← keygenFiniteWorld_run prims S t ht cache, bind_map_left]
    exact bind_congr fun p => ih p.1 p.2

/-- Full lazy-to-eager conversion for a programmable world, from every initial cache. -/
theorem evalDist_keygenWorld_eager (prims : Primitives) (S : Finset (Query C))
    {α : Type} (oa : OracleComp (WorldSpec C) α) (hc : KeygenWorldCovered S oa)
    (cache : HashCache C) :
    𝒟[(simulateQ (worldAnswer prims) oa).run' cache] =
      𝒟[do let h ← $ᵗ (S → HashOutput);
            (simulateQ (keygenFiniteEager h) (simulateQ (keygenFiniteWorld prims S) oa)).run'
              (keygenRestrictCache S cache)] := by
  have he := congrArg (Functor.map Prod.fst) (keygenFiniteWorld_simulate_run prims S oa hc cache)
  simp only [Functor.map_map] at he
  change (simulateQ (worldAnswer prims) oa).run' cache =
    (simulateQ keygenFiniteLazy (simulateQ (keygenFiniteWorld prims S) oa)).run'
      (keygenRestrictCache S cache) at he
  rw [he, StateT.run'_eq, evalDist_map, evalDist_keygenFiniteEager]
  simp only [StateT.run'_eq]
  rw [← evalDist_map, map_bind]

/-- Every complete world program has a finite eager representation. This applies without any
query-budget or freshness hypothesis to the real and ideal keygen experiments alike. -/
theorem keygenWorld_eager_exists (prims : Primitives) {α : Type}
    (oa : OracleComp (WorldSpec C) α) :
    ∃ S : Finset (Query C), ∀ cache : HashCache C,
      𝒟[(simulateQ (worldAnswer prims) oa).run' cache] =
        𝒟[do let h ← $ᵗ (S → HashOutput);
              (simulateQ (keygenFiniteEager h) (simulateQ (keygenFiniteWorld prims S) oa)).run'
                (keygenRestrictCache S cache)] := by
  obtain ⟨S, hS⟩ := keygenWorldCovered_exists oa
  exact ⟨S, evalDist_keygenWorld_eager prims S oa hS⟩

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- The fixed total oracle represented by a finite table; the MPC domains still use `Th`. -/
def keygenFiniteTotal (prims : Primitives) (S : Finset (Query C)) (h : S → HashOutput)
    (q : Query C) : HashOutput :=
  match q with
  | .hash input => if MpcInput input then prims.Th input else
      if hq : q ∈ S then h ⟨q, hq⟩ else 0
  | _ => if hq : q ∈ S then h ⟨q, hq⟩ else 0

theorem keygenFiniteTotal_good (prims : Primitives) (S : Finset (Query C)) (h : S → HashOutput) :
    Good prims (keygenFiniteTotal prims S h) := by
  intro input hi
  simp [keygenFiniteTotal, hi]

/-- Reading a table value into the occupancy cache leaves the overlaid total function unchanged. -/
theorem keygenTableExtending_read {Ω : Type} [DecidableEq Ω] (cache : KeygenFiniteCache Ω)
    (h : Ω → HashOutput) (q : Ω) :
    tableExtending (cache.cacheQuery q (tableExtending cache h q)) h = tableExtending cache h := by
  rw [tableExtending_cacheQuery, Function.update_eq_self]

/-- An eager hash step preserves the total oracle, although it records occupancy for later
programming attempts. -/
theorem keygenFiniteHash_eager_step (prims : Primitives) (S : Finset (Query C))
    (h : S → HashOutput) (q : Query C) (cache : KeygenFiniteCache S) :
    ∃ cache',
      (simulateQ (keygenFiniteEager h) (keygenFiniteHash prims S q)).run cache =
        pure (keygenFiniteTotal prims S (tableExtending cache h) q, cache') ∧
      tableExtending cache' h = tableExtending cache h := by
  by_cases hf : IsFixed q
  · obtain ⟨input, rfl, hi⟩ := hf
    exact ⟨cache, by simp [keygenFiniteHash, keygenFiniteTotal, hi], rfl⟩
  · have hred : keygenFiniteHash prims S q =
        if hq : q ∈ S then OracleComp.lift ((KeygenFiniteSpec S).query (.inr (.inl ⟨q, hq⟩))) else pure 0 := by
      cases q <;> simp_all [keygenFiniteHash, IsFixed]
    have hv : keygenFiniteTotal prims S (tableExtending cache h) q =
        if hq : q ∈ S then tableExtending cache h ⟨q, hq⟩ else 0 := by
      cases q <;> simp_all [keygenFiniteTotal, IsFixed]
    rw [hred, hv]
    by_cases hq : q ∈ S
    · rw [dif_pos hq, dif_pos hq]
      erw [simulateQ_spec_query]
      change ∃ cache',
        (QueryImpl.withCaching (fun q => pure (h q) : QueryImpl (S →ₒ HashOutput) ProbComp)
          ⟨q, hq⟩).run cache = pure (tableExtending cache h ⟨q, hq⟩, cache') ∧ _
      cases hc : cache ⟨q, hq⟩ with
      | none =>
        refine ⟨cache.cacheQuery ⟨q, hq⟩ (h ⟨q, hq⟩), ?_, ?_⟩
        · rw [QueryImpl.withCaching_run_none _ hc]
          simp [tableExtending, hc]
        · simpa only [tableExtending, hc, Option.getD_none] using keygenTableExtending_read cache h ⟨q, hq⟩
      | some y =>
        refine ⟨cache, ?_, rfl⟩
        rw [QueryImpl.withCaching_run_some _ hc]
        simp [tableExtending, hc]
    · exact ⟨cache, by simp [hq], rfl⟩

/-- After the last programming block, the whole adaptive local computation sees one fixed
oracle. Private honest hashes do not change that oracle or restrict later legitimate queries. -/
theorem keygenFiniteLocal_eager_fixed (prims : Primitives) (S : Finset (Query C))
    (h : S → HashOutput) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∀ cache : KeygenFiniteCache S,
      (simulateQ (keygenFiniteEager h) (simulateQ (keygenFiniteLocal prims S) oa)).run' cache =
        simulateQ (fixedLocal prims (keygenFiniteTotal prims S (tableExtending cache h))) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro cache; rfl
  | query_bind t k ih =>
    intro cache
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    rcases t with n | q | x
    · change ((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        (fun p : unifSpec.Range n × KeygenFiniteCache S =>
          Prod.fst <$> (simulateQ (keygenFiniteEager h) (simulateQ (keygenFiniteLocal prims S) (k p.1))).run p.2) = _
      rw [bind_map_left]
      apply bind_congr
      intro y
      exact ih y cache
    · obtain ⟨cache', he, ht⟩ := keygenFiniteHash_eager_step prims S h q cache
      change (simulateQ (keygenFiniteEager h) (keygenFiniteHash prims S q)).run cache >>= _ = _
      rw [he, pure_bind]
      change (simulateQ (keygenFiniteEager h) (simulateQ (keygenFiniteLocal prims S)
        (k (keygenFiniteTotal prims S (tableExtending cache h) q)))).run' cache' = _
      rw [ih, ht]
      rfl
    · obtain ⟨cache', he, ht⟩ := keygenFiniteHash_eager_step prims S h (.streamKey x.2.1) cache
      change (simulateQ (keygenFiniteEager h) (keygenFiniteHash prims S (.streamKey x.2.1) >>=
        fun y => pure (prims.aes.eval (truncateHash y) x.2.2))).run cache >>= _ = _
      simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, he, pure_bind]
      change (simulateQ (keygenFiniteEager h) (simulateQ (keygenFiniteLocal prims S)
        (k (prims.aes.eval (truncateHash (keygenFiniteTotal prims S (tableExtending cache h)
          (.streamKey x.2.1))) x.2.2)))).run' cache' = _
      rw [ih, ht]
      rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem keygenCrossCoordinates_has_corrupt (coalition : C.Coalition) (p : C.Pair)
    (hp : p ∈ keygenCrossCoordinates coalition) : p.1.1 ∈ coalition.1 ∨ p.1.2 ∈ coalition.1 := by
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hp
  have hr := (keygenCrossList_mem coalition r.1).mp r.2
  unfold keygenCrossPair Committee.pairOf
  split_ifs <;> simp [hr.1]

/-- The actual simulator programming-input list is invariant under shifts of hidden term
and honest--honest pair coordinates when its pre-programming transcript is fixed. -/
theorem keygenProgrammingInputs_privateInvariant (coalition : C.Coalition)
    (log : CallLog C) (sent : C.Party → Mail C E) :
    KeygenPrivateInvariant coalition (fun parts =>
      keygenProgrammingInputs coalition (keygenProgramView coalition parts log sent)) := by
  constructor
  · intro a T hh c parts
    have hparam (i j : C.Party) :
        (keygenProgramView coalition (shiftAt a (some T) none c parts) log sent i j).parameter =
          (keygenProgramView coalition parts log sent i j).parameter := by
      unfold keygenProgramView shiftAt
      split_ifs <;> rfl
    have hterm (U : C.Term) (hu : U ∈ keygenKnownCoordinates coalition) (i j : C.Party) :
        (keygenProgramView coalition (shiftAt a (some T) none c parts) log sent i j).term U =
          (keygenProgramView coalition parts log sent i j).term U := by
      have hu' : KnownTo coalition.1 U := of_decide_eq_true (List.mem_filter.mp hu).2
      have hne : T ≠ U := fun he => hh (he ▸ hu')
      unfold keygenProgramView shiftAt
      split_ifs <;> simp [shiftParts, hne]
    have hpair (i j k : C.Party) :
        (keygenProgramView coalition (shiftAt a (some T) none c parts) log sent i j).pair k =
          (keygenProgramView coalition parts log sent i j).pair k := by
      unfold keygenProgramView shiftAt
      split_ifs <;> simp [shiftParts]
    dsimp only
    unfold keygenProgrammingInputs
    apply congrArg₂ List.append
    · apply congrArg₂ List.cons
      · simp only [keygenParameterProgrammingInput, hparam]
      · apply List.map_congr_left
        intro U hU
        simp only [keygenTermProgrammingInput]
        congr 1
        apply List.map_congr_left
        intro j _
        exact hterm U hU _ j
    · apply List.map_congr_left
      intro p _
      simp only [keygenPairProgrammingInput, hpair]
  · intro p ha hb c parts
    have hparam (i j : C.Party) :
        (keygenProgramView coalition (shiftAt p.1.1 none (some p.1.2) c parts) log sent i j).parameter =
          (keygenProgramView coalition parts log sent i j).parameter := by
      unfold keygenProgramView shiftAt
      split_ifs <;> rfl
    have hterm (U : C.Term) (i j : C.Party) :
        (keygenProgramView coalition (shiftAt p.1.1 none (some p.1.2) c parts) log sent i j).term U =
          (keygenProgramView coalition parts log sent i j).term U := by
      unfold keygenProgramView shiftAt
      split_ifs <;> simp [shiftParts]
    have hpart (i j k : C.Party) (hn : ¬ (j = p.1.1 ∧ k = p.1.2)) :
        (keygenProgramView coalition (shiftAt p.1.1 none (some p.1.2) c parts) log sent i j).pair k =
          (keygenProgramView coalition parts log sent i j).pair k := by
      unfold keygenProgramView shiftAt
      by_cases hj : j ∈ coalition.1
      · simp [hj]
      · by_cases he : j = p.1.1
        · have hk : p.1.2 ≠ k := fun hk => hn ⟨he, hk.symm⟩
          simp [ha, he, shiftParts, hk]
        · simp [hj, he]
    have hpair (r : C.Pair) (hr : r ∈ keygenCrossCoordinates coalition) :
        keygenPairProgrammingInput coalition
            (keygenProgramView coalition (shiftAt p.1.1 none (some p.1.2) c parts) log sent) r =
          keygenPairProgrammingInput coalition (keygenProgramView coalition parts log sent) r := by
      have hr' := keygenCrossCoordinates_has_corrupt coalition r hr
      have hn₁ : ¬ (r.1.1 = p.1.1 ∧ r.1.2 = p.1.2) := by
        rintro ⟨he₁, he₂⟩
        rcases hr' with hr' | hr'
        · exact ha (he₁ ▸ hr')
        · exact hb (he₂ ▸ hr')
      have hn₂ : ¬ (r.1.2 = p.1.1 ∧ r.1.1 = p.1.2) := by
        rintro ⟨he₁, he₂⟩
        rcases hr' with hr' | hr'
        · exact hb (he₂ ▸ hr')
        · exact ha (he₁ ▸ hr')
      simp only [keygenPairProgrammingInput, hpart _ _ _ hn₁, hpart _ _ _ hn₂]
    dsimp only
    unfold keygenProgrammingInputs
    apply congrArg₂ List.append
    · apply congrArg₂ List.cons
      · simp only [keygenParameterProgrammingInput, hparam]
      · apply List.map_congr_left
        intro U _
        simp only [keygenTermProgrammingInput, hterm]
    · exact List.map_congr_left hpair

/-- Randomized private-invariant kernels remain invariant when postprocessed with a function
that may inspect the parts, provided it too ignores the hidden coordinates. -/
theorem KeygenPrivateInvariant.map_kernel {α β : Type} (coalition : C.Coalition)
    (K : (C.Party → Parts C) → ProbComp α) (f : (C.Party → Parts C) → α → β)
    (hK : KeygenPrivateInvariant coalition K) (hf : ∀ a, KeygenPrivateInvariant coalition (fun parts => f parts a)) :
    KeygenPrivateInvariant coalition (fun parts => f parts <$> K parts) := by
  constructor
  · intro a T hh c parts
    dsimp only
    rw [hK.1 a T hh c parts]
    congr 1
    funext r
    exact (hf r).1 a T hh c parts
  · intro p ha hb c parts
    dsimp only
    rw [hK.2 p ha hb c parts]
    congr 1
    funext r
    exact (hf r).2 p ha hb c parts

/-- The number of actual programming attempts; it does not depend on the transcript. -/
def keygenProgrammingCount (coalition : C.Coalition) : ℕ :=
  1 + (keygenKnownCoordinates coalition).length + (keygenCrossCoordinates coalition).length

theorem keygenProgrammingInputs_length (coalition : C.Coalition) (view : C.Party → C.Party → Parts C) :
    (keygenProgrammingInputs coalition view).length = keygenProgrammingCount coalition := by
  simp [keygenProgrammingInputs, keygenProgrammingCount, Nat.add_comm, Nat.add_assoc]

/-- Bound aliases between canonical hidden inputs and extracted-view programming inputs
for an invariant pre-programming transcript. -/
theorem probEvent_keygenProgramming_hidden_alias (coalition : C.Coalition)
    (K : (C.Party → Parts C) → ProbComp (CallLog C × (C.Party → Mail C E)))
    (hK : KeygenPrivateInvariant coalition K) :
    Pr[fun p => ∃ q ∈ keygenProgrammingInputs coalition (keygenProgramView coalition p.1 p.2.1 p.2.2),
        KeygenHiddenInput coalition p.1 q | keygenPartsKernel K] ≤
      ((keygenProgrammingCount coalition * keygenSecrets C : ℕ) : ℝ≥0∞) *
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  let queries := fun (parts : C.Party → Parts C) (r : CallLog C × (C.Party → Mail C E))
      (i : Fin (keygenProgrammingCount coalition)) =>
    (keygenProgrammingInputs coalition (keygenProgramView coalition parts r.1 r.2)).getD i
      (.derive .keygen .parameter [])
  have hqi (r : CallLog C × (C.Party → Mail C E)) :
      KeygenPrivateInvariant coalition (fun parts => queries parts r) := by
    have hi := keygenProgrammingInputs_privateInvariant coalition r.1 r.2
    constructor
    · intro a T hh c parts
      funext i
      exact congrArg (fun xs : List (Query C) => xs.getD i (.derive .keygen .parameter []))
        (hi.1 a T hh c parts)
    · intro p ha hb c parts
      funext i
      exact congrArg (fun xs : List (Query C) => xs.getD i (.derive .keygen .parameter []))
        (hi.2 p ha hb c parts)
  have hb := probEvent_keygenHiddenInput_kernel coalition (keygenProgrammingCount coalition)
    (fun parts => queries parts <$> K parts) (hK.map_kernel coalition K queries hqi)
  have he : Pr[fun p => ∃ i : Fin (keygenProgrammingCount coalition),
        KeygenHiddenInput coalition p.1 (queries p.1 p.2 i) | keygenPartsKernel K] =
      Pr[fun p => ∃ i : Fin (keygenProgrammingCount coalition), KeygenHiddenInput coalition p.1 (p.2 i) |
        keygenPartsKernel (fun parts => queries parts <$> K parts)] := by
    simp only [keygenPartsKernel, bind_map_left, probEvent_bind_eq_tsum, probEvent_pure, probEvent_map,
      Function.comp_def]
  rw [← he] at hb
  apply le_trans (probEvent_mono (fun p _ hp => ?_)) hb
  obtain ⟨q, hq, hh⟩ := hp
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hq
  have hi' : i < keygenProgrammingCount coalition := by
    rwa [keygenProgrammingInputs_length] at hi
  refine ⟨⟨i, hi'⟩, ?_⟩
  dsimp only [queries]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, heq]
  exact hh

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Erase only private coordinates that no corrupt recipient receives. -/
def keygenExposedParts (coalition : C.Coalition) (parts : C.Party → Parts C) : C.Party → Parts C :=
  fun i => ⟨(parts i).parameter,
    fun T => if KnownTo coalition.1 T then (parts i).term T else 0,
    fun j => if i ∈ coalition.1 ∨ j ∈ coalition.1 then (parts i).pair j else 0⟩

theorem keygenExposedParts_privateInvariant (coalition : C.Coalition) :
    KeygenPrivateInvariant coalition (keygenExposedParts coalition) := by
  constructor
  · intro a T hh c parts
    funext i
    change Parts.mk _ _ _ = Parts.mk _ _ _
    congr 1
    · simp only [keygenExposedParts, shiftAt]
      split_ifs <;> rfl
    · funext U
      by_cases hU : KnownTo coalition.1 U
      · have hne : T ≠ U := fun he => hh (he ▸ hU)
        by_cases hi : i = a <;> simp [hU, shiftAt, shiftParts, hne, hi]
      · simp [keygenExposedParts, hU]
    · funext j
      simp only [keygenExposedParts, shiftAt]
      split_ifs <;> rfl
  · intro p ha hb c parts
    funext i
    change Parts.mk _ _ _ = Parts.mk _ _ _
    congr 1
    · simp only [keygenExposedParts, shiftAt]
      split_ifs <;> rfl
    · funext T
      simp only [keygenExposedParts, shiftAt]
      split_ifs <;> rfl
    · funext j
      by_cases hi : i = p.1.1
      · subst i
        by_cases hj : j = p.1.2
        · subst j; simp [keygenExposedParts, ha, hb]
        · simp [keygenExposedParts, shiftAt, shiftParts, Ne.symm hj]
      · simp [keygenExposedParts, shiftAt, hi]

theorem keygenExposedParts_reveal (coalition : C.Coalition) (parts : C.Party → Parts C)
    (i j : C.Party) (hj : j ∈ coalition.1) :
    revealTo .keygen (keygenExposedParts coalition parts i) i j = revealTo .keygen (parts i) i j := by
  simp only [revealTo, keygenExposedParts, hj, or_true, if_true]
  congr 2
  apply List.map_congr_left
  intro T hT
  simp [keygen_sharedTerms_known coalition i j hj T hT]

/-- Commit-round aborts depend only on the corrupt messages, including self messages. -/
def keygenCommitAborted (coalition : C.Coalition) (sent : C.Party → Mail C E) (i : C.Party) : Bool :=
  C.parties.any fun j => if j ∈ coalition.1 then Msg.isAbort (sent j i) else false

theorem keygenCommitInbox_aborted (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) (sent : C.Party → Mail C E) (i : C.Party) :
    (C.parties.any fun j => Msg.isAbort (keygenCommitInbox coalition parts commitments sent i j)) =
      keygenCommitAborted coalition sent i := by
  unfold keygenCommitAborted
  apply congrArg (fun f => C.parties.any f)
  funext j
  by_cases hj : j ∈ coalition.1
  · simp [keygenCommitInbox, roundInbox, hj]
  · simp [keygenCommitInbox, roundInbox, keygenInitialSteps, hj, keygenStart,
      Step.delivered, isAbort_commitOutbox]

/-- The real reveal inbox expressed without private commitment digests. -/
def keygenReferenceRevealInbox (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitSent revealSent : C.Party → Mail C E) (i j : C.Party) : Option (Msg E) :=
  if j ∈ coalition.1 then revealSent j i else
    if keygenCommitAborted coalition commitSent j then some .abort else
      revealOutbox .keygen j (parts j) i

theorem keygenRevealInbox_reference (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) (commitSent revealSent : C.Party → Mail C E) :
    keygenRevealInbox coalition parts (keygenCommitInbox coalition parts commitments commitSent) revealSent =
      keygenReferenceRevealInbox coalition parts commitSent revealSent := by
  funext i j
  simp only [keygenRevealInbox, roundInbox, keygenRevealSteps, keygenCommitInbox_aborted,
    keygenReferenceRevealInbox]
  by_cases hj : j ∈ coalition.1
  · simp [hj]
  · simp only [hj, false_or, if_false]
    split_ifs <;> rfl

/-- Once the reveal round has no abort, only corrupt openings need checking. -/
theorem keygenOpenCheck_corrupt_iff (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) (hi : i ∉ coalition.1)
    (ha : (C.parties.any fun j => Msg.isAbort
      (keygenReferenceRevealInbox coalition parts commitSent revealSent i j)) = false) :
    let commitments := fun j => D prims h (commitQueries .keygen j (parts j))
    let committed := keygenCommitInbox coalition parts commitments commitSent
    let revealed := keygenReferenceRevealInbox coalition parts commitSent revealSent
    openCheck .keygen i (parts i) (committed i) (revealed i)
      (D prims h (openQueries .keygen i (revealed i))) ↔
      ∀ j, j ∈ coalition.1 →
        (Msg.hashesOf (revealSent j i)).length = (revealTo .keygen (parts i) j i).length ∧
        [h (.commit .keygen j i (Msg.hashesOf (revealSent j i)))] = Msg.hashesOf (commitSent j i) := by
  dsimp only
  have hreceived := keygenRevealInbox_all_honest coalition parts
    (keygenCommitInbox coalition parts (fun j => D prims h (commitQueries .keygen j (parts j))) commitSent)
    revealSent i (by simpa only [keygenRevealInbox_reference] using ha)
  rw [keygenRevealInbox_reference] at hreceived
  simp only [openCheck, openQueries, D_mapM, D_hashQuery, getD_parties]
  constructor
  · intro ho j hj
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simpa only [keygenReferenceRevealInbox, if_pos hj, keygenCommitInbox, roundInbox] using ho j hji
  · intro ho j hji
    by_cases hj : j ∈ coalition.1
    · simpa only [keygenReferenceRevealInbox, if_pos hj, keygenCommitInbox, roundInbox] using ho j hj
    · rw [hreceived i j hj hji]
      constructor
      · simp [revealTo]
      · simp only [keygenCommitInbox, roundInbox, if_neg hj, keygenInitialSteps, if_neg hj,
          keygenStart, Step.delivered, commitOutbox, if_neg (Ne.symm hji), Msg.hashesOf,
          D_commitQueries, getD_parties]

/-- Honest parts together with the actual corrupt openings, without unused read fields. -/
def keygenCorruptView (coalition : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i j : C.Party) : Parts C :=
  if j ∈ coalition.1 then readReveal .keygen (Msg.hashesOf (revealed i j)) i j else parts j

theorem keygen_derived_corruptView (prims : Primitives) (coalition : C.Coalition)
    (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i : C.Party) (hi : i ∉ coalition.1)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .keygen (parts j) j i)
    (h : Query C → HashOutput) :
    D prims h (deriveKeys .keygen i (setupView .keygen i (parts i) (revealed i))) =
      D prims h (deriveKeys .keygen i (keygenCorruptView coalition parts revealed i)) := by
  have corrupt (j : C.Party) (hj : j ∈ coalition.1) :
      setupView .keygen i (parts i) (revealed i) j = keygenCorruptView coalition parts revealed i j := by
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simp only [setupView, if_neg hji, keygenCorruptView, if_pos hj]
  have parameter (j : C.Party) :
      (setupView .keygen i (parts i) (revealed i) j).parameter =
        (keygenCorruptView coalition parts revealed i j).parameter := by
    by_cases hj : j ∈ coalition.1
    · rw [corrupt j hj]
    · rw [setupView_honest_sender coalition parts revealed hreceived i j hj, honestView_parameter]
      simp [keygenCorruptView, hj]
  have term (T : C.Term) (hiT : i ∈ C.holders T) (j : C.Party) (hjT : j ∈ C.holders T) :
      (setupView .keygen i (parts i) (revealed i) j).term T =
        (keygenCorruptView coalition parts revealed i j).term T := by
    by_cases hj : j ∈ coalition.1
    · rw [corrupt j hj]
    · rw [setupView_honest_sender coalition parts revealed hreceived i j hj,
        honestView_term .keygen parts hjT hiT]
      simp [keygenCorruptView, hj]
  have pair (a b : C.Party) (hab : a = i ∨ b = i) :
      (setupView .keygen i (parts i) (revealed i) a).pair b =
        (keygenCorruptView coalition parts revealed i a).pair b := by
    by_cases ha : a ∈ coalition.1
    · rw [corrupt a ha]
    · rw [setupView_honest_sender coalition parts revealed hreceived i a ha,
        honestView_pair .keygen parts hab]
      simp [keygenCorruptView, ha]
  rw [D_deriveKeys, D_deriveKeys]
  simp only [ite_true]
  apply Prod.ext
  · apply congrArg h
    apply congrArg (Query.derive .keygen .parameter)
    apply List.map_congr_left
    intro j _
    exact parameter j
  · apply Prod.ext
    · funext T
      by_cases hiT : i ∈ C.holders T
      · simp only [if_pos hiT]
        apply congrArg h
        apply congrArg (Query.derive .keygen .term)
        apply List.map_congr_left
        intro j hj
        exact term T hiT j (by simpa using (List.mem_filter.mp hj).2)
      · simp [hiT]
    · funext j
      by_cases hji : j = i
      · simp [hji]
      · simp only [dif_neg hji]
        have hp := pairOf_left_or_right i j (Ne.symm hji)
        apply congrArg h
        apply congrArg (Query.derive .keygen .pair)
        exact congrArg₂ List.cons (pair _ _ hp)
          (congrArg (fun y => [y]) (pair _ _ hp.symm))

/-- Replace the hidden derived keys by an independently named table. -/
def keygenMaskKeys (coalition : C.Coalition) (table : KeyName C → HashOutput) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput) :=
  (keys.1, fun T => if KnownTo coalition.1 T then keys.2.1 T else
    if i ∈ C.holders T then table (.term T) else 0,
   fun j => if hj : j = i then 0 else
     if i ∈ coalition.1 ∨ j ∈ coalition.1 then keys.2.2 j
     else table (.pair (C.pairOf i j (Ne.symm hj))))

/-- The reference derivation uses the actual corrupt openings. -/
def keygenReferenceKeys (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) :=
  keygenMaskKeys coalition table i
    (D prims h (deriveKeys .keygen i (keygenCorruptView coalition parts revealed i)))

theorem keygenReferenceKeys_exposed (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) :
    keygenReferenceKeys prims coalition h table (keygenExposedParts coalition parts) revealed i =
      keygenReferenceKeys prims coalition h table parts revealed i := by
  have hp (j : C.Party) :
      (keygenCorruptView coalition (keygenExposedParts coalition parts) revealed i j).parameter =
        (keygenCorruptView coalition parts revealed i j).parameter := by
    unfold keygenCorruptView
    split_ifs <;> rfl
  have ht (T : C.Term) (hT : KnownTo coalition.1 T) (j : C.Party) :
      (keygenCorruptView coalition (keygenExposedParts coalition parts) revealed i j).term T =
        (keygenCorruptView coalition parts revealed i j).term T := by
    unfold keygenCorruptView
    split_ifs <;> simp [keygenExposedParts, hT]
  have hpair (a b : C.Party) (hab : a ∈ coalition.1 ∨ b ∈ coalition.1) :
      (keygenCorruptView coalition (keygenExposedParts coalition parts) revealed i a).pair b =
        (keygenCorruptView coalition parts revealed i a).pair b := by
    unfold keygenCorruptView
    split_ifs <;> simp [keygenExposedParts, hab]
  simp only [keygenReferenceKeys, keygenMaskKeys, D_deriveKeys, ite_true]
  apply Prod.ext
  · simp only [hp]
  · apply Prod.ext
    · funext T
      by_cases hT : KnownTo coalition.1 T
      · simp only [if_pos hT, ht T hT]
      · simp only [if_neg hT]
    · funext j
      by_cases hj : j = i
      · simp [hj]
      · simp only [dif_neg hj]
        by_cases hc : i ∈ coalition.1 ∨ j ∈ coalition.1
        · simp only [if_pos hc]
          have hab : (C.pairOf i j (Ne.symm hj)).1.1 ∈ coalition.1 ∨
              (C.pairOf i j (Ne.symm hj)).1.2 ∈ coalition.1 := by
            unfold Committee.pairOf
            split_ifs <;> simp_all [or_comm]
          simp only [hpair _ _ hab, hpair _ _ hab.symm]
        · simp only [if_neg hc]

/-- The reveal abort test, independent of every honest private part. -/
def keygenReferenceRevealAborted (coalition : C.Coalition)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) : Bool :=
  C.parties.any fun j => if j ∈ coalition.1 then Msg.isAbort (revealSent j i)
    else keygenCommitAborted coalition commitSent j

theorem keygenReferenceRevealInbox_aborted (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) :
    (C.parties.any fun j => Msg.isAbort (keygenReferenceRevealInbox coalition parts commitSent revealSent i j)) =
      keygenReferenceRevealAborted coalition commitSent revealSent i := by
  unfold keygenReferenceRevealAborted
  apply congrArg (fun f => C.parties.any f)
  funext j
  unfold keygenReferenceRevealInbox
  by_cases hj : j ∈ coalition.1
  · simp [hj]
  · simp only [if_neg hj]
    cases hb : keygenCommitAborted coalition commitSent j <;>
      simp [hb, revealOutbox, Msg.isAbort]

/-- Check each actual corrupt opening against its earlier commitment and expected length. -/
def keygenReferenceOpenCheck (coalition : C.Coalition) (h : Query C → HashOutput)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) : Prop :=
  ∀ j, j ∈ coalition.1 →
    (Msg.hashesOf (revealSent j i)).length = 1 + (sharedTerms j i).length + 1 ∧
    [h (.commit .keygen j i (Msg.hashesOf (revealSent j i)))] = Msg.hashesOf (commitSent j i)

/-- Concrete reference data for the echo round. Only hidden derivations are replaced. -/
def keygenReferenceData (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E)
    (i : C.Party) : Option (KeygenEchoData C) :=
  if i ∈ coalition.1 ∨ keygenCommitAborted coalition commitSent i then none else
    if keygenReferenceRevealAborted coalition commitSent revealSent i then none else
      if keygenReferenceOpenCheck coalition h commitSent revealSent i then
        let keys := keygenReferenceKeys prims coalition h table parts (fun i j => revealSent j i) i
        some (keys, D prims h (sharedQueries .keygen i keys))
      else none

theorem keygenReferenceData_exposed (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) :
    keygenReferenceData prims coalition h table (keygenExposedParts coalition parts) commitSent revealSent =
      keygenReferenceData prims coalition h table parts commitSent revealSent := by
  funext i
  simp only [keygenReferenceData, keygenReferenceKeys_exposed]

/-- Masking the actual reveal computation gives exactly the concrete reference data. -/
theorem keygenRevealAllFixed_mask (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) (i : C.Party) :
    let committed := keygenCommitInbox coalition parts
      (fun j => D prims h (commitQueries .keygen j (parts j))) commitSent
    Option.map (fun data : KeygenEchoData C =>
      let keys := keygenMaskKeys coalition table i data.1
      (keys, D prims h (sharedQueries .keygen i keys)))
      (keygenRevealAllFixed prims coalition h parts committed revealSent i) =
        keygenReferenceData prims coalition h table parts commitSent revealSent i := by
  dsimp only
  unfold keygenRevealAllFixed keygenReferenceData
  rw [keygenCommitInbox_aborted]
  by_cases hi : i ∈ coalition.1 ∨ keygenCommitAborted coalition commitSent i = true
  · simp only [if_pos hi, Option.map_none]
  · simp only [if_neg hi, keygenRevealDataFixed, keygenRevealInbox_reference,
      keygenReferenceRevealInbox_aborted]
    by_cases ha : keygenReferenceRevealAborted coalition commitSent revealSent i = true
    · simp only [if_pos ha, Option.map_none]
    · simp only [if_neg ha]
      have hi' : i ∉ coalition.1 := fun hh => hi (Or.inl hh)
      have ha' : (C.parties.any fun j => Msg.isAbort
          (keygenReferenceRevealInbox coalition parts commitSent revealSent i j)) = false := by
        rw [keygenReferenceRevealInbox_aborted]
        exact Bool.eq_false_iff.mpr ha
      have hc := keygenOpenCheck_corrupt_iff prims coalition h parts commitSent revealSent i hi' ha'
      dsimp only at hc
      have hl (j : C.Party) : (revealTo .keygen (parts i) j i).length =
          1 + (sharedTerms j i).length + 1 := by simp [revealTo, Nat.add_comm]
      simp only [hl] at hc
      change _ ↔ keygenReferenceOpenCheck coalition h commitSent revealSent i at hc
      rw [hc]
      split_ifs with ho
      · simp only [Option.map_some]
        have hreceived := keygenRevealInbox_all_honest coalition parts
          (keygenCommitInbox coalition parts (fun j => D prims h (commitQueries .keygen j (parts j))) commitSent)
          revealSent i (by simpa only [keygenRevealInbox_reference] using ha')
        rw [keygenRevealInbox_reference] at hreceived
        rw [keygen_derived_corruptView prims coalition parts _ i hi' hreceived h]
        have hv : keygenCorruptView coalition parts
            (keygenReferenceRevealInbox coalition parts commitSent revealSent) i =
              keygenCorruptView coalition parts (fun i j => revealSent j i) i := by
          funext j
          unfold keygenCorruptView
          split_ifs with hj
          · simp only [keygenReferenceRevealInbox, if_pos hj]
          · rfl
        rw [hv]
        rfl
      · rfl

/-- A consistent named table leaves the actual hidden derivations unchanged. -/
theorem keygenMaskKeys_actual (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .keygen (parts j) j i)
    (htable : ∀ name, Hidden coalition name → table name = h (keygenNamedInput parts name))
    (i : C.Party) (hi : i ∉ coalition.1) :
    keygenMaskKeys coalition table i
      (D prims h (deriveKeys .keygen i (setupView .keygen i (parts i) (revealed i)))) =
        D prims h (deriveKeys .keygen i (setupView .keygen i (parts i) (revealed i))) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext T
    by_cases hT : KnownTo coalition.1 T
    · simp [keygenMaskKeys, hT]
    · simp only [keygenMaskKeys, if_neg hT]
      by_cases hiT : i ∈ C.holders T
      · rw [if_pos hiT, htable (.term T) hT,
          keygen_hiddenTerm_derived prims coalition h parts revealed hreceived T hT i hiT]
        rfl
      · simp [hiT, D_deriveKeys]
  · funext j
    by_cases hji : j = i
    · subst j; simp [keygenMaskKeys, D_deriveKeys]
    · simp only [keygenMaskKeys, dif_neg hji]
      by_cases hj : j ∈ coalition.1
      · simp [hj]
      · simp only [hi, hj, or_self, if_false]
        rw [keygen_hiddenPair_derived prims coalition h parts revealed hreceived i j hi hj hji]
        apply htable
        change (C.pairOf i j (Ne.symm hji)).1.1 ∉ coalition.1 ∧
          (C.pairOf i j (Ne.symm hji)).1.2 ∉ coalition.1
        unfold Committee.pairOf
        split_ifs <;> exact ⟨by assumption, by assumption⟩

/-- The fixed-oracle actual reveal equals the reference when the named table records its
hidden derivations. Abort and opening failures are included in the equality. -/
theorem keygenRevealAllFixed_reference (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (htable : ∀ name, Hidden coalition name → table name = h (keygenNamedInput parts name))
    (commitSent revealSent : C.Party → Mail C E) :
    keygenRevealAllFixed prims coalition h parts
      (keygenCommitInbox coalition parts (fun j => D prims h (commitQueries .keygen j (parts j))) commitSent)
      revealSent = keygenReferenceData prims coalition h table parts commitSent revealSent := by
  funext i
  rw [← keygenRevealAllFixed_mask prims coalition h table parts commitSent revealSent i]
  let committed := keygenCommitInbox coalition parts
    (fun j => D prims h (commitQueries .keygen j (parts j))) commitSent
  change keygenRevealAllFixed prims coalition h parts committed revealSent i = _
  cases hd : keygenRevealAllFixed prims coalition h parts committed revealSent i with
  | none => rfl
  | some data =>
    have hi : i ∉ coalition.1 := by
      intro hc
      simp [keygenRevealAllFixed, hc] at hd
    have ha : (keygenRevealAllFixed prims coalition h parts committed revealSent i).isSome := by
      simp only [hd, Option.isSome_some]
    obtain ⟨he, hb⟩ := keygenRevealAllFixed_some prims coalition h parts committed revealSent i ha
    have hr := keygenRevealInbox_all_honest coalition parts committed revealSent i hb
    have hv := Option.some.inj (hd.symm.trans he)
    simp only [hv, Option.map_some, keygenMaskKeys_actual prims coalition h table parts _ hr htable i hi]

/-- The complete corrupt-facing reveal view, retaining honest commit aborts. -/
def keygenReferenceRevealView (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitSent : C.Party → Mail C E) (c i : C.Party) : Option (Msg E) :=
  if c ∈ coalition.1 ∧ i ∉ coalition.1 then
    if keygenCommitAborted coalition commitSent i then none else revealOutbox .keygen i (parts i) c
  else none

theorem keygenRevealSteps_view_reference (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) (commitSent : C.Party → Mail C E) :
    (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (keygenRevealSteps coalition parts (keygenCommitInbox coalition parts commitments commitSent) i).outbox c
      else none) = keygenReferenceRevealView coalition parts commitSent := by
  funext c i
  unfold keygenReferenceRevealView
  by_cases hc : c ∈ coalition.1 ∧ i ∉ coalition.1
  · simp only [if_pos hc, keygenRevealSteps, hc.2, false_or, keygenCommitInbox_aborted]
    split_ifs <;> rfl
  · simp only [if_neg hc]

theorem keygenReferenceRevealView_exposed (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitSent : C.Party → Mail C E) :
    keygenReferenceRevealView coalition (keygenExposedParts coalition parts) commitSent =
      keygenReferenceRevealView coalition parts commitSent := by
  funext c i
  unfold keygenReferenceRevealView
  split_ifs with hc hb
  · rfl
  · simp only [revealOutbox, keygenExposedParts_reveal coalition parts i c hc.1]
  · rfl

/-- The reference executes the actual adversary and actual final echo check. -/
def keygenReferencePostCommit (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (commitSent : C.Party → Mail C E) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (Keys C))) :=
  if ∀ i, i ∉ coalition.1 → keygenCommitAborted coalition commitSent i = true then
    pure (state, fun _ => none)
  else do
    let (st, sent) ← A.round state (keygenReferenceRevealView coalition parts commitSent)
    keygenFinishLocal coalition A st (keygenReferenceData prims coalition h table parts commitSent sent)

theorem keygenReferencePostCommit_exposed (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (commitSent : C.Party → Mail C E) :
    keygenReferencePostCommit prims coalition h table A state (keygenExposedParts coalition parts) commitSent =
      keygenReferencePostCommit prims coalition h table A state parts commitSent := by
  simp only [keygenReferencePostCommit, keygenReferenceRevealView_exposed, keygenReferenceData_exposed]

/-- Exact connection to both actual remaining rounds in the fixed-oracle representation. -/
theorem simulateQ_keygenPostCommit_reference (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (htable : ∀ name, Hidden coalition name → table name = h (keygenNamedInput parts name))
    (commitSent : C.Party → Mail C E) :
    simulateQ (fixedLocal prims h) (keygenPostCommitLocal coalition A state parts
      (keygenCommitInbox coalition parts (fun j => D prims h (commitQueries .keygen j (parts j))) commitSent)) =
      simulateQ (fixedLocal prims h) (keygenReferencePostCommit prims coalition h table A state parts commitSent) := by
  simp only [keygenPostCommitLocal, keygenCommitInbox_aborted, keygenReferencePostCommit]
  split_ifs with ha
  · rfl
  · rw [keygenRevealSteps_view_reference]
    simp only [simulateQ_bind]
    apply bind_congr
    intro r
    rcases r with ⟨st, sent⟩
    rw [simulateQ_fixedLocal_keygenRevealComputations, pure_bind,
      keygenRevealAllFixed_reference prims coalition h table parts htable]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Actual honest commitments as seen by the corrupted recipients, under a fixed oracle. -/
def keygenFixedCommitView (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (c i : C.Party) : Option (Msg E) :=
  if c ∈ coalition.1 ∧ i ∉ coalition.1 then
    commitOutbox i (D prims h (commitQueries .keygen i (parts i))) c else none

theorem keygenFixedCommitView_exposed (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    keygenFixedCommitView (E := E) prims coalition h (keygenExposedParts coalition parts) =
      keygenFixedCommitView prims coalition h parts := by
  funext c i
  unfold keygenFixedCommitView
  by_cases hc : c ∈ coalition.1 ∧ i ∉ coalition.1
  · simp only [if_pos hc, commitOutbox, D_commitQueries, getD_parties,
      keygenExposedParts_reveal coalition parts i c hc.1]
  · simp only [if_neg hc]

/-- Full reference execution, with the original adversary, distinguisher, and abort behavior. -/
def keygenReferenceLocalGame (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) : OracleComp (LocalSpec C) Bool := do
  let state ← A.start (corruptInputs coalition x) z
  let (st, sent) ← A.round state (keygenFixedCommitView prims coalition h parts)
  let r ← keygenReferencePostCommit prims coalition h table A st parts sent
  Z r

theorem keygenReferenceLocalGame_exposed (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) :
    keygenReferenceLocalGame prims coalition h table A x z Z (keygenExposedParts coalition parts) =
      keygenReferenceLocalGame prims coalition h table A x z Z parts := by
  simp only [keygenReferenceLocalGame, keygenFixedCommitView_exposed, keygenReferencePostCommit_exposed]

/-- Private-coordinate independence is proved for the whole adaptive reference execution. -/
theorem keygenReferenceLocalGame_privateInvariant (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    KeygenPrivateInvariant coalition (keygenReferenceLocalGame prims coalition h table A x z Z) := by
  have he := keygenReferenceLocalGame_exposed prims coalition h table A x z Z
  have hinv := keygenExposedParts_privateInvariant coalition
  constructor
  · intro a T hT c parts
    rw [← he (shiftAt a (some T) none c parts), hinv.1 a T hT c parts, he parts]
  · intro p ha hb c parts
    rw [← he (shiftAt p.1.1 none (some p.1.2) c parts), hinv.2 p ha hb c parts, he parts]

theorem keygenFinishLocal_queryBound (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (state : A.State) (data : C.Party → Option (KeygenEchoData C)) :
    IsQueryBoundP (keygenFinishLocal coalition A state data) Counted step := by
  unfold keygenFinishLocal
  split_ifs
  · exact isQueryBoundP_pure Counted _ step
  · simpa using isQueryBoundP_bind (hr state _) (fun r _ => isQueryBoundP_pure Counted
      (r.1, keygenEchoDataOutput coalition data r.2) 0)

theorem keygenReferencePostCommit_queryBound (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (state : A.State) (parts : C.Party → Parts C) (sent : C.Party → Mail C E) :
    IsQueryBoundP (keygenReferencePostCommit prims coalition h table A state parts sent) Counted (2 * step) := by
  unfold keygenReferencePostCommit
  split_ifs
  · exact isQueryBoundP_pure Counted _ _
  · simpa only [two_mul] using isQueryBoundP_bind (hr state _)
      (fun r _ => keygenFinishLocal_queryBound coalition A step hr r.1 _)

/-- The reference consumes only the original adversary/distinguisher budget. -/
theorem keygenReferenceLocalGame_queryBound (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q)
    (parts : C.Party → Parts C) :
    IsQueryBoundP (keygenReferenceLocalGame prims coalition h table A x z Z parts) Counted q := by
  obtain ⟨start, step, final, htotal, hs, hr, _, hz⟩ := hq
  unfold keygenReferenceLocalGame
  have hb := isQueryBoundP_bind (hs (corruptInputs coalition x) z) (fun state _ =>
    isQueryBoundP_bind (hr state (keygenFixedCommitView prims coalition h parts)) (fun r _ =>
      isQueryBoundP_bind (keygenReferencePostCommit_queryBound prims coalition h table A step hr r.1 parts r.2)
        (fun out _ => hz out)))
  apply hb.mono
  simp only [setupRounds] at htotal
  omega

theorem keygenHashLog_query (t : (LocalSpec C).Domain) :
    keygenHashLog (OracleComp.lift ((LocalSpec C).query t)) =
      (fun u => (u, keygenLocalHashInputs t)) <$> OracleComp.lift ((LocalSpec C).query t) := by
  simp only [keygenHashLog, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
  simp [QueryImpl.withTraceAppend_apply, QueryImpl.id', WriterT.run_bind, map_eq_bind_pure_comp]

/-- Random inputs in the transcript correspond exactly to counted calls, including PRG. -/
theorem keygenLocalHashInputs_counted (t : (LocalSpec C).Domain) :
    ((keygenLocalHashInputs t).filter fun q => ¬ IsFixed q).length = if Counted t then 1 else 0 := by
  rcases t with t | (q | x)
  · simp [keygenLocalHashInputs, Counted]
  · cases q with
    | hash input =>
      have hf : IsFixed (Query.hash (C := C) input) ↔ MpcInput input := by simp [IsFixed]
      by_cases hm : MpcInput input <;> simp [keygenLocalHashInputs, Counted, List.filter_cons, hf, hm]
    | _ => simp [keygenLocalHashInputs, Counted, IsFixed]
  · simp [keygenLocalHashInputs, Counted, IsFixed]

/-- A syntactic query budget bounds the logged random inputs, regardless of answers. -/
theorem keygenHashLog_random_length_le {α : Type} (oa : OracleComp (LocalSpec C) α)
    (n : ℕ) (hq : IsQueryBoundP oa Counted n) (r : α × List (Query C))
    (hr : r ∈ support (keygenHashLog oa)) :
    (r.2.filter fun q => ¬ IsFixed q).length ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n r with
  | pure a =>
    simp only [keygenHashLog_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [keygenHashLog_bind, keygenHashLog_query] at hr
    simp only [support_bind, support_map, Set.mem_iUnion, Set.mem_image, Prod.exists,
      support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, l, ⟨v, _, he⟩, a, rest, hk, hr⟩ := hr
    cases he
    cases hr
    have hrest := ih u _ (hq.2 u) (a, rest) hk
    simp only [List.filter_append, List.length_append, keygenLocalHashInputs_counted]
    split_ifs at hrest ⊢ with ht <;> simp_all <;> omega

/-- A fixed-oracle interpretation cannot add a new syntactic output. -/
theorem keygenFixedLocal_support_subset (prims : Primitives) (h : Query C → HashOutput)
    {α : Type} (oa : OracleComp (LocalSpec C) α) :
    support (simulateQ (fixedLocal prims h) oa) ⊆ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    intro r hr
    rw [simulateQ_bind] at hr
    rcases (mem_support_bind_iff _ _ _).mp hr with ⟨u, _, hu⟩
    exact (mem_support_bind_iff _ _ _).mpr ⟨u, mem_support_query t u, ih u hu⟩

/-- Log every adversarial and distinguisher query in the reference execution. -/
def keygenReferenceKernel (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) :
    ProbComp (Bool × List (Query C)) :=
  simulateQ (fixedLocal prims h)
    (keygenHashLog (keygenReferenceLocalGame prims coalition h table A x z Z parts))

theorem keygenReferenceKernel_privateInvariant (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    KeygenPrivateInvariant coalition (keygenReferenceKernel prims coalition h table A x z Z) := by
  have hi := keygenReferenceLocalGame_privateInvariant prims coalition h table A x z Z
  constructor
  · intro a T hT c parts
    unfold keygenReferenceKernel
    rw [hi.1 a T hT c parts]
  · intro p ha hb c parts
    unfold keygenReferenceKernel
    rw [hi.2 p ha hb c parts]

theorem keygenReferenceKernel_random_length_le (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q)
    (parts : C.Party → Parts C) (r : Bool × List (Query C))
    (hr : r ∈ support (keygenReferenceKernel prims coalition h table A x z Z parts)) :
    (r.2.filter fun v => ¬ IsFixed v).length ≤ q :=
  keygenHashLog_random_length_le _ q
    (keygenReferenceLocalGame_queryBound prims coalition h table A x z Z q hq parts) r
    (keygenFixedLocal_support_subset prims h _ hr)

/-- The guessing lemma applies to a variable-length transcript bounded on its support. -/
theorem probEvent_keygenHiddenInput_kernel_list {α : Type} (coalition : C.Coalition)
    (K : (C.Party → Parts C) → ProbComp α) (hinv : KeygenPrivateInvariant coalition K)
    (queries : α → List (Query C)) (m : ℕ)
    (hbound : ∀ parts r, r ∈ support (K parts) → (queries r).length ≤ m) :
    Pr[fun p => ∃ v ∈ queries p.2, KeygenHiddenInput coalition p.1 v | keygenPartsKernel K] ≤
      ((m * keygenSecrets C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  let targets (r : α) (i : Fin m) := (queries r).getD i.val (.streamKey 0)
  let K' (parts : C.Party → Parts C) := targets <$> K parts
  have hinv' : KeygenPrivateInvariant coalition K' := by
    constructor
    · intro a T hT c parts
      dsimp only [K']
      rw [hinv.1 a T hT c parts]
    · intro p ha hb c parts
      dsimp only [K']
      rw [hinv.2 p ha hb c parts]
  have he : keygenPartsKernel K' =
      (fun p : (C.Party → Parts C) × α => (p.1, targets p.2)) <$> keygenPartsKernel K := by
    simp only [keygenPartsKernel, K', map_bind, bind_map_left, map_pure]
  have hb := probEvent_keygenHiddenInput_kernel coalition m K' hinv'
  rw [he, probEvent_map] at hb
  apply le_trans (probEvent_mono (fun p hp hh => ?_)) hb
  rcases p with ⟨parts, r⟩
  have hr : r ∈ support (K parts) := by
    simp only [keygenPartsKernel, support_bind, Set.mem_iUnion, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hp
    obtain ⟨p', _, r', hr', he₁, he₂⟩ := hp
    cases he₁
    cases he₂
    exact hr'
  obtain ⟨v, hv, hh⟩ := hh
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hv
  refine ⟨⟨j, Nat.lt_of_lt_of_le hj (hbound parts r hr)⟩, ?_⟩
  simpa only [targets, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some, he] using hh

/-- The full reference transcript guesses a hidden raw input with probability at most `q*S/N`.
There is no invariance or transcript-length assumption left for the caller to discharge. -/
theorem probEvent_keygenReference_hidden_guess (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    Pr[fun p => ∃ v ∈ p.2.2, KeygenHiddenInput coalition p.1 v |
      keygenPartsKernel (keygenReferenceKernel prims coalition h table A x z Z)] ≤
      ((q * keygenSecrets C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have hb := probEvent_keygenHiddenInput_kernel_list coalition
    (keygenReferenceKernel prims coalition h table A x z Z)
    (keygenReferenceKernel_privateInvariant prims coalition h table A x z Z)
    (fun r => r.2.filter fun v => ¬ IsFixed v) q
    (keygenReferenceKernel_random_length_le prims coalition h table A x z Z q hq)
  apply le_trans (probEvent_mono (fun p _ hh => ?_)) hb
  obtain ⟨v, hv, name, hn, he⟩ := hh
  refine ⟨v, List.mem_filter.mpr ⟨hv, ?_⟩, name, hn, he⟩
  apply decide_eq_true
  rw [← he]
  exact keygenNamedInput_not_fixed p.1 name

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The reference reaches echo precisely when these actual abort and opening checks pass. -/
def keygenReferenceActive (coalition : C.Coalition) (h : Query C → HashOutput)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) : Prop :=
  i ∉ coalition.1 ∧ keygenCommitAborted coalition commitSent i = false ∧
    keygenReferenceRevealAborted coalition commitSent revealSent i = false ∧
    keygenReferenceOpenCheck coalition h commitSent revealSent i

theorem keygenReferenceData_active (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) (i : C.Party) :
    keygenReferenceData prims coalition h table parts commitSent revealSent i =
      if keygenReferenceActive coalition h commitSent revealSent i then
        let keys := keygenReferenceKeys prims coalition h table parts (fun i j => revealSent j i) i
        some (keys, D prims h (sharedQueries .keygen i keys)) else none := by
  unfold keygenReferenceData keygenReferenceActive
  split_ifs <;> simp_all

theorem keygenReferenceKeys_known (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) (T : C.Term)
    (hT : KnownTo coalition.1 T) :
    (keygenReferenceKeys prims coalition h left parts revealed i).2.1 T =
      (keygenReferenceKeys prims coalition h right parts revealed i).2.1 T := by
  simp only [keygenReferenceKeys, keygenMaskKeys, if_pos hT]

theorem keygenReferenceKeys_coherent (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i j : C.Party) (T : C.Term)
    (hT : ¬ KnownTo coalition.1 T) (hi : i ∈ C.holders T) (hj : j ∈ C.holders T) :
    (keygenReferenceKeys prims coalition h table parts revealed i).2.1 T =
      (keygenReferenceKeys prims coalition h table parts revealed j).2.1 T := by
  simp only [keygenReferenceKeys, keygenMaskKeys, if_neg hT, if_pos hi, if_pos hj]

theorem keygenReferenceKeys_shared_corrupt (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i c : C.Party)
    (hc : c ∈ coalition.1) :
    h (.sharedKeys .keygen ((sharedTerms i c).map
      (keygenReferenceKeys prims coalition h left parts revealed i).2.1)) =
      h (.sharedKeys .keygen ((sharedTerms i c).map
        (keygenReferenceKeys prims coalition h right parts revealed i).2.1)) := by
  apply congrArg h
  exact keygen_sharedInput_known coalition i c hc _ _
    (keygenReferenceKeys_known prims coalition h left right parts revealed i)

/-- A sufficient noncollision condition for every honest pair in the reference echo round. -/
def KeygenReferenceEchoRegular (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) : Prop :=
  ∀ i j, i ∉ coalition.1 → j ∉ coalition.1 →
    let ki := keygenReferenceKeys prims coalition h table parts revealed i
    let kj := keygenReferenceKeys prims coalition h table parts revealed j
    h (.sharedKeys .keygen ((sharedTerms i j).map ki.2.1)) =
      h (.sharedKeys .keygen ((sharedTerms j i).map kj.2.1)) →
    Query.sharedKeys (C := C) .keygen ((sharedTerms i j).map ki.2.1) =
      Query.sharedKeys .keygen ((sharedTerms j i).map kj.2.1)

theorem keygenReferenceData_echoStep (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) (i : C.Party) :
    keygenEchoDataStep (E := E) i (keygenReferenceData prims coalition h table parts commitSent revealSent i) =
      keygenEchoStep prims coalition (keygenReferenceActive coalition h commitSent revealSent) h
        (keygenReferenceKeys prims coalition h table parts (fun i j => revealSent j i)) i := by
  rw [keygenReferenceData_active]
  unfold keygenEchoStep
  by_cases ha : keygenReferenceActive coalition h commitSent revealSent i
  · have hi := ha.1
    simp [ha, hi, keygenEchoDataStep]
  · simp [ha, keygenEchoDataStep]

/-- Corrupt recipients see identical echo messages for every independent hidden table. -/
theorem keygenReferenceData_visible (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E)
    (i c : C.Party) (hc : c ∈ coalition.1) :
    (keygenEchoDataStep (E := E) i (keygenReferenceData prims coalition h left parts commitSent revealSent i)).outbox c =
      (keygenEchoDataStep (E := E) i (keygenReferenceData prims coalition h right parts commitSent revealSent i)).outbox c := by
  simp only [keygenReferenceData_active]
  split_ifs with ha
  · simp only [keygenEchoDataStep, Step.outbox, echoOutbox]
    congr 2
    simp only [echoOf, ite_true, D_sharedQueries_at]
    rw [keygenReferenceKeys_shared_corrupt prims coalition h left right parts _ i c hc]
    rfl
  · rfl

/-- The actual reference receiver decision is invariant under hidden-table replacement,
except for the stated relevant honest echo collisions in either table. -/
theorem keygenReferenceData_receivers (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent echoSent : C.Party → Mail C E)
    (hl : KeygenReferenceEchoRegular prims coalition h left parts (fun i j => revealSent j i))
    (hr : KeygenReferenceEchoRegular prims coalition h right parts (fun i j => revealSent j i)) (i : C.Party) :
    (keygenEchoDataOutput coalition (keygenReferenceData prims coalition h left parts commitSent revealSent) echoSent i).isSome =
      (keygenEchoDataOutput coalition (keygenReferenceData prims coalition h right parts commitSent revealSent) echoSent i).isSome := by
  let active := keygenReferenceActive coalition h commitSent revealSent
  let kl := keygenReferenceKeys prims coalition h left parts (fun i j => revealSent j i)
  let kr := keygenReferenceKeys prims coalition h right parts (fun i j => revealSent j i)
  have hsteps (table : KeyName C → HashOutput) :
      (fun j => keygenEchoDataStep (E := E) j (keygenReferenceData prims coalition h table parts commitSent revealSent j)) =
        keygenEchoStep prims coalition active h (keygenReferenceKeys prims coalition h table parts (fun i j => revealSent j i)) :=
    funext fun j => keygenReferenceData_echoStep prims coalition h table parts commitSent revealSent j
  unfold keygenEchoDataOutput
  rw [keygenReferenceData_active, keygenReferenceData_active]
  by_cases ha : active i
  · change keygenReferenceActive coalition h commitSent revealSent i at ha
    simp only [if_pos ha]
    have hi := ha.1
    simp only [if_neg hi, hsteps, roundInbox_keygenEchoStep]
    have hab : (fun j => Msg.isAbort (keygenEchoInbox prims coalition active echoSent h kl i j)) =
        (fun j => Msg.isAbort (keygenEchoInbox prims coalition active echoSent h kr i j)) :=
      funext fun j => keygenEchoInbox_isAbort prims coalition active echoSent h h kl kr i j
    have hc := keygen_echoCheck_hidden_invariant prims coalition active echoSent h h kl kr
      (fun _ _ => rfl)
      (fun j T _ hT => keygenReferenceKeys_known prims coalition h left right parts _ j T hT)
      (fun j k T _ _ hT hj hk => keygenReferenceKeys_coherent prims coalition h left parts _ j k T hT hj hk)
      (fun j k T _ _ hT hj hk => keygenReferenceKeys_coherent prims coalition h right parts _ j k T hT hj hk)
      (fun j c _ hc => keygenReferenceKeys_shared_corrupt prims coalition h left right parts _ j c hc)
      hl hr i hi
    change (if C.parties.any (fun j => Msg.isAbort (keygenEchoInbox prims coalition active echoSent h kl i j)) then none
      else if echoCheck .keygen i (kl i) (D prims h (sharedQueries .keygen i (kl i)))
        (keygenEchoInbox prims coalition active echoSent h kl i) then some (keysOf (kl i)) else none).isSome = _
    rw [hab, hc]
    split_ifs <;> rfl
  · change ¬ keygenReferenceActive coalition h commitSent revealSent i at ha
    simp only [if_neg ha, Option.isSome_none]

/-- The complete final reference round preserves the adversary state and receiver set
under hidden-table replacement outside the two relevant collision events. -/
theorem keygenReferenceFinish_receivers (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E)
    (hl : KeygenReferenceEchoRegular prims coalition h left parts (fun i j => revealSent j i))
    (hr : KeygenReferenceEchoRegular prims coalition h right parts (fun i j => revealSent j i)) :
    (fun r => (r.1, fun i => (r.2 i).isSome)) <$>
      keygenFinishLocal coalition A state (keygenReferenceData prims coalition h left parts commitSent revealSent) =
    (fun r => (r.1, fun i => (r.2 i).isSome)) <$>
      keygenFinishLocal coalition A state (keygenReferenceData prims coalition h right parts commitSent revealSent) := by
  have he (table : KeyName C → HashOutput) :
      (∀ i, i ∉ coalition.1 → keygenReferenceData prims coalition h table parts commitSent revealSent i = none) ↔
        ∀ i, i ∉ coalition.1 → ¬ keygenReferenceActive coalition h commitSent revealSent i := by
    apply forall_congr'
    intro i
    apply forall_congr'
    intro _
    rw [keygenReferenceData_active]
    split_ifs <;> simp_all
  unfold keygenFinishLocal
  simp only [he]
  split_ifs with ha
  · rfl
  · have hv : (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        (keygenEchoDataStep (E := E) i (keygenReferenceData prims coalition h left parts commitSent revealSent i)).outbox c
        else none) = (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        (keygenEchoDataStep (E := E) i (keygenReferenceData prims coalition h right parts commitSent revealSent i)).outbox c
        else none) := by
      funext c i
      split_ifs with hc
      · exact keygenReferenceData_visible prims coalition h left right parts commitSent revealSent i c hc.1
      · rfl
    rw [hv]
    simp only [map_bind, map_pure]
    apply bind_congr
    intro r
    congr 2
    funext i
    exact keygenReferenceData_receivers prims coalition h left right parts commitSent revealSent r.2 hl hr i

/-- Stop symmetrically if the honest-pair noncollision test fails for either table. -/
def keygenReferenceStoppedFinish (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) (useLeft : Bool) :
    OracleComp (LocalSpec C) (Option (A.State × (C.Party → Bool))) :=
  if KeygenReferenceEchoRegular prims coalition h left parts (fun i j => revealSent j i) ∧
      KeygenReferenceEchoRegular prims coalition h right parts (fun i j => revealSent j i) then
    (fun r => some (r.1, fun i => (r.2 i).isSome)) <$>
      keygenFinishLocal coalition A state (keygenReferenceData prims coalition h
        (if useLeft then left else right) parts commitSent revealSent)
  else pure none

/-- The symmetric stopped echo comparison has no collision hypothesis. -/
theorem keygenReferenceStoppedFinish_eq (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) :
    keygenReferenceStoppedFinish prims coalition h left right A state parts commitSent revealSent true =
      keygenReferenceStoppedFinish prims coalition h left right A state parts commitSent revealSent false := by
  unfold keygenReferenceStoppedFinish
  by_cases hc : KeygenReferenceEchoRegular prims coalition h left parts (fun i j => revealSent j i) ∧
      KeygenReferenceEchoRegular prims coalition h right parts (fun i j => revealSent j i)
  · rw [if_pos hc, if_pos hc]
    have he := keygenReferenceFinish_receivers prims coalition h left right A state parts commitSent revealSent hc.1 hc.2
    simpa only [Functor.map_map, Bool.false_eq_true, if_true, if_false] using
      congrArg (fun oa => Option.some <$> oa) he
  · rw [if_neg hc, if_neg hc]

/-- The remaining actual reference rounds, stopped on the symmetric echo collision event. -/
def keygenReferenceStoppedPostCommit (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (commitSent : C.Party → Mail C E) (useLeft : Bool) :
    OracleComp (LocalSpec C) (Option (A.State × (C.Party → Bool))) :=
  if ∀ i, i ∉ coalition.1 → keygenCommitAborted coalition commitSent i = true then
    pure (some (state, fun _ => false))
  else do
    let (st, sent) ← A.round state (keygenReferenceRevealView coalition parts commitSent)
    keygenReferenceStoppedFinish prims coalition h left right A st parts commitSent sent useLeft

/-- Exact hidden-table invariance through both remaining reference rounds, including early abort. -/
theorem keygenReferenceStoppedPostCommit_eq (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (commitSent : C.Party → Mail C E) :
    keygenReferenceStoppedPostCommit prims coalition h left right A state parts commitSent true =
      keygenReferenceStoppedPostCommit prims coalition h left right A state parts commitSent false := by
  simp only [keygenReferenceStoppedPostCommit, keygenReferenceStoppedFinish_eq]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The real simulator's observed commit round makes no honest hash calls after delivery. -/
theorem stepRound_keygenInitialSteps_observed (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) :
    stepRound observedRoles coalition A noFunctionality state
        (keygenInitialSteps coalition parts commitments) = (do
      let (st, sent) ← observedRoles.adversary (A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        commitOutbox i (commitments i) c else none)
      pure (st, keygenRevealSteps coalition parts (keygenCommitInbox coalition parts commitments sent), sent)) := by
  unfold stepRound
  rw [if_neg (by simp only [callInput_real, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, not_false_eq_true])]
  have hmsg : (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (keygenInitialSteps coalition parts commitments (E := E) i).outbox c else none) =
      (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then commitOutbox i (commitments i) c else none) := by
    funext c i
    split_ifs with hc
    · simp only [keygenInitialSteps, if_neg hc.2, keygenStart, Step.outbox]
    · rfl
  rw [hmsg]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only [observedRoles]
  trans (Concrete.sequenceFin (fun j =>
    (pure (keygenRevealSteps coalition parts (keygenCommitInbox coalition parts commitments sent) j) :
      WriterT (CallLog C) (OracleComp (WorldSpec C)) _)) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext j
    by_cases hj : j ∈ coalition.1
    · simp [keygenInitialSteps, keygenRevealSteps, hj]
    · simp only [keygenInitialSteps, if_neg hj, keygenStart]
      rw [advance_keygenCommitResume]
      simp only [keygenRevealSteps, hj, false_or, keygenCommitInbox, roundInbox]
      simp only [free_pure, liftM_pure]
      rfl
  · rw [sequenceFin_pure, pure_bind]

/-- Fixed-oracle interpretation of the two local copies. Programming is unused in a prefix. -/
def keygenFixedPrefixWorld (prims : Primitives) (h : Query C → HashOutput) : QueryImpl (WorldSpec C) ProbComp :=
  fixedLocal prims h + ((fun _ => pure false) : QueryImpl (ProgramSpec C) ProbComp) + fixedLocal prims h

/-- The actual observed adversary prefix, using fixed honest commitment answers. -/
def keygenFixedCommitKernel (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    ProbComp (CallLog C × (C.Party → Mail C E)) :=
  simulateQ (keygenFixedPrefixWorld prims h) do
    let (state, log) ← observe (A.start (corruptInputs coalition x) z)
    let ((_, sent), calls) ← observe (A.round state (keygenFixedCommitView prims coalition h parts))
    pure (log ++ calls, sent)

theorem keygenFixedCommitKernel_privateInvariant (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    KeygenPrivateInvariant coalition (keygenFixedCommitKernel prims coalition h A x z) := by
  have he (parts : C.Party → Parts C) :
      keygenFixedCommitKernel prims coalition h A x z (keygenExposedParts coalition parts) =
        keygenFixedCommitKernel prims coalition h A x z parts := by
    simp only [keygenFixedCommitKernel, keygenFixedCommitView_exposed]
  have hi := keygenExposedParts_privateInvariant coalition
  constructor
  · intro a T hT c parts
    rw [← he (shiftAt a (some T) none c parts), hi.1 a T hT c parts, he parts]
  · intro p ha hb c parts
    rw [← he (shiftAt p.1.1 none (some p.1.2) c parts), hi.2 p ha hb c parts, he parts]

/-- The programming alias bound is instantiated for the actual fixed-oracle observed prefix. -/
theorem probEvent_keygenFixedCommit_programming_alias (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    Pr[fun p => ∃ v ∈ keygenProgrammingInputs coalition
        (keygenProgramView coalition p.1 p.2.1 p.2.2), KeygenHiddenInput coalition p.1 v |
      keygenPartsKernel (keygenFixedCommitKernel prims coalition h A x z)] ≤
      ((keygenProgrammingCount coalition * keygenSecrets C : ℕ) : ℝ≥0∞) *
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  exact probEvent_keygenProgramming_hidden_alias coalition _
    (keygenFixedCommitKernel_privateInvariant prims coalition h A x z)

/-- The fixed prefix retains exactly the simulator's actual observed `stepRound` log. -/
theorem keygenFixedCommitKernel_stepRound (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    simulateQ (keygenFixedPrefixWorld prims h) (do
      let (state, log) ← observe (A.start (corruptInputs coalition x) z)
      let (r, calls) ← (stepRound observedRoles coalition A noFunctionality state
        (keygenInitialSteps coalition parts (fun j => D prims h (commitQueries .keygen j (parts j))))).run
      pure (log ++ calls, r.2.2)) = keygenFixedCommitKernel prims coalition h A x z parts := by
  unfold keygenFixedCommitKernel
  apply congrArg (simulateQ (keygenFixedPrefixWorld prims h))
  apply bind_congr
  rintro ⟨state, log⟩
  dsimp only
  erw [stepRound_keygenInitialSteps_observed coalition A state parts
    (fun j => D prims h (commitQueries .keygen j (parts j)))]
  simp only [observedRoles, WriterT.run_bind, WriterT.run_pure, map_pure, pure_bind, bind_assoc,
    show (∅ : CallLog C) = [] from rfl, List.append_nil, keygenFixedCommitView]
  rfl

/-- Start and commit of the actual adversary, with fixed honest commitment answers. -/
def keygenFixedCommitLocal (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Mail C E)) := do
  let state ← A.start (corruptInputs coalition x) z
  A.round state (keygenFixedCommitView prims coalition h parts)

def keygenFixedCommitQueryKernel (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (parts : C.Party → Parts C) :
    ProbComp ((A.State × (C.Party → Mail C E)) × List (Query C)) :=
  simulateQ (fixedLocal prims h) (keygenHashLog (keygenFixedCommitLocal prims coalition h A x z parts))

theorem keygenFixedCommitQueryKernel_privateInvariant (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    KeygenPrivateInvariant coalition (keygenFixedCommitQueryKernel prims coalition h A x z) := by
  have he (parts : C.Party → Parts C) :
      keygenFixedCommitQueryKernel prims coalition h A x z (keygenExposedParts coalition parts) =
        keygenFixedCommitQueryKernel prims coalition h A x z parts := by
    simp only [keygenFixedCommitQueryKernel, keygenFixedCommitLocal, keygenFixedCommitView_exposed]
  have hi := keygenExposedParts_privateInvariant coalition
  constructor
  · intro a T hT c parts
    rw [← he (shiftAt a (some T) none c parts), hi.1 a T hT c parts, he parts]
  · intro p ha hb c parts
    rw [← he (shiftAt p.1.1 none (some p.1.2) c parts), hi.2 p ha hb c parts, he parts]

/-- A direct hidden-input guessing bound for the actual fixed-oracle start/commit prefix. -/
theorem probEvent_keygenFixedCommit_hidden_guess (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C))
    (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    Pr[fun p => ∃ v ∈ p.2.2, KeygenHiddenInput coalition p.1 v |
      keygenPartsKernel (keygenFixedCommitQueryKernel prims coalition h A x z)] ≤
      ((q * keygenSecrets C : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have hbound (parts : C.Party → Parts C) :
      IsQueryBoundP (keygenFixedCommitLocal prims coalition h A x z parts) Counted q := by
    obtain ⟨start, step, final, ht, hs, hr, _, _⟩ := hq
    apply (isQueryBoundP_bind (hs (corruptInputs coalition x) z) (fun state _ => hr state _)).mono
    simp only [setupRounds] at ht
    omega
  have hb := probEvent_keygenHiddenInput_kernel_list coalition
    (keygenFixedCommitQueryKernel prims coalition h A x z)
    (keygenFixedCommitQueryKernel_privateInvariant prims coalition h A x z)
    (fun r => r.2.filter fun v => ¬ IsFixed v) q
    (fun parts r hr => keygenHashLog_random_length_le _ q (hbound parts) r
      (keygenFixedLocal_support_subset prims h _ hr))
  apply le_trans (probEvent_mono (fun p _ hh => ?_)) hb
  obtain ⟨v, hv, name, hn, he⟩ := hh
  refine ⟨v, List.mem_filter.mpr ⟨hv, ?_⟩, name, hn, he⟩
  apply decide_eq_true
  rw [← he]
  exact keygenNamedInput_not_fixed p.1 name

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem simulateQ_fixedLocal_private (prims : Primitives) (h : Query C → HashOutput)
    {α : Type} (oa : ProbComp α) :
    simulateQ (fixedLocal prims h) (liftComp oa (LocalSpec C)) = oa := by
  rw [fixedLocal, QueryImpl.simulateQ_add_liftComp_left]
  exact simulateQ_id' oa

def keygenFixedInitialCommitments (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) : C.Party → List HashOutput :=
  fun i => if i ∈ coalition.1 then [] else D prims h (commitQueries .keygen i (parts i))

theorem simulateQ_fixedLocal_keygenInitialCommitments (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    simulateQ (fixedLocal prims h) (keygenInitialCommitments coalition parts) =
      pure (keygenFixedInitialCommitments prims coalition h parts) := by
  rw [keygenInitialCommitments, simulateQ_sequenceFin]
  trans Concrete.sequenceFin (fun i => (pure (keygenFixedInitialCommitments prims coalition h parts i) : ProbComp _))
  · congr 1
    funext i
    unfold keygenFixedInitialCommitments
    split_ifs
    · rfl
    · exact simulateQ_fixedLocal_liftComp (prims := prims) h _
  · exact sequenceFin_pure _

theorem keygenFixedInitialCommitments_inbox (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (sent : C.Party → Mail C E) :
    keygenCommitInbox coalition parts (keygenFixedInitialCommitments prims coalition h parts) sent =
      keygenCommitInbox coalition parts (fun j => D prims h (commitQueries .keygen j (parts j))) sent := by
  funext i j
  unfold keygenCommitInbox roundInbox
  by_cases hj : j ∈ coalition.1
  · simp only [if_pos hj]
  · simp only [if_neg hj, keygenInitialSteps, if_neg hj, keygenFixedInitialCommitments]

theorem keygenFixedInitialCommitments_view (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      commitOutbox (E := E) i (keygenFixedInitialCommitments prims coalition h parts i) c else none) =
      keygenFixedCommitView prims coalition h parts := by
  funext c i
  unfold keygenFixedCommitView
  by_cases hc : c ∈ coalition.1 ∧ i ∉ coalition.1
  · simp only [if_pos hc, keygenFixedInitialCommitments, if_neg hc.2]
  · simp only [if_neg hc]

/-- The whole normalized game equals the concrete reference with the actual hidden oracle
values. The sampling order of `A.start` and honest parts is exchanged only at the distribution level. -/
theorem evalDist_keygenNormalized_fixed_reference (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    𝒟[simulateQ (fixedLocal prims h) (keygenNormalizedLocalGame coalition A x z Z)] =
      𝒟[(do
        let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
        simulateQ (fixedLocal prims h)
          (keygenReferenceLocalGame prims coalition h (fun name => h (keygenNamedInput parts name)) A x z Z parts))] := by
  simp only [keygenNormalizedLocalGame, simulateQ_bind, simulateQ_sequenceFin,
    simulateQ_fixedLocal_private, simulateQ_fixedLocal_keygenInitialCommitments, pure_bind]
  rw [OracleComp.DeferredSampling.evalDist_bind_comm]
  apply evalDist_bind_congr'
  intro parts
  simp only [keygenReferenceLocalGame, simulateQ_bind]
  apply evalDist_bind_congr'
  intro state
  rw [keygenFixedInitialCommitments_view]
  apply evalDist_bind_congr'
  rintro ⟨st, sent⟩
  dsimp only
  rw [keygenFixedInitialCommitments_inbox,
    simulateQ_keygenPostCommit_reference prims coalition h (fun name => h (keygenNamedInput parts name))
      A st parts (fun _ _ => rfl) sent]

/-- Every complete local computation is a mixture of fixed finite oracle tables.
The envelope is a semantic device; its size is not used as a query bound. -/
theorem keygenLocal_eager_fixed_exists (prims : Primitives) {α : Type}
    (oa : OracleComp (LocalSpec C) α) :
    ∃ S : Finset (Query C),
      𝒟[(simulateQ (localAnswer prims) oa).run' ∅] =
        𝒟[do let h ← $ᵗ (S → HashOutput);
              simulateQ (fixedLocal prims (keygenFiniteTotal prims S h)) oa] := by
  obtain ⟨S, hS⟩ := keygenWorld_eager_exists prims (free oa)
  refine ⟨S, ?_⟩
  have he := hS ∅
  simp only [worldAnswer, keygenFiniteWorld, simulateQ_free] at he
  have hc : keygenRestrictCache S (∅ : HashCache C) = ∅ := rfl
  simp only [hc, keygenFiniteLocal_eager_fixed, tableExtending_empty] at he
  exact he

/-- End-to-end distributional connection from the actual real experiment to the finite
reference game. Its hidden table is still the actual oracle table, not an independent dealer. -/
theorem keygenReal_reference_exists (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    ∃ S : Finset (Query C),
      𝒟[(simulateQ (worldAnswer prims)
        (distinguish (realExecution coalition A noFunctionality setupRounds
          (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) Z)).run' ∅] =
        𝒟[do
          let ht ← $ᵗ (S → HashOutput);
          let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
          let h := keygenFiniteTotal prims S ht
          simulateQ (fixedLocal prims h)
            (keygenReferenceLocalGame prims coalition h (fun name => h (keygenNamedInput parts name)) A x z Z parts)] := by
  obtain ⟨S, hS⟩ := keygenLocal_eager_fixed_exists prims (keygenNormalizedLocalGame coalition A x z Z)
  refine ⟨S, ?_⟩
  rw [simulateQ_keygenReal_eq_local, (sameRun_keygenLocal_normalized prims coalition A x z Z).run'_eq, hS]
  apply evalDist_bind_congr'
  intro ht
  exact evalDist_keygenNormalized_fixed_reference prims coalition (keygenFiniteTotal prims S ht) A x z Z

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The vector of honest private parts has a finite type, despite its function fields. -/
theorem keygenParts_finite (C : Committee) : Finite (Parts C) := by
  apply Finite.of_injective (fun p : Parts C => (p.parameter, p.term, p.pair))
  intro p q hp
  cases p
  cases q
  simpa only [Prod.mk.injEq, Parts.mk.injEq] using hp

/-- All canonical named inputs, for every possible sampled parts vector. This finite set is
only an oracle domain; its cardinality never appears in the security estimate. -/
def keygenAllNamedInputs (C : Committee) : Finset (Query C) :=
  letI : Finite (Parts C) := keygenParts_finite C
  letI : Fintype (C.Party → Parts C) := Fintype.ofFinite _
  Finset.univ.biUnion fun parts : C.Party → Parts C =>
    (keygenNames C).toFinset.image (keygenNamedInput parts)

theorem keygenAllNamedInputs_mem (parts : C.Party → Parts C) (name : KeyName C) :
    keygenNamedInput parts name ∈ keygenAllNamedInputs C := by
  letI : Finite (Parts C) := keygenParts_finite C
  letI : Fintype (C.Party → Parts C) := Fintype.ofFinite _
  unfold keygenAllNamedInputs
  apply Finset.mem_biUnion.mpr
  refine ⟨parts, Finset.mem_univ _, Finset.mem_image.mpr ⟨name, ?_, rfl⟩⟩
  simp [keygenNames]

/-- Any requested finite set can be included in the eager oracle domain. -/
theorem keygenLocal_eager_fixed_exists_cover (prims : Primitives) (R : Finset (Query C))
    {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∃ S : Finset (Query C), R ⊆ S ∧
      𝒟[(simulateQ (localAnswer prims) oa).run' ∅] =
        𝒟[do let h ← $ᵗ (S → HashOutput);
              simulateQ (fixedLocal prims (keygenFiniteTotal prims S h)) oa] := by
  obtain ⟨S₀, hS₀⟩ := keygenWorldCovered_exists (free oa)
  let S := S₀ ∪ R
  have hS : KeygenWorldCovered S (free oa) := hS₀.mono (by intro q hq; exact Finset.mem_union_left R hq)
  refine ⟨S, (by intro q hq; exact Finset.mem_union_right S₀ hq), ?_⟩
  have he := evalDist_keygenWorld_eager prims S (free oa) hS ∅
  simp only [worldAnswer, keygenFiniteWorld, simulateQ_free] at he
  have hc : keygenRestrictCache S (∅ : HashCache C) = ∅ := rfl
  simp only [hc, keygenFiniteLocal_eager_fixed, tableExtending_empty] at he
  exact he

/-- The actual real experiment has a finite reference representation whose oracle includes
every canonical hidden input, even on branches where no honest operator reaches derivation. -/
theorem keygenReal_reference_exists_cover (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    ∃ S : Finset (Query C), (∀ parts name, keygenNamedInput parts name ∈ S) ∧
      𝒟[(simulateQ (worldAnswer prims)
        (distinguish (realExecution coalition A noFunctionality setupRounds
          (fun i (_ : Unit) => (keygen i : PartyM C E RealSpec (Keys C))) x z) Z)).run' ∅] =
        𝒟[do
          let ht ← $ᵗ (S → HashOutput);
          let parts ← Concrete.sequenceFin fun _ : C.Party => sampleParts (C := C)
          let h := keygenFiniteTotal prims S ht
          simulateQ (fixedLocal prims h)
            (keygenReferenceLocalGame prims coalition h (fun name => h (keygenNamedInput parts name)) A x z Z parts)] := by
  obtain ⟨S, hmem, hS⟩ := keygenLocal_eager_fixed_exists_cover prims (keygenAllNamedInputs C)
    (keygenNormalizedLocalGame coalition A x z Z)
  refine ⟨S, (fun parts name => hmem (keygenAllNamedInputs_mem parts name)), ?_⟩
  rw [simulateQ_keygenReal_eq_local, (sameRun_keygenLocal_normalized prims coalition A x z Z).run'_eq, hS]
  apply evalDist_bind_congr'
  intro ht
  exact evalDist_keygenNormalized_fixed_reference prims coalition (keygenFiniteTotal prims S ht) A x z Z

/-- A canonical input in the enlarged domain reads an actual sampled cell, never the fallback. -/
theorem keygenFiniteTotal_named (prims : Primitives) (S : Finset (Query C))
    (h : S → HashOutput) (parts : C.Party → Parts C) (name : KeyName C)
    (hn : keygenNamedInput parts name ∈ S) :
    keygenFiniteTotal prims S h (keygenNamedInput parts name) = h ⟨keygenNamedInput parts name, hn⟩ := by
  cases name <;>
    simp [keygenFiniteTotal, keygenNamedInput, parameterInput, termInput, pairInput] at hn ⊢ <;>
    simp [hn]

/-- On distinct canonical inputs, the sampled finite oracle induces a uniform
named table. This marginal statement does not assert independence from an adaptive transcript. -/
theorem evalDist_keygenFiniteNamed_uniform (prims : Primitives) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, keygenNamedInput parts name ∈ S)
    (hinj : Function.Injective (keygenNamedInput parts)) :
    𝒟[(fun h name => keygenFiniteTotal prims S h (keygenNamedInput parts name)) <$>
      ($ᵗ (S → HashOutput))] = 𝒟[$ᵗ (KeyName C → HashOutput)] := by
  let e : KeyName C → S := fun name => ⟨keygenNamedInput parts name, hmem name⟩
  have he : Function.Injective e := fun a b hab => hinj (congrArg Subtype.val hab)
  have ht : (fun (h : S → HashOutput) name => keygenFiniteTotal prims S h (keygenNamedInput parts name)) =
      (fun h : S → HashOutput => h ∘ e) := by
    funext h name
    exact keygenFiniteTotal_named prims S h parts name (hmem name)
  rw [ht, map_eq_bind_pure_comp]
  exact evalDist_uniformSample_map_comp_injective he

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- Exchange the finite oracle cells at canonical hidden inputs with the independent dealer
coordinates. Every other oracle cell and every exposed dealer coordinate stays fixed. -/
def keygenFiniteHiddenSwap (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, keygenNamedInput parts name ∈ S)
    (p : (S → HashOutput) × (KeyName C → HashOutput)) :
    (S → HashOutput) × (KeyName C → HashOutput) :=
  (fun q => if hh : KeygenHiddenInput coalition parts q.val then p.2 (Classical.choose hh) else p.1 q,
   fun name => if Hidden coalition name then p.1 ⟨keygenNamedInput parts name, hmem name⟩ else p.2 name)

theorem keygenFiniteHiddenSwap_cell (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, keygenNamedInput parts name ∈ S)
    (hinj : Function.Injective (keygenNamedInput parts))
    (p : (S → HashOutput) × (KeyName C → HashOutput)) (name : KeyName C) (hh : Hidden coalition name) :
    (keygenFiniteHiddenSwap coalition S parts hmem p).1 ⟨keygenNamedInput parts name, hmem name⟩ = p.2 name := by
  have hp : KeygenHiddenInput coalition parts (keygenNamedInput parts name) := ⟨name, hh, rfl⟩
  simp only [keygenFiniteHiddenSwap, dif_pos hp]
  have he : Classical.choose hp = name := hinj (Classical.choose_spec hp).2
  rw [he]

theorem keygenFiniteHiddenSwap_off (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, keygenNamedInput parts name ∈ S)
    (p : (S → HashOutput) × (KeyName C → HashOutput)) (q : S)
    (hq : ¬ KeygenHiddenInput coalition parts q.val) :
    (keygenFiniteHiddenSwap coalition S parts hmem p).1 q = p.1 q := by
  simp only [keygenFiniteHiddenSwap, dif_neg hq]

theorem keygenFiniteHiddenSwap_dealer_known (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, keygenNamedInput parts name ∈ S)
    (p : (S → HashOutput) × (KeyName C → HashOutput)) (name : KeyName C) (hh : ¬ Hidden coalition name) :
    (keygenFiniteHiddenSwap coalition S parts hmem p).2 name = p.2 name := by
  simp only [keygenFiniteHiddenSwap, if_neg hh]

/-- Distinct canonical names make the exchange between oracle and dealer an involution. -/
theorem keygenFiniteHiddenSwap_involutive (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, keygenNamedInput parts name ∈ S)
    (hinj : Function.Injective (keygenNamedInput parts)) :
    Function.Involutive (keygenFiniteHiddenSwap coalition S parts hmem) := by
  intro p
  apply Prod.ext
  · funext q
    by_cases hq : KeygenHiddenInput coalition parts q.val
    · obtain ⟨name, hh, he⟩ := hq
      have hq' : q = ⟨keygenNamedInput parts name, hmem name⟩ := Subtype.ext he.symm
      rw [hq', keygenFiniteHiddenSwap_cell coalition S parts hmem hinj _ name hh]
      simp only [keygenFiniteHiddenSwap, if_pos hh]
    · rw [keygenFiniteHiddenSwap_off coalition S parts hmem _ q hq,
        keygenFiniteHiddenSwap_off coalition S parts hmem _ q hq]
  · funext name
    by_cases hh : Hidden coalition name
    · change (if Hidden coalition name then
        (keygenFiniteHiddenSwap coalition S parts hmem p).1 ⟨keygenNamedInput parts name, hmem name⟩
        else (keygenFiniteHiddenSwap coalition S parts hmem p).2 name) = p.2 name
      rw [if_pos hh, keygenFiniteHiddenSwap_cell coalition S parts hmem hinj p name hh]
    · rw [keygenFiniteHiddenSwap_dealer_known coalition S parts hmem _ name hh,
        keygenFiniteHiddenSwap_dealer_known coalition S parts hmem _ name hh]

/-- The complete joint law of the eager oracle and independent dealer is preserved. -/
theorem evalDist_keygenFiniteHiddenSwap (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, keygenNamedInput parts name ∈ S)
    (hinj : Function.Injective (keygenNamedInput parts)) :
    𝒟[keygenFiniteHiddenSwap coalition S parts hmem <$>
      ($ᵗ ((S → HashOutput) × (KeyName C → HashOutput)))] =
      𝒟[$ᵗ ((S → HashOutput) × (KeyName C → HashOutput))] :=
  evalDist_map_bijective_uniform_cross _ _ (keygenFiniteHiddenSwap_involutive coalition S parts hmem hinj).bijective

/-- The total oracles agree away from canonical hidden inputs, including all fixed Th calls. -/
theorem keygenFiniteHiddenSwap_total_off (prims : Primitives) (coalition : C.Coalition)
    (S : Finset (Query C)) (parts : C.Party → Parts C)
    (hmem : ∀ name, keygenNamedInput parts name ∈ S)
    (p : (S → HashOutput) × (KeyName C → HashOutput)) (q : Query C)
    (hq : ¬ KeygenHiddenInput coalition parts q) :
    keygenFiniteTotal prims S (keygenFiniteHiddenSwap coalition S parts hmem p).1 q =
      keygenFiniteTotal prims S p.1 q := by
  have he (hm : q ∈ S) :
      (keygenFiniteHiddenSwap coalition S parts hmem p).1 ⟨q, hm⟩ = p.1 ⟨q, hm⟩ :=
    keygenFiniteHiddenSwap_off coalition S parts hmem p _ hq
  cases q <;> simp only [keygenFiniteTotal] <;> split_ifs <;> first | apply he | rfl

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

variable {C : Committee} {E : Type} (prims : Primitives)

end ThresholdLeanXmssSecurity
