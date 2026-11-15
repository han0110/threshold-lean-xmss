import ThresholdLeanXmssSecurity.Proof.Execution
import ThresholdLeanXmssSecurity.Proof.Lemmas
import VCVio.EvalDist.List
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import Common.CostCombinators
import XmssSecurity.Proof.EvalDistEq

/-!
# The seed generation

`SeedGenCompletenessStatement` follows from the honest run of `seedGen`. `SeedGenSecurityStatement`
reduces to `SeedGenCoupling`. `seedGenSimulator_queryBound` gives the query half. The
supporting lemmas concern `SeedGenCoupling` (CDG+18).
-/

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

/-! ## The seed generation and the setup of a ceremony -/

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
  (if phase = .seedGen then [keys.1] else []) ++ [shared.getD j.val 0]

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
    (honestView (E := E) .seedGen parts x k).parameter = (parts k).parameter := by
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
      (if phase = .seedGen then h (.derive phase .parameter (C.parties.map fun j => (view j).parameter)) else 0,
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

/-- The input of the derivation of `P` in an honest seed generation. -/
def parameterInput (parts : C.Party → Parts C) : Query C :=
  .derive .seedGen .parameter (C.parties.map fun j => (parts j).parameter)

/-- The input of the derivation of the key of term `T` in an honest setup. -/
def termInput (phase : Phase) (parts : C.Party → Parts C) (T : C.Term) : Query C :=
  .derive phase .term ((C.parties.filter (· ∈ C.holders T)).map fun j => (parts j).term T)

/-- The input of the derivation of the key of pair `p` in an honest setup. -/
def pairInput (phase : Phase) (parts : C.Party → Parts C) (p : C.Pair) : Query C :=
  .derive phase .pair [(parts p.1.1).pair p.1.2, (parts p.1.2).pair p.1.1]

theorem D_deriveKeys_honest (h : Query C → HashOutput) (phase : Phase) (parts : C.Party → Parts C) (i : C.Party) :
    D prims h (deriveKeys phase i (honestView (E := E) phase parts i)) =
      (if phase = .seedGen then h (parameterInput parts) else 0,
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

section SeedGenRun

variable {C : Committee} {E : Type} (prims : Primitives)

/-- The keys of an operator from the keys that its seed generation derives. -/
def keysOf (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) : Keys C :=
  ⟨truncateHash keys.1, keys.2.1, keys.2.2⟩

/-- The seed generation of operator `i` after the commit round. -/
def seedGenRound1 (i : C.Party) (own : Parts C) : Mail C E → PartyM C E RealSpec (Keys C) := fun committed =>
  exchange (revealOutbox .seedGen i own) >>= fun revealed =>
    setupRest .seedGen i own committed revealed >>= fun keys => pure (keysOf keys)

/-- The step of operator `i` after the start of its seed generation. -/
def seedGenStart (i : C.Party) (own : Parts C) (commitments : List HashOutput) : Step C E RealSpec (Keys C) :=
  .wait (commitOutbox i commitments) (exchangeResume (seedGenRound1 i own))

theorem advance_seedGen (i : C.Party) :
    advance (seedGen i : PartyM C E RealSpec (Keys C)).run =
      liftComp sampleParts (LocalSpec C) >>= fun own =>
        liftComp (commitQueries .seedGen i own) (LocalSpec C) >>= fun commitments =>
          pure (seedGenStart i own commitments) := by
  have : (seedGen i : PartyM C E RealSpec (Keys C)) =
      localStep (liftComp sampleParts _) >>= fun own =>
        commitRevealEcho .seedGen i own >>= fun keys => pure (keysOf keys) := rfl
  rw [this, advance_localStep_bind]
  refine bind_congr fun own => ?_
  rw [advance_setup_start]
  rfl

/-- The seed generation after the parts, from the commitments on. -/
def seedGenRest (parts : C.Party → Parts C) : OracleComp (LocalSpec C) (C.Party → Option (Keys C)) := do
  let commitments ← OverPermutation.sequenceFin fun j => liftComp (commitQueries .seedGen j (parts j)) (LocalSpec C)
  honestRounds noFunctionality (fun l => l.elim) setupRounds fun j => seedGenStart (E := E) j (parts j) (commitments j)

/-- The honest seed generation samples all parts first. -/
theorem sameRun_seedGen :
    SameRun prims (honestStart (fun i => (seedGen i : PartyM C E RealSpec (Keys C))) >>=
        honestRounds noFunctionality (fun l => l.elim) setupRounds)
      (OverPermutation.sequenceFin (fun _ => liftComp sampleParts (LocalSpec C)) >>= seedGenRest (E := E)) := by
  unfold honestStart seedGenRest
  simp only [advance_seedGen]
  refine (sameRun_sequenceFin_dep prims _ _ (fun j own commitments => seedGenStart (E := E) j own commitments)).bind
    (fun steps => SameRun.refl prims _) |>.trans ?_
  simp only [bind_assoc, pure_bind]
  exact SameRun.refl prims _

/-- The keys of operator `i` in an honest seed generation with `H` fixed to `h`. -/
def honestKeys (h : Query C → HashOutput) (parts : C.Party → Parts C) (i : C.Party) : Keys C :=
  ⟨truncateHash (h (parameterInput parts)), fun T => if i ∈ C.holders T then h (termInput .seedGen parts T) else 0,
    fun j => if hj : j = i then 0 else h (pairInput .seedGen parts (C.pairOf i j (Ne.symm hj)))⟩

theorem honestRounds_wait {I O L R α : Type} (F : Functionality C I O L R) (reply : L → R) (fuel : ℕ)
    (outbox : C.Party → Mail C E) (f : C.Party → Mail C E → PartyM C E (CallSpec I O) α) :
    honestRounds F reply (fuel + 1) (fun i => .wait (outbox i) (exchangeResume (f i))) =
      OverPermutation.sequenceFin (fun j => advance (exchangeResume (f j) fun k => outbox k j)) >>=
        honestRounds F reply fuel := by
  rw [honestRounds_succ, honestStep_exchange]
  exact fun h => (h (firstParty C) : False)

theorem keysOf_honest (h : Query C → HashOutput) (parts : C.Party → Parts C) (i : C.Party) :
    keysOf (D prims h (deriveKeys .seedGen i (honestView (E := E) .seedGen parts i))) = honestKeys h parts i := by
  rw [D_deriveKeys_honest]
  rfl

/-- The seed generation with `H` fixed gives the honest keys to every operator. -/
theorem simulateQ_fixedLocal_seedGenRest (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    simulateQ (fixedLocal prims h) (seedGenRest (E := E) parts) = pure fun i => some (honestKeys h parts i) := by
  set keys := fun x => D prims h (deriveKeys .seedGen x (honestView (E := E) .seedGen parts x)) with hk
  set shared := fun x => D prims h (sharedQueries .seedGen x (keys x)) with hs
  have h1 : ∀ j, advance (exchangeResume (seedGenRound1 (E := E) j (parts j)) fun k => commitOutbox k (D prims h (commitQueries .seedGen k (parts k))) j) =
      pure (.wait (revealOutbox .seedGen j (parts j)) (exchangeResume fun revealed =>
        setupRest .seedGen j (parts j) (fun k => commitOutbox k (D prims h (commitQueries .seedGen k (parts k))) j) revealed >>=
          fun keys => pure (keysOf keys))) := by
    intro j
    rw [exchangeResume_of_no_abort _ _ fun k => isAbort_commitOutbox k _ j]
    exact advance_setup_reveal _ _ _ _
  have h2 : ∀ j, simulateQ (fixedLocal prims h) (advance (exchangeResume (fun revealed =>
        setupRest (G := RealSpec) .seedGen j (parts j) (fun k => commitOutbox (E := E) k (D prims h (commitQueries .seedGen k (parts k))) j) revealed >>=
          fun keys => pure (keysOf keys)) fun k => revealOutbox .seedGen k (parts k) j)) =
      pure (Step.wait (G := RealSpec) (echoOutbox .seedGen j (keys j) (shared j)) (exchangeResume fun received =>
        require (echoCheck .seedGen j (keys j) (shared j) received) >>= fun _ => pure (keysOf (keys j)))) := by
    intro j
    rw [exchangeResume_of_no_abort _ _ fun k => isAbort_revealOutbox _ k _ j, advance_setupRest, simulateQ_bind,
      simulateQ_fixedLocal_liftComp, pure_bind]
    split_ifs with hcheck
    · rw [simulateQ_bind, simulateQ_fixedLocal_liftComp, pure_bind,
        simulateQ_bind, simulateQ_fixedLocal_liftComp, pure_bind, simulateQ_pure]
      rfl
    · exact absurd (openCheck_honest prims h .seedGen parts j) hcheck
  have h3 : ∀ j, simulateQ (fixedLocal prims h) (advance (exchangeResume (fun received =>
        require (echoCheck .seedGen j (keys j) (shared j) received) >>= fun _ => pure (keysOf (keys j)))
          fun k => echoOutbox (E := E) .seedGen k (keys k) (shared k) j)) =
      pure (Step.done (G := RealSpec) (some (honestKeys h parts j))) := by
    intro j
    rw [exchangeResume_of_no_abort _ _ fun k => isAbort_echoOutbox _ k _ _ j, advance_require_bind]
    split_ifs with hcheck
    · rw [advance_run_pure, simulateQ_pure, hk, keysOf_honest]
    · exact absurd (echoCheck_honest prims h .seedGen parts j) hcheck
  unfold seedGenRest
  rw [simulateQ_bind, simulateQ_sequenceFin]
  simp only [simulateQ_fixedLocal_liftComp]
  rw [sequenceFin_pure, pure_bind]
  show simulateQ _ (honestRounds _ _ (2 + 1) _) = _
  unfold seedGenStart
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
    (simulateQ (localAnswer prims) (W >>= fun _ => X)).run' s =ᵈ (simulateQ (localAnswer prims) X).run' s := by
  have hswap := sameRun_swap prims W X (fun _ x => pure x) s
  simp only [bind_pure] at hswap
  rw [StateT.run'_eq, StateT.run'_eq]
  refine (hswap.map _).trans ?_
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  rw [← StateT.run'_eq, StateT.run'_eq, map_eq_bind_pure_comp]
  refine OracleComp.EvalDistEq.bind_congr_of_support _ fun p _ => ?_
  exact evalDist_eq_pure_of_support _ _ fun y hy => by
    simp at hy
    exact hy.2.symm

/-- The bind of local computations from a cache, with continuations of the same output on every
reachable result and cache. -/
theorem evalDist_run'_bind_congr {α β : Type} (m : OracleComp (LocalSpec C) β) (f g : β → OracleComp (LocalSpec C) α)
    (s : HashCache C)
    (h : ∀ p ∈ support ((simulateQ (localAnswer prims) m).run s),
      (simulateQ (localAnswer prims) (f p.1)).run' p.2 =ᵈ (simulateQ (localAnswer prims) (g p.1)).run' p.2) :
    (simulateQ (localAnswer prims) (m >>= f)).run' s =ᵈ (simulateQ (localAnswer prims) (m >>= g)).run' s := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  exact OracleComp.EvalDistEq.bind_congr_of_support _ fun p hp => by simpa [StateT.run'_eq] using h p hp

/-- All pairs, in one fixed order. -/
def pairList (C : Committee) : List C.Pair := (Finset.univ : Finset C.Pair).toList

/-- The derivations of an honest seed generation, namely `P`, the key of each term and the key of each pair. -/
def seedGenInputs (parts : C.Party → Parts C) : List (Query C) :=
  parameterInput parts :: (C.terms.map (termInput .seedGen parts) ++ (pairList C).map (pairInput .seedGen parts))

/-- The derivations of an honest seed generation, queried in a fixed order. -/
def seedGenDerivations (parts : C.Party → Parts C) : OracleComp (LocalSpec C) (List HashOutput) :=
  liftComp ((seedGenInputs parts).mapM hashQuery) (LocalSpec C)

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
    keysFromValues ((seedGenInputs parts).map h) i = honestKeys h parts i := by
  have hT : ∀ T, (C.terms.map (h ∘ termInput .seedGen parts) ++ (pairList C).map (h ∘ pairInput .seedGen parts)).getD
      (C.terms.idxOf T) 0 = h (termInput .seedGen parts T) := by
    intro T
    have hT : T ∈ C.terms := Finset.mem_toList.mpr (Finset.mem_univ T)
    have hlt := List.idxOf_lt_length_of_mem hT
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using hlt), ← List.getD_eq_getElem?_getD]
    exact getD_terms_idxOf (h ∘ termInput .seedGen parts) 0 T
  have hp : ∀ p, (C.terms.map (h ∘ termInput .seedGen parts) ++ (pairList C).map (h ∘ pairInput .seedGen parts)).getD
      (C.terms.length + (pairList C).idxOf p) 0 = h (pairInput .seedGen parts p) := by
    intro p
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp only [List.length_map, Nat.add_sub_cancel_left]
    rw [← List.getD_eq_getElem?_getD]
    exact getD_pairList_idxOf (h ∘ pairInput .seedGen parts) 0 p
  unfold keysFromValues honestKeys seedGenInputs
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

theorem simulateQ_fixedLocal_seedGenDerivations (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    simulateQ (fixedLocal prims h) (seedGenDerivations parts) = pure ((seedGenInputs parts).map h) := by
  rw [seedGenDerivations, simulateQ_fixedLocal_liftComp, D_mapM]
  simp [D_hashQuery]

/-- The honest seed generation gives the keys from fresh derivations. -/
theorem evalDist_seedGen_derivations :
    (simulateQ (localAnswer prims) (OverPermutation.sequenceFin (fun _ => liftComp sampleParts (LocalSpec C)) >>=
        seedGenRest (E := E))).run' ∅ =ᵈ
      (simulateQ (localAnswer prims) (OverPermutation.sequenceFin (fun _ => liftComp sampleParts (LocalSpec C)) >>=
        fun parts => seedGenDerivations parts >>= fun values => pure fun i => some (keysFromValues values i))).run' ∅ := by
  refine (evalDist_run'_bind_congr prims _ (seedGenRest (E := E))
    (fun parts => seedGenDerivations parts >>= fun _ => seedGenRest (E := E) parts) ∅
    fun p _ => (evalDist_run'_prepend prims (seedGenDerivations p.1) _ _).symm).trans ?_
  refine evalDist_run'_bind_congr prims _ (fun parts => seedGenDerivations parts >>= fun _ => seedGenRest (E := E) parts)
    (fun parts => seedGenDerivations parts >>= fun values => pure fun i => some (keysFromValues values i)) ∅
    fun p hp => ?_
  refine evalDist_run'_bind_congr prims (seedGenDerivations p.1) (fun _ => seedGenRest (E := E) p.1)
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
  rw [simulateQ_fixedLocal_seedGenRest, support_pure, Set.mem_singleton_iff] at hk
  rw [simulateQ_fixedLocal_seedGenDerivations, support_pure, Set.mem_singleton_iff] at hv
  show z.1 = fun i => some (keysFromValues q.1 i)
  rw [hk, hv]
  funext i
  rw [keysFromValues_map]

/-- Distinct fresh inputs of `H` give independent uniform outputs. -/
theorem evalDist_fresh_mapM (qs : List (Query C)) :
    ∀ (s : HashCache C), qs.Nodup → (∀ q ∈ qs, s q = none) → (∀ q ∈ qs, ¬ IsFixed q) →
      (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (qs.mapM hashQuery)).run' s =ᵈ
        (qs.mapM fun _ => $ᵗ HashOutput) := by
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
    refine EvalDistEq.bind_right _ fun u => ?_
    simp only [StateT.run_bind, map_bind, StateT.run_pure, map_pure]
    have hne : ∀ q' ∈ qs, q' ≠ q := fun q' hq' e => hnd.1 (e ▸ hq')
    have := ih (s.cacheQuery q u) hnd.2 (fun q' hq' => by
        rw [QueryCache.cacheQuery_of_ne _ _ (hne q' hq')]
        exact hfresh q' (List.mem_cons_of_mem _ hq'))
      fun q' hq' => hfix q' (List.mem_cons_of_mem _ hq')
    rw [StateT.run'_eq] at this
    have e1 : ((simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (qs.mapM hashQuery)).run
        (s.cacheQuery q u) >>= fun p => pure (u :: p.1)) = (fun l => u :: l) <$> ((fun p => p.1) <$>
          (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) (qs.mapM hashQuery)).run
            (s.cacheQuery q u)) := by
      rw [Functor.map_map, map_eq_bind_pure_comp]; rfl
    have e2 : (qs.mapM (fun _ => $ᵗ HashOutput) >>= fun l => pure (u :: l)) =
        (fun l => u :: l) <$> qs.mapM (fun _ => $ᵗ HashOutput) := by
      rw [map_eq_bind_pure_comp]; rfl
    rw [e1, e2]
    exact this.map _

theorem run'_localAnswer_liftComp {α : Type} (p : ProbComp α) (s : HashCache C) :
    (simulateQ (localAnswer prims) (liftComp p (LocalSpec C))).run' s = p := by
  rw [show simulateQ (localAnswer prims) (liftComp p (LocalSpec C)) =
      simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p from
    QueryImpl.simulateQ_add_liftComp_left (unifFwdImpl (Query C →ₒ HashOutput)) _ p]
  rw [StateT.run'_eq, unifFwdImpl.simulateQ_run, Functor.map_map]
  simp

/-- The ideal seed generation with the honest replies gives the keys of `KeyGen'` to every operator. -/
theorem seedGen_ideal :
    (simulateQ (localAnswer prims) (simulateQ (replyImpl (fun _ => (Finset.univ : Finset C.Party)))
        ((FseedGen (C := C)).run noCoalition fun _ => some ()))).run' ∅ =
      (fun r i => some (r.2.2 i)) <$> prawnsKeyGen (C := C) := by
  have : simulateQ (replyImpl (C := C) (fun _ => (Finset.univ : Finset C.Party)))
      ((FseedGen (C := C)).run noCoalition fun _ => some ()) =
        liftComp ((fun r i => some (r.2.2 i)) <$> prawnsKeyGen (C := C)) (LocalSpec C) := by
    unfold FseedGen
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
    liftComp (OverPermutation.sequenceFin f) (LocalSpec C) = OverPermutation.sequenceFin fun i => liftComp (f i) (LocalSpec C) :=
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

/-- The real seed generation as a computation that samples the parts and then queries the derivations. -/
theorem seedGen_real :
    (simulateQ (localAnswer prims) (OverPermutation.sequenceFin (fun _ => liftComp sampleParts (LocalSpec C)) >>=
        fun parts => seedGenDerivations parts >>= fun values => pure fun i => some (keysFromValues values i))).run' ∅ =
      OverPermutation.sequenceFin (fun _ => sampleParts (C := C)) >>= fun parts =>
        (fun values (i : C.Party) => some (keysFromValues (C := C) values i)) <$>
          (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) ((seedGenInputs parts).mapM hashQuery)).run' ∅ := by
  rw [← liftComp_sequenceFin, run'_localAnswer_liftComp_bind]
  refine bind_congr fun parts => ?_
  rw [seedGenDerivations, simulateQ_bind, simulateQ_localAnswer_liftComp, StateT.run'_eq, StateT.run'_eq,
    StateT.run_bind, map_bind, Functor.map_map]
  simp only [simulateQ_pure, StateT.run_pure, map_pure]
  rw [map_eq_bind_pure_comp]
  rfl

end SeedGenRun

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

section Uniform

/-- A computation whose outputs all have one probability is uniform. -/
theorem evalDist_eq_uniform_of_probOutput_eq {β : Type} [Fintype β] [SampleableType β] (mx : ProbComp β)
    (h : ∀ x y, Pr{let z ← mx}[z = x] = Pr{let z ← mx}[z = y]) : mx =ᵈ $ᵗ β := by
  refine OracleComp.evalDistEq_of_forall_prEvent_eq_output fun x => ?_
  rw [SampleableType.prEvent_uniformSample_eq_singleton]
  have hsum := OracleComp.tsum_prEvent_eq_one mx
  rw [tsum_fintype, Finset.sum_congr rfl (fun y _ => h y x), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hsum)

theorem xor_bijective {n : ℕ} (c : BitVec n) : Function.Bijective fun y : BitVec n => y ^^^ c :=
  Function.Involutive.bijective (fun y => by simp [BitVec.xor_assoc])

theorem truncateHash_xor (y : HashOutput) (c : Digest) :
    truncateHash (y ^^^ c.setWidth 256) = truncateHash y ^^^ c := by
  unfold truncateHash
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
  simp [hi, show i < 256 by unfold digestBits at hi; omega]

/-- The first 128 bits of a uniform hash output are uniform. -/
theorem evalDist_truncateHash :
    (truncateHash <$> ($ᵗ HashOutput) : ProbComp Digest) =ᵈ $ᵗ Digest := by
  refine evalDist_eq_uniform_of_probOutput_eq _ fun x y => ?_
  have hU : ((fun z => z ^^^ (x ^^^ y).setWidth 256) <$> ($ᵗ HashOutput)) =ᵈ $ᵗ HashOutput :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective (xor_bijective _)
  have hshift : (truncateHash <$> ($ᵗ HashOutput) : ProbComp Digest) =ᵈ
      ((fun d => d ^^^ (x ^^^ y)) <$> (truncateHash <$> ($ᵗ HashOutput) : ProbComp Digest)) :=
    calc (truncateHash <$> ($ᵗ HashOutput) : ProbComp Digest)
        =ᵈ (truncateHash <$> ((fun z => z ^^^ (x ^^^ y).setWidth 256) <$> ($ᵗ HashOutput)) : ProbComp Digest) :=
          (hU.map _).symm
      _ = _ := by
          rw [Functor.map_map, Functor.map_map]
          congr 2
          funext z
          exact truncateHash_xor z _
  have hx : x = y ^^^ (x ^^^ y) := by
    rw [BitVec.xor_comm x y, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  have key := prEvent_map_injective (truncateHash <$> ($ᵗ HashOutput) : ProbComp Digest)
    (xor_bijective (x ^^^ y)).1 y
  rw [← hx] at key
  exact (hshift.prEvent_eq _).trans key

/-- A list of uniform values, read as a function through an index, is a uniform function. -/
theorem evalDist_listFunction {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [SampleableType β] [SampleableType (α → β)]
    (L : List α) (idx : α → ℕ) (d : β) (hlen : L.length = Fintype.card α)
    (h1 : ∀ f : α → β, (fun a => (L.map f).getD (idx a) d) = f)
    (h2 : ∀ l : List β, l.length = L.length → L.map (fun a => l.getD (idx a) d) = l) :
    ((fun l a => l.getD (idx a) d) <$> L.mapM (fun _ => $ᵗ β)) =ᵈ $ᵗ (α → β) := by
  refine OracleComp.evalDistEq_of_forall_prEvent_eq_output fun f => ?_
  rw [prEvent_map, SampleableType.prEvent_uniformSample_eq_singleton, Fintype.card_fun, ← hlen]
  have hlen' : ∀ l ∈ support (L.mapM fun _ => $ᵗ β), l.length = L.length :=
    Common.length_of_mem_support_mapM _ L
  have hpoint : ∀ ys : List β, ys.length = L.length →
      Pr{let l ← L.mapM fun _ => $ᵗ β}[l = ys] = (Fintype.card β : ENNReal)⁻¹ ^ L.length := by
    clear hlen hlen' h1 h2
    induction L with
    | nil =>
      intro ys hys
      rw [List.length_nil, List.length_eq_zero_iff] at hys
      subst hys
      simp
    | cons a L ih =>
      intro ys hys
      rcases ys with _ | ⟨y, ys⟩
      · simp at hys
      rw [List.mapM_cons, OracleComp.prEvent_bind_eq_mul_of_unique _ _ y _ fun x' _ hx' => by
          simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hx'
          obtain ⟨xs, -, hxs⟩ := hx'
          exact (List.cons.inj hxs).1.symm,
        SampleableType.prEvent_uniformSample_eq_singleton, bind_pure_comp,
        prEvent_map_injective _ (List.cons_injective) ys, ih ys (by simpa using hys), List.length_cons,
        pow_succ, mul_comm]
  rw [prEvent_congr_of_support _ _ (fun l => l = L.map f) fun l hl => ⟨fun e => by
        rw [← h2 l (hlen' l hl), e], fun e => by rw [e, h1]⟩, hpoint _ (by simp)]
  rw [Nat.cast_pow, ENNReal.inv_pow]

end Uniform

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section Collision

open scoped ENNReal

variable {C : Committee}

theorem evalDist_sequenceFin_congr {α : Type} :
    ∀ {n : ℕ} (f g : Fin n → ProbComp α), (∀ i, f i =ᵈ g i) →
      OverPermutation.sequenceFin f =ᵈ OverPermutation.sequenceFin g
  | 0, f, g, _ => by simp only [OverPermutation.sequenceFin, EvalDistEq.refl]
  | n + 1, f, g, h => by
    simp only [OverPermutation.sequenceFin]
    exact (h 0).bind fun a => (evalDist_sequenceFin_congr _ _ fun i => h i.succ).bind_left _

/-- The parts of one operator with one coordinate shifted. -/
def shiftParts (own : Parts C) (term : Option C.Term) (pair : Option C.Party) (c : HashOutput) : Parts C :=
  ⟨own.parameter, fun T => if term = some T then own.term T ^^^ c else own.term T,
    fun j => if pair = some j then own.pair j ^^^ c else own.pair j⟩

theorem evalDist_shift_sampleParts (term : Option C.Term) (pair : Option C.Party) (c : HashOutput) :
    ((fun own => shiftParts own term pair c) <$> sampleParts (C := C)) =ᵈ sampleParts (C := C) := by
  have hterm : ((fun t (T : C.Term) => if term = some T then t T ^^^ c else t T) <$> ($ᵗ (C.Term → HashOutput))) =ᵈ
      $ᵗ (C.Term → HashOutput) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective (Function.Involutive.bijective fun t => by
      funext T; by_cases hT : term = some T <;> simp [hT, BitVec.xor_assoc])
  have hpair : ((fun p (j : C.Party) => if pair = some j then p j ^^^ c else p j) <$> ($ᵗ (C.Party → HashOutput))) =ᵈ
      $ᵗ (C.Party → HashOutput) :=
    SampleableType.map_uniformSample_evalDistEq_of_bijective (Function.Involutive.bijective fun p => by
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
  exact EvalDistEq.bind_right _ fun parameter => hterm.bind fun t => hpair.bind_left _

/-- The parts of all operators with one coordinate of operator `a` shifted. -/
def shiftAt (a : C.Party) (term : Option C.Term) (pair : Option C.Party) (c : HashOutput)
    (parts : C.Party → Parts C) : C.Party → Parts C :=
  fun i => if i = a then shiftParts (parts i) term pair c else parts i

theorem evalDist_shiftAt (a : C.Party) (term : Option C.Term) (pair : Option C.Party) (c : HashOutput) :
    (shiftAt a term pair c <$> OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))) =ᵈ
      OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C)) := by
  have h := sequenceFin_bind_pure (m := ProbComp) (fun _ : C.Party => sampleParts (C := C))
    (fun i own => if i = a then shiftParts own term pair c else own)
  rw [map_eq_bind_pure_comp]
  have : (pure ∘ shiftAt a term pair c : (C.Party → Parts C) → ProbComp (C.Party → Parts C)) =
      fun rs => pure fun i => if i = a then shiftParts (rs i) term pair c else rs i := rfl
  rw [this, ← h]
  refine evalDist_sequenceFin_congr _ _ fun i => ?_
  by_cases hi : i = a
  · simp only [hi, if_true]
    rw [bind_pure_comp]
    exact evalDist_shift_sampleParts _ _ _
  · simp only [hi, if_false, bind_pure, EvalDistEq.refl]

/-- Two different coordinates of the parts collide with probability `2^-256`. -/
theorem probEvent_parts_collision (X Y : (C.Party → Parts C) → HashOutput) (a : C.Party) (term : Option C.Term)
    (pair : Option C.Party) (hX : ∀ c parts, X (shiftAt a term pair c parts) = X parts ^^^ c)
    (hY : ∀ c parts, Y (shiftAt a term pair c parts) = Y parts) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[X parts = Y parts] =
      (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have huniform : ((fun parts => X parts ^^^ Y parts) <$>
      OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))) =ᵈ $ᵗ HashOutput := by
    refine evalDist_eq_uniform_of_probOutput_eq _ fun u v => ?_
    have hshift : ((fun parts => X parts ^^^ Y parts) <$>
          OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))) =ᵈ
        ((fun d => d ^^^ (u ^^^ v)) <$> ((fun parts => X parts ^^^ Y parts) <$>
          OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C)))) :=
      calc ((fun parts => X parts ^^^ Y parts) <$>
            OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C)) : ProbComp HashOutput)
          =ᵈ ((fun parts => X parts ^^^ Y parts) <$> (shiftAt a term pair (u ^^^ v) <$>
              OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))) : ProbComp HashOutput) :=
            ((evalDist_shiftAt a term pair (u ^^^ v)).map _).symm
        _ = _ := by
            rw [Functor.map_map, Functor.map_map]
            congr 2
            funext parts
            simp only [hX, hY, BitVec.xor_assoc, BitVec.xor_comm (u ^^^ v) (Y parts)]
    have hu : u = v ^^^ (u ^^^ v) := by
      rw [BitVec.xor_comm u v, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    have key := prEvent_map_injective ((fun parts => X parts ^^^ Y parts) <$>
      OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))) (xor_bijective (u ^^^ v)).1 v
    rw [← hu] at key
    exact (hshift.prEvent_eq _).trans key
  have : Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[X parts = Y parts] =
      Pr{let z ← (fun parts => X parts ^^^ Y parts) <$> OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[z = 0] := by
    rw [prEvent_map]
    exact prEvent_congr _ _ _ fun parts => BitVec.xor_eq_zero_iff.symm
  rw [this, huniform.prEvent_eq, SampleableType.prEvent_uniformSample_eq_singleton]

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

theorem nodup_seedGenInputs (parts : C.Party → Parts C)
    (hT : ∀ T T', termInput .seedGen parts T = termInput .seedGen parts T' → T = T')
    (hp : ∀ p p', pairInput .seedGen parts p = pairInput .seedGen parts p' → p = p') : (seedGenInputs parts).Nodup := by
  unfold seedGenInputs
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
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      T ≠ T' ∧ termInput .seedGen parts T = termInput .seedGen parts T'] ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  by_cases hTT : T = T'
  · simp [hTT]
  obtain ⟨a, rest, ha⟩ := exists_first_holder T
  obtain ⟨b, rest', hb⟩ := exists_first_holder T'
  calc _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
        (parts a).term T = (parts b).term T'] := by
        refine prEvent_mono _ _ _ fun parts h => ?_
        have := h.2
        simp only [termInput, ha, hb, List.map_cons, Query.derive.injEq, true_and, List.cons.injEq] at this
        exact this.1
    _ = _ := probEvent_parts_collision (fun parts => (parts a).term T) (fun parts => (parts b).term T') a (some T)
        none (fun c parts => by simp [shiftAt, shiftParts]) (fun c parts => by
          by_cases hba : b = a <;> simp [shiftAt, shiftParts, hba, hTT])

theorem probEvent_pairInput_eq (p p' : C.Pair) :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
      p ≠ p' ∧ pairInput .seedGen parts p = pairInput .seedGen parts p'] ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  by_cases hpp : p = p'
  · simp [hpp]
  calc _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
        (parts p.1.1).pair p.1.2 = (parts p'.1.1).pair p'.1.2] := by
        refine prEvent_mono _ _ _ fun parts h => ?_
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
theorem probEvent_seedGen_collision :
    Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[¬ (seedGenInputs parts).Nodup] ≤
      ((Fintype.card C.Term ^ 2 + Fintype.card C.Pair ^ 2 : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  calc _ ≤ Pr{let parts ← OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))}[
        (∃ T ∈ Finset.univ, ∃ T' ∈ Finset.univ,
          T ≠ T' ∧ termInput .seedGen parts T = termInput .seedGen parts T') ∨
        (∃ p ∈ Finset.univ, ∃ p' ∈ Finset.univ, p ≠ p' ∧ pairInput .seedGen parts p = pairInput .seedGen parts p')] := by
        refine prEvent_mono _ _ _ fun parts hbad => ?_
        by_contra hgood
        push_neg at hgood
        exact hbad (nodup_seedGenInputs parts (fun T T' h => by_contra fun hne => hgood.1 T (by simp) T' (by simp) hne h)
          fun p p' h => by_contra fun hne => hgood.2 p (by simp) p' (by simp) hne h)
    _ ≤ _ := prEvent_or_le _ _ _
    _ ≤ (∑ T : C.Term, ∑ T' : C.Term, (Fintype.card HashOutput : ℝ≥0∞)⁻¹) +
        ∑ p : C.Pair, ∑ p' : C.Pair, (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
        gcongr
        · refine (prEvent_exists_finset_le _ _ _).trans (Finset.sum_le_sum fun T _ => ?_)
          exact (prEvent_exists_finset_le _ _ _).trans (Finset.sum_le_sum fun T' _ => probEvent_termInput_eq T T')
        · refine (prEvent_exists_finset_le _ _ _).trans (Finset.sum_le_sum fun p _ => ?_)
          exact (prEvent_exists_finset_le _ _ _).trans (Finset.sum_le_sum fun p' _ => probEvent_pairInput_eq p p')
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

end Collision

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section SeedGenCompleteness

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
    ((fun values (i : C.Party) => some (keysFromValues values i)) <$>
        (seedGenInputs parts).mapM (fun _ => $ᵗ HashOutput)) =ᵈ
      ((fun r (i : C.Party) => some (r.2.2 i)) <$> prawnsKeyGen (C := C)) := by
  have hterms : ((fun (l : List HashOutput) (T : C.Term) => l.getD (C.terms.idxOf T) 0) <$>
      C.terms.mapM (fun _ => $ᵗ HashOutput)) =ᵈ $ᵗ (C.Term → HashOutput) :=
    evalDist_listFunction C.terms (C.terms.idxOf ·) 0 (by simp [Committee.terms])
      (fun f => funext fun T => getD_terms_idxOf f 0 T) (map_getD_idxOf C.terms (Finset.nodup_toList _))
  have hpairs : ((fun (l : List HashOutput) (p : C.Pair) => l.getD ((pairList C).idxOf p) 0) <$>
      (pairList C).mapM (fun _ => $ᵗ HashOutput)) =ᵈ $ᵗ (C.Pair → HashOutput) :=
    evalDist_listFunction (pairList C) ((pairList C).idxOf ·) 0 (by simp [pairList])
      (fun f => funext fun p => getD_pairList_idxOf f 0 p) (map_getD_idxOf (pairList C) (Finset.nodup_toList _))
  have hlen1 : ∀ l ∈ support (C.terms.mapM fun _ => $ᵗ HashOutput), l.length = C.terms.length :=
    Common.length_of_mem_support_mapM _ _
  have hlen2 : ∀ l ∈ support ((pairList C).mapM fun _ => $ᵗ HashOutput), l.length = (pairList C).length :=
    Common.length_of_mem_support_mapM _ _
  have hmapM : (seedGenInputs parts).mapM (fun _ => $ᵗ HashOutput) = (do
      let a ← $ᵗ HashOutput
      let l₁ ← C.terms.mapM (fun _ => $ᵗ HashOutput)
      let l₂ ← (pairList C).mapM (fun _ => $ᵗ HashOutput)
      pure (a :: (l₁ ++ l₂))) := by
    simp only [seedGenInputs, List.mapM_cons, List.mapM_append, List.mapM_map, bind_assoc, pure_bind]
    rfl
  have htrunc : (truncateHash <$> ($ᵗ HashOutput) : ProbComp PublicParameter) =ᵈ $ᵗ PublicParameter :=
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
  calc _ =ᵈ (do
        let a ← $ᵗ HashOutput
        let l₁ ← C.terms.mapM (fun _ => $ᵗ HashOutput)
        let l₂ ← (pairList C).mapM (fun _ => $ᵗ HashOutput)
        pure fun i => some (dealtKeys (truncateHash a) (fun T => l₁.getD (C.terms.idxOf T) 0)
          (fun p => l₂.getD ((pairList C).idxOf p) 0) i) : ProbComp (C.Party → Option (Keys C))) := by
        refine EvalDistEq.bind_right _ fun a => OracleComp.EvalDistEq.bind_congr_of_support _ fun l₁ hl₁ =>
          EvalDistEq.bind_right _ fun l₂ => ?_
        simp only [hkeys a l₁ l₂ (hlen1 l₁ hl₁), EvalDistEq.refl]
    _ = (do
        let parameter ← (truncateHash <$> ($ᵗ HashOutput) : ProbComp PublicParameter)
        let seeds ← (fun (l : List HashOutput) (T : C.Term) => l.getD (C.terms.idxOf T) 0) <$>
          C.terms.mapM (fun _ => $ᵗ HashOutput)
        let pairKeys ← (fun (l : List HashOutput) (p : C.Pair) => l.getD ((pairList C).idxOf p) 0) <$>
          (pairList C).mapM (fun _ => $ᵗ HashOutput)
        pure fun i => some (dealtKeys parameter seeds pairKeys i)) := by
        simp only [bind_map_left]
        rfl
    _ =ᵈ _ := htrunc.bind fun parameter => hterms.bind fun seeds => hpairs.bind_left _

/-- `SeedGenCompletenessStatement`. An honest seed generation gives the keys of `F_seedGen`, except when two
derived keys of one kind have the same parts. -/
theorem seedGenCompleteness (prims : Primitives) : SeedGenCompletenessStatement (C := C) (E := E) prims := by
  unfold SeedGenCompletenessStatement
  rw [completes_iff]
  intro x _
  set P := OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))
  set F := fun parts => (fun values (i : C.Party) => some (keysFromValues values i)) <$>
    (simulateQ (hashAnswer (C := C) prims + prgAnswer (C := C) prims) ((seedGenInputs parts).mapM hashQuery)).run' ∅
  set G := (fun r (i : C.Party) => some (r.2.2 i)) <$> prawnsKeyGen (C := C)
  have hreal : (simulateQ (localAnswer prims) (honestStart (fun i => (fun i (_ : Unit) =>
      (seedGen i : PartyM C E RealSpec (Keys C))) i (x i)) >>=
        honestRounds noFunctionality (fun l => l.elim) setupRounds)).run' ∅ =ᵈ (P >>= F) := by
    refine ((sameRun_seedGen (E := E) prims).run'_eq).trans ((evalDist_seedGen_derivations prims).trans ?_)
    rw [seedGen_real]
  have hideal : (simulateQ (localAnswer prims) (simulateQ (replyImpl (fun _ => (Finset.univ : Finset C.Party)))
      ((FseedGen (C := C)).run noCoalition fun i => some (x i)))).run' ∅ =ᵈ (P >>= fun _ => G) := by
    rw [seedGen_ideal]
    exact (OracleComp.EvalDistEq.bind_const P G).symm
  have hgood : ∀ parts, ¬ ¬ (seedGenInputs parts).Nodup → F parts =ᵈ G := by
    intro parts hnd
    rw [not_not] at hnd
    simp only [F, G]
    exact ((evalDist_fresh_mapM prims _ ∅ hnd (fun _ _ => rfl)
      (fun q hq => by
        simp only [seedGenInputs, List.mem_cons, List.mem_append, List.mem_map] at hq
        rcases hq with rfl | ⟨T, -, rfl⟩ | ⟨p, -, rfl⟩ <;> rintro ⟨_, h, _⟩ <;> cases h)).map _).trans
      (evalDist_keysFromValues parts)
  have hbound := probEvent_seedGen_collision (C := C)
  rw [Fintype.card_bitVec] at hbound
  let : MeasurableSpace (C.Party → Option (Keys C)) := ⊤
  calc measureTVDist _ _ = measureTVDist (P >>= F) (P >>= fun _ => G) := by
        unfold measureTVDist
        rw [hreal.evalDist_eq, hideal.evalDist_eq]
    _ ≤ (Pr{let parts ← P}[¬ (seedGenInputs parts).Nodup]).toReal :=
        measureTVDist_bind_left_le_prEvent_of_evalDistEq P F (fun _ => G) _ hgood
    _ ≤ ((((Fintype.card C.Term ^ 2 + Fintype.card C.Pair ^ 2 : ℕ) : ℝ≥0∞) *
          ((2 ^ 256 : ℕ) : ℝ≥0∞)⁻¹)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) (by simp)) hbound
    _ = ((Fintype.card C.Term ^ 2 + Fintype.card C.Pair ^ 2 : ℕ) : ℝ) / 2 ^ 256 := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast, div_eq_mul_inv]
        norm_num
    _ ≤ derivedKeyCollision C := by
        unfold derivedKeyCollision termCount
        gcongr
        · rw [card_term]
        · exact card_pair_le C

end SeedGenCompleteness

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

section SeedGenSecurity

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

/-- One answer of `seedGenSimulator` costs one round of the adversary, the programming queries, and two
more rounds. -/
theorem costLe_seedGenSimulator_answer (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hround : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step) (st : (seedGenSimulator D A).State)
    (l : PublicParameter × (C.Party → Option (Keys C))) :
    CostLe prims ((seedGenSimulator D A).answer st l)
      (step + (1 + (C.terms.length * 1 + (C.parties.length * (C.parties.length * 1) + (setupRounds - 1) * step)))) := by
  rcases l with ⟨parameter, corrupt⟩
  unfold seedGenSimulator
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

theorem seedGenSimulator_queryBound (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit)
    (z : Aux) (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q) :
    HasHashQueryBound (runWorld prims (distinguish (idealExecution (fun oa => oa) D FseedGen
      (seedGenSimulator D A) x z) Z)) (q + seedGenOverhead C) := by
  obtain ⟨start, step, final, hsum, hs, hr, ha, hz⟩ := hq
  apply hasHashQueryBound_of_costLe
  unfold distinguish idealExecution
  simp only [bind_assoc]
  have hstart : CostLe prims ((seedGenSimulator D A).start (corruptInputs D x) z) start :=
    ((CostLe.observe prims _ start (hs _ _)).bind prims fun _ => CostLe.pure prims _).mono prims (by simp)
  have hanswer := costLe_seedGenSimulator_answer prims D A step hr
  set M := step + (1 + (C.terms.length * 1 + (C.parties.length * (C.parties.length * 1) +
    (setupRounds - 1) * step))) with hM
  refine CostLe.mono prims (CostLe.bind prims hstart (m := 0 + ((M + 0) + (0 + (0 + (0 + final))))) fun st => ?_) ?_
  · unfold FseedGen
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
    unfold seedGenOverhead termCount
    simp only [setupRounds] at hsum ⊢
    nlinarith [hsum]

/-- The distance half of `SeedGenSecurityStatement`. -/
def SeedGenSecurityDistance (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    |accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z) Z) -
      accepts prims (distinguish (idealExecution (fun oa => oa) D FseedGen (seedGenSimulator D A) x z) Z)| ≤
        seedGenHashError C q

/-- `SeedGenSecurityStatement` from its distance half. The query half is `seedGenSimulator_queryBound`. -/
theorem seedGenSecurity_of_distance (h : SeedGenSecurityDistance (C := C) (E := E) prims) :
    SeedGenSecurityStatement (C := C) (E := E) prims :=
  fun D A x z Z q _ hq => ⟨seedGenSimulator_queryBound prims D A x z Z q hq, h D A x z Z q hq⟩

/-- The coupling of the seed generation run and the ideal run of `seedGenSimulator`, identical until bad. -/
def SeedGenCoupling : Prop :=
  ∀ (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ), IsQueryBounded A Z setupRounds q →
    ∃ oa ob : OracleComp (WorldSpec C) (Bool × Bool),
      accepts prims (Prod.fst <$> oa) = accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z) Z) ∧
      accepts prims (Prod.fst <$> ob) =
        accepts prims (distinguish (idealExecution (fun oa => oa) D FseedGen (seedGenSimulator D A) x z) Z) ∧
      Pr{let r ← runWorld prims oa}[r.1 = (true, false)] = Pr{let r ← runWorld prims ob}[r.1 = (true, false)] ∧
      Pr{let r ← runWorld prims oa}[r.1.2 = true].toReal ≤ seedGenHashError C q ∧
      Pr{let r ← runWorld prims ob}[r.1.2 = true].toReal ≤ seedGenHashError C q

/-- `SeedGenSecurityDistance` from the coupling. -/
theorem seedGenDistance_of_coupling (h : SeedGenCoupling (C := C) (E := E) prims) :
    SeedGenSecurityDistance (C := C) (E := E) prims := by
  intro D A x z Z q hq
  obtain ⟨oa, ob, hoa, hob, heq, hbad₁, hbad₂⟩ := h D A x z Z q hq
  have hdist := abs_accepts_sub_le_of_eq_until_bad prims oa ob heq
  rw [hoa, hob] at hdist
  exact hdist.trans (max_le hbad₁ hbad₂)

/-- `SeedGenSecurityStatement` from the coupling. -/
theorem seedGenSecurity_of_coupling (h : SeedGenCoupling (C := C) (E := E) prims) :
    SeedGenSecurityStatement (C := C) (E := E) prims :=
  seedGenSecurity_of_distance prims (seedGenDistance_of_coupling prims h)

end SeedGenSecurity

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The complete private transcript of one round, used only to define bad events. -/
structure SeedGenRoundTrace (C : Committee) (E : Type) where
  queries : (WorldSpec C).QueryLog
  outgoing : C.Party → Mail C E
  sent : C.Party → Mail C E

structure SeedGenRealTrace (C : Committee) (E : Type) where
  start : (WorldSpec C).QueryLog
  honestStart : (WorldSpec C).QueryLog
  rounds : List (SeedGenRoundTrace C E)
  final : (WorldSpec C).QueryLog

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Programming a fresh random-oracle input inserts the prescribed answer. -/
theorem programAnswer_run_fresh {q : Query C} (hfixed : ¬ IsFixed q)
    (s : HashCache C) (hfresh : s q = none) (y : HashOutput) :
    (programAnswer (q, y)).run s = pure (true, s.cacheQuery q y) := by
  change ¬ (∃ input, q = .hash input ∧ MpcInput input) at hfixed
  simp [programAnswer, StateT.run_bind, StateT.run_get, hfixed, hfresh, StateT.run_set]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
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
    (hcall : (.commit .seedGen j i reveal, value) ∈ calls)
    (hsent : [value] = Msg.hashesOf (sent j i))
    (hunique : ∀ reveal' value', (.commit .seedGen j i reveal', value') ∈ calls →
      [value'] = Msg.hashesOf (sent j i) → reveal' = reveal) :
    extractReveal calls sent j i = reveal := by
  unfold extractReveal
  have h := findSome_eq_of_unique
    (fun (q, out) => match q with
      | .commit .seedGen j' i' opening =>
          if j' = j ∧ i' = i ∧ [out] = Msg.hashesOf (sent j i) then some opening else none
      | _ => none) calls reveal
    (by exact ⟨(.commit .seedGen j i reveal, value), hcall, by simp [hsent]⟩)
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

/-- Every term has exactly `t` holders. -/
theorem seedGen_card_holders (C : Committee) (T : C.Term) : (C.holders T).card = C.t := by
  rw [Committee.holders, Finset.card_compl, Fintype.card_fin, T.2]
  have := C.one_le_t
  unfold Committee.n
  omega

/-- The honest sender's fields in a received reveal agree with the sampled fields. -/
theorem setupView_honest_sender (D : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ D.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .seedGen (parts j) j i)
    (i j : C.Party) (hj : j ∉ D.1) :
    setupView .seedGen i (parts i) (revealed i) j = honestView (E := E) .seedGen parts i j := by
  by_cases hji : j = i
  · subst j; simp [setupView, honestView]
  · rw [honestView_ne _ _ hji]
    simp only [setupView, if_neg hji, hreceived i j hj hji]

def seedGenPairViewInput (parts : C.Party → Parts C) (revealed : C.Party → Mail C E)
    (i : C.Party) (p : C.Pair) : Query C :=
  let view := setupView .seedGen i (parts i) (revealed i)
  .derive .seedGen .pair [(view p.1.1).pair p.1.2, (view p.1.2).pair p.1.1]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
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
theorem seedGen_echo_agreement (prims : Primitives) (h : Query C → HashOutput)
    (i j : C.Party)
    (ki kj : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hecho : echoOf .seedGen ki (D prims h (sharedQueries .seedGen i ki)) j =
      echoOf .seedGen kj (D prims h (sharedQueries .seedGen j kj)) i)
    (hnocollision :
      h (.sharedKeys .seedGen ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys .seedGen ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) .seedGen ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys (C := C) .seedGen ((sharedTerms j i).map kj.2.1)) :
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
theorem seedGen_echoCheck_agreement (prims : Primitives) (h : Query C → HashOutput)
    (i j : C.Party) (hji : j ≠ i)
    (ki kj : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (received : Mail C E)
    (hsender : received j = some (.hashes (echoOf .seedGen kj
      (D prims h (sharedQueries .seedGen j kj)) i)))
    (hcheck : echoCheck .seedGen i ki (D prims h (sharedQueries .seedGen i ki)) received)
    (hnocollision :
      h (.sharedKeys .seedGen ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys .seedGen ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) .seedGen ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys (C := C) .seedGen ((sharedTerms j i).map kj.2.1)) :
    ki.1 = kj.1 ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.2.1 T = kj.2.1 T := by
  apply seedGen_echo_agreement prims h i j ki kj _ hnocollision
  have heq := hcheck j hji
  simpa only [hsender, Msg.hashesOf] using heq.symm

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- An echo to a corrupt recipient contains only terms known to the coalition. -/
theorem seedGen_sharedTerms_known (D : C.Coalition) (i j : C.Party) (hj : j ∈ D.1)
    (T : C.Term) (hT : T ∈ sharedTerms i j) : KnownTo D.1 T := by
  have hm := (List.mem_filter.mp hT).2
  exact ⟨j, hj, (of_decide_eq_true hm).2⟩

/-- Changing only hidden seeds preserves every echo input sent to a corrupt recipient. -/
theorem seedGen_sharedInput_known (D : C.Coalition) (i j : C.Party) (hj : j ∈ D.1)
    (s s' : C.Term → HashOutput) (hs : ∀ T, KnownTo D.1 T → s T = s' T) :
    Query.sharedKeys (C := C) .seedGen ((sharedTerms i j).map s) =
      Query.sharedKeys .seedGen ((sharedTerms i j).map s') := by
  congr 1
  exact List.map_congr_left fun T hT => hs T (seedGen_sharedTerms_known D i j hj T hT)

/-- On two honest endpoints, the complete seed comparison reduces to known seeds when hidden
terms are internally consistent. This allows the dealer's hidden seeds to replace emulated ones. -/
theorem seedGen_sharedAgreement_iff_known (D : C.Coalition) (i j : C.Party)
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
theorem seedGen_echo_eq_iff (prims : Primitives) (h : Query C → HashOutput)
    (i j : C.Party)
    (ki kj : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hnocollision :
      h (.sharedKeys .seedGen ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys .seedGen ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) .seedGen ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys .seedGen ((sharedTerms j i).map kj.2.1)) :
    (echoOf .seedGen ki (D prims h (sharedQueries .seedGen i ki)) j =
      echoOf .seedGen kj (D prims h (sharedQueries .seedGen j kj)) i) ↔
    (ki.1 = kj.1 ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.2.1 T = kj.2.1 T) := by
  constructor
  · exact fun heq => seedGen_echo_agreement prims h i j ki kj heq hnocollision
  · rintro ⟨hp, hs⟩
    simp only [echoOf, ite_true, List.singleton_append, List.cons.injEq, and_true,
      D_sharedQueries_at, hp, true_and]
    rw [sharedTerms_comm j i]
    congr 2
    exact List.map_congr_left fun T hT => by
      have hm := of_decide_eq_true (List.mem_filter.mp hT).2
      exact hs T hm.1 hm.2

/-- Replacing coherent hidden seeds preserves the equality of two honest echoes. -/
theorem seedGen_echo_eq_hidden_invariant (prims : Primitives) (coalition : C.Coalition)
    (h h' : Query C → HashOutput) (i j : C.Party)
    (ki kj ki' kj' : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hpi : ki.1 = ki'.1) (hpj : kj.1 = kj'.1)
    (hki : ∀ T, KnownTo coalition.1 T → ki.2.1 T = ki'.2.1 T)
    (hkj : ∀ T, KnownTo coalition.1 T → kj.2.1 T = kj'.2.1 T)
    (hhidden : ∀ T, ¬ KnownTo coalition.1 T → i ∈ C.holders T → j ∈ C.holders T → ki.2.1 T = kj.2.1 T)
    (hhidden' : ∀ T, ¬ KnownTo coalition.1 T → i ∈ C.holders T → j ∈ C.holders T → ki'.2.1 T = kj'.2.1 T)
    (hnocollision :
      h (.sharedKeys .seedGen ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys .seedGen ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) .seedGen ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys .seedGen ((sharedTerms j i).map kj.2.1))
    (hnocollision' :
      h' (.sharedKeys .seedGen ((sharedTerms i j).map ki'.2.1)) =
        h' (.sharedKeys .seedGen ((sharedTerms j i).map kj'.2.1)) →
      Query.sharedKeys (C := C) .seedGen ((sharedTerms i j).map ki'.2.1) =
        Query.sharedKeys .seedGen ((sharedTerms j i).map kj'.2.1)) :
    (echoOf .seedGen ki (D prims h (sharedQueries .seedGen i ki)) j =
      echoOf .seedGen kj (D prims h (sharedQueries .seedGen j kj)) i) ↔
    (echoOf .seedGen ki' (D prims h' (sharedQueries .seedGen i ki')) j =
      echoOf .seedGen kj' (D prims h' (sharedQueries .seedGen j kj')) i) := by
  rw [seedGen_echo_eq_iff prims h i j ki kj hnocollision,
    seedGen_echo_eq_iff prims h' i j ki' kj' hnocollision',
    seedGen_sharedAgreement_iff_known coalition i j ki.2.1 kj.2.1 hhidden,
    seedGen_sharedAgreement_iff_known coalition i j ki'.2.1 kj'.2.1 hhidden', hpi, hpj]
  apply and_congr Iff.rfl
  apply forall_congr'
  intro T
  apply forall_congr'
  intro hT
  rw [hki T hT, hkj T hT]

/-- Every hidden term uses the honest parts, in every holder's view, even when the corrupt
operators send inconsistent openings for other terms. -/
theorem seedGen_hiddenTerm_input (coalition : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .seedGen (parts j) j i)
    (T : C.Term) (hhidden : ¬ KnownTo coalition.1 T) (i : C.Party) (hi : i ∈ C.holders T) :
    Query.derive (C := C) .seedGen .term
      ((C.parties.filter (· ∈ C.holders T)).map fun j =>
        (setupView .seedGen i (parts i) (revealed i) j).term T) =
      termInput .seedGen parts T := by
  unfold termInput
  congr 1
  apply List.map_congr_left
  intro j hj
  have hjT : j ∈ C.holders T := of_decide_eq_true (List.mem_filter.mp hj).2
  have hjhonest : j ∉ coalition.1 := fun hc => hhidden ⟨j, hc, hjT⟩
  rw [setupView_honest_sender coalition parts revealed hreceived i j hjhonest]
  exact honestView_term .seedGen parts hjT hi

/-- The actual derived hidden seed is common to all its honest holders. -/
theorem seedGen_hiddenTerm_derived (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .seedGen (parts j) j i)
    (T : C.Term) (hhidden : ¬ KnownTo coalition.1 T) (i : C.Party) (hi : i ∈ C.holders T) :
    (D prims h (deriveKeys .seedGen i (setupView .seedGen i (parts i) (revealed i)))).2.1 T =
      h (termInput .seedGen parts T) := by
  rw [D_deriveKeys]
  simp only [hi, if_true]
  rw [seedGen_hiddenTerm_input coalition parts revealed hreceived T hhidden i hi]

/-- The echo-round inbox, including the abort frame of any honest operator that failed earlier. -/
def seedGenEchoInbox (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (i : C.Party) : Mail C E := fun j =>
  if j ∈ coalition.1 then sent j i else
  if active j then echoOutbox .seedGen j (keys j) (D prims h (sharedQueries .seedGen j (keys j))) i
  else some .abort

/-- The last local continuation of seed generation makes no oracle calls. -/
theorem advance_seedGenEchoResume (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (shared : List HashOutput) (received : Mail C E) :
    advance (exchangeResume (G := RealSpec) (fun inbox =>
      require (echoCheck .seedGen i keys shared inbox) >>= fun _ => pure (keysOf keys)) received) =
      pure (Step.done (if (C.parties.any fun j => Msg.isAbort (received j)) then none else
        if echoCheck .seedGen i keys shared received then some (keysOf keys) else none)) := by
  unfold exchangeResume
  split_ifs with ha hc
  · rfl
  · rw [advance_require_bind, if_pos hc, advance_run_pure]
  · rw [advance_require_bind, if_neg hc]

/-- Aborts in the last inbox do not depend on the keys or the oracle table. -/
theorem seedGenEchoInbox_isAbort (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h h' : Query C → HashOutput)
    (keys keys' : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (i j : C.Party) :
    Msg.isAbort (seedGenEchoInbox prims coalition active sent h keys i j) =
      Msg.isAbort (seedGenEchoInbox prims coalition active sent h' keys' i j) := by
  unfold seedGenEchoInbox
  split_ifs <;> simp only [isAbort_echoOutbox]

/-- A seed generation step waiting for the echo, or the persistent abort of an earlier round. -/
def seedGenEchoStep (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (i : C.Party) : Step C E RealSpec (Keys C) :=
  if i ∈ coalition.1 ∨ ¬ active i then .done none else
    .wait (echoOutbox .seedGen i (keys i) (D prims h (sharedQueries .seedGen i (keys i))))
      (exchangeResume fun inbox => require
        (echoCheck .seedGen i (keys i) (D prims h (sharedQueries .seedGen i (keys i))) inbox) >>=
        fun _ => pure (keysOf (keys i)))

/-- The concrete inbox used by `stepRound` is the echo inbox above. -/
theorem roundInbox_seedGenEchoStep (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) (i : C.Party) :
    roundInbox coalition sent (seedGenEchoStep prims coalition active h keys) i =
      seedGenEchoInbox prims coalition active sent h keys i := by
  funext j
  unfold roundInbox seedGenEchoStep seedGenEchoInbox
  by_cases hj : j ∈ coalition.1
  · simp only [hj, if_true]
  · simp only [hj, false_or, if_false]
    by_cases ha : active j <;> simp [ha, Step.delivered]

/-- The possible output of the final local step. -/
def seedGenEchoOutput (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (sent : C.Party → Mail C E)
    (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (i : C.Party) : Option (Keys C) :=
  if i ∈ coalition.1 ∨ ¬ active i then none else
    let inbox := seedGenEchoInbox prims coalition active sent h keys i
    if C.parties.any fun j => Msg.isAbort (inbox j) then none else
      if echoCheck .seedGen i (keys i) (D prims h (sharedQueries .seedGen i (keys i))) inbox
      then some (keysOf (keys i)) else none

/-- One concrete echo round, with all honest local continuations reduced to pure outputs. -/
theorem stepRound_seedGenEchoStep (prims : Primitives) (coalition : C.Coalition)
    (active : C.Party → Prop) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (h : Query C → HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    stepRound worldRoles coalition A noFunctionality state (seedGenEchoStep prims coalition active h keys) =
      (do
        let (state, sent) ← worldRoles.adversary (A.round state fun c i =>
          if c ∈ coalition.1 ∧ i ∉ coalition.1 then
            (seedGenEchoStep prims coalition active h keys i).outbox c else none)
        pure (state, (fun i => Step.done (seedGenEchoOutput prims coalition active sent h keys i)), sent)) := by
  unfold stepRound
  have hc : ¬ (∃ i, i ∉ coalition.1 ∧
      (seedGenEchoStep prims coalition active h keys (E := E) i).callInput.isSome) := by
    simp only [callInput_real, Option.isSome_none, Bool.false_eq_true, and_false, exists_false, not_false_eq_true]
  rw [if_neg (fun h => hc h.1)]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only
  trans (OverPermutation.sequenceFin (fun i =>
    (pure (Step.done (seedGenEchoOutput prims coalition active sent h keys i)) :
      OracleComp (WorldSpec C) (Step C E RealSpec (Keys C)))) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext i
    by_cases hi : i ∈ coalition.1 ∨ ¬ active i
    · simp only [seedGenEchoStep, if_pos hi, seedGenEchoOutput]
    · have hih : i ∉ coalition.1 := fun hh => hi (Or.inl hh)
      rw [show seedGenEchoStep prims coalition active h keys (E := E) i = _ from if_neg hi]
      simp only [if_neg hih]
      change worldRoles.honest (advance (exchangeResume _
        (roundInbox coalition sent (seedGenEchoStep prims coalition active h keys) i))) = _
      rw [roundInbox_seedGenEchoStep, advance_seedGenEchoResume]
      simp only [worldRoles, free, seedGenEchoOutput, if_neg hi]
      exact simulateQ_pure _ _
  · rw [sequenceFin_pure, pure_bind]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
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
    (uniformProgram q).run s =ᵈ
      (hashAnswer prims q >>= fun _ => pure ()).run s := by
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
    exact OracleComp.EvalDistEq.bind_const ($ᵗ HashOutput) _

/-- The discarded programming swap is valid before every cache-dependent continuation. -/
theorem evalDist_uniformProgram_bind (prims : Primitives) (q : Query C) (hq : ¬ IsFixed q)
    {α : Type} (k : StateT (HashCache C) ProbComp α) (s : HashCache C) :
    (uniformProgram q >>= fun _ => k).run s =ᵈ
      (hashAnswer prims q >>= fun _ => k).run s := by
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
    (uniformPrograms qs >>= fun _ => k).run s =ᵈ
      ((qs.mapM (hashAnswer prims)) >>= fun _ => k).run s := by
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
    (uniformPrograms qs >>= fun _ => simulateQ (localAnswer prims) k).run' s =ᵈ
      (simulateQ (localAnswer prims) k).run' s := by
  have h := evalDist_uniformPrograms_bind prims qs hq (simulateQ (localAnswer prims) k) s
  have hm := h.map Prod.fst
  simp only [← StateT.run'_eq] at hm
  refine hm.trans ?_
  rw [← simulateQ_localAnswer_hashes]
  rw [← simulateQ_bind]
  exact evalDist_run'_prepend prims _ k s

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity

def seedGenFullParameter (high : HashOutput) (parameter : PublicParameter) : HashOutput :=
  high >>> digestBits <<< digestBits ||| parameter.setWidth 256

theorem seedGenFullParameter_getLsbD (high : HashOutput) (parameter : PublicParameter)
    (i : ℕ) (hi : i < 256) :
    (seedGenFullParameter high parameter).getLsbD i =
      if i < digestBits then parameter.getLsbD i else high.getLsbD i := by
  simp only [seedGenFullParameter, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  by_cases h : i < digestBits
  · simp [h, hi]
  · have hp : parameter.getLsbD i = false := BitVec.getLsbD_of_ge parameter i (by exact Nat.le_of_not_gt h)
    simp [h, hp, hi, Nat.le_of_not_gt h]

theorem truncate_seedGenFullParameter (high : HashOutput) (parameter : PublicParameter) :
    truncateHash (seedGenFullParameter high parameter) = parameter := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [truncateHash, BitVec.getLsbD_extractLsb', Nat.zero_add]
  rw [seedGenFullParameter_getLsbD high parameter i (by
    unfold digestBits at hi; omega)]
  simp only [hi, if_pos, decide_true, Bool.true_and]
  rfl

theorem seedGenFullParameter_restore (high : HashOutput) (parameter : PublicParameter) :
    seedGenFullParameter (seedGenFullParameter high parameter) (truncateHash high) = high := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  refine (seedGenFullParameter_getLsbD _ _ i hi).trans ?_
  by_cases hl : i < digestBits
  · rw [if_pos hl]
    change (BitVec.extractLsb' 0 digestBits high).getLsbD i = high.getLsbD i
    simp only [BitVec.getLsbD_extractLsb', Nat.zero_add, hl, decide_true, Bool.true_and]
  · rw [if_neg hl, seedGenFullParameter_getLsbD high parameter i hi, if_neg hl]

/-- The parameter encoding swaps the low halves of a pair of uniform samples. -/
def seedGenParameterSwap (p : HashOutput × PublicParameter) : HashOutput × PublicParameter :=
  (seedGenFullParameter p.1 p.2, truncateHash p.1)

theorem seedGenParameterSwap_involutive : Function.Involutive seedGenParameterSwap := by
  intro p
  exact Prod.ext (seedGenFullParameter_restore p.1 p.2) (truncate_seedGenFullParameter p.1 p.2)

theorem evalDist_seedGenFullParameter_pair :
    ((fun p : HashOutput × PublicParameter => seedGenFullParameter p.1 p.2) <$>
        ($ᵗ (HashOutput × PublicParameter))) =ᵈ $ᵗ HashOutput := by
  have h := SampleableType.map_uniformSample_evalDistEq_of_bijective
    seedGenParameterSwap_involutive.bijective
  calc ((fun p : HashOutput × PublicParameter => seedGenFullParameter p.1 p.2) <$>
        ($ᵗ (HashOutput × PublicParameter)) : ProbComp HashOutput)
    _ = Prod.fst <$> (seedGenParameterSwap <$> ($ᵗ (HashOutput × PublicParameter))) := by
      rw [Functor.map_map]; rfl
    _ =ᵈ Prod.fst <$> ($ᵗ (HashOutput × PublicParameter)) := h.map _
    _ =ᵈ _ := by
      rw [SampleableType.uniformSample_prod_eq_bind]
      simp only [map_bind, map_pure]
      exact (EvalDistEq.bind_right _ fun a => OracleComp.EvalDistEq.bind_const _ _).trans
        (by rw [bind_pure])

/-- The exact full-width parameter programmed by `seedGenSimulator` is uniform. -/
theorem evalDist_seedGenFullParameter :
    (do
      let parameter ← $ᵗ PublicParameter
      let high ← $ᵗ HashOutput
      pure (high >>> digestBits <<< digestBits ||| parameter.setWidth 256) : ProbComp HashOutput) =ᵈ
      $ᵗ HashOutput := by
  change (($ᵗ PublicParameter) >>= fun p => ($ᵗ HashOutput) >>= fun h => pure (seedGenFullParameter h p)) =ᵈ _
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  have he : ((fun p : HashOutput × PublicParameter => seedGenFullParameter p.1 p.2) <$>
      ($ᵗ (HashOutput × PublicParameter))) =
      (($ᵗ HashOutput) >>= fun h => ($ᵗ PublicParameter) >>= fun p => pure (seedGenFullParameter h p)) := by
    change ((fun p : HashOutput × PublicParameter => seedGenFullParameter p.1 p.2) <$>
      (Prod.mk <$> ($ᵗ HashOutput) <*> ($ᵗ PublicParameter))) = _
    simp only [seq_eq_bind_map, map_eq_bind_pure_comp]
    rfl
  rw [← he]
  exact evalDist_seedGenFullParameter_pair

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

/-- Distinct coordinates of the dealer's uniform table may be sampled separately. -/
theorem evalDist_uniform_table_list {ι R : Type} [Finite ι] [DecidableEq ι]
    [Finite R] [Nonempty R] [SampleableType R] [SampleableType (ι → R)]
    (indices : List ι) (hnd : indices.Nodup) :
    ((fun f : ι → R => indices.map f) <$> ($ᵗ (ι → R))) =ᵈ
      (indices.mapM fun _ => $ᵗ R) := by
  induction indices with
  | nil =>
    simp only [List.map_nil, List.mapM_nil, map_eq_bind_pure_comp]
    exact OracleComp.EvalDistEq.bind_const _ _
  | cons i indices ih =>
    have hn := List.nodup_cons.mp hnd
    have hs := evalDistEq_uniformSample_bind_update (R := R) i
      (fun f : ι → R => (pure ((i :: indices).map f) : ProbComp (List R)))
    have hmap : ∀ (f : ι → R) (r : R), indices.map (Function.update f i r) = indices.map f := by
      intro f r
      apply List.map_congr_left
      intro j hj
      have hji : j ≠ i := fun h => hn.1 (h ▸ hj)
      simp [hji]
    simp only [List.map_cons, Function.update_self, hmap] at hs
    simp only [List.map_cons, map_eq_bind_pure_comp, Function.comp_def]
    refine hs.symm.trans ?_
    simp only [List.mapM_cons]
    refine EvalDistEq.bind_right _ fun r => ?_
    have hr := (ih hn.2).map (List.cons r)
    simpa only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using hr

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Interpret both network roles through the same oracle implementation. -/
def seedGenMapRoles {ι : Type} {spec : OracleSpec ι} {m : Type → Type} [Monad m]
    (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec)) : Roles C m :=
  ⟨fun oa => simulateQ impl (roles.adversary oa), fun oa => simulateQ impl (roles.honest oa)⟩

theorem simulateQ_stepRound_real {ι : Type} {spec : OracleSpec ι} {m : Type → Type}
    [Monad m] [LawfulMonad m] (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec))
    (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec (Keys C)) :
    simulateQ impl (stepRound roles coalition A noFunctionality state steps) =
      stepRound (seedGenMapRoles impl roles) coalition A noFunctionality state steps := by
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
    by_cases hi : i ∈ coalition.1 <;> simp [hi, seedGenMapRoles]
  | call input resume => exact input.elim

theorem simulateQ_executeRounds_real {ι : Type} {spec : OracleSpec ι} {m : Type → Type}
    [Monad m] [LawfulMonad m] (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec))
    (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    ∀ fuel state (steps : C.Party → Step C E RealSpec (Keys C)),
    simulateQ impl (executeRounds roles coalition A noFunctionality fuel state steps) =
      executeRounds (seedGenMapRoles impl roles) coalition A noFunctionality fuel state steps
  | 0, state, steps => by simp [executeRounds]
  | fuel + 1, state, steps => by
    simp only [executeRounds]
    split_ifs
    · simp
    · rw [simulateQ_bind, simulateQ_stepRound_real]
      refine bind_congr fun r => ?_
      exact simulateQ_executeRounds_real impl roles coalition A fuel r.1 r.2.1

/-- Counted and free local computations have the same cache semantics after the counter is erased. -/
theorem seedGenMapRoles_world (prims : Primitives) :
    seedGenMapRoles (worldAnswer (C := C) prims) worldRoles =
      seedGenMapRoles (localAnswer prims) localRoles := by
  unfold seedGenMapRoles
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
  rw [simulateQ_executeRounds_real, seedGenMapRoles_world, ← simulateQ_executeRounds_real]

theorem simulateQ_startSteps_real {ι : Type} {spec : OracleSpec ι} {m : Type → Type}
    [Monad m] [LawfulMonad m] (impl : QueryImpl spec m) (roles : Roles C (OracleComp spec))
    (coalition : C.Coalition) (program : C.Party → PartyM C E RealSpec (Keys C)) :
    simulateQ impl (startSteps roles coalition program) =
      startSteps (seedGenMapRoles impl roles) coalition program := by
  unfold startSteps
  rw [simulateQ_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ coalition.1 <;> simp [hi, seedGenMapRoles]

theorem simulateQ_world_adversary (prims : Primitives) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    simulateQ (worldAnswer prims) (worldRoles.adversary oa) = simulateQ (localAnswer prims) oa :=
  congrArg (fun roles : Roles C (StateT (HashCache C) ProbComp) => roles.adversary oa)
    (seedGenMapRoles_world prims)

/-- The real seed generation game after removing only the counted/free wrappers. -/
def seedGenLocalGame (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    OracleComp (LocalSpec C) Bool := do
  let state ← A.start (corruptInputs coalition x) z
  let steps ← startSteps localRoles coalition fun i => (seedGen i : PartyM C E RealSpec (Keys C))
  let out ← executeRounds localRoles coalition A noFunctionality setupRounds state steps
  Z out

/-- The complete real game, including the distinguisher, runs on the one shared cache. -/
theorem simulateQ_seedGenReal_eq_local (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    simulateQ (worldAnswer prims)
      (distinguish (realExecution coalition A noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z) Z) =
      simulateQ (localAnswer prims) (seedGenLocalGame coalition A x z Z) := by
  unfold distinguish realExecution executePhase seedGenLocalGame
  simp only [simulateQ_bind, simulateQ_world_adversary, simulateQ_startSteps_real,
    simulateQ_executeRounds_real, seedGenMapRoles_world, bind_assoc]

/-- In particular, the local game has exactly the acceptance probability of the real game. -/
theorem seedGenLocalGame_accepts (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    (Pr{let y ← (simulateQ (localAnswer prims) (seedGenLocalGame coalition A x z Z)).run' ∅}[y = true]).toReal =
      accepts prims (distinguish (realExecution coalition A noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z) Z) := by
  unfold accepts
  rw [← simulateQ_seedGenReal_eq_local, ← fst_map_runWorld, prEvent_map]

/-- An unused private draw changes neither an output nor the cache. -/
theorem sameRun_private_unused (prims : Primitives) {α β : Type} (p : ProbComp α) (b : β) :
    SameRun (C := C) prims (liftComp p (LocalSpec C) >>= fun _ => pure b) (pure b) := by
  intro s
  have hl : simulateQ (localAnswer prims) (liftComp p (LocalSpec C)) =
      simulateQ (unifFwdImpl (Query C →ₒ HashOutput)) p :=
    QueryImpl.simulateQ_add_liftComp_left (unifFwdImpl (Query C →ₒ HashOutput)) _ p
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, hl,
    unifFwdImpl.simulateQ_run, bind_map_left]
  exact OracleComp.EvalDistEq.bind_const p _

theorem SameRun.sequenceFin (prims : Primitives) {α : Type} {n : ℕ}
    (f g : Fin n → OracleComp (LocalSpec C) α) (h : ∀ i, SameRun prims (f i) (g i)) :
    SameRun prims (OverPermutation.sequenceFin f) (OverPermutation.sequenceFin g) := by
  induction n with
  | zero => exact SameRun.refl prims _
  | succ n ih =>
    simp only [OverPermutation.sequenceFin]
    apply (h 0).bind
    intro a
    apply (ih (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)).bind
    intro rest
    exact SameRun.refl prims _

theorem advance_seedGen_sampling (i : C.Party) :
    advance (seedGen i : PartyM C E RealSpec (Keys C)).run =
      liftComp sampleParts (LocalSpec C) >>= fun parts =>
        advance (seedGenWith i parts : PartyM C E RealSpec (Keys C)).run :=
  advance_localStep_bind _ _

/-- Moving all private parts before the first commitments is valid for any coalition. The unused
parts of corrupt operators can be sampled too, as the explicit simulator does. -/
theorem sameRun_startSteps_seedGen_parts (prims : Primitives) (coalition : C.Coalition) :
    SameRun prims
      (startSteps localRoles coalition fun i => (seedGen i : PartyM C E RealSpec (Keys C)))
      (do
        let parts ← OverPermutation.sequenceFin fun (_ : C.Party) => liftComp (sampleParts (C := C)) (LocalSpec C)
        startSteps localRoles coalition fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))) := by
  let draws : C.Party → OracleComp (LocalSpec C) (Parts C) := fun _ => liftComp sampleParts (LocalSpec C)
  let next : C.Party → Parts C → OracleComp (LocalSpec C) (Step C E RealSpec (Keys C)) := fun i parts =>
    if i ∈ coalition.1 then pure (.done none) else advance (seedGenWith i parts : PartyM C E RealSpec (Keys C)).run
  have hlocal : ∀ i, SameRun prims
      (if i ∈ coalition.1 then pure (.done none) else advance (seedGen i : PartyM C E RealSpec (Keys C)).run)
      (draws i >>= next i) := by
    intro i
    by_cases hi : i ∈ coalition.1
    · simpa only [draws, next, if_pos hi] using
        (sameRun_private_unused prims (sampleParts (C := C)) (Step.done (C := C) (E := E) (G := RealSpec) (none : Option (Keys C)))).symm
    · simp only [draws, next, if_neg hi, advance_seedGen_sampling]
      exact SameRun.refl prims _
  have hseq := SameRun.sequenceFin prims _ _ hlocal
  change SameRun prims (OverPermutation.sequenceFin _) _
  refine hseq.trans ?_
  have hmove := sameRun_sequenceFin_dep prims draws next (fun _ _ step => step)
  simp only [bind_pure] at hmove
  change SameRun prims (OverPermutation.sequenceFin fun i => draws i >>= next i)
    (OverPermutation.sequenceFin draws >>= fun parts =>
      (OverPermutation.sequenceFin fun i => next i (parts i)) >>= pure) at hmove
  simpa only [bind_pure, draws, next, startSteps, localRoles] using hmove

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The commitment computation of the honest operators, with an empty entry for each corrupt one. -/
def seedGenInitialCommitments (coalition : C.Coalition) (parts : C.Party → Parts C) :
    OracleComp (LocalSpec C) (C.Party → List HashOutput) :=
  OverPermutation.sequenceFin fun i => if i ∈ coalition.1 then pure [] else
    liftComp (commitQueries .seedGen i (parts i)) (LocalSpec C)

def seedGenInitialSteps (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) : C.Party → Step C E RealSpec (Keys C) := fun i =>
  if i ∈ coalition.1 then .done none else seedGenStart i (parts i) (commitments i)

theorem advance_seedGenWith (i : C.Party) (parts : Parts C) :
    advance (seedGenWith i parts : PartyM C E RealSpec (Keys C)).run =
      liftComp (commitQueries .seedGen i parts) (LocalSpec C) >>= fun commitments =>
        pure (seedGenStart i parts commitments) := by
  change advance (commitRevealEcho .seedGen i parts >>= fun keys => pure (keysOf keys)).run = _
  rw [advance_setup_start]
  rfl

/-- The initial network state consists of waiting commit senders and corrupt dummy steps. -/
theorem startSteps_seedGenWith (coalition : C.Coalition) (parts : C.Party → Parts C) :
    startSteps localRoles coalition (fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))) =
      seedGenInitialSteps coalition parts <$> seedGenInitialCommitments coalition parts := by
  unfold startSteps seedGenInitialCommitments
  have hl : (fun i => if i ∈ coalition.1 then pure (Step.done none) else
      localRoles.honest (advance (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C)).run)) =
      (fun i => (if i ∈ coalition.1 then pure [] else
        liftComp (commitQueries .seedGen i (parts i)) (LocalSpec C)) >>= fun commits =>
        pure (if i ∈ coalition.1 then Step.done none else seedGenStart i (parts i) commits)) := by
    funext i
    by_cases hi : i ∈ coalition.1 <;> simp [hi, localRoles, advance_seedGenWith]
  rw [hl]
  rw [sequenceFin_bind_pure]
  rw [map_eq_bind_pure_comp]
  rfl

/-- Every allowed coalition has an honest operator. -/
theorem seedGen_exists_honest (coalition : C.Coalition) : ∃ i : C.Party, i ∉ coalition.1 := by
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
theorem executeRounds_seedGenInitialSteps (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) :
    executeRounds localRoles coalition A noFunctionality setupRounds state
      (seedGenInitialSteps coalition parts commitments) =
    (do
      let (state, steps, _) ← stepRound localRoles coalition A noFunctionality state
        (seedGenInitialSteps coalition parts commitments)
      executeRounds localRoles coalition A noFunctionality (setupRounds - 1) state steps) := by
  change executeRounds localRoles coalition A noFunctionality (2 + 1) state _ = _
  rw [executeRounds, if_neg]
  · rfl
  · intro hd
    obtain ⟨i, hi⟩ := seedGen_exists_honest coalition
    have hh := hd i hi
    simpa only [seedGenInitialSteps, if_neg hi, seedGenStart, Step.isDone] using hh

/-- The real prefix through the commit round, retaining its private parts and corrupt messages. -/
def seedGenLocalCommitPrefix (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    OracleComp (LocalSpec C)
      ((C.Party → Parts C) × A.State × (C.Party → Step C E RealSpec (Keys C)) × (C.Party → Mail C E)) := do
  let state ← A.start (corruptInputs coalition x) z
  let parts ← OverPermutation.sequenceFin fun (_ : C.Party) => liftComp (sampleParts (C := C)) (LocalSpec C)
  let commitments ← seedGenInitialCommitments coalition parts
  let (state, steps, sent) ← stepRound localRoles coalition A noFunctionality state
    (seedGenInitialSteps coalition parts commitments)
  pure (parts, state, steps, sent)

/-- The continuation after the commit round includes the final distinguisher. -/
def seedGenLocalPostCommit (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C))
    (r : (C.Party → Parts C) × A.State × (C.Party → Step C E RealSpec (Keys C)) × (C.Party → Mail C E)) :
    OracleComp (LocalSpec C) Bool := do
  let out ← executeRounds localRoles coalition A noFunctionality (setupRounds - 1) r.2.1 r.2.2.1
  Z out

/-- The complete real game split at the simulator's programming boundary. -/
theorem sameRun_seedGenLocal_split (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    SameRun prims (seedGenLocalGame coalition A x z Z)
      (seedGenLocalCommitPrefix coalition A x z >>= seedGenLocalPostCommit coalition A Z) := by
  unfold seedGenLocalGame seedGenLocalCommitPrefix seedGenLocalPostCommit
  simp only [bind_assoc, pure_bind]
  apply SameRun.bind_right
  intro state
  refine ((sameRun_startSteps_seedGen_parts prims coalition).bind fun steps =>
    SameRun.refl prims (executeRounds localRoles coalition A noFunctionality setupRounds state steps >>= Z)).trans ?_
  simp only [bind_assoc]
  apply SameRun.bind_right
  intro parts
  rw [startSteps_seedGenWith, bind_map_left]
  apply SameRun.bind_right
  intro commitments
  rw [executeRounds_seedGenInitialSteps]
  simp only [bind_assoc]
  exact SameRun.refl prims _

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
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

theorem idealExecution_FseedGen {σ : Type} (D : C.Coalition)
    (S : Simulator (C := C) (WorldSpec C) Unit
      (PublicParameter × (C.Party → Option (Keys C))) (Finset C.Party) σ)
    (x : C.Party → Unit) (z : Aux) :
    idealExecution (fun oa => oa) D FseedGen S x z = (do
      let st ← S.start (corruptInputs D x) z
      let (parameter, _, keys) ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
      let (st, receivers) ← S.answer st (parameter, fun i => if i ∈ D.1 then some (keys i) else none)
      let out ← S.output st
      pure (out, fun i => if i ∉ D.1 ∧ i ∈ receivers then some (keys i) else none)) := by
  unfold idealExecution FseedGen
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

def seedGenProgramView (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) (i j : C.Party) : Parts C :=
  if j ∈ D.1 then readReveal .seedGen (extractReveal log sent j i) i j else parts j

def seedGenFirstHonest (D : C.Coalition) (S : Finset C.Party) : C.Party :=
  (C.parties.find? fun i => i ∈ S ∧ i ∉ D.1).getD (firstParty C)

/-- The simulator's complete programming block, including failed attempts. -/
def seedGenProgramBlock (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) (parameter : PublicParameter)
    (corrupt : C.Party → Option (Keys C)) (high : HashOutput) : OracleComp (WorldSpec C) Unit := do
  let view := seedGenProgramView D parts log sent
  let _ ← program (.derive .seedGen .parameter
    (C.parties.map fun j => (view (seedGenFirstHonest D Finset.univ) j).parameter))
    (seedGenFullParameter high parameter)
  let _ ← C.terms.mapM fun T => match (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
    | some j =>
      let i := seedGenFirstHonest D (C.holders T)
      program (.derive .seedGen .term
        ((C.parties.filter (· ∈ C.holders T)).map fun k => (view i k).term T))
        (((corrupt j).map (·.seed T)).getD 0)
    | none => pure true
  let _ ← C.parties.mapM fun j => C.parties.mapM fun i =>
    if h : j ∈ D.1 ∧ i ∉ D.1 then
      let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
      program (.derive .seedGen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1])
        (((corrupt j).map (·.pairKey i)).getD 0)
    else pure true
  pure ()

/-- The actual simulator with its emulated key values retained. -/
def seedGenEmulation (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (st : SimulatorState C Unit A.State) (parameter : PublicParameter)
    (corrupt : C.Party → Option (Keys C)) :
    OracleComp (WorldSpec C) (SimulatorState C Unit A.State × (C.Party → Option (Keys C))) := do
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) =>
    (sampleParts : ProbComp (Parts C))) _)
  let steps ← startSteps worldRoles D fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))
  let ((state, steps, sent), calls) ← (stepRound observedRoles D A noFunctionality st.adversary steps).run
  let log := st.log ++ calls
  let high ← free (liftComp ($ᵗ HashOutput) _)
  seedGenProgramBlock D parts log sent parameter corrupt high
  let ((state, keys), rest) ← (executeRounds observedRoles D A noFunctionality
    (setupRounds - 1) state steps).run
  pure (⟨state, log ++ rest, st.corrupt⟩, keys)

theorem seedGenSimulator_answer_emulation (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (st : SimulatorState C Unit A.State)
    (parameter : PublicParameter) (corrupt : C.Party → Option (Keys C)) :
    (seedGenSimulator D A).answer st (parameter, corrupt) =
      (fun r => (r.1, Finset.univ.filter fun i => (r.2 i).isSome)) <$>
        seedGenEmulation D A st parameter corrupt := by
  simp only [seedGenSimulator, seedGenEmulation, seedGenProgramBlock, seedGenProgramView,
    seedGenFirstHonest, seedGenFullParameter, map_bind, map_pure, bind_assoc, pure_bind]
  rfl

/-- One common game retains both the emulated outputs and the dealer's keys. -/
def seedGenCommonGame (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    OracleComp (WorldSpec C) (A.State × (C.Party → Option (Keys C)) × (C.Party → Keys C)) := do
  let st ← (seedGenSimulator D A).start (corruptInputs D x) z
  let (parameter, _, keys) ← free (liftComp (prawnsKeyGen (C := C)) (LocalSpec C))
  let (st, emulated) ← seedGenEmulation D A st parameter fun i =>
    if i ∈ D.1 then some (keys i) else none
  pure (st.adversary, emulated, keys)

def seedGenIdealProjection {σ : Type*} (D : C.Coalition)
    (r : σ × (C.Party → Option (Keys C)) × (C.Party → Keys C)) :
    σ × (C.Party → Option (Keys C)) :=
  (r.1, fun i => if i ∉ D.1 ∧ (r.2.1 i).isSome then some (r.2.2 i) else none)

/-- The ideal marginal is exactly the specified functionality and simulator, for every run. -/
theorem seedGenCommonGame_ideal (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) :
    seedGenIdealProjection D <$> seedGenCommonGame D A x z =
      idealExecution (fun oa => oa) D FseedGen (seedGenSimulator D A) x z := by
  rw [idealExecution_FseedGen]
  unfold seedGenCommonGame
  simp only [map_bind, map_pure]
  apply bind_congr
  intro st
  apply bind_congr
  rintro ⟨parameter, seeds, keys⟩
  erw [seedGenSimulator_answer_emulation, bind_map_left]
  apply bind_congr
  rintro ⟨st, emulated⟩
  change pure (seedGenIdealProjection D (st.adversary, emulated, keys)) =
    (pure st.adversary >>= fun out => pure (out, fun i =>
      if i ∉ D.1 ∧ i ∈ Finset.univ.filter (fun i => (emulated i).isSome)
      then some (keys i) else none))
  simp only [pure_bind, seedGenIdealProjection, Finset.mem_filter, Finset.mem_univ, true_and]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
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
def seedGenCrossList (D : C.Coalition) : List (C.Party × C.Party) :=
  (C.parties.product C.parties).filter fun p => p.1 ∈ D.1 ∧ p.2 ∉ D.1

theorem seedGenCrossList_mem (D : C.Coalition) (p : C.Party × C.Party) :
    p ∈ seedGenCrossList D ↔ p.1 ∈ D.1 ∧ p.2 ∉ D.1 := by
  rcases p with ⟨j, i⟩
  simp [seedGenCrossList, Committee.parties, List.mem_product, List.mem_finRange]

def seedGenCrossPair (D : C.Coalition) (p : {p // p ∈ seedGenCrossList D}) : C.Pair :=
  C.pairOf p.1.2 p.1.1 (fun e => (seedGenCrossList_mem D p.1).mp p.2 |>.2
    (e ▸ ((seedGenCrossList_mem D p.1).mp p.2).1))

theorem seedGenCrossPair_injective (D : C.Coalition) : Function.Injective (seedGenCrossPair D) := by
  intro p q h
  apply Subtype.ext
  have hp := (seedGenCrossList_mem D p.1).mp p.2
  have hq := (seedGenCrossList_mem D q.1).mp q.2
  have he := pairOf_cross_injective D p.1.2 p.1.1 q.1.2 q.1.1 hp.1 hp.2 hq.1 hq.2 h
  exact Prod.ext he.2 he.1

def seedGenCrossCoordinates (D : C.Coalition) : List C.Pair :=
  (seedGenCrossList D).attach.map (seedGenCrossPair D)

theorem seedGenCrossCoordinates_nodup (D : C.Coalition) : (seedGenCrossCoordinates D).Nodup := by
  apply List.Nodup.map (seedGenCrossPair_injective D)
  apply List.Nodup.attach
  apply List.Nodup.filter
  exact List.Nodup.product (List.nodup_finRange _) (List.nodup_finRange _)

def seedGenKnownCoordinates (D : C.Coalition) : List C.Term :=
  C.terms.filter fun T => KnownTo D.1 T

theorem seedGenKnownCoordinates_nodup (D : C.Coalition) : (seedGenKnownCoordinates D).Nodup := by
  apply List.Nodup.filter
  exact Finset.nodup_toList _

theorem seedGenDealer_known_value (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (T : C.Term) (j : C.Party)
    (hj : j ∈ D.1) (hT : j ∈ C.holders T) :
    (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.seed T)).getD 0) = seeds T := by
  simp [hj, dealtKeys, hT]

theorem seedGenDealer_cross_value (D : C.Coalition) (parameter : PublicParameter)
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

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
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
    (do let table ← $ᵗ (ι → HashOutput)
        (programValues (indices.map inputs) (indices.map table)).run s) =ᵈ
      (uniformPrograms (indices.map inputs)).run s := by
  have h := evalDist_uniform_table_list (R := HashOutput) indices hnd
  calc
    _ = (((fun table : ι → HashOutput => indices.map table) <$> ($ᵗ (ι → HashOutput))) >>=
      fun ys => (programValues (indices.map inputs) ys).run s) := by rw [bind_map_left]
    _ =ᵈ ((indices.mapM fun _ => $ᵗ HashOutput) >>= fun ys =>
      (programValues (indices.map inputs) ys).run s) := h.bind_left _
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
    (tablePrograms indices inputs).run s =ᵈ
      (uniformPrograms (indices.map inputs)).run s := by
  simp only [tablePrograms, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  exact evalDist_table_programValues indices hnd inputs s

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

def seedGenEraseLog {α : Type} (p : WriterT (CallLog C) (OracleComp (WorldSpec C)) α) :
    OracleComp (WorldSpec C) α := Prod.fst <$> p.run

theorem seedGenEraseLog_pure {α : Type} (a : α) : seedGenEraseLog (C := C) (pure a) = pure a := by
  simp [seedGenEraseLog]

theorem seedGenEraseLog_bind {α β : Type}
    (p : WriterT (CallLog C) (OracleComp (WorldSpec C)) α)
    (k : α → WriterT (CallLog C) (OracleComp (WorldSpec C)) β) :
    seedGenEraseLog (p >>= k) = seedGenEraseLog p >>= fun a => seedGenEraseLog (k a) := by
  simp [seedGenEraseLog, WriterT.run_bind, map_bind, Functor.map_map, bind_map_left]

theorem seedGenEraseLog_lift {α : Type} (p : OracleComp (WorldSpec C) α) :
    seedGenEraseLog (liftM p) = p := by
  simp [seedGenEraseLog, WriterT.run_liftM, Functor.map_map]

theorem seedGenEraseLog_sequenceFin {α : Type} : ∀ {n : ℕ}
    (p : Fin n → WriterT (CallLog C) (OracleComp (WorldSpec C)) α),
    seedGenEraseLog (OverPermutation.sequenceFin p) = OverPermutation.sequenceFin fun i => seedGenEraseLog (p i)
  | 0, p => by simp [OverPermutation.sequenceFin, seedGenEraseLog_pure]
  | n + 1, p => by
    simp only [OverPermutation.sequenceFin, seedGenEraseLog_bind, seedGenEraseLog_pure,
      seedGenEraseLog_sequenceFin]

theorem fst_observe {α : Type} (p : OracleComp (LocalSpec C) α) :
    Prod.fst <$> observe p = worldRoles.adversary p := by
  change seedGenEraseLog (simulateQ _ p) = _
  induction p using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure, seedGenEraseLog_pure, worldRoles_adversary_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, seedGenEraseLog_bind, ih]
    rw [show worldRoles.adversary (liftM (OracleSpec.query t) >>= k) =
      worldRoles.adversary (liftM (OracleSpec.query t)) >>= fun a => worldRoles.adversary (k a) by
        change counted (liftComp (liftM (OracleSpec.query t) >>= k) (SimulatorSpec C)) = _
        rw [liftComp_bind, counted_bind]
        rfl]
    congr 1
    rcases t with t | (q | x)
    · simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      exact seedGenEraseLog_lift _
    · simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      simp only [seedGenEraseLog_bind, seedGenEraseLog_lift, seedGenEraseLog_pure]
      simp [seedGenEraseLog, WriterT.run_tell, map_pure]
      rfl
    · simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
      exact seedGenEraseLog_lift _

theorem seedGenEraseLog_adversary {α : Type} (p : OracleComp (LocalSpec C) α) :
    seedGenEraseLog (observedRoles.adversary p) = worldRoles.adversary p := fst_observe p

theorem seedGenEraseLog_honest {α : Type} (p : OracleComp (LocalSpec C) α) :
    seedGenEraseLog (observedRoles.honest p) = worldRoles.honest p := seedGenEraseLog_lift _

theorem seedGenEraseLog_stepRound (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec (Keys C)) :
    seedGenEraseLog (stepRound observedRoles D A noFunctionality state steps) =
      stepRound worldRoles D A noFunctionality state steps := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real]), if_neg (by simp [callInput_real])]
  simp only [seedGenEraseLog_bind, seedGenEraseLog_adversary, seedGenEraseLog_pure,
    seedGenEraseLog_sequenceFin]
  apply bind_congr
  intro r
  congr 1
  congr 1
  funext j
  cases hs : steps j with
  | done out => exact seedGenEraseLog_pure _
  | wait outbox resume =>
    by_cases hj : j ∈ D.1
    · simp [hj, seedGenEraseLog_pure]
    · simp [hj, seedGenEraseLog_honest]
  | call input resume => exact input.elim

theorem seedGenEraseLog_executeRounds (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :
    ∀ fuel state (steps : C.Party → Step C E RealSpec (Keys C)),
      seedGenEraseLog (executeRounds observedRoles D A noFunctionality fuel state steps) =
        executeRounds worldRoles D A noFunctionality fuel state steps
  | 0, state, steps => by simp [executeRounds, seedGenEraseLog_pure]
  | fuel + 1, state, steps => by
    simp only [executeRounds]
    split_ifs
    · exact seedGenEraseLog_pure _
    · simp only [seedGenEraseLog_bind, seedGenEraseLog_stepRound, seedGenEraseLog_executeRounds]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
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

theorem seedGen_mapM_congr {m : Type → Type} [Monad m] [LawfulMonad m]
    {α β : Type} (xs : List α) (f g : α → m β) (h : ∀ x ∈ xs, f x = g x) :
    xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.mapM_cons, h x (List.mem_cons_self ..),
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

def seedGenTermProgrammingInput (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (T : C.Term) : Query C :=
  .derive .seedGen .term ((C.parties.filter (· ∈ C.holders T)).map fun k =>
    (view (seedGenFirstHonest D (C.holders T)) k).term T)

def seedGenPairProgrammingInput (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (p : C.Pair) : Query C :=
  let i := if p.1.1 ∈ D.1 then p.1.2 else p.1.1
  .derive .seedGen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1]

theorem seedGenPairProgrammingInput_cross (D : C.Coalition)
    (view : C.Party → C.Party → Parts C) (i j : C.Party) (h : j ∈ D.1 ∧ i ∉ D.1) :
    seedGenPairProgrammingInput D view (C.pairOf i j (fun e => h.2 (e ▸ h.1))) =
      .derive .seedGen .pair
        [(view i (C.pairOf i j (fun e => h.2 (e ▸ h.1))).1.1).pair
            (C.pairOf i j (fun e => h.2 (e ▸ h.1))).1.2,
          (view i (C.pairOf i j (fun e => h.2 (e ▸ h.1))).1.2).pair
            (C.pairOf i j (fun e => h.2 (e ▸ h.1))).1.1] := by
  unfold seedGenPairProgrammingInput Committee.pairOf
  split_ifs <;> simp_all

theorem seedGenKnown_find (D : C.Coalition) (T : C.Term) :
    (C.parties.find? fun j => j ∈ D.1 ∧ j ∈ C.holders T).isSome ↔ KnownTo D.1 T := by
  simp [List.find?_isSome, Committee.parties, List.mem_finRange, KnownTo]

theorem seedGenProgramTerms_dealt (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) :
    (C.terms.mapM (fun T => match C.parties.find? (fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
      | some j => program (seedGenTermProgrammingInput D view T)
          (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.seed T)).getD 0)
      | none => pure true) >>= fun _ => pure ()) =
    ((seedGenKnownCoordinates D).mapM (fun T =>
      program (seedGenTermProgrammingInput D view T) (seeds T)) >>= fun _ => pure ()) := by
  have he : (fun T => match C.parties.find? (fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
      | some j => program (seedGenTermProgrammingInput D view T)
          (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.seed T)).getD 0)
      | none => pure true) = (fun T => if KnownTo D.1 T then
        program (seedGenTermProgrammingInput D view T) (seeds T) else pure true) := by
    funext T
    cases hf : C.parties.find? (fun j => j ∈ D.1 ∧ j ∈ C.holders T) with
    | none =>
      have hn : ¬ KnownTo D.1 T := by rw [← seedGenKnown_find, hf]; simp
      simp [hn]
    | some j =>
      have hj : j ∈ D.1 ∧ j ∈ C.holders T := by
        simpa only [decide_eq_true_eq] using List.find?_some hf
      simp only [if_pos (show KnownTo D.1 T from ⟨j, hj⟩),
        seedGenDealer_known_value D parameter seeds pairs T j hj.1 hj.2]
  rw [he, discard_mapM_filter C.terms (fun T => decide (KnownTo D.1 T)) _ true
    (by intro T _ h; simp_all)]
  congr 1
  apply seedGen_mapM_congr
  intro T hT
  exact if_pos (by simpa only [List.mem_filter, decide_eq_true_eq] using (List.mem_filter.mp hT).2)

theorem seedGenProgramPairs_coordinates (D : C.Coalition)
    (view : C.Party → C.Party → Parts C) (pairs : C.Pair → HashOutput) :
    (C.parties.mapM (fun j => C.parties.mapM (fun i =>
      if h : j ∈ D.1 ∧ i ∉ D.1 then
        program (seedGenPairProgrammingInput D view (C.pairOf i j (fun e => h.2 (e ▸ h.1))))
          (pairs (C.pairOf i j (fun e => h.2 (e ▸ h.1))))
      else pure true)) >>= fun _ => pure ()) =
    ((seedGenCrossCoordinates D).mapM (fun p =>
      program (seedGenPairProgrammingInput D view p) (pairs p)) >>= fun _ => pure ()) := by
  rw [discard_mapM_product]
  let f : C.Party × C.Party → OracleComp (WorldSpec C) Bool := fun p =>
    if h : p.1 ∈ D.1 ∧ p.2 ∉ D.1 then
      program (seedGenPairProgrammingInput D view (C.pairOf p.2 p.1 (fun e => h.2 (e ▸ h.1))))
        (pairs (C.pairOf p.2 p.1 (fun e => h.2 (e ▸ h.1))))
    else pure true
  change ((C.parties.product C.parties).mapM f >>= fun _ => pure ()) = _
  rw [discard_mapM_filter _ (fun p => decide (p.1 ∈ D.1 ∧ p.2 ∉ D.1)) f true
    (by intro p _ h; simp_all [f])]
  unfold seedGenCrossCoordinates
  rw [List.mapM_map]
  have hm : ((seedGenCrossList D).attach.mapM (fun p =>
        program (seedGenPairProgrammingInput D view (seedGenCrossPair D p))
          (pairs (seedGenCrossPair D p)))) = (seedGenCrossList D).mapM f := by
    rw [List.mapM_subtype (g := f) (by
      intro p hp
      have hd := (seedGenCrossList_mem D p).mp hp
      simp only [f, dif_pos hd, seedGenCrossPair])]
    simp
  change ((seedGenCrossList D).mapM f >>= fun _ => pure ()) = _
  simpa only [Function.comp_def] using congrArg (fun p : OracleComp (WorldSpec C) (List Bool) => p >>= fun _ => pure ()) hm.symm

/-- The full actual programming block on a dealer leak is a parameter attempt, followed by
one attempt per known term and one per corrupt--honest pair. -/
theorem seedGenProgramBlock_dealt (D : C.Coalition) (parts : C.Party → Parts C)
    (log : CallLog C) (sent : C.Party → Mail C E) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (high : HashOutput) :
    seedGenProgramBlock D parts log sent parameter
      (fun j => if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none) high = (do
      let view := seedGenProgramView D parts log sent
      let _ ← program (.derive .seedGen .parameter
        (C.parties.map fun j => (view (seedGenFirstHonest D Finset.univ) j).parameter))
        (seedGenFullParameter high parameter)
      let _ ← (seedGenKnownCoordinates D).mapM fun T =>
        program (seedGenTermProgrammingInput D view T) (seeds T)
      let _ ← (seedGenCrossCoordinates D).mapM fun p =>
        program (seedGenPairProgrammingInput D view p) (pairs p)
      pure ()) := by
  unfold seedGenProgramBlock
  apply bind_congr
  intro _
  let view := seedGenProgramView D parts log sent
  have hp := seedGenProgramPairs_coordinates D view pairs
  have hpair : (C.parties.mapM (fun j => C.parties.mapM (fun i =>
      if h : j ∈ D.1 ∧ i ∉ D.1 then
        let p := C.pairOf i j (fun e => h.2 (e ▸ h.1))
        program (.derive .seedGen .pair [(view i p.1.1).pair p.1.2, (view i p.1.2).pair p.1.1])
          (((if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none).map (·.pairKey i)).getD 0)
      else pure true)) >>= fun _ => pure ()) =
      ((seedGenCrossCoordinates D).mapM (fun p =>
        program (seedGenPairProgrammingInput D view p) (pairs p)) >>= fun _ => pure ()) := by
    rw [← hp]
    congr 1
    apply seedGen_mapM_congr
    intro j _
    apply seedGen_mapM_congr
    intro i _
    by_cases h : j ∈ D.1 ∧ i ∉ D.1
    · simp only [dif_pos h, seedGenDealer_cross_value D parameter seeds pairs i j h,
        seedGenPairProgrammingInput_cross D view i j h]
    · simp only [dif_neg h]
  change (_ >>= fun _ => _ ) = (_ >>= fun _ => _)
  conv_lhs => arg 2; ext; rw [hpair]
  have ht := seedGenProgramTerms_dealt D view parameter seeds pairs
  have he := congrArg (fun p : OracleComp (WorldSpec C) Unit => p >>= fun _ =>
    (seedGenCrossCoordinates D).mapM (fun p => program (seedGenPairProgrammingInput D view p) (pairs p))
      >>= fun _ => pure ()) ht
  simp only [bind_assoc, pure_bind] at he
  convert he using 1 <;> rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Private sampling commutes with any independent computation on the oracle cache. -/
theorem commutes_private_stateT {σ α β : Type} (p : ProbComp α) (m : StateT σ ProbComp β) :
    Commutes (StateT.lift p) m := by
  intro s
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  exact OracleComp.EvalDistEq.bind_bind_swap _ _ _

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
    ((do
      let parameter ← StateT.lift ($ᵗ PublicParameter)
      let high ← StateT.lift ($ᵗ HashOutput)
      let _ ← programAnswer (q, seedGenFullParameter high parameter)
      pure () : StateT (HashCache C) ProbComp Unit)).run s =ᵈ
      (uniformProgram q).run s := by
  let p : ProbComp HashOutput := do
    let parameter ← $ᵗ PublicParameter
    let high ← $ᵗ HashOutput
    pure (seedGenFullParameter high parameter)
  have hp : p =ᵈ $ᵗ HashOutput := evalDist_seedGenFullParameter
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
    uniformProgram, StateT.run_pure]
  change (p >>= fun y => (programAnswer (q, y)).run s >>= fun r => pure ((), r.2)) =ᵈ _
  exact hp.bind_left _

/-- The actual independent dealer samples followed by the simulator's programming block. -/
def seedGenDealerPrograms (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E) :
    StateT (HashCache C) ProbComp Unit := do
  let parameter ← StateT.lift ($ᵗ PublicParameter)
  let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
  let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
  let high ← StateT.lift ($ᵗ HashOutput)
  simulateQ (worldAnswer prims) (seedGenProgramBlock D parts log sent parameter
    (fun j => if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none) high)

def seedGenParameterProgrammingInput (D : C.Coalition) (view : C.Party → C.Party → Parts C) : Query C :=
  .derive .seedGen .parameter (C.parties.map fun j => (view (seedGenFirstHonest D Finset.univ) j).parameter)

def parameterProgram (q : Query C) (parameter : PublicParameter) : StateT (HashCache C) ProbComp Unit := do
  let high ← StateT.lift ($ᵗ HashOutput)
  let _ ← programAnswer (q, seedGenFullParameter high parameter)
  pure ()

theorem seedGenDealerPrograms_expand (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E) :
    seedGenDealerPrograms prims D parts log sent = (do
      let parameter ← StateT.lift ($ᵗ PublicParameter)
      let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
      let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
      let view := seedGenProgramView D parts log sent
      parameterProgram (seedGenParameterProgrammingInput D view) parameter
      programValues ((seedGenKnownCoordinates D).map (seedGenTermProgrammingInput D view))
        ((seedGenKnownCoordinates D).map seeds)
      programValues ((seedGenCrossCoordinates D).map (seedGenPairProgrammingInput D view))
        ((seedGenCrossCoordinates D).map pairs)) := by
  unfold seedGenDealerPrograms
  simp only [seedGenProgramBlock_dealt]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro seeds
  apply bind_congr
  intro pairs
  simp only [parameterProgram, seedGenParameterProgrammingInput, bind_assoc, pure_bind,
    simulateQ_bind, simulateQ_world_program, simulateQ_pure]
  apply bind_congr
  intro high
  apply bind_congr
  intro _
  rw [← simulateQ_programValues prims (seedGenKnownCoordinates D),
    ← simulateQ_programValues prims (seedGenCrossCoordinates D)]
  simp only [simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind]

/-- The dealer tables can be delayed until their own programming blocks. -/
theorem evalDist_seedGenDealerPrograms_reorder (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E) (s : HashCache C) :
    (seedGenDealerPrograms prims D parts log sent).run s =ᵈ
    ((do
      let parameter ← StateT.lift ($ᵗ PublicParameter)
      let view := seedGenProgramView D parts log sent
      parameterProgram (seedGenParameterProgrammingInput D view) parameter
      tablePrograms (seedGenKnownCoordinates D) (seedGenTermProgrammingInput D view)
      tablePrograms (seedGenCrossCoordinates D) (seedGenPairProgrammingInput D view)
      : StateT (HashCache C) ProbComp Unit)).run s := by
  rw [seedGenDealerPrograms_expand]
  apply evalDist_run_bind_congr
  intro parameter s'
  let view := seedGenProgramView D parts log sent
  let pp := parameterProgram (seedGenParameterProgrammingInput D view) parameter
  let kt := (seedGenKnownCoordinates D).map (seedGenTermProgrammingInput D view)
  let kp := (seedGenCrossCoordinates D).map (seedGenPairProgrammingInput D view)
  let ts (seeds : C.Term → HashOutput) := programValues kt ((seedGenKnownCoordinates D).map seeds)
  let ps (pairs : C.Pair → HashOutput) := programValues kp ((seedGenCrossCoordinates D).map pairs)
  change ((do
    let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
    let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
    pp
    ts seeds
    ps pairs) : StateT (HashCache C) ProbComp Unit).run s' =ᵈ _
  refine EvalDistEq.trans (my := ((do
    let seeds ← StateT.lift ($ᵗ (C.Term → HashOutput))
    pp
    ts seeds
    let pairs ← StateT.lift ($ᵗ (C.Pair → HashOutput))
    ps pairs) : StateT (HashCache C) ProbComp Unit).run s') ?_ ?_
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

def seedGenProgrammingInputs (D : C.Coalition) (view : C.Party → C.Party → Parts C) : List (Query C) :=
  seedGenParameterProgrammingInput D view ::
    (seedGenKnownCoordinates D).map (seedGenTermProgrammingInput D view) ++
    (seedGenCrossCoordinates D).map (seedGenPairProgrammingInput D view)

theorem seedGenProgrammingInputs_not_fixed (D : C.Coalition) (view : C.Party → C.Party → Parts C)
    (q : Query C) (hq : q ∈ seedGenProgrammingInputs D view) : ¬ IsFixed q := by
  simp only [seedGenProgrammingInputs, List.mem_cons, List.mem_append, List.mem_map] at hq
  rcases hq with (rfl | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩ <;>
    simp [IsFixed, seedGenParameterProgrammingInput, seedGenTermProgrammingInput, seedGenPairProgrammingInput]

/-- After forgetting the dealer values, the exact simulator block has the cache distribution
of independent uniform programming at its actual inputs. -/
theorem evalDist_seedGenDealerPrograms (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E) (s : HashCache C) :
    (seedGenDealerPrograms prims D parts log sent).run s =ᵈ
      (uniformPrograms (seedGenProgrammingInputs D (seedGenProgramView D parts log sent))).run s := by
  refine (evalDist_seedGenDealerPrograms_reorder prims D parts log sent s).trans ?_
  let view := seedGenProgramView D parts log sent
  let kt := (seedGenKnownCoordinates D).map (seedGenTermProgrammingInput D view)
  let kp := (seedGenCrossCoordinates D).map (seedGenPairProgrammingInput D view)
  refine EvalDistEq.trans (my := ((do
    let parameter ← StateT.lift ($ᵗ PublicParameter)
    parameterProgram (seedGenParameterProgrammingInput D view) parameter
    uniformPrograms kt
    uniformPrograms kp) : StateT (HashCache C) ProbComp Unit).run s) ?_ ?_
  · apply evalDist_run_bind_congr
    intro parameter s'
    apply evalDist_run_bind_congr
    intro _ s''
    refine (evalDist_run_bind_of_eq
      (fun _ : Unit => tablePrograms (seedGenCrossCoordinates D) (seedGenPairProgrammingInput D view)) s''
      (evalDist_tablePrograms (seedGenKnownCoordinates D) (seedGenKnownCoordinates_nodup D)
        (seedGenTermProgrammingInput D view) s'')).trans ?_
    apply evalDist_run_bind_congr
    intro _ s'''
    exact evalDist_tablePrograms (seedGenCrossCoordinates D) (seedGenCrossCoordinates_nodup D)
      (seedGenPairProgrammingInput D view) s'''
  · have he := evalDist_run_bind_of_eq
      (fun _ : Unit => uniformPrograms kt >>= fun _ => uniformPrograms kp) s
      (evalDist_parameterProgramming (seedGenParameterProgrammingInput D view) s)
    simpa only [parameterProgram, seedGenProgrammingInputs, uniformPrograms, uniformPrograms_append,
      bind_assoc, pure_bind, view, kt, kp] using he

/-- Exact erasure of the specified simulator's dealer programming, before any local continuation.
It is valid for every cache and extracted view, including failed extraction or programming. -/
theorem evalDist_seedGenDealerPrograms_prepend (prims : Primitives) (D : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E)
    {α : Type} (k : OracleComp (LocalSpec C) α) (s : HashCache C) :
    (seedGenDealerPrograms prims D parts log sent >>= fun _ =>
      simulateQ (localAnswer prims) k).run' s =ᵈ
      (simulateQ (localAnswer prims) k).run' s := by
  have he := evalDist_run_bind_of_eq (fun _ : Unit => simulateQ (localAnswer prims) k) s
    (evalDist_seedGenDealerPrograms prims D parts log sent s)
  have hm := he.map Prod.fst
  simp only [StateT.run'_eq]
  refine hm.trans ?_
  simpa only [StateT.run'_eq] using evalDist_uniformPrograms_prepend prims
    (seedGenProgrammingInputs D (seedGenProgramView D parts log sent))
    (seedGenProgrammingInputs_not_fixed D _) k s

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
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
  exact map_eq_bind_pure_comp (m := ProbComp) _ _

/-- The unobserved real execution with all private parts sampled before the commits. -/
def seedGenPartsWorldGame (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    OracleComp (WorldSpec C) Bool := do
  let state ← worldRoles.adversary (A.start (corruptInputs D x) z)
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) =>
    (sampleParts : ProbComp (Parts C))) (LocalSpec C))
  let steps ← startSteps worldRoles D fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))
  let (state, steps, _) ← stepRound worldRoles D A noFunctionality state steps
  let out ← executeRounds worldRoles D A noFunctionality (setupRounds - 1) state steps
  worldRoles.adversary (Z out)

theorem simulateQ_seedGenPartsWorldGame (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    simulateQ (worldAnswer prims) (seedGenPartsWorldGame D A x z Z) =
      simulateQ (localAnswer prims)
        (seedGenLocalCommitPrefix D A x z >>= seedGenLocalPostCommit D A Z) := by
  unfold seedGenPartsWorldGame seedGenLocalCommitPrefix seedGenLocalPostCommit
  simp only [simulateQ_bind, bind_assoc, pure_bind, simulateQ_world_adversary,
    simulateQ_world_executeRounds]
  apply bind_congr
  intro state
  rw [simulateQ_free, liftComp_sequenceFin]
  apply bind_congr
  intro parts
  rw [simulateQ_startSteps_real, seedGenMapRoles_world, ← simulateQ_startSteps_real,
    startSteps_seedGenWith, simulateQ_map, bind_map_left]
  apply bind_congr
  intro commitments
  rw [simulateQ_stepRound_real, seedGenMapRoles_world, ← simulateQ_stepRound_real]

/-- The parts-first game has exactly the real acceptance probability. -/
theorem seedGenPartsWorldGame_accepts (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    accepts prims (seedGenPartsWorldGame D A x z Z) =
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z) Z) := by
  have hp : accepts prims (seedGenPartsWorldGame D A x z Z) =
      (Pr{let y ← (simulateQ (worldAnswer prims) (seedGenPartsWorldGame D A x z Z)).run' ∅}[y = true]).toReal := by
    rw [← fst_map_runWorld]
    unfold accepts
    rw [prEvent_map]
  rw [hp, simulateQ_seedGenPartsWorldGame]
  have he := (sameRun_seedGenLocal_split prims D A x z Z).run'_eq
  exact (congrArg ENNReal.toReal (he.symm.prEvent_eq _)).trans (seedGenLocalGame_accepts prims D A x z Z)

abbrev SeedGenObservedCommitData (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) :=
  (C.Party → Parts C) × A.State × (C.Party → Step C E RealSpec (Keys C)) × (C.Party → Mail C E) × CallLog C

def seedGenObservedCommit (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) :
    OracleComp (WorldSpec C) (SeedGenObservedCommitData D A) := do
  let parts ← free (liftComp (OverPermutation.sequenceFin fun (_ : C.Party) =>
    (sampleParts : ProbComp (Parts C))) _)
  let steps ← startSteps worldRoles D fun i => (seedGenWith i (parts i) : PartyM C E RealSpec (Keys C))
  let (r, calls) ← (stepRound observedRoles D A noFunctionality state steps).run
  pure (parts, r.1, r.2.1, r.2.2, calls)

def seedGenObservedPost (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C)) (state : A.State)
    (steps : C.Party → Step C E RealSpec (Keys C)) : OracleComp (WorldSpec C) Bool := do
  let (out, _) ← (executeRounds observedRoles D A noFunctionality (setupRounds - 1) state steps).run
  worldRoles.adversary (Z out)

theorem seedGenObservedPost_eq (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (Z : Distinguisher C A.State (Keys C)) (state : A.State)
    (steps : C.Party → Step C E RealSpec (Keys C)) :
    seedGenObservedPost D A Z state steps = (do
      let out ← executeRounds worldRoles D A noFunctionality (setupRounds - 1) state steps
      worldRoles.adversary (Z out)) := by
  unfold seedGenObservedPost
  rw [← seedGenEraseLog_executeRounds D A (setupRounds - 1) state steps]
  simp only [seedGenEraseLog, bind_map_left]

theorem simulateQ_seedGenObservedPost (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (Z : Distinguisher C A.State (Keys C))
    (state : A.State) (steps : C.Party → Step C E RealSpec (Keys C)) :
    simulateQ (worldAnswer prims) (seedGenObservedPost D A Z state steps) =
      simulateQ (localAnswer prims) (do
        let out ← executeRounds localRoles D A noFunctionality (setupRounds - 1) state steps
        Z out) := by
  rw [seedGenObservedPost_eq]
  simp only [simulateQ_bind, simulateQ_world_executeRounds, simulateQ_world_adversary]

def seedGenObservedPartsGame (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    OracleComp (WorldSpec C) Bool := do
  let (state, _) ← observe (A.start (corruptInputs D x) z)
  let r ← seedGenObservedCommit D A state
  seedGenObservedPost D A Z r.2.1 r.2.2.1

theorem seedGenObservedPartsGame_eq (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    seedGenObservedPartsGame D A x z Z = seedGenPartsWorldGame D A x z Z := by
  unfold seedGenObservedPartsGame seedGenPartsWorldGame seedGenObservedCommit
  simp only [bind_assoc, pure_bind, seedGenObservedPost_eq]
  rw [← fst_observe (A.start (corruptInputs D x) z), bind_map_left]
  apply bind_congr
  intro st
  apply bind_congr
  intro parts
  apply bind_congr
  intro steps
  rw [← seedGenEraseLog_stepRound D A st.1 steps]
  simp only [seedGenEraseLog, bind_map_left]

def seedGenDealerSamples : ProbComp (PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput)) := do
  let parameter ← $ᵗ PublicParameter
  let seeds ← $ᵗ (C.Term → HashOutput)
  let pairs ← $ᵗ (C.Pair → HashOutput)
  pure (parameter, seeds, pairs)

def seedGenEmulatedProjection {σ : Type*} (r : σ × (C.Party → Option (Keys C)) × (C.Party → Keys C)) := (r.1, r.2.1)

def seedGenCommonEmulatedGame (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) : OracleComp (WorldSpec C) Bool :=
  distinguish (seedGenEmulatedProjection <$> seedGenCommonGame D A x z) Z

/-- Exact normal form of the common game's emulated-output marginal. -/
theorem seedGenCommonEmulatedGame_expand (D : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    seedGenCommonEmulatedGame D A x z Z = (do
      let (state, log) ← observe (A.start (corruptInputs D x) z)
      let (parameter, seeds, pairs) ← free (liftComp (seedGenDealerSamples (C := C)) (LocalSpec C))
      let r ← seedGenObservedCommit D A state
      let high ← free (liftComp ($ᵗ HashOutput) (LocalSpec C))
      seedGenProgramBlock D r.1 (log ++ r.2.2.2.2) r.2.2.2.1 parameter
        (fun j => if j ∈ D.1 then some (dealtKeys parameter seeds pairs j) else none) high
      seedGenObservedPost D A Z r.2.1 r.2.2.1) := by
  unfold seedGenCommonEmulatedGame distinguish seedGenCommonGame seedGenEmulation
    seedGenObservedCommit seedGenObservedPost seedGenDealerSamples prawnsKeyGen
  simp only [map_bind, map_pure, bind_map_left, bind_assoc, pure_bind,
    liftComp_bind, liftComp_pure, free_bind, free_pure, seedGenEmulatedProjection]
  simp only [seedGenSimulator, bind_assoc, pure_bind]

/-- Congruence for output distributions under an arbitrary cache-state prefix. -/
theorem evalDist_stateT_run'_bind_congr {σ α β : Type} (p : StateT σ ProbComp α)
    (f g : α → StateT σ ProbComp β)
    (h : ∀ a s, (f a).run' s =ᵈ (g a).run' s) (s : σ) :
    (p >>= f).run' s =ᵈ (p >>= g).run' s := by
  simp only [StateT.run'_eq, StateT.run_bind, map_bind]
  refine EvalDistEq.bind_right _ fun r => ?_
  exact h r.1 r.2

/-- The common game's emulated-output marginal is exactly the real game, including the final
oracle-aided distinguisher. This statement does not require a good-event assumption. -/
theorem evalDist_seedGenCommonEmulatedGame (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (s : HashCache C) :
    (simulateQ (worldAnswer prims) (seedGenCommonEmulatedGame D A x z Z)).run' s =ᵈ
      (simulateQ (worldAnswer prims) (seedGenPartsWorldGame D A x z Z)).run' s := by
  rw [seedGenCommonEmulatedGame_expand, ← seedGenObservedPartsGame_eq]
  unfold seedGenObservedPartsGame
  simp only [simulateQ_bind, simulateQ_world_sample]
  apply evalDist_stateT_run'_bind_congr
  rintro ⟨state, log⟩ s₁
  let stageRun := simulateQ (worldAnswer prims) (seedGenObservedCommit D A state)
  let afterProgram := fun (dealer : PublicParameter × (C.Term → HashOutput) × (C.Pair → HashOutput))
      (r : SeedGenObservedCommitData D A) => (do
    let high ← StateT.lift ($ᵗ HashOutput)
    simulateQ (worldAnswer prims) (seedGenProgramBlock D r.1 (log ++ r.2.2.2.2) r.2.2.2.1 dealer.1
      (fun j => if j ∈ D.1 then some (dealtKeys dealer.1 dealer.2.1 dealer.2.2 j) else none) high)
    simulateQ (worldAnswer prims) (seedGenObservedPost D A Z r.2.1 r.2.2.1))
  have hs := (commutes_private_stateT (seedGenDealerSamples (C := C)) stageRun).bind afterProgram s₁
  have hs' := hs.map Prod.fst
  rw [← StateT.run'_eq, ← StateT.run'_eq] at hs'
  refine hs'.trans ?_
  apply evalDist_stateT_run'_bind_congr
  intro r s₂
  dsimp only [afterProgram]
  simp only [simulateQ_seedGenObservedPost]
  simpa only [seedGenDealerPrograms, seedGenDealerSamples, StateT.run'_eq, StateT.run_bind,
    StateT.run_lift, bind_assoc, pure_bind, map_bind] using
    evalDist_seedGenDealerPrograms_prepend prims D r.1 (log ++ r.2.2.2.2) r.2.2.2.1
      (do
        let out ← executeRounds localRoles D A noFunctionality (setupRounds - 1) r.2.1 r.2.2.1
        Z out) s₂

/-- Exact real acceptance of the common game's emulated-output projection. -/
theorem seedGenCommonGame_real_accepts (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    accepts prims (seedGenCommonEmulatedGame D A x z Z) =
      accepts prims (distinguish (realExecution D A noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) x z) Z) := by
  rw [← seedGenPartsWorldGame_accepts prims D A x z Z]
  have he := congrArg ENNReal.toReal
    ((evalDist_seedGenCommonEmulatedGame prims D A x z Z ∅).prEvent_eq (· = true))
  simpa only [← fst_map_runWorld, prEvent_map, accepts] using he

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

theorem seedGenFirstHonest_spec (coalition : C.Coalition) (S : Finset C.Party)
    (hex : ∃ i ∈ S, i ∉ coalition.1) : seedGenFirstHonest coalition S ∈ S ∧ seedGenFirstHonest coalition S ∉ coalition.1 := by
  have hs : (C.parties.find? fun i => i ∈ S ∧ i ∉ coalition.1).isSome := by
    simpa only [List.find?_isSome, Committee.parties, List.mem_finRange, true_and, decide_eq_true_eq] using hex
  unfold seedGenFirstHonest
  cases hf : C.parties.find? (fun i => i ∈ S ∧ i ∉ coalition.1) with
  | none => rw [hf] at hs; contradiction
  | some i =>
    simpa only [Option.getD_some, decide_eq_true_eq] using List.find?_some hf

theorem seedGen_honest_holder (coalition : C.Coalition) (T : C.Term) : ∃ i ∈ C.holders T, i ∉ coalition.1 := by
  by_contra hn
  have hs : C.holders T ⊆ coalition.1 := by
    intro i hi
    by_contra hd
    exact hn ⟨i, hi, hd⟩
  have hc := Finset.card_le_card hs
  rw [seedGen_card_holders] at hc
  have hd := coalition.2
  have ht := C.one_le_t
  omega

theorem seedGenFirstHonest_univ (coalition : C.Coalition) : seedGenFirstHonest coalition Finset.univ ∉ coalition.1 :=
  (seedGenFirstHonest_spec coalition Finset.univ (by
    obtain ⟨i, hi⟩ := seedGen_exists_honest coalition
    exact ⟨i, Finset.mem_univ _, hi⟩)).2

theorem seedGenFirstHonest_holder (coalition : C.Coalition) (T : C.Term) :
    seedGenFirstHonest coalition (C.holders T) ∈ C.holders T ∧
      seedGenFirstHonest coalition (C.holders T) ∉ coalition.1 :=
  seedGenFirstHonest_spec coalition _ (seedGen_honest_holder coalition T)

/-- When extraction matches the actual corrupt openings, all fields used in an honest derivation
match the simulator's extracted view. The unused fields need not match. -/
theorem seedGen_derived_programView (prims : Primitives) (coalition : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent : C.Party → Mail C E)
    (revealed : C.Party → Mail C E) (i : C.Party) (hi : i ∉ coalition.1)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .seedGen (parts j) j i)
    (hextract : ∀ j, j ∈ coalition.1 → extractReveal log sent j i = Msg.hashesOf (revealed i j))
    (h : Query C → HashOutput) :
    D prims h (deriveKeys .seedGen i (setupView .seedGen i (parts i) (revealed i))) =
      D prims h (deriveKeys .seedGen i (seedGenProgramView coalition parts log sent i)) := by
  have corrupt (j : C.Party) (hj : j ∈ coalition.1) :
      setupView .seedGen i (parts i) (revealed i) j = seedGenProgramView coalition parts log sent i j := by
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simp only [setupView, if_neg hji, seedGenProgramView, if_pos hj, hextract j hj]
  have parameter (j : C.Party) :
      (setupView .seedGen i (parts i) (revealed i) j).parameter =
        (seedGenProgramView coalition parts log sent i j).parameter := by
    by_cases hj : j ∈ coalition.1
    · rw [corrupt j hj]
    · rw [setupView_honest_sender coalition parts revealed hreceived i j hj, honestView_parameter]
      simp [seedGenProgramView, hj]
  have term (T : C.Term) (hiT : i ∈ C.holders T) (j : C.Party) (hjT : j ∈ C.holders T) :
      (setupView .seedGen i (parts i) (revealed i) j).term T =
        (seedGenProgramView coalition parts log sent i j).term T := by
    by_cases hj : j ∈ coalition.1
    · rw [corrupt j hj]
    · rw [setupView_honest_sender coalition parts revealed hreceived i j hj,
        honestView_term .seedGen parts hjT hiT]
      simp [seedGenProgramView, hj]
  have pair (a b : C.Party) (hab : a = i ∨ b = i) :
      (setupView .seedGen i (parts i) (revealed i) a).pair b =
        (seedGenProgramView coalition parts log sent i a).pair b := by
    by_cases ha : a ∈ coalition.1
    · rw [corrupt a ha]
    · rw [setupView_honest_sender coalition parts revealed hreceived i a ha,
        honestView_pair .seedGen parts hab]
      simp [seedGenProgramView, ha]
  rw [D_deriveKeys, D_deriveKeys]
  simp only [ite_true]
  apply Prod.ext
  · apply congrArg h
    apply congrArg (Query.derive .seedGen .parameter)
    apply List.map_congr_left
    intro j _
    exact parameter j
  · apply Prod.ext
    · funext T
      by_cases hiT : i ∈ C.holders T
      · simp only [if_pos hiT]
        apply congrArg h
        apply congrArg (Query.derive .seedGen .term)
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
        apply congrArg (Query.derive .seedGen .pair)
        exact congrArg₂ List.cons (pair _ _ hp)
          (congrArg (fun y => [y]) (pair _ _ hp.symm))

theorem seedGenCrossCoordinates_cross_mem (coalition : C.Coalition) (i j : C.Party)
    (hj : j ∈ coalition.1) (hi : i ∉ coalition.1) :
    C.pairOf i j (fun e => hi (e ▸ hj)) ∈ seedGenCrossCoordinates coalition := by
  apply List.mem_map.mpr
  have hm : (j, i) ∈ seedGenCrossList coalition := (seedGenCrossList_mem coalition (j, i)).mpr ⟨hj, hi⟩
  exact ⟨⟨(j, i), hm⟩, List.mem_attach _ _, rfl⟩

/-- Successful programming plus the accepting party's honest echo agreements fixes every
parameter, known term and corrupt--honest pair key to the dealer's value. -/
theorem seedGen_known_outputs_of_programmed (prims : Primitives) (coalition : C.Coalition)
    (view : C.Party → C.Party → Parts C) (h : Query C → HashOutput)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (high : HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hderive : ∀ j, j ∉ coalition.1 → keys j = D prims h (deriveKeys .seedGen j (view j)))
    (hparameter : h (seedGenParameterProgrammingInput coalition view) = seedGenFullParameter high parameter)
    (hterm : ∀ T, KnownTo coalition.1 T → h (seedGenTermProgrammingInput coalition view T) = seeds T)
    (hpair : ∀ p ∈ seedGenCrossCoordinates coalition, h (seedGenPairProgrammingInput coalition view p) = pairs p)
    (i : C.Party) (hi : i ∉ coalition.1)
    (hagree : ∀ j, j ∉ coalition.1 →
      (keys i).1 = (keys j).1 ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T →
        (keys i).2.1 T = (keys j).2.1 T) :
    (keysOf (keys i)).parameter = parameter ∧
      (∀ T, KnownTo coalition.1 T → (keysOf (keys i)).seed T = (dealtKeys parameter seeds pairs i).seed T) ∧
      (∀ j, j ∈ coalition.1 → (keysOf (keys i)).pairKey j = (dealtKeys parameter seeds pairs i).pairKey j) := by
  constructor
  · have he := (hagree (seedGenFirstHonest coalition Finset.univ) (seedGenFirstHonest_univ coalition)).1
    change truncateHash (keys i).1 = parameter
    rw [he, hderive _ (seedGenFirstHonest_univ coalition), D_deriveKeys]
    change truncateHash (h (seedGenParameterProgrammingInput coalition view)) = parameter
    rw [hparameter, truncate_seedGenFullParameter]
  constructor
  · intro T hT
    by_cases hiT : i ∈ C.holders T
    · have href := seedGenFirstHonest_holder coalition T
      have he := (hagree (seedGenFirstHonest coalition (C.holders T)) href.2).2 T hiT href.1
      change (keys i).2.1 T = (if i ∈ C.holders T then seeds T else 0)
      rw [if_pos hiT, he, hderive _ href.2, D_deriveKeys]
      simp only [if_pos href.1]
      exact hterm T hT
    · change (keys i).2.1 T = (if i ∈ C.holders T then seeds T else 0)
      rw [hderive i hi, D_deriveKeys]
      simp [hiT]
  · intro j hj
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    have hm := seedGenCrossCoordinates_cross_mem coalition i j hj hi
    have hp := hpair (C.pairOf i j (Ne.symm hji)) hm
    rw [seedGenPairProgrammingInput_cross coalition view i j ⟨hj, hi⟩] at hp
    change (keys i).2.2 j = (if h : j = i then 0 else pairs (C.pairOf i j (Ne.symm h)))
    rw [hderive i hi, D_deriveKeys]
    simp only [dif_neg hji]
    exact hp

/-- The derivation input of a pair of honest operators uses just their original pair parts. -/
theorem seedGen_hiddenPair_input (coalition : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .seedGen (parts j) j i)
    (p : C.Pair) (hp : p.1.1 ∉ coalition.1 ∧ p.1.2 ∉ coalition.1)
    (i : C.Party) (hi : p.1.1 = i ∨ p.1.2 = i) :
    seedGenPairViewInput parts revealed i p = pairInput .seedGen parts p := by
  unfold seedGenPairViewInput pairInput
  dsimp only
  rw [setupView_honest_sender coalition parts revealed hreceived i p.1.1 hp.1,
    setupView_honest_sender coalition parts revealed hreceived i p.1.2 hp.2,
    honestView_pair .seedGen parts hi, honestView_pair .seedGen parts hi.symm]

/-- The actual hidden pair key is the oracle value at its canonical raw-parts input. -/
theorem seedGen_hiddenPair_derived (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .seedGen (parts j) j i)
    (i j : C.Party) (hi : i ∉ coalition.1) (hj : j ∉ coalition.1) (hji : j ≠ i) :
    (D prims h (deriveKeys .seedGen i (setupView .seedGen i (parts i) (revealed i)))).2.2 j =
      h (pairInput .seedGen parts (C.pairOf i j (Ne.symm hji))) := by
  rw [D_deriveKeys]
  simp only [dif_neg hji]
  change h (seedGenPairViewInput parts revealed i (C.pairOf i j (Ne.symm hji))) = _
  apply congrArg h
  apply seedGen_hiddenPair_input coalition parts revealed hreceived
  · unfold Committee.pairOf
    split_ifs <;> exact ⟨by assumption, by assumption⟩
  · exact pairOf_left_or_right i j (Ne.symm hji)

def seedGenHybridSeeds (coalition : C.Coalition) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (seeds : C.Term → HashOutput) : C.Term → HashOutput :=
  fun T => if KnownTo coalition.1 T then seeds T else h (termInput .seedGen parts T)

def seedGenHybridPairs (coalition : C.Coalition) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (pairs : C.Pair → HashOutput) : C.Pair → HashOutput :=
  fun p => if p.1.1 ∉ coalition.1 ∧ p.1.2 ∉ coalition.1 then h (pairInput .seedGen parts p) else pairs p

/-- Under extraction, successful programming, and the accepting party's honest agreements,
its entire key is one dealing. Only the hidden seeds and honest--honest pairs still use raw oracle
values; every exposed coordinate is the dealer's value. -/
theorem seedGen_output_eq_hybrid_dealing (prims : Primitives) (coalition : C.Coalition)
    (parts : C.Party → Parts C) (log : CallLog C) (sent revealed : C.Party → Mail C E)
    (h : Query C → HashOutput) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (high : HashOutput)
    (keys : C.Party → HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .seedGen (parts j) j i)
    (hextract : ∀ i j, i ∉ coalition.1 → j ∈ coalition.1 →
      extractReveal log sent j i = Msg.hashesOf (revealed i j))
    (hderive : ∀ i, i ∉ coalition.1 →
      keys i = D prims h (deriveKeys .seedGen i (setupView .seedGen i (parts i) (revealed i))))
    (hparameter : h (seedGenParameterProgrammingInput coalition (seedGenProgramView coalition parts log sent)) =
      seedGenFullParameter high parameter)
    (hterm : ∀ T, KnownTo coalition.1 T →
      h (seedGenTermProgrammingInput coalition (seedGenProgramView coalition parts log sent) T) = seeds T)
    (hpair : ∀ p ∈ seedGenCrossCoordinates coalition,
      h (seedGenPairProgrammingInput coalition (seedGenProgramView coalition parts log sent) p) = pairs p)
    (i : C.Party) (hi : i ∉ coalition.1)
    (hagree : ∀ j, j ∉ coalition.1 →
      (keys i).1 = (keys j).1 ∧ ∀ T, i ∈ C.holders T → j ∈ C.holders T →
        (keys i).2.1 T = (keys j).2.1 T) :
    keysOf (keys i) = dealtKeys parameter (seedGenHybridSeeds coalition h parts seeds)
      (seedGenHybridPairs coalition h parts pairs) i := by
  have hprogramView : ∀ j, j ∉ coalition.1 →
      keys j = D prims h (deriveKeys .seedGen j (seedGenProgramView coalition parts log sent j)) := by
    intro j hj
    exact (hderive j hj).trans (seedGen_derived_programView prims coalition parts log sent revealed j hj
      hreceived (fun k hk => hextract j k hj hk) h)
  have hk := seedGen_known_outputs_of_programmed prims coalition _ h parameter seeds pairs high keys
    hprogramView hparameter hterm hpair i hi hagree
  unfold keysOf dealtKeys
  congr 1
  · exact hk.1
  · funext T
    by_cases hiT : i ∈ C.holders T
    · simp only [if_pos hiT]
      by_cases hT : KnownTo coalition.1 T
      · rw [seedGenHybridSeeds, if_pos hT]
        simpa only [keysOf, dealtKeys, if_pos hiT] using hk.2.1 T hT
      · rw [seedGenHybridSeeds, if_neg hT, hderive i hi]
        exact seedGen_hiddenTerm_derived prims coalition h parts revealed hreceived T hT i hiT
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
        rw [seedGenHybridPairs, if_neg hn]
        simpa only [keysOf, dealtKeys, dif_neg hji] using hk.2.2 j hj
      · have hh : (C.pairOf i j (Ne.symm hji)).1.1 ∉ coalition.1 ∧
            (C.pairOf i j (Ne.symm hji)).1.2 ∉ coalition.1 := by
          unfold Committee.pairOf
          split_ifs <;> exact ⟨by assumption, by assumption⟩
        rw [seedGenHybridPairs, if_pos hh, hderive i hi]
        exact seedGen_hiddenPair_derived prims coalition h parts revealed hreceived i j hi hj hji

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- Canonical raw-parts derivation inputs, indexed by the model's existing key names. -/
def seedGenNamedInput (parts : C.Party → Parts C) : KeyName C → Query C
  | .parameter => parameterInput parts
  | .term T => termInput .seedGen parts T
  | .pair p => pairInput .seedGen parts p

def seedGenNames (C : Committee) : List (KeyName C) := (Finset.univ : Finset (KeyName C)).toList

theorem seedGenNamedInput_not_fixed (parts : C.Party → Parts C) (name : KeyName C) :
    ¬ IsFixed (seedGenNamedInput parts name) := by
  cases name <;> simp [seedGenNamedInput, parameterInput, termInput, pairInput, IsFixed]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The commit-round continuation only checks abort frames and prepares the reveal. -/
theorem advance_seedGenCommitResume (i : C.Party) (own : Parts C) (committed : Mail C E) :
    advance (exchangeResume (seedGenRound1 i own) committed) =
      pure (if C.parties.any (fun j => Msg.isAbort (committed j)) then .done none else
        .wait (revealOutbox .seedGen i own) (exchangeResume fun revealed =>
          setupRest .seedGen i own committed revealed >>= fun keys => pure (keysOf keys))) := by
  unfold exchangeResume
  split_ifs
  · rfl
  · exact advance_exchange_bind _ _

/-- The inboxes at the commit boundary, including all corrupt abort frames. -/
def seedGenCommitInbox (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) (sent : C.Party → Mail C E) : C.Party → Mail C E :=
  roundInbox coalition sent (seedGenInitialSteps coalition parts commitments)

/-- The actual network state after the commit round. -/
def seedGenRevealSteps (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) : C.Party → Step C E RealSpec (Keys C) := fun i =>
  if i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j)) then .done none else
    .wait (revealOutbox .seedGen i (parts i)) (exchangeResume fun revealed =>
      setupRest .seedGen i (parts i) (committed i) revealed >>= fun keys => pure (keysOf keys))

/-- The first network step computes no hashes after the adversary's commit messages. -/
theorem stepRound_seedGenInitialSteps (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) :
    stepRound localRoles coalition A noFunctionality state
        (seedGenInitialSteps coalition parts commitments) = (do
      let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        commitOutbox i (commitments i) c else none
      pure (st, seedGenRevealSteps coalition parts (seedGenCommitInbox coalition parts commitments sent), sent)) := by
  unfold stepRound
  rw [if_neg (by simp only [callInput_real, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, not_false_eq_true])]
  have hmsg : (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (seedGenInitialSteps coalition parts commitments (E := E) i).outbox c else none) =
      (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then commitOutbox i (commitments i) c else none) := by
    funext c i
    split_ifs with hc
    · simp only [seedGenInitialSteps, if_neg hc.2, seedGenStart, Step.outbox]
    · rfl
  rw [hmsg]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only [localRoles]
  trans (OverPermutation.sequenceFin (fun j =>
    (pure (seedGenRevealSteps coalition parts (seedGenCommitInbox coalition parts commitments sent) j) :
      OracleComp (LocalSpec C) _)) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext j
    by_cases hj : j ∈ coalition.1
    · simp [seedGenInitialSteps, seedGenRevealSteps, hj]
    · simp only [seedGenInitialSteps, if_neg hj, seedGenStart]
      rw [advance_seedGenCommitResume]
      simp only [seedGenRevealSteps, hj, false_or, seedGenCommitInbox, roundInbox]
      rfl
  · rw [sequenceFin_pure, pure_bind]

/-- The inbox before the honest opening checks. -/
def seedGenRevealInbox (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) (sent : C.Party → Mail C E) : C.Party → Mail C E :=
  roundInbox coalition sent (seedGenRevealSteps coalition parts committed)

/-- If one honest operator passed the abort-frame check at reveal, all honest operators sent
reveals in that round. This includes senders that fail their own opening checks afterwards. -/
theorem seedGenRevealInbox_all_honest (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) (i : C.Party)
    (ha : (C.parties.any fun j => Msg.isAbort (seedGenRevealInbox coalition parts committed sent i j)) = false) :
    ∀ k j, j ∉ coalition.1 → j ≠ k →
      Msg.hashesOf (seedGenRevealInbox coalition parts committed sent k j) = revealTo .seedGen (parts j) j k := by
  intro k j hj hjk
  have hno := List.any_eq_false.mp ha j (List.mem_finRange j)
  by_cases hb : (C.parties.any fun l => Msg.isAbort (committed j l)) = true
  · have hstep : seedGenRevealSteps coalition parts committed j = .done none := by
      simp only [seedGenRevealSteps, hb, or_true, if_true]
    have hr := roundInbox_abort coalition sent (seedGenRevealSteps coalition parts committed) i j hj hstep
    change ¬ Msg.isAbort (roundInbox coalition sent (seedGenRevealSteps coalition parts committed) i j) = true at hno
    rw [hr] at hno
    exact (hno rfl).elim
  · simp only [seedGenRevealInbox, roundInbox, seedGenRevealSteps,
      hj, hb, Bool.false_eq_true, false_or, if_false, Step.delivered, revealOutbox, if_neg (Ne.symm hjk), Msg.hashesOf]

abbrev SeedGenEchoData (C : Committee) :=
  (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) × List HashOutput

/-- Everything the honest reveal continuation computes, before waiting for the echo round. -/
def seedGenRevealCompute (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    OracleComp (LocalSpec C) (Option (SeedGenEchoData C)) := do
  if C.parties.any (fun j => Msg.isAbort (revealed j)) then return none
  let opens ← liftComp (openQueries .seedGen i revealed) (LocalSpec C)
  if ¬ openCheck .seedGen i own committed revealed opens then return none
  let keys ← liftComp (deriveKeys .seedGen i (setupView .seedGen i own revealed)) (LocalSpec C)
  let shared ← liftComp (sharedQueries .seedGen i keys) (LocalSpec C)
  pure (some (keys, shared))

/-- An echo step carrying the actual values and the actual shared-key hash answers. -/
def seedGenEchoDataStep (i : C.Party) : Option (SeedGenEchoData C) → Step C E RealSpec (Keys C)
  | none => .done none
  | some (keys, shared) => .wait (echoOutbox .seedGen i keys shared) (exchangeResume fun received =>
      require (echoCheck .seedGen i keys shared received) >>= fun _ => pure (keysOf keys))

/-- Exact expansion of the honest reveal continuation, with both abort tests. -/
theorem advance_seedGenRevealResume (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    advance (exchangeResume (G := RealSpec) (fun revealed =>
      setupRest .seedGen i own committed revealed >>= fun keys => pure (keysOf keys)) revealed) =
      seedGenEchoDataStep i <$> seedGenRevealCompute i own committed revealed := by
  unfold exchangeResume seedGenRevealCompute
  split_ifs with ha
  · rfl
  · rw [advance_setupRest]
    simp only [map_bind]
    refine bind_congr fun opens => ?_
    split_ifs with ho
    · simp only [map_bind, map_pure, seedGenEchoDataStep, pure_bind]
    · rfl

/-- All honest computations between the reveal and echo boundaries. -/
def seedGenRevealComputations (coalition : C.Coalition) (parts : C.Party → Parts C)
    (committed sent : C.Party → Mail C E) : OracleComp (LocalSpec C) (C.Party → Option (SeedGenEchoData C)) :=
  OverPermutation.sequenceFin fun i =>
    if i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j)) then pure none else
      seedGenRevealCompute i (parts i) (committed i) (seedGenRevealInbox coalition parts committed sent i)

/-- Exact reduction of the second round, retaining all honest echo data. -/
theorem stepRound_seedGenRevealSteps (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) :
    stepRound localRoles coalition A noFunctionality state (seedGenRevealSteps coalition parts committed) =
    (do
      let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        (seedGenRevealSteps coalition parts committed i).outbox c else none
      let data ← seedGenRevealComputations coalition parts committed sent
      pure (st, (fun i => seedGenEchoDataStep i (data i)), sent)) := by
  unfold stepRound
  rw [if_neg (by simp only [callInput_real, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, not_false_eq_true])]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only [localRoles]
  trans (OverPermutation.sequenceFin (fun i =>
    (if i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j)) then pure none else
      seedGenRevealCompute i (parts i) (committed i) (seedGenRevealInbox coalition parts committed sent i)) >>=
      fun v => pure (seedGenEchoDataStep i v)) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext i
    by_cases hi : i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j))
    · simp only [seedGenRevealSteps, if_pos hi, pure_bind, seedGenEchoDataStep]
    · have hc : i ∉ coalition.1 := fun hh => hi (Or.inl hh)
      rw [show seedGenRevealSteps coalition parts committed i = _ from if_neg hi]
      simp only [if_neg hi, if_neg hc]
      change advance (exchangeResume _ (seedGenRevealInbox coalition parts committed sent i)) = _
      rw [advance_seedGenRevealResume, map_eq_bind_pure_comp]
      rfl
  · rw [sequenceFin_bind_pure]
    simp only [bind_assoc, pure_bind, seedGenRevealComputations]

/-- The echo continuation has no free hash queries, even when some operators aborted. -/
theorem stepRound_seedGenEchoDataSteps (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (data : C.Party → Option (SeedGenEchoData C)) :
    stepRound localRoles coalition A noFunctionality state (fun i => seedGenEchoDataStep i (data i)) =
    (do
      let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        (seedGenEchoDataStep i (data i)).outbox c else none
      pure (st, (fun i => Step.done (match data i with
        | none => none
        | some (keys, shared) => if i ∈ coalition.1 then none else
          let inbox := roundInbox coalition sent (fun j => seedGenEchoDataStep j (data j)) i
          if C.parties.any (fun j => Msg.isAbort (inbox j)) then none else
            if echoCheck .seedGen i keys shared inbox then some (keysOf keys) else none)), sent)) := by
  unfold stepRound
  rw [if_neg (by simp only [callInput_real, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, not_false_eq_true])]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only [localRoles]
  trans (OverPermutation.sequenceFin (fun i => (pure (Step.done (match data i with
        | none => none
        | some (keys, shared) => if i ∈ coalition.1 then none else
          let inbox := roundInbox coalition sent (fun j => seedGenEchoDataStep j (data j)) i
          if C.parties.any (fun j => Msg.isAbort (inbox j)) then none else
            if echoCheck .seedGen i keys shared inbox then some (keysOf keys) else none)) :
      OracleComp (LocalSpec C) _)) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext i
    cases hd : data i with
    | none => rfl
    | some v =>
      rcases v with ⟨keys, shared⟩
      by_cases hi : i ∈ coalition.1
      · simp only [seedGenEchoDataStep, if_pos hi]
      · simp only [seedGenEchoDataStep, if_neg hi]
        exact advance_seedGenEchoResume i keys shared _
  · rw [sequenceFin_pure, pure_bind]

def seedGenEchoDataOutput (coalition : C.Coalition) (data : C.Party → Option (SeedGenEchoData C))
    (sent : C.Party → Mail C E) (i : C.Party) : Option (Keys C) :=
  match data i with
  | none => none
  | some (keys, shared) => if i ∈ coalition.1 then none else
      let inbox := roundInbox coalition sent (fun j => seedGenEchoDataStep j (data j)) i
      if C.parties.any (fun j => Msg.isAbort (inbox j)) then none else
        if echoCheck .seedGen i keys shared inbox then some (keysOf keys) else none

/-- The complete last round after its honest work has already been computed. -/
def seedGenFinishLocal (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (data : C.Party → Option (SeedGenEchoData C)) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (Keys C))) :=
  if ∀ i, i ∉ coalition.1 → data i = none then pure (state, fun _ => none) else do
    let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (seedGenEchoDataStep i (data i)).outbox c else none
    pure (st, seedGenEchoDataOutput coalition data sent)

theorem executeRounds_seedGenEchoDataSteps_one (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (data : C.Party → Option (SeedGenEchoData C)) :
    executeRounds localRoles coalition A noFunctionality 1 state (fun i => seedGenEchoDataStep i (data i)) =
      seedGenFinishLocal coalition A state data := by
  have hd : (∀ i, i ∉ coalition.1 → (seedGenEchoDataStep (E := E) i (data i)).isDone) ↔
      ∀ i, i ∉ coalition.1 → data i = none := by
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    cases data i <;> simp [seedGenEchoDataStep, Step.isDone]
  rw [executeRounds]
  simp only [hd, seedGenFinishLocal]
  split_ifs with ha
  · congr 1
    apply congrArg (fun f => (state, f))
    funext i
    cases data i <;> rfl
  · rw [stepRound_seedGenEchoDataSteps]
    simp only [bind_assoc, pure_bind, executeRounds, Step.output]
    rfl

/-- The remaining two rounds, with every early-exit and abort test explicit. -/
def seedGenPostCommitLocal (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (state : A.State) (parts : C.Party → Parts C) (committed : C.Party → Mail C E) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (Keys C))) :=
  if ∀ i, i ∉ coalition.1 → (C.parties.any fun j => Msg.isAbort (committed i j)) = true then
    pure (state, fun _ => none)
  else do
    let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (seedGenRevealSteps coalition parts committed i).outbox c else none
    let data ← seedGenRevealComputations coalition parts committed sent
    seedGenFinishLocal coalition A st data

theorem executeRounds_seedGenRevealSteps_two (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (committed : C.Party → Mail C E) :
    executeRounds localRoles coalition A noFunctionality 2 state (seedGenRevealSteps coalition parts committed) =
      seedGenPostCommitLocal coalition A state parts committed := by
  have hd : (∀ i, i ∉ coalition.1 → (seedGenRevealSteps coalition parts committed i).isDone) ↔
      ∀ i, i ∉ coalition.1 → (C.parties.any fun j => Msg.isAbort (committed i j)) = true := by
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    simp only [seedGenRevealSteps, hi, false_or]
    split_ifs <;> simp_all [Step.isDone]
  rw [executeRounds]
  simp only [hd, seedGenPostCommitLocal]
  split_ifs with ha
  · congr 1
    apply congrArg (fun f => (state, f))
    funext i
    unfold seedGenRevealSteps
    split_ifs <;> rfl
  · rw [stepRound_seedGenRevealSteps]
    simp only [bind_assoc, pure_bind, executeRounds_seedGenEchoDataSteps_one]

/-- A fully split local game: start, commit, reveal, echo and final distinguish. -/
def seedGenNormalizedLocalGame (coalition : C.Coalition) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) : OracleComp (LocalSpec C) Bool := do
  let state ← A.start (corruptInputs coalition x) z
  let parts ← OverPermutation.sequenceFin fun (_ : C.Party) => liftComp (sampleParts (C := C)) (LocalSpec C)
  let commitments ← seedGenInitialCommitments coalition parts
  let (st, sent) ← A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
    commitOutbox i (commitments i) c else none
  let r ← seedGenPostCommitLocal coalition A st parts (seedGenCommitInbox coalition parts commitments sent)
  Z r

/-- The complete real game has the explicit three-round normal form, including arbitrary aborts. -/
theorem sameRun_seedGenLocal_normalized (prims : Primitives) (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    SameRun prims (seedGenLocalGame coalition A x z Z) (seedGenNormalizedLocalGame coalition A x z Z) := by
  refine (sameRun_seedGenLocal_split prims coalition A x z Z).trans (SameRun.of_eq ?_)
  simp only [seedGenLocalCommitPrefix, seedGenLocalPostCommit, seedGenNormalizedLocalGame,
    stepRound_seedGenInitialSteps, bind_assoc, pure_bind]
  change _ = _
  simp only [setupRounds, Nat.reduceSub, executeRounds_seedGenRevealSteps_two]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- All random-oracle inputs of one local query; a PRG call includes its internal hash. -/
def seedGenLocalHashInputs : (LocalSpec C).Domain → List (Query C)
  | .inl _ => []
  | .inr (.inl q) => [q]
  | .inr (.inr x) => [.streamKey x.2.1]

/-- Instrument a local computation without changing any of its oracle answers. -/
def seedGenHashLog {α : Type} (oa : OracleComp (LocalSpec C) α) :
    OracleComp (LocalSpec C) (α × List (Query C)) :=
  (simulateQ ((QueryImpl.id' (LocalSpec C)).withTraceAppend (fun t _ => seedGenLocalHashInputs t)) oa).run

@[simp] theorem seedGenHashLog_pure {α : Type} (a : α) :
    seedGenHashLog (C := C) (pure a) = pure (a, []) := rfl

theorem seedGenHashLog_fst {α : Type} (oa : OracleComp (LocalSpec C) α) :
    Prod.fst <$> seedGenHashLog oa = oa := by
  unfold seedGenHashLog
  rw [QueryImpl.fst_map_run_withTraceAppend]
  simp

theorem seedGenHashLog_bind {α β : Type} (oa : OracleComp (LocalSpec C) α)
    (k : α → OracleComp (LocalSpec C) β) :
    seedGenHashLog (oa >>= k) = (do
      let (a, l) ← seedGenHashLog oa
      let (b, r) ← seedGenHashLog (k a)
      pure (b, l ++ r)) := by
  simp [seedGenHashLog, simulateQ_bind, WriterT.run_bind]

theorem seedGenHashLog_hash (q : Query C) :
    seedGenHashLog (liftComp (hashQuery q) (LocalSpec C)) =
      (fun y => (y, [q])) <$> liftComp (hashQuery q) (LocalSpec C) := by
  change (simulateQ ((QueryImpl.id' (LocalSpec C)).withTraceAppend
    (fun t _ => seedGenLocalHashInputs t))
    (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q))))).run = _
  simp only [simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
  rfl

/-- Syntactic support of an instrumented computation, including arbitrary oracle answers. -/
def SeedGenUsesOnly {α : Type} (Q : Query C → Prop) (oa : OracleComp (LocalSpec C) α) : Prop :=
  ∀ r ∈ support (seedGenHashLog oa), ∀ q ∈ r.2, Q q

theorem SeedGenUsesOnly.pure {α : Type} (Q : Query C → Prop) (a : α) :
    SeedGenUsesOnly Q (pure a) := by
  simp [SeedGenUsesOnly]

theorem SeedGenUsesOnly.mono {α : Type} {P Q : Query C → Prop} {oa : OracleComp (LocalSpec C) α}
    (h : SeedGenUsesOnly P oa) (hp : ∀ q, P q → Q q) : SeedGenUsesOnly Q oa :=
  fun r hr q hq => hp q (h r hr q hq)

theorem SeedGenUsesOnly.bind {α β : Type} {Q : Query C → Prop} {oa : OracleComp (LocalSpec C) α}
    {k : α → OracleComp (LocalSpec C) β} (h : SeedGenUsesOnly Q oa)
    (hk : ∀ a, SeedGenUsesOnly Q (k a)) : SeedGenUsesOnly Q (oa >>= k) := by
  intro r hr q hq
  rw [seedGenHashLog_bind] at hr
  simp only [support_bind, Set.mem_iUnion, Prod.exists, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨a, l, hal, b, t, hbt, rfl⟩ := hr
  rcases List.mem_append.mp hq with hq | hq
  · exact h (a, l) hal q hq
  · exact hk a (b, t) hbt q hq

theorem SeedGenUsesOnly.map {α β : Type} {Q : Query C → Prop} {oa : OracleComp (LocalSpec C) α}
    (h : SeedGenUsesOnly Q oa) (f : α → β) : SeedGenUsesOnly Q (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact h.bind fun a => SeedGenUsesOnly.pure Q (f a)

theorem SeedGenUsesOnly.hash {Q : Query C → Prop} (q : Query C) (hq : Q q) :
    SeedGenUsesOnly Q (liftComp (hashQuery q) (LocalSpec C)) := by
  intro r hr q' hq'
  rw [seedGenHashLog_hash] at hr
  rw [support_map, Set.mem_image] at hr
  rcases hr with ⟨y, _, rfl⟩
  simpa using List.mem_singleton.mp hq' ▸ hq

theorem seedGen_liftComp_mapM {α β : Type} (f : α → OracleComp (RoSpec C) β) (l : List α) :
    liftComp (l.mapM f) (LocalSpec C) = l.mapM (fun a => liftComp (f a) (LocalSpec C)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.mapM_cons, liftComp_bind, liftComp_pure, ih]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- The points query test includes the internal hash of a counted PRG call. -/
def SeedGenTouches (points : Query C → Prop) (t : (LocalSpec C).Domain) : Prop :=
  ∃ q ∈ seedGenLocalHashInputs t, points q

/-- Stop a local computation immediately before its first points query. -/
def seedGenAvoid (points : Query C → Prop) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    OracleComp (LocalSpec C) (Option α) :=
  (simulateQ (fun t => (if SeedGenTouches points t then failure else
    OptionT.lift (OracleComp.lift (OracleSpec.query t)) : OptionT (OracleComp (LocalSpec C)) _)) oa).run

@[simp] theorem seedGenAvoid_pure (points : Query C → Prop) {α : Type} (a : α) :
    seedGenAvoid points (pure a) = pure (some a) := rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

def SeedGenGoodLog (points : Query C → Prop) (l : List (Query C)) : Prop := ∀ q ∈ l, ¬ points q

@[simp] theorem seedGenGoodLog_append (points : Query C → Prop) (l r : List (Query C)) :
    SeedGenGoodLog points (l ++ r) ↔ SeedGenGoodLog points l ∧ SeedGenGoodLog points r := by
  simp [SeedGenGoodLog, List.mem_append, or_imp, forall_and]

@[simp] theorem seedGenGoodLog_local (points : Query C → Prop) (t : (LocalSpec C).Domain) :
    SeedGenGoodLog points (seedGenLocalHashInputs t) ↔ ¬ SeedGenTouches points t := by
  simp [SeedGenGoodLog, SeedGenTouches]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- Only raw derivation inputs of hidden names are excluded. Echo inputs remain unrestricted. -/
def SeedGenHiddenInput (coalition : C.Coalition) (parts : C.Party → Parts C) (q : Query C) : Prop :=
  ∃ name, Hidden coalition name ∧ seedGenNamedInput parts name = q

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The deterministic reveal result under a fixed oracle, with both actual abort tests. -/
def seedGenRevealDataFixed (prims : Primitives) (h : Query C → HashOutput) (i : C.Party)
    (own : Parts C) (committed revealed : Mail C E) : Option (SeedGenEchoData C) :=
  if C.parties.any (fun j => Msg.isAbort (revealed j)) then none else
    if openCheck .seedGen i own committed revealed (D prims h (openQueries .seedGen i revealed)) then
      let keys := D prims h (deriveKeys .seedGen i (setupView .seedGen i own revealed))
      some (keys, D prims h (sharedQueries .seedGen i keys))
    else none

theorem simulateQ_fixedLocal_seedGenRevealCompute (prims : Primitives) (h : Query C → HashOutput)
    (i : C.Party) (own : Parts C) (committed revealed : Mail C E) :
    simulateQ (fixedLocal prims h) (seedGenRevealCompute i own committed revealed) =
      pure (seedGenRevealDataFixed prims h i own committed revealed) := by
  unfold seedGenRevealCompute seedGenRevealDataFixed
  by_cases ha : (C.parties.any fun j => Msg.isAbort (revealed j)) = true
  · simp only [if_pos ha, simulateQ_pure]
  · simp only [if_neg ha, pure_bind, simulateQ_bind, simulateQ_fixedLocal_liftComp, pure_bind]
    by_cases ho : openCheck .seedGen i own committed revealed (D prims h (openQueries .seedGen i revealed))
    · simp only [ho, not_true_eq_false, if_false, if_true, pure_bind, simulateQ_bind,
        simulateQ_fixedLocal_liftComp, simulateQ_pure]
    · simp only [ho, not_false_eq_true, if_true, if_false, simulateQ_pure]

def seedGenRevealAllFixed (prims : Primitives) (coalition : C.Coalition) (h : Query C → HashOutput)
    (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) :
    C.Party → Option (SeedGenEchoData C) := fun i =>
  if i ∈ coalition.1 ∨ C.parties.any (fun j => Msg.isAbort (committed i j)) then none else
    seedGenRevealDataFixed prims h i (parts i) (committed i) (seedGenRevealInbox coalition parts committed sent i)

theorem simulateQ_fixedLocal_seedGenRevealComputations (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E) :
    simulateQ (fixedLocal prims h) (seedGenRevealComputations coalition parts committed sent) =
      pure (seedGenRevealAllFixed prims coalition h parts committed sent) := by
  rw [seedGenRevealComputations, simulateQ_sequenceFin]
  trans OverPermutation.sequenceFin (fun i => (pure (seedGenRevealAllFixed prims coalition h parts committed sent i) : ProbComp _))
  · congr 1
    funext i
    unfold seedGenRevealAllFixed
    split_ifs
    · rfl
    · exact simulateQ_fixedLocal_seedGenRevealCompute prims h i (parts i) (committed i) _
  · exact sequenceFin_pure _

/-- A successful echo output supplies the actual inbox checks and its honest key value. -/
theorem seedGenEchoDataOutput_some (coalition : C.Coalition) (data : C.Party → Option (SeedGenEchoData C))
    (sent : C.Party → Mail C E) (i : C.Party) (key : Keys C)
    (ho : seedGenEchoDataOutput coalition data sent i = some key) :
    i ∉ coalition.1 ∧ ∃ keys shared,
      data i = some (keys, shared) ∧ key = keysOf keys ∧
      (C.parties.any fun j => Msg.isAbort (roundInbox coalition sent (fun j => seedGenEchoDataStep j (data j)) i j)) = false ∧
      echoCheck .seedGen i keys shared (roundInbox coalition sent (fun j => seedGenEchoDataStep j (data j)) i) := by
  unfold seedGenEchoDataOutput at ho
  cases hd : data i with
  | none => simp only [hd] at ho; contradiction
  | some v =>
    rcases v with ⟨keys, shared⟩
    simp only [hd] at ho
    split_ifs at ho with hi hb hc <;> try contradiction
    refine ⟨hi, keys, shared, rfl, (Option.some.inj ho).symm, ?_, hc⟩
    exact Bool.eq_false_iff.mpr hb

/-- Every honest operator reached its echo step if any honest output survives. -/
theorem seedGenEchoDataOutput_all_some (coalition : C.Coalition)
    (data : C.Party → Option (SeedGenEchoData C)) (sent : C.Party → Mail C E)
    (i : C.Party) (key : Keys C) (ho : seedGenEchoDataOutput coalition data sent i = some key) :
    ∀ j, j ∉ coalition.1 → (data j).isSome := by
  obtain ⟨_, keys, shared, _, _, ha, _⟩ := seedGenEchoDataOutput_some coalition data sent i key ho
  intro j hj
  cases hd : data j with
  | some v => rfl
  | none =>
    have hn := List.any_eq_false.mp ha j (List.mem_finRange j)
    simp only [roundInbox, if_neg hj, hd, seedGenEchoDataStep, Step.delivered, Msg.isAbort] at hn
    exact (hn trivial).elim

/-- A non-aborting deterministic reveal supplies its actual derived keys and shared hashes. -/
theorem seedGenRevealAllFixed_some (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (committed sent : C.Party → Mail C E)
    (i : C.Party) (ha : (seedGenRevealAllFixed prims coalition h parts committed sent i).isSome) :
    let revealed := seedGenRevealInbox coalition parts committed sent
    let keys := D prims h (deriveKeys .seedGen i (setupView .seedGen i (parts i) (revealed i)))
    seedGenRevealAllFixed prims coalition h parts committed sent i =
      some (keys, D prims h (sharedQueries .seedGen i keys)) ∧
    (C.parties.any fun j => Msg.isAbort (revealed i j)) = false := by
  unfold seedGenRevealAllFixed seedGenRevealDataFixed at ha ⊢
  dsimp only
  split_ifs with hi hr hc <;> simp_all

/-- Outside the stated shared-hash collision event, acceptance gives the honest agreements
required by output identification. -/
theorem seedGenRevealAllFixed_output_agreement (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (committed sent echoSent : C.Party → Mail C E)
    (i : C.Party) (key : Keys C)
    (ho : seedGenEchoDataOutput coalition (seedGenRevealAllFixed prims coalition h parts committed sent) echoSent i = some key)
    (hn : ∀ j, j ∉ coalition.1 →
      let revealed := seedGenRevealInbox coalition parts committed sent
      let ki := D prims h (deriveKeys .seedGen i (setupView .seedGen i (parts i) (revealed i)))
      let kj := D prims h (deriveKeys .seedGen j (setupView .seedGen j (parts j) (revealed j)))
      h (.sharedKeys .seedGen ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys .seedGen ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) .seedGen ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys .seedGen ((sharedTerms j i).map kj.2.1)) :
    let revealed := seedGenRevealInbox coalition parts committed sent
    let keys := fun j => D prims h (deriveKeys .seedGen j (setupView .seedGen j (parts j) (revealed j)))
    i ∉ coalition.1 ∧ key = keysOf (keys i) ∧
    (∀ k j, j ∉ coalition.1 → j ≠ k → Msg.hashesOf (revealed k j) = revealTo .seedGen (parts j) j k) ∧
    ∀ j, j ∉ coalition.1 → (keys i).1 = (keys j).1 ∧
      ∀ T, i ∈ C.holders T → j ∈ C.holders T → (keys i).2.1 T = (keys j).2.1 T := by
  let data := seedGenRevealAllFixed prims coalition h parts committed sent
  let revealed := seedGenRevealInbox coalition parts committed sent
  let keys := fun j => D prims h (deriveKeys .seedGen j (setupView .seedGen j (parts j) (revealed j)))
  have hall := seedGenEchoDataOutput_all_some coalition data echoSent i key ho
  obtain ⟨hi, ki, si, hdi, hkey, _, hcheck⟩ := seedGenEchoDataOutput_some coalition data echoSent i key ho
  have hdf (j : C.Party) (hj : j ∉ coalition.1) :
      data j = some (keys j, D prims h (sharedQueries .seedGen j (keys j))) :=
    (seedGenRevealAllFixed_some prims coalition h parts committed sent j (hall j hj)).1
  have he := Option.some.inj (hdi.symm.trans (hdf i hi))
  obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp he
  refine ⟨hi, hkey, seedGenRevealInbox_all_honest coalition parts committed sent i
    (seedGenRevealAllFixed_some prims coalition h parts committed sent i (hall i hi)).2, ?_⟩
  intro j hj
  by_cases hji : j = i
  · subst j
    exact ⟨rfl, fun _ _ _ => rfl⟩
  · apply seedGen_echoCheck_agreement prims h i j hji (keys i) (keys j) _ _ hcheck (hn j hj)
    simp only [roundInbox, if_neg hj, hdf j hj, seedGenEchoDataStep, Step.delivered,
      echoOutbox, if_neg (Ne.symm hji)]

/-- Complete output identification for the concrete reveal and echo execution. The protocol's
successful output supplies honest delivery, derivation and agreement facts automatically. -/
theorem seedGenRevealEcho_output_eq_hybrid (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (committed sent echoSent commitSent : C.Party → Mail C E) (log : CallLog C)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (high : HashOutput)
    (hextract : ∀ i j, i ∉ coalition.1 → j ∈ coalition.1 →
      extractReveal log commitSent j i = Msg.hashesOf (seedGenRevealInbox coalition parts committed sent i j))
    (hparameter : h (seedGenParameterProgrammingInput coalition (seedGenProgramView coalition parts log commitSent)) =
      seedGenFullParameter high parameter)
    (hterm : ∀ T, KnownTo coalition.1 T →
      h (seedGenTermProgrammingInput coalition (seedGenProgramView coalition parts log commitSent) T) = seeds T)
    (hpair : ∀ p ∈ seedGenCrossCoordinates coalition,
      h (seedGenPairProgrammingInput coalition (seedGenProgramView coalition parts log commitSent) p) = pairs p)
    (i : C.Party) (key : Keys C)
    (ho : seedGenEchoDataOutput coalition (seedGenRevealAllFixed prims coalition h parts committed sent) echoSent i = some key)
    (hn : ∀ j, j ∉ coalition.1 →
      let revealed := seedGenRevealInbox coalition parts committed sent
      let ki := D prims h (deriveKeys .seedGen i (setupView .seedGen i (parts i) (revealed i)))
      let kj := D prims h (deriveKeys .seedGen j (setupView .seedGen j (parts j) (revealed j)))
      h (.sharedKeys .seedGen ((sharedTerms i j).map ki.2.1)) =
        h (.sharedKeys .seedGen ((sharedTerms j i).map kj.2.1)) →
      Query.sharedKeys (C := C) .seedGen ((sharedTerms i j).map ki.2.1) =
        Query.sharedKeys .seedGen ((sharedTerms j i).map kj.2.1)) :
    key = dealtKeys parameter (seedGenHybridSeeds coalition h parts seeds)
      (seedGenHybridPairs coalition h parts pairs) i := by
  obtain ⟨hi, hkey, hreceived, hagree⟩ :=
    seedGenRevealAllFixed_output_agreement prims coalition h parts committed sent echoSent i key ho hn
  rw [hkey]
  exact seedGen_output_eq_hybrid_dealing prims coalition parts log commitSent _ h parameter seeds pairs high
    (fun j => D prims h (deriveKeys .seedGen j
      (setupView .seedGen j (parts j) (seedGenRevealInbox coalition parts committed sent j))))
    hreceived hextract (fun _ _ => rfl) hparameter hterm hpair i hi hagree

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- A transcript whose queries are unchanged by any shift of a hidden private coordinate. -/
def SeedGenPrivateInvariant {α : Type} (coalition : C.Coalition) (f : (C.Party → Parts C) → α) : Prop :=
  (∀ a T, ¬ KnownTo coalition.1 T → ∀ c parts,
    f (shiftAt a (some T) none c parts) = f parts) ∧
  (∀ p : C.Pair, p.1.1 ∉ coalition.1 → p.1.2 ∉ coalition.1 → ∀ c parts,
    f (shiftAt p.1.1 none (some p.1.2) c parts) = f parts)

def seedGenDeriveHead : Query C → HashOutput
  | .derive _ _ values => values.headD 0
  | _ => 0

/-- Sample the private parts and then an arbitrary randomized transcript. -/
def seedGenPartsKernel {α : Type} (K : (C.Party → Parts C) → ProbComp α) :
    ProbComp ((C.Party → Parts C) × α) := do
  let parts ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)
  let out ← K parts
  pure (parts, out)

/-- Private-coordinate shifts preserve the complete joint law of the parts and invariant transcript. -/
theorem evalDist_seedGenPartsKernel_shift {α : Type} (K : (C.Party → Parts C) → ProbComp α)
    (a : C.Party) (term : Option C.Term) (pair : Option C.Party) (c : HashOutput)
    (hK : ∀ parts, K (shiftAt a term pair c parts) = K parts) :
    ((fun p => (shiftAt a term pair c p.1, p.2)) <$> seedGenPartsKernel K) =ᵈ seedGenPartsKernel K := by
  have he : (fun p => (shiftAt a term pair c p.1, p.2)) <$> seedGenPartsKernel K =
      (do let parts ← shiftAt a term pair c <$> OverPermutation.sequenceFin (fun _ : C.Party => sampleParts (C := C))
          let out ← K parts
          pure (parts, out)) := by
    simp only [seedGenPartsKernel, map_bind, map_pure, bind_map_left, hK]
  rw [he]
  exact (evalDist_shiftAt a term pair c).bind_left _

/-- A transcript that is invariant under one hidden coordinate has exactly the uniform guessing
probability at that coordinate. This includes arbitrarily adaptive randomized computations. -/
theorem probEvent_seedGenPartsKernel_coordinate {α : Type}
    (K : (C.Party → Parts C) → ProbComp α) (X : (C.Party → Parts C) → HashOutput)
    (Y : α → HashOutput) (a : C.Party) (term : Option C.Term) (pair : Option C.Party)
    (hX : ∀ c parts, X (shiftAt a term pair c parts) = X parts ^^^ c)
    (hK : ∀ c parts, K (shiftAt a term pair c parts) = K parts) :
    Pr{let p ← seedGenPartsKernel K}[X p.1 = Y p.2] = (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have huniform : ((fun p => X p.1 ^^^ Y p.2) <$> seedGenPartsKernel K) =ᵈ $ᵗ HashOutput := by
    apply evalDist_eq_uniform_of_probOutput_eq
    intro u v
    have hshift : ((fun p => X p.1 ^^^ Y p.2) <$> seedGenPartsKernel K) =ᵈ
        ((fun d => d ^^^ (u ^^^ v)) <$> ((fun p => X p.1 ^^^ Y p.2) <$> seedGenPartsKernel K)) := by
      calc ((fun p => X p.1 ^^^ Y p.2) <$> seedGenPartsKernel K : ProbComp HashOutput)
        _ =ᵈ ((fun p => X p.1 ^^^ Y p.2) <$>
          ((fun p => (shiftAt a term pair (u ^^^ v) p.1, p.2)) <$> seedGenPartsKernel K) : ProbComp HashOutput) :=
            ((evalDist_seedGenPartsKernel_shift K a term pair (u ^^^ v) (hK _)).map _).symm
        _ = _ := by
          rw [Functor.map_map, Functor.map_map]
          congr 2
          funext p
          simp only [hX, BitVec.xor_assoc, BitVec.xor_comm (u ^^^ v) (Y p.2)]
    have hu : u = v ^^^ (u ^^^ v) := by
      rw [BitVec.xor_comm u v, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    have he := prEvent_map_injective ((fun p => X p.1 ^^^ Y p.2) <$> seedGenPartsKernel K)
      (xor_bijective (u ^^^ v)).1 v
    rw [← hu] at he
    exact (hshift.prEvent_eq _).trans he
  have he : Pr{let p ← seedGenPartsKernel K}[X p.1 = Y p.2] =
      Pr{let z ← (fun p => X p.1 ^^^ Y p.2) <$> seedGenPartsKernel K}[z = 0] := by
    rw [prEvent_map]
    exact prEvent_congr _ _ _ fun _ => BitVec.xor_eq_zero_iff.symm
  rw [he, huniform.prEvent_eq, SampleableType.prEvent_uniformSample_eq_singleton]

/-- The one-point bound for a transcript sampled adaptively, rather than a fixed proposed query. -/
theorem probEvent_seedGenHiddenInput_kernel_one {α : Type} (coalition : C.Coalition)
    (K : (C.Party → Parts C) → ProbComp α) (hinv : SeedGenPrivateInvariant coalition K)
    (target : α → Query C) :
    Pr{let p ← seedGenPartsKernel K}[SeedGenHiddenInput coalition p.1 (target p.2)] ≤
      ((Fintype.card C.Term + Fintype.card C.Pair : ℕ) : ℝ≥0∞) * (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
  have ht (T : C.Term) :
      Pr{let p ← seedGenPartsKernel K}[¬ KnownTo coalition.1 T ∧ termInput .seedGen p.1 T = target p.2] ≤
        (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    by_cases hh : ¬ KnownTo coalition.1 T
    · obtain ⟨a, rest, ha⟩ := exists_first_holder T
      calc
        _ ≤ Pr{let p ← seedGenPartsKernel K}[(p.1 a).term T = seedGenDeriveHead (target p.2)] := by
          refine prEvent_mono _ _ _ fun p hp => ?_
          rw [← hp.2]
          simp [termInput, ha, seedGenDeriveHead]
        _ = _ := probEvent_seedGenPartsKernel_coordinate K (fun parts => (parts a).term T)
          (fun r => seedGenDeriveHead (target r)) a (some T) none
          (fun c parts => by simp [shiftAt, shiftParts]) (hinv.1 a T hh)
    · simp [hh]
  have hp (pair : C.Pair) :
      Pr{let p ← seedGenPartsKernel K}[pair.1.1 ∉ coalition.1 ∧ pair.1.2 ∉ coalition.1 ∧
        pairInput .seedGen p.1 pair = target p.2] ≤ (Fintype.card HashOutput : ℝ≥0∞)⁻¹ := by
    by_cases hh : pair.1.1 ∉ coalition.1 ∧ pair.1.2 ∉ coalition.1
    · calc
        _ ≤ Pr{let p ← seedGenPartsKernel K}[(p.1 pair.1.1).pair pair.1.2 = seedGenDeriveHead (target p.2)] := by
          refine prEvent_mono _ _ _ fun p hp => ?_
          rw [← hp.2.2]
          simp [pairInput, seedGenDeriveHead]
        _ = _ := probEvent_seedGenPartsKernel_coordinate K (fun parts => (parts pair.1.1).pair pair.1.2)
          (fun r => seedGenDeriveHead (target r)) pair.1.1 none (some pair.1.2)
          (fun c parts => by simp [shiftAt, shiftParts]) (hinv.2 pair hh.1 hh.2)
    · have he : ∀ p : (C.Party → Parts C) × α, ¬ (pair.1.1 ∉ coalition.1 ∧ pair.1.2 ∉ coalition.1 ∧ pairInput .seedGen p.1 pair = target p.2) :=
        fun _ h => hh ⟨h.1, h.2.1⟩
      simp only [he, prEvent_false, zero_le]
  have hm : ∀ p : (C.Party → Parts C) × α, SeedGenHiddenInput coalition p.1 (target p.2) →
      (∃ T ∈ (Finset.univ : Finset C.Term), ¬ KnownTo coalition.1 T ∧ termInput .seedGen p.1 T = target p.2) ∨
      (∃ pair ∈ (Finset.univ : Finset C.Pair), pair.1.1 ∉ coalition.1 ∧ pair.1.2 ∉ coalition.1 ∧
        pairInput .seedGen p.1 pair = target p.2) := by
    rintro p ⟨name, hn, he⟩
    cases name with
    | parameter => exact hn.elim
    | term T => exact Or.inl ⟨T, Finset.mem_univ _, hn, he⟩
    | pair pair => exact Or.inr ⟨pair, Finset.mem_univ _, hn.1, hn.2, he⟩
  refine (prEvent_mono _ _ _ (fun p => hm p)).trans ((prEvent_or_le _ _ _).trans ?_)
  calc
    _ ≤ (∑ _T : C.Term, (Fintype.card HashOutput : ℝ≥0∞)⁻¹) +
        (∑ _p : C.Pair, (Fintype.card HashOutput : ℝ≥0∞)⁻¹) :=
      add_le_add ((prEvent_exists_finset_le _ _ _).trans (Finset.sum_le_sum fun T _ => ht T))
        ((prEvent_exists_finset_le _ _ _).trans (Finset.sum_le_sum fun p _ => hp p))
    _ = _ := by simp [add_mul]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable

abbrev SeedGenFiniteSpec (Ω : Type) := unifSpec + ((Ω →ₒ HashOutput) + ((Ω × HashOutput) →ₒ Bool))
abbrev SeedGenFiniteCache (Ω : Type) := (Ω →ₒ HashOutput).QueryCache

def seedGenFiniteProgram {Ω : Type} [DecidableEq Ω] (x : Ω × HashOutput) :
    StateT (SeedGenFiniteCache Ω) ProbComp Bool := fun cache =>
  if (cache x.1).isSome then pure (false, cache)
  else pure (true, cache.cacheQuery x.1 x.2)

def seedGenFiniteEager {Ω : Type} [DecidableEq Ω] (h : Ω → HashOutput) :
    QueryImpl (SeedGenFiniteSpec Ω) (StateT (SeedGenFiniteCache Ω) ProbComp) :=
  unifFwdImpl (Ω →ₒ HashOutput) + ((QueryImpl.withCaching (fun q => pure (h q) : QueryImpl (Ω →ₒ HashOutput) ProbComp)) + seedGenFiniteProgram (Ω := Ω))

def seedGenFiniteLazy {Ω : Type} [DecidableEq Ω] :
    QueryImpl (SeedGenFiniteSpec Ω) (StateT (SeedGenFiniteCache Ω) ProbComp) :=
  unifFwdImpl (Ω →ₒ HashOutput) + ((Ω →ₒ HashOutput).randomOracle + seedGenFiniteProgram (Ω := Ω))

/-- Once a cell is cached, its unused eager-table value cannot affect any future computation,
including an adaptive programming attempt. -/
theorem seedGenFiniteEager_congr {Ω α : Type} [DecidableEq Ω]
    (oa : OracleComp (SeedGenFiniteSpec Ω) α) (h g : Ω → HashOutput) :
    ∀ cache : SeedGenFiniteCache Ω, (∀ q, cache q = none → h q = g q) →
      (simulateQ (seedGenFiniteEager h) oa).run cache =
        (simulateQ (seedGenFiniteEager g) oa).run cache := by
  induction oa using OracleComp.inductionOn with
  | pure a => intros; rfl
  | query_bind t k ih =>
    intro cache he
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with n | q | x
    · change (((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        fun p : unifSpec.Range n × SeedGenFiniteCache Ω => (simulateQ (seedGenFiniteEager h) (k p.1)).run p.2) =
        (((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        fun p : unifSpec.Range n × SeedGenFiniteCache Ω => (simulateQ (seedGenFiniteEager g) (k p.1)).run p.2)
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
    · change seedGenFiniteProgram x cache >>= _ = seedGenFiniteProgram x cache >>= _
      unfold seedGenFiniteProgram
      split_ifs
      · simp only [pure_bind]; exact ih false cache he
      · simp only [pure_bind]
        apply ih
        intro q' hq'
        by_cases hn : q' = x.1
        · subst q'; simp at hq'
        · exact he q' (by simpa [QueryCache.cacheQuery, hn] using hq')

/-- Marginalization remains valid for a randomized continuation, not just a deterministic map. -/
theorem seedGenUniform_update_bind {Ω α : Type} [Finite Ω] [DecidableEq Ω]
    [SampleableType (Ω → HashOutput)] (q : Ω) (k : (Ω → HashOutput) → ProbComp α) :
    (do let y ← $ᵗ HashOutput; let h ← $ᵗ (Ω → HashOutput); k (Function.update h q y)) =ᵈ
      (do let h ← $ᵗ (Ω → HashOutput); k h) := by
  exact evalDistEq_uniformSample_bind_update (R := HashOutput) q k

/-- The eager and lazy programmable worlds have exactly the same joint result/cache law.
The occupancy cache is kept separately, so eager sampling does not make programming fail. -/
theorem evalDist_seedGenFiniteEager {Ω α : Type} [Finite Ω] [DecidableEq Ω]
    [SampleableType (Ω → HashOutput)] (oa : OracleComp (SeedGenFiniteSpec Ω) α) :
    ∀ cache : SeedGenFiniteCache Ω,
      (simulateQ seedGenFiniteLazy oa).run cache =ᵈ
        (do let h ← $ᵗ (Ω → HashOutput); (simulateQ (seedGenFiniteEager h) oa).run cache) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro cache
    simp only [simulateQ_pure, StateT.run_pure]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | query_bind t k ih =>
    intro cache
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with n | q | x
    · change (((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        fun p : unifSpec.Range n × SeedGenFiniteCache Ω => (simulateQ seedGenFiniteLazy (k p.1)).run p.2) =ᵈ
        (do let h ← $ᵗ (Ω → HashOutput);
              ((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
                fun p : unifSpec.Range n × SeedGenFiniteCache Ω => (simulateQ (seedGenFiniteEager h) (k p.1)).run p.2)
      simp only [bind_map_left]
      refine (EvalDistEq.bind_right _ fun y => ih y cache).trans ?_
      exact OracleComp.EvalDistEq.bind_bind_swap _ _ _
    · change (((Ω →ₒ HashOutput).randomOracle q).run cache >>= _) =ᵈ
        (do let h ← $ᵗ (Ω → HashOutput);
              (QueryImpl.withCaching (fun q => pure (h q) : QueryImpl (Ω →ₒ HashOutput) ProbComp) q).run cache >>= _)
      cases hc : cache q with
      | some y =>
        simp only [randomOracle, QueryImpl.withCaching_run_some _ hc, pure_bind]
        exact ih y cache
      | none =>
        simp only [randomOracle, QueryImpl.withCaching_run_none _ hc, bind_map_left, map_pure, pure_bind]
        change (($ᵗ HashOutput) >>= fun y => (simulateQ seedGenFiniteLazy (k y)).run (cache.cacheQuery q y)) =ᵈ _
        refine (EvalDistEq.bind_right _ fun y => ih y (cache.cacheQuery q y)).trans ?_
        let cont := fun h : Ω → HashOutput =>
          (simulateQ (seedGenFiniteEager h) (k (h q))).run (cache.cacheQuery q (h q))
        have he (y : HashOutput) (h : Ω → HashOutput) :
            (simulateQ (seedGenFiniteEager h) (k y)).run (cache.cacheQuery q y) =
              cont (Function.update h q y) := by
          dsimp only [cont]
          rw [Function.update_self]
          apply seedGenFiniteEager_congr
          intro q' hq'
          by_cases hn : q' = q
          · subst q'; simp at hq'
          · simp [Function.update_of_ne hn]
        simp_rw [he, Function.update_eq_self]
        exact seedGenUniform_update_bind q cont
    · change (seedGenFiniteProgram x cache >>= _) =ᵈ
        (do let h ← $ᵗ (Ω → HashOutput); seedGenFiniteProgram x cache >>= _)
      unfold seedGenFiniteProgram
      split_ifs
      · simp only [pure_bind]; exact ih false cache
      · simp only [pure_bind]; exact ih true (cache.cacheQuery x.1 x.2)

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- Every underlying hash input, including a PRG's hash and a programming attempt. -/
def seedGenWorldHashInputs : (WorldSpec C).Domain → Finset (Query C)
  | .inl (.inl t) => (seedGenLocalHashInputs t).toFinset
  | .inl (.inr x) => {x.1}
  | .inr t => (seedGenLocalHashInputs t).toFinset

/-- Syntactic coverage of every possible branch by a finite hash-input domain. -/
inductive SeedGenWorldCovered (S : Finset (Query C)) {α : Type} : OracleComp (WorldSpec C) α → Prop
  | pure (a : α) : SeedGenWorldCovered S (pure a)
  | query_bind (t : (WorldSpec C).Domain) (k : (WorldSpec C).Range t → OracleComp (WorldSpec C) α)
      (ht : seedGenWorldHashInputs t ⊆ S) (hk : ∀ y, SeedGenWorldCovered S (k y)) :
      SeedGenWorldCovered S (OracleComp.lift (OracleSpec.query t) >>= k)

theorem SeedGenWorldCovered.mono {S T : Finset (Query C)} {α : Type}
    {oa : OracleComp (WorldSpec C) α} (h : SeedGenWorldCovered S oa) (hst : S ⊆ T) :
    SeedGenWorldCovered T oa := by
  induction h with
  | pure a => exact .pure a
  | query_bind t k ht hk ih => exact .query_bind t k (ht.trans hst) ih

/-- Finite answer ranges give a finite envelope even for an arbitrarily adaptive world program. -/
theorem seedGenWorldCovered_exists {α : Type} (oa : OracleComp (WorldSpec C) α) :
    ∃ S : Finset (Query C), SeedGenWorldCovered S oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact ⟨∅, .pure a⟩
  | query_bind t k ih =>
    have hi : Finite ((WorldSpec C).Range t) := by
      rcases t with (n | q | x) | x | (n | q | x) <;> infer_instance
    letI := Fintype.ofFinite ((WorldSpec C).Range t)
    choose S hS using ih
    refine ⟨seedGenWorldHashInputs t ∪ Finset.univ.biUnion S, .query_bind t k ?_ ?_⟩
    · exact Finset.subset_union_left
    · intro y
      apply (hS y).mono
      intro q hq
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨y, Finset.mem_univ _, hq⟩)

def seedGenRestrictCache (S : Finset (Query C)) (cache : HashCache C) : SeedGenFiniteCache S :=
  QueryCache.ofFn fun q => cache q.1

theorem seedGenRestrictCache_update (S : Finset (Query C)) (cache : HashCache C)
    (q : Query C) (hq : q ∈ S) (y : HashOutput) :
    seedGenRestrictCache S (cache.cacheQuery q y) =
      (seedGenRestrictCache S cache).cacheQuery ⟨q, hq⟩ y := by
  refine QueryCache.ext fun q' => ?_
  by_cases he : q'.1 = q
  · have he' : q' = ⟨q, hq⟩ := Subtype.ext he
    subst q'
    simp [seedGenRestrictCache]
  · have he' : q' ≠ ⟨q, hq⟩ := fun h => he (congrArg Subtype.val h)
    simp [seedGenRestrictCache, QueryCache.cacheQuery, he, he']

/-- Translation to a finite domain keeps fixed `Th` calls deterministic. -/
def seedGenFiniteHash (prims : Primitives) (S : Finset (Query C)) (q : Query C) :
    OracleComp (SeedGenFiniteSpec S) HashOutput :=
  match q with
  | .hash input => if MpcInput input then pure (prims.Th input) else
      if hq : q ∈ S then OracleComp.lift ((SeedGenFiniteSpec S).query (.inr (.inl ⟨q, hq⟩))) else pure 0
  | _ => if hq : q ∈ S then OracleComp.lift ((SeedGenFiniteSpec S).query (.inr (.inl ⟨q, hq⟩))) else pure 0

def seedGenFiniteLocal (prims : Primitives) (S : Finset (Query C)) :
    QueryImpl (LocalSpec C) (OracleComp (SeedGenFiniteSpec S)) :=
  (fun n : ℕ => OracleComp.lift ((SeedGenFiniteSpec S).query (.inl n)) : QueryImpl unifSpec (OracleComp (SeedGenFiniteSpec S))) +
    (seedGenFiniteHash prims S + fun x : PrgInput C => do
      let y ← seedGenFiniteHash prims S (.streamKey x.2.1)
      pure (prims.aes.eval (truncateHash y) x.2.2))

def seedGenFiniteProgramming (S : Finset (Query C)) (x : Query C × HashOutput) :
    OracleComp (SeedGenFiniteSpec S) Bool :=
  if IsFixed x.1 then pure false else
    if hx : x.1 ∈ S then OracleComp.lift ((SeedGenFiniteSpec S).query (.inr (.inr (⟨x.1, hx⟩, x.2)))) else pure false

def seedGenFiniteWorld (prims : Primitives) (S : Finset (Query C)) :
    QueryImpl (WorldSpec C) (OracleComp (SeedGenFiniteSpec S)) :=
  seedGenFiniteLocal prims S + seedGenFiniteProgramming S + seedGenFiniteLocal prims S

/-- A hash call's exact joint answer/cache law survives restriction to its finite domain. -/
theorem seedGenFiniteHash_run (prims : Primitives) (S : Finset (Query C))
    (q : Query C) (hq : q ∈ S) (cache : HashCache C) :
    (fun r : HashOutput × HashCache C => (r.1, seedGenRestrictCache S r.2)) <$>
        (hashAnswer prims q).run cache =
      (simulateQ seedGenFiniteLazy (seedGenFiniteHash prims S q)).run (seedGenRestrictCache S cache) := by
  by_cases hf : IsFixed q
  · obtain ⟨input, rfl, hi⟩ := hf
    rw [hashAnswer_of_isFixed prims hi]
    simp [seedGenFiniteHash, hi, seedGenRestrictCache]
  · have ht : seedGenFiniteHash prims S q = OracleComp.lift ((SeedGenFiniteSpec S).query (.inr (.inl ⟨q, hq⟩))) := by
      cases q <;> simp_all [seedGenFiniteHash, IsFixed]
    rw [ht, hashAnswer_of_not_isFixed prims hf]
    erw [simulateQ_spec_query]
    change _ <$> ((Query C →ₒ HashOutput).randomOracle q).run cache =
      ((S →ₒ HashOutput).randomOracle ⟨q, hq⟩).run (seedGenRestrictCache S cache)
    cases hc : cache q with
    | none =>
      rw [randomOracle, QueryImpl.withCaching_run_none _ hc,
        QueryImpl.withCaching_run_none _ (show seedGenRestrictCache S cache ⟨q, hq⟩ = none from hc)]
      simp only [Functor.map_map, seedGenRestrictCache_update S cache q hq]
      rfl
    | some y =>
      rw [randomOracle, QueryImpl.withCaching_run_some _ hc,
        QueryImpl.withCaching_run_some _ (show seedGenRestrictCache S cache ⟨q, hq⟩ = some y from hc)]
      rfl

/-- The finite translation also preserves private sampling and internal PRG hashes. -/
theorem seedGenFiniteLocal_run (prims : Primitives) (S : Finset (Query C))
    (t : (LocalSpec C).Domain) (ht : ∀ q ∈ seedGenLocalHashInputs t, q ∈ S) (cache : HashCache C) :
    (fun r : (LocalSpec C).Range t × HashCache C => (r.1, seedGenRestrictCache S r.2)) <$>
        (localAnswer prims t).run cache =
      (simulateQ seedGenFiniteLazy (seedGenFiniteLocal prims S t)).run (seedGenRestrictCache S cache) := by
  rcases t with n | q | x
  · change _ <$> (fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _) = _
    simp only [Functor.map_map]
    rfl
  · exact seedGenFiniteHash_run prims S q (ht q (by simp [seedGenLocalHashInputs])) cache
  · change _ <$> (prgAnswer prims x).run cache =
      (simulateQ seedGenFiniteLazy (seedGenFiniteHash prims S (.streamKey x.2.1) >>=
        fun y => pure (prims.aes.eval (truncateHash y) x.2.2))).run _
    simp only [prgAnswer, StateT.run_bind, StateT.run_pure, map_bind, map_pure,
      simulateQ_bind, simulateQ_pure]
    rw [← seedGenFiniteHash_run prims S (.streamKey x.2.1)
      (ht _ (by simp [seedGenLocalHashInputs])) cache, bind_map_left]

/-- Fresh-only programming, including its returned success bit, is preserved. -/
theorem seedGenFiniteProgramming_run (S : Finset (Query C))
    (x : Query C × HashOutput) (hx : x.1 ∈ S) (cache : HashCache C) :
    (fun r : Bool × HashCache C => (r.1, seedGenRestrictCache S r.2)) <$>
        (programAnswer x).run cache =
      (simulateQ seedGenFiniteLazy (seedGenFiniteProgramming S x)).run (seedGenRestrictCache S cache) := by
  rw [programAnswer_run_cache]
  unfold seedGenFiniteProgramming programCache
  by_cases hf : IsFixed x.1
  · simp [hf]
  · simp only [hf, false_or, if_false, dif_pos hx]
    erw [simulateQ_spec_query]
    change _ = seedGenFiniteProgram (⟨x.1, hx⟩, x.2) (seedGenRestrictCache S cache)
    unfold seedGenFiniteProgram
    by_cases hc : (cache x.1).isSome
    · simp [seedGenRestrictCache, hc]
    · simp [seedGenRestrictCache, hc]
      exact seedGenRestrictCache_update S cache x.1 hx x.2

/-- Both oracle copies and programming use the same restricted cache. -/
theorem seedGenFiniteWorld_run (prims : Primitives) (S : Finset (Query C))
    (t : (WorldSpec C).Domain) (ht : seedGenWorldHashInputs t ⊆ S) (cache : HashCache C) :
    (fun r : (WorldSpec C).Range t × HashCache C => (r.1, seedGenRestrictCache S r.2)) <$>
        (worldAnswer prims t).run cache =
      (simulateQ seedGenFiniteLazy (seedGenFiniteWorld prims S t)).run (seedGenRestrictCache S cache) := by
  rcases t with t | t
  · rcases t with t | x
    · exact seedGenFiniteLocal_run prims S t (fun q hq => ht (by simpa [seedGenWorldHashInputs] using hq)) cache
    · exact seedGenFiniteProgramming_run S x (ht (by simp [seedGenWorldHashInputs])) cache
  · exact seedGenFiniteLocal_run prims S t (fun q hq => ht (by simpa [seedGenWorldHashInputs] using hq)) cache

/-- The finite translation preserves complete executions, not just individual oracle calls. -/
theorem seedGenFiniteWorld_simulate_run (prims : Primitives) (S : Finset (Query C))
    {α : Type} (oa : OracleComp (WorldSpec C) α) (hc : SeedGenWorldCovered S oa) :
    ∀ cache : HashCache C,
      (fun r : α × HashCache C => (r.1, seedGenRestrictCache S r.2)) <$>
          (simulateQ (worldAnswer prims) oa).run cache =
        (simulateQ seedGenFiniteLazy (simulateQ (seedGenFiniteWorld prims S) oa)).run
          (seedGenRestrictCache S cache) := by
  induction hc with
  | pure a => intro cache; rfl
  | query_bind t k ht hk ih =>
    intro cache
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
    rw [← seedGenFiniteWorld_run prims S t ht cache, bind_map_left]
    exact bind_congr fun p => ih p.1 p.2

/-- Full lazy-to-eager conversion for a programmable world, from every initial cache. -/
theorem evalDist_seedGenWorld_eager (prims : Primitives) (S : Finset (Query C))
    {α : Type} (oa : OracleComp (WorldSpec C) α) (hc : SeedGenWorldCovered S oa)
    (cache : HashCache C) :
    (simulateQ (worldAnswer prims) oa).run' cache =ᵈ
      (do let h ← $ᵗ (S → HashOutput);
            (simulateQ (seedGenFiniteEager h) (simulateQ (seedGenFiniteWorld prims S) oa)).run'
              (seedGenRestrictCache S cache)) := by
  have he := congrArg (Functor.map Prod.fst) (seedGenFiniteWorld_simulate_run prims S oa hc cache)
  simp only [Functor.map_map] at he
  change (simulateQ (worldAnswer prims) oa).run' cache =
    (simulateQ seedGenFiniteLazy (simulateQ (seedGenFiniteWorld prims S) oa)).run'
      (seedGenRestrictCache S cache) at he
  rw [he, StateT.run'_eq]
  refine ((evalDist_seedGenFiniteEager _ _).map _).trans ?_
  simp only [StateT.run'_eq]
  rw [map_bind]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- The fixed total oracle represented by a finite table; the MPC domains still use `Th`. -/
def seedGenFiniteTotal (prims : Primitives) (S : Finset (Query C)) (h : S → HashOutput)
    (q : Query C) : HashOutput :=
  match q with
  | .hash input => if MpcInput input then prims.Th input else
      if hq : q ∈ S then h ⟨q, hq⟩ else 0
  | _ => if hq : q ∈ S then h ⟨q, hq⟩ else 0

/-- Reading a table value into the occupancy cache leaves the overlaid total function unchanged. -/
theorem seedGenTableExtending_read {Ω : Type} [DecidableEq Ω] (cache : SeedGenFiniteCache Ω)
    (h : Ω → HashOutput) (q : Ω) :
    tableExtending (cache.cacheQuery q (tableExtending cache h q)) h = tableExtending cache h := by
  rw [tableExtending_cacheQuery, Function.update_eq_self]

/-- An eager hash step preserves the total oracle, although it records occupancy for later
programming attempts. -/
theorem seedGenFiniteHash_eager_step (prims : Primitives) (S : Finset (Query C))
    (h : S → HashOutput) (q : Query C) (cache : SeedGenFiniteCache S) :
    ∃ cache',
      (simulateQ (seedGenFiniteEager h) (seedGenFiniteHash prims S q)).run cache =
        pure (seedGenFiniteTotal prims S (tableExtending cache h) q, cache') ∧
      tableExtending cache' h = tableExtending cache h := by
  by_cases hf : IsFixed q
  · obtain ⟨input, rfl, hi⟩ := hf
    exact ⟨cache, by simp [seedGenFiniteHash, seedGenFiniteTotal, hi], rfl⟩
  · have hred : seedGenFiniteHash prims S q =
        if hq : q ∈ S then OracleComp.lift ((SeedGenFiniteSpec S).query (.inr (.inl ⟨q, hq⟩))) else pure 0 := by
      cases q <;> simp_all [seedGenFiniteHash, IsFixed]
    have hv : seedGenFiniteTotal prims S (tableExtending cache h) q =
        if hq : q ∈ S then tableExtending cache h ⟨q, hq⟩ else 0 := by
      cases q <;> simp_all [seedGenFiniteTotal, IsFixed]
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
        · simpa only [tableExtending, hc, Option.getD_none] using seedGenTableExtending_read cache h ⟨q, hq⟩
      | some y =>
        refine ⟨cache, ?_, rfl⟩
        rw [QueryImpl.withCaching_run_some _ hc]
        simp [tableExtending, hc]
    · exact ⟨cache, by simp [hq], rfl⟩

/-- After the last programming block, the whole adaptive local computation sees one fixed
oracle. Private honest hashes do not change that oracle or restrict later legitimate queries. -/
theorem seedGenFiniteLocal_eager_fixed (prims : Primitives) (S : Finset (Query C))
    (h : S → HashOutput) {α : Type} (oa : OracleComp (LocalSpec C) α) :
    ∀ cache : SeedGenFiniteCache S,
      (simulateQ (seedGenFiniteEager h) (simulateQ (seedGenFiniteLocal prims S) oa)).run' cache =
        simulateQ (fixedLocal prims (seedGenFiniteTotal prims S (tableExtending cache h))) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro cache; rfl
  | query_bind t k ih =>
    intro cache
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    rcases t with n | q | x
    · change ((fun y => (y, cache)) <$> (query (spec := unifSpec) n : ProbComp _)) >>=
        (fun p : unifSpec.Range n × SeedGenFiniteCache S =>
          Prod.fst <$> (simulateQ (seedGenFiniteEager h) (simulateQ (seedGenFiniteLocal prims S) (k p.1))).run p.2) = _
      rw [bind_map_left]
      apply bind_congr
      intro y
      exact ih y cache
    · obtain ⟨cache', he, ht⟩ := seedGenFiniteHash_eager_step prims S h q cache
      change (simulateQ (seedGenFiniteEager h) (seedGenFiniteHash prims S q)).run cache >>= _ = _
      rw [he, pure_bind]
      change (simulateQ (seedGenFiniteEager h) (simulateQ (seedGenFiniteLocal prims S)
        (k (seedGenFiniteTotal prims S (tableExtending cache h) q)))).run' cache' = _
      rw [ih, ht]
      rfl
    · obtain ⟨cache', he, ht⟩ := seedGenFiniteHash_eager_step prims S h (.streamKey x.2.1) cache
      change (simulateQ (seedGenFiniteEager h) (seedGenFiniteHash prims S (.streamKey x.2.1) >>=
        fun y => pure (prims.aes.eval (truncateHash y) x.2.2))).run cache >>= _ = _
      simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, he, pure_bind]
      change (simulateQ (seedGenFiniteEager h) (simulateQ (seedGenFiniteLocal prims S)
        (k (prims.aes.eval (truncateHash (seedGenFiniteTotal prims S (tableExtending cache h)
          (.streamKey x.2.1))) x.2.2)))).run' cache' = _
      rw [ih, ht]
      rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The number of actual programming attempts; it does not depend on the transcript. -/
def seedGenProgrammingCount (coalition : C.Coalition) : ℕ :=
  1 + (seedGenKnownCoordinates coalition).length + (seedGenCrossCoordinates coalition).length

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Erase only private coordinates that no corrupt recipient receives. -/
def seedGenExposedParts (coalition : C.Coalition) (parts : C.Party → Parts C) : C.Party → Parts C :=
  fun i => ⟨(parts i).parameter,
    fun T => if KnownTo coalition.1 T then (parts i).term T else 0,
    fun j => if i ∈ coalition.1 ∨ j ∈ coalition.1 then (parts i).pair j else 0⟩

theorem seedGenExposedParts_privateInvariant (coalition : C.Coalition) :
    SeedGenPrivateInvariant coalition (seedGenExposedParts coalition) := by
  constructor
  · intro a T hh c parts
    funext i
    change Parts.mk _ _ _ = Parts.mk _ _ _
    congr 1
    · simp only [seedGenExposedParts, shiftAt]
      split_ifs <;> rfl
    · funext U
      by_cases hU : KnownTo coalition.1 U
      · have hne : T ≠ U := fun he => hh (he ▸ hU)
        by_cases hi : i = a <;> simp [hU, shiftAt, shiftParts, hne, hi]
      · simp [seedGenExposedParts, hU]
    · funext j
      simp only [seedGenExposedParts, shiftAt]
      split_ifs <;> rfl
  · intro p ha hb c parts
    funext i
    change Parts.mk _ _ _ = Parts.mk _ _ _
    congr 1
    · simp only [seedGenExposedParts, shiftAt]
      split_ifs <;> rfl
    · funext T
      simp only [seedGenExposedParts, shiftAt]
      split_ifs <;> rfl
    · funext j
      by_cases hi : i = p.1.1
      · subst i
        by_cases hj : j = p.1.2
        · subst j; simp [seedGenExposedParts, ha, hb]
        · simp [seedGenExposedParts, shiftAt, shiftParts, Ne.symm hj]
      · simp [seedGenExposedParts, shiftAt, hi]

theorem seedGenExposedParts_reveal (coalition : C.Coalition) (parts : C.Party → Parts C)
    (i j : C.Party) (hj : j ∈ coalition.1) :
    revealTo .seedGen (seedGenExposedParts coalition parts i) i j = revealTo .seedGen (parts i) i j := by
  simp only [revealTo, seedGenExposedParts, hj, or_true, if_true]
  congr 2
  apply List.map_congr_left
  intro T hT
  simp [seedGen_sharedTerms_known coalition i j hj T hT]

/-- Commit-round aborts depend only on the corrupt messages, including self messages. -/
def seedGenCommitAborted (coalition : C.Coalition) (sent : C.Party → Mail C E) (i : C.Party) : Bool :=
  C.parties.any fun j => if j ∈ coalition.1 then Msg.isAbort (sent j i) else false

theorem seedGenCommitInbox_aborted (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) (sent : C.Party → Mail C E) (i : C.Party) :
    (C.parties.any fun j => Msg.isAbort (seedGenCommitInbox coalition parts commitments sent i j)) =
      seedGenCommitAborted coalition sent i := by
  unfold seedGenCommitAborted
  apply congrArg (fun f => C.parties.any f)
  funext j
  by_cases hj : j ∈ coalition.1
  · simp [seedGenCommitInbox, roundInbox, hj]
  · simp [seedGenCommitInbox, roundInbox, seedGenInitialSteps, hj, seedGenStart,
      Step.delivered, isAbort_commitOutbox]

/-- The real reveal inbox expressed without private commitment digests. -/
def seedGenReferenceRevealInbox (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitSent revealSent : C.Party → Mail C E) (i j : C.Party) : Option (Msg E) :=
  if j ∈ coalition.1 then revealSent j i else
    if seedGenCommitAborted coalition commitSent j then some .abort else
      revealOutbox .seedGen j (parts j) i

theorem seedGenRevealInbox_reference (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) (commitSent revealSent : C.Party → Mail C E) :
    seedGenRevealInbox coalition parts (seedGenCommitInbox coalition parts commitments commitSent) revealSent =
      seedGenReferenceRevealInbox coalition parts commitSent revealSent := by
  funext i j
  simp only [seedGenRevealInbox, roundInbox, seedGenRevealSteps, seedGenCommitInbox_aborted,
    seedGenReferenceRevealInbox]
  by_cases hj : j ∈ coalition.1
  · simp [hj]
  · simp only [hj, false_or, if_false]
    split_ifs <;> rfl

/-- Once the reveal round has no abort, only corrupt openings need checking. -/
theorem seedGenOpenCheck_corrupt_iff (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) (hi : i ∉ coalition.1)
    (ha : (C.parties.any fun j => Msg.isAbort
      (seedGenReferenceRevealInbox coalition parts commitSent revealSent i j)) = false) :
    let commitments := fun j => D prims h (commitQueries .seedGen j (parts j))
    let committed := seedGenCommitInbox coalition parts commitments commitSent
    let revealed := seedGenReferenceRevealInbox coalition parts commitSent revealSent
    openCheck .seedGen i (parts i) (committed i) (revealed i)
      (D prims h (openQueries .seedGen i (revealed i))) ↔
      ∀ j, j ∈ coalition.1 →
        (Msg.hashesOf (revealSent j i)).length = (revealTo .seedGen (parts i) j i).length ∧
        [h (.commit .seedGen j i (Msg.hashesOf (revealSent j i)))] = Msg.hashesOf (commitSent j i) := by
  dsimp only
  have hreceived := seedGenRevealInbox_all_honest coalition parts
    (seedGenCommitInbox coalition parts (fun j => D prims h (commitQueries .seedGen j (parts j))) commitSent)
    revealSent i (by simpa only [seedGenRevealInbox_reference] using ha)
  rw [seedGenRevealInbox_reference] at hreceived
  simp only [openCheck, openQueries, D_mapM, D_hashQuery, getD_parties]
  constructor
  · intro ho j hj
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simpa only [seedGenReferenceRevealInbox, if_pos hj, seedGenCommitInbox, roundInbox] using ho j hji
  · intro ho j hji
    by_cases hj : j ∈ coalition.1
    · simpa only [seedGenReferenceRevealInbox, if_pos hj, seedGenCommitInbox, roundInbox] using ho j hj
    · rw [hreceived i j hj hji]
      constructor
      · simp [revealTo]
      · simp only [seedGenCommitInbox, roundInbox, if_neg hj, seedGenInitialSteps, if_neg hj,
          seedGenStart, Step.delivered, commitOutbox, if_neg (Ne.symm hji), Msg.hashesOf,
          D_commitQueries, getD_parties]

/-- Honest parts together with the actual corrupt openings, without unused read fields. -/
def seedGenCorruptView (coalition : C.Coalition) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i j : C.Party) : Parts C :=
  if j ∈ coalition.1 then readReveal .seedGen (Msg.hashesOf (revealed i j)) i j else parts j

theorem seedGen_derived_corruptView (prims : Primitives) (coalition : C.Coalition)
    (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E) (i : C.Party) (hi : i ∉ coalition.1)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .seedGen (parts j) j i)
    (h : Query C → HashOutput) :
    D prims h (deriveKeys .seedGen i (setupView .seedGen i (parts i) (revealed i))) =
      D prims h (deriveKeys .seedGen i (seedGenCorruptView coalition parts revealed i)) := by
  have corrupt (j : C.Party) (hj : j ∈ coalition.1) :
      setupView .seedGen i (parts i) (revealed i) j = seedGenCorruptView coalition parts revealed i j := by
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    simp only [setupView, if_neg hji, seedGenCorruptView, if_pos hj]
  have parameter (j : C.Party) :
      (setupView .seedGen i (parts i) (revealed i) j).parameter =
        (seedGenCorruptView coalition parts revealed i j).parameter := by
    by_cases hj : j ∈ coalition.1
    · rw [corrupt j hj]
    · rw [setupView_honest_sender coalition parts revealed hreceived i j hj, honestView_parameter]
      simp [seedGenCorruptView, hj]
  have term (T : C.Term) (hiT : i ∈ C.holders T) (j : C.Party) (hjT : j ∈ C.holders T) :
      (setupView .seedGen i (parts i) (revealed i) j).term T =
        (seedGenCorruptView coalition parts revealed i j).term T := by
    by_cases hj : j ∈ coalition.1
    · rw [corrupt j hj]
    · rw [setupView_honest_sender coalition parts revealed hreceived i j hj,
        honestView_term .seedGen parts hjT hiT]
      simp [seedGenCorruptView, hj]
  have pair (a b : C.Party) (hab : a = i ∨ b = i) :
      (setupView .seedGen i (parts i) (revealed i) a).pair b =
        (seedGenCorruptView coalition parts revealed i a).pair b := by
    by_cases ha : a ∈ coalition.1
    · rw [corrupt a ha]
    · rw [setupView_honest_sender coalition parts revealed hreceived i a ha,
        honestView_pair .seedGen parts hab]
      simp [seedGenCorruptView, ha]
  rw [D_deriveKeys, D_deriveKeys]
  simp only [ite_true]
  apply Prod.ext
  · apply congrArg h
    apply congrArg (Query.derive .seedGen .parameter)
    apply List.map_congr_left
    intro j _
    exact parameter j
  · apply Prod.ext
    · funext T
      by_cases hiT : i ∈ C.holders T
      · simp only [if_pos hiT]
        apply congrArg h
        apply congrArg (Query.derive .seedGen .term)
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
        apply congrArg (Query.derive .seedGen .pair)
        exact congrArg₂ List.cons (pair _ _ hp)
          (congrArg (fun y => [y]) (pair _ _ hp.symm))

/-- Replace the hidden derived keys by an independently named table. -/
def seedGenMaskKeys (coalition : C.Coalition) (table : KeyName C → HashOutput) (i : C.Party)
    (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput) :=
  (keys.1, fun T => if KnownTo coalition.1 T then keys.2.1 T else
    if i ∈ C.holders T then table (.term T) else 0,
   fun j => if hj : j = i then 0 else
     if i ∈ coalition.1 ∨ j ∈ coalition.1 then keys.2.2 j
     else table (.pair (C.pairOf i j (Ne.symm hj))))

/-- The reference derivation uses the actual corrupt openings. -/
def seedGenReferenceKeys (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) :=
  seedGenMaskKeys coalition table i
    (D prims h (deriveKeys .seedGen i (seedGenCorruptView coalition parts revealed i)))

theorem seedGenReferenceKeys_exposed (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) :
    seedGenReferenceKeys prims coalition h table (seedGenExposedParts coalition parts) revealed i =
      seedGenReferenceKeys prims coalition h table parts revealed i := by
  have hp (j : C.Party) :
      (seedGenCorruptView coalition (seedGenExposedParts coalition parts) revealed i j).parameter =
        (seedGenCorruptView coalition parts revealed i j).parameter := by
    unfold seedGenCorruptView
    split_ifs <;> rfl
  have ht (T : C.Term) (hT : KnownTo coalition.1 T) (j : C.Party) :
      (seedGenCorruptView coalition (seedGenExposedParts coalition parts) revealed i j).term T =
        (seedGenCorruptView coalition parts revealed i j).term T := by
    unfold seedGenCorruptView
    split_ifs <;> simp [seedGenExposedParts, hT]
  have hpair (a b : C.Party) (hab : a ∈ coalition.1 ∨ b ∈ coalition.1) :
      (seedGenCorruptView coalition (seedGenExposedParts coalition parts) revealed i a).pair b =
        (seedGenCorruptView coalition parts revealed i a).pair b := by
    unfold seedGenCorruptView
    split_ifs <;> simp [seedGenExposedParts, hab]
  simp only [seedGenReferenceKeys, seedGenMaskKeys, D_deriveKeys, ite_true]
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
def seedGenReferenceRevealAborted (coalition : C.Coalition)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) : Bool :=
  C.parties.any fun j => if j ∈ coalition.1 then Msg.isAbort (revealSent j i)
    else seedGenCommitAborted coalition commitSent j

theorem seedGenReferenceRevealInbox_aborted (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) :
    (C.parties.any fun j => Msg.isAbort (seedGenReferenceRevealInbox coalition parts commitSent revealSent i j)) =
      seedGenReferenceRevealAborted coalition commitSent revealSent i := by
  unfold seedGenReferenceRevealAborted
  apply congrArg (fun f => C.parties.any f)
  funext j
  unfold seedGenReferenceRevealInbox
  by_cases hj : j ∈ coalition.1
  · simp [hj]
  · simp only [if_neg hj]
    cases hb : seedGenCommitAborted coalition commitSent j <;>
      simp [hb, revealOutbox, Msg.isAbort]

/-- Check each actual corrupt opening against its earlier commitment and expected length. -/
def seedGenReferenceOpenCheck (coalition : C.Coalition) (h : Query C → HashOutput)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) : Prop :=
  ∀ j, j ∈ coalition.1 →
    (Msg.hashesOf (revealSent j i)).length = 1 + (sharedTerms j i).length + 1 ∧
    [h (.commit .seedGen j i (Msg.hashesOf (revealSent j i)))] = Msg.hashesOf (commitSent j i)

/-- Concrete reference data for the echo round. Only hidden derivations are replaced. -/
def seedGenReferenceData (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E)
    (i : C.Party) : Option (SeedGenEchoData C) :=
  if i ∈ coalition.1 ∨ seedGenCommitAborted coalition commitSent i then none else
    if seedGenReferenceRevealAborted coalition commitSent revealSent i then none else
      if seedGenReferenceOpenCheck coalition h commitSent revealSent i then
        let keys := seedGenReferenceKeys prims coalition h table parts (fun i j => revealSent j i) i
        some (keys, D prims h (sharedQueries .seedGen i keys))
      else none

theorem seedGenReferenceData_exposed (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) :
    seedGenReferenceData prims coalition h table (seedGenExposedParts coalition parts) commitSent revealSent =
      seedGenReferenceData prims coalition h table parts commitSent revealSent := by
  funext i
  simp only [seedGenReferenceData, seedGenReferenceKeys_exposed]

/-- Masking the actual reveal computation gives exactly the concrete reference data. -/
theorem seedGenRevealAllFixed_mask (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) (i : C.Party) :
    let committed := seedGenCommitInbox coalition parts
      (fun j => D prims h (commitQueries .seedGen j (parts j))) commitSent
    Option.map (fun data : SeedGenEchoData C =>
      let keys := seedGenMaskKeys coalition table i data.1
      (keys, D prims h (sharedQueries .seedGen i keys)))
      (seedGenRevealAllFixed prims coalition h parts committed revealSent i) =
        seedGenReferenceData prims coalition h table parts commitSent revealSent i := by
  dsimp only
  unfold seedGenRevealAllFixed seedGenReferenceData
  rw [seedGenCommitInbox_aborted]
  by_cases hi : i ∈ coalition.1 ∨ seedGenCommitAborted coalition commitSent i = true
  · simp only [if_pos hi, Option.map_none]
  · simp only [if_neg hi, seedGenRevealDataFixed, seedGenRevealInbox_reference,
      seedGenReferenceRevealInbox_aborted]
    by_cases ha : seedGenReferenceRevealAborted coalition commitSent revealSent i = true
    · simp only [if_pos ha, Option.map_none]
    · simp only [if_neg ha]
      have hi' : i ∉ coalition.1 := fun hh => hi (Or.inl hh)
      have ha' : (C.parties.any fun j => Msg.isAbort
          (seedGenReferenceRevealInbox coalition parts commitSent revealSent i j)) = false := by
        rw [seedGenReferenceRevealInbox_aborted]
        exact Bool.eq_false_iff.mpr ha
      have hc := seedGenOpenCheck_corrupt_iff prims coalition h parts commitSent revealSent i hi' ha'
      dsimp only at hc
      have hl (j : C.Party) : (revealTo .seedGen (parts i) j i).length =
          1 + (sharedTerms j i).length + 1 := by simp [revealTo, Nat.add_comm]
      simp only [hl] at hc
      change _ ↔ seedGenReferenceOpenCheck coalition h commitSent revealSent i at hc
      rw [hc]
      split_ifs with ho
      · simp only [Option.map_some]
        have hreceived := seedGenRevealInbox_all_honest coalition parts
          (seedGenCommitInbox coalition parts (fun j => D prims h (commitQueries .seedGen j (parts j))) commitSent)
          revealSent i (by simpa only [seedGenRevealInbox_reference] using ha')
        rw [seedGenRevealInbox_reference] at hreceived
        rw [seedGen_derived_corruptView prims coalition parts _ i hi' hreceived h]
        have hv : seedGenCorruptView coalition parts
            (seedGenReferenceRevealInbox coalition parts commitSent revealSent) i =
              seedGenCorruptView coalition parts (fun i j => revealSent j i) i := by
          funext j
          unfold seedGenCorruptView
          split_ifs with hj
          · simp only [seedGenReferenceRevealInbox, if_pos hj]
          · rfl
        rw [hv]
        rfl
      · rfl

/-- A consistent named table leaves the actual hidden derivations unchanged. -/
theorem seedGenMaskKeys_actual (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (revealed : C.Party → Mail C E)
    (hreceived : ∀ i j, j ∉ coalition.1 → j ≠ i →
      Msg.hashesOf (revealed i j) = revealTo .seedGen (parts j) j i)
    (htable : ∀ name, Hidden coalition name → table name = h (seedGenNamedInput parts name))
    (i : C.Party) (hi : i ∉ coalition.1) :
    seedGenMaskKeys coalition table i
      (D prims h (deriveKeys .seedGen i (setupView .seedGen i (parts i) (revealed i)))) =
        D prims h (deriveKeys .seedGen i (setupView .seedGen i (parts i) (revealed i))) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · funext T
    by_cases hT : KnownTo coalition.1 T
    · simp [seedGenMaskKeys, hT]
    · simp only [seedGenMaskKeys, if_neg hT]
      by_cases hiT : i ∈ C.holders T
      · rw [if_pos hiT, htable (.term T) hT,
          seedGen_hiddenTerm_derived prims coalition h parts revealed hreceived T hT i hiT]
        rfl
      · simp [hiT, D_deriveKeys]
  · funext j
    by_cases hji : j = i
    · subst j; simp [seedGenMaskKeys, D_deriveKeys]
    · simp only [seedGenMaskKeys, dif_neg hji]
      by_cases hj : j ∈ coalition.1
      · simp [hj]
      · simp only [hi, hj, or_self, if_false]
        rw [seedGen_hiddenPair_derived prims coalition h parts revealed hreceived i j hi hj hji]
        apply htable
        change (C.pairOf i j (Ne.symm hji)).1.1 ∉ coalition.1 ∧
          (C.pairOf i j (Ne.symm hji)).1.2 ∉ coalition.1
        unfold Committee.pairOf
        split_ifs <;> exact ⟨by assumption, by assumption⟩

/-- The fixed-oracle actual reveal equals the reference when the named table records its
hidden derivations. Abort and opening failures are included in the equality. -/
theorem seedGenRevealAllFixed_reference (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput) (parts : C.Party → Parts C)
    (htable : ∀ name, Hidden coalition name → table name = h (seedGenNamedInput parts name))
    (commitSent revealSent : C.Party → Mail C E) :
    seedGenRevealAllFixed prims coalition h parts
      (seedGenCommitInbox coalition parts (fun j => D prims h (commitQueries .seedGen j (parts j))) commitSent)
      revealSent = seedGenReferenceData prims coalition h table parts commitSent revealSent := by
  funext i
  rw [← seedGenRevealAllFixed_mask prims coalition h table parts commitSent revealSent i]
  let committed := seedGenCommitInbox coalition parts
    (fun j => D prims h (commitQueries .seedGen j (parts j))) commitSent
  change seedGenRevealAllFixed prims coalition h parts committed revealSent i = _
  cases hd : seedGenRevealAllFixed prims coalition h parts committed revealSent i with
  | none => rfl
  | some data =>
    have hi : i ∉ coalition.1 := by
      intro hc
      simp [seedGenRevealAllFixed, hc] at hd
    have ha : (seedGenRevealAllFixed prims coalition h parts committed revealSent i).isSome := by
      simp only [hd, Option.isSome_some]
    obtain ⟨he, hb⟩ := seedGenRevealAllFixed_some prims coalition h parts committed revealSent i ha
    have hr := seedGenRevealInbox_all_honest coalition parts committed revealSent i hb
    have hv := Option.some.inj (hd.symm.trans he)
    simp only [hv, Option.map_some, seedGenMaskKeys_actual prims coalition h table parts _ hr htable i hi]

/-- The complete corrupt-facing reveal view, retaining honest commit aborts. -/
def seedGenReferenceRevealView (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitSent : C.Party → Mail C E) (c i : C.Party) : Option (Msg E) :=
  if c ∈ coalition.1 ∧ i ∉ coalition.1 then
    if seedGenCommitAborted coalition commitSent i then none else revealOutbox .seedGen i (parts i) c
  else none

theorem seedGenRevealSteps_view_reference (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) (commitSent : C.Party → Mail C E) :
    (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (seedGenRevealSteps coalition parts (seedGenCommitInbox coalition parts commitments commitSent) i).outbox c
      else none) = seedGenReferenceRevealView coalition parts commitSent := by
  funext c i
  unfold seedGenReferenceRevealView
  by_cases hc : c ∈ coalition.1 ∧ i ∉ coalition.1
  · simp only [if_pos hc, seedGenRevealSteps, hc.2, false_or, seedGenCommitInbox_aborted]
    split_ifs <;> rfl
  · simp only [if_neg hc]

theorem seedGenReferenceRevealView_exposed (coalition : C.Coalition) (parts : C.Party → Parts C)
    (commitSent : C.Party → Mail C E) :
    seedGenReferenceRevealView coalition (seedGenExposedParts coalition parts) commitSent =
      seedGenReferenceRevealView coalition parts commitSent := by
  funext c i
  unfold seedGenReferenceRevealView
  split_ifs with hc hb
  · rfl
  · simp only [revealOutbox, seedGenExposedParts_reveal coalition parts i c hc.1]
  · rfl

/-- The reference executes the actual adversary and actual final echo check. -/
def seedGenReferencePostCommit (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (commitSent : C.Party → Mail C E) :
    OracleComp (LocalSpec C) (A.State × (C.Party → Option (Keys C))) :=
  if ∀ i, i ∉ coalition.1 → seedGenCommitAborted coalition commitSent i = true then
    pure (state, fun _ => none)
  else do
    let (st, sent) ← A.round state (seedGenReferenceRevealView coalition parts commitSent)
    seedGenFinishLocal coalition A st (seedGenReferenceData prims coalition h table parts commitSent sent)

theorem seedGenReferencePostCommit_exposed (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State)
    (parts : C.Party → Parts C) (commitSent : C.Party → Mail C E) :
    seedGenReferencePostCommit prims coalition h table A state (seedGenExposedParts coalition parts) commitSent =
      seedGenReferencePostCommit prims coalition h table A state parts commitSent := by
  simp only [seedGenReferencePostCommit, seedGenReferenceRevealView_exposed, seedGenReferenceData_exposed]

/-- Exact connection to both actual remaining rounds in the fixed-oracle representation. -/
theorem simulateQ_seedGenPostCommit_reference (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (htable : ∀ name, Hidden coalition name → table name = h (seedGenNamedInput parts name))
    (commitSent : C.Party → Mail C E) :
    simulateQ (fixedLocal prims h) (seedGenPostCommitLocal coalition A state parts
      (seedGenCommitInbox coalition parts (fun j => D prims h (commitQueries .seedGen j (parts j))) commitSent)) =
      simulateQ (fixedLocal prims h) (seedGenReferencePostCommit prims coalition h table A state parts commitSent) := by
  simp only [seedGenPostCommitLocal, seedGenCommitInbox_aborted, seedGenReferencePostCommit]
  split_ifs with ha
  · rfl
  · rw [seedGenRevealSteps_view_reference]
    simp only [simulateQ_bind]
    apply bind_congr
    intro r
    rcases r with ⟨st, sent⟩
    rw [simulateQ_fixedLocal_seedGenRevealComputations, pure_bind,
      seedGenRevealAllFixed_reference prims coalition h table parts htable]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- Actual honest commitments as seen by the corrupted recipients, under a fixed oracle. -/
def seedGenFixedCommitView (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (c i : C.Party) : Option (Msg E) :=
  if c ∈ coalition.1 ∧ i ∉ coalition.1 then
    commitOutbox i (D prims h (commitQueries .seedGen i (parts i))) c else none

theorem seedGenFixedCommitView_exposed (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    seedGenFixedCommitView (E := E) prims coalition h (seedGenExposedParts coalition parts) =
      seedGenFixedCommitView prims coalition h parts := by
  funext c i
  unfold seedGenFixedCommitView
  by_cases hc : c ∈ coalition.1 ∧ i ∉ coalition.1
  · simp only [if_pos hc, commitOutbox, D_commitQueries, getD_parties,
      seedGenExposedParts_reveal coalition parts i c hc.1]
  · simp only [if_neg hc]

/-- Full reference execution, with the original adversary, distinguisher, and abort behavior. -/
def seedGenReferenceLocalGame (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) : OracleComp (LocalSpec C) Bool := do
  let state ← A.start (corruptInputs coalition x) z
  let (st, sent) ← A.round state (seedGenFixedCommitView prims coalition h parts)
  let r ← seedGenReferencePostCommit prims coalition h table A st parts sent
  Z r

theorem seedGenReferenceLocalGame_exposed (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) :
    seedGenReferenceLocalGame prims coalition h table A x z Z (seedGenExposedParts coalition parts) =
      seedGenReferenceLocalGame prims coalition h table A x z Z parts := by
  simp only [seedGenReferenceLocalGame, seedGenFixedCommitView_exposed, seedGenReferencePostCommit_exposed]

/-- Private-coordinate independence is proved for the whole adaptive reference execution. -/
theorem seedGenReferenceLocalGame_privateInvariant (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    SeedGenPrivateInvariant coalition (seedGenReferenceLocalGame prims coalition h table A x z Z) := by
  have he := seedGenReferenceLocalGame_exposed prims coalition h table A x z Z
  have hinv := seedGenExposedParts_privateInvariant coalition
  constructor
  · intro a T hT c parts
    rw [← he (shiftAt a (some T) none c parts), hinv.1 a T hT c parts, he parts]
  · intro p ha hb c parts
    rw [← he (shiftAt p.1.1 none (some p.1.2) c parts), hinv.2 p ha hb c parts, he parts]

theorem seedGenFinishLocal_queryBound (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (state : A.State) (data : C.Party → Option (SeedGenEchoData C)) :
    IsQueryBoundP (seedGenFinishLocal coalition A state data) Counted step := by
  unfold seedGenFinishLocal
  split_ifs
  · exact isQueryBoundP_pure Counted _ step
  · simpa using isQueryBoundP_bind (hr state _) (fun r _ => isQueryBoundP_pure Counted
      (r.1, seedGenEchoDataOutput coalition data r.2) 0)

theorem seedGenReferencePostCommit_queryBound (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) Counted step)
    (state : A.State) (parts : C.Party → Parts C) (sent : C.Party → Mail C E) :
    IsQueryBoundP (seedGenReferencePostCommit prims coalition h table A state parts sent) Counted (2 * step) := by
  unfold seedGenReferencePostCommit
  split_ifs
  · exact isQueryBoundP_pure Counted _ _
  · simpa only [two_mul] using isQueryBoundP_bind (hr state _)
      (fun r _ => seedGenFinishLocal_queryBound coalition A step hr r.1 _)

/-- The reference consumes only the original adversary/distinguisher budget. -/
theorem seedGenReferenceLocalGame_queryBound (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q)
    (parts : C.Party → Parts C) :
    IsQueryBoundP (seedGenReferenceLocalGame prims coalition h table A x z Z parts) Counted q := by
  obtain ⟨start, step, final, htotal, hs, hr, _, hz⟩ := hq
  unfold seedGenReferenceLocalGame
  have hb := isQueryBoundP_bind (hs (corruptInputs coalition x) z) (fun state _ =>
    isQueryBoundP_bind (hr state (seedGenFixedCommitView prims coalition h parts)) (fun r _ =>
      isQueryBoundP_bind (seedGenReferencePostCommit_queryBound prims coalition h table A step hr r.1 parts r.2)
        (fun out _ => hz out)))
  apply hb.mono
  simp only [setupRounds] at htotal
  omega

theorem seedGenHashLog_query (t : (LocalSpec C).Domain) :
    seedGenHashLog (OracleComp.lift ((LocalSpec C).query t)) =
      (fun u => (u, seedGenLocalHashInputs t)) <$> OracleComp.lift ((LocalSpec C).query t) := by
  simp only [seedGenHashLog, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map]
  simp [QueryImpl.withTraceAppend_apply, QueryImpl.id', WriterT.run_bind, map_eq_bind_pure_comp]

/-- Random inputs in the transcript correspond exactly to counted calls, including PRG. -/
theorem seedGenLocalHashInputs_counted (t : (LocalSpec C).Domain) :
    ((seedGenLocalHashInputs t).filter fun q => ¬ IsFixed q).length = if Counted t then 1 else 0 := by
  rcases t with t | (q | x)
  · simp [seedGenLocalHashInputs, Counted]
  · cases q with
    | hash input =>
      have hf : IsFixed (Query.hash (C := C) input) ↔ MpcInput input := by simp [IsFixed]
      by_cases hm : MpcInput input <;> simp [seedGenLocalHashInputs, Counted, List.filter_cons, hf, hm]
    | _ => simp [seedGenLocalHashInputs, Counted, IsFixed]
  · simp [seedGenLocalHashInputs, Counted, IsFixed]

/-- A syntactic query budget bounds the logged random inputs, regardless of answers. -/
theorem seedGenHashLog_random_length_le {α : Type} (oa : OracleComp (LocalSpec C) α)
    (n : ℕ) (hq : IsQueryBoundP oa Counted n) (r : α × List (Query C))
    (hr : r ∈ support (seedGenHashLog oa)) :
    (r.2.filter fun q => ¬ IsFixed q).length ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n r with
  | pure a =>
    simp only [seedGenHashLog_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    rw [seedGenHashLog_bind, seedGenHashLog_query] at hr
    simp only [support_bind, support_map, Set.mem_iUnion, Set.mem_image, Prod.exists,
      support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, l, ⟨v, _, he⟩, a, rest, hk, hr⟩ := hr
    cases he
    cases hr
    have hrest := ih u _ (hq.2 u) (a, rest) hk
    simp only [List.filter_append, List.length_append, seedGenLocalHashInputs_counted]
    split_ifs at hrest ⊢ with ht <;> simp_all <;> omega

/-- A fixed-oracle interpretation cannot add a new syntactic output. -/
theorem seedGenFixedLocal_support_subset (prims : Primitives) (h : Query C → HashOutput)
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
def seedGenReferenceKernel (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (parts : C.Party → Parts C) :
    ProbComp (Bool × List (Query C)) :=
  simulateQ (fixedLocal prims h)
    (seedGenHashLog (seedGenReferenceLocalGame prims coalition h table A x z Z parts))

theorem seedGenReferenceKernel_privateInvariant (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) :
    SeedGenPrivateInvariant coalition (seedGenReferenceKernel prims coalition h table A x z Z) := by
  have hi := seedGenReferenceLocalGame_privateInvariant prims coalition h table A x z Z
  constructor
  · intro a T hT c parts
    unfold seedGenReferenceKernel
    rw [hi.1 a T hT c parts]
  · intro p ha hb c parts
    unfold seedGenReferenceKernel
    rw [hi.2 p ha hb c parts]

theorem seedGenReferenceKernel_random_length_le (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (A : Adversary C E Unit PEmpty PEmpty) (x : C.Party → Unit) (z : Aux)
    (Z : Distinguisher C A.State (Keys C)) (q : ℕ) (hq : IsQueryBounded A Z setupRounds q)
    (parts : C.Party → Parts C) (r : Bool × List (Query C))
    (hr : r ∈ support (seedGenReferenceKernel prims coalition h table A x z Z parts)) :
    (r.2.filter fun v => ¬ IsFixed v).length ≤ q :=
  seedGenHashLog_random_length_le _ q
    (seedGenReferenceLocalGame_queryBound prims coalition h table A x z Z q hq parts) r
    (seedGenFixedLocal_support_subset prims h _ hr)

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The reference reaches echo precisely when these actual abort and opening checks pass. -/
def seedGenReferenceActive (coalition : C.Coalition) (h : Query C → HashOutput)
    (commitSent revealSent : C.Party → Mail C E) (i : C.Party) : Prop :=
  i ∉ coalition.1 ∧ seedGenCommitAborted coalition commitSent i = false ∧
    seedGenReferenceRevealAborted coalition commitSent revealSent i = false ∧
    seedGenReferenceOpenCheck coalition h commitSent revealSent i

theorem seedGenReferenceData_active (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) (i : C.Party) :
    seedGenReferenceData prims coalition h table parts commitSent revealSent i =
      if seedGenReferenceActive coalition h commitSent revealSent i then
        let keys := seedGenReferenceKeys prims coalition h table parts (fun i j => revealSent j i) i
        some (keys, D prims h (sharedQueries .seedGen i keys)) else none := by
  unfold seedGenReferenceData seedGenReferenceActive
  split_ifs <;> simp_all

theorem seedGenReferenceKeys_known (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i : C.Party) (T : C.Term)
    (hT : KnownTo coalition.1 T) :
    (seedGenReferenceKeys prims coalition h left parts revealed i).2.1 T =
      (seedGenReferenceKeys prims coalition h right parts revealed i).2.1 T := by
  simp only [seedGenReferenceKeys, seedGenMaskKeys, if_pos hT]

theorem seedGenReferenceKeys_coherent (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i j : C.Party) (T : C.Term)
    (hT : ¬ KnownTo coalition.1 T) (hi : i ∈ C.holders T) (hj : j ∈ C.holders T) :
    (seedGenReferenceKeys prims coalition h table parts revealed i).2.1 T =
      (seedGenReferenceKeys prims coalition h table parts revealed j).2.1 T := by
  simp only [seedGenReferenceKeys, seedGenMaskKeys, if_neg hT, if_pos hi, if_pos hj]

theorem seedGenReferenceKeys_shared_corrupt (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (revealed : C.Party → Mail C E) (i c : C.Party)
    (hc : c ∈ coalition.1) :
    h (.sharedKeys .seedGen ((sharedTerms i c).map
      (seedGenReferenceKeys prims coalition h left parts revealed i).2.1)) =
      h (.sharedKeys .seedGen ((sharedTerms i c).map
        (seedGenReferenceKeys prims coalition h right parts revealed i).2.1)) := by
  apply congrArg h
  exact seedGen_sharedInput_known coalition i c hc _ _
    (seedGenReferenceKeys_known prims coalition h left right parts revealed i)

theorem seedGenReferenceData_echoStep (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (table : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E) (i : C.Party) :
    seedGenEchoDataStep (E := E) i (seedGenReferenceData prims coalition h table parts commitSent revealSent i) =
      seedGenEchoStep prims coalition (seedGenReferenceActive coalition h commitSent revealSent) h
        (seedGenReferenceKeys prims coalition h table parts (fun i j => revealSent j i)) i := by
  rw [seedGenReferenceData_active]
  unfold seedGenEchoStep
  by_cases ha : seedGenReferenceActive coalition h commitSent revealSent i
  · have hi := ha.1
    simp [ha, hi, seedGenEchoDataStep]
  · simp [ha, seedGenEchoDataStep]

/-- Corrupt recipients see identical echo messages for every independent hidden table. -/
theorem seedGenReferenceData_visible (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (left right : KeyName C → HashOutput)
    (parts : C.Party → Parts C) (commitSent revealSent : C.Party → Mail C E)
    (i c : C.Party) (hc : c ∈ coalition.1) :
    (seedGenEchoDataStep (E := E) i (seedGenReferenceData prims coalition h left parts commitSent revealSent i)).outbox c =
      (seedGenEchoDataStep (E := E) i (seedGenReferenceData prims coalition h right parts commitSent revealSent i)).outbox c := by
  simp only [seedGenReferenceData_active]
  split_ifs with ha
  · simp only [seedGenEchoDataStep, Step.outbox, echoOutbox]
    congr 2
    simp only [echoOf, ite_true, D_sharedQueries_at]
    rw [seedGenReferenceKeys_shared_corrupt prims coalition h left right parts _ i c hc]
    rfl
  · rfl

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The real simulator's observed commit round makes no honest hash calls after delivery. -/
theorem stepRound_seedGenInitialSteps_observed (coalition : C.Coalition)
    (A : Adversary C E Unit PEmpty PEmpty) (state : A.State) (parts : C.Party → Parts C)
    (commitments : C.Party → List HashOutput) :
    stepRound observedRoles coalition A noFunctionality state
        (seedGenInitialSteps coalition parts commitments) = (do
      let (st, sent) ← observedRoles.adversary (A.round state fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
        commitOutbox i (commitments i) c else none)
      pure (st, seedGenRevealSteps coalition parts (seedGenCommitInbox coalition parts commitments sent), sent)) := by
  unfold stepRound
  rw [if_neg (by simp only [callInput_real, Option.isSome_none, Bool.false_eq_true,
    and_false, exists_false, false_and, not_false_eq_true])]
  have hmsg : (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      (seedGenInitialSteps coalition parts commitments (E := E) i).outbox c else none) =
      (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then commitOutbox i (commitments i) c else none) := by
    funext c i
    split_ifs with hc
    · simp only [seedGenInitialSteps, if_neg hc.2, seedGenStart, Step.outbox]
    · rfl
  rw [hmsg]
  refine bind_congr fun r => ?_
  rcases r with ⟨st, sent⟩
  dsimp only [observedRoles]
  trans (OverPermutation.sequenceFin (fun j =>
    (pure (seedGenRevealSteps coalition parts (seedGenCommitInbox coalition parts commitments sent) j) :
      WriterT (CallLog C) (OracleComp (WorldSpec C)) _)) >>= fun steps => pure (st, steps, sent))
  · congr 1
    congr 1
    funext j
    by_cases hj : j ∈ coalition.1
    · simp [seedGenInitialSteps, seedGenRevealSteps, hj]
    · simp only [seedGenInitialSteps, if_neg hj, seedGenStart]
      rw [advance_seedGenCommitResume]
      simp only [seedGenRevealSteps, hj, false_or, seedGenCommitInbox, roundInbox]
      simp only [free_pure, liftM_pure]
      rfl
  · rw [sequenceFin_pure, pure_bind]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
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

def seedGenFixedInitialCommitments (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) : C.Party → List HashOutput :=
  fun i => if i ∈ coalition.1 then [] else D prims h (commitQueries .seedGen i (parts i))

theorem simulateQ_fixedLocal_seedGenInitialCommitments (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    simulateQ (fixedLocal prims h) (seedGenInitialCommitments coalition parts) =
      pure (seedGenFixedInitialCommitments prims coalition h parts) := by
  rw [seedGenInitialCommitments, simulateQ_sequenceFin]
  trans OverPermutation.sequenceFin (fun i => (pure (seedGenFixedInitialCommitments prims coalition h parts i) : ProbComp _))
  · congr 1
    funext i
    unfold seedGenFixedInitialCommitments
    split_ifs
    · rfl
    · exact simulateQ_fixedLocal_liftComp (prims := prims) h _
  · exact sequenceFin_pure _

theorem seedGenFixedInitialCommitments_inbox (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) (sent : C.Party → Mail C E) :
    seedGenCommitInbox coalition parts (seedGenFixedInitialCommitments prims coalition h parts) sent =
      seedGenCommitInbox coalition parts (fun j => D prims h (commitQueries .seedGen j (parts j))) sent := by
  funext i j
  unfold seedGenCommitInbox roundInbox
  by_cases hj : j ∈ coalition.1
  · simp only [if_pos hj]
  · simp only [if_neg hj, seedGenInitialSteps, if_neg hj, seedGenFixedInitialCommitments]

theorem seedGenFixedInitialCommitments_view (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (parts : C.Party → Parts C) :
    (fun c i => if c ∈ coalition.1 ∧ i ∉ coalition.1 then
      commitOutbox (E := E) i (seedGenFixedInitialCommitments prims coalition h parts i) c else none) =
      seedGenFixedCommitView prims coalition h parts := by
  funext c i
  unfold seedGenFixedCommitView
  by_cases hc : c ∈ coalition.1 ∧ i ∉ coalition.1
  · simp only [if_pos hc, seedGenFixedInitialCommitments, if_neg hc.2]
  · simp only [if_neg hc]

/-- The whole normalized game equals the concrete reference with the actual hidden oracle
values. The sampling order of `A.start` and honest parts is exchanged only at the distribution level. -/
theorem evalDist_seedGenNormalized_fixed_reference (prims : Primitives) (coalition : C.Coalition)
    (h : Query C → HashOutput) (A : Adversary C E Unit PEmpty PEmpty)
    (x : C.Party → Unit) (z : Aux) (Z : Distinguisher C A.State (Keys C)) :
    simulateQ (fixedLocal prims h) (seedGenNormalizedLocalGame coalition A x z Z) =ᵈ
      (do
        let parts ← OverPermutation.sequenceFin fun _ : C.Party => sampleParts (C := C)
        simulateQ (fixedLocal prims h)
          (seedGenReferenceLocalGame prims coalition h (fun name => h (seedGenNamedInput parts name)) A x z Z parts)) := by
  simp only [seedGenNormalizedLocalGame, simulateQ_bind, simulateQ_sequenceFin,
    simulateQ_fixedLocal_private, simulateQ_fixedLocal_seedGenInitialCommitments, pure_bind]
  refine (OracleComp.EvalDistEq.bind_bind_swap _ _ _).trans ?_
  refine EvalDistEq.bind_right _ fun parts => ?_
  simp only [seedGenReferenceLocalGame, simulateQ_bind]
  refine EvalDistEq.bind_right _ fun state => ?_
  rw [seedGenFixedInitialCommitments_view]
  refine EvalDistEq.bind_right _ ?_
  rintro ⟨st, sent⟩
  dsimp only
  rw [seedGenFixedInitialCommitments_inbox,
    simulateQ_seedGenPostCommit_reference prims coalition h (fun name => h (seedGenNamedInput parts name))
      A st parts (fun _ _ => rfl) sent]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

/-- The vector of honest private parts has a finite type, despite its function fields. -/
theorem seedGenParts_finite (C : Committee) : Finite (Parts C) := by
  apply Finite.of_injective (fun p : Parts C => (p.parameter, p.term, p.pair))
  intro p q hp
  cases p
  cases q
  simpa only [Prod.mk.injEq, Parts.mk.injEq] using hp

/-- All canonical named inputs, for every possible sampled parts vector. This finite set is
only an oracle domain; its cardinality never appears in the security estimate. -/
def seedGenAllNamedInputs (C : Committee) : Finset (Query C) :=
  letI : Finite (Parts C) := seedGenParts_finite C
  letI : Fintype (C.Party → Parts C) := Fintype.ofFinite _
  Finset.univ.biUnion fun parts : C.Party → Parts C =>
    (seedGenNames C).toFinset.image (seedGenNamedInput parts)

theorem seedGenAllNamedInputs_mem (parts : C.Party → Parts C) (name : KeyName C) :
    seedGenNamedInput parts name ∈ seedGenAllNamedInputs C := by
  letI : Finite (Parts C) := seedGenParts_finite C
  letI : Fintype (C.Party → Parts C) := Fintype.ofFinite _
  unfold seedGenAllNamedInputs
  apply Finset.mem_biUnion.mpr
  refine ⟨parts, Finset.mem_univ _, Finset.mem_image.mpr ⟨name, ?_, rfl⟩⟩
  simp [seedGenNames]

/-- A canonical input in the enlarged domain reads an actual sampled cell, never the fallback. -/
theorem seedGenFiniteTotal_named (prims : Primitives) (S : Finset (Query C))
    (h : S → HashOutput) (parts : C.Party → Parts C) (name : KeyName C)
    (hn : seedGenNamedInput parts name ∈ S) :
    seedGenFiniteTotal prims S h (seedGenNamedInput parts name) = h ⟨seedGenNamedInput parts name, hn⟩ := by
  cases name <;>
    simp [seedGenFiniteTotal, seedGenNamedInput, parameterInput, termInput, pairInput] at hn ⊢ <;>
    simp [hn]

end ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- Exchange the finite oracle cells at canonical hidden inputs with the independent dealer
coordinates. Every other oracle cell and every exposed dealer coordinate stays fixed. -/
def seedGenFiniteHiddenSwap (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, seedGenNamedInput parts name ∈ S)
    (p : (S → HashOutput) × (KeyName C → HashOutput)) :
    (S → HashOutput) × (KeyName C → HashOutput) :=
  (fun q => if hh : SeedGenHiddenInput coalition parts q.val then p.2 (Classical.choose hh) else p.1 q,
   fun name => if Hidden coalition name then p.1 ⟨seedGenNamedInput parts name, hmem name⟩ else p.2 name)

theorem seedGenFiniteHiddenSwap_cell (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, seedGenNamedInput parts name ∈ S)
    (hinj : Function.Injective (seedGenNamedInput parts))
    (p : (S → HashOutput) × (KeyName C → HashOutput)) (name : KeyName C) (hh : Hidden coalition name) :
    (seedGenFiniteHiddenSwap coalition S parts hmem p).1 ⟨seedGenNamedInput parts name, hmem name⟩ = p.2 name := by
  have hp : SeedGenHiddenInput coalition parts (seedGenNamedInput parts name) := ⟨name, hh, rfl⟩
  simp only [seedGenFiniteHiddenSwap, dif_pos hp]
  have he : Classical.choose hp = name := hinj (Classical.choose_spec hp).2
  rw [he]

theorem seedGenFiniteHiddenSwap_off (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, seedGenNamedInput parts name ∈ S)
    (p : (S → HashOutput) × (KeyName C → HashOutput)) (q : S)
    (hq : ¬ SeedGenHiddenInput coalition parts q.val) :
    (seedGenFiniteHiddenSwap coalition S parts hmem p).1 q = p.1 q := by
  simp only [seedGenFiniteHiddenSwap, dif_neg hq]

theorem seedGenFiniteHiddenSwap_dealer_known (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, seedGenNamedInput parts name ∈ S)
    (p : (S → HashOutput) × (KeyName C → HashOutput)) (name : KeyName C) (hh : ¬ Hidden coalition name) :
    (seedGenFiniteHiddenSwap coalition S parts hmem p).2 name = p.2 name := by
  simp only [seedGenFiniteHiddenSwap, if_neg hh]

/-- Distinct canonical names make the exchange between oracle and dealer an involution. -/
theorem seedGenFiniteHiddenSwap_involutive (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, seedGenNamedInput parts name ∈ S)
    (hinj : Function.Injective (seedGenNamedInput parts)) :
    Function.Involutive (seedGenFiniteHiddenSwap coalition S parts hmem) := by
  intro p
  apply Prod.ext
  · funext q
    by_cases hq : SeedGenHiddenInput coalition parts q.val
    · obtain ⟨name, hh, he⟩ := hq
      have hq' : q = ⟨seedGenNamedInput parts name, hmem name⟩ := Subtype.ext he.symm
      rw [hq', seedGenFiniteHiddenSwap_cell coalition S parts hmem hinj _ name hh]
      simp only [seedGenFiniteHiddenSwap, if_pos hh]
    · rw [seedGenFiniteHiddenSwap_off coalition S parts hmem _ q hq,
        seedGenFiniteHiddenSwap_off coalition S parts hmem _ q hq]
  · funext name
    by_cases hh : Hidden coalition name
    · change (if Hidden coalition name then
        (seedGenFiniteHiddenSwap coalition S parts hmem p).1 ⟨seedGenNamedInput parts name, hmem name⟩
        else (seedGenFiniteHiddenSwap coalition S parts hmem p).2 name) = p.2 name
      rw [if_pos hh, seedGenFiniteHiddenSwap_cell coalition S parts hmem hinj p name hh]
    · rw [seedGenFiniteHiddenSwap_dealer_known coalition S parts hmem _ name hh,
        seedGenFiniteHiddenSwap_dealer_known coalition S parts hmem _ name hh]

/-- The complete joint law of the eager oracle and independent dealer is preserved. -/
theorem evalDist_seedGenFiniteHiddenSwap (coalition : C.Coalition) (S : Finset (Query C))
    (parts : C.Party → Parts C) (hmem : ∀ name, seedGenNamedInput parts name ∈ S)
    (hinj : Function.Injective (seedGenNamedInput parts)) :
    (seedGenFiniteHiddenSwap coalition S parts hmem <$>
      ($ᵗ ((S → HashOutput) × (KeyName C → HashOutput)))) =ᵈ
      $ᵗ ((S → HashOutput) × (KeyName C → HashOutput)) :=
  SampleableType.map_uniformSample_evalDistEq_of_bijective
    (seedGenFiniteHiddenSwap_involutive coalition S parts hmem hinj).bijective

/-- The total oracles agree away from canonical hidden inputs, including all fixed Th calls. -/
theorem seedGenFiniteHiddenSwap_total_off (prims : Primitives) (coalition : C.Coalition)
    (S : Finset (Query C)) (parts : C.Party → Parts C)
    (hmem : ∀ name, seedGenNamedInput parts name ∈ S)
    (p : (S → HashOutput) × (KeyName C → HashOutput)) (q : Query C)
    (hq : ¬ SeedGenHiddenInput coalition parts q) :
    seedGenFiniteTotal prims S (seedGenFiniteHiddenSwap coalition S parts hmem p).1 q =
      seedGenFiniteTotal prims S p.1 q := by
  have he (hm : q ∈ S) :
      (seedGenFiniteHiddenSwap coalition S parts hmem p).1 ⟨q, hm⟩ = p.1 ⟨q, hm⟩ :=
    seedGenFiniteHiddenSwap_off coalition S parts hmem p _ hq
  cases q <;> simp only [seedGenFiniteTotal] <;> split_ifs <;> first | apply he | rfl

end ThresholdLeanXmssSecurity

namespace ThresholdLeanXmssSecurity

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

variable {C : Committee} {E : Type} (prims : Primitives)

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.seedGenCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.seedGenCompleteness
