import ThresholdLeanXmssSecurity.Proof.Execution
import ThresholdLeanXmssSecurity.Proof.Lemmas
import VCVio.EvalDist.List
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable
import Common.CostCombinators
import XmssSecurity.Proof.EvalDistEq

/-!
# The seed generation

This module holds the setup of a ceremony and the honest run of `seedGen`.
`SeedGenCompletenessStatement` follows from the honest run. `Proof/SeedGenGames.lean` holds the games
of the security proof.
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

/-- A setup of `phase` of operator `i` from its parts, with the keys of the carrier. -/
def setupWith (phase : Phase) (i : C.Party) (own : Parts C) : PartyM C E RealSpec (Keys C) :=
  commitRevealEcho phase i own >>= fun keys => pure (keysOf keys)

/-- A setup of `phase` of operator `i`. -/
def setupKeys (phase : Phase) (i : C.Party) : PartyM C E RealSpec (Keys C) :=
  localStep (liftComp sampleParts _) >>= fun own => setupWith phase i own

/-- A setup of `phase` after the commit round. -/
def setupRound1 (phase : Phase) (i : C.Party) (own : Parts C) : Mail C E → PartyM C E RealSpec (Keys C) :=
  fun committed => exchange (revealOutbox phase i own) >>= fun revealed =>
    setupRest phase i own committed revealed >>= fun keys => pure (keysOf keys)

/-- The step of operator `i` after the start of its setup. -/
def setupStart (phase : Phase) (i : C.Party) (own : Parts C) (commitments : List HashOutput) :
    Step C E RealSpec (Keys C) :=
  .wait (commitOutbox i commitments) (exchangeResume (setupRound1 phase i own))

theorem advance_setupWith (phase : Phase) (i : C.Party) (parts : Parts C) :
    advance (setupWith phase i parts : PartyM C E RealSpec (Keys C)).run =
      liftComp (commitQueries phase i parts) (LocalSpec C) >>= fun commitments =>
        pure (setupStart phase i parts commitments) := by
  unfold setupWith
  rw [advance_setup_start]
  rfl

theorem advance_seedGen (i : C.Party) :
    advance (seedGen i : PartyM C E RealSpec (Keys C)).run =
      liftComp sampleParts (LocalSpec C) >>= fun own =>
        liftComp (commitQueries .seedGen i own) (LocalSpec C) >>= fun commitments =>
          pure (setupStart .seedGen i own commitments) := by
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
  honestRounds noFunctionality (fun l => l.elim) setupRounds fun j => setupStart (E := E) .seedGen j (parts j) (commitments j)

/-- The honest seed generation samples all parts first. -/
theorem sameRun_seedGen :
    SameRun prims (honestStart (fun i => (seedGen i : PartyM C E RealSpec (Keys C))) >>=
        honestRounds noFunctionality (fun l => l.elim) setupRounds)
      (OverPermutation.sequenceFin (fun _ => liftComp sampleParts (LocalSpec C)) >>= seedGenRest (E := E)) := by
  unfold honestStart seedGenRest
  simp only [advance_seedGen]
  refine (sameRun_sequenceFin_dep prims _ _ (fun j own commitments => setupStart (E := E) .seedGen j own commitments)).bind
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
  have h1 : ∀ j, advance (exchangeResume (setupRound1 (E := E) .seedGen j (parts j)) fun k => commitOutbox k (D prims h (commitQueries .seedGen k (parts k))) j) =
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
  unfold setupStart
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

variable {C : Committee} {E : Type} (prims : Primitives)

theorem costLe_simulateQ_leak {σ L R : Type}
    (impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT σ (OracleComp (WorldSpec C)))) (l : L) (st : σ) {n : ℕ}
    (h : CostLe prims ((impl (.inr l)).run st) n) :
    CostLe prims ((simulateQ impl (leak (C := C) (R := R) l)).run st) n := by
  unfold leak
  erw [simulateQ_query]
  simpa using h

theorem seedGen_liftComp_mapM {α β : Type} (f : α → OracleComp (RoSpec C) β) (l : List α) :
    liftComp (l.mapM f) (LocalSpec C) = l.mapM (fun a => liftComp (f a) (LocalSpec C)) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.mapM_cons, liftComp_bind, liftComp_pure, ih]

/-- Marginalization remains valid for a randomized continuation, not just a deterministic map. -/
theorem seedGenUniform_update_bind {Ω α : Type} [Finite Ω] [DecidableEq Ω]
    [SampleableType (Ω → HashOutput)] (q : Ω) (k : (Ω → HashOutput) → ProbComp α) :
    (do let y ← $ᵗ HashOutput; let h ← $ᵗ (Ω → HashOutput); k (Function.update h q y)) =ᵈ
      (do let h ← $ᵗ (Ω → HashOutput); k h) := by
  exact evalDistEq_uniformSample_bind_update (R := HashOutput) q k

end ThresholdLeanXmssSecurity

/-- info: 'ThresholdLeanXmssSecurity.seedGenCompleteness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.seedGenCompleteness
