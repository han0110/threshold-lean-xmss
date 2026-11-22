import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Cost
import ThresholdLeanXmssSecurity.Proof.Tree

/-!
# The forwarded calls of an emulated operator

An emulated honest operator of `dkgReduction` forwards to `tsigGame` each call of `H` outside the
setup domains. This file bounds these calls on each path of its programs.

* `PartyCost p n` says that the operator program `p` forwards at most `n` calls. `StateCost` is the
  same for a program on a state.
* The setups, the PRSS randomness, the reshares, the check and `OpenRep` forward no call
  (`commitRevealEcho_cost`, `check_cost`, `openRep_cost`).
* The input sharings of a job and its output in the clear forward one call for each term and each
  point (`inputShares_cost`, `runJobs_cost`), so a ceremony forwards two calls for each term and each
  point of its jobs (`ceremonyRun_cost`).
* The local steps of a tree forward the hashes of the roots, of the path and of the top signature
  (`merkleNode_cost`, `merklePath_cost`, `layerRoot_cost`).
* `emulatedProgram_cost` bounds the program of one operator in one run of a tree by
  `operatorCalls C tree`.
-/

set_option autoImplicit false

open OracleComp OracleSpec ThresholdLeanXmss HashSig LeanXmss
open PFunctor.FreeM (costWith cost costWith_mono costWith_le_cost_add)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The forwarded calls of the programs -/

section Programs

variable {E : Type}

/-- The charge of a call of `H` or `PRG`, a call of `H` outside the setup domains. -/
abbrev roCharge (t : (RoSpec C).Domain) : ℕ∞ := honestCost (.inr t)

/-- A computation of `H` and `PRG` forwards no call. -/
def RoFree {α : Type} (oa : OracleComp (RoSpec C) α) : Prop := cost roCharge oa ≤ 0

theorem roFree_pure {α : Type} (a : α) : RoFree (pure a : OracleComp (RoSpec C) α) := cost_pure_le _ _ _

theorem roFree_bind {α β : Type} {oa : OracleComp (RoSpec C) α} {f : α → OracleComp (RoSpec C) β}
    (h : RoFree oa) (hf : ∀ a, RoFree (f a)) : RoFree (oa >>= f) :=
  (cost_bind_le_add h hf).trans (le_of_eq (add_zero 0))

theorem roFree_map {α β : Type} {oa : OracleComp (RoSpec C) α} (f : α → β) (h : RoFree oa) : RoFree (f <$> oa) :=
  cost_map_le f h

theorem roFree_mapM {α β : Type} (f : α → OracleComp (RoSpec C) β) (hf : ∀ a, RoFree (f a)) (xs : List α) :
    RoFree (xs.mapM f) :=
  (cost_mapM_le f (fun _ => 0) hf xs).trans (by simp)

theorem roFree_hashQuery (q : Query C) (hq : isSetupQuery q = true) : RoFree (hashQuery q) :=
  (cost_query_le _).trans (by simp [honestCost, hq])

/-- A local computation forwards at most the calls of `honestCost` as a computation of an operator. -/
theorem cost_liftComp_party {α : Type} (oa : OracleComp (LocalSpec C) α) :
    cost (partyCharge (E := E)) (liftComp oa (PartySpec C E RealSpec)) ≤ cost (fun t => (honestCost t : ℕ∞)) oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact le_rfl
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (PartySpec C E RealSpec) =
        (liftM ((PartySpec C E RealSpec).query (.inl (.inl t))) : OracleComp (PartySpec C E RealSpec) _) >>=
          fun u => liftComp (k u) (PartySpec C E RealSpec) := by
      rw [liftComp_bind]
      rcases t with _ | _ | _ <;> rfl
    rw [e, cost, cost, costWith_query_bind, costWith_query_bind]
    exact add_le_add le_rfl (iSup_mono ih)

theorem cost_liftComp_ro {α : Type} (oa : OracleComp (RoSpec C) α) :
    cost (fun t => (honestCost t : ℕ∞)) (liftComp oa (LocalSpec C)) ≤ cost roCharge oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact le_rfl
  | query_bind t k ih =>
    have e : liftComp (liftM (OracleSpec.query t) >>= k) (LocalSpec C) =
        (liftM ((LocalSpec C).query (.inr t)) : OracleComp (LocalSpec C) _) >>= fun u => liftComp (k u) (LocalSpec C) := by
      rw [liftComp_bind]
      rfl
    rw [e, cost, cost, costWith_query_bind, costWith_query_bind]
    exact add_le_add le_rfl (iSup_mono ih)

/-- An operator program forwards at most `n` calls on each path. -/
def PartyCost {α : Type} (p : PartyM C E RealSpec α) (n : ℕ∞) : Prop := cost (partyCharge (E := E)) p.run ≤ n

/-- A program on a state forwards at most `n` calls from each state. -/
def StateCost {σ α : Type} (p : StateT σ (PartyM C E RealSpec) α) (n : ℕ∞) : Prop := ∀ s, PartyCost (p.run s) n

namespace PartyCost

variable {α β : Type}

theorem mono {p : PartyM C E RealSpec α} {n m : ℕ∞} (h : PartyCost p n) (hnm : n ≤ m) : PartyCost p m :=
  le_trans h hnm

theorem pure (a : α) (n : ℕ∞) : PartyCost (Pure.pure a : PartyM C E RealSpec α) n := cost_pure_le _ _ _

theorem failure (n : ℕ∞) : PartyCost (failure : PartyM C E RealSpec α) n := cost_pure_le _ _ _

theorem bind {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β} {n m : ℕ∞} (h : PartyCost p n)
    (hf : ∀ a, PartyCost (f a) m) : PartyCost (p >>= f) (n + m) := by
  unfold PartyCost
  rw [OptionT.run_bind]
  refine cost_bind_le_add h fun o => ?_
  cases o with
  | none => exact cost_pure_le _ _ _
  | some a => exact hf a

theorem bind_zero {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β} {m : ℕ∞} (h : PartyCost p 0)
    (hf : ∀ a, PartyCost (f a) m) : PartyCost (p >>= f) m := by
  simpa using bind h hf

theorem localStep {oa : OracleComp (LocalSpec C) α} {n : ℕ∞} (h : cost (fun t => (honestCost t : ℕ∞)) oa ≤ n) :
    PartyCost (ThresholdLeanXmss.localStep oa : PartyM C E RealSpec α) n := by
  unfold PartyCost ThresholdLeanXmss.localStep
  change cost _ (liftComp oa (PartySpec C E RealSpec) >>= fun a => Pure.pure (some a)) ≤ n
  exact (cost_bind_le_add (m := 0) ((cost_liftComp_party oa).trans h) fun a => cost_pure_le _ (some a) 0).trans
    (le_of_eq (add_zero n))

theorem oracleStep {oa : OracleComp (RoSpec C) α} {n : ℕ∞} (h : cost roCharge oa ≤ n) :
    PartyCost (ThresholdLeanXmss.oracleStep oa : PartyM C E RealSpec α) n :=
  localStep ((cost_liftComp_ro oa).trans h)

theorem require (P : Prop) : PartyCost (ThresholdLeanXmss.require P : PartyM C E RealSpec Unit) 0 := by
  unfold ThresholdLeanXmss.require
  split_ifs
  · exact pure _ _
  · exact failure _

theorem exchange (outbox : Mail C E) : PartyCost (ThresholdLeanXmss.exchange outbox : PartyM C E RealSpec _) 0 := by
  unfold ThresholdLeanXmss.exchange PartyCost
  rw [OptionT.run_bind, OptionT.run_lift]
  refine (cost_bind_le_add (n := 0) (m := 0) ?_ fun o => ?_).trans (by simp)
  · refine (cost_bind_le_add (m := 0) (cost_query_le _) fun _ => cost_pure_le _ _ _).trans (by simp [partyCost])
  · rcases o with _ | inbox
    · exact cost_pure_le _ _ _
    · dsimp only [Option.elim]
      split_ifs <;> exact cost_pure_le _ _ _

theorem mapM (f : α → PartyM C E RealSpec β) (n : α → ℕ∞) (hf : ∀ a, PartyCost (f a) (n a)) :
    ∀ xs : List α, PartyCost (xs.mapM f) (xs.map n).sum
  | [] => pure _ _
  | a :: xs => by
    rw [List.mapM_cons, List.map_cons, List.sum_cons]
    exact (bind (hf a) fun b => (bind (mapM f n hf xs) fun bs => pure (b :: bs) 0)).mono (by simp)

end PartyCost

namespace StateCost

variable {σ α β : Type}

theorem mono {p : StateT σ (PartyM C E RealSpec) α} {n m : ℕ∞} (h : StateCost p n) (hnm : n ≤ m) :
    StateCost p m := fun s => (h s).mono hnm

theorem pure (a : α) (n : ℕ∞) : StateCost (Pure.pure a : StateT σ (PartyM C E RealSpec) α) n :=
  fun _ => PartyCost.pure _ _

theorem bind {p : StateT σ (PartyM C E RealSpec) α} {f : α → StateT σ (PartyM C E RealSpec) β} {n m : ℕ∞}
    (h : StateCost p n) (hf : ∀ a, StateCost (f a) m) : StateCost (p >>= f) (n + m) := fun s =>
  PartyCost.bind (h s) fun a => hf a.1 a.2

theorem bind_zero {p : StateT σ (PartyM C E RealSpec) α} {f : α → StateT σ (PartyM C E RealSpec) β} {m : ℕ∞}
    (h : StateCost p 0) (hf : ∀ a, StateCost (f a) m) : StateCost (p >>= f) m := by
  simpa using bind h hf

theorem bind_zero' {p : StateT σ (PartyM C E RealSpec) α} {f : α → StateT σ (PartyM C E RealSpec) β} {n : ℕ∞}
    (h : StateCost p n) (hf : ∀ a, StateCost (f a) 0) : StateCost (p >>= f) n := by
  simpa using bind h hf

theorem lift {p : PartyM C E RealSpec α} {n : ℕ∞} (h : PartyCost p n) :
    StateCost (StateT.lift p : StateT σ (PartyM C E RealSpec) α) n := fun s => by
  change PartyCost (p >>= fun a => Pure.pure (a, s)) n
  simpa using PartyCost.bind h fun a => PartyCost.pure (a, s) 0

theorem get : StateCost (MonadState.get : StateT σ (PartyM C E RealSpec) σ) 0 := fun _ => PartyCost.pure _ _

theorem set (s : σ) : StateCost (MonadState.set s : StateT σ (PartyM C E RealSpec) PUnit) 0 :=
  fun _ => PartyCost.pure _ _

theorem modify (f : σ → σ) : StateCost (modify f : StateT σ (PartyM C E RealSpec) PUnit) 0 :=
  fun _ => PartyCost.pure _ _

theorem modifyGet (f : σ → α × σ) : StateCost (MonadState.modifyGet f : StateT σ (PartyM C E RealSpec) α) 0 :=
  fun _ => PartyCost.pure _ _

theorem foldlM_zero {γ : Type} (f : α → γ → StateT σ (PartyM C E RealSpec) α) (hf : ∀ a g, StateCost (f a g) 0) :
    ∀ (xs : List γ) (a : α), StateCost (xs.foldlM f a) 0
  | [], a => pure _ _
  | g :: xs, a => by
    rw [List.foldlM_cons]
    exact bind_zero (hf a g) fun a' => foldlM_zero f hf xs a'

theorem mapM (f : α → StateT σ (PartyM C E RealSpec) β) (n : α → ℕ∞) (hf : ∀ a, StateCost (f a) (n a)) :
    ∀ xs : List α, StateCost (xs.mapM f) (xs.map n).sum
  | [] => pure _ _
  | a :: xs => by
    rw [List.mapM_cons, List.map_cons, List.sum_cons]
    exact (bind (hf a) fun b => (bind (mapM f n hf xs) fun bs => pure (b :: bs) 0)).mono (by simp)

end StateCost

end Programs

/-! ## The setups and the building blocks forward no call -/

section Blocks

variable {E : Type}

theorem roFree_deriveKeys (phase : Phase) (i : C.Party) (view : C.Party → Parts C) :
    RoFree (deriveKeys phase i view) := by
  unfold deriveKeys
  split_ifs <;> refine roFree_bind ?_ fun _ => roFree_bind (roFree_mapM _ (fun T => ?_) _) fun _ =>
    roFree_bind (roFree_mapM _ (fun j => ?_) _) fun _ => roFree_pure _
  all_goals first
    | exact roFree_pure _
    | exact roFree_hashQuery _ rfl
    | (split_ifs
       · exact roFree_hashQuery _ rfl
       · exact roFree_pure _)
    | (split
       · exact roFree_pure _
       · exact roFree_hashQuery _ rfl)

/-- A setup with commit, reveal and echo forwards no call. -/
theorem commitRevealEcho_cost (phase : Phase) (i : C.Party) (own : Parts C) :
    PartyCost (commitRevealEcho phase i own : PartyM C E RealSpec _) 0 := by
  unfold commitRevealEcho
  refine PartyCost.bind_zero (PartyCost.oracleStep (roFree_mapM _ (fun j => roFree_hashQuery _ rfl) _)) fun _ => ?_
  refine PartyCost.bind_zero (PartyCost.exchange _) fun _ => ?_
  refine PartyCost.bind_zero (PartyCost.exchange _) fun _ => ?_
  refine PartyCost.bind_zero (PartyCost.oracleStep (roFree_mapM _ (fun j => roFree_hashQuery _ rfl) _)) fun _ => ?_
  refine PartyCost.bind_zero (PartyCost.require _) fun _ => ?_
  refine PartyCost.bind_zero (PartyCost.oracleStep (roFree_deriveKeys _ _ _)) fun _ => ?_
  refine PartyCost.bind_zero (PartyCost.oracleStep (roFree_mapM _ (fun j => roFree_hashQuery _ rfl) _)) fun _ => ?_
  refine PartyCost.bind_zero (PartyCost.exchange _) fun _ => ?_
  exact PartyCost.bind_zero (PartyCost.require _) fun _ => PartyCost.pure _ _

theorem seedGenWith_cost (i : C.Party) (parts : Parts C) :
    PartyCost (seedGenWith i parts : PartyM C E RealSpec (Keys C)) 0 := by
  unfold seedGenWith
  exact PartyCost.bind_zero (commitRevealEcho_cost _ _ _) fun _ => PartyCost.pure _ _

theorem prssSetup_cost (i : C.Party) : PartyCost (prssSetup i : PartyM C E RealSpec _) 0 := by
  unfold prssSetup prssSetupWith
  exact PartyCost.bind_zero (PartyCost.localStep (cost_liftComp_local _)) fun _ =>
    PartyCost.bind_zero (commitRevealEcho_cost _ _ _) fun _ => PartyCost.pure _ _

theorem roFree_prgBits (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    RoFree (prgBits name key ρ idx count) := by
  unfold prgBits
  exact roFree_bind (roFree_mapM _ (fun position =>
    (cost_query_le (spec := RoSpec C) (.inr (name, key, ρ, idx, position))).trans (by simp [honestCost])) _) fun _ =>
    roFree_pure _

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C)

omit [Field E] [Algebra Bit E] in
theorem prssRandomness_cost {R : Type} [Zero R] (codec : Codec C E R)
    (hdraw : ∀ name key ρ idx count, RoFree (codec.draw name key ρ idx count)) (idx count : ℕ) :
    StateCost (prssRandomness ctx codec idx count : RunM C E RealSpec _) 0 := by
  unfold prssRandomness freshLabel
  refine StateCost.bind_zero (StateCost.modifyGet _) fun ρ => ?_
  refine StateCost.bind_zero (StateCost.lift (PartyCost.oracleStep (roFree_mapM _ (fun T => ?_) _))) fun _ => ?_
  · split_ifs
    · exact hdraw _ _ _ _ _
    · exact roFree_pure _
  refine StateCost.bind_zero (StateCost.lift (PartyCost.oracleStep (roFree_mapM _ (fun j => ?_) _))) fun _ =>
    StateCost.pure _ _
  split
  · exact roFree_pure _
  · exact hdraw _ _ _ _ _

omit [Field E] [Algebra Bit E] in
theorem roFree_bitCodec (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    RoFree ((bitCodec (C := C) (E := E)).draw name key ρ idx count) :=
  roFree_prgBits name key ρ idx count

theorem roFree_elementCodec (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    RoFree ((elementCodec K).draw name key ρ idx count) :=
  roFree_bind (roFree_prgBits _ _ _ _ _) fun _ => roFree_pure _

theorem reshare_cost {R : Type} [Field R] (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R)
    (count : ℕ) : StateCost (reshare K ctx codec randomness v count : RunM C E RealSpec _) 0 := by
  rcases randomness with ⟨r, Z⟩
  unfold reshare
  exact StateCost.bind_zero (StateCost.lift (PartyCost.exchange _)) fun _ =>
    StateCost.bind_zero (StateCost.modify _) fun _ => StateCost.pure _ _

theorem reshareCollector_cost (randomness : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    StateCost (reshareCollector K ctx randomness v count : RunM C E RealSpec _) 0 := by
  rcases randomness with ⟨r, Z⟩
  unfold reshareCollector
  exact StateCost.bind_zero (StateCost.lift (PartyCost.exchange _)) fun _ =>
    StateCost.bind_zero (StateCost.lift (PartyCost.exchange _)) fun _ =>
      StateCost.bind_zero (StateCost.modify _) fun _ => StateCost.pure _ _

theorem openSh_cost (v : ℕ → E) (count : ℕ) : PartyCost (openSh K ctx v count : PartyM C E RealSpec _) 0 :=
  PartyCost.bind_zero (PartyCost.exchange _) fun _ =>
    PartyCost.bind_zero (PartyCost.require _) fun _ => PartyCost.pure _ _

theorem roFree_findChallenge (key : HashOutput) : ∀ tries index, RoFree (findChallenge K key tries index) := by
  intro tries
  induction tries with
  | zero => intro index; exact roFree_pure _
  | succ tries ih =>
    intro index
    unfold findChallenge
    refine roFree_bind (roFree_hashQuery _ rfl) fun r => ?_
    dsimp only
    generalize Classical.propDecidable (elementOfHash K r ≠ 0 ∧ elementOfHash K r ≠ 1) = d
    rcases d with ⟨_ | _, _⟩
    · exact ih _
    · exact roFree_pure _

theorem coin_cost (count : ℕ) :
    StateCost ((realCheckBuildingBlocks K ctx).coin count : RunM C E RealSpec _) 0 := by
  unfold realCheckBuildingBlocks coinWith
  exact StateCost.bind_zero (prssRandomness_cost ctx _ (roFree_elementCodec K) _ _) fun _ =>
    StateCost.bind_zero (StateCost.lift (openSh_cost K ctx _ _)) fun _ => StateCost.pure _ _

theorem extendMult_cost (products : List (Product C E)) :
    StateCost ((realCheckBuildingBlocks K ctx).extendMult products : RunM C E RealSpec _) 0 := by
  unfold realCheckBuildingBlocks
  exact StateCost.bind_zero (prssRandomness_cost ctx _ (roFree_elementCodec K) _ _) fun _ =>
    reshare_cost K ctx _ _ _ _

theorem coinKey_cost : StateCost (coinKey K (realCheckBuildingBlocks K ctx) : RunM C E RealSpec _) 0 := by
  unfold coinKey
  exact StateCost.bind_zero StateCost.get fun _ => StateCost.bind_zero (coin_cost K ctx 2) fun _ =>
    StateCost.lift (PartyCost.oracleStep (roFree_hashQuery _ rfl))

theorem challenge_cost : StateCost (challenge K (realCheckBuildingBlocks K ctx) : RunM C E RealSpec _) 0 := by
  unfold challenge
  refine StateCost.bind_zero (coinKey_cost K ctx) fun key => ?_
  refine StateCost.bind_zero (StateCost.lift (PartyCost.oracleStep (roFree_findChallenge K key _ _))) fun r => ?_
  split
  · exact StateCost.pure _ _
  · exact StateCost.lift (PartyCost.failure _)

theorem expand_cost (key : HashOutput) (count : ℕ) : StateCost (expand K key count : RunM C E RealSpec _) 0 := by
  unfold expand
  exact StateCost.lift (PartyCost.oracleStep (roFree_mapM _ (fun _ => roFree_map _ (roFree_hashQuery _ rfl)) _))

omit [Field E] [Algebra Bit E] in
theorem compareDigests_cost (salts : Shares C Bit) :
    StateCost (compareDigests ctx salts : RunM C E RealSpec Unit) 0 := by
  unfold compareDigests
  refine StateCost.bind_zero StateCost.get fun st => ?_
  refine StateCost.bind_zero (StateCost.lift (PartyCost.oracleStep (roFree_mapM _ (fun T => ?_) _))) fun _ => ?_
  · split_ifs
    · exact roFree_bind (roFree_hashQuery _ rfl) fun _ => roFree_hashQuery _ rfl
    · exact roFree_pure _
  · exact StateCost.bind_zero (StateCost.lift (PartyCost.exchange _)) fun _ => StateCost.lift (PartyCost.require _)

theorem openRep_cost (v : Shares C Bit) (count : ℕ) : PartyCost (openRep K ctx v count : PartyM C E RealSpec _) 0 := by
  unfold openRep
  exact PartyCost.bind_zero (PartyCost.oracleStep (roFree_mapM _ (fun T => roFree_hashQuery _ rfl) _)) fun _ =>
    PartyCost.bind_zero (PartyCost.exchange _) fun _ =>
      PartyCost.bind_zero (PartyCost.oracleStep (roFree_mapM _ (fun T => roFree_hashQuery _ rfl) _)) fun _ =>
        PartyCost.bind_zero (PartyCost.require _) fun _ => PartyCost.pure _ _

/-- The real check forwards no call. -/
theorem check_cost (tuples : List (Tuple C)) :
    StateCost (check K ctx (realCheckBuildingBlocks K ctx) tuples : RunM C E RealSpec Unit) 0 := by
  unfold check
  dsimp only
  split_ifs with hz
  · exact StateCost.pure _ _
  refine StateCost.bind_zero (coinKey_cost K ctx) fun key => ?_
  refine StateCost.bind_zero (expand_cost K key _) fun τ => ?_
  refine StateCost.bind_zero (StateCost.lift (PartyCost.require _)) fun _ => ?_
  refine StateCost.bind_zero (StateCost.foldlM_zero _ (fun v j => ?_) _ _) fun v => ?_
  · rcases v with ⟨xs, ys, D⟩
    exact StateCost.bind_zero (extendMult_cost K ctx _) fun _ =>
      StateCost.bind_zero (challenge_cost K ctx) fun _ => StateCost.pure _ _
  rcases v with ⟨xs, ys, D⟩
  refine StateCost.bind_zero (StateCost.foldlM_zero _ (fun v j => ?_) _ _) fun v => ?_
  · rcases v with ⟨A, B, D⟩
    exact StateCost.bind_zero (extendMult_cost K ctx _) fun _ =>
      StateCost.bind_zero (challenge_cost K ctx) fun _ => StateCost.pure _ _
  rcases v with ⟨A, B, D⟩
  refine StateCost.bind_zero (prssRandomness_cost ctx _ (roFree_elementCodec K) _ _) fun w => ?_
  refine StateCost.bind_zero (extendMult_cost K ctx _) fun q => ?_
  refine StateCost.bind_zero (prssRandomness_cost ctx _ roFree_bitCodec _ _) fun salts => ?_
  refine StateCost.bind_zero (compareDigests_cost ctx _) fun _ => ?_
  exact StateCost.bind_zero (challenge_cost K ctx) fun _ =>
    StateCost.bind_zero (StateCost.lift (openSh_cost K ctx _ _)) fun _ => StateCost.lift (PartyCost.require _)

theorem mult_cost (mode : ReshareMode) (x y : Shares C Bit) (count : ℕ) :
    StateCost ((realRunBuildingBlocks K ctx mode).mult x y count : RunM C E RealSpec _) 0 := by
  unfold realRunBuildingBlocks reshareWith
  refine StateCost.bind_zero (prssRandomness_cost ctx _ roFree_bitCodec _ _) fun r => ?_
  cases mode
  · exact reshare_cost K ctx _ _ _ _
  · exact reshareCollector_cost K ctx _ _ _

theorem rerand_cost (mode : ReshareMode) (v : Shares C Bit) (count : ℕ) :
    StateCost ((realRunBuildingBlocks K ctx mode).rerand v count : RunM C E RealSpec _) 0 := by
  unfold realRunBuildingBlocks
  exact StateCost.bind_zero (prssRandomness_cost ctx _ roFree_bitCodec _ _) fun _ => reshare_cost K ctx _ _ _ _

end Blocks

/-! ## The hashes of the local steps -/

section Hashes

/-- One unit for each call of `Th`. -/
abbrev hashCharge (_ : HashInput) : ℕ∞ := 1

/-- A call of `Th` through `tweakable` is one forwarded call. -/
theorem cost_tweakable {α : Type} (oa : OracleComp HashSpec α) :
    cost roCharge (tweakable (C := C) oa) ≤ cost hashCharge oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact le_rfl
  | query_bind t f ih =>
    unfold tweakable at ih ⊢
    rw [simulateQ_query_bind]
    change cost roCharge (hashQuery (.hash t) >>= fun u => _root_.simulateQ _ (f u)) ≤
      costWith hashCharge (liftM (HashSpec.query t) >>= f) (fun _ => 0)
    rw [costWith_query_bind]
    exact cost_bind_le_add ((cost_query_le _).trans (by simp [honestCost, isSetupQuery]))
      fun u => (ih u).trans (le_iSup (fun u => cost hashCharge (f u)) u)

variable (P : PublicParameter)

theorem tweakableHash_cost (domain : HashDomain) (payload : HashInput) :
    cost hashCharge (Verification.tweakableHashWithHash P domain payload : OracleComp HashSpec Digest) ≤ 1 := by
  unfold Verification.tweakableHashWithHash Verification.thWithHash Verification.oracleHashWithHash
  exact (cost_bind_le_add (m := 0) (cost_query_le _) fun _ => cost_pure_le _ _ _).trans (by simp)

theorem walkChain_cost {S : ℕ} (step : Fin S → Digest → OracleComp HashSpec Digest)
    (h : ∀ i v, cost hashCharge (step i v) ≤ 1) :
    ∀ start steps v, cost hashCharge (HashSig.OverPermutation.walkChain step start steps v) ≤ steps
  | _, 0, v => cost_pure_le _ _ _
  | start, steps + 1, v => by
    rw [HashSig.OverPermutation.walkChain]
    refine (cost_bind_le_add (walkChain_cost step h start steps v) fun _ => ?_).trans (by push_cast; rfl)
    split
    · exact h _ _
    · exact cost_pure_le _ _ _

theorem foldPath_cost (node : ℕ → ℕ → HashInput → OracleComp HashSpec Digest)
    (h : ∀ l j payload, cost hashCharge (node l j payload) ≤ 1) (leafIndex : ℕ) (sibling : ℕ → Digest) :
    ∀ levels v, cost hashCharge (HashSig.OverPermutation.foldPath node leafIndex sibling levels v) ≤ levels
  | 0, v => cost_pure_le _ _ _
  | l + 1, v => by
    rw [HashSig.OverPermutation.foldPath]
    exact (cost_bind_le_add (foldPath_cost node h leafIndex sibling l v) fun _ => h _ _ _).trans (by push_cast; rfl)

theorem merkleNode_cost (lay : Layer) (ends : KeyIndex → ChainIndex → Digest) :
    ∀ level idx, cost hashCharge (merkleNode P lay ends level idx) ≤ ((2 ^ (level + 1) - 1 : ℕ) : ℕ∞)
  | 0, idx => by
    rw [merkleNode]
    exact (tweakableHash_cost P _ _).trans (by norm_num)
  | level + 1, idx => by
    rw [merkleNode]
    refine (cost_bind_le_add (merkleNode_cost lay ends level _) fun _ =>
      cost_bind_le_add (merkleNode_cost lay ends level _) fun _ => tweakableHash_cost P _ _).trans (le_of_eq ?_)
    have h1 : 1 ≤ 2 ^ (level + 1) := Nat.one_le_two_pow
    norm_cast
    rw [pow_succ 2 (level + 1)]
    omega

theorem sum_pow_sub (h : ℕ) : ∑ l : Fin h, (2 ^ (l.val + 1) - 1) = 2 ^ (h + 1) - h - 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun l => 2 ^ (l + 1) - 1)]
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : h + 2 ≤ 2 ^ (h + 1) := Nat.lt_two_pow_self
    have h2 : 1 ≤ 2 ^ (h + 1) := Nat.one_le_two_pow
    rw [pow_succ 2 (h + 1)]
    omega

theorem merklePath_cost (lay : Layer) (ends : KeyIndex → ChainIndex → Digest) (key : KeyIndex) :
    cost hashCharge (merklePath P lay ends key) ≤ ((2 ^ (layerHeight + 1) - layerHeight - 2 : ℕ) : ℕ∞) := by
  unfold merklePath
  refine (cost_sequenceFin_sum _ (fun l => ((2 ^ (l.val + 1) - 1 : ℕ) : ℕ∞))
    fun l => merkleNode_cost P lay ends _ _).trans (le_of_eq ?_)
  rw [← sum_pow_sub]
  push_cast
  rfl

theorem layerRoot_cost (lay : Layer) (key : KeyIndex) (message : HashInput) (part : LayerSignature) :
    cost hashCharge (Verification.layerRootWithHash P lay key message part : OracleComp HashSpec (Option Digest)) ≤
      ((2 + 3 * chainCount + layerHeight : ℕ) : ℕ∞) := by
  unfold Verification.layerRootWithHash Verification.otsLeafWithHash
  refine (cost_bind_le_add (n := ((2 + 3 * chainCount : ℕ) : ℕ∞)) (m := (layerHeight : ℕ∞))
    ((cost_bind_le_add (n := 1) (m := ((3 * chainCount + 1 : ℕ) : ℕ∞)) (tweakableHash_cost P _ _)
      fun digest => ?_).trans (le_of_eq ?_)) fun leaf => ?_).trans (le_of_eq ?_)
  · cases Codeword.decode digest with
    | none => exact cost_pure_le _ _ _
    | some encoding =>
      dsimp only
      refine (cost_bind_le_add (cost_sequenceFin_sum _ (fun _ => (3 : ℕ∞)) fun l => ?_) fun _ =>
        cost_bind_le_add (m := 0) (tweakableHash_cost P _ _) fun _ => cost_pure_le _ _ 0).trans (le_of_eq ?_)
      · unfold Verification.recoverChainWithHash Verification.chainWalkWithHash
        refine (walkChain_cost _ (fun _ _ => tweakableHash_cost P _ _) _ _ _).trans ?_
        norm_cast
        simp only [chainLength, winternitzBits]
        omega
      · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, add_zero]
        push_cast
        ring
  · push_cast
    ring
  · cases leaf with
    | none => exact cost_pure_le _ _ _
    | some leaf =>
      exact (cost_bind_le_add (m := 0) (foldPath_cost _ (fun _ _ _ => tweakableHash_cost P _ _) _ _ _ _)
        fun _ => cost_pure_le _ _ 0).trans (le_of_eq (add_zero _))
  · push_cast
    ring

end Hashes

/-! ## The forwarded calls of a ceremony -/

section Ceremony

theorem cost_flatMapM_le {ι α β : Type} {spec : OracleSpec.{0, 0} ι} {c : ι → ℕ∞} (f : α → OracleComp spec (List β))
    (n : ℕ∞) (hf : ∀ a, cost c (f a) ≤ n) : ∀ xs : List α, cost c (xs.flatMapM f) ≤ xs.length * n
  | [] => cost_pure_le c _ _
  | a :: xs => by
    rw [List.flatMapM_cons]
    refine (cost_bind_le_add (hf a) fun _ => cost_bind_le_add (cost_flatMapM_le f n hf xs) fun _ =>
      cost_pure_le c _ 0).trans (le_of_eq ?_)
    simp only [List.length_cons]
    push_cast
    ring

theorem cost_prf (seed : HashOutput) (x : Point) : cost roCharge (prf (C := C) seed x) ≤ 1 :=
  cost_map_le _ ((cost_query_le _).trans (by simp [honestCost, isSetupQuery]))

theorem cost_prfValue (seeds : C.Term → HashOutput) (x : Point) :
    cost roCharge (prfValue seeds x) ≤ C.terms.length := by
  unfold prfValue
  refine (cost_bind_le_add (m := 0) (cost_mapM_le _ (fun _ => 1) (fun T => cost_prf _ _) _) fun _ =>
    cost_pure_le _ _ _).trans (le_of_eq ?_)
  simp

theorem cost_evalJob (circuits : Circuits) (parameter : PublicParameter) (seeds : C.Term → HashOutput) (job : Job) :
    cost roCharge (evalJob circuits parameter seeds job) ≤ (job.points.length : ℕ∞) * C.terms.length := by
  unfold evalJob
  refine (cost_bind_le_add (m := 0) (cost_mapM_le _ (fun _ => (C.terms.length : ℕ∞))
    (fun x => cost_prfValue _ _) _) fun _ => cost_pure_le _ _ _).trans (le_of_eq ?_)
  simp

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (D : C.Coalition)

omit [Field E] [Algebra Bit E] in
theorem inputShares_cost (ctx : Context C) (job : Job) :
    PartyCost (inputShares ctx job : PartyM C E RealSpec _) ((job.points.length : ℕ∞) * C.terms.length) := by
  unfold inputShares
  refine (PartyCost.bind (m := 0) (PartyCost.oracleStep ((cost_mapM_le _ (fun _ => (job.points.length : ℕ∞))
    (fun T => ?_) _).trans (le_of_eq ?_))) fun _ => PartyCost.pure _ _).mono (le_of_eq (add_zero _))
  · split_ifs
    · exact (cost_flatMapM_le _ 1 (fun x => cost_map_le _ (cost_prf _ _)) _).trans (le_of_eq (mul_one _))
    · exact cost_pure_le _ _ _
  · simp [mul_comm]

/-- A run of a batch with the shifted building blocks forwards the calls of its outputs in the clear. -/
theorem runJobs_cost (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (ctx : Context C) (k : ℕ) (batch : List Job) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    StateCost (runJobs K (shiftedBuildingBlocks K circuits settings D parameter seeds openings ctx k batch) jobs inputs :
      RunM C E RealSpec _) (batch.map fun job => (job.points.length : ℕ∞) * C.terms.length).sum := by
  unfold runJobs shiftedBuildingBlocks
  refine StateCost.bind_zero (StateCost.foldlM_zero _ (fun v layer => ?_) _ _) fun v => ?_
  · rcases v with ⟨wires, tuples⟩
    exact StateCost.bind_zero (mult_cost K ctx settings.mode _ _ _) fun _ => StateCost.pure _ _
  rcases v with ⟨wires, tuples⟩
  dsimp only
  refine StateCost.bind_zero (rerand_cost K ctx _ _ _) fun v' => ?_
  refine StateCost.bind_zero (check_cost K ctx _) fun _ => ?_
  refine StateCost.bind_zero' ?_ fun _ => StateCost.pure _ _
  refine StateCost.bind_zero' (StateCost.lift (PartyCost.oracleStep
    ((cost_mapM_le _ _ (fun job => cost_evalJob circuits _ _ job) _)))) fun _ => ?_
  exact StateCost.lift (openRep_cost K ctx _ _)

end Ceremony

/-! ## The forwarded calls of a run of a tree -/

section Tree

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (D : C.Coalition)

/-- The forwarded calls of the jobs of a ceremony, two for each term and each point. -/
theorem jobs_sum (jobs : List Job) :
    (jobs.map fun job => (job.points.length : ℕ∞) * C.terms.length +
      (job.points.length : ℕ∞) * C.terms.length).sum =
      ((2 * termCount C * (jobs.map (·.points.length)).sum : ℕ) : ℕ∞) := by
  rw [show termCount C = C.terms.length from check_terms_length.symm]
  induction jobs with
  | nil => simp
  | cons job jobs ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]
    push_cast
    ring

theorem sum_chunks {α : Type} (f : α → ℕ∞) (hsize : 0 < settings.batchSize) (items : List α) :
    ((chunks settings.batchSize items).map fun batch => (batch.map f).sum).sum = (items.map f).sum := by
  have h : ∀ L : List (List α), (L.map fun batch => (batch.map f).sum).sum = (L.flatten.map f).sum := by
    intro L
    induction L with
    | nil => simp
    | cons l L ih => simp [ih]
  rw [h, chunks_flatten _ hsize]

/-- A ceremony with the shifted building blocks forwards two calls for each term and each point. -/
theorem ceremonyRun_cost (hsize : 0 < settings.batchSize) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (openings : List (List (List Bit))) (i : C.Party) (keys : Keys C) (jobs : List Job) :
    StateCost (ceremonyRun K circuits settings (shiftedBuildingBlocks K circuits settings D parameter seeds openings)
      i keys jobs) ((2 * termCount C * (jobs.map (·.points.length)).sum : ℕ) : ℕ∞) := by
  rw [← jobs_sum, ← sum_chunks settings _ hsize]
  unfold ceremonyRun batched
  refine StateCost.bind_zero (StateCost.lift (prssSetup_cost i)) fun prss => ?_
  refine StateCost.bind_zero' (StateCost.mapM _ _ (fun batch => ?_) _) fun _ => StateCost.pure _ _
  refine StateCost.bind_zero StateCost.get fun lk => ?_
  rcases lk with ⟨label, k⟩
  dsimp only
  rw [List.sum_map_add]
  refine StateCost.bind (StateCost.lift (PartyCost.mapM _ _ (fun job => inputShares_cost _ job) _)) fun inputs => ?_
  refine StateCost.bind_zero' (StateCost.lift (runJobs_cost K circuits settings D _ _ _ _ _ _ _ _ _)) fun r => ?_
  rcases r with ⟨outputs, state⟩
  exact StateCost.bind_zero (StateCost.set _) fun _ => StateCost.pure _ _

end Tree

/-! ## The forwarded calls of an emulated operator -/

/-- The forwarded calls of one emulated operator in one run of `tree`. -/
def operatorCalls (C : Committee) : Tree → ℕ
  | .top => 2 * termCount C * treePoints .top + 2 ^ (layerHeight + 1) - 1
  | .bottom b => 2 * termCount C * treePoints (.bottom b) + 2 ^ (layerHeight + 2) + 3 * chainCount

theorem treeReductionCalls_eq (tree : Tree) : treeReductionCalls C tree = C.n * operatorCalls C tree := by
  cases tree <;> rfl

section Operator

variable {E : Type} [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)
  (D : C.Coalition)

omit [Field E] [Algebra Bit E] in
theorem PartyCost.map {α β : Type} {p : PartyM C E RealSpec α} (f : α → β) {n : ℕ∞} (h : PartyCost p n) :
    PartyCost (f <$> p) n := by
  unfold PartyCost at h ⊢
  rw [OptionT.run_map]
  exact cost_map_le _ h

omit [Field E] [Algebra Bit E] in
theorem lift_tweakable_cost {α : Type} (oa : OracleComp HashSpec α) {n : ℕ∞} (h : cost hashCharge oa ≤ n) :
    StateCost (StateT.lift (oracleStep (tweakable oa)) : StateT (ℕ × ℕ) (PartyM C E RealSpec) α) n :=
  StateCost.lift (PartyCost.oracleStep ((cost_tweakable oa).trans h))

theorem signJobs_points (b : Fin (2 ^ layerHeight)) (encoding : Encoding) :
    ((signJobs b encoding).map (·.points.length)).sum = chainCount := by
  simp [signJobs, Function.comp_def]

variable (hsize : 0 < settings.batchSize) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
  (openings : List (List (List Bit)))

include hsize in
/-- An emulated operator in a run of the top tree forwards at most `operatorCalls C .top` calls. -/
theorem topOutput_cost (i : C.Party) (keys : Keys C) (top : TopTree) :
    StateCost (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter
      (ceremonyRun K circuits settings (shiftedBuildingBlocks K circuits settings D parameter seeds openings) i keys)
      top .top) (operatorCalls C .top) := by
  unfold ceremonyOutput
  dsimp only
  refine (StateCost.bind (m := ((2 ^ (layerHeight + 1) - 1 : ℕ) : ℕ∞))
    (ceremonyRun_cost K circuits settings D hsize parameter seeds openings i keys topJobs) fun out => ?_).mono ?_
  · rcases out with _ | outputs
    · exact StateCost.pure _ _
    · exact StateCost.bind_zero' (lift_tweakable_cost _ (merkleNode_cost _ _ _ _ _)) fun _ => StateCost.pure _ _
  · have h1 : 1 ≤ 2 ^ (layerHeight + 1) := Nat.one_le_two_pow
    have key : 2 * termCount C * (topJobs.map (·.points.length)).sum + (2 ^ (layerHeight + 1) - 1) ≤
        2 * termCount C * (topJobs.map (·.points.length)).sum + 2 ^ (layerHeight + 1) - 1 := by
      omega
    simp only [operatorCalls, treePoints]
    exact_mod_cast key

include hsize in
/-- An emulated operator in a run of bottom tree `b` forwards at most `operatorCalls C (.bottom b)`
calls. -/
theorem bottomOutput_cost (i : C.Party) (keys : Keys C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (randomizer : Randomizer) :
    StateCost (bottomOutputWith (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) keys.parameter
      (ceremonyRun K circuits settings (shiftedBuildingBlocks K circuits settings D parameter seeds openings) i keys)
      top b randomizer) (operatorCalls C (.bottom b)) := by
  unfold bottomOutputWith
  dsimp only
  have hrun := ceremonyRun_cost K circuits settings D hsize parameter seeds openings i keys
  refine (StateCost.bind (m := ((2 ^ (layerHeight + 1) - 1 : ℕ) : ℕ∞) + (1 + (((2 * termCount C * chainCount : ℕ) : ℕ∞) +
    (((2 ^ (layerHeight + 1) - layerHeight - 2 : ℕ) : ℕ∞) + ((2 + 3 * chainCount + layerHeight : ℕ) : ℕ∞)))))
    (hrun (bottomJobs b)) fun out => ?_).mono ?_
  · rcases out with _ | outputs
    · exact StateCost.pure _ _
    refine StateCost.bind (lift_tweakable_cost _ (merkleNode_cost _ _ _ _ _)) fun root => ?_
    refine StateCost.bind (lift_tweakable_cost _ (tweakableHash_cost _ _ _)) fun digest => ?_
    rcases Codeword.decode digest with _ | encoding
    · exact StateCost.pure _ _
    dsimp only
    refine StateCost.bind ((hrun (signJobs b encoding)).mono (le_of_eq (by rw [signJobs_points]))) fun values => ?_
    rcases values with _ | values
    · exact StateCost.pure _ _
    refine StateCost.bind (lift_tweakable_cost _ (merklePath_cost _ _ _ _)) fun path => ?_
    refine StateCost.bind_zero' (lift_tweakable_cost _ (layerRoot_cost _ _ _ _ _)) fun topRoot => ?_
    split_ifs <;> exact StateCost.pure _ _
  · have h1 : 2 ^ (layerHeight + 1) - layerHeight - 2 + layerHeight + 2 = 2 ^ (layerHeight + 1) := by
      have := Nat.lt_two_pow_self (n := layerHeight + 1)
      omega
    have h2 : 1 ≤ 2 ^ (layerHeight + 1) := Nat.one_le_two_pow
    have e : 2 ^ (layerHeight + 2) = 2 ^ (layerHeight + 1) * 2 := pow_succ _ _
    have key : 2 * termCount C * ((bottomJobs b).map (·.points.length)).sum + ((2 ^ (layerHeight + 1) - 1) +
        (1 + (2 * termCount C * chainCount + ((2 ^ (layerHeight + 1) - layerHeight - 2) +
          (2 + 3 * chainCount + layerHeight))))) ≤
        2 * termCount C * (((bottomJobs b).map (·.points.length)).sum + chainCount) + 2 ^ (layerHeight + 2) +
          3 * chainCount := by
      rw [e, mul_add]
      generalize 2 ^ (layerHeight + 1) = P at *
      omega
    simp only [operatorCalls, treePoints]
    exact_mod_cast key

include hsize in
/-- The program of an emulated operator in a run of `tree` forwards at most `operatorCalls C tree`
calls. -/
theorem emulatedProgram_cost (randomizer : Randomizer) (i : C.Party) (operator : OperatorState C) (tree : Tree) :
    PartyCost (emulatedProgram K circuits settings (shiftedBuildingBlocks K circuits settings D parameter seeds openings)
      randomizer i operator tree) (operatorCalls C tree) := by
  cases tree with
  | top =>
    simp only [emulatedProgram]
    split
    · unfold newTreeWith
      exact (PartyCost.bind (m := 0) (PartyCost.map _ (topOutput_cost K circuits settings D hsize parameter seeds
        openings i _ _ (0, 0))) fun out => by
          rcases out with _ | out
          · exact PartyCost.failure _
          · exact PartyCost.pure _ _).mono (le_of_eq (add_zero _))
    · exact PartyCost.failure _
  | bottom b =>
    simp only [emulatedProgram]
    split
    · unfold newBottomWith
      exact (PartyCost.bind (m := 0) (PartyCost.map _ (bottomOutput_cost K circuits settings D hsize parameter seeds
        openings i _ _ b randomizer (0, 0))) fun out => by
          rcases out with _ | out
          · exact PartyCost.failure _
          · exact PartyCost.pure _ _).mono (le_of_eq (add_zero _))
    · exact PartyCost.failure _

end Operator

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.emulatedProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.emulatedProgram_cost
