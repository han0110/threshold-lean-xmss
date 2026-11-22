import ThresholdLeanXmssSecurity.Proof.CeremonyHybrid.Phase

/-!
# The real programs as timed phases

`check_of_count_eq_zero` gives the check with no tuple bit. `executePhase_bind` cuts a run of the
programs `p i >>= k i` when each `p i` is `Timed`, and this file writes the real programs of
`Scheme.lean` in that form. `RunTimed n x` states that `x` takes exactly `n` rounds or calls from
each state, on each path that does not abort. The `timed_*` and `runTimed_*` lemmas give the rounds
of the PRSS setup, of the building blocks and of the check (`runTimed_check`, `runTimed_realCheck`).
-/

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

section RealBlocks

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}

/-- The check with no tuple is `pure ()`. -/
theorem check_of_count_eq_zero (K : Constants C E) (ctx : Context C)
    (buildingBlocks : CheckBuildingBlocks C E G) (tuples : List (Tuple C))
    (h : (tuples.map (·.count)).sum = 0) :
    check K ctx buildingBlocks tuples = pure () := by
  simp [check, h]

end RealBlocks

end ThresholdLeanXmssSecurity

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

section Generic

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-- The PRSS setup takes three rounds, namely commit, reveal and echo. -/
theorem timed_commitRevealEcho (phase : Phase) (i : C.Party) (own : Parts C) :
    Timed 3 (commitRevealEcho (E := E) (G := G) phase i own).run := by
  unfold commitRevealEcho
  refine Timed.oracleStep_bind 3 _ _ fun commitments => ?_
  refine Timed.exchange_bind 2 _ _ fun committed => ?_
  refine Timed.exchange_bind 1 _ _ fun revealed => ?_
  refine Timed.oracleStep_bind 1 _ _ fun opens => ?_
  refine Timed.require_bind 1 _ _ fun _ => ?_
  refine Timed.oracleStep_bind 1 _ _ fun keys => ?_
  refine Timed.oracleStep_bind 1 _ _ fun shared => ?_
  refine Timed.exchange_bind 0 _ _ fun received => ?_
  exact Timed.require_bind 0 _ _ fun _ => timed_pure _

/-- `prssSetup` is one phase of `setupRounds = 3` rounds. -/
theorem timed_prssSetup (i : C.Party) : Timed setupRounds (prssSetup (E := E) (G := G) i).run := by
  unfold prssSetup prssSetupWith
  refine Timed.localStep_bind 3 _ _ fun own => ?_
  exact (timed_commitRevealEcho (E := E) (G := G) .prss i own).bind (n := 0)
    (k := fun r => (pure ⟨r.2.1, r.2.2⟩ : PartyM C E G (PrssKeys C))) fun r => timed_pure _

/-- A program on a state that takes exactly `n` rounds or calls from every state, on each path that
does not abort. -/
def RunTimed {σ α : Type} (n : ℕ) (x : StateT σ (PartyM C E G) α) : Prop :=
  ∀ st, Timed n (x.run st).run

variable {σ : Type}

theorem RunTimed.bind {α β : Type} {m n : ℕ} {x : StateT σ (PartyM C E G) α}
    {k : α → StateT σ (PartyM C E G) β} (hx : RunTimed m x) (hk : ∀ a, RunTimed n (k a)) :
    RunTimed (m + n) (x >>= k) := fun st => by
  rw [StateT.run_bind]
  exact (hx st).bind fun q => hk q.1 q.2

theorem runTimed_pure {α : Type} (a : α) : RunTimed 0 (pure a : StateT σ (PartyM C E G) α) := fun st => by
  rw [StateT.run_pure]
  exact timed_pure _

/-- A program that only reads or writes the state takes no round. -/
theorem runTimed_of_run {α : Type} (x : StateT σ (PartyM C E G) α) (f : σ → α × σ)
    (hx : ∀ st, x.run st = pure (f st)) : RunTimed 0 x := fun st => by
  rw [hx]
  exact timed_pure _

theorem RunTimed.lift {α : Type} {n : ℕ} {p : PartyM C E G α} (hp : Timed n p.run) :
    RunTimed n (StateT.lift p : StateT σ (PartyM C E G) α) := fun st => by
  rw [StateT.run_lift]
  simpa only [Nat.add_zero] using hp.bind fun a => timed_pure (a, st)

theorem RunTimed.of_eq {α : Type} {m n : ℕ} {x : StateT σ (PartyM C E G) α} (hx : RunTimed m x) (h : m = n) :
    RunTimed n x := h ▸ hx

theorem RunTimed.foldlM {α β : Type} {n : ℕ} (f : α → β → StateT σ (PartyM C E G) α)
    (hf : ∀ a b, RunTimed n (f a b)) : ∀ (l : List β) (init : α), RunTimed (l.length * n) (l.foldlM f init)
  | [], init => by simpa only [List.foldlM_nil, List.length_nil, Nat.zero_mul] using runTimed_pure init
  | b :: l, init => by
    rw [List.foldlM_cons, List.length_cons, Nat.succ_mul, Nat.add_comm]
    exact (hf init b).bind fun a => RunTimed.foldlM f hf l a

/-- Local work over a list takes no round. -/
theorem timed_mapM {α β : Type} (f : α → PartyM C E G β) (hf : ∀ a, Timed 0 (f a).run) :
    ∀ l : List α, Timed 0 (l.mapM f).run
  | [] => timed_pure _
  | a :: l => by
    rw [List.mapM_cons]
    exact (hf a).bind fun b => (timed_mapM f hf l).bind (n := 0) fun bs => timed_pure _

end Generic

section Blocks

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}
  (K : Constants C E) (ctx : Context C)

omit [Field E] [Algebra Bit E] in
theorem runTimed_freshLabel : RunTimed 0 (freshLabel (C := C) (E := E) (G := G)) :=
  runTimed_of_run _ (fun s => (s.label, { s with label := s.label + 1 })) fun _ => rfl

omit [Field E] [Algebra Bit E] in
theorem timed_oracleStep {α : Type} (oa : OracleComp (RoSpec C) α) : Timed 0 (oracleStep (E := E) (G := G) oa).run := by
  rw [← bind_pure (oracleStep oa)]
  exact Timed.oracleStep_bind 0 _ _ fun a => timed_pure a

omit [Field E] [Algebra Bit E] in
theorem timed_exchange (out : Mail C E) : Timed 1 (exchange (G := G) out).run := by
  rw [← bind_pure (exchange out)]
  exact Timed.exchange_bind 0 _ _ fun a => timed_pure a

omit [Field E] [Algebra Bit E] in
theorem timed_require (c : Prop) : Timed 0 (require (C := C) (E := E) (G := G) c).run := by
  rw [← bind_pure (require c)]
  exact Timed.require_bind 0 _ _ fun _ => timed_pure _

omit [Field E] [Algebra Bit E] in
/-- `Rand` is local work. -/
theorem runTimed_prssRandomness {R : Type} [Zero R] (codec : Codec C E R) (idx count : ℕ) :
    RunTimed 0 (prssRandomness (G := G) ctx codec idx count) := by
  unfold prssRandomness
  refine RunTimed.bind (m := 0) (n := 0) runTimed_freshLabel fun ρ => ?_
  refine RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun r => ?_
  exact RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun Z => runTimed_pure _

theorem runTimed_record {R : Type} (codec : Codec C E R) (mode : ReshareMode) (z : Shares C R) (count : ℕ) :
    RunTimed 0 (record (G := G) K ctx codec mode z count) :=
  runTimed_of_run _ _ fun _ => rfl

/-- A peer reshare takes one round. -/
theorem runTimed_reshare {R : Type} [Field R] (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R)
    (count : ℕ) : RunTimed 1 (reshare (G := G) K ctx codec randomness v count) := by
  obtain ⟨r, Z⟩ := randomness
  unfold reshare
  dsimp only
  refine RunTimed.bind (m := 1) (n := 0) (RunTimed.lift (timed_exchange _)) fun inbox => ?_
  exact RunTimed.bind (m := 0) (n := 0) (runTimed_record K ctx codec .peer _ count) fun _ => runTimed_pure _

/-- A collector reshare takes two rounds. -/
theorem runTimed_reshareCollector (randomness : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    RunTimed 2 (reshareCollector (G := G) K ctx randomness v count) := by
  obtain ⟨r, Z⟩ := randomness
  unfold reshareCollector
  dsimp only
  refine RunTimed.bind (m := 1) (n := 1) (RunTimed.lift (timed_exchange _)) fun inbox => ?_
  refine RunTimed.bind (m := 1) (n := 0) (RunTimed.lift (timed_exchange _)) fun forward => ?_
  exact RunTimed.bind (m := 0) (n := 0) (runTimed_record K ctx bitCodec .collector _ count) fun _ => runTimed_pure _

/-- A reshare of the AND gates takes `mode.rounds` rounds. -/
theorem runTimed_reshareWith (mode : ReshareMode) (randomness : PrssOutput C Bit) (v : ℕ → Bit) (count : ℕ) :
    RunTimed mode.rounds (reshareWith (G := G) K ctx mode randomness v count) := by
  cases mode with
  | peer => exact runTimed_reshare K ctx bitCodec randomness v count
  | collector => exact runTimed_reshareCollector K ctx randomness v count

/-- `OpenRep` takes one round, in every hybrid model. -/
theorem timed_openRep_any (v : Shares C Bit) (count : ℕ) : Timed 1 (openRep (G := G) K ctx v count).run := by
  unfold openRep
  exact Timed.oracleStep_bind 1 _ _ fun digests => Timed.exchange_bind 0 _ _ fun inbox =>
    Timed.oracleStep_bind 0 _ _ fun copyDigests => Timed.require_bind 0 _ _ fun _ => timed_pure _

/-- `OpenSh` takes one round. -/
theorem timed_openSh (v : ℕ → E) (count : ℕ) : Timed 1 (openSh (G := G) K ctx v count).run := by
  unfold openSh
  exact Timed.exchange_bind 0 _ _ fun inbox => Timed.require_bind 0 _ _ fun _ => timed_pure _

end Blocks

section CheckTimed

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}
  (K : Constants C E) (ctx : Context C) (buildingBlocks : CheckBuildingBlocks C E G)
  (hcoin : ∀ n, RunTimed 1 (buildingBlocks.coin n))
  (hextend : ∀ products, RunTimed 1 (buildingBlocks.extendMult products))
  (helements : ∀ n, RunTimed 0 (buildingBlocks.randElements n))
  (hbits : ∀ n, RunTimed 0 (buildingBlocks.randBits n))

omit [Field E] [Algebra Bit E] in
theorem runTimed_get : RunTimed 0 (get : RunM C E G (RunState C)) :=
  runTimed_of_run _ (fun s => (s, s)) fun _ => rfl

include hcoin in
/-- A coin key takes the one round of `Coin`. -/
theorem runTimed_coinKey : RunTimed 1 (coinKey K buildingBlocks) := by
  unfold coinKey
  refine RunTimed.bind (m := 0) (n := 1) runTimed_get fun state => ?_
  exact RunTimed.bind (m := 1) (n := 0) (hcoin 2) fun values => RunTimed.lift (timed_oracleStep _)

theorem runTimed_expand (key : HashOutput) (count : ℕ) : RunTimed 0 (expand (G := G) K key count) :=
  RunTimed.lift (timed_oracleStep _)

include hcoin in
/-- A challenge takes the one round of its coin. -/
theorem runTimed_challenge : RunTimed 1 (challenge K buildingBlocks) := by
  unfold challenge
  refine RunTimed.bind (m := 1) (n := 0) (runTimed_coinKey K buildingBlocks hcoin) fun key => ?_
  refine RunTimed.bind (m := 0) (n := 0) (RunTimed.lift (timed_oracleStep _)) fun r => ?_
  rcases r with _ | r
  · exact RunTimed.lift (timed_failure 0)
  · exact runTimed_pure r

omit [Field E] [Algebra Bit E] in
/-- The comparison of the salted digests takes one round. -/
theorem runTimed_compareDigests (salts : Shares C Bit) : RunTimed 1 (compareDigests (E := E) (G := G) ctx salts) := by
  unfold compareDigests
  refine RunTimed.bind (m := 0) (n := 1) runTimed_get fun state => ?_
  refine RunTimed.bind (m := 0) (n := 1) (RunTimed.lift (timed_oracleStep _)) fun digests => ?_
  exact RunTimed.bind (m := 1) (n := 0) (RunTimed.lift (timed_exchange _)) fun inbox => RunTimed.lift (timed_require _)

include hcoin hextend in
/-- A slice step takes one `extendMult` and one challenge. -/
theorem runTimed_sliceStep (τ : List E) (count : ℕ) (p : Shares C E × Shares C E × E) (j : ℕ) :
    RunTimed 2 (sliceStep K ctx buildingBlocks τ count p j) := by
  obtain ⟨xs, ys, D⟩ := p
  unfold sliceStep
  dsimp only
  refine RunTimed.bind (m := 1) (n := 1) (hextend _) fun t => ?_
  exact RunTimed.bind (m := 1) (n := 0) (runTimed_challenge K buildingBlocks hcoin) fun r => runTimed_pure _

include hcoin hextend in
/-- A halving step takes one `extendMult` and one challenge. -/
theorem runTimed_halvingStep (width : ℕ) (p : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    RunTimed 2 (halvingStep K ctx buildingBlocks width p j) := by
  obtain ⟨A, B, D⟩ := p
  unfold halvingStep
  dsimp only
  refine RunTimed.bind (m := 1) (n := 1) (hextend _) fun t => ?_
  exact RunTimed.bind (m := 1) (n := 0) (runTimed_challenge K buildingBlocks hcoin) fun r => runTimed_pure _

include hcoin hextend helements hbits in
/-- The randomization takes four rounds, namely `extendMult`, the digests, the coin and `OpenSh`. -/
theorem runTimed_finalStep (p : (ℕ → E) × (ℕ → E) × E) : RunTimed 4 (finalStep K ctx buildingBlocks p) := by
  obtain ⟨A, B, D⟩ := p
  unfold finalStep
  dsimp only
  refine RunTimed.bind (m := 0) (n := 4) (helements 2) fun w => ?_
  refine RunTimed.bind (m := 1) (n := 3) (hextend _) fun q => ?_
  refine RunTimed.bind (m := 0) (n := 3) (hbits 256) fun salts => ?_
  refine RunTimed.bind (m := 1) (n := 2) (runTimed_compareDigests ctx _) fun _ => ?_
  refine RunTimed.bind (m := 1) (n := 1) (runTimed_challenge K buildingBlocks hcoin) fun r => ?_
  exact RunTimed.bind (m := 1) (n := 0) (RunTimed.lift (timed_openSh K ctx _ 3)) fun opened =>
    RunTimed.lift (timed_require _)

include hcoin hextend helements hbits in
/-- The check of tuples with `count` positions in all takes `checkLabels count` rounds, which is
`2 * halvings count + 5`, or none for no position. -/
theorem runTimed_check (tuples : List (Tuple C)) :
    RunTimed (checkLabels ((tuples.map (·.count)).sum)) (check K ctx buildingBlocks tuples) := by
  by_cases h : (tuples.map (·.count)).sum = 0
  · have hc : check K ctx buildingBlocks tuples = pure () := by
      simp only [check, h, ↓reduceIte]
    rw [hc, checkLabels, ite_eq_left h]
    exact runTimed_pure ()
  · rw [check_eq K ctx buildingBlocks tuples h]
    have hlab : checkLabels ((tuples.map (·.count)).sum) =
        1 + (0 + (0 + ((List.range sliceBits).length * 2 +
          ((List.range (halvings ((tuples.map (·.count)).sum) - sliceBits)).length * 2 + 4)))) := by
      rw [checkLabels, ite_eq_right h, List.length_range, List.length_range, halvings]
      omega
    rw [hlab]
    refine (runTimed_coinKey K buildingBlocks hcoin).bind fun key => ?_
    refine (runTimed_expand K key _).bind fun τ => ?_
    refine (RunTimed.lift (timed_require _)).bind fun _ => ?_
    refine (RunTimed.foldlM _ (runTimed_sliceStep K ctx buildingBlocks hcoin hextend τ _) _ _).bind fun p => ?_
    refine (RunTimed.foldlM _ (runTimed_halvingStep K ctx buildingBlocks hcoin hextend _) _ _).bind fun p' => ?_
    exact runTimed_finalStep K ctx buildingBlocks hcoin hextend helements hbits p'

end CheckTimed

section RealBlocks

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}
  (K : Constants C E) (ctx : Context C) (mode : ReshareMode)

theorem runTimed_realCoin (count : ℕ) : RunTimed 1 ((realCheckBuildingBlocks (G := G) K ctx).coin count) := by
  refine RunTimed.bind (m := 0) (n := 1) (runTimed_prssRandomness ctx _ 1 count) fun randomness => ?_
  unfold coinWith
  exact RunTimed.bind (m := 1) (n := 0) (RunTimed.lift (timed_openSh K ctx _ count)) fun _ => runTimed_pure _

theorem runTimed_realExtendMult (products : List (Product C E)) :
    RunTimed 1 ((realCheckBuildingBlocks (G := G) K ctx).extendMult products) :=
  RunTimed.bind (m := 0) (n := 1) (runTimed_prssRandomness ctx _ 0 _) fun _ => runTimed_reshare K ctx _ _ _ _

/-- The real check of tuples with `count` positions takes `checkLabels count` rounds. -/
theorem runTimed_realCheck (tuples : List (Tuple C)) :
    RunTimed (checkLabels ((tuples.map (·.count)).sum)) (check (G := G) K ctx (realCheckBuildingBlocks K ctx) tuples) :=
  runTimed_check K ctx _ (runTimed_realCoin K ctx) (runTimed_realExtendMult K ctx)
    (fun n => runTimed_prssRandomness ctx _ 1 n) (fun n => runTimed_prssRandomness ctx _ 2 n) tuples

/-- The real multiplication of one AND layer takes `mode.rounds` rounds. -/
theorem runTimed_realMult (x y : Shares C Bit) (count : ℕ) :
    RunTimed mode.rounds ((realRunBuildingBlocks (G := G) K ctx mode).mult x y count) :=
  (RunTimed.bind (m := 0) (n := mode.rounds) (runTimed_prssRandomness ctx _ 0 count) fun _ =>
    runTimed_reshareWith K ctx mode _ _ count).of_eq (Nat.zero_add _)

/-- The real `Rerand` takes one round. -/
theorem runTimed_realRerand (v : Shares C Bit) (count : ℕ) :
    RunTimed 1 ((realRunBuildingBlocks (G := G) K ctx mode).rerand v count) :=
  RunTimed.bind (m := 0) (n := 1) (runTimed_prssRandomness ctx _ 0 count) fun _ => runTimed_reshare K ctx _ _ _ _

/-- The real `OpenRep` of the outputs takes one round. -/
theorem runTimed_realOutput (v : Shares C Bit) (count : ℕ) :
    RunTimed 1 ((realRunBuildingBlocks (G := G) K ctx mode).output v count) :=
  RunTimed.lift (timed_openRep_any K ctx v count)

end RealBlocks

section Batch

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}
  (K : Constants C E) (buildingBlocks : RunBuildingBlocks C E G) (jobs : List Circuit)

/-- The rest of a run of `jobs` before the AND layers `ls`, from the wires and tuples `p` and the
state `st`. -/
def runAt (ls : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C) :
    PartyM C E G (List (List Bit) × RunState C) :=
  (ls.foldlM (layerBody K buildingBlocks jobs) p >>= tailBody K buildingBlocks jobs).run st

/-- An AND layer is one phase, the call of `mult`. The rest takes the new values `z` and the new
state. The tuple counts of the rest do not depend on `z`. -/
theorem runAt_cons (l : ℕ) (ls : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C) :
    runAt K buildingBlocks jobs (l :: ls) p st =
      (buildingBlocks.mult (layerX K jobs l p.1) (layerY K jobs l p.1) (gatesAt jobs l).length).run st >>= fun r =>
        runAt K buildingBlocks jobs ls (appendLayer jobs l p.1 r.1,
          p.2 ++ [⟨layerX K jobs l p.1, layerY K jobs l p.1, r.1, (gatesAt jobs l).length, buildingBlocks.mode⟩]) r.2 := by
  simp only [runAt, List.foldlM_cons, layerBody_apply, bind_assoc, pure_bind, StateT.run_bind]

/-- The tail of a run is three phases, namely `Rerand`, the check and `OpenRep`. -/
theorem runAt_nil (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C) :
    runAt K buildingBlocks jobs [] p st =
      (buildingBlocks.rerand (outputShares K jobs p.1) (outputsOf jobs).length).run st >>= fun r =>
        (buildingBlocks.verify (p.2 ++ [⟨outputShares K jobs p.1, one K, r.1, (outputsOf jobs).length, .peer⟩])).run r.2 >>=
          fun s => (buildingBlocks.output r.1 (outputsOf jobs).length).run s.2 >>= fun o =>
            pure (assemble jobs o.1, o.2) := by
  simp only [runAt, List.foldlM_nil, pure_bind, tailBody_apply, StateT.run_bind, StateT.run_pure]

variable (rounds : ℕ)
  (hmult : ∀ x y n, RunTimed rounds (buildingBlocks.mult x y n))
  (hrerand : ∀ v n, RunTimed 1 (buildingBlocks.rerand v n))
  (hverify : ∀ tuples : List (Tuple C), RunTimed (checkLabels ((tuples.map (·.count)).sum)) (buildingBlocks.verify tuples))
  (houtput : ∀ v n, RunTimed 1 (buildingBlocks.output v n))

include hmult hrerand hverify houtput in
/-- The rest of a run before the layers `ls` takes `rounds` for each layer, one round for `Rerand`,
the rounds of the check of all tuples and one round for `OpenRep`. -/
theorem timed_runAt : ∀ (ls : List ℕ) (p : List (C.Term → List Bit) × List (Tuple C)) (st : RunState C),
    Timed (ls.length * rounds + 1 + checkLabels ((p.2.map (·.count)).sum +
        (ls.map fun l => (gatesAt jobs l).length).sum + (outputsOf jobs).length) + 1)
      (runAt K buildingBlocks jobs ls p st).run
  | [], p, st => by
    rw [runAt_nil]
    simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, List.map_nil, List.sum_nil, Nat.add_zero]
    rw [Nat.add_assoc]
    refine Timed.bind (m := 1) (hrerand _ _ st) fun r => ?_
    have hv := hverify (p.2 ++ [⟨outputShares K jobs p.1, one K, r.1, (outputsOf jobs).length, .peer⟩]) r.2
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero] at hv
    exact hv.bind fun s => (houtput _ _ s.2).bind (n := 0) fun o => timed_pure _
  | l :: ls, p, st => by
    rw [runAt_cons]
    have harg : (p.2.map (·.count)).sum + ((l :: ls).map fun l => (gatesAt jobs l).length).sum + (outputsOf jobs).length =
        (p.2.map (·.count)).sum + (gatesAt jobs l).length + (ls.map fun l => (gatesAt jobs l).length).sum +
          (outputsOf jobs).length := by
      simp only [List.map_cons, List.sum_cons]
      omega
    rw [harg, show (l :: ls).length * rounds + 1 = rounds + (ls.length * rounds + 1) by
      simp only [List.length_cons, Nat.succ_mul]; omega, Nat.add_assoc rounds, Nat.add_assoc rounds]
    refine Timed.bind (m := rounds) (hmult _ _ _ st) fun r => ?_
    have h := timed_runAt ls (appendLayer jobs l p.1 r.1,
      p.2 ++ [⟨layerX K jobs l p.1, layerY K jobs l p.1, r.1, (gatesAt jobs l).length, buildingBlocks.mode⟩]) r.2
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero] at h
    exact h

end Batch

section TreePhases

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings)

omit [Fintype E] [DecidableEq E] in
/-- One real batch is the local input work and then the phases of `runAt`. -/
theorem realBatch_phases (mode : ReshareMode) (ctx : Context C) (parameter : PublicParameter) (jobs : List Job)
    (st : ℕ × ℕ) :
    (realBatch K circuits mode ctx parameter jobs).run st =
      jobs.mapM (inputShares ctx) >>= fun inputs =>
        runAt K (realRunBuildingBlocks K ctx mode) (jobs.map (circuits parameter ·.kind))
            (List.range (depth (jobs.map (circuits parameter ·.kind)))) (inputs, []) ⟨fun _ => [], st.1, st.2⟩ >>=
          fun r => pure (some r.1, (r.2.label, st.2 + 1)) :=
  realBatch_run K circuits mode ctx parameter jobs st

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
/-- The input wires of a batch are local work. -/
theorem timed_inputShares (ctx : Context C) (jobs : List Job) :
    Timed 0 (jobs.mapM (inputShares (E := E) (G := RealSpec) ctx)).run :=
  timed_mapM _ (fun _ => Timed.oracleStep_bind 0 _ _ fun _ => timed_pure _) jobs

/-- A real batch takes `batchRounds` rounds from every start of the counters. -/
theorem runTimed_realBatch (mode : ReshareMode) (ctx : Context C) (parameter : PublicParameter) (jobs : List Job) :
    RunTimed (batchRounds circuits mode parameter jobs) (realBatch K circuits mode ctx parameter jobs) := fun st => by
  rw [realBatch_phases, batchRounds, batchCount, tupleCount_eq, ← Nat.zero_add (_ + 1), ← Nat.add_zero (_ + 1)]
  refine Timed.bind (timed_inputShares ctx jobs) fun inputs => Timed.bind ?_ fun r => timed_pure _
  have h := timed_runAt K (realRunBuildingBlocks (G := RealSpec) K ctx mode) (jobs.map (circuits parameter ·.kind)) mode.rounds
    (runTimed_realMult K ctx mode) (runTimed_realRerand K ctx mode) (runTimed_realCheck K ctx)
    (runTimed_realOutput K ctx mode) (List.range (depth (jobs.map (circuits parameter ·.kind)))) (inputs, [])
    ⟨fun _ => [], st.1, st.2⟩
  simpa only [List.length_range, List.map_nil, List.sum_nil, Nat.zero_add] using h

/-- The batches `js` of a ceremony take the sum of their `batchRounds`. -/
theorem runTimed_batches (mode : ReshareMode) (ctx : Context C) (parameter : PublicParameter) :
    ∀ js : List (List Job), RunTimed ((js.map (batchRounds circuits mode parameter)).sum)
      (js.mapM (realBatch K circuits mode ctx parameter))
  | [] => runTimed_pure []
  | jobs :: js => by
    rw [List.mapM_cons, List.map_cons, List.sum_cons]
    exact (runTimed_realBatch K circuits mode ctx parameter jobs).bind fun b =>
      ((runTimed_batches mode ctx parameter js).bind fun bs => runTimed_pure (b :: bs)).of_eq (Nat.add_zero _)

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
/-- The fuel of a top tree is the exact rounds of its program and a rest, which the network runs
after the program ends. -/
theorem topRounds_le (parameter : PublicParameter) :
    setupRounds + ((chunks settings.batchSize topJobs).map (batchRounds circuits settings.mode parameter)).sum ≤
      setupRounds + ceremonyFuel circuits settings := by
  have hx := (chunks_rounds_le circuits settings parameter 0 (fun _ => digit 0) (chunks settings.batchSize topJobs)
    fun jobs hj => Or.inl hj).trans
      (Nat.mul_le_mul_right (maxBatch circuits settings (runRounds settings.mode))
        (treeBatches_le_ceremonyBatches settings .top))
  unfold ceremonyFuel
  omega

omit [Field E] [Algebra Bit E] [Fintype E] [DecidableEq E] in
/-- The fuel of a bottom tree covers both ceremonies at every encoding. The rest runs after the
program ends. -/
theorem bottomRounds_le (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (encoding : Encoding) :
    (setupRounds + ((chunks settings.batchSize (bottomJobs b)).map (batchRounds circuits settings.mode parameter)).sum) +
        (setupRounds + ((chunks settings.batchSize (signJobs b encoding)).map
          (batchRounds circuits settings.mode parameter)).sum) ≤
      setupRounds + ceremonyFuel circuits settings := by
  have hx := chunks_rounds_le circuits settings parameter b encoding (chunks settings.batchSize (bottomJobs b))
    fun jobs hj => Or.inr (Or.inl hj)
  have hy := chunks_rounds_le circuits settings parameter b encoding (chunks settings.batchSize (signJobs b encoding))
    fun jobs hj => Or.inr (Or.inr hj)
  have hb := treeBatches_le_ceremonyBatches settings (.bottom b)
  simp only [treeBatches] at hb
  rw [length_chunks_signJobs settings b b (fun _ => digit 0) encoding] at hb
  have hm := Nat.mul_le_mul_right (maxBatch circuits settings (runRounds settings.mode)) hb
  rw [Nat.add_mul] at hm
  unfold ceremonyFuel setupRounds
  omega

end TreePhases

end ThresholdLeanXmssSecurity

end

end

/-- info: 'ThresholdLeanXmssSecurity.check_of_count_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.check_of_count_eq_zero

/-- info: 'ThresholdLeanXmssSecurity.timed_prssSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.timed_prssSetup

/-- info: 'ThresholdLeanXmssSecurity.runTimed_realCheck' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.runTimed_realCheck

/-- info: 'ThresholdLeanXmssSecurity.runTimed_realMult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.runTimed_realMult

/-- info: 'ThresholdLeanXmssSecurity.runTimed_realRerand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.runTimed_realRerand

/-- info: 'ThresholdLeanXmssSecurity.runTimed_realOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.runTimed_realOutput

/-- info: 'ThresholdLeanXmssSecurity.runAt_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.runAt_cons

/-- info: 'ThresholdLeanXmssSecurity.runAt_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.runAt_nil

/-- info: 'ThresholdLeanXmssSecurity.timed_runAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.timed_runAt

/-- info: 'ThresholdLeanXmssSecurity.realBatch_phases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.realBatch_phases

/-- info: 'ThresholdLeanXmssSecurity.runTimed_realBatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.runTimed_realBatch

/-- info: 'ThresholdLeanXmssSecurity.runTimed_batches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.runTimed_batches

/-- info: 'ThresholdLeanXmssSecurity.topRounds_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.topRounds_le

/-- info: 'ThresholdLeanXmssSecurity.bottomRounds_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.bottomRounds_le
