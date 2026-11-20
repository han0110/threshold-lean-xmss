import ThresholdLeanXmssSecurity.Proof.BatchCheck.Schedule
import ThresholdLeanXmssSecurity.Proof.CeremonyHybrid.Phase
import ThresholdLeanXmssSecurity.Proof.CheckFinish

/-!
# The wrapper of the hybrid step of a check

`c1Wrapper` is the hybrid adversary of the step of one check, `roundScheduled` with concrete parts.
`checkHead` and `checkRest` cut the check after the masked multiplication of the randomization, and
`C1aStatement` and `C1bStatement` state the two halves of the step. The file holds the route of the
step as named statements, the bound of the digest calls of the head, the memory of the wrapper after
a reply, the count of the cells before a check, and the part bounds of the wrapper.
-/

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1s

open RealNetworkV3

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-- The leaks of the functionalities of the check. -/
abbrev CheckLeak (C : Committee) (E : Type) := (List E ⊕ (C.Party → List (Product C E))) ⊕ (Unit ⊕ Unit)

/-- The replies to the functionalities of the check. -/
abbrev CheckAnswer (C : Committee) (E : Type) :=
  (Finset C.Party ⊕ ((ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party)) ⊕
    ((Shares C E × (C.Party → C.Party → ℕ → E)) ⊕ (Shares C Bit × (C.Party → C.Party → ℕ → Bit)))

/-! ## The tails and the survivors of the wrapper -/

section Copies

variable [Field E] [Algebra Bit E]

/-- The tail of `Coin`. -/
def coinTail [SampleableType E] {Ia L R : Type} (K : Constants C E) (D : C.Coalition) (A : Adversary C E Ia L R)
    (known : Shares C E) (knownPairs : C.Party → C.Party → ℕ → E) (count : ℕ) (live : Finset C.Party)
    (st : A.State) : OracleComp (LocalSpec C) A.State := do
  let fresh ← liftComp ($ᵗ (C.Term → Fin count → E)) (LocalSpec C)
  let freshPair ← liftComp ($ᵗ (C.Pair → Fin count → E)) (LocalSpec C)
  let b ← A.round st fun c i => if c ∈ D.1 ∧ i ∈ live then
    openOut i (conv K (localContext i) (frandShare D count known knownPairs fresh freshPair i).1) count c
    else none
  pure b.1

/-- The tail of a peer reshare. -/
def reshareTail {M : Type} [Field M] [SampleableType M] {Ia L R : Type} (K : Constants C E) (D : C.Coalition)
    (codec : Codec C E M) (A : Adversary C E Ia L R) (known : Shares C M)
    (knownPairs : C.Party → C.Party → ℕ → M) (count : ℕ) (live : Finset C.Party) (st : A.State) :
    OracleComp (LocalSpec C) A.State := do
  let fresh ← liftComp ($ᵗ (C.Term → Fin count → M)) (LocalSpec C)
  let freshPair ← liftComp ($ᵗ (C.Pair → Fin count → M)) (LocalSpec C)
  let b ← A.round st fun c i =>
    if i ∈ live then realMsgs K D codec known knownPairs fresh freshPair (fun _ _ => 0) c i else none
  pure b.1

omit [Field E] [Algebra Bit E] in
/-- The inbox of operator `j` as the wrapper rebuilds it. -/
def digestInbox (D : C.Coalition) (view sent : C.Party → C.Party → Option (Msg E)) (c₀ j : C.Party) : Mail C E :=
  fun k => if k ∈ D.1 then sent k j else if k = j then none else view c₀ k

omit [Field E] [Algebra Bit E] in
/-- The survivors of the digest round that the wrapper names. -/
def digestSurv (D : C.Coalition) (view sent : C.Party → C.Party → Option (Msg E)) (j : C.Party) : Prop :=
  if h : ∃ c, c ∈ D.1 then
    (C.parties.any fun k => Msg.isAbort (digestInbox D view sent h.choose j k)) = false ∧
      DigestsAgree j (Msg.hashesOf (view h.choose j)) (digestInbox D view sent h.choose j)
  else True

end Copies

/-! ## The parts of the wrapper -/

section Parts

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The memory of the wrapper. `hist i T` is the history of the known term `T` at the honest operator
`i`. `values` holds the leak of the last call of `F_coin`. -/
structure C1Memory (C : Committee) (E : Type) where
  hist : C.Party → C.Term → List Bit
  values : List E

/-- The adversary `W` in the `F_rand`-hybrid model, with the fixed reply `known`. The block simulators
`coinSimAnswer` and `peerSimAnswer` read only its rounds and its replies, so its start is the state `st`. -/
@[reducible] def frandAdv {Ia I L R M : Type} (W : Adversary C E Ia L R)
    (known : Shares C M × (C.Party → C.Party → ℕ → M)) (st : W.State) :
    Adversary C E I Unit (Shares C M × (C.Party → C.Party → ℕ → M)) where
  State := W.State
  start _ _ := pure st
  round := W.round
  answer s _ := pure (s, known)

/-- The receivers in a reply to `F_coin`. Another reply counts as the default reply, as in
`Functionality.sum`. -/
def coinReply : CheckAnswer C E → Finset C.Party
  | .inl (.inl receivers) => receivers
  | _ => ∅

/-- The reply to `F_extendMult`. Another reply counts as the default reply. -/
def extendReply : CheckAnswer C E → (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party
  | .inl (.inr r) => r
  | _ => default

/-- The honest receivers that a reply names. `F_coin` and `F_extendMult` give an output to the receivers
of the reply. `F_rand` gives an output to each honest operator. -/
def c1Names : CheckLeak C E → CheckAnswer C E → C.Party → Prop
  | .inl (.inl _), r, i => i ∈ coinReply r
  | .inl (.inr _), r, i => i ∈ (extendReply r).2.2.2
  | .inr _, _, _ => True

/-- The premise on `names`. It reports the receivers of each reply at each honest operator. -/
def NamesReceivers (D : C.Coalition) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) : Prop :=
  ∀ l r, ∀ i ∉ D.1, names l r i ↔ c1Names l r i

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
theorem c1Names_receivers (D : C.Coalition) : NamesReceivers D (c1Names (C := C) (E := E)) :=
  fun _ _ _ _ => Iff.rfl

/-- The histories of the known terms after the reply `r` to `F_extendMult` with two products. A holder
of the known term `T` records the value `known T g` of the reply, plus its `offset` at each position
that a corrupt operator fills (`Fmult` and `record`). -/
def recordKnown (K : Constants C E) (D : C.Coalition) (hist : C.Party → C.Term → List Bit)
    (r : (ℕ → E) × Shares C E × (C.Party → Shares C E) × Finset C.Party) : C.Party → C.Term → List Bit :=
  fun i T => if i ∉ D.1 ∧ KnownTo D.1 T then
    recordHistory K i (hist i)
      (fun T' g => r.2.1 T' g + if ∃ j ∈ D.1, filler K .peer T' g = some j then r.2.2.1 i T' g else 0) 2 T
  else []

/-- The block simulators. The reply to `F_coin` is `coinSimAnswer`, and the memory keeps the values. The
reply to `F_extendMult` is `peerSimAnswer` for two products, and the memory records the known terms.
The replies to `F_rand` are the known streams of the label. -/
def c1Sims {Ia : Type} (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) :
    ℕ → W.State × C1Memory C E → CheckLeak C E →
      OracleComp (LocalSpec C) ((W.State × C1Memory C E) × CheckAnswer C E) :=
  fun n s l => match l with
    | .inl (.inl values) => (fun r => ((r.1, ⟨s.2.hist, values⟩), Sum.inl (Sum.inl r.2))) <$>
        coinSimAnswer K D (frandAdv W (knownE n) s.1) values.length values s.1
    | .inl (.inr _) => (fun r => ((r.1, ⟨recordKnown K D s.2.hist r.2, s.2.values⟩), Sum.inl (Sum.inr r.2))) <$>
        peerSimAnswer K D (frandAdv (I := Ia) W (knownE n) s.1) (elementCodec K) 2 s.1
    | .inr (.inl _) => pure (s, Sum.inr (Sum.inl (knownE n)))
    | .inr (.inr _) => pure (s, Sum.inr (Sum.inr knownB))

/-- The label position of the next `extendMult` after the coin at position `n`, with `R` halvings. After
the last halving step the randomization draws its mask first. -/
def nextMult (R n : ℕ) : ℕ := if n < 2 * R then n + 1 else n + 2

/-- The digest columns of the known terms, from the known salts and the histories of the memory. -/
def knownColumns (live : Finset C.Party) (known : Shares C Bit) (hist : C.Party → C.Term → List Bit)
    (T : C.Term) : OracleComp (LocalSpec C) (DigestColumn C) :=
  OverPermutation.sequenceFin fun i => RealNetworkRC.liveCol (· ∈ live) (fun _ => known) hist T i

/-- The tails of the replies, for a check of `count` tuple bits at the label `L` with the tag `tg`.
Position `n` is the count of the calls before. With `R = halvings count` the calls are `F_coin` at 0,
`F_extendMult` at `2 j + 1` and `F_coin` at `2 j + 2` for `j < R`, then `F_rand`, `F_extendMult`,
`F_rand` and `F_coin` at `2 R + 1` to `2 R + 4`.

* After the first coin the wrapper computes the coins `τ`, and plays the round of the first reshare.
* After `F_extendMult` of a step it plays the round of the next coin.
* After the coin of a challenge it repeats the search, and plays the round of the next reshare.
* After `F_extendMult` of the randomization it plays the digest round.
* After the last coin the next block is a round in both models, so it plays no tail. -/
def c1Tails {Ia : Type} (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg : ℕ) :
    ℕ → Finset C.Party → W.State × C1Memory C E → OracleComp (LocalSpec C) (W.State × C1Memory C E) :=
  fun n live s =>
    if n = 0 then do
      let τ ← liftComp (startQuery K tg L s.2.values (coins count)) (LocalSpec C)
      if ∀ b < sliceBits, τ.getD b 0 ≠ 0 then
        (fun st' => (st', s.2)) <$> reshareTail K D (elementCodec K) W (knownE (nextMult (halvings count) 0)).1
          (knownE (nextMult (halvings count) 0)).2 2 live s.1
      else pure s
    else if n = 2 * halvings count + 2 then
      (fun st' => (st', s.2)) <$> RealNetworkRC.digestTail D W live (knownColumns live knownB.1 s.2.hist) s.1
    else if 2 * halvings count < n then pure s
    else if n % 2 = 1 then
      (fun st' => (st', s.2)) <$> coinTail K D W (knownE (n + 1)).1 (knownE (n + 1)).2 2 live s.1
    else do
      let r ← liftComp (challengeQuery K tg (L + n) s.2.values) (LocalSpec C)
      if r.isSome then
        (fun st' => (st', s.2)) <$> reshareTail K D (elementCodec K) W (knownE (nextMult (halvings count) n)).1
          (knownE (nextMult (halvings count) n)).2 2 live s.1
      else pure s

/-- The tails with no digest round. `C1aStatement` uses them before the digest round. -/
def c1HeadTails {Ia : Type} (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg : ℕ) :
    ℕ → Finset C.Party → W.State × C1Memory C E → OracleComp (LocalSpec C) (W.State × C1Memory C E) :=
  fun n live s => if n = 2 * halvings count + 2 then pure s else c1Tails K D W knownE knownB count L tg n live s

/-- The tail of the digest round. The survivors play the round of the last coin. -/
def c1Rtails {Ia : Type} (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (count : ℕ) :
    ℕ → Finset C.Party → W.State × C1Memory C E → OracleComp (LocalSpec C) (W.State × C1Memory C E) :=
  fun n live s => if n = 2 * halvings count + 4 then
    (fun st' => (st', s.2)) <$> coinTail K D W (knownE n).1 (knownE n).2 2 live s.1
  else pure s

/-- The wrapper with free `names` and `tails`. Its start holds the histories `hist` of the known terms. -/
@[reducible] def c1WrapperWith {Ia : Type} (K : Constants C E) (D : C.Coalition)
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count : ℕ) (hist : C.Party → C.Term → List Bit)
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (tails : ℕ → Finset C.Party → W.State × C1Memory C E → OracleComp (LocalSpec C) (W.State × C1Memory C E)) :
    Adversary C E Ia (CheckLeak C E) (CheckAnswer C E) :=
  roundScheduled D (relabel (withMemory W (C1Memory C E) ⟨hist, []⟩) (checkReply (C := C) (E := E)))
    (c1Sims K D W knownE knownB) names tails (fun _ => digestSurv D) (c1Rtails K D W knownE count)

/-- The wrapper of the hybrid step of one check for the public schedule `(count, L, tg)`. -/
@[reducible] def c1Wrapper {Ia : Type} (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit) : Adversary C E Ia (CheckLeak C E) (CheckAnswer C E) :=
  c1WrapperWith K D W knownE knownB count hist c1Names (c1Tails K D W knownE knownB count L tg)

end Parts

/-! ## The counted calls of one activation -/

section Budget

/-- One reply of a wrapper is one reply of its block simulator and one tail. -/
theorem roundScheduled_answer_counted {Ia L R : Type} (D : C.Coalition) (W : Adversary C E Ia L R)
    (sims : ℕ → W.State → L → OracleComp (LocalSpec C) (W.State × R)) (names : L → R → C.Party → Prop)
    (tails : ℕ → Finset C.Party → W.State → OracleComp (LocalSpec C) W.State)
    (surv : ℕ → (C.Party → C.Party → Option (Msg E)) → (C.Party → C.Party → Option (Msg E)) → C.Party → Prop)
    (rtails : ℕ → Finset C.Party → W.State → OracleComp (LocalSpec C) W.State) (a b : ℕ)
    (hs : ∀ k st l, IsQueryBoundP (sims k st l) Counted a)
    (ht : ∀ k live st, IsQueryBoundP (tails k live st) Counted b) (s : W.State × ℕ) (l : L) :
    IsQueryBoundP ((roundScheduled D W sims names tails surv rtails).answer s l) Counted (a + b) := by
  refine isQueryBoundP_bind (hs s.2 s.1 l) fun x _ => ?_
  split_ifs
  · exact (isQueryBoundP_map_iff (p := Counted) _ _ _).2 (ht _ _ _)
  · exact isQueryBoundP_pure Counted _ _

/-- One round of a wrapper is one round of `W` and one tail. -/
theorem roundScheduled_round_counted {Ia L R : Type} (D : C.Coalition) (W : Adversary C E Ia L R)
    (sims : ℕ → W.State → L → OracleComp (LocalSpec C) (W.State × R)) (names : L → R → C.Party → Prop)
    (tails : ℕ → Finset C.Party → W.State → OracleComp (LocalSpec C) W.State)
    (surv : ℕ → (C.Party → C.Party → Option (Msg E)) → (C.Party → C.Party → Option (Msg E)) → C.Party → Prop)
    (rtails : ℕ → Finset C.Party → W.State → OracleComp (LocalSpec C) W.State) (a b : ℕ)
    (hr : ∀ st m, IsQueryBoundP (W.round st m) Counted a)
    (ht : ∀ k live st, IsQueryBoundP (rtails k live st) Counted b) (s : W.State × ℕ)
    (m : C.Party → C.Party → Option (Msg E)) :
    IsQueryBoundP ((roundScheduled D W sims names tails surv rtails).round s m) Counted (a + b) := by
  refine isQueryBoundP_bind (hr s.1 m) fun x _ => ?_
  split_ifs
  · exact (isQueryBoundP_map_iff (p := Counted) _ _ _).2 (ht _ _ _)
  · exact isQueryBoundP_pure Counted _ _

/-- Two local samples before a computation add no counted call. The samplers are variables, because
`IsQueryBoundP` unfolds a sample over `C.Term → Fin count → E` and does not end. -/
theorem two_samples_counted {α β σ : Type} (p : ProbComp α) (q : ProbComp β)
    (f : α → β → OracleComp (LocalSpec C) σ) (step : ℕ) (hf : ∀ a b, IsQueryBoundP (f a b) Counted step) :
    IsQueryBoundP (liftComp p (LocalSpec C) >>= fun a => liftComp q (LocalSpec C) >>= fun b => f a b)
      Counted step := by
  refine (isQueryBoundP_bind (n := 0) (m := step) (isQueryBoundP_liftComp_counted p) fun a _ => ?_).mono (by omega)
  exact (isQueryBoundP_bind (n := 0) (m := step) (isQueryBoundP_liftComp_counted q) fun b _ => hf a b).mono (by omega)

/-- One round of the adversary, with its new state as the result. -/
theorem round_fst_counted {Ia L R : Type} (A : Adversary C E Ia L R) (step : ℕ)
    (hr : ∀ st m, IsQueryBoundP (A.round st m) Counted step) (st : A.State)
    (m : C.Party → C.Party → Option (Msg E)) :
    IsQueryBoundP (A.round st m >>= fun b => pure b.1) Counted step :=
  (isQueryBoundP_bind (m := 0) (hr st m) fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- A block simulator makes the counted calls of one round of `W`. -/
def C1SimsCountedStatement (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (step : ℕ),
    (∀ st m, IsQueryBoundP (W.round st m) Counted step) →
    ∀ n s l, IsQueryBoundP (c1Sims K D W knownE knownB n s l) Counted step

/-- The tail of the digest round makes one round of `W`. -/
def C1RtailsCountedStatement (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (count step : ℕ), (∀ st m, IsQueryBoundP (W.round st m) Counted step) →
    ∀ n live s, IsQueryBoundP (c1Rtails K D W knownE count n live s) Counted step

end Budget

end ThresholdLeanXmssSecurity.RealNetworkC1s

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1s

open RealNetworkV3

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-! ## The cut of the check before the digests -/

/-- The check in the hybrid model up to the masked multiplication of the randomization. It returns the
last elements `A 0` and `B 0`, the claim `D`, the mask `w` and the output `q` of the multiplication. -/
def checkHead (K : Constants C E) (i : C.Party) (tuples : List (Tuple C)) :
    RunM C E (CheckSpec C E) (E × E × E × Shares C E × Shares C E) := do
  let count := (tuples.map (·.count)).sum
  let τ ← expand K (← coinKey K (hybridCheckBuildingBlocks K i)) (coins count)
  StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
  let p ← (List.range sliceBits).foldlM (sliceStep K (localContext i) (hybridCheckBuildingBlocks K i) τ count)
    ((fun T k => wordWeightOf K τ count k * liftedPart tuples (·.x) T k : Shares C E), liftedPart tuples (·.y),
      conv K (localContext i) (claimOf K τ count (liftedPart tuples (·.z))) 0)
  let p' ← (List.range (halvings count - sliceBits)).foldlM
    (halvingStep K (localContext i) (hybridCheckBuildingBlocks K i) (sliceWidth count))
    (conv K (localContext i) p.1, conv K (localContext i) p.2.1, p.2.2)
  let w ← (hybridCheckBuildingBlocks K i).randElements 2
  let q ← (hybridCheckBuildingBlocks K i).extendMult
    (maskedProducts K (fun _ => p'.1 0) (fun _ => p'.2.1 0) i w.1)
  pure (p'.1 0, p'.2.1 0, p'.2.2, w.1, q)

/-- The check from the salts of the digests, `finalRest` of `Proof/CheckStages.lean`. -/
def checkRest (K : Constants C E) (i : C.Party) (v : E × E × E × Shares C E × Shares C E) :
    RunM C E (CheckSpec C E) Unit :=
  finalRest K i v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2

/-- A check with a tuple is its head and then its rest. -/
theorem check_head_rest (K : Constants C E) (i : C.Party) (tuples : List (Tuple C))
    (h : (tuples.map (·.count)).sum ≠ 0) :
    check K (localContext i) (hybridCheckBuildingBlocks K i) tuples = checkHead K i tuples >>= checkRest K i := by
  rw [check_eq K (localContext i) (hybridCheckBuildingBlocks K i) tuples h]
  simp only [checkHead, checkRest, bind_assoc, pure_bind]
  refine bind_congr fun key => bind_congr fun τ => bind_congr fun _ => bind_congr fun p =>
    bind_congr fun p' => ?_
  exact finalStep_eq K i p'.1 p'.2.1 p'.2.2 (fun _ => p'.1 0) (fun _ => p'.2.1 0) rfl rfl

/-- The head of the check at operator `i`, from the state of a batch at its check. It returns the values
of the head and the state of the run. -/
def headAt (K : Constants C E) (L tg : ℕ) (x : C.Party → List (Tuple C)) (i : C.Party) :
    PartyM C E (CheckSpec C E) ((E × E × E × Shares C E × Shares C E) × RunState C) :=
  (checkHead K i (x i)).run ⟨filledHistory K i (x i), L, tg⟩

/-- The rest of the check at operator `i`, from the output of its head. -/
def restAt (K : Constants C E) (i : C.Party) (p : (E × E × E × Shares C E × Shares C E) × RunState C) :
    PartyM C E (CheckSpec C E) Unit :=
  (checkRest K i p.1).run' p.2

/-! ## The three runs -/

section Runs

variable {Ia : Type} (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia PEmpty PEmpty)
  (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E)) (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))

/-- The real check on drawn values. -/
def c1Real (counts : List ℕ) (L tg : ℕ) (x : C.Party → List (Tuple C)) (st : W.State) :
    OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
  drawTables (C := C) (E := E) (RealNetworkV3.checkLabels counts.sum) >>= fun tables =>
    executePhase localRoles D W noFunctionality (checkRounds counts.sum) st
      (drawnCheckAt K D L tg knownE knownB tables x)

/-- The salts of operator `i` from the drawn table, as `randBits` of `drawnCheckBuildingBlocks` gives
them. -/
def digestSalts (table : C.Term → Fin 256 → Bit) (i : C.Party) : Shares C Bit :=
  (frandShare D 256 knownB.1 knownB.2 table (fun _ _ => 0) i).1

/-- The check in the hybrid model under the wrapper, where the digest round after a partial start stays
real. The head runs under the wrapper with no digest tail. After a partial output of the head, the live
operators run the real digest round on drawn salts against `W`. After each other output, the rest of
the check runs under the wrapper. -/
def c1Mid (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (counts : List ℕ) (L tg : ℕ)
    (x : C.Party → List (Tuple C)) (st : W.State) :
    OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) := do
  let r ← executePhase localRoles D
    (c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x) names
      (c1HeadTails K D W knownE knownB counts.sum L tg))
    (checkFunctionalities K) (2 * halvings counts.sum + 3) ((st, ⟨knownHist K D x, []⟩), 0) (headAt K L tg x)
  if PartialOut D r.2 then do
    let table ← liftComp ($ᵗ (C.Term → Fin 256 → Bit)) (LocalSpec C)
    RealNetworkRC.realDigestPhase D W noFunctionality 1 r.1.1.1 (digestSalts D knownB table)
      (fun i => (r.2 i).map Prod.snd) (fun _ _ => (pure () : RunM C E RealSpec Unit))
  else
    (fun r' => (r'.1.1.1, r'.2)) <$> executePhase localRoles D
      (c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x) names
        (c1Tails K D W knownE knownB counts.sum L tg))
      (checkFunctionalities K) 5 r.1 (fun i => (r.2 i).elim failure (restAt K i))

/-- The check in the hybrid model under the wrapper. -/
def c1Hybrid (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (counts : List ℕ) (L tg : ℕ)
    (x : C.Party → List (Tuple C)) (st : W.State) :
    OracleComp (LocalSpec C) (W.State × (C.Party → Option Unit)) :=
  (fun r => (r.1.1.1, r.2)) <$> executePhase localRoles D
    (c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x) names
      (c1Tails K D W knownE knownB counts.sum L tg))
    (checkFunctionalities K) (checkRounds counts.sum) ((st, ⟨knownHist K D x, []⟩), 0) (checkAt K L tg x)

end Runs

/-! ## The statements -/

/-- For each adversary `W` of the real network, each choice of the known streams, each
`names` that reports the receivers of each reply, and each public schedule, the real check on drawn
values is `c1Mid`. The fact is `SameRun`, so it keeps the final cache. -/
def C1aStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (counts : List ℕ) (L tg : ℕ) (x : C.Party → List (Tuple C)) (st : W.State), counts.sum ≠ 0 →
      (∀ i, i ∉ D.1 → (x i).map (·.count) = counts) →
      SameRun prims (c1Real K D W knownE knownB counts L tg x st) (c1Mid K D W knownE knownB names counts L tg x st)

/-- `c1Mid` and the check under the wrapper are close. The error is `c1Error`, the bound of the hiding
of the salted digests for the one digest round after a partial start. The hidden terms of the
tuples are consistent, and the memory of the wrapper starts with the histories of the known terms. -/
def C1bStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (step : ℕ), (∀ st sent, IsQueryBoundP (W.round st sent) Counted step) →
    ∀ (counts : List ℕ) (L tg : ℕ) (x : C.Party → List (Tuple C)) (st : W.State), counts.sum ≠ 0 →
      (∀ i, i ∉ D.1 → (x i).map (·.count) = counts) →
      (∀ T, ¬ KnownTo D.1 T → ∀ i j, i ∉ D.1 → j ∉ D.1 → i ∈ C.holders T → j ∈ C.holders T →
        filledHistory K i (x i) T = filledHistory K j (x j) T) →
      ∀ (cache : HashCache C) (seen : Finset (List Bit)), DigestSaltsCovered cache seen →
      ∀ (Z : W.State × (C.Party → Option Unit) → OracleComp (LocalSpec C) Bool) (q : ℕ),
        (∀ out, IsQueryBoundP (Z out) DigestQuery q) →
        measureTVDist
          ((simulateQ (localAnswer prims) (c1Mid K D W knownE knownB names counts L tg x st >>= Z)).run' cache)
          ((simulateQ (localAnswer prims) (executePhase localRoles D
            (c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x) names
              (c1Tails K D W knownE knownB counts.sum L tg))
            (checkFunctionalities K) (checkRounds counts.sum) ((st, ⟨knownHist K D x, []⟩), 0)
            (checkAt K L tg x) >>= fun r => Z (r.1.1.1, r.2))).run' cache) ≤
          c1Error C step q seen.card counts.sum

/-- The check with no tuple. It has no round and no call in both models (`check_of_count_eq_zero`). -/
def C1ZeroStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (counts : List ℕ) (L tg : ℕ) (x : C.Party → List (Tuple C)) (st : W.State), counts.sum = 0 →
      (∀ i, i ∉ D.1 → (x i).map (·.count) = counts) →
      SameRun prims (c1Real K D W knownE knownB counts L tg x st)
        (c1Hybrid K D W knownE knownB c1Names counts L tg x st)

end ThresholdLeanXmssSecurity.RealNetworkC1s

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1s

open RealNetworkV3

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-! ## One activation of a wrapper, for each kind of call -/

section Sum

variable {p : (LocalSpec C).Domain → Prop}

/-- One reply of a wrapper is one reply of its block simulator and one tail. -/
theorem roundScheduled_answer_bound {Ia L R : Type} (D : C.Coalition) (W : Adversary C E Ia L R)
    (sims : ℕ → W.State → L → OracleComp (LocalSpec C) (W.State × R)) (names : L → R → C.Party → Prop)
    (tails : ℕ → Finset C.Party → W.State → OracleComp (LocalSpec C) W.State)
    (surv : ℕ → (C.Party → C.Party → Option (Msg E)) → (C.Party → C.Party → Option (Msg E)) → C.Party → Prop)
    (rtails : ℕ → Finset C.Party → W.State → OracleComp (LocalSpec C) W.State) (a b : ℕ)
    (hs : ∀ k st l, IsQueryBoundP (sims k st l) p a)
    (ht : ∀ k live st, IsQueryBoundP (tails k live st) p b) (s : W.State × ℕ) (l : L) :
    IsQueryBoundP ((roundScheduled D W sims names tails surv rtails).answer s l) p (a + b) := by
  refine isQueryBoundP_bind (hs s.2 s.1 l) fun x _ => ?_
  split_ifs
  · exact (isQueryBoundP_map_iff (p := p) _ _ _).2 (ht _ _ _)
  · exact isQueryBoundP_pure p _ _

/-- One round of a wrapper is one round of `W` and one tail. -/
theorem roundScheduled_round_bound {Ia L R : Type} (D : C.Coalition) (W : Adversary C E Ia L R)
    (sims : ℕ → W.State → L → OracleComp (LocalSpec C) (W.State × R)) (names : L → R → C.Party → Prop)
    (tails : ℕ → Finset C.Party → W.State → OracleComp (LocalSpec C) W.State)
    (surv : ℕ → (C.Party → C.Party → Option (Msg E)) → (C.Party → C.Party → Option (Msg E)) → C.Party → Prop)
    (rtails : ℕ → Finset C.Party → W.State → OracleComp (LocalSpec C) W.State) (a b : ℕ)
    (hr : ∀ st m, IsQueryBoundP (W.round st m) p a)
    (ht : ∀ k live st, IsQueryBoundP (rtails k live st) p b) (s : W.State × ℕ)
    (m : C.Party → C.Party → Option (Msg E)) :
    IsQueryBoundP ((roundScheduled D W sims names tails surv rtails).round s m) p (a + b) := by
  refine isQueryBoundP_bind (hr s.1 m) fun x _ => ?_
  split_ifs
  · exact (isQueryBoundP_map_iff (p := p) _ _ _).2 (ht _ _ _)
  · exact isQueryBoundP_pure p _ _

end Sum

/-- The digest calls of a functionality with one leak are the digest calls of the reply. -/
theorem runFunctionality_digestBound {I O L R Ia : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (step : ℕ)
    (hF : ∀ inputs, WeightedBound (F.run D inputs) (hybridWeight step) step)
    (hA : ∀ st l, IsQueryBoundP (A.answer st l) DigestQuery step)
    (st : A.State) (inputs : C.Party → Option I) :
    IsQueryBoundP (runFunctionality localRoles D A F st inputs) DigestQuery step := by
  let impl : QueryImpl (LocalSpec C + (L →ₒ R)) (StateT A.State (OracleComp (LocalSpec C))) :=
    (fun (t : (LocalSpec C).Domain) =>
      (StateT.lift (OracleComp.lift (OracleSpec.query t)) : StateT A.State (OracleComp (LocalSpec C)) _)) +
    (fun l => StateT.mk fun s => do
      let a ← A.answer s l
      pure (a.2, a.1))
  have hi : ∀ t s, IsQueryBoundP ((impl t).run s) DigestQuery (hybridWeight step t) := by
    intro t s
    rcases t with t | l
    · change IsQueryBoundP ((fun a => (a, s)) <$> (liftM (OracleSpec.query (spec := LocalSpec C) t) : OracleComp _ _))
        DigestQuery (hybridWeight (L := L) step (.inl t))
      rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      rcases t with u | v
      · simp [hybridWeight, DigestQuery, digestSaltProjection]
      · simp [hybridWeight]
    · change IsQueryBoundP (A.answer s l >>= fun a => pure (a.2, a.1)) DigestQuery step
      exact (isQueryBoundP_bind (hA s l) (fun a _ => isQueryBoundP_pure _ _ 0)).mono (by omega)
  have hrun := WeightedBound.simulateQ_state impl hi (hF inputs) st
  have hswap := isQueryBoundP_bind hrun (fun out _ => isQueryBoundP_pure DigestQuery (out.2, out.1) 0)
  unfold runFunctionality
  split_ifs <;> (try dsimp only)
  all_goals first
    | exact isQueryBoundP_pure DigestQuery _ step
    | simpa only [Nat.add_zero, impl, localRoles] using hswap

/-! ## The honest head makes no digest call -/

section Honest

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma mapM_expand_no_digest (K : Constants C E) (key : HashOutput) : ∀ l : List ℕ,
    IsQueryBoundP (liftComp (l.mapM fun k => elementOfHash K <$> hashQuery (C := C) (.expand key k)) (LocalSpec C))
      DigestQuery 0
  | [] => by simp only [List.mapM_nil, liftComp_pure, isQueryBoundP_pure]
  | k :: l => by
    simp only [List.mapM_cons, liftComp_bind, liftComp_map, liftComp_pure]
    refine isQueryBoundP_bind (n := 0) (m := 0) ((isQueryBoundP_map_iff _ _ _).2
      (hashQuery_no_digest _ (by simp [DigestQuery, digestSaltProjection]))) fun h _ => ?_
    exact isQueryBoundP_bind (n := 0) (m := 0) (mapM_expand_no_digest K key l) fun _ _ =>
      isQueryBoundP_pure _ _ _

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma hybrid_coinKey_no_digest (K : Constants C E) (i : C.Party) :
    DigestRunBound (coinKey K (hybridCheckBuildingBlocks K i)) := by
  unfold coinKey
  apply (DigestRunBound.of_zero RunBound.get).bind
  intro hs
  apply (DigestRunBound.of_zero (hybrid_coin_queryBound K i 2)).bind
  intro values
  apply DigestRunBound.lift
  exact localStep_digestBound (hashQuery_no_digest _ (by simp [DigestQuery, digestSaltProjection]))

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma hybrid_expand_no_digest (K : Constants C E) (key : HashOutput) (count : ℕ) :
    DigestRunBound (expand (G := CheckSpec C E) K key count) := by
  unfold expand
  exact DigestRunBound.lift (localStep_digestBound (mapM_expand_no_digest K key (List.range count)))

omit [Fintype E] [DecidableEq E] [SampleableType E] in
lemma digestRunBound_foldlM {α γ : Type} (f : α → γ → RunM C E (CheckSpec C E) α)
    (hf : ∀ a g, DigestRunBound (f a g)) : ∀ (xs : List γ) (a : α), DigestRunBound (xs.foldlM f a)
  | [], a => DigestRunBound.of_zero (RunBound.pure a)
  | g :: xs, a => by
    rw [List.foldlM_cons]
    exact (hf a g).bind fun a' => digestRunBound_foldlM f hf xs a'

lemma sliceStep_no_digest (K : Constants C E) (i : C.Party) (τ : List E) (count : ℕ)
    (a : Shares C E × Shares C E × E) (j : ℕ) :
    DigestRunBound (sliceStep K (localContext i) (hybridCheckBuildingBlocks K i) τ count a j) := by
  obtain ⟨xs, ys, V⟩ := a
  unfold sliceStep
  exact (DigestRunBound.of_zero (hybrid_extendMult_queryBound K i _)).bind fun t =>
    (hybrid_challenge_no_digest K i).bind fun r => DigestRunBound.of_zero (RunBound.pure _)

lemma halvingStep_no_digest (K : Constants C E) (i : C.Party) (width : ℕ) (a : (ℕ → E) × (ℕ → E) × E) (j : ℕ) :
    DigestRunBound (halvingStep K (localContext i) (hybridCheckBuildingBlocks K i) width a j) := by
  obtain ⟨A, B, V⟩ := a
  unfold halvingStep
  exact (DigestRunBound.of_zero (hybrid_extendMult_queryBound K i _)).bind fun t =>
    (hybrid_challenge_no_digest K i).bind fun r => DigestRunBound.of_zero (RunBound.pure _)

/-- The honest head of the check makes no digest call. Its hash calls are coin keys and expansions. -/
theorem checkHead_no_digest (K : Constants C E) (i : C.Party) (tuples : List (Tuple C)) :
    DigestRunBound (checkHead K i tuples) := by
  unfold checkHead
  refine (hybrid_coinKey_no_digest K i).bind fun key => (hybrid_expand_no_digest K key _).bind fun τ => ?_
  refine (DigestRunBound.of_zero (RunBound.lift (PartyBound.require _))).bind fun _ => ?_
  refine (digestRunBound_foldlM _ (fun a g => sliceStep_no_digest K i τ _ a g) _ _).bind fun p => ?_
  refine (digestRunBound_foldlM _ (fun a g => halvingStep_no_digest K i _ a g) _ _).bind fun p' => ?_
  refine (DigestRunBound.of_zero (hybrid_randElements_queryBound K i 2)).bind fun w => ?_
  exact (DigestRunBound.of_zero (hybrid_extendMult_queryBound K i _)).bind fun q =>
    DigestRunBound.of_zero (RunBound.pure _)

end Honest

/-! ## The bound of the head -/

section Head

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- A tail of the head makes the digest calls of one round of `W`. The search of a challenge and the
coins of the first coin make no digest call, and the head has no digest tail. -/
def C1HeadTailsDigestStatement (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg step : ℕ),
    (∀ st m, IsQueryBoundP (W.round st m) Counted step) →
    ∀ n live s, IsQueryBoundP (c1HeadTails K D W knownE knownB count L tg n live s) DigestQuery step

/-- The digest calls of the head of the check under the wrapper with no digest tail. With
`R = halvings counts.sum` they are at most `2 * (2 * R + 3) * step`. -/
theorem head_digestBound (K : Constants C E) (D : C.Coalition) (hs : C1SimsCountedStatement K D)
    (ht : C1HeadTailsDigestStatement K D) (hrt : C1RtailsCountedStatement K D) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit))
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (step : ℕ)
    (hW : ∀ st m, IsQueryBoundP (W.round st m) Counted step) (counts : List ℕ) (L tg : ℕ)
    (x : C.Party → List (Tuple C)) (st : W.State) :
    IsQueryBoundP (executePhase localRoles D
      (c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x) names
        (c1HeadTails K D W knownE knownB counts.sum L tg))
      (checkFunctionalities K) (2 * halvings counts.sum + 3) ((st, ⟨knownHist K D x, []⟩), 0) (headAt K L tg x))
      DigestQuery (2 * (2 * halvings counts.sum + 3) * step) := by
  have hround : ∀ s m, IsQueryBoundP ((relabel (withMemory W (C1Memory C E) ⟨knownHist K D x, []⟩)
      (checkReply (C := C) (E := E))).round s m) DigestQuery step := fun s m =>
    (isQueryBoundP_map_iff (p := DigestQuery) _ _ _).2 (counted_digestBound (hW s.1 m))
  have hr := roundScheduled_round_bound (p := DigestQuery) D
    (relabel (withMemory W (C1Memory C E) ⟨knownHist K D x, []⟩) (checkReply (C := C) (E := E)))
    (c1Sims K D W knownE knownB) names (c1HeadTails K D W knownE knownB counts.sum L tg) (fun _ => digestSurv D)
    (c1Rtails K D W knownE counts.sum) step step hround
    (fun n live s => counted_digestBound (hrt W knownE counts.sum step hW n live s))
  have ha := roundScheduled_answer_bound (p := DigestQuery) D
    (relabel (withMemory W (C1Memory C E) ⟨knownHist K D x, []⟩) (checkReply (C := C) (E := E)))
    (c1Sims K D W knownE knownB) names (c1HeadTails K D W knownE knownB counts.sum L tg) (fun _ => digestSurv D)
    (c1Rtails K D W knownE counts.sum) step step
    (fun n s l => counted_digestBound (hs W knownE knownB step hW n s l))
    (ht W knownE knownB counts.sum L tg step hW)
  have h := executePhase_digestBound D
    (c1WrapperWith K D W knownE knownB counts.sum (knownHist K D x) names
      (c1HeadTails K D W knownE knownB counts.sum L tg))
    (checkFunctionalities K) (step + step) hr
    (fun s inputs => runFunctionality_digestBound D _ (checkFunctionalities K) (step + step)
      (fun inputs => checkFunctionalities_queryBound K D inputs (step + step)) ha s inputs)
    (2 * halvings counts.sum + 3) ((st, ⟨knownHist K D x, []⟩), 0) (headAt K L tg x) (fun _ => 0)
    (fun i _ => checkHead_no_digest K i (x i) _)
  refine h.mono ?_
  rw [Finset.sum_const_zero, Nat.add_zero]
  exact le_of_eq (by ring)

/-- The charge of the hiding of the salted digests for the head and the round of the adversary is in
`c1Error`. -/
theorem head_slack (x step n : ℕ) (hx : x ≤ 2 * (2 * halvings n + 3) * step) :
    x + step ≤ 4 * checkRounds n * step := by
  unfold checkRounds
  nlinarith [hx, Nat.zero_le (halvings n * step), Nat.zero_le step]

end Head

end ThresholdLeanXmssSecurity.RealNetworkC1s

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1s

open RealNetworkV3

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-! ## Test 2, a wrong receiver set -/

/-- The two values of `F_coin`, with the count as `runFunctionality_coin_local` types it. -/
abbrev CoinValues (D : C.Coalition) (E : Type) :=
  Fin (firstInput fun i : C.Party => if i ∈ D.1 then (none : Option ℕ) else some 2) → E

/-- The values in an output of the functionalities of the check. -/
def coinOutput : (List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit) → Option (List E)
  | .inl (.inl values) => some values
  | _ => none

/-- The outputs of `F_coin` for the values `v` and the reply `r`. -/
def coinOutputs (D : C.Coalition) (v : CoinValues D E) (r : CheckAnswer C E) (i : C.Party) :
    Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) :=
  if i ∉ D.1 ∧ i ∈ coinReply r then some (Sum.inl (Sum.inl (List.ofFn v))) else none

/-- The normal form of a call of `F_coin` for two values from a full start, as `callPhase_eq` takes it. -/
theorem coinRun_form (K : Constants C E) (D : C.Coalition) {Ia : Type} (A : CheckAdversary C E Ia)
    (st : A.State) :
    runFunctionality localRoles D A (checkFunctionalities K) st
        (fun i => if i ∈ D.1 then none else some (Sum.inl (Sum.inl 2))) =
      liftComp ($ᵗ (CoinValues D E)) (LocalSpec C) >>= fun v =>
        A.answer st (Sum.inl (Sum.inl (List.ofFn v))) >>= fun a =>
          (pure () : OracleComp (LocalSpec C) Unit) >>= fun _ => pure (a.1, coinOutputs D v a.2) := by
  unfold checkFunctionalities
  rw [runFunctionality_sum_inl D A _ _ st (fun _ => Sum.inl 2),
    runFunctionality_sum_inl D (leftAdversary A) _ _ st (fun _ => 2),
    runFunctionality_coin_local D (leftAdversary (leftAdversary A)) st _ (fun i hi => by simp [hi])]
  simp only [leftAdversary, map_bind, bind_assoc, pure_bind, map_pure]
  refine bind_congr fun v => bind_congr fun a => ?_
  congr 2
  funext i
  unfold coinOutputs
  rcases a with ⟨s, (r | r) | r⟩ <;> by_cases hi : i ∈ D.1 <;>
    simp [hi, coinReply] <;> exact Finset.notMem_empty i

omit [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- The premise `hnames` of `callPhase_tail` at `F_coin`, for a `names` that reports the receivers. -/
theorem coin_hnames (D : C.Coalition) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (hn : NamesReceivers D names) (v : CoinValues D E) (r : CheckAnswer C E) (j : C.Party) (hj : j ∉ D.1) :
    ((coinOutputs D v r j).bind coinOutput).isSome ↔ names (Sum.inl (Sum.inl (List.ofFn v))) r j := by
  rw [hn _ _ j hj]
  unfold coinOutputs
  by_cases h : j ∈ coinReply r <;> simp [hj, h, c1Names, coinOutput]

/-- Test 1, the wrapper side. For each adversary `W`, the tail in the reply to `F_coin` at position `k`
is the tail after the phase of this call. It runs exactly when the output of `F_coin` is a partial
abort. -/
theorem coinPhase_tail (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg : ℕ)
    (hist : C.Party → C.Term → List Bit) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (hn : NamesReceivers D names) (fuel : ℕ) (st : W.State × C1Memory C E) (k : ℕ) :
    SameRun prims
      (RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names
          (c1Tails K D W knownE knownB count L tg)) (checkFunctionalities K) (fuel + 1) (st, k)
        (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput))
      (RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
          (checkFunctionalities K) (fuel + 1) (st, k) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput) >>=
        fun r => if PartialOut D r.2 then
          (fun s' => ((s', r.1.2), r.2)) <$> c1Tails K D W knownE knownB count L tg k (liveSet D r.2) r.1.1
        else pure r) := by
  have h := RealNetworkGP.callPhase_tail D (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2))
    (fun _ => coinOutput) (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C))
    (fun v => Sum.inl (Sum.inl (List.ofFn v))) (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit))
    (fun v r _ => coinOutputs D v r) prims
    (relabel (withMemory W (C1Memory C E) ⟨hist, []⟩) (checkReply (C := C) (E := E)))
    (c1Sims K D W knownE knownB) names (c1Tails K D W knownE knownB count L tg)
    (fun A st => coinRun_form K D A st) (fun v r _ j hj => coin_hnames D names hn v r j hj) fuel st k
  rw [RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput)
      (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C)) (fun v => Sum.inl (Sum.inl (List.ofFn v)))
      (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit)) (fun v r _ => coinOutputs D v r) _
      (fun st => coinRun_form K D _ st),
    RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput)
      (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C)) (fun v => Sum.inl (Sum.inl (List.ofFn v)))
      (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit)) (fun v r _ => coinOutputs D v r) _
      (fun st => coinRun_form K D _ st)] at h
  rw [RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput)
      (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C)) (fun v => Sum.inl (Sum.inl (List.ofFn v)))
      (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit)) (fun v r _ => coinOutputs D v r) _
      (fun st => coinRun_form K D _ st),
    RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput)
      (liftComp ($ᵗ (CoinValues D E)) (LocalSpec C)) (fun v => Sum.inl (Sum.inl (List.ofFn v)))
      (fun _ _ => (pure () : OracleComp (LocalSpec C) Unit)) (fun v r _ => coinOutputs D v r) _
      (fun st => coinRun_form K D _ st)]
  exact h

/-! ## Test 1, the adversary that counts its rounds -/

end ThresholdLeanXmssSecurity.RealNetworkC1s

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1s

open RealNetworkV3

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The head of a check with a tuple takes exactly `2 * halvings count + 3` calls on each path with no
abort. They are the first coin, two calls for each step, `F_rand` and `F_extendMult`. -/
def HeadTimedStatement (K : Constants C E) : Prop :=
  ∀ (L tg : ℕ) (i : C.Party) (tuples : List (Tuple C)), (tuples.map (·.count)).sum ≠ 0 →
    Timed (2 * halvings (tuples.map (·.count)).sum + 3)
      ((checkHead K i tuples).run ⟨filledHistory K i tuples, L, tg⟩).run

/-- The check in the hybrid model is its head and then its rest, for each adversary. An operator with
no output of the head does not start the rest. -/
def HybridCutStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (A : CheckAdversary C E Ia) (counts : List ℕ) (L tg : ℕ) (x : C.Party → List (Tuple C))
    (st : A.State), counts.sum ≠ 0 → (∀ i, i ∉ D.1 → (x i).map (·.count) = counts) →
    SameRun prims
      (executePhase localRoles D A (checkFunctionalities K) (checkRounds counts.sum) st (checkAt K L tg x))
      (executePhase localRoles D A (checkFunctionalities K) (2 * halvings counts.sum + 3) st (headAt K L tg x) >>=
        fun r => executePhase localRoles D A (checkFunctionalities K) 5 r.1
          (fun i => (r.2 i).elim failure (restAt K i)))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- The live operators of a phase start with one computation `oa` of `H`. When an honest operator is
live, the phase is `oa` one time and then the phase on its result. -/
def HoistStatement (prims : Primitives) (D : C.Coalition) : Prop :=
  ∀ {Ia I O L R α γ σ : Type} (A : Adversary C E Ia L R) (F : Functionality C I O L R) (fuel : ℕ)
    (st : A.State) (oa : OracleComp (RoSpec C) γ) (inputs : C.Party → Option σ)
    (next : C.Party → γ → σ → PartyM C E (CallSpec I O) α), (∃ i ∉ D.1, (inputs i).isSome) →
    SameRun prims
      (executePhase localRoles D A F fuel st fun i =>
        (inputs i).elim failure fun hs => oracleStep oa >>= fun c => next i c hs)
      (liftComp oa (LocalSpec C) >>= fun c =>
        executePhase localRoles D A F fuel st fun i => (inputs i).elim failure fun hs => next i c hs)

/-- The real `Coin` of `count` values on the drawn PRSS outputs `rnd`. -/
def realCoinPhase {I O L R Ia : Type} (K : Constants C E) (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R) (rnd : C.Party → PrssOutput C E) (count fuel : ℕ) (st : A.State)
    (inputs : C.Party → Option Unit) : OracleComp (LocalSpec C) (A.State × (C.Party → Option (ℕ → E))) :=
  executePhase localRoles D A F fuel st fun i =>
    (inputs i).elim failure fun _ => openSh K (localContext i) (conv K (localContext i) (rnd i).1) count

/-- The block hop of `Coin` from a full start, at position `k` of the schedule. The real coin opens the
drawn PRSS output of the label. The hybrid coin is a call of `F_coin` with the wrapper and no tail. -/
def CoinHopStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count : ℕ) (hist : C.Party → C.Term → List Bit)
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (k fuel fuel' : ℕ) (s : W.State × C1Memory C E),
      SameRun prims
        (do
          let fresh ← liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C)
          let freshPair ← liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C)
          (fun r => (r.1, fun i => (r.2 i).map (vector 2))) <$>
            realCoinPhase K D W noFunctionality (frandShare D 2 (knownE k).1 (knownE k).2 fresh freshPair) 2
              (fuel + 1) s.1 (fun _ => some ()))
        ((fun r => (r.1.1.1, r.2)) <$> RealNetworkGP.callPhase D
          (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
          (checkFunctionalities K) (fuel' + 1) (s, k) (fun _ => Sum.inl (Sum.inl 2)) (fun _ => coinOutput))

/-- The shares in an output of the functionalities of the check. -/
def extendOutput : (List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit) → Option (Shares C E)
  | .inl (.inr z) => some z
  | _ => none

/-- The real `extendMult` at operator `i`, as `drawnCheckBuildingBlocks` runs it on the drawn PRSS
output `rnd i`. It returns the output and the state of the run. -/
def realExtendProg (K : Constants C E) (rnd : C.Party → PrssOutput C E) (i : C.Party)
    (p : List (Product C E) × RunState C) : PartyM C E RealSpec (Shares C E × RunState C) :=
  (do
    let _ ← freshLabel
    reshare K (localContext i) (elementCodec K) (rnd i)
      (fun g => match p.1[g]? with | some q => productShare K (localContext i) q | none => 0) p.1.length).run p.2

/-- The state of the run of operator `i` after a call of `F_extendMult` for two products with the
output `z`. -/
def extendState (K : Constants C E) (i : C.Party) (hs : RunState C) (z : Shares C E) : RunState C :=
  ⟨recordHistory K i hs.history z 2, hs.label + 1, hs.tag⟩

/-- The block hop of `extendMult` for two products from a full start, at position `k` of the schedule.
Both sides return the output and the state of the run. -/
def ExtendHopStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count : ℕ) (hist : C.Party → C.Term → List Bit)
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop), NamesReceivers D names →
    ∀ (k fuel fuel' : ℕ) (s : W.State × C1Memory C E) (products : C.Party → List (Product C E))
      (hs : C.Party → RunState C), (∀ i, i ∉ D.1 → (products i).length = 2) →
      SameRun prims
        (do
          let fresh ← liftComp ($ᵗ (C.Term → Fin 2 → E)) (LocalSpec C)
          let freshPair ← liftComp ($ᵗ (C.Pair → Fin 2 → E)) (LocalSpec C)
          executePhase localRoles D W noFunctionality (fuel + 1) s.1 fun i =>
            realExtendProg K (frandShare D 2 (knownE k).1 (knownE k).2 fresh freshPair) i (products i, hs i))
        ((fun r => (r.1.1.1, r.2)) <$> RealNetworkGP.callPhase D
          (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
          (checkFunctionalities K) (fuel' + 1) (s, k) (fun i => Sum.inl (Sum.inr (products i)))
          (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z)))

end ThresholdLeanXmssSecurity.RealNetworkC1s

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1s

open RealNetworkV3

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-! ## The cut of a check with any building blocks -/

section Cut

variable [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}

/-- The check with the building blocks `bb` up to the masked multiplication of the randomization. It
returns the last elements `A 0` and `B 0`, the claim `D`, the mask `w` and the output `q`. -/
def checkHeadOf (K : Constants C E) (ctx : Context C) (bb : CheckBuildingBlocks C E G) (tuples : List (Tuple C)) :
    RunM C E G (E × E × E × Shares C E × Shares C E) := do
  let count := (tuples.map (·.count)).sum
  let τ ← expand K (← coinKey K bb) (coins count)
  StateT.lift (require (∀ b < sliceBits, τ.getD b 0 ≠ 0))
  let p ← (List.range sliceBits).foldlM (sliceStep K ctx bb τ count)
    ((fun T k => wordWeightOf K τ count k * liftedPart tuples (·.x) T k : Shares C E), liftedPart tuples (·.y),
      conv K ctx (claimOf K τ count (liftedPart tuples (·.z))) 0)
  let p' ← (List.range (halvings count - sliceBits)).foldlM (halvingStep K ctx bb (sliceWidth count))
    (conv K ctx p.1, conv K ctx p.2.1, p.2.2)
  let w ← bb.randElements 2
  let wa := conv K ctx w.1 0
  let wb := conv K ctx w.1 1
  let q ← bb.extendMult [.shamir (fun _ => wa) (fun _ => wb) 1,
    .shamir (fun _ => wa + p'.1 0) (fun _ => wb + p'.2.1 0) 1]
  pure (p'.1 0, p'.2.1 0, p'.2.2, w.1, q)

/-- The check with the building blocks `bb` from the salts of the digests. -/
def checkRestOf (K : Constants C E) (ctx : Context C) (bb : CheckBuildingBlocks C E G)
    (v : E × E × E × Shares C E × Shares C E) : RunM C E G Unit := do
  let wa := conv K ctx v.2.2.2.1 0
  let wb := conv K ctx v.2.2.2.1 1
  let q₀ := conv K ctx v.2.2.2.2 0
  let q₂ := conv K ctx v.2.2.2.2 1
  let salts ← bb.randBits 256
  compareDigests ctx salts.1
  let r ← challenge K bb
  let opened ← StateT.lift (openSh K ctx (fun k => match k with
    | 0 => wa + r * (wa + v.1)
    | 1 => wb + r * (wb + v.2.1)
    | _ => q₀ + (v.2.2.1 + q₀ + q₂) * r + q₂ * r ^ 2) 3)
  StateT.lift (require (opened 0 * opened 1 = opened 2))

/-- A check with a tuple is its head and then its rest, for each choice of the building blocks. -/
theorem check_headOf_restOf (K : Constants C E) (ctx : Context C) (bb : CheckBuildingBlocks C E G)
    (tuples : List (Tuple C)) (h : (tuples.map (·.count)).sum ≠ 0) :
    check K ctx bb tuples = checkHeadOf K ctx bb tuples >>= checkRestOf K ctx bb := by
  rw [check_eq K ctx bb tuples h]
  simp only [checkHeadOf, checkRestOf, bind_assoc, pure_bind]
  refine bind_congr fun key => bind_congr fun τ => bind_congr fun _ => bind_congr fun p =>
    bind_congr fun p' => ?_
  obtain ⟨A, B, V⟩ := p'
  rfl

end Cut

section RealCut

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The head of the real check on drawn values at operator `i`. -/
def drawnHeadAt {m : ℕ} (K : Constants C E) (D : C.Coalition) (L tg : ℕ)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (tables : DrawTables C E m)
    (x : C.Party → List (Tuple C)) (i : C.Party) :
    PartyM C E RealSpec ((E × E × E × Shares C E × Shares C E) × RunState C) :=
  (checkHeadOf K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB tables i) (x i)).run
    ⟨filledHistory K i (x i), L, tg⟩

/-- The rest of the real check on drawn values at operator `i`, from the output of its head. -/
def drawnRestAt {m : ℕ} (K : Constants C E) (D : C.Coalition) (L : ℕ)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (tables : DrawTables C E m) (i : C.Party)
    (p : (E × E × E × Shares C E × Shares C E) × RunState C) : PartyM C E RealSpec Unit :=
  (checkRestOf K (localContext i) (drawnCheckBuildingBlocks K D L knownE knownB tables i) p.1).run' p.2

/-- The head of the real check on drawn values takes exactly `2 * halvings count + 2` rounds on each
path with no abort. They are the first coin, two rounds for each step, and the masked multiplication.
The draw of the mask is local. -/
def RealHeadTimedStatement (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {m : ℕ} (L tg : ℕ) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (tables : DrawTables C E m)
    (x : C.Party → List (Tuple C)) (i : C.Party), ((x i).map (·.count)).sum ≠ 0 →
    Timed (2 * halvings ((x i).map (·.count)).sum + 2) (drawnHeadAt K D L tg knownE knownB tables x i).run

/-- The real check on drawn values is its head and then its rest. The head has `2 * R + 2` steps and
the rest has 6, which are the 3 rounds of the rest and 3 spare steps of `checkRounds`. -/
def RealCutStatement (prims : Primitives) (K : Constants C E) (D : C.Coalition) : Prop :=
  ∀ {Ia : Type} (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (counts : List ℕ) (L tg : ℕ)
    (tables : DrawTables C E (RealNetworkV3.checkLabels counts.sum)) (x : C.Party → List (Tuple C))
    (st : W.State), counts.sum ≠ 0 → (∀ i, i ∉ D.1 → (x i).map (·.count) = counts) →
    SameRun prims
      (executePhase localRoles D W noFunctionality (checkRounds counts.sum) st
        (drawnCheckAt K D L tg knownE knownB tables x))
      (executePhase localRoles D W noFunctionality (2 * halvings counts.sum + 2) st
          (drawnHeadAt K D L tg knownE knownB tables x) >>= fun r =>
        executePhase localRoles D W noFunctionality 6 r.1
          (fun i => (r.2 i).elim failure (drawnRestAt K D L knownE knownB tables i)))

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The head in the hybrid model is `checkHeadOf` with the building blocks of the hybrid model. -/
theorem checkHead_eq (K : Constants C E) (i : C.Party) (tuples : List (Tuple C)) :
    checkHead K i tuples = checkHeadOf K (localContext i) (hybridCheckBuildingBlocks K i) tuples := rfl

end RealCut

/-! ## The tail in the reply to `F_extendMult` -/

section Extend

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The inputs of a call from a full start. -/
abbrev fullInputs {I : Type} (D : C.Coalition) (inp : C.Party → I) : C.Party → Option I :=
  fun i => if i ∈ D.1 then none else some (inp i)

/-- The outputs of `F_extendMult` for the products `products`, the reply `r` and the fresh table. -/
def extendOutputs (K : Constants C E) (D : C.Coalition) (products : C.Party → List (Product C E))
    (r : CheckAnswer C E) (fresh : C.Term → Fin (firstInput (fullInputs D products)).length → E) (i : C.Party) :
    Option ((List E ⊕ Shares C E) ⊕ (PrssOutput C E ⊕ PrssOutput C Bit)) :=
  (multFinish D (firstInput (fullInputs D products)).length (filler K .peer)
    (fun g => extendTotal K D (fullInputs D products) g + (extendReply r).1 g) (extendReply r).2.1
    (extendReply r).2.2.1 (extendReply r).2.2.2 fresh i).map fun z => Sum.inl (Sum.inr z)

/-- The normal form of a call of `F_extendMult` from a full start, as `callPhase_eq` takes it. -/
theorem extendRun_form (K : Constants C E) (D : C.Coalition) {Ia : Type} (A : CheckAdversary C E Ia)
    (st : A.State) (products : C.Party → List (Product C E)) :
    runFunctionality localRoles D A (checkFunctionalities K) st
        (fun i => if i ∈ D.1 then none else some (Sum.inl (Sum.inr (products i)))) =
      (pure () : OracleComp (LocalSpec C) Unit) >>= fun _ =>
        A.answer st (Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products)))) >>= fun a =>
          liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C) >>=
            fun fresh => pure (a.1, extendOutputs K D products a.2 fresh) := by
  unfold checkFunctionalities
  rw [runFunctionality_sum_inl D A _ _ st (fun i => Sum.inr (products i)),
    runFunctionality_sum_inr D (leftAdversary A) _ _ st products,
    runFunctionality_extend_local K D (rightAdversary (leftAdversary A)) st _ (fun i hi => by simp [hi])]
  simp only [leftAdversary, rightAdversary, map_bind, bind_assoc, pure_bind, map_pure]
  refine bind_congr fun a => bind_congr fun fresh => ?_
  congr 2
  funext i
  unfold extendOutputs
  rcases a with ⟨s, (r | r) | r⟩ <;> rw [Option.map_map] <;> rfl

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The premise `hnames` of `callPhase_tail` at `F_extendMult`, for a `names` that reports the receivers. -/
theorem extend_hnames (K : Constants C E) (D : C.Coalition)
    (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop) (hn : NamesReceivers D names)
    (products : C.Party → List (Product C E)) (hs : C.Party → RunState C) (r : CheckAnswer C E)
    (fresh : C.Term → Fin (firstInput (fullInputs D products)).length → E) (j : C.Party) (hj : j ∉ D.1) :
    ((extendOutputs K D products r fresh j).bind
      fun o => (extendOutput o).map fun z => (z, extendState K j (hs j) z)).isSome ↔
      names (Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products)))) r j := by
  rw [hn _ _ j hj]
  unfold extendOutputs multFinish
  by_cases h : j ∈ (extendReply r).2.2.2 <;> simp [hj, h, c1Names, extendOutput]

/-- For each adversary `W` and each `tails`, the tail in the reply to `F_extendMult` at position `k`
is the tail after the phase of this call. It runs exactly when the output is a partial abort. -/
theorem extendPhase_tail (prims : Primitives) (K : Constants C E) (D : C.Coalition) {Ia : Type}
    (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count : ℕ)
    (hist : C.Party → C.Term → List Bit) (names : CheckLeak C E → CheckAnswer C E → C.Party → Prop)
    (hn : NamesReceivers D names)
    (tails : ℕ → Finset C.Party → W.State × C1Memory C E → OracleComp (LocalSpec C) (W.State × C1Memory C E))
    (products : C.Party → List (Product C E)) (hs : C.Party → RunState C) (fuel : ℕ)
    (st : W.State × C1Memory C E) (k : ℕ) :
    SameRun prims
      (RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names tails)
        (checkFunctionalities K) (fuel + 1) (st, k) (fun i => Sum.inl (Sum.inr (products i)))
        (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z)))
      (RealNetworkGP.callPhase D (c1WrapperWith K D W knownE knownB count hist names RealNetworkGP.noTails)
          (checkFunctionalities K) (fuel + 1) (st, k) (fun i => Sum.inl (Sum.inr (products i)))
          (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z)) >>=
        fun r => if PartialOut D r.2 then
          (fun s' => ((s', r.1.2), r.2)) <$> tails k (liveSet D r.2) r.1.1
        else pure r) := by
  have h := RealNetworkGP.callPhase_tail D (checkFunctionalities K) (fun i => Sum.inl (Sum.inr (products i)))
    (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z))
    (pure () : OracleComp (LocalSpec C) Unit)
    (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
    (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
    (fun _ r fresh => extendOutputs K D products r fresh) prims
    (relabel (withMemory W (C1Memory C E) ⟨hist, []⟩) (checkReply (C := C) (E := E)))
    (c1Sims K D W knownE knownB) names tails
    (fun A st => extendRun_form K D A st products)
    (fun _ r fresh j hj => extend_hnames K D names hn products hs r fresh j hj) fuel st k
  rw [RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun i => Sum.inl (Sum.inr (products i)))
      (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z))
      (pure () : OracleComp (LocalSpec C) Unit)
      (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
      (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
      (fun _ r fresh => extendOutputs K D products r fresh) _ (fun st => extendRun_form K D _ st products),
    RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun i => Sum.inl (Sum.inr (products i)))
      (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z))
      (pure () : OracleComp (LocalSpec C) Unit)
      (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
      (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
      (fun _ r fresh => extendOutputs K D products r fresh) _ (fun st => extendRun_form K D _ st products)] at h
  rw [RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun i => Sum.inl (Sum.inr (products i)))
      (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z))
      (pure () : OracleComp (LocalSpec C) Unit)
      (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
      (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
      (fun _ r fresh => extendOutputs K D products r fresh) _ (fun st => extendRun_form K D _ st products),
    RealNetworkGP.callPhase_eq D (checkFunctionalities K) (fun i => Sum.inl (Sum.inr (products i)))
      (fun i o => (extendOutput o).map fun z => (z, extendState K i (hs i) z))
      (pure () : OracleComp (LocalSpec C) Unit)
      (fun _ => Sum.inl (Sum.inr (extendView K D.1 (fullInputs D products))))
      (fun _ _ => liftComp ($ᵗ (C.Term → Fin (firstInput (fullInputs D products)).length → E)) (LocalSpec C))
      (fun _ r fresh => extendOutputs K D products r fresh) _ (fun st => extendRun_form K D _ st products)]
  exact h

end Extend

end ThresholdLeanXmssSecurity.RealNetworkC1s

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1q

open RealNetworkV3 RealNetworkC1s

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- A result of a simulated run is a result of the run. -/
theorem fst_mem_support_run (prims : Primitives) {α : Type} (oa : OracleComp (LocalSpec C) α)
    (cache : HashCache C) (z : α × HashCache C)
    (hz : z ∈ support ((simulateQ (localAnswer prims) oa).run cache)) : z.1 ∈ support oa :=
  support_simulateQ_run'_subset (localAnswer prims) oa cache (by
    simp only [StateT.run'_eq, support_map, Set.mem_image]; exact ⟨z, hz, rfl⟩)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
theorem exists_of_mem_support_map {α β : Type} (f : α → β) (oa : OracleComp (LocalSpec C) α) (y : β)
    (h : y ∈ support (f <$> oa)) : ∃ x ∈ support oa, f x = y :=
  (Set.mem_image _ _ _).1 ((support_map _ _).subst (motive := fun S => y ∈ S) h)

omit [Fintype E] in
/-- Each tail of the wrapper keeps the memory. -/
theorem c1Tails_memory {Ia : Type} (K : Constants C E) (D : C.Coalition) (W : Adversary C E Ia PEmpty PEmpty)
    (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg n : ℕ) (live : Finset C.Party)
    (s : W.State × C1Memory C E) :
    ∀ y ∈ support (c1Tails K D W knownE knownB count L tg n live s), y.2 = s.2 := by
  intro y hy
  unfold c1Tails at hy
  split_ifs at hy <;> simp only [support_map, Set.mem_image, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hy
  all_goals first
    | (subst hy; rfl)
    | (obtain ⟨x, -, rfl⟩ := hy; rfl)
    | (obtain ⟨x, -, hy⟩ := hy
       split_ifs at hy <;> simp only [support_map, Set.mem_image, support_pure, Set.mem_singleton_iff] at hy
       all_goals first | (subst hy; rfl) | (obtain ⟨x, -, rfl⟩ := hy; rfl))

end ThresholdLeanXmssSecurity.RealNetworkC1q

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkALP

open RealNetworkV3 RealNetworkC1s

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP

variable {C : Committee} {E : Type}

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-! ## The count of the cells before a check -/

/-- The calls of a party program in the domain `P` of local calls. Rounds and calls of a functionality
are not local calls. -/
def PartyCalls {ι : Type} {G : OracleSpec ι} (P : (LocalSpec C).Domain → Prop) :
    (PartySpec C E G).Domain → Prop
  | .inl (.inl q) => P q
  | _ => False

/-! ## The budget -/

end ThresholdLeanXmssSecurity.RealNetworkALP

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkALP

open RealNetworkV3 RealNetworkC1s

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP

variable {C : Committee} {E : Type}

/-! ## The bound of a phase at the domain of the digest calls -/

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-! ## Test 3, the replay of the challenge search -/

section Replay

variable {Ia : Type}

omit [Fintype E] [DecidableEq E] in
/-- The tail of `Coin` makes the counted calls of one round of the adversary. -/
theorem coinTail_counted {L R : Type} (K : Constants C E) (D : C.Coalition) (A : Adversary C E Ia L R) (step : ℕ)
    (hr : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step) (known : Shares C E)
    (knownPairs : C.Party → C.Party → ℕ → E) (count : ℕ) (live : Finset C.Party) (st : A.State) :
    IsQueryBoundP (RealNetworkC1s.coinTail K D A known knownPairs count live st) Counted step := by
  unfold RealNetworkC1s.coinTail
  exact two_samples_counted _ _ _ step fun _ _ => round_fst_counted A step hr st _

omit [Fintype E] [DecidableEq E] in
/-- The tail of a peer reshare makes the counted calls of one round of the adversary. -/
theorem reshareTail_counted {L R : Type} (K : Constants C E) (D : C.Coalition) (A : Adversary C E Ia L R)
    (step : ℕ) (hr : ∀ st sent, IsQueryBoundP (A.round st sent) Counted step) (known : Shares C E)
    (knownPairs : C.Party → C.Party → ℕ → E) (count : ℕ) (live : Finset C.Party) (st : A.State) :
    IsQueryBoundP (RealNetworkC1s.reshareTail K D (elementCodec K) A known knownPairs count live st) Counted
      step := by
  unfold RealNetworkC1s.reshareTail
  exact two_samples_counted _ _ _ step fun _ _ => round_fst_counted A step hr st _

end Replay

end ThresholdLeanXmssSecurity.RealNetworkALP

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1p

open RealNetworkV3 RealNetworkC1s RealNetworkRC RealNetworkALP

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP

variable {C : Committee} {E : Type}

section Generic

variable {κ β : Type} {spec : OracleSpec κ} {p : κ → Prop} [DecidablePred p]

/-- A sequence of `N` computations with at most `n` calls of `p` each makes at most `N * n` calls. -/
theorem isQueryBoundP_sequenceFin_le {n : ℕ} :
    ∀ {N : ℕ} (f : Fin N → OracleComp spec β), (∀ i, IsQueryBoundP (f i) p n) →
      IsQueryBoundP (OverPermutation.sequenceFin f) p (N * n)
  | 0, f, _ => by simp [OverPermutation.sequenceFin]
  | N + 1, f, h => by
    simp only [OverPermutation.sequenceFin]
    refine (isQueryBoundP_bind (h 0) fun _ _ => isQueryBoundP_bind (m := 0)
      (isQueryBoundP_sequenceFin_le (fun i : Fin N => f i.succ) fun i => h i.succ) fun _ _ =>
        isQueryBoundP_pure _ _ 0).mono ?_
    rw [Nat.succ_mul]
    omega

/-- A map over a list with at most `n` calls of `p` for each element. -/
theorem isQueryBoundP_mapM_le {δ : Type} {n : ℕ} (f : δ → OracleComp spec β) :
    ∀ (l : List δ), (∀ x, IsQueryBoundP (f x) p n) → IsQueryBoundP (l.mapM f) p (l.length * n)
  | [], _ => by simp
  | x :: l, h => by
    rw [List.mapM_cons]
    refine (isQueryBoundP_bind (h x) fun _ _ => isQueryBoundP_bind (m := 0) (isQueryBoundP_mapM_le f l h)
      fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_
    rw [List.length_cons, Nat.succ_mul]
    omega

end Generic

section Digest

variable {P : (LocalSpec C).Domain → Prop} [DecidablePred P]

/-- A digest of a live holder makes one digest call. -/
theorem liveCol_digest (live : C.Party → Prop) (salts : C.Party → Shares C Bit) (hist : C.Party → C.Term → List Bit)
    (T : C.Term) (i : C.Party) : IsQueryBoundP (liveCol live salts hist T i) DigestQuery 1 := by
  unfold liveCol
  split_ifs
  · exact oneDigestQuery_digestBound _ _
  · exact isQueryBoundP_pure _ _ _

end Digest

section Parts

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

omit [Fintype E] [DecidableEq E] [SampleableType E] in
omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The coin simulator makes the counted calls of one reply and one round of its adversary. -/
theorem coinSimAnswer_counted [SampleableType E] (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E ℕ Unit (Shares C E × (C.Party → C.Party → ℕ → E))) (step : ℕ)
    (ha : ∀ st, IsQueryBoundP (A.answer st ()) Counted 0) (hr : ∀ st m, IsQueryBoundP (A.round st m) Counted step)
    (n : ℕ) (vals : List E) (st : A.State) : IsQueryBoundP (coinSimAnswer K D A n vals st) Counted step := by
  unfold coinSimAnswer
  refine (isQueryBoundP_bind (n := 0) (m := step) (ha st) fun a _ => ?_).mono (by omega)
  exact two_samples_counted _ _ _ step fun _ _ =>
    (isQueryBoundP_bind (m := 0) (hr _ _) fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The peer-reshare simulator makes the counted calls of one reply and one round of its adversary. -/
theorem peerSimAnswer_counted {I M : Type} [Field M] [SampleableType M] (K : Constants C E) (D : C.Coalition)
    (A : Adversary C E I Unit (Shares C M × (C.Party → C.Party → ℕ → M))) (codec : Codec C E M) (step : ℕ)
    (ha : ∀ st, IsQueryBoundP (A.answer st ()) Counted 0) (hr : ∀ st m, IsQueryBoundP (A.round st m) Counted step)
    (n : ℕ) (st : A.State) : IsQueryBoundP (peerSimAnswer K D A codec n st) Counted step := by
  unfold peerSimAnswer
  refine (isQueryBoundP_bind (n := 0) (m := step) (ha st) fun a _ => ?_).mono (by omega)
  exact two_samples_counted _ _ _ step fun _ _ =>
    (isQueryBoundP_bind (m := 0) (hr _ _) fun _ _ => isQueryBoundP_pure _ _ 0).mono (by omega)

omit [Fintype E] [DecidableEq E] in
/-- A part bound of the counted calls. A block simulator makes the counted calls of one round of `W`. -/
theorem c1SimsCounted (K : Constants C E) (D : C.Coalition) : C1SimsCountedStatement K D := by
  intro Ia W knownE knownB step hr n s l
  unfold c1Sims
  rcases l with (values | products) | (u | u)
  · exact (isQueryBoundP_map_iff _ _ _).2 (coinSimAnswer_counted K D (frandAdv W (knownE n) s.1) step
      (fun _ => isQueryBoundP_pure _ _ 0) hr values.length values s.1)
  · exact (isQueryBoundP_map_iff _ _ _).2 (peerSimAnswer_counted K D (frandAdv (I := Ia) W (knownE n) s.1)
      (elementCodec K) step (fun _ => isQueryBoundP_pure _ _ 0) hr 2 s.1)
  · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_pure _ _ _

omit [Fintype E] [DecidableEq E] in
/-- A part bound of the counted calls. The tail of the digest round makes one round of `W`. -/
theorem c1RtailsCounted (K : Constants C E) (D : C.Coalition) : C1RtailsCountedStatement K D := by
  intro Ia W knownE count step hr n live s
  unfold c1Rtails
  split_ifs
  · exact (isQueryBoundP_map_iff _ _ _).2 (coinTail_counted K D W step hr _ _ _ _ _)
  · exact isQueryBoundP_pure _ _ _

omit [Fintype E] in
/-- A tail at a position other than the digest round. It is the first coin or the search of a challenge,
then at most one round of `W`. -/
theorem c1Tails_bound_of_ne {P : (LocalSpec C).Domain → Prop} [DecidablePred P] {Ia : Type} (K : Constants C E)
    (D : C.Coalition) (W : Adversary C E Ia PEmpty PEmpty) (knownE : ℕ → Shares C E × (C.Party → C.Party → ℕ → E))
    (knownB : Shares C Bit × (C.Party → C.Party → ℕ → Bit)) (count L tg step x y B : ℕ)
    (hco : ∀ known knownPairs live st, IsQueryBoundP (RealNetworkC1s.coinTail K D W known knownPairs 2 live st) P step)
    (hre : ∀ known knownPairs live st,
      IsQueryBoundP (RealNetworkC1s.reshareTail K D (elementCodec K) W known knownPairs 2 live st) P step)
    (hstart : ∀ values, IsQueryBoundP (liftComp (startQuery K tg L values (coins count)) (LocalSpec C)) P x)
    (hchallenge : ∀ label values, IsQueryBoundP (liftComp (challengeQuery K tg label values) (LocalSpec C)) P y)
    (hx : x + step ≤ B) (hy : y + step ≤ B) (n : ℕ) (live : Finset C.Party) (s : W.State × C1Memory C E)
    (hn : n ≠ 2 * halvings count + 2) :
    IsQueryBoundP (c1Tails K D W knownE knownB count L tg n live s) P B := by
  unfold c1Tails
  split_ifs
  · refine (isQueryBoundP_bind (hstart _) fun τ _ => ?_).mono hx
    split_ifs
    · exact (isQueryBoundP_map_iff _ _ _).2 (hre _ _ _ _)
    · exact isQueryBoundP_pure _ _ _
  · exact isQueryBoundP_pure _ _ _
  · exact ((isQueryBoundP_map_iff _ _ _).2 (hco _ _ _ _)).mono (by omega)
  · refine (isQueryBoundP_bind (hchallenge _ _) fun r _ => ?_).mono hy
    split_ifs
    · exact (isQueryBoundP_map_iff _ _ _).2 (hre _ _ _ _)
    · exact isQueryBoundP_pure _ _ _

/-- The digest budget of a tail of the head. It is one round of `W`. -/
theorem c1HeadTailsDigest (K : Constants C E) (D : C.Coalition) : C1HeadTailsDigestStatement K D := by
  intro Ia W knownE knownB count L tg step hr n live s
  unfold c1HeadTails
  split_ifs with hn
  · exact isQueryBoundP_pure _ _ _
  · exact c1Tails_bound_of_ne K D W knownE knownB count L tg step 0 0 _
      (fun _ _ _ _ => counted_digestBound (coinTail_counted K D W step hr _ _ _ _ _))
      (fun _ _ _ _ => counted_digestBound (reshareTail_counted K D W step hr _ _ _ _ _))
      (fun _ => startQuery_no_digest K tg L _ _) (fun _ _ => wrapperChallenge_no_digest K tg _ _)
      (by omega) (by omega) n live s hn

end Parts

end ThresholdLeanXmssSecurity.RealNetworkC1p

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkC1p

open RealNetworkV3 RealNetworkC1s RealNetworkRC RealNetworkALP

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]
attribute [local instance] inhabitedField

/-- The bound of the digest calls of the head, with each part bound proved. -/
abbrev head_digestBound_proved (K : Constants C E) (D : C.Coalition) :=
  @head_digestBound C E _ _ _ _ _ K D (c1SimsCounted K D) (c1HeadTailsDigest K D) (c1RtailsCounted K D)

end ThresholdLeanXmssSecurity.RealNetworkC1p

end

end

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1s.check_head_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1s.check_head_rest

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1s.head_digestBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1s.head_digestBound

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1s.head_slack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1s.head_slack

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1s.coinPhase_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1s.coinPhase_tail

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1s.check_headOf_restOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1s.check_headOf_restOf

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1s.extendPhase_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1s.extendPhase_tail

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkALP.reshareTail_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkALP.reshareTail_counted

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1p.c1SimsCounted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1p.c1SimsCounted

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1p.c1RtailsCounted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1p.c1RtailsCounted

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkC1p.c1HeadTailsDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkC1p.c1HeadTailsDigest
