import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.SeedTouch

/-!
# The steps from the seeds of the hidden terms to `CompHit`

`CompHit` bounds a counted call at a PRF cell under the seed of a hidden term in `compRun`. This file
replaces the echo hashes of the honest pairs by lists, moves all hidden seeds by one common scalar,
and states the statements on the world that remain.

* `listRun` is `compRun` with the list program `listSuffix`. An honest operator asks no shared key
  cell for an operator with which it shares a hidden term, and the echo test of two such honest
  operators compares their lists of keys. `ListHit` is the hit of `compRun` or a counted call at a
  shared key cell that holds the seed of the first hidden term of an honest pair at its position.
* `EchoCompare` states the step from `compRun` to `listRun`, with the cost `1 / 2^256` for each pair.
* `shiftHidden D δ seed` adds `δ` to the seed of each hidden term. `shiftFreeHidden D parts δ` adds `δ`
  to the answer of each free call of `H` at a hidden cell. `compWorld_shift` states that `compWorld`
  on the shifted seeds is `compWorld` under this rewrite.
* `ListShift` states that the list program under `shiftFreeHidden` is the list program where each
  honest operator adds `δ` to the seed of each held term whose derive address is a hidden cell.
* `ListShiftStep` states that the shifted list program and the list program give one law of the
  parts, the seeds and the world, up to a derivation of a known term at a hidden cell.
* `ListCount` bounds the shifts that a run names. `CompLog` bounds the log of `compRun`.
* `compHit_of_steps` gives `CompHit` from the five statements.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

variable {C : Committee}

/-! ## The mean over a shift with a constant -/

/-- A probability `p` that is at most `a` plus the probability of `δ ∈ named` in one run for each `δ`,
with at most `N` named values at the end of each run, is at most `a` plus `N` over the number of the
values. The bound is a mean over the run and over `δ`. -/
theorem prEvent_le_add_of_shiftMean {V Y : Type} [Fintype V] [SampleableType V] (p a : ℝ≥0∞) (run : ProbComp Y)
    (named : Y → Finset V) (N : ℕ) (step : ∀ δ, p ≤ a + Pr{let y ← run}[δ ∈ named y])
    (count : ∀ y ∈ support run, (named y).card ≤ N) : p ≤ a + (N : ℝ≥0∞) / (Fintype.card V : ℝ≥0∞) := by
  have h₁ : p ≤ wp ($ᵗ V) (fun δ => a + wp run (fun y => if δ ∈ named y then 1 else 0)) := by
    calc p = wp ($ᵗ V) (fun _ => p) := (wp_const _ p).symm
      _ ≤ _ := wp_mono _ fun δ => (step δ).trans_eq (by rw [prEvent_eq_wp_indicator])
  refine h₁.trans ?_
  rw [wp_add, wp_const]
  refine add_le_add le_rfl ?_
  rw [DkgSecurityProof.wp_swap]
  refine (wp_mono_of_support run fun y hy => ?_).trans_eq (wp_const run _)
  rw [← prEvent_eq_wp_indicator, SampleableType.prEvent_uniformSample]
  refine ENNReal.div_le_div_right ?_ _
  have hc : (Finset.univ.filter fun δ => δ ∈ named y).card ≤ N := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact count y hy
  exact_mod_cast hc

/-! ## The common shift of the hidden seeds -/

section Shift

variable (prims : Primitives) (D : C.Coalition) (parts : C.Party → Parts C)

/-- The seeds with `δ` added to the seed of each hidden term. -/
def shiftHidden (δ : HashOutput) (seed : C.Term → HashOutput) : C.Term → HashOutput :=
  fun T => if KnownTo D.1 T then seed T else seed T ^^^ δ

theorem shiftHidden_shiftHidden (δ : HashOutput) (seed : C.Term → HashOutput) :
    shiftHidden D δ (shiftHidden D δ seed) = seed := by
  funext T
  unfold shiftHidden
  split_ifs <;> simp [BitVec.xor_assoc]

theorem shiftHidden_bijective (δ : HashOutput) : Function.Bijective (shiftHidden (C := C) D δ) :=
  Function.Involutive.bijective (shiftHidden_shiftHidden D δ)

/-- The calls of a run with `δ` added to the answer of each free call of `H` at a hidden cell. -/
def shiftFreeHidden (δ : HashOutput) : QueryImpl (WorldSpec C) (OracleComp (WorldSpec C)) := fun t =>
  match t with
  | .inr (.inr (.inl q)) =>
      if HiddenCell D parts q then
        (fun a => a ^^^ δ) <$> (liftM (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inl q)))) :
          OracleComp (WorldSpec C) HashOutput)
      else liftM (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inl q))))
  | t => liftM (OracleSpec.query t)

/-- `compWorld` on the shifted seeds answers each call as `compWorld` on the seeds answers the call
under `shiftFreeHidden`. -/
theorem compWorld_shift (δ : HashOutput) (seed : C.Term → HashOutput) (t : (WorldSpec C).Domain) :
    simulateQ (compWorld prims D parts seed) (shiftFreeHidden D parts δ t) =
      compWorld prims D parts (shiftHidden D δ seed) t := by
  rcases t with ((n | q | x) | p) | (n | q | x)
  rotate_left 5
  · by_cases hq : HiddenCell D parts q
    · obtain ⟨T, hT⟩ : ∃ T, hiddenTermOf D parts q = some T := by
        unfold hiddenTermOf
        split_ifs with h
        · exact ⟨_, rfl⟩
        · exact absurd hq h
      have hk := (hiddenTermOf_some D parts hT).1
      simp only [shiftFreeHidden, hq, ↓reduceIte, simulateQ_map, simulateQ_spec_query]
      rw [compWorld_some prims D parts seed hT, compWorld_some prims D parts _ hT]
      simp [shiftHidden, hk]
    · have hn : hiddenTermOf D parts q = none := by
        unfold hiddenTermOf
        split_ifs with h
        · exact absurd h hq
        · rfl
      simp only [shiftFreeHidden, hq, ↓reduceIte, simulateQ_spec_query]
      simp only [compWorld, hn]
  all_goals exact simulateQ_spec_query _ _

/-- A run of `compWorld` on the shifted seeds is a run of `compWorld` on the seeds of the program
under `shiftFreeHidden`. -/
theorem compWorld_shift_run (δ : HashOutput) (seed : C.Term → HashOutput) {α : Type}
    (oa : OracleComp (WorldSpec C) α) :
    simulateQ (compWorld prims D parts (shiftHidden D δ seed)) oa =
      simulateQ (compWorld prims D parts seed) (simulateQ (shiftFreeHidden D parts δ) oa) :=
  (QueryImpl.simulateQ_simulateQ_eq_of_apply (compWorld_shift prims D parts δ seed) oa).symm

end Shift

/-! ## The list program -/

section List

variable {E : Type}

/-- The honest operator `j` shares a term with no corrupt holder with `i`. -/
def SharesHidden (D : C.Coalition) (i j : C.Party) : Prop :=
  j ∉ D.1 ∧ ∃ T ∈ sharedTerms i j, ¬ KnownTo D.1 T

/-- The keys of operator `i` with `δ` added to the seed of each held term whose derive address is a
hidden cell. The test is on the address of the place in the code. -/
def shiftKeysHidden (D : C.Coalition) (parts : C.Party → Parts C) (δ : HashOutput) (i : C.Party)
    (inbox : Mail C E) (keys : HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput) :=
  (keys.1, fun T => if i ∈ C.holders T ∧ HiddenCell D parts (termAddress D parts i inbox T) then keys.2.1 T ^^^ δ
    else keys.2.1 T, keys.2.2)

/-- The local step of operator `i` after round 2 in the list program. The keys are changed by `adj`.
The operator asks no shared key cell for an operator with which it shares a hidden term. -/
def revealNextList (D : C.Coalition) (parts : C.Party → Parts C)
    (adj : C.Party → Mail C E → (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) →
      HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (committed : C.Party → Mail C E) (i : C.Party) (inbox : Mail C E) :
    OracleComp (LocalSpec C) (Option (SeedGenEchoData C)) :=
  liftComp (C.parties.mapM fun k => hashQuery (openAddress D parts i inbox k)) (LocalSpec C) >>= fun opens =>
    if openCheck .seedGen i (parts i) (committed i) (normRevealed D parts i inbox) opens then
      liftComp (deriveKeys .seedGen i (normView D parts i inbox)) (LocalSpec C) >>= fun keys =>
        liftComp (C.parties.mapM fun j => if SharesHidden D i j then pure 0 else
          hashQuery (sharedAddress i j (adj i inbox keys).2.1)) (LocalSpec C) >>= fun shared =>
          pure (some (adj i inbox keys, shared))
    else pure none

/-- The list that operator `i` compares with operator `j`, the key of `P` and the seeds of the shared
terms. -/
def echoList (i j : C.Party) (x : SeedGenEchoData C) : List HashOutput :=
  x.1.1 :: (sharedTerms i j).map x.1.2.1

/-- The echo message of operator `i` in the list program. An honest operator with which `i` shares a
hidden term gets the list. Each other operator gets the echo of the protocol. -/
def outList (D : C.Coalition) (i : C.Party) (x : SeedGenEchoData C) : Mail C E :=
  fun j => if j ≠ i ∧ SharesHidden D i j then some (.hashes (echoList i j x)) else echoOutbox .seedGen i x.1 x.2 j

/-- The echo test of operator `i` in the list program. -/
def echoListCheck (D : C.Coalition) (i : C.Party) (x : SeedGenEchoData C) (received : Mail C E) : Prop :=
  ∀ j, j ≠ i → Msg.hashesOf (received j) = if SharesHidden D i j then echoList i j x else echoOf .seedGen x.1 x.2 j

/-- The local step of operator `i` after round 3 in the list program. -/
def echoNextList (D : C.Coalition) (i : C.Party) (x : SeedGenEchoData C) (inbox : Mail C E) :
    OracleComp (LocalSpec C) (Option (Keys C)) :=
  pure (if echoListCheck D i x inbox then some (_root_.ThresholdLeanXmssSecurity.keysOf x.1) else none)

/-- The seed generation of the list program, with the change `adj` of the keys. -/
def seedGenList (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (adj : C.Party → Mail C E → (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) →
      HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    OracleComp (WorldSpec C) (net.State × (C.Party → Option (Keys C))) :=
  commitDraws D parts >>= fun commitments =>
  observe (net.round state (commitMail D commitments)) >>= fun r =>
  programBlock D (early ++ r.2) r.1.2 parameter dealt parts >>= fun _ =>
  levelRound D net (setupRounds - 1) r.1.1 (revealReady (commitInbox D commitments r.1.2))
    (fun i _ => revealOutbox .seedGen i (parts i))
    (fun i _ inbox => revealNextList D parts adj (commitInbox D commitments r.1.2) i inbox) fun f2 s2 d2 =>
  levelRound D net f2 s2 d2 (outList D) (echoNextList D) fun _ s3 d3 =>
  pure (s3, fun j => if j ∈ D.1 then none else d3 j)

end List

/-! ## The runs of the list program -/

section Runs

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The rest of the game after the seed generation with the output `y`. -/
def restOf (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State)
    (y : A.net.State × (C.Party → Option (Keys C))) : OracleComp (WorldSpec C) (RunOut C) := do
  let keys := fun i => (y.2 i).map fun _ => x.2.1.2.2 i
  let win ← (secRest K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.2.1.1 x.2.1.2.1 x.2.1.2.2 y.2).run'
    (startState D y.1 keys)
  pure (win, x.2.1.1, x.2.1.2.1, x.2.1.2.2, y.2)

/-- The suffix of the game with the list program, with the change `adj` of the keys. -/
def listSuffix (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State)
    (adj : C.Party → Mail C E → (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) →
      HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :
    OracleComp (WorldSpec C) (RunOut C) := do
  let (state, emu) ← seedGenList D A.net x.1.1 x.1.2 x.2.1.1 x.2.1.2.2 x.2.2 adj
  let keys := fun i => (emu i).map fun _ => x.2.1.2.2 i
  let win ← (secRest K circuits settings runLimit ⟨true, fun _ => 0⟩ D A x.2.1.1 x.2.1.2.1 x.2.1.2.2 emu).run'
    (startState D state keys)
  pure (win, x.2.1.1, x.2.1.2.1, x.2.1.2.2, emu)

/-- The run of the list program with the keys changed by `adj parts` and the seeds `g seed` in the
world. The result is the parts, the seeds of the world and the world state. -/
def listRunWith (D : C.Coalition) (A : DkgTsigAdversary C E)
    (adj : (C.Party → Parts C) → C.Party → Mail C E → (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) →
      HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput))
    (g : (C.Term → HashOutput) → C.Term → HashOutput) :
    ProbComp ((C.Party → Parts C) × (C.Term → HashOutput) × LogState C) := do
  let x ← (simulateQ (loggedWorld prims D) (dealtPrefix D A)).run ((∅, ∅), [])
  let seed ← $ᵗ (C.Term → HashOutput)
  let z ← (simulateQ (compWorld prims D x.1.2.2 (g seed))
    (listSuffix K circuits settings runLimit D A x.1 (adj x.1.2.2))).run x.2
  pure (x.1.2.2, g seed, z.2)

/-- The run of the list program. -/
def listRun (D : C.Coalition) (A : DkgTsigAdversary C E) :
    ProbComp ((C.Party → Parts C) × (C.Term → HashOutput) × LogState C) :=
  listRunWith prims K circuits settings runLimit D A (fun _ _ _ keys => keys) id

/-- The run of the list program where each honest operator adds `δ` to the seed of each held term
whose derive address is a hidden cell. -/
def listRunShift (D : C.Coalition) (A : DkgTsigAdversary C E) (δ : HashOutput) :
    ProbComp ((C.Party → Parts C) × (C.Term → HashOutput) × LogState C) :=
  listRunWith prims K circuits settings runLimit D A (fun parts => shiftKeysHidden D parts δ) id

/-- The seed that an honest holder of the hidden term `T` derives in `compWorld`, the seed of the term
that `hiddenTermOf` selects at its cell. -/
def heldSeed (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput) (T : C.Term) :
    HashOutput :=
  match hiddenTermOf D parts (hiddenInput parts T) with
  | some T' => seed T'
  | none => 0

/-- A counted call asks a shared key cell whose list holds, at the position of the first hidden term
`T` that two honest operators share, the seed that a holder of `T` derives. -/
def EchoPrior (D : C.Coalition) (parts : C.Party → Parts C) (seed : C.Term → HashOutput) (w : LogState C) :
    Prop :=
  ∃ q ∈ w.2, ∃ (L : List HashOutput) (i j : C.Party) (T : C.Term), i ∉ D.1 ∧ j ∉ D.1 ∧ i ≠ j ∧
    (sharedTerms i j).find? (fun T' => ¬ KnownTo D.1 T') = some T ∧ q = .sharedKeys .seedGen L ∧
    L.getD ((sharedTerms i j).idxOf T) 0 = heldSeed D parts seed T

/-- The event of the list run, a counted call at a PRF cell under the seed of a hidden term or
`EchoPrior`. -/
def ListHit (D : C.Coalition) (r : (C.Party → Parts C) × (C.Term → HashOutput) × LogState C) : Prop :=
  (∃ q ∈ r.2.2.2, ∃ (T : C.Term) (x : Point), ¬ KnownTo D.1 T ∧ q = .prf (r.2.1 T) x) ∨
    EchoPrior D r.1 r.2.1 r.2.2

/-- The shifts `δ` for which the run with the hidden seeds shifted by `δ` shows `ListHit`. A counted
call at a PRF cell names at most one shift for each hidden term, and a counted call at a shared key
cell names at most one shift for each pair. -/
def listNamed (D : C.Coalition) (r : (C.Party → Parts C) × (C.Term → HashOutput) × LogState C) :
    Finset HashOutput :=
  Finset.univ.filter fun δ => ListHit D (r.1, shiftHidden D δ r.2.1, r.2.2)

/-- The cost of a derivation of a known term at a hidden cell, `n h k / 2^(256 t)`. -/
def aliasCost (D : C.Coalition) : ℝ≥0∞ :=
  ((C.n * (hiddenTerms D).card * (knownTerms D).card : ℕ) : ℝ≥0∞) / 2 ^ (256 * C.t)

/-- The echo comparison. The hit in `compRun` has at most the probability of `ListHit` in `listRun`
and `1 / 2^256` for each pair. The two runs agree until the hashes of two distinct lists of an honest
pair are equal with a fresh cell (at most `1 / 2^256` for each pair), or a counted call asks the list
of an honest pair, before or after the honest call (`EchoPrior` reads the log at the end). The self
cell `sharedAddress i i` of an operator with a hidden term has a value in `compRun` and none in
`listRun`. No step reads that value, so a counted call there sees one law in the two runs. The bound
is a mean over the run from the empty start. -/
def EchoCompare : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    Pr{let r ← compRun prims K circuits settings runLimit D A}[CompHitOf D r] ≤
      (C.n.choose 2 : ℝ≥0∞) / 2 ^ 256 + Pr{let r ← listRun prims K circuits settings runLimit D A}[ListHit D r]

/-- The program fact on the seeds. The list suffix with `δ` added to the answer of each free call at a
hidden cell is the list suffix where each honest operator adds `δ` to the seed of each held term whose
derive address is a hidden cell. The two sides are equal as programs. -/
def ListShift : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (x : PrefixOut C A.net.State) (δ : HashOutput),
    simulateQ (shiftFreeHidden D x.2.2 δ) (listSuffix K circuits settings runLimit D A x (fun _ _ keys => keys)) =
      listSuffix K circuits settings runLimit D A x (shiftKeysHidden D x.2.2 δ)

/-- The step on the world. The list program with the shifted keys and the list program give one law
of the parts, the seeds and the world state, up to the probability `aliasCost D` of a derivation of a
known term at a hidden cell. Off that event the shifted seeds enter only the lists of the honest pairs
that share a hidden term, whose test is invariant under the common shift, and the output keys, which
the rest of the game does not read. The bound is a mean over the run from the empty start. -/
def ListShiftStep : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (δ : HashOutput)
    (event : (C.Party → Parts C) × (C.Term → HashOutput) × LogState C → Prop),
    Pr{let r ← listRunShift prims K circuits settings runLimit D A δ}[event r] ≤
      aliasCost D + Pr{let r ← listRun prims K circuits settings runLimit D A}[event r]

/-- The count of the named shifts at the end of the list run with the budget `q`, at most `q` counted
calls, each with at most `h` hidden terms or `C(n,2)` pairs. -/
def ListCount : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ r ∈ support (listRun prims K circuits settings runLimit D A),
      (listNamed D r).card ≤ q * ((hiddenTerms D).card + C.n.choose 2)

/-- The log of `compRun` with the budget `q` has at most `q` cells. -/
def CompLog : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ r ∈ support (compRun prims K circuits settings runLimit D A), r.2.2.2.2.length ≤ q

end Runs

/-! ## Tests at the zero shift -/

section Zero

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

end Zero

/-! ## The glue -/

section Glue

/-- With `h` hidden terms, `n h` is at most `2^(256 (t - 1))`. -/
theorem n_hidden_le (D : C.Coalition) : C.n * (hiddenTerms D).card ≤ 2 ^ (256 * (C.t - 1)) := by
  have hh : (hiddenTerms D).card ≤ termCount C := by
    have := hidden_add_known D
    omega
  rcases Nat.lt_or_ge C.t 2 with ht | ht
  · have ht1 : C.t = 1 := by have := C.one_le_t; omega
    have hn : C.n = 1 := by unfold Committee.n; omega
    have hm : termCount C = 1 := by unfold termCount; rw [hn, ht1]; rfl
    rw [hn, ht1]
    simp only [one_mul, Nat.sub_self, mul_zero, pow_zero]
    omega
  · have hm : termCount C ≤ 2 ^ C.n := Nat.choose_le_two_pow _ _
    have hn : C.n ≤ 2 ^ C.n := (Nat.lt_two_pow_self).le
    calc C.n * (hiddenTerms D).card ≤ 2 ^ C.n * 2 ^ C.n := Nat.mul_le_mul hn (hh.trans hm)
      _ = 2 ^ (2 * C.n) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (256 * (C.t - 1)) := by
          refine Nat.pow_le_pow_right (by norm_num) ?_
          unfold Committee.n
          omega

/-- For `q ≥ 1` the cost of the alias fits in `q k / 2^256`. -/
theorem aliasCost_real_le (D : C.Coalition) (q : ℕ) (hq : 1 ≤ q) :
    ((C.n * (hiddenTerms D).card * (knownTerms D).card : ℕ) : ℝ) / 2 ^ (256 * C.t) ≤
      ((q * (knownTerms D).card : ℕ) : ℝ) / 2 ^ 256 := by
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hnat : C.n * (hiddenTerms D).card * (knownTerms D).card * 2 ^ 256 ≤
      q * (knownTerms D).card * 2 ^ (256 * C.t) := by
    have ht := C.one_le_t
    have hpow : 2 ^ (256 * C.t) = 2 ^ (256 * (C.t - 1)) * 2 ^ 256 := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    have h1 := n_hidden_le D
    calc C.n * (hiddenTerms D).card * (knownTerms D).card * 2 ^ 256
        ≤ 2 ^ (256 * (C.t - 1)) * (knownTerms D).card * 2 ^ 256 := by gcongr
      _ ≤ q * (knownTerms D).card * (2 ^ (256 * (C.t - 1)) * 2 ^ 256) := by
          have : 2 ^ (256 * (C.t - 1)) * (knownTerms D).card * 2 ^ 256 ≤
              q * (2 ^ (256 * (C.t - 1)) * (knownTerms D).card * 2 ^ 256) := Nat.le_mul_of_pos_left _ hq
          calc _ ≤ _ := this
            _ = _ := by ring
  exact_mod_cast hnat

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
/-- By `ListShift`, the list run is the shifted list run with the hidden seeds of the result shifted
back, in law. The seeds are uniform and `shiftHidden D δ` is a bijection. -/
theorem listRun_eq_shift (shift : ListShift K circuits settings runLimit) (D : C.Coalition)
    (A : DkgTsigAdversary C E) (δ : HashOutput) :
    listRun prims K circuits settings runLimit D A =ᵈ
      (fun r => (r.1, shiftHidden D δ r.2.1, r.2.2)) <$> listRunShift prims K circuits settings runLimit D A δ := by
  unfold listRun listRunShift listRunWith
  rw [map_bind]
  refine EvalDistEq.bind_right _ fun x => ?_
  have hu := (SampleableType.map_uniformSample_evalDistEq_of_bijective (shiftHidden_bijective D δ)).symm
  refine (hu.bind_left _).trans ?_
  rw [bind_map_left, map_bind]
  have e : ∀ seed : C.Term → HashOutput,
      ((simulateQ (compWorld prims D x.1.2.2 (id (shiftHidden D δ seed)))
        (listSuffix K circuits settings runLimit D A x.1 (fun _ _ keys => keys))).run x.2 >>= fun z =>
          (pure (x.1.2.2, id (shiftHidden D δ seed), z.2) : ProbComp _)) =
      (fun r => (r.1, shiftHidden D δ r.2.1, r.2.2)) <$>
        ((simulateQ (compWorld prims D x.1.2.2 (id seed))
          (listSuffix K circuits settings runLimit D A x.1 (shiftKeysHidden D x.1.2.2 δ))).run x.2 >>= fun z =>
            (pure (x.1.2.2, id seed, z.2) : ProbComp _)) := by
    intro seed
    simp only [id, map_bind, map_pure]
    rw [compWorld_shift_run prims D x.1.2.2 δ seed, shift D A x.1 δ]
  simp only [e]
  exact EvalDistEq.rfl

omit [Fintype E] [DecidableEq E] in
/-- `ListShift`, `ListShiftStep` and `ListCount` bound `ListHit` in the list run by the mean over the
common shift. -/
theorem listHit_le (shift : ListShift K circuits settings runLimit)
    (step : ListShiftStep prims K circuits settings runLimit) (count : ListCount prims K circuits settings runLimit)
    (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ) (bounded : DkgTsigBounded circuits settings runLimit A q) :
    Pr{let r ← listRun prims K circuits settings runLimit D A}[ListHit D r] ≤
      aliasCost D + ((q * ((hiddenTerms D).card + C.n.choose 2) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have key : ∀ δ : HashOutput, Pr{let r ← listRun prims K circuits settings runLimit D A}[ListHit D r] ≤
      aliasCost D + Pr{let r ← listRun prims K circuits settings runLimit D A}[δ ∈ listNamed D r] := by
    intro δ
    rw [(listRun_eq_shift prims K circuits settings runLimit shift D A δ).prEvent_eq, prEvent_map]
    have e : (fun r : (C.Party → Parts C) × (C.Term → HashOutput) × LogState C => δ ∈ listNamed D r) =
        fun r => ListHit D (r.1, shiftHidden D δ r.2.1, r.2.2) := by
      funext r
      simp [listNamed]
    rw [e]
    exact step D A δ _
  have h := prEvent_le_add_of_shiftMean _ (aliasCost D) _ (listNamed D) _ key (count D A q bounded)
  have hcard : (Fintype.card HashOutput : ℝ≥0∞) = 2 ^ 256 := by
    simp
    norm_num
  rwa [hcard] at h

omit [Fintype E] [DecidableEq E] in
/-- The five statements give `CompHit`. -/
theorem compHit_of_steps (echo : EchoCompare prims K circuits settings runLimit)
    (shift : ListShift K circuits settings runLimit) (step : ListShiftStep prims K circuits settings runLimit)
    (count : ListCount prims K circuits settings runLimit) (log : CompLog prims K circuits settings runLimit) :
    CompHit prims K circuits settings runLimit := by
  intro D A q bounded
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have h0 : Pr{let r ← compRun prims K circuits settings runLimit D A}[CompHitOf D r] = 0 :=
      prEvent_eq_zero_of_forall_mem_support _ _ fun r hr ⟨q', hq', _⟩ => by
        have hl := log D A 0 bounded r hr
        rw [Nat.le_zero, List.length_eq_zero_iff] at hl
        rw [hl] at hq'
        exact List.not_mem_nil hq'
    rw [h0]
    unfold compHitError
    simp only [ENNReal.toReal_zero]
    positivity
  · have h1 := (echo D A).trans (add_le_add le_rfl (listHit_le prims K circuits settings runLimit shift step count
      D A q bounded))
    unfold aliasCost at h1
    have hfin : (C.n.choose 2 : ℝ≥0∞) / 2 ^ 256 +
        (((C.n * (hiddenTerms D).card * (knownTerms D).card : ℕ) : ℝ≥0∞) / 2 ^ (256 * C.t) +
          ((q * ((hiddenTerms D).card + C.n.choose 2) : ℕ) : ℝ≥0∞) / 2 ^ 256) ≠ ⊤ := by
      refine ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity),
        ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity),
          ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)⟩⟩
    have h2 := ENNReal.toReal_mono hfin h1
    rw [ENNReal.toReal_add (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity))
        (ENNReal.add_ne_top.2 ⟨ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity),
          ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)⟩),
      ENNReal.toReal_add (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity))
        (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity))] at h2
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at h2
    refine h2.trans ?_
    have h3 := aliasCost_real_le D q hq
    have hm := hidden_add_known D
    unfold compHitError
    rw [← hm]
    have e : ((q * ((hiddenTerms D).card + (knownTerms D).card) + C.n.choose 2 * (q + 1) : ℕ) : ℝ) / 2 ^ 256 =
        (C.n.choose 2 : ℝ) / 2 ^ 256 + ((q * (knownTerms D).card : ℕ) : ℝ) / 2 ^ 256 +
          ((q * ((hiddenTerms D).card + C.n.choose 2) : ℕ) : ℝ) / 2 ^ 256 := by
      push_cast
      ring
    rw [e]
    linarith

end Glue

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.compHit_of_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedSteps.compHit_of_steps
