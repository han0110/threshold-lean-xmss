import ThresholdLeanXmssSecurity.Proof.TreeTwinSavedKinds
import ThresholdLeanXmssSecurity.Proof.TreeTwinSegments
import ThresholdLeanXmssSecurity.Proof.TreeTwinGlue
import ThresholdLeanXmssSecurity.Proof.TreeLockstepReach
import ThresholdLeanXmssSecurity.Proof.TreeLockstepLateBottom

/-!
# The fixed final-segment kinds

The final Coin decoder reads honest pending programs. Interpolation is total
even for unrelated party-local randomness; honest acceptance identifies its
value. The singleton committee exposes its share through the first captured
Coin-key query in the retained continuation.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 4096
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
open Finset
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeTwinSegment
open TreeTwinLinked2 TreeTwinSavedSchedule TreeTwinSavedKinds
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E)

/-- Decode the first local Coin-key query, with zero for other programs. -/
def firstCoinKey {β : Type} : OracleComp (LocalSpec C) β → E
  | .roll (Sum.inr (Sum.inl (.coinKey _ _ bits))) _ =>
      K.encode.symm (fun b => bits.getD b.val 0)
  | _ => 0

/-- Observe the first local query after an empty-mail resume. -/
def resumeCoin {α : Type} : Step C E RealSpec α → E
  | .wait _ resume => firstCoinKey K (advance (resume fun _ => none))
  | _ => 0

private theorem firstCoinKey_tail {α : Type} (tag label : ℕ) (v : E) (st : RunState C)
    (body : E × RunState C → PartyM C E RealSpec α) :
    firstCoinKey K (advance ((treeStagesChallengeTail K tag label body) ([v], st)).run) = v := by
  unfold treeStagesChallengeTail
  rw [advance_oracleStep_bind]
  change K.encode.symm (fun b => (List.ofFn (K.encode v)).getD b.val 0) = v
  simp

/-- For a singleton committee, empty mail opens the sole retained share. -/
theorem resumeCoin_tail {α : Type} (i : C.Party)
    (alone : ¬ ∃ j : C.Party, j ≠ i) (o : PrssOutput C E) (st : RunState C)
    (tag label : ℕ) (body : E × RunState C → PartyM C E RealSpec α) :
    resumeCoin K (treeSimCoinStep K (localContext i) o 1 st
      (treeStagesChallengeTail K tag label body)) = conv K (localContext i) o.1 0 := by
  have all : ∀ j : C.Party, j = i := by simpa using alone
  have first : (univ.filter fun j : C.Party => j.val < C.t) = {i} := by
    ext j
    have ji := all j
    subst j
    have hn : C.n = 1 := by
      have hc : Fintype.card C.Party = 1 := Fintype.card_eq_one_iff.mpr ⟨i, all⟩
      simpa only [Committee.Party, Fintype.card_fin] using hc
    have ht : C.t = 1 := by have := C.one_le_t; dsimp [Committee.n] at hn; omega
    simp [ht, (show i.val = 0 from by have := i.isLt; omega)]
  have lag (x : E) : lagrangeFirst K x i = 1 := by simp [lagrangeFirst, first]
  have agree : OpenAgreesN K i (conv K (localContext i) o.1) 1 (fun _ => none) := by
    intro j g hg
    simp [first, all j, lag]
  have value : openValueN K i (conv K (localContext i) o.1) (fun _ => none) =
      conv K (localContext i) o.1 := by
    funext g
    simp [openValueN, first, lag, openShareN]
  have noAbort : (C.parties.any fun _ => false) = false := by simp
  simp only [resumeCoin, treeSimCoinStep, exchangeResume, Msg.isAbort, noAbort,
    Bool.false_eq_true, if_false]
  rw [advance_require_bind]
  simp only [show (localContext i).self = i from rfl, if_pos agree, value]
  simpa [vector] using firstCoinKey_tail K tag label (conv K (localContext i) o.1 0)
    (nextLabel st) body


/-- Read the local share from another recipient, or from the singleton continuation. -/
def coinShare {α : Type} (s : Step C E RealSpec α) (i : C.Party) : E :=
  if h : ∃ j : C.Party, j ≠ i then Msg.elementAt (s.outbox (Classical.choose h)) 0
  else resumeCoin K s

/-- The total interpolation decoder on honest pending Coin steps. -/
def coinOf {α : Type} (D : C.Coalition) (steps : C.Party → Step C E RealSpec α) : E :=
  (Lagrange.interpolate (univ.filter (· ∉ D.1)) K.point (fun l => coinShare K (steps l) l)).eval 0

/-- The same interpolation on the actual party-local PRSS conversions. -/
def coinValue (D : C.Coalition) (rnd : C.Party → PrssOutput C E) : E :=
  (Lagrange.interpolate (univ.filter (· ∉ D.1)) K.point
    (fun l => conv K (localContext l) (rnd l).1 0)).eval 0

theorem coinShare_coinStep {α : Type} (i : C.Party) (other : ∃ j : C.Party, j ≠ i)
    (o : PrssOutput C E) (st : RunState C)
    (k : List E × RunState C → PartyM C E RealSpec α) :
    coinShare K (treeSimCoinStep K (localContext i) o 1 st k) i =
      conv K (localContext i) o.1 0 := by
  simp only [coinShare, dif_pos other, treeSimCoinStep, Step.outbox, openOut,
    show (localContext i).self = i from rfl, if_neg (Classical.choose_spec other), Msg.elementAt]
  exact vector_getD 1 _ 0 (by omega)

theorem coinShare_tail {α : Type} (i : C.Party) (o : PrssOutput C E) (st : RunState C)
    (tag label : ℕ) (body : E × RunState C → PartyM C E RealSpec α) :
    coinShare K (treeSimCoinStep K (localContext i) o 1 st
      (treeStagesChallengeTail K tag label body)) i = conv K (localContext i) o.1 0 := by
  by_cases other : ∃ j : C.Party, j ≠ i
  · exact coinShare_coinStep K i other o st _
  · simpa only [coinShare, dif_neg other] using resumeCoin_tail K i other o st tag label body

theorem coinOf_waiting {α : Type} (D : C.Coalition) (rnd : C.Party → PrssOutput C E)
    (st : C.Party → RunState C) (tag label : C.Party → ℕ)
    (body : C.Party → E × RunState C → PartyM C E RealSpec α) :
    coinOf K D (treeSimCoinWaiting K D 1 rnd st
      (fun i => treeStagesChallengeTail K (tag i) (label i) (body i))) = coinValue K D rnd := by
  unfold coinOf coinValue
  congr 1
  apply Lagrange.interpolate_eq_of_values_eq_on
  intro i hi
  have honest : i ∉ D.1 := (mem_filter.mp hi).2
  simp only [treeSimCoinWaiting, if_neg honest]
  exact coinShare_tail K i (rnd i) (st i) (tag i) (label i) (body i)

/-- Port of the honest-share and acceptance steps of A178 `coinOutput_agree`.
An accepting polynomial is determined by the honest evaluations alone. -/
theorem coinOutput_eq_coinValue (D : C.Coalition) (rnd : C.Party → PrssOutput C E)
    (sent : C.Party → Mail C E) {i : C.Party} (hi : i ∉ D.1) {vals : List E}
    (accept : treeSimCoinOutput K D 1 rnd sent i = some vals) : vals = [coinValue K D rnd] := by
  let share := fun l => conv K (localContext l) (rnd l).1
  let inbox := fun l => if l ∈ D.1 then sent l i else coinOut K l 1 (rnd l) i
  have honest (l : C.Party) (hl : l ∉ D.1) : openShare i (share i) inbox l 0 = share l 0 := by
    by_cases he : l = i
    · subst l; simp [openShare]
    · simp only [openShare, if_neg he, inbox, if_neg hl, coinOut, openOut, localContext]
      rw [if_neg (Ne.symm he)]
      exact vector_getD 1 _ 0 (by omega)
  have accepted :
      (∀ l : C.Party, ∀ g < 1, openShare i (share i) inbox l g =
        ∑ m ∈ firstParties C, lagrangeFirst K (K.point l) m * openShare i (share i) inbox m g) ∧
      vals = vector 1 (fun g => ∑ m ∈ firstParties C,
        lagrangeFirst K 0 m * openShare i (share i) inbox m g) := by
    simp only [treeSimCoinOutput, if_neg hi, coinRes] at accept
    split at accept
    · cases accept
    · change (openRes K i (share i) 1 inbox).map (vector 1) = some vals at accept
      unfold openRes at accept
      split at accept
      · rename_i hp
        exact ⟨hp, (Option.some.inj accept).symm⟩
      · cases accept
  obtain ⟨agree, rfl⟩ := accepted
  have interp : Lagrange.interpolate (firstParties C) K.point (fun l => openShare i (share i) inbox l 0) =
      Lagrange.interpolate (univ.filter (· ∉ D.1)) K.point (fun l => share l 0) := by
    apply Lagrange.eq_interpolate_of_eval_eq _ K.point.injective.injOn
    · have degree := Lagrange.degree_interpolate_lt (fun l => openShare i (share i) inbox l 0)
          (K.point.injective.injOn (s := firstParties C))
      rw [card_firstParties] at degree
      exact degree.trans_le (by exact_mod_cast card_honest_ge D)
    · intro l hl
      rw [eval_interpolate_first, ← agree l 0 (by omega), honest l (mem_filter.mp hl).2]
  simp only [vector, List.range_one, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  rw [← eval_interpolate_first, interp]
  rfl

/-- A stopped Coin has equal decoders even with arbitrary retained continuations. -/
theorem coinOf_partial_eq {α : Type} (D : C.Coalition) (live : C.Party → Bool)
    (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true) (count : ℕ) (rnd : C.Party → PrssOutput C E)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → List E × RunState C → PartyM C E RealSpec α) :
    coinOf K D (treeSimCoinPartial K D live count rnd st₁ k₁) =
      coinOf K D (treeSimCoinPartial K D live count rnd st₂ k₂) := by
  unfold coinOf
  congr 1
  apply Lagrange.interpolate_eq_of_values_eq_on
  intro i hi
  by_cases other : ∃ j : C.Party, j ≠ i
  · simp only [coinShare, dif_pos other, treeSimCoinPartial, treeSimCoinWaiting]
    split <;> simp only [treeSimCoinStep, Step.outbox]
    split <;> rfl
  · obtain ⟨j, hj, off⟩ := stopped
    have ji : j = i := by by_contra h; exact other ⟨j, h⟩
    subst j
    simp [treeSimCoinPartial, off]

/-- The fixed cache's option-valued challenge for a single Coin element. -/
abbrev challengeAt (cache : HashCache C) (tag label : ℕ) (c : E) : Option E :=
  treeStagesCachedChallenge K cache tag label [c]

theorem challengeAt_some (cache : HashCache C) (tag label : ℕ) (c r : E)
    (some_r : challengeAt K cache tag label c = some r) : r ≠ 0 ∧ r ≠ 1 := by
  have find (key : HashOutput) (tries index : ℕ) :
      treeStagesCachedFindChallenge K cache key tries index = some r → r ≠ 0 ∧ r ≠ 1 := by
    induction tries generalizing index with
    | zero => simp [treeStagesCachedFindChallenge]
    | succ tries ih =>
      simp only [treeStagesCachedFindChallenge]
      split_ifs with good
      · intro eq; cases Option.some.inj eq; exact good
      · exact ih (index + 1)
  exact find _ _ _ some_r


theorem challengeAt_swapAll (swaps : List (List Bit × HashOutput × HashOutput))
    (cache : HashCache C) (tag label : ℕ) (c : E) :
    challengeAt K (treeStagesSwapAll swaps cache) tag label c = challengeAt K cache tag label c :=
  treeTwin_cachedChallenge_swapAll K swaps cache tag label [c]

theorem challengeAt_mono {a b : HashCache C} (h : a ≤ b) (tag label : ℕ) (c : E)
    (covered : TreeStagesChallengeCovered K a tag label [c]) :
    challengeAt K a tag label c = challengeAt K b tag label c :=
  treeStages_cachedChallenge_mono K h tag label [c] covered

section Stages
variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
  (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (openings : List (List (List Bit)))

/-- The visible shift and both future-cache frames at the next unused label. -/
def Frames (L : ℕ) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧ TreeSimFutureZero L δ ∧
    TreeSimFutureEmpty L a.2.1.2 ∧ TreeSimFutureEmpty L b.2.2

/-- The final Coin with all honest senders live and equality at one guessed Coin value. -/
def FinalCoinAt (c : E) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (f : FinalData K circuits settings top tree D parameter openings)
    (st₁ st₂ : C.Party → RunState C) (q₁ q₂ : C.Party → Shares C E)
    (rnd : C.Party → PrssOutput C E) (offset L : ℕ),
    Position circuits settings tree D parameter f.caller.rest.circs offset st₁ ∧
    (∀ i, i ∉ D.1 → (st₁ i).tag = (st₂ i).tag ∧ (st₁ i).label = L ∧ (st₂ i).label = L) ∧
    CommonHistory D (fun _ => true) st₁ ∧ CommonHistory D (fun _ => true) st₂ ∧
    Frames D A (L + 1) δ a b ∧
    (∀ i, i ∉ D.1 → ∀ r, challengeAt K a.2.1.1 (st₁ i).tag L c = some r → ∀ k < 3,
      finalVector K (f.caller.peer.ctx₁ i) (f.claim₁ i) (f.w₁ i) (q₁ i) r k =
        finalVector K (f.caller.peer.ctx₂ i) (f.claim₂ i) (f.w₂ i) (q₂ i) r k) ∧
    a.1.2 = treeSimCoinWaiting K D 1 rnd st₁ (fun i =>
      treeStagesChallengeTail K (st₁ i).tag (st₁ i).label
        (finalAfterCoin K (f.caller.peer.ctx₁ i) (f.claim₁ i) (f.w₁ i) (q₁ i)
          (f.finish₁ K circuits settings top tree D parameter openings i))) ∧
    b.1.2 = treeSimCoinWaiting K D 1 rnd st₂ (fun i =>
      treeStagesChallengeTail K (st₂ i).tag (st₂ i).label
        (finalAfterCoin K (f.caller.peer.ctx₂ i) (f.claim₂ i) (f.w₂ i) (q₂ i)
          (f.finish₂ K circuits settings top tree D parameter openings i)))

/-- The guessed final Coin relation at its actual decoded value. -/
def FinalCoinEqualStage (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  FinalCoinAt K circuits settings top tree D A parameter openings (coinOf K D a.1.2) δ a b

/-- One common final challenge, equal live opening vectors, and the next unused-label frame. -/
def FinalOpenEqualStage (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (f : FinalData K circuits settings top tree D parameter openings) (live : C.Party → Bool)
    (st₁ st₂ : C.Party → RunState C) (q₁ q₂ : C.Party → Shares C E) (r : E) (offset L : ℕ),
    Position circuits settings tree D parameter f.caller.rest.circs offset st₁ ∧
    (∀ i, i ∉ D.1 → (st₁ i).tag = (st₂ i).tag ∧ (st₁ i).label = L ∧ (st₂ i).label = L) ∧
    CommonHistory D live st₁ ∧ CommonHistory D live st₂ ∧ Frames D A L δ a b ∧
    (∀ i, i ∉ D.1 → live i = true → ∀ k < 3,
      finalVector K (f.caller.peer.ctx₁ i) (f.claim₁ i) (f.w₁ i) (q₁ i) r k =
        finalVector K (f.caller.peer.ctx₂ i) (f.claim₂ i) (f.w₂ i) (q₂ i) r k) ∧
    a.1.2 = treeSimCheckWaiting K D live
      (.opening (fun i => finalVector K (f.caller.peer.ctx₁ i) (f.claim₁ i) (f.w₁ i) (q₁ i) r))
      (fun i => f.finish₁ K circuits settings top tree D parameter openings i ((), st₁ i)) ∧
    b.1.2 = treeSimCheckWaiting K D live
      (.opening (fun i => finalVector K (f.caller.peer.ctx₂ i) (f.claim₂ i) (f.w₂ i) (q₂ i) r))
      (fun i => f.finish₂ K circuits settings top tree D parameter openings i ((), st₂ i))

/-- The live two-product exchange with the conditional per-party output-shift equation. -/
def GuessFieldStage (r? : Option E) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (f : FinalData K circuits settings top tree D parameter openings) (d : TreeSimExtendMultData K D)
    (offset L : ℕ),
    d.ctx₁ = f.caller.peer.ctx₁ ∧ d.ctx₂ = f.caller.peer.ctx₂ ∧ d.count = 2 ∧
    d.v₁ = (fun i => contextProductValues K (d.ctx₁ i) (f.products₁ K circuits settings top tree D parameter openings i)) ∧
    d.v₂ = (fun i => contextProductValues K (d.ctx₂ i) (f.products₂ K circuits settings top tree D parameter openings i)) ∧
    d.k₁ = (fun i => finalAfterField K (d.ctx₁ i) (f.claim₁ i) (f.w₁ i)
      (f.finish₁ K circuits settings top tree D parameter openings i)) ∧
    d.k₂ = (fun i => finalAfterField K (d.ctx₂ i) (f.claim₂ i) (f.w₂ i)
      (f.finish₂ K circuits settings top tree D parameter openings i)) ∧
    Position circuits settings tree D parameter f.caller.rest.circs offset d.st₁ ∧
    (∀ i, i ∉ D.1 → (d.st₁ i).tag = (d.st₂ i).tag ∧ (d.st₁ i).label = L ∧ (d.st₂ i).label = L) ∧
    CommonHistory D (fun _ => true) d.st₁ ∧ CommonHistory D (fun _ => true) d.st₂ ∧
    Frames D A (L + 1) δ a b ∧ δ = d.δ ∧
    (AllHistory D d.st₁ → ∀ r, r? = some r → ∀ i, i ∉ D.1 → ∀ o₁ o₂,
      o₂ = treeSimFieldHeldShift D i 2
        (fun g => ∑ j ∈ univ.filter (· ∉ D.1), (d.v₁ j g - d.v₂ j g)) o₁ → ∀ k < 3,
      finalVector K (d.ctx₁ i) (f.claim₁ i) (f.w₁ i) o₁ r k =
        finalVector K (d.ctx₂ i) (f.claim₂ i) (f.w₂ i) o₂ r k) ∧
    a.1.2 = treeSimExtendMultWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
    b.1.2 = treeSimExtendMultWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂

/-- The digest exchange carrying the same option-valued challenge and conditional final equation. -/
def GuessDigestStage (r? : Option E) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (f : FinalData K circuits settings top tree D parameter openings)
    (live : C.Party → Bool) (st₁ st₂ : C.Party → RunState C)
    (q₁ q₂ : C.Party → Shares C E) (salts : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) (offset L : ℕ),
    Position circuits settings tree D parameter f.caller.rest.circs offset st₁ ∧
    (∀ i, i ∉ D.1 → (st₁ i).tag = (st₂ i).tag ∧ (st₁ i).label = L ∧ (st₂ i).label = L) ∧
    DigestCertificate D live st₁ st₂ salts ds a.2.2 a.2.1.1 ∧ Frames D A L δ a b ∧
    (AllHistory D st₁ → ∀ r, r? = some r → ∀ i, i ∉ D.1 → live i = true → ∀ k < 3,
      finalVector K (f.caller.peer.ctx₁ i) (f.claim₁ i) (f.w₁ i) (q₁ i) r k =
        finalVector K (f.caller.peer.ctx₂ i) (f.claim₂ i) (f.w₂ i) (q₂ i) r k) ∧
    a.1.2 = treeSimCheckWaiting K D live (.digests ds) (fun i =>
      (challenge K (realCheckGadgets K (f.caller.peer.ctx₁ i))).run (st₁ i) >>=
        finalAfterCoin K (f.caller.peer.ctx₁ i) (f.claim₁ i) (f.w₁ i) (q₁ i)
          (f.finish₁ K circuits settings top tree D parameter openings i)) ∧
    b.1.2 = treeSimCheckWaiting K D live (.digests ds) (fun i =>
      (challenge K (realCheckGadgets K (f.caller.peer.ctx₂ i))).run (st₂ i) >>=
        finalAfterCoin K (f.caller.peer.ctx₂ i) (f.claim₂ i) (f.w₂ i) (q₂ i)
          (f.finish₂ K circuits settings top tree D parameter openings i))

/-- The eleven fixed kinds; the final field and digest are internal segment boundaries. -/
def segKinds : List ((HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop) :=
  [CollectorStage K circuits settings top tree D A parameter openings,
   PeerStage K circuits settings top tree D A parameter openings,
   RerandStage K circuits settings top tree D A parameter openings,
   RerandCoinStage K circuits settings top tree D A parameter openings,
   TreeTwinExtendChallengeStage K D (SavedRel K circuits settings top tree D parameter openings),
   TreeTwinChallengeCoinStage K D (SavedRel K circuits settings top tree D parameter openings),
   TreeTwinStoppedCoinStage K D, StoppedExtendStage K D,
   FinalCoinEqualStage K circuits settings top tree D A parameter openings,
   FinalOpenEqualStage K circuits settings top tree D A parameter openings,
   OutputStage K circuits settings top tree D A parameter openings]

/-- The single fixed relation used by every segment kind. -/
def segReq := treeTwinReq D (treeTwinDataStage K D (fun _ => False)
  (segKinds K circuits settings top tree D A parameter openings))

/-- A guessed Coin endpoint, including both stopped branches. -/
def GuessEnd (c : E) := treeTwinReq D (fun _ δ a b =>
  TreeTwinDoneStage a b ∨ TreeTwinStoppedCoinStage K D δ a b ∨
    FinalCoinAt K circuits settings top tree D A parameter openings c δ a b)

/-- A saved finishing Coin whose honest entrants are all live. -/
def FinishingCoinLive (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ (q : TreeStagesExtendMultChallenge K D) (rnd : C.Party → PrssOutput C E)
    (sent : C.Party → Mail C E) (coinRnd : C.Party → PrssOutput C E),
    SavedFinishing K circuits settings top tree D parameter openings q ∧
    (∀ i, i ∉ D.1 → (q.coinNext K D rnd δ sent).live i = true) ∧
    (∀ x, ¬ Hidden D x.1.1 → δ x = 0) ∧
    TreeSimFutureZero (q.label + 2) δ ∧
    TreeSimFutureEmpty (q.label + 2) a.2.1.2 ∧ TreeSimFutureEmpty (q.label + 2) b.2.2 ∧
    a.1.2 = treeSimCoinPartial K D (q.coinNext K D rnd δ sent).live
      (q.coinNext K D rnd δ sent).count coinRnd (q.coinNext K D rnd δ sent).st₁
      (q.coinNext K D rnd δ sent).next₁ ∧
    b.1.2 = treeSimCoinPartial K D (q.coinNext K D rnd δ sent).live
      (q.coinNext K D rnd δ sent).count coinRnd (q.coinNext K D rnd δ sent).st₂
      (q.coinNext K D rnd δ sent).next₂

/-- Both pending Coin programs give the same total decoder. -/
theorem finalCoinAt_decoder_eq (c : E) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (h : FinalCoinAt K circuits settings top tree D A parameter openings c δ a b) :
    coinOf K D a.1.2 = coinOf K D b.1.2 := by
  obtain ⟨f, st₁, st₂, q₁, q₂, rnd, offset, L, _, _, _, _, _, _, left, right⟩ := h
  rw [left, right, coinOf_waiting, coinOf_waiting]

/-- A guessed endpoint lies in the fixed relation on its own decoder cell. -/
theorem guessEnd_cell (c : E) (n : ℕ) (δ : HiddenAddress C → Bit)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (h : GuessEnd K circuits settings top tree D A parameter openings c n δ a b)
    (cell : coinOf K D a.1.2 = c) :
    coinOf K D b.1.2 = c ∧ segReq K circuits settings top tree D A parameter openings n δ a b := by
  obtain ⟨related, state, done, flags, stage⟩ := h
  rcases stage with stopped | stopped | final
  · refine ⟨?_, related, state, done, flags, Or.inl stopped⟩
    rw [stopped.1] at cell
    simpa only [stopped.2] using cell
  · have same : coinOf K D a.1.2 = coinOf K D b.1.2 := by
      obtain ⟨live, count, rnd, st₁, st₂, k₁, k₂, off, left, right⟩ := stopped
      rw [left, right]
      exact coinOf_partial_eq K D live off count rnd st₁ st₂ k₁ k₂
    refine ⟨same.symm.trans cell, related, state, done, flags, Or.inr (Or.inr ⟨_, ?_, stopped⟩)⟩
    simp [segKinds]
  · have same := finalCoinAt_decoder_eq K circuits settings top tree D A parameter openings c δ a b final
    refine ⟨same.symm.trans cell, related, state, done, flags, Or.inr (Or.inr ⟨
      FinalCoinEqualStage K circuits settings top tree D A parameter openings, ?_, ?_⟩)⟩
    · simp [segKinds]
    · simpa only [FinalCoinEqualStage, cell] using final

end Stages

variable (prims : Primitives) (circuits : Circuits) (settings : Settings)
section Fields
variable (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
  (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
  (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
  (r : Unit × HashCache C)

/-- A fixed source kind's one-round contract into `segKinds`. -/
def SegNext (Kind : (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
    TreeSimConfig A (HashCache C × HiddenCache C) → Prop) : Prop :=
  TreeTwinKindNext prims K circuits settings top tree D A parameter seeds pairs z p r (fun _ => False)
    (segKinds K circuits settings top tree D A parameter p.1.2) Kind

/-- Entry into the fixed segment relation. -/
def SegEntry : Prop :=
  TreeTwinEntry3 prims K circuits settings top tree D A parameter seeds pairs z p r
    (segReq K circuits settings top tree D A parameter p.1.2)

/-- Three actual driver rounds from one live saved finishing Coin. -/
def FinalSegmentFor : Prop :=
  ∀ n δ swaps (a : TreeSimConfig A (TreeSimState C)) b,
    TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
      p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
    n + 3 ≤ ceremonyFuel circuits settings →
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
    ¬ AllDone D a.1.2 → (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
    segReq K circuits settings top tree D A parameter p.1.2 n δ (a.1, treeStagesTwin swaps a.2) b →
    FinishingCoinLive K circuits settings top tree D A parameter p.1.2 δ (a.1, treeStagesTwin swaps a.2) b →
    SegStepAt prims K circuits settings top tree D A parameter seeds pairs z
      (segReq K circuits settings top tree D A parameter p.1.2) 3 n a b

/-- Pointwise guessed segments glue because the decoder ignores salt swaps. -/
theorem segStepAt_glue
    (Req : ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    {J : Type} [Inhabited J]
    (Guess : J → ℕ → (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (key : (C.Party → Step C E RealSpec TreeOutput) → J)
    (cell : ∀ j n δ (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)),
      Guess j n δ a b → key a.1.2 = j → key b.1.2 = j ∧ Req n δ a b)
    (k n : ℕ) (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (guesses : ∀ j, SegStepAt prims K circuits settings top tree D A parameter seeds pairs z (Guess j) k n a b) :
    SegStepAt prims K circuits settings top tree D A parameter seeds pairs z Req k n a b := by
  refine ⟨(guesses default).1, ?_⟩
  apply TreeTwinGlue.relTriple_glue _ _ _ (fun u => key u.1.2) (fun v => key v.1.2)
    (twinR D A Req (n + k))
  intro j
  apply relTriple_post_mono (guesses j).2
  rintro u v (bad | ⟨swaps, δ, salts, h⟩)
  · exact Or.inl bad
  · refine Or.inr (fun eq => ?_)
    obtain ⟨keyEq, req⟩ := cell j (n + k) δ (u.1, treeStagesTwin swaps u.2) v h eq
    exact ⟨keyEq, swaps, δ, salts, req⟩

/-- The family of actual guessed runs supplies the one fixed final segment. -/
theorem finalSegmentFor_of_guesses
    (guesses : ∀ n δ swaps (a : TreeSimConfig A (TreeSimState C)) b,
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      n + 3 ≤ ceremonyFuel circuits settings →
      ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2 →
      ¬ AllDone D a.1.2 → (∀ x ∈ swaps, TreeSimHiddenSalt D a.2.2 x.1) →
      segReq K circuits settings top tree D A parameter p.1.2 n δ (a.1, treeStagesTwin swaps a.2) b →
      FinishingCoinLive K circuits settings top tree D A parameter p.1.2 δ (a.1, treeStagesTwin swaps a.2) b →
      ∀ c, SegStepAt prims K circuits settings top tree D A parameter seeds pairs z
        (GuessEnd K circuits settings top tree D A parameter p.1.2 c) 3 n a b) :
    FinalSegmentFor K prims circuits settings top tree D A parameter seeds pairs z p r := by
  intro n δ swaps a b reach bound good active salts req stage
  letI : Inhabited E := ⟨0⟩
  exact segStepAt_glue K prims circuits settings top tree D A parameter seeds pairs z
    (segReq K circuits settings top tree D A parameter p.1.2)
    (GuessEnd K circuits settings top tree D A parameter p.1.2) (coinOf K D)
    (guessEnd_cell K circuits settings top tree D A parameter p.1.2)
    3 n a b (guesses n δ swaps a b reach bound good active salts req stage)

/-- The three data-layer transitions for the same kind list. -/
def SegLayersAt : Prop :=
  SegNext K prims circuits settings top tree D A parameter seeds pairs z p r
    (CollectorStage K circuits settings top tree D A parameter p.1.2) ∧
  SegNext K prims circuits settings top tree D A parameter seeds pairs z p r
    (PeerStage K circuits settings top tree D A parameter p.1.2) ∧
  SegNext K prims circuits settings top tree D A parameter seeds pairs z p r
    (RerandStage K circuits settings top tree D A parameter p.1.2)

/-- Dispatch the fixed kinds, using three rounds only for live finishing Coins. -/
theorem segStep_of_kinds
    (padding : r ∈ support ((simulateQ (localAnswer prims)
      (TreeTwinLinked2.padding K circuits settings tree parameter seeds)).run p.2.2.1.1))
    (drawn : TreeTwinDigestDrawnGoal3 prims K circuits settings top tree D A parameter seeds pairs z p r)
    (layers : SegLayersAt K prims circuits settings top tree D A parameter seeds pairs z p r)
    (rerand : SegNext K prims circuits settings top tree D A parameter seeds pairs z p r
      (RerandCoinStage K circuits settings top tree D A parameter p.1.2))
    (final : FinalSegmentFor K prims circuits settings top tree D A parameter seeds pairs z p r)
    (coin : SegNext K prims circuits settings top tree D A parameter seeds pairs z p r
      (FinalCoinEqualStage K circuits settings top tree D A parameter p.1.2))
    (opening : SegNext K prims circuits settings top tree D A parameter seeds pairs z p r
      (FinalOpenEqualStage K circuits settings top tree D A parameter p.1.2))
    (output : SegNext K prims circuits settings top tree D A parameter seeds pairs z p r
      (OutputStage K circuits settings top tree D A parameter p.1.2)) :
    TreeTwinSegStep prims K circuits settings top tree D A parameter seeds pairs z p r
      (segReq K circuits settings top tree D A parameter p.1.2) := by
  rintro n a b reach bound good active ⟨swaps, δ, salts, req⟩
  have one (Kind : (HiddenAddress C → Bit) → TreeSimConfig A (TreeSimState C) →
      TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
      (next : SegNext K prims circuits settings top tree D A parameter seeds pairs z p r Kind)
      (stage : Kind δ (a.1, treeStagesTwin swaps a.2) b) :
      ∃ k, 0 < k ∧ SegStepAt prims K circuits settings top tree D A parameter seeds pairs z
        (segReq K circuits settings top tree D A parameter p.1.2) k n a b := by
    refine ⟨1, by omega, ?_⟩
    exact segStepAt_of_round prims K circuits settings top tree D A parameter seeds pairs z p r
      (segReq K circuits settings top tree D A parameter p.1.2) drawn n δ swaps a b reach bound good
      active (fun h => active (req.2.2.1.mpr h)) salts
      (next n δ swaps a b reach bound good active salts req stage)
  rcases req.2.2.2.2 with done | collector | ⟨Kind, mem, stage⟩
  · exact (active fun i _ => by rw [done.1]; trivial).elim
  · obtain ⟨_, _, allowed, _⟩ := collector
    exact allowed.elim
  · simp only [segKinds, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact one _ layers.1 stage
    · exact one _ layers.2.1 stage
    · exact one _ layers.2.2 stage
    · exact one _ rerand stage
    · exact one _ (treeTwinKindNext_extendChallenge prims K circuits settings top tree D A
        parameter seeds pairs z p r (fun _ => False)
        (SavedRel K circuits settings top tree D parameter p.1.2) _ (by simp [segKinds])) stage
    · obtain ⟨q, rnd, sent, coinRnd, saved, visible, future, fresh₁, fresh₂, left, right⟩ := stage
      rcases savedRel_cases saved with advancing | finishing
      · exact one _ (treeTwinKindNext_savedAdvancing prims K circuits settings top tree D A
          parameter p.1.2 seeds pairs z p r (fun _ => False) _ padding
          (by simp [segKinds]) (by simp [segKinds]))
          ⟨q, rnd, sent, coinRnd, advancing, visible, future, fresh₁, fresh₂, left, right⟩
      · by_cases live : ∀ i, i ∉ D.1 → (q.coinNext K D rnd δ sent).live i = true
        · exact ⟨3, by omega, final n δ swaps a b reach bound good active salts req
            ⟨q, rnd, sent, coinRnd, finishing, live, visible, future, fresh₁, fresh₂, left, right⟩⟩
        · push Not at live
          exact one _ (treeTwinKindNext_stoppedCoin prims K circuits settings top tree D A
            parameter seeds pairs z p r (fun _ => False) _)
            ⟨(q.coinNext K D rnd δ sent).live, (q.coinNext K D rnd δ sent).count, coinRnd,
              (q.coinNext K D rnd δ sent).st₁, (q.coinNext K D rnd δ sent).st₂,
              (q.coinNext K D rnd δ sent).next₁, (q.coinNext K D rnd δ sent).next₂,
              live, left, right⟩
    · exact one _ (treeTwinKindNext_stoppedCoin prims K circuits settings top tree D A
        parameter seeds pairs z p r (fun _ => False) _) stage
    · exact one _ (treeTwinKindNext_stoppedExtend prims K circuits settings top tree D A
        parameter seeds pairs z p r (fun _ => False) _) stage
    · exact one _ coin stage
    · exact one _ opening stage
    · exact one _ output stage

end Fields

/-- A statement at each good prefix and each result of the fixed padding. -/
def AtGoodPrefix
    (P : ∀ (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
      (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
      (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
      (r : Unit × HashCache C), Prop) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ¬ TreeSimBad3 prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z p.2.2.2 →
    ∀ r ∈ support ((simulateQ (localAnswer prims)
      (TreeTwinLinked2.padding K circuits settings tree parameter seeds)).run p.2.2.1.1),
    P top tree D A parameter seeds pairs z p r

/-- The fixed entry contract at every good prefix. -/
def SegEntryGoal : Prop :=
  AtGoodPrefix K prims circuits settings (SegEntry K prims circuits settings)

/-- The three fixed data-layer kinds at every good prefix. -/
def SegLayersGoal : Prop :=
  AtGoodPrefix K prims circuits settings (SegLayersAt K prims circuits settings)

/-- The initial check Coin kind at every good prefix. -/
def SegRerandCoinGoal : Prop :=
  AtGoodPrefix K prims circuits settings (fun top tree D A parameter seeds pairs z p r =>
    SegNext K prims circuits settings top tree D A parameter seeds pairs z p r
      (RerandCoinStage K circuits settings top tree D A parameter p.1.2))

/-- The three-round finishing segment at every good prefix. -/
def FinalSegmentGoal : Prop :=
  AtGoodPrefix K prims circuits settings (FinalSegmentFor K prims circuits settings)

/-- The final Coin kind at every good prefix. -/
def SegFinalCoinGoal : Prop :=
  AtGoodPrefix K prims circuits settings (fun top tree D A parameter seeds pairs z p r =>
    SegNext K prims circuits settings top tree D A parameter seeds pairs z p r
      (FinalCoinEqualStage K circuits settings top tree D A parameter p.1.2))

/-- The equal final-opening kind at every good prefix. -/
def SegFinalOpenGoal : Prop :=
  AtGoodPrefix K prims circuits settings (fun top tree D A parameter seeds pairs z p r =>
    SegNext K prims circuits settings top tree D A parameter seeds pairs z p r
      (FinalOpenEqualStage K circuits settings top tree D A parameter p.1.2))

/-- The final output kind at every good prefix. -/
def SegOutputGoal : Prop :=
  AtGoodPrefix K prims circuits settings (fun top tree D A parameter seeds pairs z p r =>
    SegNext K prims circuits settings top tree D A parameter seeds pairs z p r
      (OutputStage K circuits settings top tree D A parameter p.1.2))

/-- The fixed padding and fixed kinds give the segment core from seven concrete inputs. -/
theorem treeTwinSegCoreGoal3_of_segmentKinds
    (entry : SegEntryGoal K prims circuits settings)
    (layers : SegLayersGoal K prims circuits settings)
    (rerand : SegRerandCoinGoal K prims circuits settings)
    (final : FinalSegmentGoal K prims circuits settings)
    (coin : SegFinalCoinGoal K prims circuits settings)
    (opening : SegFinalOpenGoal K prims circuits settings)
    (output : SegOutputGoal K prims circuits settings) :
    TreeTwinSegCoreGoal3 prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq small p hp good
  refine ⟨TreeTwinLinked2.padding K circuits settings tree parameter seeds, ?_⟩
  intro r hr
  refine ⟨treeTwinDataStage K D (fun _ => False)
    (segKinds K circuits settings top tree D A parameter p.1.2),
    entry hb top tree D A parameter seeds pairs z Z q hq small p hp good r hr, ?_⟩
  have drawn := treeTwinDigestGoal3_of_segments circuits prims K settings
    (treeLockstepSegments K circuits settings prims) hb top tree D A parameter seeds pairs z p hp
    (TreeTwinLinked2.padding K circuits settings tree parameter seeds) r hr
  exact segStep_of_kinds K prims circuits settings top tree D A parameter seeds pairs z p r hr drawn
    (layers hb top tree D A parameter seeds pairs z Z q hq small p hp good r hr)
    (rerand hb top tree D A parameter seeds pairs z Z q hq small p hp good r hr)
    (final hb top tree D A parameter seeds pairs z Z q hq small p hp good r hr)
    (coin hb top tree D A parameter seeds pairs z Z q hq small p hp good r hr)
    (opening hb top tree D A parameter seeds pairs z Z q hq small p hp good r hr)
    (output hb top tree D A parameter seeds pairs z Z q hq small p hp good r hr)

/-- The original ceremony coupling from the seven fixed segment contracts. -/
theorem treeSimCeremonyGoal3_of_segmentKinds
    (entry : SegEntryGoal K prims circuits settings)
    (layers : SegLayersGoal K prims circuits settings)
    (rerand : SegRerandCoinGoal K prims circuits settings)
    (final : FinalSegmentGoal K prims circuits settings)
    (coin : SegFinalCoinGoal K prims circuits settings)
    (opening : SegFinalOpenGoal K prims circuits settings)
    (output : SegOutputGoal K prims circuits settings) :
    TreeSimCeremonyGoal3 prims K circuits settings :=
  treeSimCeremonyGoal3_of_segments prims K circuits settings
    (treeTwinSegCoreGoal3_of_segmentKinds K prims circuits settings entry layers rerand final coin opening output)

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.resumeCoin_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms resumeCoin_tail

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.coinShare_coinStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coinShare_coinStep

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.coinShare_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coinShare_tail

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.coinOf_waiting' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coinOf_waiting

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.coinOutput_eq_coinValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coinOutput_eq_coinValue

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.coinOf_partial_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coinOf_partial_eq

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.challengeAt_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms challengeAt_some

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.challengeAt_swapAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms challengeAt_swapAll

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.challengeAt_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms challengeAt_mono

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.finalCoinAt_decoder_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalCoinAt_decoder_eq

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.guessEnd_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guessEnd_cell

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.segStepAt_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms segStepAt_glue

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.finalSegmentFor_of_guesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finalSegmentFor_of_guesses

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.segStep_of_kinds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms segStep_of_kinds

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.treeTwinSegCoreGoal3_of_segmentKinds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinSegCoreGoal3_of_segmentKinds

/-- info: 'ThresholdLeanXmssSecurity.TreeTwinSegment.treeSimCeremonyGoal3_of_segmentKinds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimCeremonyGoal3_of_segmentKinds


end ThresholdLeanXmssSecurity.TreeTwinSegment
