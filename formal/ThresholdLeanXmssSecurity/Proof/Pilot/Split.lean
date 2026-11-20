import ThresholdLeanXmssSecurity.Proof.BatchCheck.LocalSplit
import ThresholdLeanXmssSecurity.Proof.BatchCheck.Programs
import ThresholdLeanXmssSecurity.Proof.CeremonyHybrid.PhaseQuiet
import ThresholdLeanXmssSecurity.Proof.Pilot.Join

/-!
# The split of the check before the salts, and the pilot with split copies

The check cuts into its head `checkHeadOf` and its rest `checkRestOf`. `PilotSplit` is the case of the
pilot where the honest copies of the tuples disagree. This file gives it from the trace facts
`SplitAcceptEvidence` of an accepted check.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

open RealNetworkC1s

attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support

/-! ## Quiet runs -/

section Quiet

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-- A timed program and then a quiet rest with a round. The local work at the end of the first program
is before the last round of the sequence. -/
theorem timedQuiet_timed_bind {α β : Type} {m n : ℕ} {p : PartyM C E G α} {k : α → PartyM C E G β}
    (hp : Timed m p.run) (hk : ∀ a, TimedQuiet (n + 1) (k a).run) : TimedQuiet (m + (n + 1)) (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change TimedQuiet (m + (n + 1)) (p.run >>= fun a => a.elim (pure none) (fun a => (k a).run))
  generalize p.run = oa at hp ⊢
  induction hp with
  | abort m => simpa only [pure_bind, Option.elim_none] using TimedQuiet.abort (α := β) (m + (n + 1))
  | done a => simpa only [pure_bind, Option.elim_some, Nat.zero_add] using hk a
  | queryLocal m q f _ ih => exact TimedQuiet.queryLocal (m + n) q _ ih
  | round m out f _ ih =>
    rw [Nat.add_right_comm m 1 (n + 1)]
    exact TimedQuiet.round (m + (n + 1)) out _ ih
  | call m input f _ ih =>
    rw [Nat.add_right_comm m 1 (n + 1)]
    exact TimedQuiet.call (m + (n + 1)) input _ ih

/-- A run of `p` from each state takes exactly `n` rounds or calls on each path that does not abort,
and it makes no local query after the last one. -/
def RunQuiet {α : Type} (n : ℕ) (p : RunM C E G α) : Prop :=
  ∀ st, TimedQuiet n (p.run st).run

theorem RunQuiet.of_eq {α : Type} {m n : ℕ} {p : RunM C E G α} (hp : RunQuiet m p) (h : m = n) : RunQuiet n p :=
  h ▸ hp

theorem RunQuiet.bind {α β : Type} {m n : ℕ} {p : RunM C E G α} {q : α → RunM C E G β} (hp : RunQuiet m p)
    (hq : ∀ a, RunQuiet n (q a)) : RunQuiet (m + n) (p >>= q) := fun st => by
  rw [StateT.run_bind]
  exact (hp st).bind fun r => hq r.1 r.2

theorem RunQuiet.timed_bind {α β : Type} {m n : ℕ} {p : RunM C E G α} {q : α → RunM C E G β}
    (hp : RunTimed m p) (hq : ∀ a, RunQuiet (n + 1) (q a)) : RunQuiet (m + (n + 1)) (p >>= q) := fun st => by
  rw [StateT.run_bind]
  exact timedQuiet_timed_bind (hp st) fun r => hq r.1 r.2

theorem RunQuiet.timed_bind_eq {α β : Type} {m n k : ℕ} {p : RunM C E G α} {q : α → RunM C E G β}
    (hp : RunTimed m p) (hq : ∀ a, RunQuiet (n + 1) (q a)) (h : m + (n + 1) = k) : RunQuiet k (p >>= q) :=
  (RunQuiet.timed_bind hp hq).of_eq h

theorem runQuiet_pure {α : Type} (a : α) : RunQuiet 0 (pure a : RunM C E G α) := fun st => by
  rw [StateT.run_pure]
  exact timedQuiet_pure _

theorem runQuiet_modify (u : RunState C → RunState C) : RunQuiet 0 (modify u : RunM C E G PUnit) := fun st => by
  rw [StateT.run_modify]
  exact timedQuiet_pure _

theorem runQuiet_exchange (out : Mail C E) :
    RunQuiet 1 (StateT.lift (exchange out) : RunM C E G (Mail C E)) := fun st => by
  rw [StateT.run_lift]
  exact TimedQuiet.exchange_bind 0 out _ fun _ => timedQuiet_pure _

end Quiet

/-! ## The real head is quiet -/

section HeadQuiet

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}
  (K : Constants C E) (ctx : Context C)

attribute [local instance] inhabitedField

/-- `Reshare` takes one round and makes no local query. -/
theorem runQuiet_reshare {R : Type} [Field R] (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R)
    (count : ℕ) : RunQuiet 1 (reshare (G := G) K ctx codec randomness v count) := by
  obtain ⟨r, Z⟩ := randomness
  unfold reshare record
  exact RunQuiet.bind (m := 1) (n := 0) (runQuiet_exchange _) fun _ =>
    RunQuiet.bind (m := 0) (n := 0) (runQuiet_modify _) fun _ => runQuiet_pure _

/-- The real `extendMult` draws its randomness and then takes the one round of `Reshare`. -/
theorem runQuiet_realExtendMult (products : List (Product C E)) :
    RunQuiet 1 ((realCheckBuildingBlocks (G := G) K ctx).extendMult products) :=
  RunQuiet.timed_bind (m := 0) (n := 0) (runTimed_prssRandomness ctx _ 0 _) fun _ => runQuiet_reshare K ctx _ _ _ _

/-- The real head takes `2 * R + 2` rounds, and the reshare of the mask is its last step. -/
theorem runQuiet_checkHeadOf_real (tuples : List (Tuple C)) :
    RunQuiet (2 * halvings (tuples.map (·.count)).sum + 2)
      (checkHeadOf K ctx (realCheckBuildingBlocks (G := G) K ctx) tuples) := by
  have hs : sliceBits ≤ halvings (tuples.map (·.count)).sum := Nat.le_add_right _ _
  unfold checkHeadOf
  refine RunQuiet.timed_bind_eq (n := 2 * halvings (tuples.map (·.count)).sum)
    (runTimed_coinKey K _ (runTimed_realCoin K ctx)) (fun key => ?_) (by omega)
  refine RunQuiet.timed_bind_eq (n := 2 * halvings (tuples.map (·.count)).sum)
    (runTimed_expand K key _) (fun τ => ?_) (by omega)
  refine RunQuiet.timed_bind_eq (n := 2 * halvings (tuples.map (·.count)).sum)
    (RunTimed.lift (timed_require _)) (fun _ => ?_) (by omega)
  refine RunQuiet.timed_bind_eq (n := 2 * (halvings (tuples.map (·.count)).sum - sliceBits)) (RunTimed.foldlM _
    (runTimed_sliceStep K ctx _ (runTimed_realCoin K ctx) (runTimed_realExtendMult K ctx) τ _) _ _) (fun p => ?_)
    (by rw [List.length_range]; omega)
  refine RunQuiet.timed_bind_eq (n := 0) (RunTimed.foldlM _
    (runTimed_halvingStep K ctx _ (runTimed_realCoin K ctx) (runTimed_realExtendMult K ctx) _) _ _) (fun p' => ?_)
    (by rw [List.length_range]; omega)
  refine RunQuiet.timed_bind_eq (n := 0) (runTimed_prssRandomness ctx _ 1 2) (fun w => ?_) (by omega)
  exact RunQuiet.bind (m := 1) (n := 0) (runQuiet_realExtendMult K ctx _) fun _ => runQuiet_pure _

end HeadQuiet

/-! ## The head only appends to the histories -/

section Grows

variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}

/-- Each history of the state `s'` extends the history of the state `s` at the same term. -/
def HistoryGrows (s s' : RunState C) : Prop := ∀ T, ∃ rest, s'.history T = s.history T ++ rest

theorem historyGrows_refl (s : RunState C) : HistoryGrows s s := fun _ => ⟨[], (List.append_nil _).symm⟩

theorem historyGrows_trans (s₁ s₂ s₃ : RunState C) (h₁ : HistoryGrows s₁ s₂) (h₂ : HistoryGrows s₂ s₃) :
    HistoryGrows s₁ s₃ := fun T => by
  obtain ⟨r₁, e₁⟩ := h₁ T
  obtain ⟨r₂, e₂⟩ := h₂ T
  exact ⟨r₁ ++ r₂, by rw [e₂, e₁, List.append_assoc]⟩

theorem moves_grows_bind {α β : Type} {p : RunM C E G α} {q : α → RunM C E G β} (hp : Moves HistoryGrows p)
    (hq : ∀ a, Moves HistoryGrows (q a)) : Moves HistoryGrows (p >>= q) :=
  moves_bind hp hq historyGrows_trans

theorem moves_grows_lift {α : Type} (x : PartyM C E G α) : Moves HistoryGrows (StateT.lift x : RunM C E G α) :=
  moves_lift historyGrows_refl x

theorem moves_grows_pure {α : Type} (a : α) : Moves HistoryGrows (pure a : RunM C E G α) :=
  moves_pure historyGrows_refl a

theorem moves_grows_foldlM {β γ : Type} (f : β → γ → RunM C E G β) (hf : ∀ b c, Moves HistoryGrows (f b c)) :
    ∀ (l : List γ) (init : β), Moves HistoryGrows (l.foldlM f init)
  | [], init => moves_grows_pure init
  | c :: l, init => by
    rw [List.foldlM_cons]
    exact moves_grows_bind (hf init c) fun b => moves_grows_foldlM f hf l b

/-- Each call of a building block of `B` only appends to the histories. -/
structure GrowingBlocks (B : CheckBuildingBlocks C E G) : Prop where
  coin : ∀ n, Moves HistoryGrows (B.coin n)
  extendMult : ∀ products, Moves HistoryGrows (B.extendMult products)
  randElements : ∀ n, Moves HistoryGrows (B.randElements n)
  randBits : ∀ n, Moves HistoryGrows (B.randBits n)

end Grows

section HeadGrows

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] {ι : Type} {G : OracleSpec ι}
  (K : Constants C E) (ctx : Context C)

attribute [local instance] inhabitedField

theorem moves_grows_coinKey {B : CheckBuildingBlocks C E G} (hB : GrowingBlocks B) :
    Moves HistoryGrows (coinKey K B) := by
  unfold coinKey
  exact moves_grows_bind (moves_get historyGrows_refl) fun _ =>
    moves_grows_bind (hB.coin 2) fun _ => moves_grows_lift _

theorem moves_grows_challenge {B : CheckBuildingBlocks C E G} (hB : GrowingBlocks B) :
    Moves HistoryGrows (challenge K B) := by
  unfold challenge
  refine moves_grows_bind (moves_grows_coinKey K hB) fun _ => moves_grows_bind (moves_grows_lift _) fun o => ?_
  cases o
  · exact moves_grows_lift _
  · exact moves_grows_pure _

/-- The head of a check only appends to the histories, when each building block does. -/
theorem moves_checkHeadOf {B : CheckBuildingBlocks C E G} (hB : GrowingBlocks B) (tuples : List (Tuple C)) :
    Moves HistoryGrows (checkHeadOf K ctx B tuples) := by
  unfold checkHeadOf
  refine moves_grows_bind (moves_grows_coinKey K hB) fun _ => moves_grows_bind (moves_grows_lift _) fun _ =>
    moves_grows_bind (moves_grows_lift _) fun _ => moves_grows_bind (moves_grows_foldlM _ (fun x j => ?_) _ _)
      fun _ => moves_grows_bind (moves_grows_foldlM _ (fun x j => ?_) _ _) fun _ =>
        moves_grows_bind (hB.randElements 2) fun _ => moves_grows_bind (hB.extendMult _) fun _ => moves_grows_pure _
  · obtain ⟨xs, ys, D⟩ := x
    unfold sliceStep
    exact moves_grows_bind (hB.extendMult _) fun _ => moves_grows_bind (moves_grows_challenge K hB) fun _ =>
      moves_grows_pure _
  · obtain ⟨A, B', D⟩ := x
    unfold halvingStep
    exact moves_grows_bind (hB.extendMult _) fun _ => moves_grows_bind (moves_grows_challenge K hB) fun _ =>
      moves_grows_pure _

omit [Field E] [Algebra Bit E] in
theorem moves_grows_prssRandomness {R : Type} [Zero R] (codec : Codec C E R) (idx count : ℕ) :
    Moves HistoryGrows (prssRandomness (G := G) ctx codec idx count) := by
  unfold prssRandomness
  exact moves_grows_bind (moves_modifyGet _ fun s => historyGrows_refl s) fun _ =>
    moves_grows_bind (moves_grows_lift _) fun _ => moves_grows_bind (moves_grows_lift _) fun _ => moves_grows_pure _

/-- `record` appends to the histories of the held terms. -/
theorem moves_grows_record {R : Type} (codec : Codec C E R) (mode : ReshareMode) (z : Shares C R) (count : ℕ) :
    Moves HistoryGrows (record (G := G) K ctx codec mode z count) := by
  unfold record
  refine moves_modify _ fun s T => ?_
  dsimp only
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨[], (List.append_nil _).symm⟩

theorem moves_grows_reshare {R : Type} [Field R] (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R)
    (count : ℕ) : Moves HistoryGrows (reshare (G := G) K ctx codec randomness v count) := by
  obtain ⟨r, Z⟩ := randomness
  unfold reshare
  exact moves_grows_bind (moves_grows_lift _) fun _ =>
    moves_grows_bind (moves_grows_record K ctx _ _ _ _) fun _ => moves_grows_pure _

/-- The real building blocks only append to the histories. -/
theorem growingBlocks_real : GrowingBlocks (realCheckBuildingBlocks (G := G) K ctx) where
  coin n := moves_grows_bind (moves_grows_prssRandomness ctx _ 1 n) fun _ => by
    unfold coinWith
    exact moves_grows_bind (moves_grows_lift _) fun _ => moves_grows_pure _
  extendMult _ := moves_grows_bind (moves_grows_prssRandomness ctx _ 0 _) fun _ => moves_grows_reshare K ctx _ _ _ _
  randElements n := moves_grows_prssRandomness ctx _ 1 n
  randBits n := moves_grows_prssRandomness ctx bitCodec 2 n

end HeadGrows

/-! ## The split of the pilot -/

section Pilot

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E] (K : Constants C E)

attribute [local instance] inhabitedField

omit [Field E] [Algebra Bit E] in
/-- A run on `worldRoles` depends only on the programs of the honest operators. It is
`executePhase_congr` of `Proof/CeremonyHybrid/Phase.lean` for `worldRoles`. -/
theorem executePhase_congr_world {I O Lk Rk Ia α : Type} (D : C.Coalition) (A : Adversary C E Ia Lk Rk)
    (F : Functionality C I O Lk Rk) (fuel : ℕ) (st : A.State) (p p' : C.Party → PartyM C E (CallSpec I O) α)
    (h : ∀ i, i ∉ D.1 → p i = p' i) :
    executePhase worldRoles D A F fuel st p = executePhase worldRoles D A F fuel st p' := by
  unfold executePhase startSteps
  congr 2
  funext i
  by_cases hi : i ∈ D.1
  · simp only [hi, ↓reduceIte]
  · simp only [hi, ↓reduceIte, h i hi]

/-- Each history of the state `s` extends the history `h` at the same term. -/
def HistoryExtends (h : C.Term → List Bit) (s : RunState C) : Prop := ∀ T, ∃ rest, s.history T = h T ++ rest

/-- The head of the real check of operator `i` in the pilot, with its end state. -/
def pilotHead (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (x : C.Party → List (Tuple C)) (L tg : ℕ)
    (i : C.Party) : PartyM C E RealSpec ((E × E × E × Shares C E × Shares C E) × RunState C) :=
  (checkHeadOf K (pilotContext keys prss i) (realCheckBuildingBlocks K (pilotContext keys prss i)) (x i)).run
    (pilotStart K x L tg i)

/-- The rest of the real check of operator `i` in the pilot, from the output and the end state of its
head. It aborts unless each history extends `filledHistory`. -/
def pilotRest (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (x : C.Party → List (Tuple C))
    (i : C.Party) (r : (E × E × E × Shares C E × Shares C E) × RunState C) : PartyM C E RealSpec Unit :=
  if HistoryExtends (filledHistory K i (x i)) r.2 then
    (checkRestOf K (pilotContext keys prss i) (realCheckBuildingBlocks K (pilotContext keys prss i)) r.1).run' r.2
  else failure

/-- The program of operator `i` in the pilot is its head and then its rest. -/
theorem pilotProgram_split (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (x : C.Party → List (Tuple C))
    (L tg : ℕ) (i : C.Party) (h : ((x i).map (·.count)).sum ≠ 0) :
    (check K (pilotContext keys prss i) (realCheckBuildingBlocks K (pilotContext keys prss i)) (x i)).run'
        ⟨filledHistory K i (x i), L, tg⟩ =
      pilotHead K keys prss x L tg i >>= pilotRest K keys prss x i := by
  rw [check_headOf_restOf K _ _ (x i) h, StateT.run'_eq, StateT.run_bind, map_bind]
  refine moves_checkHeadOf K _ (growingBlocks_real K _) (x i) (pilotStart K x L tg i) _ _ fun a s hs => ?_
  have he : HistoryExtends (filledHistory K i (x i)) s := hs
  simp only [pilotRest, he, ↓reduceIte, StateT.run'_eq]

/-- The split of the pilot before the salts. The heads take `2 * R + 2` steps on `worldRoles`, and the
rests take the 6 other steps of `checkRounds`. Each rest runs from the end state of its head, whose
histories extend `filledHistory`. The equation is one of programs of `WorldSpec C`, so it holds under
each handler. -/
theorem pilotRun_split (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (keys : C.Party → Keys C)
    (prss : C.Party → PrssKeys C) (counts : List ℕ) (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State)
    (hsum : counts.sum ≠ 0) (hx : ∀ i, i ∉ D.1 → (x i).map (·.count) = counts) :
    pilotRun K D net keys prss counts x L tg st =
      executePhase worldRoles D net noFunctionality (2 * halvings counts.sum + 2) st
          (pilotHead K keys prss x L tg) >>= fun r =>
        executePhase worldRoles D net noFunctionality 6 r.1 fun i => (r.2 i).elim failure (pilotRest K keys prss x i) := by
  unfold pilotRun
  rw [show checkRounds counts.sum = (2 * halvings counts.sum + 2) + 6 by unfold checkRounds; omega,
    executePhase_congr_world D net noFunctionality _ st _
      (fun i => pilotHead K keys prss x L tg i >>= pilotRest K keys prss x i)
      fun i hi => pilotProgram_split K keys prss x L tg i (by rw [hx i hi]; exact hsum)]
  refine executePhase_bind_eq D net noFunctionality _ _ st _ _ fun i hi => ?_
  have hq := runQuiet_checkHeadOf_real (G := RealSpec) K (pilotContext keys prss i) (x i) (pilotStart K x L tg i)
  rw [hx i hi] at hq
  exact hq

end Pilot

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The birthday bound in `streamWorld` -/

/-- A call of a run in the world that adds a cell of `P` to the hash cache, on the counted copy or
on the free copy. -/
def WorldRegionCounted (P : Query C → Prop) : (WorldSpec C).Domain → Prop
  | .inl (.inl u) => SplitRegionCounted P u
  | .inl (.inr _) => False
  | .inr u => SplitRegionCounted P u

/-- A call of a run in the world that programs the hash cache. -/
def WorldProgramQuery : (WorldSpec C).Domain → Prop
  | .inl (.inr _) => True
  | _ => False

/-- A step on the hash cache and then a continuation in `streamWorld` give the same hash cache as
the step and the continuation with the cache of the hidden streams fixed. -/
lemma onHash_bind_run {β γ : Type} (m : StateT (HashCache C) ProbComp β)
    (F : β → StateT (HashCache C × HiddenCache C) ProbComp γ) (cache : HashCache C)
    (hidden : HiddenCache C) (E : HashCache C → Prop) :
    Pr{let z ← (onHash m >>= F).run (cache, hidden)}[E z.2.1] =
      Pr{let z ← (m >>= fun r => StateT.mk fun c =>
        (fun z => (z.1, z.2.1)) <$> (F r).run (c, hidden)).run cache}[E z.2] := by
  simp [StateT.run_bind, onHash]

/-- One local call on the hash cache in `streamWorld` adds its birthday term to the bound of the
continuation. -/
lemma streamRegion_local_step (prims : Primitives) (P : Query C → Prop) (u : (LocalSpec C).Domain)
    {γ : Type} (F : (LocalSpec C).Range u → StateT (HashCache C × HiddenCache C) ProbComp γ)
    (n k : ℕ) (hn : ¬ SplitRegionCounted P u ∨ 0 < n) (cache : HashCache C) (hidden : HiddenCache C)
    (hno : ¬ CacheHasCollision (splitRegionCache P cache))
    (hk : SplitCacheBound (splitRegionCache P cache) k)
    (hF : ∀ n' k', (SplitRegionCounted P u → n' = n - 1 ∧ k' = k + 1) →
      (¬ SplitRegionCounted P u → n' = n ∧ k' = k) → ∀ r s,
      ¬ CacheHasCollision (splitRegionCache P s) → SplitCacheBound (splitRegionCache P s) k' →
      Pr{let z ← (F r).run (s, hidden)}[CacheHasCollision (splitRegionCache P z.2.1)] ≤
        ∑ j ∈ Finset.range n', ((k' + j : ℕ) : ℝ≥0∞) / 2 ^ 256) :
    Pr{let z ← (onHash (localAnswer prims u) >>= F).run (cache, hidden)}[
      CacheHasCollision (splitRegionCache P z.2.1)] ≤
      ∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [onHash_bind_run _ _ _ _ (fun c => CacheHasCollision (splitRegionCache P c))]
  cases he : splitLocalHashInput u with
  | none =>
    obtain ⟨p, hp⟩ := splitLocalHashInput_none prims u he
    have ht : ¬ SplitRegionCounted P u := by simp [SplitRegionCounted, he]
    rw [hp]
    simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
    apply prEvent_bind_le_of_forall_le_of_support
    intro r _
    simp only [StateT.run_mk, prEvent_map]
    exact hF n k (fun h => (ht h).elim) (fun _ => ⟨rfl, rfl⟩) r cache hno hk
  | some q =>
    obtain ⟨g, hg⟩ := splitLocalHashInput_some prims u q he
    have ht : SplitRegionCounted P u ↔ P q := by simp [SplitRegionCounted, he]
    rw [hg, bind_map_left]
    by_cases hq : P q
    · have hcount := ht.mpr hq
      have hnpos : 0 < n := hn.resolve_left (not_not.mpr hcount)
      have hsum : (k : ℝ≥0∞) / 2 ^ 256 +
          ∑ j ∈ Finset.range (n - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) / 2 ^ 256 =
          ∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
        conv_rhs => rw [show n = (n - 1) + 1 from by omega]
        rw [Finset.sum_range_succ']
        simp only [Nat.add_zero]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [show k + 1 + j = k + (j + 1) by omega]
      rw [← hsum]
      have h := splitRegion_random_bind P q (fun v => StateT.mk fun c =>
          (fun z => (z.1, z.2.1)) <$> (F (g v)).run (c, hidden))
        cache k hno hk (∑ j ∈ Finset.range (n - 1), ((k + 1 + j : ℕ) : ℝ≥0∞) / 2 ^ 256) (by
          intro v s hs hsk
          simp only [StateT.run_mk, prEvent_map]
          exact hF (n - 1) (k + 1) (fun _ => ⟨rfl, rfl⟩) (fun h => (h hcount).elim) (g v) s hs
            (by simpa [hq] using hsk))
      simpa [hq] using h
    · have hcount : ¬ SplitRegionCounted P u := fun h => hq (ht.mp h)
      have h := splitRegion_random_bind P q (fun v => StateT.mk fun c =>
          (fun z => (z.1, z.2.1)) <$> (F (g v)).run (c, hidden))
        cache k hno hk (∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256) (by
          intro v s hs hsk
          simp only [StateT.run_mk, prEvent_map]
          exact hF n k (fun h => (hcount h).elim) (fun _ => ⟨rfl, rfl⟩) (g v) s hs
            (by simpa [hq] using hsk))
      simpa [hq] using h

/-- The bound of `streamRegion_birthday_aux` at a local call on the hash cache, from the bound of
each continuation. -/
lemma streamRegion_local_case (prims : Primitives) (D : C.Coalition) (P : Query C → Prop) {α : Type}
    (u : (LocalSpec C).Domain) (f : (LocalSpec C).Range u → OracleComp (WorldSpec C) α) (n k : ℕ)
    (hn : ¬ SplitRegionCounted P u ∨ 0 < n)
    (hf : ∀ r, IsQueryBoundP (f r) (WorldRegionCounted P) (if SplitRegionCounted P u then n - 1 else n))
    (hp : ∀ r, IsQueryBoundP (f r) WorldProgramQuery 0)
    (ih : ∀ r (n k : ℕ), IsQueryBoundP (f r) (WorldRegionCounted P) n →
      IsQueryBoundP (f r) WorldProgramQuery 0 →
      ∀ (cache : HashCache C) (hidden : HiddenCache C), ¬ CacheHasCollision (splitRegionCache P cache) →
      SplitCacheBound (splitRegionCache P cache) k →
      Pr{let z ← (simulateQ (streamWorld prims D) (f r)).run (cache, hidden)}[
        CacheHasCollision (splitRegionCache P z.2.1)] ≤
        ∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256)
    (cache : HashCache C) (hidden : HiddenCache C)
    (hno : ¬ CacheHasCollision (splitRegionCache P cache))
    (hk : SplitCacheBound (splitRegionCache P cache) k) :
    Pr{let z ← (onHash (localAnswer prims u) >>= fun r =>
      simulateQ (streamWorld prims D) (f r)).run (cache, hidden)}[
      CacheHasCollision (splitRegionCache P z.2.1)] ≤
      ∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  apply streamRegion_local_step prims P u _ n k hn cache hidden hno hk
  intro n' k' h1 h2 r s hs hsk
  by_cases hc : SplitRegionCounted P u
  · obtain ⟨rfl, rfl⟩ := h1 hc
    exact ih r _ _ (by simpa [hc] using hf r) (hp r) s hidden hs hsk
  · obtain ⟨rfl, rfl⟩ := h2 hc
    exact ih r _ _ (by simpa [hc] using hf r) (hp r) s hidden hs hsk

/-- The birthday bound of the history and digest cells in `streamWorld`. A run with at most `n`
calls on the cells of `P` and no programming call adds a collision of these cells to a cache with
at most `k` such cells with probability at most `∑ j < n, (k + j) / 2^256`. -/
theorem streamRegion_birthday_aux (prims : Primitives) (D : C.Coalition) (P : Query C → Prop)
    {α : Type} (oa : OracleComp (WorldSpec C) α) : ∀ (n k : ℕ),
    IsQueryBoundP oa (WorldRegionCounted P) n → IsQueryBoundP oa WorldProgramQuery 0 →
    ∀ (cache : HashCache C) (hidden : HiddenCache C), ¬ CacheHasCollision (splitRegionCache P cache) →
    SplitCacheBound (splitRegionCache P cache) k →
    Pr{let z ← (simulateQ (streamWorld prims D) oa).run (cache, hidden)}[
      CacheHasCollision (splitRegionCache P z.2.1)] ≤
      ∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n k _ _ cache hidden hno _
    simp [hno]
  | query_bind t f ih =>
    intro n k hn hp cache hidden hno hk
    rw [isQueryBoundP_query_bind_iff] at hn hp
    change Pr{let z ← (streamWorld prims D t >>= fun u =>
      simulateQ (streamWorld prims D) (f u)).run (cache, hidden)}[
        CacheHasCollision (splitRegionCache P z.2.1)] ≤ _
    have hp' : ∀ r, IsQueryBoundP (f r) WorldProgramQuery 0 := fun r => by
      simpa using hp.2 r
    rcases t with (u | p) | (v | q | x)
    · exact streamRegion_local_case prims D P u f n k hn.1 hn.2 hp' ih cache hidden hno hk
    · exact absurd hp.1 (by simp [WorldProgramQuery])
    · exact streamRegion_local_case prims D P (.inl v) f n k hn.1 hn.2 hp' ih cache hidden hno hk
    · exact streamRegion_local_case prims D P (.inr (.inl q)) f n k hn.1 hn.2 hp' ih cache hidden
        hno hk
    · by_cases hx : Hidden D x.1
      · rw [show streamWorld prims D (Sum.inr (Sum.inr (Sum.inr x))) = _ from ite_eq_left_of_eq_true _ _ (eq_true hx),
          StateT.run_bind, StateT.run_mk, bind_map_left]
        apply prEvent_bind_le_of_forall_le_of_support
        intro r _
        exact ih r.1 n k ((hn.2 r.1).mono (by split_ifs <;> omega)) (hp' r.1) cache r.2 hno hk
      · rw [show streamWorld prims D (Sum.inr (Sum.inr (Sum.inr x))) =
          onHash (localAnswer prims (.inr (.inr x))) from ite_eq_right_of_eq_false _ _ (eq_false hx)]
        exact streamRegion_local_case prims D P (.inr (.inr x)) f n k hn.1 hn.2 hp' ih cache hidden
          hno hk

/-- The birthday bound of `streamRegion_birthday_aux` as the real `splitRisk k n`. -/
theorem streamRegion_birthday_real (prims : Primitives) (D : C.Coalition) {α : Type}
    (oa : OracleComp (WorldSpec C) α) (n k : ℕ)
    (hn : IsQueryBoundP oa (WorldRegionCounted SplitHashDomain) n)
    (hp : IsQueryBoundP oa WorldProgramQuery 0) (cache : HashCache C) (hidden : HiddenCache C)
    (hno : ¬ CacheHasCollision (splitRegionCache SplitHashDomain cache))
    (hk : SplitCacheBound (splitRegionCache SplitHashDomain cache) k) :
    (Pr{let z ← (simulateQ (streamWorld prims D) oa).run (cache, hidden)}[
      CacheHasCollision (splitRegionCache SplitHashDomain z.2.1)]).toReal ≤ splitRisk k n := by
  have hfin : ∀ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256 ≠ ⊤ := by
    intros; finiteness
  have h := ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr hfin)
    (streamRegion_birthday_aux prims D SplitHashDomain oa n k hn hp cache hidden hno hk)
  have hs : (∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ≥0∞) / 2 ^ 256).toReal =
      (∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ)) / 2 ^ 256 := by
    rw [ENNReal.toReal_sum hfin]
    simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
      ENNReal.toReal_ofNat, Finset.sum_div]
  rw [hs] at h
  refine h.trans ?_
  have hsum : ∀ n : ℕ, 2 * (∑ j ∈ Finset.range n, ((k + j : ℕ) : ℝ)) ≤
      ((k + n : ℕ) : ℝ) ^ 2 - (k : ℝ) ^ 2 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one] at *
      nlinarith
  have hden : (0 : ℝ) < 2 ^ 256 := by positivity
  unfold splitRisk
  apply (div_le_div_iff₀ hden (by positivity)).2
  nlinarith [hsum n]

/-! ## The calls of a phase on `worldRoles` in a region -/

section WorldBound

open ThresholdLeanXmssSecurity.RealNetworkALP (PartyCalls)
open ThresholdLeanXmssSecurity.RealNetworkCLp (LocalStepBound)

variable {E : Type} {ι : Type} {G : OracleSpec ι} {α β : Type} (P : Query C → Prop)

/-- The adversary side spends on the region what its local computation spends. -/
lemma adversary_regionBound {γ : Type} (oa : OracleComp (LocalSpec C) γ) :
    ∀ n, IsQueryBoundP oa (SplitRegionCounted P) n →
      IsQueryBoundP (worldRoles.adversary oa) (WorldRegionCounted P) n := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _
    rw [adversary_pure]
    exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    intro n h
    have hq : (liftM (OracleSpec.query t) : OracleComp (LocalSpec C) _) =
        OracleComp.lift (OracleSpec.query t) := rfl
    rw [isQueryBoundP_query_bind_iff] at h
    rw [hq, adversary_bind, adversary_query, isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

/-- Advancing a party on the free copy spends only its local budget. -/
theorem free_advance_bind_regionBound (oa : OracleComp (PartySpec C E G) (Option α))
    (k : Step C E G α → OracleComp (WorldSpec C) β) (extra : ℕ) :
    ∀ n, IsQueryBoundP oa (PartyCalls (E := E) (G := G) (SplitRegionCounted P)) n →
      (∀ st b, b ≤ n → LocalStepBound (SplitRegionCounted P) st b →
        IsQueryBoundP (k st) (WorldRegionCounted P) (extra + b)) →
      IsQueryBoundP (free (advance oa) >>= k) (WorldRegionCounted P) (extra + n) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ hk
    rw [advance_pure, free_pure, pure_bind]
    exact hk (.done a) n le_rfl trivial
  | query_bind t f ih =>
    intro n h hk
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with (q | outbox) | input
    · have e : free (advance (liftM (OracleSpec.query (Sum.inl (Sum.inl q))) >>= f)) =
          (liftM ((WorldSpec C).query (.inr q)) : OracleComp (WorldSpec C) _) >>=
            fun u => free (advance (f u)) := by
        rw [show (liftM (OracleSpec.query (Sum.inl (Sum.inl q))) : OracleComp (PartySpec C E G) _) =
          OracleComp.lift (OracleSpec.query (spec := PartySpec C E G) (Sum.inl (Sum.inl q))) from rfl,
          advance_query_bind, free_bind]
        rfl
      rw [e, bind_assoc, isQueryBoundP_query_bind_iff]
      constructor
      · by_cases hc : SplitRegionCounted P q
        · right
          have hn := h.1.resolve_left (not_not.mpr hc)
          omega
        · exact Or.inl hc
      · intro u
        have hb : (if PartyCalls (E := E) (G := G) (SplitRegionCounted P) (.inl (.inl q)) then n - 1
            else n) ≤ n := by
          split_ifs <;> omega
        have hi := ih u _ (h.2 u) (fun st b hb' hs => hk st b (hb'.trans hb) hs)
        apply hi.mono
        by_cases hc : SplitRegionCounted P q
        · have hp : PartyCalls (E := E) (G := G) (SplitRegionCounted P) (.inl (.inl q)) := hc
          have hw : WorldRegionCounted P (.inr q) := hc
          simp only [hp, hw, ite_true]
          have hn := h.1.resolve_left (not_not.mpr hp)
          omega
        · have hp : ¬ PartyCalls (E := E) (G := G) (SplitRegionCounted P) (.inl (.inl q)) := hc
          have hw : ¬ WorldRegionCounted P (.inr q) := hc
          simp only [hp, hw, ite_false]
          exact le_rfl
    · change IsQueryBoundP (free (pure (Step.wait outbox f)) >>= k) _ (extra + n)
      rw [free_pure, pure_bind]
      apply hk _ n le_rfl
      simpa [LocalStepBound, PartyCalls] using h.2
    · change IsQueryBoundP (free (pure (Step.call input f)) >>= k) _ (extra + n)
      rw [free_pure, pure_bind]
      apply hk _ n le_rfl
      simpa [LocalStepBound, PartyCalls] using h.2

/-- Advance the parties on the free copy one by one, with the residual budget of each. -/
theorem sequenceFin_free_advance_bind_regionBound : ∀ {N : ℕ}
    (oa : Fin N → OracleComp (PartySpec C E G) (Option α)) (budget : Fin N → ℕ)
    (_h : ∀ i, IsQueryBoundP (oa i) (PartyCalls (E := E) (G := G) (SplitRegionCounted P)) (budget i))
    (k : (Fin N → Step C E G α) → OracleComp (WorldSpec C) β) (extra : ℕ),
    (∀ st (b : Fin N → ℕ), (∀ i, b i ≤ budget i) →
      (∀ i, LocalStepBound (SplitRegionCounted P) (st i) (b i)) →
      IsQueryBoundP (k st) (WorldRegionCounted P) (extra + ∑ i, b i)) →
    IsQueryBoundP ((OverPermutation.sequenceFin fun i => free (advance (oa i))) >>= k)
      (WorldRegionCounted P) (extra + ∑ i, budget i)
  | 0, oa, budget, _, k, extra, hk => by
    simp only [OverPermutation.sequenceFin, pure_bind, Fin.sum_univ_zero, Nat.add_zero]
    simpa using hk Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | N + 1, oa, budget, h, k, extra, hk => by
    simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind]
    rw [Fin.sum_univ_succ]
    have he : extra + (budget 0 + ∑ i : Fin N, budget i.succ) =
        (extra + ∑ i : Fin N, budget i.succ) + budget 0 := by omega
    rw [he]
    refine free_advance_bind_regionBound P (oa 0) _ _ (budget 0) (h 0) (fun st0 b0 hb0 hs0 => ?_)
    have he' : (extra + ∑ i : Fin N, budget i.succ) + b0 =
        (extra + b0) + ∑ i : Fin N, budget i.succ := by omega
    rw [he']
    refine sequenceFin_free_advance_bind_regionBound (fun i : Fin N => oa i.succ)
      (fun i => budget i.succ) (fun i => h i.succ) (fun st => k (Fin.cases st0 st)) (extra + b0)
      (fun st b hb hs => ?_)
    have hp := hk (Fin.cases st0 st) (Fin.cases b0 b)
      (fun i => Fin.cases hb0 hb i) (fun i => Fin.cases hs0 hs i)
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hp

variable {O Ia : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)
    (F : Functionality C PEmpty O PEmpty PEmpty)

lemma stepRound_bind_regionBound (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) (SplitRegionCounted P) step)
    (state : A.State) (steps : C.Party → Step C E (CallSpec PEmpty O) α) (budget : C.Party → ℕ)
    (h : ∀ j, LocalStepBound (SplitRegionCounted P) (steps j) (budget j))
    (k : (A.State × (C.Party → Step C E (CallSpec PEmpty O) α) × (C.Party → C.Party → Option (Msg E))) →
      OracleComp (WorldSpec C) β) (extra : ℕ)
    (hk : ∀ st (b : C.Party → ℕ), (∀ j, b j ≤ budget j) →
      (∀ j, LocalStepBound (SplitRegionCounted P) (st.2.1 j) (b j)) →
      IsQueryBoundP (k st) (WorldRegionCounted P) (extra + ∑ j, b j)) :
    IsQueryBoundP (stepRound worldRoles D A F state steps >>= k) (WorldRegionCounted P)
      (step + extra + ∑ j, budget j) := by
  unfold stepRound
  split_ifs with hcall
  · obtain ⟨i, -, hi⟩ := hcall.1
    obtain ⟨e, -⟩ := Option.isSome_iff_exists.mp hi
    exact e.elim
  · simp only [bind_assoc, pure_bind]
    apply (isQueryBoundP_bind (m := extra + ∑ j, budget j)
      (adversary_regionBound P _ _ (hr _ _)) (fun result _ => ?_)).mono (by omega)
    have he : (fun j => match steps j with
        | .done out => pure (Step.done out)
        | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
            worldRoles.honest (advance (resume fun k => if k ∈ D.1 then result.2 k j else
              (steps k).delivered j))
        | .call _ _ => pure (Step.done none)) =
        fun j => free (advance (roundResume D result.2 steps j)) := by
      funext j
      cases hs : steps j with
      | done out => simp only [roundResume, hs]; rfl
      | call input k => simp only [roundResume, hs]; rfl
      | wait out k => simp only [roundResume, hs]; split_ifs <;> rfl
    have hseq := sequenceFin_free_advance_bind_regionBound P
      (fun j => roundResume D result.2 steps j) budget
      (ThresholdLeanXmssSecurity.RealNetworkCLp.roundResume_localBound D result.2 steps budget h)
      (fun st => k (result.1, st, result.2)) extra
      (fun st b hb hs => hk (result.1, st, result.2) b hb hs)
    convert (congrArg (fun f : C.Party → OracleComp (WorldSpec C) (Step C E (CallSpec PEmpty O) α) =>
      IsQueryBoundP (OverPermutation.sequenceFin f >>= fun st => k (result.1, st, result.2))
        (WorldRegionCounted P) (extra + ∑ j, budget j)) he).mpr hseq using 1
    congr 2
    funext j
    cases steps j <;> rfl

lemma executeRounds_regionBound (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) (SplitRegionCounted P) step) :
    ∀ fuel state (steps : C.Party → Step C E (CallSpec PEmpty O) α) (budget : C.Party → ℕ),
      (∀ j, LocalStepBound (SplitRegionCounted P) (steps j) (budget j)) →
      IsQueryBoundP (executeRounds worldRoles D A F fuel state steps) (WorldRegionCounted P)
        (fuel * step + ∑ j, budget j)
  | 0, state, steps, budget, h => isQueryBoundP_pure _ _ _
  | fuel + 1, state, steps, budget, h => by
    unfold executeRounds
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · refine (stepRound_bind_regionBound P D A F step hr state steps budget h _ (fuel * step)
        ?_).mono ?_
      · intro st b hb hs
        exact executeRounds_regionBound step hr fuel st.1 st.2.1 b hs
      · simp [Nat.succ_mul, Nat.add_comm, Nat.add_assoc]

/-- A phase on `worldRoles` makes at most `step` calls in the region for each round of the
adversary, and the calls of the honest programs. -/
lemma executePhase_regionBound (step : ℕ)
    (hr : ∀ state sent, IsQueryBoundP (A.round state sent) (SplitRegionCounted P) step)
    (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E (CallSpec PEmpty O) α)
    (budget : C.Party → ℕ)
    (hp : ∀ j, j ∉ D.1 → IsQueryBoundP (program j).run
      (PartyCalls (E := E) (G := CallSpec PEmpty O) (SplitRegionCounted P)) (budget j)) :
    IsQueryBoundP (executePhase worldRoles D A F fuel state program) (WorldRegionCounted P)
      (fuel * step + ∑ j, budget j) := by
  unfold executePhase startSteps
  have he : (fun i => if i ∈ D.1 then pure (Step.done none) else
      worldRoles.honest (advance (program i).run)) =
      fun i => free (advance (if i ∈ D.1 then pure none else (program i).run)) := by
    funext i
    split_ifs <;> rfl
  change IsQueryBoundP ((OverPermutation.sequenceFin _) >>= _) _ _
  rw [he]
  apply sequenceFin_free_advance_bind_regionBound P _ budget
  · intro j
    split_ifs with hj
    · exact isQueryBoundP_pure _ _ _
    · exact hp j hj
  · intro st b hb hs
    exact executeRounds_regionBound P D A F step hr fuel state st b hs

end WorldBound

/-! ## The premises and the case with split copies -/

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (prims : Primitives) (K : Constants C E)

/-- An honest operator accepts the check with split copies only on a collision of the history and
digest cells. On each outcome of `pilotRun` in `streamWorld` with the premises of `PilotSplit`, an
honest accept implies a collision of these cells in the end cache. -/
def SplitAcceptCollides : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ),
    (∀ st sent, IsQueryBoundP (net.round st sent) Counted step) →
    ∀ (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (counts : List ℕ)
      (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State) (cache : HashCache C)
      (hidden : HiddenCache C) (seen : Finset (Query C)) (expansionKeys : Finset HashOutput)
      (salts : Finset (List Bit)) (split : ℕ),
      TupleInputs K counts D x →
      ¬ MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) →
      PrssKeysAgree D prss → StreamsFresh D L prss hidden →
      PilotCache L cache seen expansionKeys salts split →
      ∀ z ∈ support ((simulateQ (streamWorld prims D)
        (pilotRun K D net keys prss counts x L tg st)).run (cache, hidden)),
        (∃ i, i ∉ D.1 ∧ z.1.2 i = some ()) → CacheHasCollision (splitRegionCache SplitHashDomain z.2.1)

/-- The calls of `pilotRun` on the history and digest cells. The adversary makes at most `step` of
them in each of the `checkRounds counts.sum` rounds and the honest operators at most
`termHashes C`. No call of `pilotRun` programs the hash cache. -/
def PilotRegionBound : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ),
    (∀ st sent, IsQueryBoundP (net.round st sent) Counted step) →
    ∀ (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (counts : List ℕ)
      (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State),
      TupleInputs K counts D x →
      IsQueryBoundP (pilotRun K D net keys prss counts x L tg st) (WorldRegionCounted SplitHashDomain)
        (checkRounds counts.sum * step + termHashes C) ∧
      IsQueryBoundP (pilotRun K D net keys prss counts x L tg st) WorldProgramQuery 0

/-- A computation makes no call of a predicate that holds at no call. -/
lemma isQueryBoundP_zero_of_forall_not {ι' γ : Type} {spec : OracleSpec ι'} (p : ι' → Prop)
    (hp : ∀ t, ¬ p t) (oa : OracleComp spec γ) : IsQueryBoundP oa p 0 := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact isQueryBoundP_pure _ _ _
  | query_bind t f ih =>
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (hp t), fun u => by simpa only [hp t, ite_false] using ih u⟩

omit [Fintype E] [DecidableEq E] in
/-- `pilotRun` makes at most `step` calls on the history and digest cells in each round of the
adversary and `2 * C.terms.length` at each honest operator, and no programming call. -/
theorem pilotRegionBound : PilotRegionBound K := by
  intro D net step hstep keys prss counts x L tg st _
  constructor
  · have hprog : ∀ j, j ∉ D.1 → IsQueryBoundP
        ((check (G := RealSpec) K (pilotContext keys prss j)
          (realCheckBuildingBlocks K (pilotContext keys prss j)) (x j)).run' ⟨filledHistory K j (x j), L, tg⟩).run
        (ThresholdLeanXmssSecurity.RealNetworkALP.PartyCalls (E := E) (G := RealSpec)
          (SplitRegionCounted SplitHashDomain)) (2 * C.terms.length) := by
      intro j _
      have h := ThresholdLeanXmssSecurity.RealNetworkCLp.realCheck_split (G := RealSpec) K
        (pilotContext keys prss j) (x j) ⟨filledHistory K j (x j), L, tg⟩
      unfold StateT.run'
      rw [map_eq_bind_pure_comp]
      exact (ThresholdLeanXmssSecurity.RealNetworkCLp.SplitPartyBound.bind h (m := 0)
        (fun _ => isQueryBoundP_pure _ _ _)).mono (by omega)
    have h := executePhase_regionBound SplitHashDomain D net noFunctionality step
      (fun s sent => counted_splitRegionBound SplitHashDomain (hstep s sent))
      (checkRounds counts.sum) st _ (fun _ => 2 * C.terms.length) hprog
    refine h.mono ?_
    have hsum : ∑ _j : C.Party, 2 * C.terms.length = termHashes C := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, termHashes,
        check_terms_length, termCount]
      ring
    omega
  · exact ThresholdLeanXmssSecurity.executePhase_free WorldProgramQuery (fun _ h => h) D net
      noFunctionality _ st _ fun i _ => isQueryBoundP_zero_of_forall_not _ (by
        rintro ((t | t) | t) <;> simp [ThresholdLeanXmssSecurity.PartyFree, WorldProgramQuery]) _

/-- The trace facts of an accepted check. On each outcome of `pilotRun` in `streamWorld` with the
premises of `PilotSplit` where an honest operator accepts, there are histories `hist` and digest rows
`ds` of the honest operators such that

* each history of an honest operator extends its `filledHistory`,
* the end cache holds the history and digest cells of each honest digest of a known held term,
* two honest holders of a term have the same digest of it. -/
def SplitAcceptEvidence : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step : ℕ),
    (∀ st sent, IsQueryBoundP (net.round st sent) Counted step) →
    ∀ (keys : C.Party → Keys C) (prss : C.Party → PrssKeys C) (counts : List ℕ)
      (x : C.Party → List (Tuple C)) (L tg : ℕ) (st : net.State) (cache : HashCache C)
      (hidden : HiddenCache C) (seen : Finset (Query C)) (expansionKeys : Finset HashOutput)
      (salts : Finset (List Bit)) (split : ℕ),
      TupleInputs K counts D x →
      ¬ MultVerifyAgree D (fun i => if i ∈ D.1 then none else some (x i)) →
      PrssKeysAgree D prss → StreamsFresh D L prss hidden →
      PilotCache L cache seen expansionKeys salts split →
      ∀ z ∈ support ((simulateQ (streamWorld prims D)
        (pilotRun K D net keys prss counts x L tg st)).run (cache, hidden)),
        (∃ i, i ∉ D.1 ∧ z.1.2 i = some ()) →
        ∃ (hist : C.Party → C.Term → List Bit) (ds : C.Party → List HashOutput),
          (∀ a, a ∉ D.1 → ∀ T, ∃ rest, hist a T = filledHistory K a (x a) T ++ rest) ∧
          (∀ a, a ∉ D.1 → ∀ T, KnownTo D.1 T → a ∈ C.holders T → ∃ salt hv d,
            z.2.1 (.history (hist a T)) = some hv ∧ z.2.1 (.digest salt hv) = some d ∧
            (ds a)[C.terms.idxOf T]? = some d) ∧
          ∀ T a b, a ∉ D.1 → b ∉ D.1 → a ∈ C.holders T → b ∈ C.holders T →
            (ds a)[C.terms.idxOf T]? = (ds b)[C.terms.idxOf T]?

omit [DecidableEq E] in
/-- The trace facts of an accepted check with split copies give a collision of the history and
digest cells. Split histories of equal length stay distinct after any appends, and two equal
digests of distinct histories collide in the history or the digest cells. -/
theorem splitAcceptCollides_of_evidence (he : SplitAcceptEvidence prims K) :
    SplitAcceptCollides prims K := by
  intro D net step hstep keys prss counts x L tg st cache hidden seen expansionKeys salts split
    hx hsplit hagree hfresh hcache z hz hacc
  obtain ⟨hist, ds, hext, hcells, hsame⟩ := he D net step hstep keys prss counts x L tg st cache
    hidden seen expansionKeys salts split hx hsplit hagree hfresh hcache z hz hacc
  let : SampleableType E := SampleableType.ofFintype E
  obtain ⟨T, hT, a, b, ha, hb, haT, hbT, hlen, hne⟩ := splitInit_histories K counts D x hx hsplit
  obtain ⟨ra, hra⟩ := hext a ha T
  obtain ⟨rb, hrb⟩ := hext b hb T
  have hdiff : hist a T ≠ hist b T := by
    rw [hra, hrb]
    exact split_history_append_ne hlen hne ra rb
  obtain ⟨sa, va, da, hva, hda, hea⟩ := hcells a ha T hT haT
  obtain ⟨sb, vb, db, hvb, hdb, heb⟩ := hcells b hb T hT hbT
  have hd : da = db := Option.some.inj (hea.symm.trans ((hsame T a b ha hb haT hbT).trans heb))
  subst db
  exact splitHistories_cacheCollision (splitRegionCache SplitHashDomain z.2.1) _ _ sa sb va vb da
    hdiff (by simpa [splitRegionCache, SplitHashDomain] using hva)
    (by simpa [splitRegionCache, SplitHashDomain] using hvb)
    (by simpa [splitRegionCache, SplitHashDomain] using hda)
    (by simpa [splitRegionCache, SplitHashDomain] using hdb)

omit [Fintype E] [DecidableEq E] in
/-- The case of the pilot with split copies follows from `SplitAcceptCollides` and
`PilotRegionBound` by the birthday bound in `streamWorld`. -/
theorem pilotSplit_of_premises (hc : SplitAcceptCollides prims K) (hb : PilotRegionBound K) :
    PilotSplit prims K := by
  intro D net step hstep keys prss counts x L tg st cache hidden seen expansionKeys salts split
    hx hsplit hagree hfresh hcache
  obtain ⟨hregion, hprog⟩ := hb D net step hstep keys prss counts x L tg st hx
  unfold pilotOutputs pilotSplitError
  rw [StateT.run'_eq, prEvent_map]
  refine (ENNReal.toReal_mono (prEvent_ne_top _)
    (prEvent_mono_of_support _ _ _ (hc D net step hstep keys prss counts x L tg st cache hidden
      seen expansionKeys salts split hx hsplit hagree hfresh hcache))).trans ?_
  exact streamRegion_birthday_real prims D _ _ _ hregion hprog cache hidden hcache.2.2.2 hcache.2.2.1

omit [Fintype E] [DecidableEq E] in
/-- The case of the pilot with split copies from `SplitAcceptCollides`, with `pilotRegionBound`. -/
theorem pilotSplit_of_accept (hc : SplitAcceptCollides prims K) : PilotSplit prims K :=
  pilotSplit_of_premises prims K hc (pilotRegionBound K)

omit [DecidableEq E] in
/-- The case of the pilot with split copies from the trace facts `SplitAcceptEvidence`. -/
theorem pilotSplit_of_evidence (he : SplitAcceptEvidence prims K) : PilotSplit prims K :=
  pilotSplit_of_accept prims K (splitAcceptCollides_of_evidence prims K he)

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotRun_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotRun_split

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotSplit_of_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotSplit_of_premises

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotSplit_of_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.pilotSplit_of_evidence
