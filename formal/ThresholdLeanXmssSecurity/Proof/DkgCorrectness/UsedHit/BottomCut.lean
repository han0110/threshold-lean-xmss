import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Bottom
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.TopLaws

/-!
# The cut of a bottom run at its second setup

`slotProgram_bottom_cut` proves `BottomSlotProgramCut`. The counter of `slotCeremony` is `0` in the first
ceremony and `1` in the second, so the first ceremony reads `fresh 0` and the second reads `fresh 1`.
`BottomHeadSplit` states the split of a bottom run at the end of its head.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

attribute [local instance] Classical.propDecidable

/-! ## Programs with a counter at known values -/

section Pin

variable {P : Type → Type} [Monad P] [LawfulMonad P] {σ : Type}

/-- From counter `n`, the run of `x` ends at counter `n'` and drops to the run of `y`. -/
def Pins {α : Type} (n n' : ℕ) (x : StateT σ (StateT ℕ P) α) (y : StateT σ P α) : Prop :=
  ∀ s, (x.run s).run n = (fun p => (p, n')) <$> y.run s

/-- From counter `n`, the run of `x` with the counter dropped is the run of `y`. -/
def ErasesAt {α : Type} (n : ℕ) (x : StateT σ (StateT ℕ P) α) (y : StateT σ P α) : Prop :=
  ∀ s, Prod.fst <$> (x.run s).run n = y.run s

theorem pins_pure {α : Type} (n : ℕ) (a : α) : Pins n n (pure a : StateT σ (StateT ℕ P) α) (pure a) := by
  intro s
  simp

theorem pins_bind {α β : Type} {n n' n'' : ℕ} {x : StateT σ (StateT ℕ P) α} {y : StateT σ P α}
    {f : α → StateT σ (StateT ℕ P) β} {g : α → StateT σ P β} (hx : Pins n n' x y)
    (hf : ∀ a, Pins n' n'' (f a) (g a)) : Pins n n'' (x >>= f) (y >>= g) := by
  intro s
  rw [StateT.run_bind, StateT.run_bind, StateT.run_bind, hx s, bind_map_left, map_bind]
  exact bind_congr fun p => hf p.1 p.2

theorem pins_lift {α : Type} (n : ℕ) (x : P α) :
    Pins n n (StateT.lift (StateT.lift x) : StateT σ (StateT ℕ P) α) (StateT.lift x) := by
  intro s
  simp

theorem pins_get (n : ℕ) : Pins n n (get : StateT σ (StateT ℕ P) σ) get := by
  intro s
  simp

theorem pins_set (n : ℕ) (s' : σ) : Pins n n (set s' : StateT σ (StateT ℕ P) PUnit) (set s') := by
  intro s
  simp

theorem pins_mapM {α β : Type} (n : ℕ) {f : α → StateT σ (StateT ℕ P) β} {g : α → StateT σ P β}
    (hf : ∀ a, Pins n n (f a) (g a)) : ∀ l : List α, Pins n n (l.mapM f) (l.mapM g)
  | [] => by simpa using pins_pure (P := P) (σ := σ) n ([] : List β)
  | a :: l => by
    simp only [List.mapM_cons]
    exact pins_bind (hf a) fun b => pins_bind (pins_mapM n hf l) fun bs => pins_pure n _

theorem erasesAt_of_pins {α β : Type} {n n' : ℕ} {x : StateT σ (StateT ℕ P) α} {y : StateT σ P α}
    {f : α → StateT σ (StateT ℕ P) β} {g : α → StateT σ P β} (hx : Pins n n' x y)
    (hf : ∀ a, ErasesAt n' (f a) (g a)) : ErasesAt n (x >>= f) (y >>= g) := by
  intro s
  rw [StateT.run_bind, StateT.run_bind, StateT.run_bind, hx s, bind_map_left, map_bind]
  exact bind_congr fun p => hf p.1 p.2

theorem erasesAt_pure {α : Type} (n : ℕ) (a : α) : ErasesAt n (pure a : StateT σ (StateT ℕ P) α) (pure a) := by
  intro s
  simp

end Pin

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The tail of a bottom run in the hybrid. It is the second setup with the fresh keys `fresh` and the
signature ceremony, as `CheckTiming.bottomTail` with the overlay. -/
def tailWith (D : C.Coalition) (fresh : Option (FreshKeys C)) (i : C.Party) (operator : OperatorState C)
    (b : Fin (2 ^ layerHeight)) (x : HeadOut) : PartyM C E RealSpec TreeOutput :=
  match operator.keys, operator.top with
  | some keys, some top => prssSetup i >>= fun prss =>
      (secondAfter K circuits settings i keys top b x.1 (withFresh D i fresh prss)).run x.2 >>= fun p =>
        p.1.elim failure pure
  | _, _ => failure

/-- The cut of the program of a bottom run at its second setup, in the hybrid. It follows
`CheckTiming.treeProgram_bottom` and the erasure of `HybridStartProof`. -/
def BottomSlotProgramCut : Prop :=
  ∀ (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party) (operator : OperatorState C)
    (b : Fin (2 ^ layerHeight)),
    slotProgram K circuits settings D fresh i operator (.bottom b) =
      headWith K circuits settings D (fresh 0) i operator b >>= tailWith K circuits settings D (fresh 1) i operator b

/-- One ceremony of a slot from counter `n` reads `fresh n` and ends at counter `n + 1`. -/
theorem slotCeremony_pins (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party) (keys : Keys C)
    (jobs : List Job) (n : ℕ) :
    Pins n (n + 1) (slotCeremony K circuits settings D fresh i keys jobs)
      (StateT.lift (prssSetup i) >>= fun prss =>
        batchesWith K circuits settings i keys (withFresh D i (fresh n) prss) jobs) := by
  have hrest : Pins (n + 1) (n + 1)
      ((StateT.lift (StateT.lift (prssSetup i)) : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) _) >>= fun prss =>
        batched settings.batchSize (fun jobs => do
          let (label, k) ← get
          let inputs ← StateT.lift (StateT.lift (jobs.mapM
            (inputShares ⟨i, keys, ((fresh n).map (prssOverlay D i prss)).getD prss⟩)))
          let (outputs, state) ← StateT.lift (StateT.lift ((runJobs K (realRunBuildingBlocks K
            ⟨i, keys, ((fresh n).map (prssOverlay D i prss)).getD prss⟩ settings.mode)
            (jobs.map (circuits keys.parameter ·.kind)) inputs).run ⟨fun _ => [], label, k⟩))
          set (state.label, k + 1)
          pure (some outputs)) jobs)
      (StateT.lift (prssSetup i) >>= fun prss =>
        batchesWith K circuits settings i keys (withFresh D i (fresh n) prss) jobs) := by
    refine pins_bind (pins_lift _ _) fun prss => ?_
    unfold batched batchesWith
    refine pins_bind (pins_mapM _ (fun batch => ?_) _) fun _ => pins_pure _ _
    unfold realBatch
    refine pins_bind (pins_get _) fun lk => ?_
    obtain ⟨label, k⟩ := lk
    exact pins_bind (pins_lift _ _) fun inputs => pins_bind (pins_lift _ _) fun r =>
      pins_bind (pins_set _ _) fun _ => pins_pure _ _
  intro s
  have h := hrest s
  unfold slotCeremony
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, bind_assoc, pure_bind] at h ⊢
  exact h

/-- `ceremonyOutput` of a bottom tree with the run `run₁` for the first ceremony and `run₂` for the
second. -/
def bottomOutputTwo (parameter : PublicParameter) (run₁ run₂ : List Job → StateT (ℕ × ℕ) (PartyM C E RealSpec)
    (Option (List (List Bit)))) (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    StateT (ℕ × ℕ) (PartyM C E RealSpec) (Option TreeOutput) := do
  let keys := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
    (List.finRange chainCount).map fun l => (bottomKey b k, l)
  let some outputs ← run₁ (bottomJobs b) | pure none
  let cpk := fun (e : KeyIndex) (l : ChainIndex) =>
    let bits := outputs.getD (keys.idxOf (e, l)) []
    (digestAt bits 0, digestAt bits 1, digestAt bits 2)
  let commitment := fun (e : KeyIndex) => digestAt (outputs.getD (keys.length + e.val % 2 ^ layerHeight) []) 0
  let ρ := digestAt (outputs.getD (keys.length + 2 ^ layerHeight) []) 0
  let root ← StateT.lift (oracleStep (tweakable
    (merkleNode parameter bottomLayer (fun e l => (cpk e l).2.2) layerHeight b.val)))
  let message := littleEndianBytes 16 root
  let base ← StateT.lift (oracleStep (tweakable
    (truncateHash <$> Verification.oracleHashWithHash (randomizerInput parameter topLayer (topKey b) ρ message))))
  let some (randomness, encoding) ← StateT.lift (oracleStep (tweakable (grind parameter topLayer (topKey b) message
      base randomizerAttemptLimit 0))) | pure none
  let some values ← run₂ (signJobs b encoding) | pure none
  let path ← StateT.lift (oracleStep (tweakable (merklePath parameter topLayer top.chainEnd (topKey b))))
  let signature : LayerSignature := ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩
  let topRoot ← StateT.lift (oracleStep (tweakable
    (Verification.layerRootWithHash parameter topLayer (topKey b) message signature)))
  if topRoot ≠ some top.root then pure none else
  pure (some (.bottom ⟨cpk, commitment, root, signature⟩))

/-- The ceremonies of a bottom tree with the counter dropped. The first reads `fresh 0` and the second
reads `fresh 1`. -/
theorem slotTree_bottom_erasesAt (D : C.Coalition) (fresh : ℕ → Option (FreshKeys C)) (i : C.Party)
    (keys : Keys C) (top : TopTree) (b : Fin (2 ^ layerHeight)) :
    ErasesAt 0 (ceremonyOutput (m := StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)))
        (fun oa => StateT.lift (StateT.lift (oracleStep (tweakable oa)))) keys.parameter
        (slotCeremony K circuits settings D fresh i keys) top (.bottom b))
      (bottomOutputTwo keys.parameter
        (fun jobs => StateT.lift (prssSetup i) >>= fun prss =>
          batchesWith K circuits settings i keys (withFresh D i (fresh 0) prss) jobs)
        (fun jobs => StateT.lift (prssSetup i) >>= fun prss =>
          batchesWith K circuits settings i keys (withFresh D i (fresh 1) prss) jobs) top b) := by
  unfold ceremonyOutput bottomOutputTwo
  refine erasesAt_of_pins (slotCeremony_pins K circuits settings D fresh i keys _ 0) fun o => ?_
  rcases o with _ | outputs
  · exact erasesAt_pure _ _
  refine erasesAt_of_pins (pins_lift _ _) fun root => ?_
  refine erasesAt_of_pins (pins_lift _ _) fun base => ?_
  refine erasesAt_of_pins (pins_lift _ _) fun g => ?_
  rcases g with _ | ⟨randomness, encoding⟩
  · exact erasesAt_pure _ _
  refine erasesAt_of_pins (slotCeremony_pins K circuits settings D fresh i keys _ 1) fun o => ?_
  rcases o with _ | values
  · exact erasesAt_pure _ _
  refine erasesAt_of_pins (pins_lift _ _) fun path => ?_
  refine erasesAt_of_pins (pins_lift _ _) fun topRoot => ?_
  split_ifs
  · exact erasesAt_pure _ _
  · exact erasesAt_pure _ _

theorem bottomOutputTwo_eq (i : C.Party) (keys : Keys C) (top : TopTree) (b : Fin (2 ^ layerHeight))
    (f₁ f₂ : Option (FreshKeys C)) (D : C.Coalition) :
    bottomOutputTwo keys.parameter
        (fun jobs => StateT.lift (prssSetup i) >>= fun prss =>
          batchesWith K circuits settings i keys (withFresh D i f₁ prss) jobs)
        (fun jobs => StateT.lift (prssSetup i) >>= fun prss =>
          batchesWith K circuits settings i keys (withFresh D i f₂ prss) jobs) top b =
      (StateT.lift (prssSetup i) >>= fun prss => firstAfter K circuits settings i keys b (withFresh D i f₁ prss)) >>=
        fun o => o.elim (pure none) fun x =>
          StateT.lift (prssSetup i) >>= fun prss => secondAfter K circuits settings i keys top b x (withFresh D i f₂ prss) := by
  simp only [bottomOutputTwo, firstAfter, bind_assoc]
  refine bind_congr fun prss => bind_congr fun o => ?_
  rcases o with _ | outputs
  · simp only [pure_bind, Option.elim]
  · simp only [bind_assoc, bCpk, bRho, bottomKeys]
    refine bind_congr fun root => bind_congr fun base => bind_congr fun g => ?_
    rcases g with _ | ⟨randomness, encoding⟩
    · simp only [pure_bind, Option.elim]
    · simp only [pure_bind, Option.elim, secondAfter, signJobs]
      rfl

/-- `BottomSlotProgramCut`. -/
theorem slotProgram_bottom_cut : BottomSlotProgramCut K circuits settings := by
  intro D fresh i operator b
  unfold headWith tailWith slotProgram
  rcases hk : operator.keys with _ | keys <;> rcases ht : operator.top with _ | top <;>
    simp only [failure_bind]
  have h := slotTree_bottom_erasesAt K circuits settings D fresh i keys top b (0, 0)
  have h' : (fun x => x.1.1) <$> ((ceremonyOutput (m := StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)))
      (fun oa => StateT.lift (StateT.lift (oracleStep (tweakable oa)))) keys.parameter
      (slotCeremony K circuits settings D fresh i keys) top (.bottom b)).run (0, 0)).run 0 =
      Prod.fst <$> (bottomOutputTwo keys.parameter
        (fun jobs => StateT.lift (prssSetup i) >>= fun prss =>
          batchesWith K circuits settings i keys (withFresh D i (fresh 0) prss) jobs)
        (fun jobs => StateT.lift (prssSetup i) >>= fun prss =>
          batchesWith K circuits settings i keys (withFresh D i (fresh 1) prss) jobs) top b).run (0, 0) := by
    rw [← h, Functor.map_map]
  unfold slotTree
  simp only [StateT.run'_eq, StateT.run_map, Functor.map_map]
  rw [h', bottomOutputTwo_eq]
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, map_bind, pure_bind]
  refine bind_congr fun prss => bind_congr fun p => ?_
  rcases p with ⟨_ | x, st⟩
  · simp [Option.elim]
  · dsimp only [Option.elim]
    simp only [StateT.run_bind, StateT.run_lift, map_bind, bind_assoc, pure_bind]
    refine bind_congr fun prss2 => ?_
    rw [bind_map_left]
    refine bind_congr fun q => ?_
    rcases q with ⟨_ | out, st'⟩ <;> rfl

variable (prims : Primitives)

/-- The split of a bottom run at its second setup in `jointKeyWorld`, for honest operators with one
parameter. It is `WorldSplit.executePhase_split` with `jointKeyWorld` in place of `streamWorld`. -/
def BottomHeadSplit : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (st : net.State) (fresh : ℕ → Option (FreshKeys C))
    (operators : C.Party → OperatorState C) (b : Fin (2 ^ layerHeight)) (w : KeyJointState C)
    (parameter : PublicParameter),
    (∀ i, i ∉ D.1 → ∀ keys, (operators i).keys = some keys → keys.parameter = parameter) →
      (simulateQ (jointKeyWorld prims D false) (executePhase worldRoles D net noFunctionality
          (treeFuel circuits settings) st
          fun i => slotProgram K circuits settings D fresh i (operators i) (.bottom b))).run w =ᵈ
        (simulateQ (jointKeyWorld prims D false) (executePhase worldRoles D net noFunctionality
          (CheckTiming.firstRounds circuits settings parameter (.bottom b)) st
          (fun i => headWith K circuits settings D (fresh 0) i (operators i) b) >>= fun r =>
            executePhase worldRoles D net noFunctionality
              (treeFuel circuits settings - CheckTiming.firstRounds circuits settings parameter (.bottom b)) r.1
              fun i => (r.2 i).elim failure (tailWith K circuits settings D (fresh 1) i (operators i) b))).run w

end ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.slotProgram_bottom_cut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.UsedHit.slotProgram_bottom_cut
