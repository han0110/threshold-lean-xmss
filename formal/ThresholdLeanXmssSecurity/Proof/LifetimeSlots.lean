import ThresholdLeanXmssSecurity.Proof.LifetimeAllowance
import ThresholdLeanXmssSecurity.Proof.LifetimeKeygenHopFinal
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy

/-!
# The slot worlds of the lifetime simulation pass

This module states the simulation pass on the dealer-keygen world of `LifetimeHybridOrder` in the
form of `LifetimeAllowance.LifetimeAfterKeygen`, with one `streamKeyError` in each slot term.

* `slotOrder` lists the top slots before the bottom slots. When a bottom slot hops, every top run
  is ideal, so every honest operator holds the same top tree, the one that `F_tree` gives. The
  joint ceremony takes one top tree for all operators.
* `slotGame k sep` is the world `S_k` (`sep = false`): the slots before `k` run `F_tree` and the
  emulated `treeSimulator`, and the other slots run the real ceremony with ideal hidden streams in
  the one shared stream table of the dealer world. `S_0` is the dealer-keygen world itself. The
  world `T_k` (`sep = true`) runs slot `k` with its own stream table, as the joint hop does.
* Each ideal run keeps its own stream table, as `treeSimulator` does. Its dealer computation runs
  on the free copy, as in `idealExecution`. Its honest receivers are the emulated operators that
  end with an output, and they receive the output of `F_tree`.
* The slot hop splits in four parts. `SlotTransport` moves slot `k` from the shared table to its
  own table, with `streamKeyError`. `SlotEmulationHit` links `T_k` and `S_{k+1}` to the two sides
  of the joint hop of slot `k`, with `seedHitError (q₀ + q)`. The joint hop
  (`JointSimulationHopFrom`, the tree side) pays `treeCheckError + (treeHashError - keySplit)`.
  `LifetimeForger` bounds the world with every slot ideal.
* `slotInstance` is the joint instance of slot `k`: a selector that computes the tables of
  `F_tree` for every tree within `cap q₀`, and a ceremony adversary and a distinguisher that
  emulate the lifetime around slot `k`, each segment within `cap Q`. `SlotSuspension` states that
  this instance meets the premises of the joint hop with the budgets `q₀` and `(fuel + 2) Q`.
* If `2 ^ 128 ≤ q₀ + q`, the slot hop is a difference of probabilities, so it is at most
  `1 ≤ treeHashError - keySplit`. The transport and the emulation link need only the case
  `q₀ + q < 2 ^ 128`, and the hash allowance is spent once.
* `lifetimeSecurity_of_slots` gives the original `LifetimeSecurityStatementSampled` from
  `LifetimePrfTransportSmallSplit`, the joint hop for every `Th`, `SlotTransport`,
  `SlotEmulationHit` and `LifetimeForger`. The keygen hop is
  `lifetimeKeygenHop_of_hasLifetimeQueryBound`.

The instance is built so that each capped part makes at most the counted calls of the matching
part of a real lifetime: the tables of the selector replace the dealer computation and the clear
evaluation of the emulated simulators, and the programmed points and the hidden streams are private
tables. The emulation link needs the caps never to cut a run of a slot world. The link also
needs the honest operators of a ceremony to end within `ceremonyFuel` rounds, because the joint
ceremony does not show the adversary the messages after its last round. The pinned and current
leanVM proof directories have no lifetime slot emulation; the module reuses `jointError_fixed_tree`,
`capAdversary_queryBound`, `compileWorld` and `LifetimeTranscriptReplay`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace ThresholdLeanXmssSecurity.LifetimeSlots

open LifetimeJointLink LifetimeHybridOrder

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## The slot order -/

theorem slotOrder_card (attempts : ℕ) : attempts + 2 ^ layerHeight * attempts = lifetimeRuns attempts := by
  simp only [lifetimeRuns]
  ring

/-- The top slots first, then the bottom slots by tree and attempt. -/
def slotOrder (attempts : ℕ) : Slot attempts ≃ Fin (lifetimeRuns attempts) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans
    (finSumFinEquiv.trans (finCongr (slotOrder_card attempts)))

theorem slotOrder_top (attempts : ℕ) (k : Fin attempts) :
    ((slotOrder attempts) (.inl k)).val = k.val := by
  simp [slotOrder]

theorem slotOrder_bottom (attempts : ℕ) (x : Fin (2 ^ layerHeight) × Fin attempts) :
    attempts ≤ ((slotOrder attempts) (.inr x)).val := by
  simp [slotOrder]

/-- The slot sum telescopes in the order of `slotOrder`. -/
theorem slotOrder_hybrid_bound (attempts : ℕ) (p : ℕ → ℝ) (e : Tree → ℝ)
    (hop : ∀ k : Fin (lifetimeRuns attempts),
      |p k - p (k + 1)| ≤ e (slotTree ((slotOrder attempts).symm k))) :
    |p 0 - p (lifetimeRuns attempts)| ≤ ∑ slot : Slot attempts, e (slotTree slot) := by
  let err : ℕ → ℝ := fun k => if h : k < lifetimeRuns attempts then
    e (slotTree ((slotOrder attempts).symm ⟨k, h⟩)) else 0
  have hs := abs_sub_le_sum_of_hybrid p (lifetimeRuns attempts) err (fun k hk => by
    simpa [err, hk] using hop ⟨k, hk⟩)
  have hfin : ∑ k ∈ Finset.range (lifetimeRuns attempts), err k =
      ∑ k : Fin (lifetimeRuns attempts), e (slotTree ((slotOrder attempts).symm k)) := by
    rw [Finset.sum_fin_eq_sum_range]
  rw [hfin] at hs
  have hslots := Fintype.sum_equiv (slotOrder attempts)
    (fun slot => e (slotTree slot))
    (fun k => e (slotTree ((slotOrder attempts).symm k))) (fun slot => by simp)
  rw [← hslots] at hs
  exact hs


/-! ## The errors do not depend on `Th` -/

/-- The AND layer lengths and the output count of a circuit. -/
def shapeOf (c : Circuit) : List ℕ × ℕ := (c.layers.map List.length, c.outputs.length)

theorem depth_eq_of_shape {xs ys : List Circuit} (h : xs.map shapeOf = ys.map shapeOf) :
    depth xs = depth ys := by
  have hx : xs.map (·.layers.length) = (xs.map shapeOf).map (·.1.length) := by
    simp [shapeOf, Function.comp_def]
  have hy : ys.map (·.layers.length) = (ys.map shapeOf).map (·.1.length) := by
    simp [shapeOf, Function.comp_def]
  simp only [depth, hx, hy, h]

theorem getD_length (l : List (List (Affine × Affine))) (n : ℕ) :
    (l.getD n []).length = (l.map List.length).getD n 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[n]? <;> simp

theorem tupleCount_eq_of_shape {xs ys : List Circuit} (h : xs.map shapeOf = ys.map shapeOf) :
    tupleCount xs = tupleCount ys := by
  have hl : ∀ (zs : List Circuit) (layer : ℕ), zs.map (fun job => (job.layers.getD layer []).length) =
      (zs.map shapeOf).map (fun s => s.1.getD layer 0) := by
    intro zs layer
    simp only [List.map_map]
    apply List.map_congr_left
    intro job _
    simp only [Function.comp_apply, shapeOf, getD_length]
  have ho : ∀ zs : List Circuit, zs.map (·.outputs.length) = (zs.map shapeOf).map (·.2) := by
    intro zs
    simp [shapeOf, Function.comp_def]
  simp only [tupleCount, hl, ho, h, depth_eq_of_shape h]

section Shape

variable (circuitsOf : (HashInput → HashOutput) → Circuits)

theorem runCircuits_shape (hshape : FixedShape circuitsOf) (Th Th' : HashInput → HashOutput)
    (parameter : PublicParameter) (jobs : List Job) :
    (runCircuits (circuitsOf Th) parameter jobs).map shapeOf =
      (runCircuits (circuitsOf Th') parameter jobs).map shapeOf := by
  simp only [runCircuits, List.map_map]
  apply List.map_congr_left
  intro job _
  obtain ⟨h1, h2⟩ := hshape Th Th' parameter job.kind
  simp only [Function.comp_apply, shapeOf, h1, h2]

theorem maxBatch_congr (hshape : FixedShape circuitsOf) (Th Th' : HashInput → HashOutput)
    (settings : Settings) (g : List Circuit → ℕ)
    (hg : ∀ xs ys : List Circuit, xs.map shapeOf = ys.map shapeOf → g xs = g ys) :
    maxBatch (circuitsOf Th) settings g = maxBatch (circuitsOf Th') settings g := by
  simp only [maxBatch, hg _ _ (runCircuits_shape circuitsOf hshape Th Th' _ _)]

theorem maxBatch_shape (hshape : FixedShape circuitsOf) (Th Th' : HashInput → HashOutput)
    (settings : Settings) (f : ℕ → ℕ) :
    maxBatch (circuitsOf Th) settings (fun jobs => f (tupleCount jobs)) =
      maxBatch (circuitsOf Th') settings (fun jobs => f (tupleCount jobs)) :=
  maxBatch_congr circuitsOf hshape Th Th' settings _ fun _ _ h => by rw [tupleCount_eq_of_shape h]

theorem ceremonyFuel_shape (hshape : FixedShape circuitsOf) (Th Th' : HashInput → HashOutput)
    (settings : Settings) :
    ceremonyFuel (circuitsOf Th) settings = ceremonyFuel (circuitsOf Th') settings := by
  simp only [ceremonyFuel]
  rw [maxBatch_congr circuitsOf hshape Th Th' settings _ fun _ _ h => by
    simp only [runRounds, tupleCount_eq_of_shape h, depth_eq_of_shape h]]

theorem treeCheckError_shape [Field E] [Fintype E] (hshape : FixedShape circuitsOf)
    (Th Th' : HashInput → HashOutput) (settings : Settings) (tree : Tree) (q : ℕ) :
    treeCheckError (E := E) (circuitsOf Th) settings tree q =
      treeCheckError (E := E) (circuitsOf Th') settings tree q := by
  simp only [treeCheckError, maxBatch_shape circuitsOf hshape Th Th' settings coins,
    maxBatch_shape circuitsOf hshape Th Th' settings halvings]

theorem treeHashError_shape (hshape : FixedShape circuitsOf) (Th Th' : HashInput → HashOutput)
    (settings : Settings) (tree : Tree) (q : ℕ) :
    treeHashError (circuitsOf Th) settings C tree q = treeHashError (circuitsOf Th') settings C tree q := by
  simp only [treeHashError, treeSecrets, maxBatch_shape circuitsOf hshape Th Th' settings halvings]

end Shape


/-! ## The joint hop of one slot, averaged over `Th` -/

/-- A selector, a ceremony adversary and a distinguisher of the joint hop. -/
structure JointInstance (C : Committee) (E : Type) where
  pre : LifetimeBridge.Selector C
  A : Adversary C E (Keys C) PEmpty PEmpty
  Z : Distinguisher C A.State TreeOutput

section Joint

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (aes : Aes)
variable (circuitsOf : (HashInput → HashOutput) → Circuits) (D : C.Coalition)

/-- The real side of the joint hop, `reductionIdeal` of the joint game, with `Th` sampled as in
`lifetimeRunSampled`. -/
def jointReal (inst : Circuits → JointInstance C E) : ℝ :=
  (Pr[fun b => b = true | do
    let values ← $ᵗ (MpcDomain → HashOutput)
    let c := circuitsOf (thOf values)
    PRFScheme.prfIdealExp (prgReduction ⟨thOf values, aes⟩ D
      (LifetimeBridge.jointGame K c settings false D (inst c).pre (inst c).A (inst c).Z))]).toReal

/-- The ideal side of the joint hop, `accepts` of the joint game, with `Th` sampled as in
`lifetimeRunSampled`. -/
def jointIdeal (inst : Circuits → JointInstance C E) : ℝ :=
  (Pr[fun b => b = true | do
    let values ← $ᵗ (MpcDomain → HashOutput)
    let c := circuitsOf (thOf values)
    Prod.fst <$> runWorld ⟨thOf values, aes⟩
      (LifetimeBridge.jointGame K c settings true D (inst c).pre (inst c).A (inst c).Z)]).toReal

/-- The premises of `JointSimulationHopFrom` for every `Th`, with one fixed selected tree. -/
def JointValid (inst : Circuits → JointInstance C E) (tree : Tree) (q₀ q : ℕ) : Prop :=
  ∀ values : MpcDomain → HashOutput,
    (∀ p ∈ support (LifetimeBridge.jointPrefixRun ⟨thOf values, aes⟩
        (inst (circuitsOf (thOf values))).pre), p.1.2.2.1 = tree) ∧
      IsQueryBoundP (LifetimeBridge.jointPrefix (inst (circuitsOf (thOf values))).pre) Counted q₀ ∧
      IsQueryBounded (inst (circuitsOf (thOf values))).A (inst (circuitsOf (thOf values))).Z
        (ceremonyFuel (circuitsOf (thOf values)) settings) q

/-- The joint hop of the tree side, averaged over `Th`, pays the fixed tree error of the selected
tree at the circuits of the statement. -/
theorem joint_average_bound (inst : Circuits → JointInstance C E) (tree : Tree) (q₀ q : ℕ)
    (hjoint : ∀ values : MpcDomain → HashOutput, LifetimeBridge.JointSimulationHopFrom
      ⟨thOf values, aes⟩ K (circuitsOf (thOf values)) settings (keySplit C))
    (hshape : FixedShape circuitsOf) (hb : 0 < settings.batchSize)
    (hvalid : JointValid settings aes circuitsOf inst tree q₀ q) :
    |jointReal K settings aes circuitsOf D inst - jointIdeal K settings aes circuitsOf D inst| ≤
      treeCheckError (E := E) (circuitsOf fun _ => 0) settings tree (q₀ + q) +
        (treeHashError (circuitsOf fun _ => 0) settings C tree (q₀ + q) - keySplit C (q₀ + q)) := by
  set ε := treeCheckError (E := E) (circuitsOf fun _ => 0) settings tree (q₀ + q) +
    (treeHashError (circuitsOf fun _ => 0) settings C tree (q₀ + q) - keySplit C (q₀ + q))
  have hv : ∀ values : MpcDomain → HashOutput,
      |(Pr[fun b => b = true | PRFScheme.prfIdealExp (prgReduction ⟨thOf values, aes⟩ D
          (LifetimeBridge.jointGame K (circuitsOf (thOf values)) settings false D
            (inst (circuitsOf (thOf values))).pre (inst (circuitsOf (thOf values))).A
            (inst (circuitsOf (thOf values))).Z))]).toReal -
        (Pr[fun b => b = true | Prod.fst <$> runWorld ⟨thOf values, aes⟩
          (LifetimeBridge.jointGame K (circuitsOf (thOf values)) settings true D
            (inst (circuitsOf (thOf values))).pre (inst (circuitsOf (thOf values))).A
            (inst (circuitsOf (thOf values))).Z)]).toReal| ≤ ε := by
    intro values
    obtain ⟨htree, hpre, hadv⟩ := hvalid values
    have h := hjoint values hb D _ _ _ q₀ q hpre hadv
    rw [jointError_fixed_tree _ _ tree _ htree,
      treeCheckError_shape circuitsOf hshape _ (fun _ => 0),
      treeHashError_shape circuitsOf hshape _ (fun _ => 0)] at h
    simp only [reductionIdeal, accepts] at h
    simp only [probEvent_eq_eq_probOutput]
    convert h using 4
    rw [← probEvent_eq_eq_probOutput, probEvent_map]
    rfl
  have hs := abs_probEvent_bind_sub_le_sum ($ᵗ (MpcDomain → HashOutput)) _ _
    (fun b : Bool => b = true) (fun _ => ε) hv
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hv fun _ => 0)
  exact hs.trans (sum_probOutput_mul_const_le _ hε)

end Joint

/-! ## The runs of a slot world -/

/-- How a run uses its hidden streams. A `shared` run uses the shared table of the dealer world, an
`own` run its own table, and an `ideal` run is `F_tree` with the emulated `treeSimulator`. -/
inductive RunMode
  | shared
  | own
  | ideal
deriving DecidableEq

/-- The lifetime state, with the own stream table of the running run and, for an ideal run, the
output of `F_tree`. -/
abbrev SlotState (C : Committee) (E : Type) :=
  LifetimeState C E × Option (StreamCache C × Option (Option TreeOutput))

/-- The slot of a run that starts now, from the run counter of its tree. -/
def startSlot (attempts : ℕ) (st : LifetimeState C E) : Tree → Option (Slot attempts)
  | .top => if h : st.topRuns < attempts then some (.inl ⟨st.topRuns, h⟩) else none
  | .bottom b => if h : st.bottomRuns b < attempts then some (.inr (b, ⟨st.bottomRuns b, h⟩)) else none

/-- The run counters after a start, as in `lifetimeOraclesWith`. -/
def countStart (st : LifetimeState C E) : Tree → LifetimeState C E
  | .top => { st with topRuns := st.topRuns + 1 }
  | .bottom b => { st with bottomRuns := Function.update st.bottomRuns b (st.bottomRuns b + 1) }

/-- `LifetimeState.settle` for an ideal run. An emulated operator that ends with an output is a
receiver of `F_tree` and keeps `output`. -/
def settleIdeal (D : C.Coalition) (output : Option TreeOutput) (st : LifetimeState C E) :
    LifetimeState C E :=
  match st.running with
  | some (tree, fuel, steps) =>
      let out := fun i => if ((steps i).output).isSome then output else none
      if fuel = 0 ∨ ∀ i, i ∉ D.1 → (steps i).isDone then
        match tree with
        | .top => { st with running := none, top := fun i => (st.top i).or (TreeOutput.topTree (out i)) }
        | .bottom b =>
            let bottom := fun i => Function.update (st.bottom i) b ((st.bottom i b).or
              (match out i with | some (.bottom tree) => some tree | _ => none))
            { st with running := none, bottom := bottom }
      else st
  | none => st

/-- The seeds of `treeSimulator`: the seed of a term that a corrupt operator holds, and zero for a
hidden term. Every term has an honest holder, which holds the same dealt seed. -/
def simSeeds (D : C.Coalition) (keys : C.Party → Keys C) : C.Term → HashOutput := fun T =>
  if KnownTo D.1 T then honestSeeds D keys T else 0

section Gadgets

variable [Field E] [Algebra Bit E] (K : Constants C E) (settings : Settings)

/-- The gadgets of `treeSimulator`. `clear` evaluates the jobs of a batch in the clear on the seeds
of the simulator, and the opening shifts the lacked term to the output of `F_tree`. -/
def simGadgets (D : C.Coalition) (openings : List (List (List Bit)))
    (clear : List Job → PartyM C E RealSpec (List (List Bit))) :
    Context C → ℕ → List Job → RunGadgets C E RealSpec := fun ctx k jobs =>
  { realRunGadgets K ctx settings.mode with
    output := fun v count => do
      let clear ← StateT.lift (clear jobs)
      let shift := fun g => ((openings.getD k []).flatten.getD g 0) + (clear.flatten.getD g 0)
      StateT.lift (openRep K ctx (fun T g => if lackedTerm D.1 = some T then v T g + shift g else v T g)
        count) }

end Gadgets

/-- Where a slot world runs its parts. `shared` runs the honest operators of a shared run, `own`
those of a run with its own table, `dealer` computes `F_tree` and `clear` evaluates the jobs of a
batch of the simulator in the clear. -/
structure SlotEnv (C : Committee) (E : Type) (m : Type → Type) where
  base : Roles C m
  shared : Roles C m
  own : Roles C (StateT (StreamCache C) m)
  dealer : PublicParameter → (C.Term → HashOutput) → TopTree → Tree →
    m (Option TreeOutput × List (List (List Bit)))
  clear : PublicParameter → (C.Term → HashOutput) → Tree → List Job →
    PartyM C E RealSpec (List (List Bit))

section Oracles

variable [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)
variable (attempts : ℕ) {m : Type → Type} [Monad m]

/-- The lifetime oracles with the run of each slot in its mode. Every other query goes to
`lifetimeOraclesWith`, whose runs use `env.shared`. -/
def slotOracles (env : SlotEnv C E m) (mode : Slot attempts → RunMode) (D : C.Coalition)
    (keys : C.Party → Keys C) (value : Point → m Digest) (h : C.Party) :
    QueryImpl (LifetimeSpec C E) (StateT (SlotState C E) m) := fun q =>
  let life := lifetimeOraclesWith K circuits settings attempts (fun _ => env.shared) env.base D keys
    value h
  let plain := fun (q : LifetimeQuery C E) =>
    (StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$> (life q).run s.1 :
      StateT (SlotState C E) m ((LifetimeSpec C E).Range q))
  match q with
  | .start tree => StateT.mk fun s =>
      if LifetimeProof.canStart attempts D s.1 tree then
        match (startSlot attempts s.1 tree).map mode with
        | some .own => do
            let (steps, own) ← (startSteps env.own D fun i =>
              (ceremony K circuits settings i (keys i) ((s.1.top i).getD emptyTop) tree :
                PartyM C E RealSpec TreeOutput)).run ∅
            let st := LifetimeState.settle D
              { countStart s.1 tree with running := some (tree, ceremonyFuel circuits settings, steps) }
            pure (some (toCoalition D steps), (st, some (own, none)))
        | some .ideal => do
            let parameter := (keys h).parameter
            let top := (s.1.top h).getD emptyTop
            let (output, openings) ← env.dealer parameter (honestSeeds D keys) top tree
            let seeds := simSeeds D keys
            let (steps, own) ← (startSteps env.own D fun i =>
              (ceremonyWith K circuits settings
                (simGadgets K settings D openings (env.clear parameter seeds tree)) i
                ⟨parameter, seeds, fun _ => 0⟩ top tree : PartyM C E RealSpec TreeOutput)).run ∅
            let st := settleIdeal D output
              { countStart s.1 tree with running := some (tree, ceremonyFuel circuits settings, steps) }
            pure (some (toCoalition D steps), (st, some (own, some output)))
        | _ => (fun r => (r.1, (r.2, none))) <$> (life (.start tree)).run s.1
      else (plain (.start tree)).run s
  | .round sent => StateT.mk fun s =>
      match s.1.running, s.2 with
      | some (tree, fuel, steps), some (own, kind) => do
          let ((_, steps, _), own) ← (stepRound env.own D (roundAdversary (I := PEmpty) sent)
            noFunctionality () steps).run own
          let st := { s.1 with running := some (tree, fuel - 1, steps) }
          let st := match kind with
            | none => LifetimeState.settle D st
            | some output => settleIdeal D output st
          pure (some (toCoalition D steps), (st, some (own, kind)))
      | _, _ => (plain (.round sent)).run s
  | q => plain q

/-- The lifetime after keygen, as `LifetimeHybridOrder.afterKeygen`, with the slot oracles. -/
def slotRun (env : SlotEnv C E m) (mode : Slot attempts → RunMode) (D : C.Coalition)
    (A : LifetimeAdversary C E) (state : A.keygen.State) (outputs : C.Party → Option (Keys C)) :
    m Bool := do
  let some h := C.parties.find? (· ∉ D.1) | pure false
  if ¬ ∀ i, i ∉ D.1 → (outputs i).isSome then pure false else do
  let keys := fun i => (outputs i).getD default
  let lift : ∀ {β : Type}, OracleComp (RoSpec C) β → m β := fun oa => env.base.honest (liftComp oa _)
  let value := fun x => lift (prfValue (honestSeeds D keys) x)
  let forger : QueryImpl (LocalSpec C) (StateT (SlotState C E) m) :=
    fun t => StateT.lift (env.base.adversary (OracleComp.lift (OracleSpec.query t)))
  let (forgery, s) ← (simulateQ
    (forger + slotOracles K circuits settings attempts env mode D keys value h)
      (A.run state (keys h).parameter)).run
    (⟨⟨D.1, fun _ => none, [], fun _ => none⟩, fun _ => none, fun _ _ => none, 0, fun _ => 0, ∅, none⟩,
      none)
  let st := s.1
  if ¬ ∀ i, i ∉ D.1 → (st.top i).isSome then pure false else do
  let some (_, top) := st.publicKey (keys h).parameter h | pure false
  forgeryWins lift (dealtWith lift (keys h).parameter keys top value) st.sign forgery

end Oracles

/-! ## The slot worlds -/

/-- The roles of a run with its own stream table, inside the emulation monad. -/
def ownRoles (D : C.Coalition) : Roles C (StateT (StreamCache C) (EmulationM C)) where
  adversary oa := StateT.lift ((emulatedRoles D).adversary oa)
  honest oa := StateT.mk fun table => StateT.lift (((emulatedRoles D).honest oa).run table)

/-- The parts of the dealer-keygen world. The keygen, the signing and `F_tree` run on the free copy,
and the shared runs use the shared table of `emulatedRoles`. -/
def worldEnv (D : C.Coalition) (circuits : Circuits) (settings : Settings) :
    SlotEnv C E (EmulationM C) where
  base := lifetimeHybridRoles D 0 0
  shared := emulatedRoles D
  own := ownRoles D
  dealer parameter seeds top tree := (lifetimeHybridRoles D 0 0).honest
    (liftComp (dealerCeremony circuits settings parameter seeds top tree) _)
  clear parameter seeds _ jobs := oracleStep (jobs.mapM (evalJob circuits parameter seeds))

/-- The modes of `S_k` (`sep = false`) and `T_k` (`sep = true`). -/
def worldMode (attempts k : ℕ) (sep : Bool) : Slot attempts → RunMode := fun slot =>
  if ((slotOrder attempts) slot).val < k then .ideal
  else if sep ∧ ((slotOrder attempts) slot).val = k then .own else .shared

/-- A run of slot `σ` is a run of the tree of `σ`. -/
theorem startSlot_tree (attempts : ℕ) (st : LifetimeState C E) (tree : Tree) (σ : Slot attempts)
    (h : startSlot attempts st tree = some σ) : slotTree σ = tree := by
  cases tree with
  | top =>
    simp only [startSlot] at h
    split_ifs at h
    cases h
    rfl
  | bottom b =>
    simp only [startSlot] at h
    split_ifs at h
    cases h
    rfl

/-- When a bottom slot is ideal, every top slot is ideal. -/
theorem worldMode_top_of_bottom (attempts k : ℕ) (sep : Bool) (x : Fin (2 ^ layerHeight) × Fin attempts)
    (hx : worldMode attempts k sep (.inr x) = .ideal) (t : Fin attempts) :
    worldMode attempts k sep (.inl t) = .ideal := by
  have hb : ((slotOrder attempts) (.inr x)).val < k := by
    by_contra hlt
    simp only [worldMode, if_neg hlt] at hx
    split_ifs at hx
  have hle := slotOrder_bottom attempts x
  have ht := slotOrder_top attempts t
  simp only [worldMode]
  rw [if_pos (by omega)]

section Worlds

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The slot world `S_k` (`sep = false`) or `T_k` (`sep = true`). `S_0` is the dealer-keygen world. -/
def slotGame (k : ℕ) (sep : Bool) (circuits : Circuits) : OracleComp (WorldSpec C) Bool :=
  if k = 0 ∧ sep = false then dealerKeygenGame K settings attempts D A circuits else
  emulationGame (do
    let (state, outputs) ← StateT.lift (liftM
      (idealExecution (fun p => p) D Fkeygen (keygenSimulator D A.keygen) (fun _ => ()) []))
    slotRun K circuits settings attempts (worldEnv D circuits settings)
      (worldMode attempts k sep) D A state outputs)

def slotProbability (k : ℕ) (sep : Bool) : ℝ :=
  (Pr[fun r => r.1 = true | lifetimeRunSampled aes fun Th =>
    slotGame K settings attempts D A k sep (circuitsOf Th)]).toReal

theorem slotProbability_zero :
    slotProbability K settings attempts aes circuitsOf D A 0 false =
      dealerKeygenProbability K settings attempts aes circuitsOf D A := by
  simp [slotProbability, slotGame, dealerKeygenProbability]

end Worlds

section Emulator

variable [Field E] [Algebra Bit E]

/-! ## The joint instance of one slot

The selector computes `F_tree` and the PRF values on the seeds of the simulator for every tree,
records its oracle answers with `LifetimeTranscriptReplay.record`, and passes the dealing and the
record in the auxiliary input. The ceremony adversary replays the record without a query, emulates
the keygen with a private table for the programmed points (`compileWorld`), and runs the lifetime
up to the start of the selected slot. Each round of the joint ceremony resumes the lifetime
adversary up to its next round query. The distinguisher records the outputs of the ceremony,
answers the pending query, and runs the rest of the lifetime and its win test. The emulated
signing uses the dealt keys. The other shared runs use one private stream table, and each ideal run
its own table. -/

instance : Countable (Keys C) :=
  Function.Injective.countable (f := fun k : Keys C => (k.parameter, k.seed, k.pairKey))
    (fun x y h => by cases x; cases y; simp_all)

/-- The PRF values of the job points of a tree, on the seeds of the simulator. -/
def treePoints : Tree → List Point
  | .top => topJobs.flatMap (·.points)
  | .bottom b => (bottomJobs b ++ signJobs b fun _ => digit 0).flatMap (·.points)

/-- The output and the openings of `F_tree`, and the PRF values of `treePoints`. -/
abbrev TreeTables := (Option TreeOutput × List (List (List Bit))) × List (Point × Digest)

def tableValue (values : List (Point × Digest)) (x : Point) : Digest := (values.lookup x).getD 0

/-- `evalJob` with the PRF values `F`. -/
def evalJobWith (circuits : Circuits) (parameter : PublicParameter) (F : Point → Digest) (job : Job) :
    List Bit :=
  (circuits parameter job.kind).eval ((job.points.map F).flatMap bitsOfDigest)

def treeTables (circuits : Circuits) (settings : Settings) (parameter : PublicParameter)
    (seeds sim : C.Term → HashOutput) (top : TopTree) (tree : Tree) :
    OracleComp (RoSpec C) TreeTables := do
  let dealt ← dealerCeremony circuits settings parameter seeds top tree
  let values ← (treePoints tree).mapM fun x => (fun v => (x, v)) <$> prfValue sim x
  pure (dealt, values)

/-- The tables of all trees. The bottom trees use the top tree that `F_tree` gives. -/
def precompute (circuits : Circuits) (settings : Settings) (D : C.Coalition)
    (dealing : LifetimeBridge.Dealing C) : OracleComp (LocalSpec C) (Tree → TreeTables) :=
  liftComp (do
    let seeds := honestSeeds D dealing.2.2
    let sim := simSeeds D dealing.2.2
    let top ← treeTables circuits settings dealing.1 seeds sim emptyTop .top
    let topTree := (TreeOutput.topTree top.1.1).getD emptyTop
    let bottoms ← (List.finRange (2 ^ layerHeight)).mapM fun b =>
      treeTables circuits settings dealing.1 seeds sim topTree (.bottom b)
    pure fun
      | .top => top
      | .bottom b => bottoms.getD b.val default : OracleComp (RoSpec C) (Tree → TreeTables)) _

/-- The emulation monad, with the private table of the programmed keygen points and the private
table of the shared runs. -/
abbrev EmuM (C : Committee) := StateT (HashCache C × StreamCache C) (OracleComp (LocalSpec C))

def onTable {α : Type} (m : StateT (HashCache C) (OracleComp (LocalSpec C)) α) : EmuM C α :=
  StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$> m.run s.1

def plainImpl : QueryImpl (LocalSpec C) (EmuM C) := fun t => onTable (compileLocal t)

def sharedImpl (D : C.Coalition) : QueryImpl (LocalSpec C) (EmuM C) := fun t =>
  match t with
  | .inr (.inr x) => if Hidden D x.1 then
      StateT.mk fun s => (fun r => (r.1, (s.1, r.2))) <$>
        liftComp (((PrgInput C →ₒ Bit).randomOracle x).run s.2) (LocalSpec C)
    else plainImpl (.inr (.inr x))
  | t => plainImpl t

def ownImpl (D : C.Coalition) : QueryImpl (LocalSpec C) (StateT (StreamCache C) (EmuM C)) := fun t =>
  match t with
  | .inr (.inr x) => if Hidden D x.1 then
      StateT.mk fun own => StateT.lift (liftComp (((PrgInput C →ₒ Bit).randomOracle x).run own) (LocalSpec C))
    else StateT.lift (plainImpl (.inr (.inr x)))
  | t => StateT.lift (plainImpl t)

/-- The parts of the emulation. `F_tree` and the clear evaluation of the simulator read the tables
of the selector. -/
def emuEnv (circuits : Circuits) (D : C.Coalition) (tables : Tree → TreeTables) : SlotEnv C E (EmuM C) where
  base := ⟨fun oa => simulateQ plainImpl oa, fun oa => simulateQ plainImpl oa⟩
  shared := ⟨fun oa => simulateQ plainImpl oa, fun oa => simulateQ (sharedImpl D) oa⟩
  own := ⟨fun oa => StateT.lift (simulateQ plainImpl oa), fun oa => simulateQ (ownImpl D) oa⟩
  dealer _ _ _ tree := pure (tables tree).1
  clear parameter _ tree jobs := pure (jobs.map (evalJobWith circuits parameter (tableValue (tables tree).2)))

/-- `F_keygen` on a given dealing. -/
def dealtKeygen (dealing : LifetimeBridge.Dealing C) :
    Functionality C Unit (Keys C) (PublicParameter × (C.Party → Option (Keys C))) (Finset C.Party) where
  run coalition _ := do
    let receivers ← leak (C := C) (dealing.1, fun i => if i ∈ coalition.1 then some (dealing.2.2 i) else none)
    pure fun i => if i ∉ coalition.1 ∧ i ∈ receivers then some (dealing.2.2 i) else none

abbrev Messages (C : Committee) (E : Type) := C.Party → C.Party → Option (Msg E)

abbrev LifetimeProgram (C : Committee) (E : Type) := OracleComp (LocalSpec C + LifetimeSpec C E) Forgery

/-- The lifetime adversary, done or waiting for the answer to a ceremony query. -/
inductive Pause (C : Committee) (E : Type) where
  | done (forgery : Forgery)
  | wait (sent : Option (Messages C E)) (k : Option (Messages C E) → LifetimeProgram C E)

/-- Run the lifetime adversary with `impl` until it ends or it makes a ceremony query that `stop`
selects. -/
def runUntil {σ : Type} {m : Type → Type} [Monad m]
    (impl : QueryImpl (LocalSpec C + LifetimeSpec C E) (StateT σ m))
    (stop : σ → LifetimeQuery C E → Bool) : LifetimeProgram C E → StateT σ m (Pause C E)
  | .pure f => pure (.done f)
  | .queryBind (.inr (.start tree)) k => do
      if stop (← get) (.start tree) then pure (.wait none k) else
        let a ← impl (.inr (.start tree))
        runUntil impl stop (k a)
  | .queryBind (.inr (.round sent)) k => do
      if stop (← get) (.round sent) then pure (.wait (some sent) k) else
        let a ← impl (.inr (.round sent))
        runUntil impl stop (k a)
  | .queryBind t k => do
      let a ← impl t
      runUntil impl stop (k a)

end Emulator


section Instance

variable [Field E] [Algebra Bit E] (K : Constants C E) (settings : Settings) (attempts : ℕ)

/-- The state of the emulation between the steps of the joint ceremony. -/
structure EmuState (C : Committee) (E : Type) where
  tables : HashCache C × StreamCache C
  slot : SlotState C E
  selected : Bool
  pause : Pause C E
  keys : C.Party → Keys C
  h : C.Party
  pre : Tree → TreeTables

/-- The start state of the lifetime oracles, as in `lifetimeGameWith`. -/
def initSlotState (D : C.Coalition) : SlotState C E :=
  (⟨⟨D.1, fun _ => none, [], fun _ => none⟩, fun _ => none, fun _ _ => none, 0, fun _ => 0, ∅, none⟩,
    none)

/-- The lifetime oracles of the emulation for the hop at position `k`, with the flag of the
selected run. -/
def emuImpl (circuits : Circuits) (k : ℕ) (D : C.Coalition) (pre : Tree → TreeTables)
    (keys : C.Party → Keys C) (h : C.Party) :
    QueryImpl (LocalSpec C + LifetimeSpec C E) (StateT (SlotState C E × Bool) (EmuM C)) :=
  let env := emuEnv (E := E) circuits D pre
  let lift : ∀ {β : Type}, OracleComp (RoSpec C) β → EmuM C β := fun oa => env.base.honest (liftComp oa _)
  let value := fun x => lift (prfValue (honestSeeds D keys) x)
  let impl : QueryImpl (LocalSpec C + LifetimeSpec C E) (StateT (SlotState C E) (EmuM C)) :=
    (fun t => StateT.lift (env.base.adversary (OracleComp.lift (OracleSpec.query t)))) +
      slotOracles K circuits settings attempts env (worldMode attempts k false) D keys value h
  fun t => StateT.mk fun s => (fun r => (r.1, (r.2, s.2))) <$> (impl t).run s.1

/-- Stop at the admitted start of the selected slot, and at each round query while it runs. -/
def stopAt (D : C.Coalition) (σ : Slot attempts) : SlotState C E × Bool → LifetimeQuery C E → Bool
  | s, .start tree => decide (LifetimeProof.canStart attempts D s.1.1 tree ∧
      startSlot attempts s.1.1 tree = some σ)
  | s, .round _ => s.2
  | _, _ => false

/-- The selected run starts: its counter moves and it runs in the joint ceremony. -/
def startSelected (circuits : Circuits) (tree : Tree) (s : SlotState C E × Bool) : SlotState C E × Bool :=
  let st : LifetimeState C E := { countStart s.1.1 tree with
    running := some (tree, ceremonyFuel circuits settings, fun _ => .done none) }
  ((st, none), true)

/-- The running selected run ends with the outputs of the joint ceremony, as `LifetimeState.settle`
records them. -/
def settleOutputs (st : LifetimeState C E) (outputs : C.Party → Option TreeOutput) : LifetimeState C E :=
  match st.running with
  | some (tree, _, _) =>
      match tree with
      | .top => { st with running := none, top := fun i => (st.top i).or (TreeOutput.topTree (outputs i)) }
      | .bottom b =>
          let bottom := fun i => Function.update (st.bottom i) b ((st.bottom i b).or
            (match outputs i with | some (.bottom tree) => some tree | _ => none))
          { st with running := none, bottom := bottom }
  | none => st

/-- The win test of the lifetime, as in `lifetimeGameWith`. -/
def emuFinish (D : C.Coalition) (keys : C.Party → Keys C) (h : C.Party) (st : LifetimeState C E)
    (forgery : Forgery) : EmuM C Bool := do
  let lift : ∀ {β : Type}, OracleComp (RoSpec C) β → EmuM C β :=
    fun oa => simulateQ plainImpl (liftComp oa (LocalSpec C))
  let value := fun x => lift (prfValue (honestSeeds D keys) x)
  if ¬ ∀ i, i ∉ D.1 → (st.top i).isSome then pure false else do
  let some (_, top) := st.publicKey (keys h).parameter h | pure false
  forgeryWins lift (dealtWith lift (keys h).parameter keys top value) st.sign forgery

/-- The ceremony adversary of the hop at position `k`, with the selected slot `σ`. -/
def rawAdversary (circuits : Circuits) (D : C.Coalition) (A : LifetimeAdversary C E) (k : ℕ)
    (σ : Slot attempts) : Adversary C E (Keys C) PEmpty PEmpty where
  State := Option (EmuState C E)
  start _ z := match decodeAux (α := LifetimeBridge.Dealing C × Aux) z with
    | none => pure none
    | some (dealing, record) =>
      let pre := (LifetimeTranscriptReplay.replay (precompute circuits settings D dealing) record).getD
        fun _ => default
      let prog : EmuM C (Option (EmuState C E)) := do
        let (state, outputs) ← onTable (simulateQ compileWorld (idealExecution (fun p => p) D
          (dealtKeygen dealing) (keygenSimulator D A.keygen) (fun _ => ()) []))
        let some h := C.parties.find? (· ∉ D.1) | pure none
        if ¬ ∀ i, i ∉ D.1 → (outputs i).isSome then pure none else do
        let keys := fun i => (outputs i).getD default
        let (pause, s) ← (runUntil (emuImpl K settings attempts circuits k D pre keys h)
          (stopAt attempts D σ) (A.run state (keys h).parameter)).run (initSlotState D, false)
        let s := match pause with
          | .wait none _ => startSelected settings circuits (slotTree σ) s
          | _ => s
        pure (some ⟨(∅, ∅), s.1, s.2, pause, keys, h, pre⟩)
      (fun r => r.1.map fun e => { e with tables := r.2 }) <$> prog.run (∅, ∅)
  round state msgs := match state with
    | none => pure (none, fun _ _ => none)
    | some e => match e.pause with
      | .done _ => pure (some e, fun _ _ => none)
      | .wait _ resume => do
        let ((pause, s), tables) ← ((runUntil (emuImpl K settings attempts circuits k D e.pre e.keys e.h)
          (stopAt attempts D σ) (resume (some msgs))).run (e.slot, e.selected)).run e.tables
        let sent := match pause with
          | .wait (some sent) _ => sent
          | _ => fun _ _ => none
        pure (some { e with tables := tables, slot := s.1, selected := s.2, pause := pause }, sent)
  answer _ l := l.elim

/-- The distinguisher of the hop at position `k`. -/
def rawDistinguisher (circuits : Circuits) (D : C.Coalition) (k : ℕ) :
    Distinguisher C (Option (EmuState C E)) TreeOutput := fun r =>
  match r.1 with
  | none => pure false
  | some e =>
    let prog : EmuM C Bool := match e.pause with
      | .done forgery => emuFinish D e.keys e.h e.slot.1 forgery
      | .wait _ resume => do
          let s := ((settleOutputs e.slot.1 r.2, e.slot.2), false)
          let (forgery, s) ← (simulateQ (emuImpl K settings attempts circuits k D e.pre e.keys e.h)
            (resume (some fun _ _ => none))).run s
          emuFinish D e.keys e.h s.1.1 forgery
    prog.run' e.tables

/-- The joint instance of the hop at position `k`. The selector runs within `q₀`, and the start, each
round and the distinguisher within `Q` each. -/
def slotInstance (D : C.Coalition) (A : LifetimeAdversary C E) (Q : ℕ)
    (k : Fin (lifetimeRuns attempts)) (circuits : Circuits) : JointInstance C E where
  pre dealing := do
    let (top, z) ← cap (Q + lifetimeOverhead C attempts Q) (do
      let (tables, record) ← LifetimeTranscriptReplay.record (precompute circuits settings D dealing)
      pure ((TreeOutput.topTree (tables .top).1.1).getD emptyTop, encodeAux (dealing, record)))
    pure (top, slotTree ((slotOrder attempts).symm k), z)
  A := capAdversary Q (rawAdversary K settings attempts circuits D A k ((slotOrder attempts).symm k))
  Z r := cap Q (rawDistinguisher K settings attempts circuits D k
    (show Option (EmuState C E) × (C.Party → Option TreeOutput) from r))

end Instance


/-! ## The slot contracts and the assembly -/

theorem liftComp_counted {α : Type} (p : ProbComp α) :
    IsQueryBoundP (liftComp p (LocalSpec C)) Counted 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, liftComp_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (.inl t)) >>= fun u =>
      liftComp (k u) (LocalSpec C)) Counted 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [Counted]), fun u => by simpa [Counted] using ih u⟩

section Contracts

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The joint instance of each position meets the premises of the joint hop: it selects the tree of
its slot, its selector stays within `q₀`, and its adversary and distinguisher within
`(fuel + 2) Q`. -/
def SlotSuspension (Q : ℕ) : Prop :=
  ∀ k : Fin (lifetimeRuns attempts),
    JointValid settings aes circuitsOf (slotInstance K settings attempts D A Q k)
      (slotTree ((slotOrder attempts).symm k)) (Q + lifetimeOverhead C attempts Q)
      ((ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q)

/-- The move of slot `k` from the shared stream table of the dealer world to its own table. -/
def SlotTransport (Q : ℕ) : Prop :=
  let q₀ := Q + lifetimeOverhead C attempts Q
  let q := (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q
  q₀ + q < 2 ^ 128 → ∀ k : Fin (lifetimeRuns attempts),
    |slotProbability K settings attempts aes circuitsOf D A k false -
      slotProbability K settings attempts aes circuitsOf D A k true| ≤ streamKeyError C

/-- The emulation of the lifetime around slot `k` by the joint instance: `T_k` against the real
side and the ideal side against `S_{k+1}`. -/
def SlotEmulationHit (Q : ℕ) : Prop :=
  let q₀ := Q + lifetimeOverhead C attempts Q
  let q := (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q
  q₀ + q < 2 ^ 128 → ∀ k : Fin (lifetimeRuns attempts),
    |slotProbability K settings attempts aes circuitsOf D A k true -
        jointReal K settings aes circuitsOf D (slotInstance K settings attempts D A Q k)| +
      |jointIdeal K settings aes circuitsOf D (slotInstance K settings attempts D A Q k) -
        slotProbability K settings attempts aes circuitsOf D A ((k : ℕ) + 1) false| ≤
      seedHitError C (q₀ + q)

/-- The world with every slot ideal against the signing bound at `q₀` and the failed searches. -/
def LifetimeForger (Q : ℕ) : Prop :=
  let q₀ := Q + lifetimeOverhead C attempts Q
  slotProbability K settings attempts aes circuitsOf D A (lifetimeRuns attempts) false ≤
    2 ^ layerHeight * searchFailure + signingHashError q₀ + seedHitError C q₀ + seedCollisionError C

theorem slotSuspension (Q : ℕ) (hshape : FixedShape circuitsOf) :
    SlotSuspension K settings attempts aes circuitsOf D A Q := by
  intro k values
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    have h1 : p.1 ∈ support (LifetimeBridge.jointPrefix
        (slotInstance K settings attempts D A Q k (circuitsOf (thOf values))).pre) := by
      apply support_simulateQ_run'_subset (localAnswer ⟨thOf values, aes⟩) _ ∅
      rw [StateT.run'_eq, support_map]
      exact ⟨p, hp, rfl⟩
    simp only [LifetimeBridge.jointPrefix, slotInstance, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at h1
    obtain ⟨keys, _, chosen, ⟨x, _, hx⟩, hp1⟩ := h1
    rw [hp1, hx]
  · unfold LifetimeBridge.jointPrefix slotInstance
    refine (isQueryBoundP_bind (liftComp_counted (C := C) (prawnsKeyGen (C := C)))
      (m := Q + lifetimeOverhead C attempts Q) fun keys _ => ?_).mono (by omega)
    refine (isQueryBoundP_bind (n := Q + lifetimeOverhead C attempts Q) (m := 0) ?_
      fun _ _ => isQueryBoundP_pure _ _ _).mono (by omega)
    refine (isQueryBoundP_bind (m := 0) (cap_bound _ _) fun x _ => ?_).mono (by omega)
    rcases x with ⟨top, z⟩
    exact isQueryBoundP_pure _ _ _
  · rw [← ceremonyFuel_shape circuitsOf hshape (thOf values) (fun _ => 0)]
    exact capAdversary_queryBound Q _ _ _

/-- The error of one slot in `LifetimeAfterKeygen`. -/
def slotError (q₀ q : ℕ) (tree : Tree) : ℝ :=
  treeCheckError (E := E) (circuitsOf fun _ => 0) settings tree (q₀ + q) +
    (treeHashError (circuitsOf fun _ => 0) settings C tree (q₀ + q) - keySplit C (q₀ + q)) +
    streamKeyError C + seedHitError C (q₀ + q)

theorem slotProbability_mem (k : ℕ) (sep : Bool) :
    0 ≤ slotProbability K settings attempts aes circuitsOf D A k sep ∧
      slotProbability K settings attempts aes circuitsOf D A k sep ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, by
    unfold slotProbability
    exact LifetimeAllowance.toReal_le_one probEvent_le_one⟩

/-- One slot hop. If `2 ^ 128 ≤ q₀ + q`, the hop is at most `1`, and the hash allowance alone pays
it. Otherwise the transport, the emulation and the joint hop pay it. -/
theorem slot_hop (Q : ℕ)
    (hjoint : ∀ values : MpcDomain → HashOutput, LifetimeBridge.JointSimulationHopFrom
      ⟨thOf values, aes⟩ K (circuitsOf (thOf values)) settings (keySplit C))
    (hshape : FixedShape circuitsOf) (hb : 0 < settings.batchSize)
    (htrans : SlotTransport K settings attempts aes circuitsOf D A Q)
    (hemu : SlotEmulationHit K settings attempts aes circuitsOf D A Q)
    (k : Fin (lifetimeRuns attempts)) :
    |slotProbability K settings attempts aes circuitsOf D A k false -
      slotProbability K settings attempts aes circuitsOf D A ((k : ℕ) + 1) false| ≤
      slotError (C := C) (E := E) settings circuitsOf (Q + lifetimeOverhead C attempts Q)
        ((ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q)
        (slotTree ((slotOrder attempts).symm k)) := by
  set q₀ := Q + lifetimeOverhead C attempts Q
  set q := (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q
  letI : Inhabited E := ⟨0⟩
  letI : SampleableType E := SampleableType.ofFintype E
  have hstream : 0 ≤ streamKeyError C := by unfold streamKeyError; positivity
  have hseed : 0 ≤ seedHitError C (q₀ + q) := by
    unfold seedHitError
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num)
  by_cases small : q₀ + q < 2 ^ 128
  · have hj := joint_average_bound K settings aes circuitsOf D
      (slotInstance K settings attempts D A Q k) (slotTree ((slotOrder attempts).symm k)) q₀ q
      hjoint hshape hb (slotSuspension K settings attempts aes circuitsOf D A Q hshape k)
    have ht := htrans small k
    have he := hemu small k
    have h1 := abs_sub_le (slotProbability K settings attempts aes circuitsOf D A k false)
      (slotProbability K settings attempts aes circuitsOf D A k true)
      (slotProbability K settings attempts aes circuitsOf D A ((k : ℕ) + 1) false)
    have h2 := abs_sub_le (slotProbability K settings attempts aes circuitsOf D A k true)
      (jointReal K settings aes circuitsOf D (slotInstance K settings attempts D A Q k))
      (slotProbability K settings attempts aes circuitsOf D A ((k : ℕ) + 1) false)
    have h3 := abs_sub_le (jointReal K settings aes circuitsOf D (slotInstance K settings attempts D A Q k))
      (jointIdeal K settings aes circuitsOf D (slotInstance K settings attempts D A Q k))
      (slotProbability K settings attempts aes circuitsOf D A ((k : ℕ) + 1) false)
    unfold slotError
    linarith
  · have hl := slotProbability_mem K settings attempts aes circuitsOf D A k false
    have hr := slotProbability_mem K settings attempts aes circuitsOf D A ((k : ℕ) + 1) false
    have hunit : |slotProbability K settings attempts aes circuitsOf D A k false -
        slotProbability K settings attempts aes circuitsOf D A ((k : ℕ) + 1) false| ≤ 1 :=
      abs_sub_le_iff.2 ⟨by linarith [hl.2, hr.1], by linarith [hl.1, hr.2]⟩
    have hhash := treeSim_largeHashBudget (C := C) (circuitsOf fun _ => 0) settings
      (slotTree ((slotOrder attempts).symm k)) (q₀ + q) (Nat.le_of_not_gt small)
    have hcheck : 0 ≤ treeCheckError (E := E) (circuitsOf fun _ => 0) settings
        (slotTree ((slotOrder attempts).symm k)) (q₀ + q) := by
      unfold treeCheckError
      exact mul_nonneg (Nat.cast_nonneg _) (checkErrorOf_nonneg K _ _ _)
    unfold slotError
    linarith

/-- `LifetimeAllowance.LifetimeAfterKeygen` from the slot contracts and the joint hop. -/
theorem lifetimeAfterKeygen_of_slots (Q : ℕ)
    (hjoint : ∀ values : MpcDomain → HashOutput, LifetimeBridge.JointSimulationHopFrom
      ⟨thOf values, aes⟩ K (circuitsOf (thOf values)) settings (keySplit C))
    (hshape : FixedShape circuitsOf) (hb : 0 < settings.batchSize)
    (htrans : SlotTransport K settings attempts aes circuitsOf D A Q)
    (hemu : SlotEmulationHit K settings attempts aes circuitsOf D A Q)
    (hforger : LifetimeForger K settings attempts aes circuitsOf D A Q) :
    LifetimeAllowance.LifetimeAfterKeygen K settings attempts aes circuitsOf D A Q := by
  have hs := slotOrder_hybrid_bound attempts
    (fun k => slotProbability K settings attempts aes circuitsOf D A k false)
    (slotError (C := C) (E := E) settings circuitsOf (Q + lifetimeOverhead C attempts Q)
      ((ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q))
    (slot_hop K settings attempts aes circuitsOf D A Q hjoint hshape hb htrans hemu)
  simp only [slotProbability_zero] at hs
  have hd := (le_abs_self _).trans hs
  simp only [slotError] at hd
  simp only [LifetimeAllowance.LifetimeAfterKeygen]
  simp only [LifetimeForger] at hforger
  linarith

/-- The original lifetime claim from the small-split PRF transport, the joint hop of the tree side
and the three slot contracts. The keygen hop is `lifetimeKeygenHop_of_hasLifetimeQueryBound`. -/
theorem lifetimeSecurity_of_slots
    (hsource : (∀ Th, CircuitsCompute (circuitsOf Th) Th) → FixedShape circuitsOf →
      0 < settings.batchSize → ∀ (D : C.Coalition) (A : LifetimeAdversary C E) (Q : ℕ),
        HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q →
        LifetimeAllowance.LifetimePrfTransportSmallSplit K settings attempts aes circuitsOf D A Q ∧
        (∀ values : MpcDomain → HashOutput, LifetimeBridge.JointSimulationHopFrom
          ⟨thOf values, aes⟩ K (circuitsOf (thOf values)) settings (keySplit C)) ∧
        SlotTransport K settings attempts aes circuitsOf D A Q ∧
        SlotEmulationHit K settings attempts aes circuitsOf D A Q ∧
        LifetimeForger K settings attempts aes circuitsOf D A Q) :
    LifetimeSecurityStatementSampled K settings attempts aes circuitsOf :=
  LifetimeAllowance.lifetimeSecurity_of_smallSplit K settings attempts aes circuitsOf
    fun hcompute hshape hbatch D A Q hQ =>
      let ⟨hp, hj, ht, he, hf⟩ := hsource hcompute hshape hbatch D A Q hQ
      ⟨hp, LifetimeKeygenHopFinal.lifetimeKeygenHop_of_hasLifetimeQueryBound
          K settings attempts aes circuitsOf D A Q hQ,
        lifetimeAfterKeygen_of_slots K settings attempts aes circuitsOf D A Q hj hshape hbatch ht he hf⟩

end Contracts

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.slotOrder_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slotOrder_top

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.slotOrder_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slotOrder_bottom

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.startSlot_tree' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms startSlot_tree

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.worldMode_top_of_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms worldMode_top_of_bottom

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.slotOrder_hybrid_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slotOrder_hybrid_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.ceremonyFuel_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyFuel_shape

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.treeCheckError_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeCheckError_shape

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.treeHashError_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeHashError_shape

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.joint_average_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms joint_average_bound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.slotProbability_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slotProbability_zero

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.liftComp_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftComp_counted

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.slotSuspension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slotSuspension

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.slot_hop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slot_hop

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.lifetimeAfterKeygen_of_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimeAfterKeygen_of_slots

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlots.lifetimeSecurity_of_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lifetimeSecurity_of_slots

end ThresholdLeanXmssSecurity.LifetimeSlots
