import ThresholdLeanXmssSecurity.Proof.LifetimeSlots
import ThresholdLeanXmssSecurity.Proof.LifetimePrfTransportProof
import ThresholdLeanXmssSecurity.Proof.LifetimeLegacy

/-!
# Transport of the fixed lifetime slot worlds

The all-shared interpreter equals the original dealer-keygen tail, including slot zero.
The evaluated request kernels retain the complete lifetime state, both caches and the
observation log. A fixed observer retains the selected private table after settlement and
records hidden-name key overlaps with the shared table through subsequent requests.

`StateRelation` identifies the shared cache with the union of the separated caches and
keeps suspended continuations, hash cache and observation log equal before an overlap.
`SchedulerKernelCoupling` is a one-request statement for the actual frozen handlers.
`SelectedKeyOverlapBound` uses the original circuit and all-answer lifetime-budget premises.
Their composition, finite union, averaging and small-budget arithmetic give the unchanged
`SlotTransport`, with one `streamKeyError` and no additional allowance.

The pinned and current leanVM sources have no threshold lifetime slot scheduler.
The proof uses VCV relational couplings and the existing lifetime evaluator and arithmetic.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
open scoped ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeSlotTransport

open LifetimeSlots LifetimeHybridOrder LifetimeJointLink
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type}

section Shared
variable [Field E] [Algebra Bit E]
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (env : SlotEnv C E m) (D : C.Coalition)
variable (keys : C.Party → Keys C) (value : Point → m Digest) (h : C.Party)

omit [LawfulMonad m] in
/-- With every slot shared, the auxiliary private-table field remains absent. -/
theorem slotOracles_shared (q : (LifetimeSpec C E).Domain) (st : LifetimeState C E) :
    (slotOracles K circuits settings attempts env (fun _ => .shared) D keys value h q).run
      (st, none) =
    (fun r => (r.1, (r.2, none))) <$>
      (lifetimeOraclesWith K circuits settings attempts (fun _ => env.shared) env.base D
        keys value h q).run st := by
  cases q with
  | sign q => rfl
  | publicKey => rfl
  | start tree =>
    simp only [slotOracles, StateT.run_mk]
    split
    · cases startSlot attempts st tree <;> rfl
    · rfl
  | round sent =>
    simp only [slotOracles, StateT.run_mk]
    cases st.running <;> rfl

end Shared

/-- An unused auxiliary state is preserved through a complete oracle computation. -/
theorem simulate_aux_none {ι σ τ α : Type} {spec : OracleSpec ι}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (plain : QueryImpl spec (StateT σ m))
    (extended : QueryImpl spec (StateT (σ × Option τ) m))
    (hext : ∀ t st, (extended t).run (st, none) =
      (fun r => (r.1, (r.2, none))) <$> (plain t).run st)
    (p : OracleComp spec α) (st : σ) :
    (simulateQ extended p).run (st, none) =
      (fun r => (r.1, (r.2, none))) <$> (simulateQ plain p).run st := by
  induction p using OracleComp.inductionOn generalizing st with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hext, bind_map_left,
      map_bind]
    apply bind_congr
    intro r
    exact ih r.1 r.2

section Zero
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The generic all-shared slot tail equals the original dealer-keygen continuation. -/
theorem slotRun_shared (state : A.keygen.State) (outputs : C.Party → Option (Keys C)) :
    slotRun K circuits settings attempts (worldEnv D circuits settings) (fun _ => .shared)
      D A state outputs = afterKeygen K settings attempts D A circuits state outputs := by
  unfold slotRun afterKeygen
  cases hh : C.parties.find? (· ∉ D.1) with
  | none => rfl
  | some h =>
    simp only
    split
    · rfl
    · rw [simulate_aux_none _ _ (fun t st => ?_)]
      · simp only [bind_map_left]
        rfl
      · rcases t with t | q
        · simp only [QueryImpl.add_apply_inl]
          change (StateT.lift _).run (st, none) = (fun r => (r.1, (r.2, none))) <$> (StateT.lift _).run st
          simp only [StateT.run_lift, bind_pure_comp, Functor.map_map]
          rfl
        · exact slotOracles_shared K circuits settings attempts _ D _ _ h q st

/-- The zero-slot mode is uniformly shared. -/
theorem worldMode_zero : worldMode attempts 0 false = fun _ => .shared := by
  funext slot
  simp [worldMode]

/-- One uniform interpreter for every slot world, including the special zero branch. -/
def genericSlotGame (k : ℕ) (sep : Bool) : OracleComp (WorldSpec C) Bool :=
  emulationGame (do
    let (state, outputs) ← StateT.lift (liftM
      (idealExecution (fun p => p) D Fkeygen (keygenSimulator D A.keygen) (fun _ => ()) []))
    slotRun K circuits settings attempts (worldEnv D circuits settings)
      (worldMode attempts k sep) D A state outputs)

theorem genericSlotGame_zero :
    genericSlotGame K circuits settings attempts D A 0 false =
      dealerKeygenGame K settings attempts D A circuits := by
  unfold genericSlotGame dealerKeygenGame
  rw [worldMode_zero]
  simp only [slotRun_shared]

omit [Field E] [Algebra Bit E] in
/-- The shared and separated modes differ at exactly the selected slot. -/
theorem worldMode_eq_of_ne (k : ℕ) (slot : Slot attempts)
    (hne : ((slotOrder attempts) slot).val ≠ k) :
    worldMode attempts k false slot = worldMode attempts k true slot := by
  simp only [worldMode]
  split <;> simp_all

end Zero

section Normalized
variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

omit [Fintype E] [DecidableEq E] in
/-- Equality of the actual programs, before oracle evaluation or acceptance projection. -/
theorem slotGame_eq_generic (k : ℕ) (sep : Bool) :
    slotGame K settings attempts D A k sep circuits =
      genericSlotGame K circuits settings attempts D A k sep := by
  unfold slotGame
  split
  · obtain ⟨rfl, rfl⟩ := ‹k = 0 ∧ sep = false›
    exact (genericSlotGame_zero K circuits settings attempts D A).symm
  · rfl

end Normalized

/-- The fixed U4 numerator fits the slot allowance in the original small-budget branch. -/
theorem overlap_allowance (attempts Q F : ℕ)
    (small : Q + lifetimeOverhead C attempts Q + (F + 2) * Q < 2 ^ 128) :
    (((2 * (lifetimeRuns attempts - 1) + Q) * prssKeyCount C : ℕ) : ℝ) / 2 ^ 256 ≤
      streamKeyError C := by
  have ho := LifetimePrfTransportProof.runs_le_lifetimeOverhead (C := C) attempts Q
  have hb : 2 ≤ bottomTreeCalls C := by
    rw [LifetimePrfTransportProof.bottomTreeCalls_eq]
    omega
  have hn : 1 ≤ C.n := by have h := C.one_le_t; unfold Committee.n; omega
  have hm : 1 ≤ prssKeyCount C := by
    have h := LifetimePrfTransportProof.n_le_termCount (C := C)
    unfold prssKeyCount
    omega
  have hr : 4 * lifetimeRuns attempts ≤ lifetimeOverhead C attempts Q := by
    calc _ = lifetimeRuns attempts * 2 * 2 := by ring
      _ ≤ lifetimeRuns attempts * (C.n + 1) * bottomTreeCalls C := by gcongr; omega
      _ ≤ _ := ho
  have hc : 2 * (2 * (lifetimeRuns attempts - 1) + Q) ≤ 2 ^ 128 := by
    have hq : 2 * Q ≤ (F + 2) * Q := by nlinarith
    omega
  have hc' : 2 * (2 * (lifetimeRuns attempts - 1) + Q) ≤ 2 ^ 128 * prssKeyCount C := by
    calc _ ≤ 2 ^ 128 := hc
      _ ≤ _ := Nat.le_mul_of_pos_right _ hm
  have hreal : (2 : ℝ) * ((2 * (lifetimeRuns attempts - 1) + Q : ℕ) : ℝ) ≤
      2 ^ 128 * (prssKeyCount C : ℝ) := by exact_mod_cast hc'
  have hmreal : 0 ≤ (prssKeyCount C : ℝ) := Nat.cast_nonneg _
  change _ ≤ ((prssKeyCount C ^ 2 : ℕ) : ℝ) / 2 ^ 129
  push_cast
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hmul := mul_le_mul_of_nonneg_right hreal hmreal
  norm_num [show (256 : ℕ) = 128 + 128 from rfl, pow_add] at *
  nlinarith

/-- The complete persistent state of an evaluated emulation. -/
abbrev WorldState (C : Committee) := StreamCache C × HashCache C × CallLog C

/-- Evaluate an emulation while retaining its stream table, hash cache and observation log. -/
def evalEmulation (prims : Primitives) {α : Type} (p : EmulationM C α) :
    StateT (WorldState C) ProbComp α := StateT.mk fun s =>
  (fun r => (r.1.1.1, (r.1.1.2, r.2, s.2.2 ++ r.1.2))) <$>
    (simulateQ (worldAnswer prims) ((p.run s.1).run)).run s.2.1

theorem evalEmulation_pure (prims : Primitives) {α : Type} (a : α) :
    evalEmulation (C := C) prims (pure a) = pure a := by
  apply StateT.ext
  intro s
  simp [evalEmulation, StateT.run_pure, WriterT.run_pure]

theorem evalEmulation_bind (prims : Primitives) {α β : Type}
    (p : EmulationM C α) (f : α → EmulationM C β) :
    evalEmulation prims (p >>= f) = evalEmulation prims p >>= fun a => evalEmulation prims (f a) := by
  apply StateT.ext
  intro s
  simp only [evalEmulation, StateT.run_bind, WriterT.run_bind, simulateQ_bind,
    simulateQ_map, StateT.run_map, StateT.run_mk, bind_map_left, map_bind,
    Functor.map_map]
  apply bind_congr
  rintro ⟨⟨⟨a, streams⟩, log⟩, cache⟩
  congr 1
  funext r
  simp [List.append_assoc]

/-- The evaluator is a monad map, so it retains adaptive continuations exactly. -/
def evalHom (prims : Primitives) : EmulationM C →ᵐ StateT (WorldState C) ProbComp where
  toFun _ := evalEmulation prims
  toFun_pure' := evalEmulation_pure prims
  toFun_bind' := evalEmulation_bind prims

/-- The actual slot scheduler state together with the full persistent oracle state. -/
abbrev Physical (C : Committee) (E : Type) := SlotState C E × WorldState C

/-- Flatten the slot state and evaluated emulation state without discarding either. -/
def evalSlot (prims : Primitives) {α : Type} (p : StateT (SlotState C E) (EmulationM C) α) :
    StateT (Physical C E) ProbComp α := StateT.mk fun s =>
  (fun r => (r.1.1, (r.1.2, r.2))) <$> (evalEmulation prims (p.run s.1)).run s.2

theorem evalSlot_pure (prims : Primitives) {α : Type} (a : α) :
    evalSlot (C := C) (E := E) prims (pure a) = pure a := by
  apply StateT.ext
  intro s
  simp [evalSlot, StateT.run_pure, evalEmulation_pure]

theorem evalSlot_bind (prims : Primitives) {α β : Type}
    (p : StateT (SlotState C E) (EmulationM C) α)
    (f : α → StateT (SlotState C E) (EmulationM C) β) :
    evalSlot prims (p >>= f) = evalSlot prims p >>= fun a => evalSlot prims (f a) := by
  apply StateT.ext
  intro s
  simp only [evalSlot, StateT.run_bind, evalEmulation_bind, StateT.run_mk, map_bind,
    bind_map_left]

def evalSlotHom (prims : Primitives) :
    StateT (SlotState C E) (EmulationM C) →ᵐ StateT (Physical C E) ProbComp where
  toFun _ := evalSlot prims
  toFun_pure' := evalSlot_pure prims
  toFun_bind' := evalSlot_bind prims

/-- Actual adversary requests, followed by the actual final win test. -/
abbrev TailSpec (C : Committee) (E : Type) :=
  (LocalSpec C + LifetimeSpec C E) + (Forgery →ₒ Bool)

/-- The original adversary continuation, with its final test made explicit. -/
def tailProgram (A : LifetimeAdversary C E) (state : A.keygen.State) (parameter : PublicParameter) :
    OracleComp (TailSpec C E) Bool := do
  let forgery ← simulateQ (fun t => OracleComp.lift (OracleSpec.query (spec := TailSpec C E) (.inl t)))
    (A.run state parameter)
  OracleComp.lift (OracleSpec.query (spec := TailSpec C E) (.inr forgery))

section Tail
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts k : ℕ)
variable (D : C.Coalition) (keys : C.Party → Keys C) (h : C.Party)

/-- The unchanged win test of the frozen slot interpreter. -/
def finish (forgery : Forgery) (st : LifetimeState C E) : EmulationM C Bool := do
  if ¬ ∀ i, i ∉ D.1 → (st.top i).isSome then pure false else do
  let some (_, top) := st.publicKey (keys h).parameter h | pure false
  let lift : ∀ {α : Type}, OracleComp (RoSpec C) α → EmulationM C α :=
    fun p => (lifetimeHybridRoles D 0 0).honest (liftComp p _)
  forgeryWins lift (dealtWith lift (keys h).parameter keys top
    (fun x => lift (prfValue (honestSeeds D keys) x))) st.sign forgery

/-- The frozen request handler and its final test, with no caps or replacement continuation. -/
def tailHandler (sep : Bool) :
    QueryImpl (TailSpec C E) (StateT (SlotState C E) (EmulationM C)) :=
  ((fun t => StateT.lift ((lifetimeHybridRoles D 0 0).adversary
      (OracleComp.lift (OracleSpec.query t)))) +
    slotOracles K circuits settings attempts (worldEnv D circuits settings)
      (worldMode attempts k sep) D keys
      (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _)) h) +
    (fun forgery => StateT.mk fun (s : SlotState C E) => (fun b => (b, s)) <$> finish D keys h forgery s.1)

/-- One actual request, evaluated with both caches and the complete observation log. -/
def rawKernel (prims : Primitives) (sep : Bool) :
    QueryImpl (TailSpec C E) (StateT (Physical C E) ProbComp) :=
  fun t => evalSlot prims (tailHandler K circuits settings attempts k D keys h sep t)

end Tail

/-- The common initial lifetime state after keygen. -/
def initialSlot (D : C.Coalition) : SlotState C E :=
  (⟨⟨D.1, fun _ => none, [], fun _ => none⟩, fun _ => none, fun _ _ => none,
    0, fun _ => 0, ∅, none⟩, none)

section TailExact
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts k : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

set_option backward.isDefEq.respectTransparency false in
/-- Splitting off the final query preserves the complete slot computation. -/
theorem tailProgram_run (sep : Bool) (state : A.keygen.State) (keys : C.Party → Keys C)
    (h : C.Party) (s : SlotState C E) :
    (simulateQ (tailHandler K circuits settings attempts k D keys h sep)
      (tailProgram A state (keys h).parameter)).run s = (do
    let (forgery, s') ← (simulateQ
      ((fun t => StateT.lift ((lifetimeHybridRoles D 0 0).adversary
        (OracleComp.lift (OracleSpec.query t)))) +
      slotOracles K circuits settings attempts (worldEnv D circuits settings)
        (worldMode attempts k sep) D keys
        (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _)) h)
      (A.run state (keys h).parameter)).run s
    (fun b => (b, s')) <$> finish D keys h forgery s'.1) := by
  unfold tailProgram
  rw [simulateQ_bind, LifetimeEmulatedBudget.simulateQ_comp]
  have hi : (fun t => simulateQ (tailHandler K circuits settings attempts k D keys h sep)
      (OracleComp.lift (OracleSpec.query (.inl t)))) =
      ((fun t => StateT.lift ((lifetimeHybridRoles D 0 0).adversary
        (OracleComp.lift (OracleSpec.query t)))) +
      slotOracles K circuits settings attempts (worldEnv D circuits settings)
        (worldMode attempts k sep) D keys
        (fun x => (lifetimeHybridRoles D 0 0).honest (liftComp (prfValue (honestSeeds D keys) x) _)) h) := by
    funext t
    rw [simulateQ_spec_query]
    rfl
  erw [hi]
  simp only [simulateQ_spec_query, StateT.run_bind]
  rfl

/-- The kernel evaluator commutes with every adaptive request of the original adversary. -/
theorem rawKernel_run (prims : Primitives) (sep : Bool) (state : A.keygen.State)
    (keys : C.Party → Keys C) (h : C.Party) :
    simulateQ (rawKernel K circuits settings attempts k D keys h prims sep)
      (tailProgram A state (keys h).parameter) =
    evalSlot prims (simulateQ (tailHandler K circuits settings attempts k D keys h sep)
      (tailProgram A state (keys h).parameter)) := by
  symm
  exact LifetimeEmulatedBudget.hom_simulateQ (evalSlotHom prims) _ _

end TailExact

/-- The selected table is retained even when a later run replaces the active auxiliary table. -/
structure Ghost (D : C.Coalition) where
  active : Bool
  started : Bool
  selected : StreamCache C
  overlaps : Finset {name : KeyName C // Hidden D name}

def Ghost.empty (D : C.Coalition) : Ghost D := ⟨false, false, ∅, ∅⟩

def overlapNames (D : C.Coalition) (shared selected : StreamCache C) :
    Finset {name : KeyName C // Hidden D name} :=
  Finset.univ.filter fun name => ∃ (key : HashOutput) (a b : ℕ × ℕ × ℕ),
    (shared (name.1, key, a)).isSome ∧ (selected (name.1, key, b)).isSome

/-- The observer changes the active marker only at an actually accepted ceremony start. -/
def advanceGhost (attempts k : ℕ) (D : C.Coalition) (t : (TailSpec C E).Domain)
    (before after : Physical C E) (g : Ghost D) : Ghost D :=
  let active := match t with
    | .inl (.inr (.start tree)) =>
        if LifetimeProof.canStart attempts D before.1.1 tree then
          decide ((startSlot attempts before.1.1 tree).map (fun slot => ((slotOrder attempts) slot).val) = some k)
        else g.active
    | _ => g.active
  let selected := if active then (after.1.2.map Prod.fst).getD g.selected else g.selected
  ⟨active, g.started || active, selected, g.overlaps ∪ overlapNames D after.2.1 selected⟩

abbrev Marked (D : C.Coalition) (E : Type) := Physical C E × Ghost D

def Bad (D : C.Coalition) (s : Marked D E) : Prop := s.2.overlaps.Nonempty

section Marked
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts k : ℕ)
variable (D : C.Coalition) (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)

/-- Instrumentation of the actual separated kernel; it changes no answer or physical state. -/
def markedKernel : QueryImpl (TailSpec C E) (StateT (Marked D E) ProbComp) := fun t =>
  StateT.mk fun s =>
    (fun r => (r.1, (r.2, advanceGhost attempts k D t s.1 r.2 s.2))) <$>
      (rawKernel K circuits settings attempts k D keys h prims true t).run s.1

/-- Erasing the observer preserves the entire physical marginal, including the log. -/
theorem markedKernel_erase {α : Type} (p : OracleComp (TailSpec C E) α) (s : Marked D E) :
    (fun r => (r.1, r.2.1)) <$>
      (simulateQ (markedKernel K circuits settings attempts k D keys h prims) p).run s =
    (simulateQ (rawKernel K circuits settings attempts k D keys h prims true) p).run s.1 := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t f ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, markedKernel,
      StateT.run_mk, map_bind, bind_map_left]
    apply bind_congr
    intro r
    exact ih r.1 _

/-- Recorded overlap names never disappear, including when the selected run has settled. -/
theorem markedKernel_grows (t : (TailSpec C E).Domain) (s : Marked D E)
    (r : TailSpec C E t × Marked D E)
    (hr : r ∈ support ((markedKernel K circuits settings attempts k D keys h prims t).run s)) :
    s.2.overlaps ⊆ r.2.2.overlaps := by
  simp only [markedKernel, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨u, _, rfl⟩ := hr
  exact Finset.subset_union_left

theorem markedRun_grows {α : Type} (p : OracleComp (TailSpec C E) α) (s : Marked D E)
    (r : α × Marked D E)
    (hr : r ∈ support ((simulateQ (markedKernel K circuits settings attempts k D keys h prims) p).run s)) :
    s.2.overlaps ⊆ r.2.2.overlaps := by
  induction p using OracleComp.inductionOn generalizing s with
  | pure a =>
    have he : r = (a, s) := by simpa using hr
    rw [he]
  | query_bind t f ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨u, hu, hr⟩ := hr
    exact (markedKernel_grows K circuits settings attempts k D keys h prims t s u hu).trans
      (ih u.1 u.2 hr)

end Marked

def slotAttempt {attempts : ℕ} : Slot attempts → ℕ
  | .inl r => r.val
  | .inr (_, r) => r.val

/-- The separated physical state and the shared physical state before the first overlap.
The full lifetime state includes every suspended party continuation. The shared table on
 the right is the union of the two actually queried tables on the left. -/
def StateRelation (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) : Prop :=
  s.1.1.1 = t.1.1 ∧ s.1.2.2.1 = t.2.2.1 ∧ s.1.2.2.2 = t.2.2.2 ∧
  (∀ x, t.2.1 x = (s.1.2.1 x).or (s.2.selected x)) ∧
  (∀ x, (s.1.2.1 x).isSome ∨ (s.2.selected x).isSome → Hidden D x.1) ∧
  (s.2.started = decide (slotAttempt ((slotOrder attempts).symm k) <
    LifetimeProof.runsAt s.1.1.1 (slotTree ((slotOrder attempts).symm k)))) ∧
  (s.2.started = false → s.2.selected = ∅) ∧
  (s.2.active = true → s.2.started = true) ∧
  (if s.2.active then s.1.1.2 = some (s.2.selected, none) ∧ t.1.2 = none
    else s.1.1.2 = t.1.2) ∧
  overlapNames D s.1.2.1 s.2.selected ⊆ s.2.overlaps

section Coupling
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))

/-- One actual request of the frozen slot worlds, below the arbitrary adversary continuation.
The relation and the observer are fixed; neither side chooses a replacement scheduler or cache. -/
def KernelCoupling : Prop :=
  ∀ (prims : Primitives) (keys : C.Party → Keys C) (h : C.Party)
    (q : (TailSpec C E).Domain) (s : Marked D E) (t : Physical C E),
    StateRelation attempts k D s t → ¬ Bad D s →
    RelTriple
      ((markedKernel K circuits settings attempts k D keys h prims q).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false q).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2))

/-- Support facts can be lifted through the product coupling without changing either marginal. -/
theorem relTriple_left_support {α β : Type} (p : ProbComp α) (q : ProbComp β)
    (R : α → Prop) (h : ∀ a ∈ support p, R a) : RelTriple p q (fun a _ => R a) := by
  let c := _root_.SPMF.Coupling.prod (probFailure_eq_zero (mx := p)) (probFailure_eq_zero (mx := q))
  refine relTriple_iff_relWP.2 ⟨c, fun z hz => ?_⟩
  apply h z.1
  have hz' : z.1 ∈ support 𝒟[p] := by
    rw [← c.2.map_fst, support_map]
    exact ⟨z, hz, rfl⟩
  exact (mem_support_iff_evalDist_apply_ne_zero p z.1).2 hz'

/-- The fixed one-request coupling composes through all actual adaptive requests. -/
theorem run_coupling (coupled : KernelCoupling K circuits settings attempts D k)
    (prims : Primitives) (keys : C.Party → Keys C) (h : C.Party)
    {α : Type} (p : OracleComp (TailSpec C E) α) (s : Marked D E) (t : Physical C E)
    (related : StateRelation attempts k D s t) :
    RelTriple
      ((simulateQ (markedKernel K circuits settings attempts k D keys h prims) p).run s)
      ((simulateQ (rawKernel K circuits settings attempts k D keys h prims false) p).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  induction p using OracleComp.inductionOn generalizing s t with
  | pure a => exact relTriple_pure_pure (Or.inr ⟨rfl, related⟩)
  | query_bind q f ih =>
    by_cases bad : Bad D s
    · apply relTriple_post_mono (relTriple_left_support _ _ _ (fun r hr => ?_))
        (fun _ _ hb => Or.inl hb)
      exact Finset.Nonempty.mono
        (markedRun_grows K circuits settings attempts k D keys h prims _ s r hr) bad
    · simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply relTriple_bind (coupled prims keys h q s t related bad)
      rintro ⟨a, s'⟩ ⟨b, t'⟩ (hb | ⟨eq, rel⟩)
      · apply relTriple_post_mono (relTriple_left_support _ _ _ (fun r hr => ?_))
          (fun _ _ hb => Or.inl hb)
        exact Finset.Nonempty.mono
          (markedRun_grows K circuits settings attempts k D keys h prims _ s' r hr) hb
      · dsimp only at eq rel ⊢
        subst b
        exact ih a s' t' rel

end Coupling

theorem initial_relation (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (cache : HashCache C) :
    StateRelation attempts k D ((initialSlot (E := E) D, (∅, cache, [])), Ghost.empty D)
      (initialSlot D, (∅, cache, [])) := by
  have runs : LifetimeProof.runsAt (initialSlot (E := E) D).1
      (slotTree ((slotOrder attempts).symm k)) = 0 := by
    cases (slotOrder attempts).symm k <;> rfl
  simp [StateRelation, Ghost.empty, overlapNames, initialSlot]
  change LifetimeProof.runsAt (initialSlot D).1 _ ≤ _
  rw [runs]
  exact Nat.zero_le _

section Games
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts k : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E) (prims : Primitives)

/-- The same actual ideal keygen prefix on both sides of a slot transport. -/
def keygenPrefix : ProbComp ((A.keygen.State × (C.Party → Option (Keys C))) × HashCache C) :=
  (simulateQ (worldAnswer prims) (idealExecution (fun p => p) D Fkeygen
    (keygenSimulator D A.keygen) (fun _ => ()) [])).run ∅

/-- The complete evaluated slot world through the explicit request kernel. -/
def rawGame (sep : Bool) : ProbComp (Bool × Physical C E) := do
  let ((state, outputs), cache) ← keygenPrefix D A prims
  let s : Physical C E := (initialSlot D, (∅, cache, []))
  let some h := C.parties.find? (· ∉ D.1) | pure (false, s)
  if ¬ ∀ i, i ∉ D.1 → (outputs i).isSome then pure (false, s) else do
  let keys := fun i => (outputs i).getD default
  (simulateQ (rawKernel K circuits settings attempts k D keys h prims sep)
    (tailProgram A state (keys h).parameter)).run s

/-- The separated world with the fixed retained-table observer. -/
def markedGame : ProbComp (Bool × Marked D E) := do
  let ((state, outputs), cache) ← keygenPrefix D A prims
  let s : Marked D E := ((initialSlot D, (∅, cache, [])), Ghost.empty D)
  let some h := C.parties.find? (· ∉ D.1) | pure (false, s)
  if ¬ ∀ i, i ∉ D.1 → (outputs i).isSome then pure (false, s) else do
  let keys := fun i => (outputs i).getD default
  (simulateQ (markedKernel K circuits settings attempts k D keys h prims)
    (tailProgram A state (keys h).parameter)).run s

/-- The complete evaluated physical state is the marginal of the instrumented world. -/
theorem markedGame_erase :
    (fun r => (r.1, r.2.1)) <$> markedGame K circuits settings attempts k D A prims =
      rawGame K circuits settings attempts k D A prims true := by
  simp only [markedGame, rawGame, map_bind]
  apply bind_congr
  rintro ⟨⟨state, outputs⟩, cache⟩
  cases hh : C.parties.find? (· ∉ D.1) with
  | none => exact map_pure _ _
  | some h =>
    dsimp only
    by_cases ho : ∀ i, i ∉ D.1 → (outputs i).isSome
    · erw [if_neg (not_not_intro ho), if_neg (not_not_intro ho)]
      exact markedKernel_erase K circuits settings attempts k D _ h prims _ _
    · erw [if_pos ho, if_pos ho]
      exact map_pure _ _

end Games

section GameCoupling
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E) (prims : Primitives)
variable (k : Fin (lifetimeRuns attempts))

/-- The actual common keygen prefix and all adaptive requests compose the fixed local coupling. -/
theorem game_coupling (coupled : KernelCoupling K circuits settings attempts D k) :
    RelTriple (markedGame K circuits settings attempts k D A prims)
      (rawGame K circuits settings attempts k D A prims false)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  unfold markedGame rawGame
  apply relTriple_bind (relTriple_refl (keygenPrefix D A prims))
  rintro ⟨⟨state, outputs⟩, cache⟩ _ rfl
  cases hh : C.parties.find? (· ∉ D.1) with
  | none => exact relTriple_pure_pure (Or.inr ⟨rfl, initial_relation attempts k D cache⟩)
  | some h =>
    dsimp only
    by_cases ho : ∀ i, i ∉ D.1 → (outputs i).isSome
    · erw [if_neg (not_not_intro ho), if_neg (not_not_intro ho)]
      exact run_coupling K circuits settings attempts D k coupled prims _ h _ _ _
        (initial_relation attempts k D cache)
    · erw [if_pos ho, if_pos ho]
      exact relTriple_pure_pure (Or.inr ⟨rfl, initial_relation attempts k D cache⟩)

end GameCoupling

theorem evalEmulation_map (prims : Primitives) {α β : Type} (f : α → β) (p : EmulationM C α) :
    evalEmulation prims (f <$> p) = f <$> evalEmulation prims p := by
  simp only [map_eq_bind_pure_comp, evalEmulation_bind, evalEmulation_pure, Function.comp_def]

theorem evalSlot_output (prims : Primitives) {α : Type}
    (p : StateT (SlotState C E) (EmulationM C) α) (st : SlotState C E) (w : WorldState C) :
    Prod.fst <$> (evalSlot prims p).run (st, w) =
      (evalEmulation prims (Prod.fst <$> p.run st)).run' w := by
  simp only [evalSlot, StateT.run_mk, Functor.map_map, evalEmulation_map, StateT.run'_eq,
    StateT.run_map]

theorem evalEmulation_lift (prims : Primitives) {α : Type} (p : OracleComp (WorldSpec C) α)
    (streams : StreamCache C) (cache : HashCache C) (log : CallLog C) :
    (evalEmulation prims (StateT.lift (liftM p))).run (streams, cache, log) =
      (fun r => (r.1, (streams, r.2, log))) <$> (simulateQ (worldAnswer prims) p).run cache := by
  simp only [evalEmulation, StateT.run_mk, StateT.run_lift, bind_pure_comp, WriterT.run_map,
    WriterT.run_liftM, simulateQ_map, StateT.run_map, Functor.map_map]
  change (fun a : α × HashCache C => (a.1, streams, a.2, log ++ [])) <$> _ = _
  simp only [List.append_nil]

section Output
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts k : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E) (prims : Primitives)

/-- The explicit final request is exactly the frozen slot interpreter's win test. -/
theorem slotRun_tail (sep : Bool) (state : A.keygen.State) (outputs : C.Party → Option (Keys C)) :
    slotRun K circuits settings attempts (worldEnv D circuits settings) (worldMode attempts k sep)
      D A state outputs = (do
    let some h := C.parties.find? (· ∉ D.1) | pure false
    if ¬ ∀ i, i ∉ D.1 → (outputs i).isSome then pure false else do
    let keys := fun i => (outputs i).getD default
    Prod.fst <$> (simulateQ (tailHandler K circuits settings attempts k D keys h sep)
      (tailProgram A state (keys h).parameter)).run (initialSlot D)) := by
  unfold slotRun
  cases hh : C.parties.find? (· ∉ D.1) with
  | none => rfl
  | some h =>
    dsimp only
    by_cases ho : ∀ i, i ∉ D.1 → (outputs i).isSome
    · rw [if_neg (not_not_intro ho), if_neg (not_not_intro ho), tailProgram_run]
      simp only [map_bind, Functor.map_map]
      apply bind_congr
      intro r
      change _ = id <$> _
      rw [id_map]
      rfl
    · rw [if_pos ho, if_pos ho]

/-- The kernel game has exactly the original Boolean output law at each fixed primitive. -/
theorem rawGame_output (sep : Bool) :
    Prod.fst <$> rawGame K circuits settings attempts k D A prims sep =
      (simulateQ (worldAnswer prims)
        (genericSlotGame K circuits settings attempts D A k sep)).run' ∅ := by
  have eval : (simulateQ (worldAnswer prims)
      (genericSlotGame K circuits settings attempts D A k sep)).run' ∅ =
      (evalEmulation prims (do
        let (state, outputs) ← StateT.lift (liftM
          (idealExecution (fun p => p) D Fkeygen (keygenSimulator D A.keygen) (fun _ => ()) []))
        slotRun K circuits settings attempts (worldEnv D circuits settings)
          (worldMode attempts k sep) D A state outputs)).run' (∅, ∅, []) := by
    simp only [genericSlotGame, emulationGame, StateT.run'_eq, evalEmulation,
      StateT.run_mk, simulateQ_map, StateT.run_map, Functor.map_map]
  rw [eval]
  simp only [rawGame, map_bind, evalEmulation_bind, StateT.run'_eq, StateT.run_bind,
    evalEmulation_lift, bind_map_left]
  unfold keygenPrefix
  apply bind_congr
  rintro ⟨⟨state, outputs⟩, cache⟩
  rw [slotRun_tail]
  cases hh : C.parties.find? (· ∉ D.1) with
  | none => simp only [map_pure, evalEmulation_pure, StateT.run_pure]
  | some h =>
    dsimp only
    by_cases ho : ∀ i, i ∉ D.1 → (outputs i).isSome
    · erw [if_neg (not_not_intro ho), if_neg (not_not_intro ho)]
      rw [rawKernel_run, evalSlot_output]
      rfl
    · erw [if_pos ho, if_pos ho]
      simp only [map_pure, evalEmulation_pure, StateT.run_pure]

end Output

/-- A coupling that preserves the event outside a fixed source bad event bounds the gap once. -/
theorem gap_le_source_bad {α β : Type} (p : ProbComp α) (q : ProbComp β)
    (left : α → Prop) (right : β → Prop) (bad : α → Prop)
    (coupled : RelTriple p q (fun a b => bad a ∨ (left a ↔ right b))) :
    |(Pr[left | p]).toReal - (Pr[right | q]).toReal| ≤ (Pr[bad | p]).toReal := by
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 coupled
  have hl : Pr[left ∘ Prod.fst | c.1] = Pr[left | p] := by
    rw [← probEvent_map, c.2.map_fst]
    rfl
  have hr : Pr[right ∘ Prod.snd | c.1] = Pr[right | q] := by
    rw [← probEvent_map, c.2.map_snd]
    rfl
  have hb : Pr[bad ∘ Prod.fst | c.1] = Pr[bad | p] := by
    rw [← probEvent_map, c.2.map_fst]
    rfl
  have forward : Pr[left | p] ≤ Pr[right | q] + Pr[bad | p] := by
    rw [← hl, ← hr, ← hb]
    refine (probEvent_mono (mx := c.1) (q := fun z => right z.2 ∨ bad z.1) ?_).trans
      (probEvent_or_le _ _ _)
    intro z hz hleft
    rcases hc z hz with hbad | eq
    · exact Or.inr hbad
    · exact Or.inl (eq.mp hleft)
  have backward : Pr[right | q] ≤ Pr[left | p] + Pr[bad | p] := by
    rw [← hl, ← hr, ← hb]
    refine (probEvent_mono (mx := c.1) (q := fun z => left z.1 ∨ bad z.1) ?_).trans
      (probEvent_or_le _ _ _)
    intro z hz hright
    rcases hc z hz with hbad | eq
    · exact Or.inr hbad
    · exact Or.inl (eq.mpr hright)
  have hf := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) forward
  have hg := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) backward
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at hf hg
  exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩

section Events
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E) (prims : Primitives)
variable (k : Fin (lifetimeRuns attempts))

/-- The local coupling pays the recorded source overlap event only once. -/
theorem rawGame_gap (coupled : KernelCoupling K circuits settings attempts D k) :
    |(Pr[fun r => r.1 = true | rawGame K circuits settings attempts k D A prims false]).toReal -
      (Pr[fun r => r.1 = true | rawGame K circuits settings attempts k D A prims true]).toReal| ≤
    (Pr[Bad D ∘ Prod.snd | markedGame K circuits settings attempts k D A prims]).toReal := by
  have hc := game_coupling K circuits settings attempts D A prims k coupled
  have hg := gap_le_source_bad _ _ (fun r => r.1 = true) (fun r => r.1 = true)
    (Bad D ∘ Prod.snd) (relTriple_post_mono hc fun a b hab => by
      rcases hab with hb | ⟨eq, _⟩
      · exact Or.inl hb
      · exact Or.inr (by rw [eq]))
  have he : Pr[fun r => r.1 = true | markedGame K circuits settings attempts k D A prims] =
      Pr[fun r => r.1 = true | rawGame K circuits settings attempts k D A prims true] := by
    rw [← markedGame_erase K circuits settings attempts k D A prims, probEvent_map]
    rfl
  rw [he, abs_sub_comm] at hg
  exact hg

/-- Finite union over the fixed hidden names, with the original U4 numerator. -/
theorem markedGame_bad_bound (Q : ℕ)
    (bounds : ∀ name : {name : KeyName C // Hidden D name},
      Pr[fun r => name ∈ r.2.2.overlaps | markedGame K circuits settings attempts k D A prims] ≤
        ((2 * (lifetimeRuns attempts - 1) + Q : ℕ) : ℝ≥0∞) / 2 ^ 256) :
    (Pr[Bad D ∘ Prod.snd | markedGame K circuits settings attempts k D A prims]).toReal ≤
      (((2 * (lifetimeRuns attempts - 1) + Q) * prssKeyCount C : ℕ) : ℝ) / 2 ^ 256 := by
  have hu := probEvent_exists_finset_le_sum
    (Finset.univ : Finset {name : KeyName C // Hidden D name})
    (markedGame K circuits settings attempts k D A prims) (fun name r => name ∈ r.2.2.overlaps)
  simp only [Finset.mem_univ, true_and] at hu
  have hsum := (Finset.sum_le_sum (s := Finset.univ) (fun name _ => bounds name))
  have hp : Pr[Bad D ∘ Prod.snd | markedGame K circuits settings attempts k D A prims] ≤
      (((2 * (lifetimeRuns attempts - 1) + Q) * prssKeyCount C : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    change Pr[fun r : Bool × Marked D E => ∃ name, name ∈ r.2.2.overlaps | _] ≤ _
    refine (hu.trans hsum).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_div_assoc,
      Nat.cast_mul]
    apply ENNReal.div_le_div_right
    rw [mul_comm]
    gcongr
    exact_mod_cast aimed_hidden_card D
  have hr := ENNReal.toReal_mono (by finiteness) hp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat] using hr

end Events

section Assembly
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The frozen slot probability is the average of the actual evaluated kernel games. -/
theorem slotProbability_raw (k : ℕ) (sep : Bool) :
    slotProbability K settings attempts aes circuitsOf D A k sep =
      (Pr[fun b : Bool => b = true | do
        let values ← $ᵗ (MpcDomain → HashOutput)
        Prod.fst <$> rawGame K (circuitsOf (thOf values)) settings attempts k D A
          ⟨thOf values, aes⟩ sep]).toReal := by
  unfold slotProbability
  have he : (fun r : Bool × ℕ => r.1 = true) = (fun b : Bool => b = true) ∘ Prod.fst := rfl
  rw [he, ← probEvent_map, LifetimeKeygenHopProof.lifetimeRun_output]
  congr 2
  apply bind_congr
  intro values
  rw [slotGame_eq_generic, ← rawGame_output]

/-- The U4 estimate for each hidden name of the selected run in the actual separated world.
The observer retains the selected table through every later shared run. The original source
circuit assumptions and all-answer lifetime budget remain premises of this estimate. -/
def SelectedKeyOverlapBound (Q : ℕ) : Prop :=
  (∀ Th, CircuitsCompute (circuitsOf Th) Th) → FixedShape circuitsOf →
  0 < settings.batchSize → HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q →
  Q + lifetimeOverhead C attempts Q + (ceremonyFuel (circuitsOf fun _ => 0) settings + 2) * Q < 2 ^ 128 →
  ∀ (k : Fin (lifetimeRuns attempts)) (values : MpcDomain → HashOutput)
      (name : {name : KeyName C // Hidden D name}),
    Pr[fun r => name ∈ r.2.2.overlaps |
      markedGame K (circuitsOf (thOf values)) settings attempts k D A ⟨thOf values, aes⟩] ≤
      ((2 * (lifetimeRuns attempts - 1) + Q : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- The concrete local coupling and recorded-name estimates imply the unchanged slot contract. -/
theorem slotTransport_of_kernel_overlap (Q : ℕ)
    (hcompute : ∀ Th, CircuitsCompute (circuitsOf Th) Th) (hshape : FixedShape circuitsOf)
    (hbatch : 0 < settings.batchSize) (hQ : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q)
    (coupled : ∀ (values : MpcDomain → HashOutput) (k : Fin (lifetimeRuns attempts)),
      KernelCoupling K (circuitsOf (thOf values)) settings attempts D k)
    (bounded : SelectedKeyOverlapBound K settings attempts aes circuitsOf D A Q) :
    SlotTransport K settings attempts aes circuitsOf D A Q := by
  intro small k
  rw [slotProbability_raw, slotProbability_raw]
  have hpoint (values : MpcDomain → HashOutput) :
      |(Pr[fun b : Bool => b = true | Prod.fst <$>
        rawGame K (circuitsOf (thOf values)) settings attempts k D A ⟨thOf values, aes⟩ false]).toReal -
      (Pr[fun b : Bool => b = true | Prod.fst <$>
        rawGame K (circuitsOf (thOf values)) settings attempts k D A ⟨thOf values, aes⟩ true]).toReal| ≤
        streamKeyError C := by
    simp only [probEvent_map, Function.comp_def]
    exact (rawGame_gap K (circuitsOf (thOf values)) settings attempts D A
      ⟨thOf values, aes⟩ k (coupled values k)).trans
      ((markedGame_bad_bound K (circuitsOf (thOf values)) settings attempts D A
        ⟨thOf values, aes⟩ k Q (bounded hcompute hshape hbatch hQ small k values)).trans
        (overlap_allowance attempts Q _ small))
  have avg := abs_probEvent_bind_sub_le_sum ($ᵗ (MpcDomain → HashOutput)) _ _
    (fun b : Bool => b = true) (fun _ => streamKeyError C) hpoint
  exact avg.trans (sum_probOutput_mul_const_le _ (by unfold streamKeyError; positivity))

end Assembly

/-- Update only the hash cache and the observation log. -/
def updateWorld (s : Physical C E) (cache : HashCache C) (log : CallLog C) : Physical C E :=
  (s.1, (s.2.1, cache, log))

theorem stateRelation_update (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (cache : HashCache C) (log : CallLog C) :
    StateRelation attempts k D (updateWorld s.1 cache log, s.2) (updateWorld t cache log) :=
  ⟨related.1, rfl, rfl, related.2.2.2⟩

/-- A plain local query cannot add a stream overlap or change the retained-table marker. -/
theorem advanceGhost_local (attempts : ℕ) (k : Fin (lifetimeRuns attempts)) (D : C.Coalition)
    (s : Marked D E) (t : Physical C E) (related : StateRelation attempts k D s t)
    (q : (LocalSpec C).Domain) (cache : HashCache C) (log : CallLog C) :
    advanceGhost attempts k D (.inl (.inl q)) s.1 (updateWorld s.1 cache log) s.2 = s.2 := by
  obtain ⟨_, _, _, _, _, _, _, active, aux, seen⟩ := related
  cases ha : s.2.active with
  | false =>
    simp only [advanceGhost, ha, Bool.false_eq_true, ↓reduceIte, Bool.or_false, updateWorld]
    rw [Finset.union_eq_left.mpr seen]
    cases hg : s.2
    simp only [hg] at ha ⊢
    cases ha
    rfl
  | true =>
    have hs := active ha
    simp only [ha, ↓reduceIte] at aux
    simp only [advanceGhost, ha, ↓reduceIte, updateWorld, aux.1, Option.map_some,
      Option.getD_some, hs, Bool.true_or]
    rw [Finset.union_eq_left.mpr seen]
    cases hg : s.2
    simp only [hg] at ha hs ⊢
    cases ha
    cases hs
    rfl

section Local
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))
variable (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)

/-- The local-query branch evaluates the same observed query on the hash cache only. -/
theorem rawKernel_local (sep : Bool) (q : (LocalSpec C).Domain) (s : Physical C E) :
    (rawKernel K circuits settings attempts k D keys h prims sep (.inl (.inl q))).run s =
      (fun r => (r.1.1, updateWorld s r.2 (s.2.2.2 ++ r.1.2))) <$>
        (simulateQ (worldAnswer prims) (observe (OracleComp.lift (OracleSpec.query q)))).run s.2.2.1 := by
  change (evalSlot prims (StateT.lift ((emulatedRoles D).adversary
    (OracleComp.lift (OracleSpec.query q))))).run s = _
  simp only [evalSlot, StateT.run_mk, StateT.run_lift, bind_pure_comp, evalEmulation_map,
    StateT.run_map, Functor.map_map]
  simp only [evalEmulation, emulatedRoles, StateT.run_mk, StateT.run_lift, bind_pure_comp,
    WriterT.run_map, Functor.map_map, simulateQ_map, StateT.run_map]
  rfl

/-- The adversary's ordinary local queries satisfy the concrete kernel coupling unconditionally. -/
theorem local_coupling (q : (LocalSpec C).Domain) (s : Marked D E) (t : Physical C E)
    (related : StateRelation attempts k D s t) :
    RelTriple
      ((markedKernel K circuits settings attempts k D keys h prims (.inl (.inl q))).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inl (.inl q))).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  simp only [markedKernel, StateT.run_mk, rawKernel_local]
  erw [Functor.map_map]
  have he : s.1.2.2.1 = t.2.2.1 := related.2.1
  rw [he]
  apply relTriple_map
  apply relTriple_post_mono (relTriple_refl _)
  intro a b hab
  change a = b at hab
  subst b
  dsimp only [Function.comp_apply]
  rw [advanceGhost_local attempts k D s t related]
  refine Or.inr ⟨rfl, ?_⟩
  have hl : s.1.2.2.2 = t.2.2.2 := related.2.2.1
  rw [hl]
  exact stateRelation_update attempts k D s t related _ _

end Local

section Control
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))
variable (keys : C.Party → Keys C) (h : C.Party) (prims : Primitives)

/-- Reading the public key has no oracle or stream-state effect. -/
theorem rawKernel_publicKey (sep : Bool) (s : Physical C E) :
    (rawKernel K circuits settings attempts k D keys h prims sep (.inl (.inr .publicKey))).run s =
      pure (s.1.1.publicKey (keys h).parameter h, s) := by
  change (evalSlot prims (StateT.mk fun st : SlotState C E =>
    pure (st.1.publicKey (keys h).parameter h, st))).run s = _
  simp only [evalSlot, StateT.run_mk, evalEmulation_pure, StateT.run_pure, map_pure]

/-- Static corruption requests are the unchanged, pure refusal of the lifetime interface. -/
theorem rawKernel_corrupt (sep : Bool) (i : C.Party) (s : Physical C E) :
    (rawKernel K circuits settings attempts k D keys h prims sep (.inl (.inr (.sign (.corrupt i))))).run s =
      pure (none, s) := by
  change (evalSlot prims (pure none)).run s = _
  rw [evalSlot_pure]
  rfl

/-- Pure unchanged-state requests preserve the concrete relation and overlap observer. -/
theorem pure_coupling {q : (TailSpec C E).Domain} (s : Marked D E) (t : Physical C E)
    (related : StateRelation attempts k D s t) (a : TailSpec C E q)
    (left : (rawKernel K circuits settings attempts k D keys h prims true q).run s.1 = pure (a, s.1))
    (right : (rawKernel K circuits settings attempts k D keys h prims false q).run t = pure (a, t))
    (observer : advanceGhost attempts k D q s.1 s.1 s.2 = s.2) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims q).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false q).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  simp only [markedKernel, StateT.run_mk, left, right, map_pure, observer]
  exact relTriple_pure_pure (Or.inr ⟨rfl, related⟩)

theorem publicKey_coupling (s : Marked D E) (t : Physical C E)
    (related : StateRelation attempts k D s t) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims (.inl (.inr .publicKey))).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inl (.inr .publicKey))).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  apply pure_coupling K circuits settings attempts D k keys h prims
    (q := .inl (.inr .publicKey)) s t related
    (s.1.1.1.publicKey (keys h).parameter h)
  · exact rawKernel_publicKey K circuits settings attempts D k keys h prims true s.1
  · rw [rawKernel_publicKey, related.1]
    rfl
  · exact advanceGhost_local attempts k D s t related (.inl 0) s.1.2.2.1 s.1.2.2.2

theorem corrupt_coupling (i : C.Party) (s : Marked D E) (t : Physical C E)
    (related : StateRelation attempts k D s t) :
    RelTriple ((markedKernel K circuits settings attempts k D keys h prims (.inl (.inr (.sign (.corrupt i))))).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false (.inl (.inr (.sign (.corrupt i))))).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2)) := by
  apply pure_coupling K circuits settings attempts D k keys h prims
    (q := .inl (.inr (.sign (.corrupt i)))) s t related none
  · exact rawKernel_corrupt K circuits settings attempts D k keys h prims true i s.1
  · exact rawKernel_corrupt K circuits settings attempts D k keys h prims false i t
  · exact advanceGhost_local attempts k D s t related (.inl 0) s.1.2.2.1 s.1.2.2.2

end Control

/-- Requests with a nontrivial scheduler or final-test computation. -/
def SchedulerRequest : (TailSpec C E).Domain → Prop
  | .inl (.inl _) => False
  | .inl (.inr .publicKey) => False
  | .inl (.inr (.sign (.corrupt _))) => False
  | _ => True

section Scheduler
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (k : Fin (lifetimeRuns attempts))

/-- The actual signing, start, round and final-test kernels, with the fixed retained-table relation.
Ordinary local calls, public-key reads and static corruption refusals are covered separately. -/
def SchedulerKernelCoupling : Prop :=
  ∀ (prims : Primitives) (keys : C.Party → Keys C) (h : C.Party)
    (q : (TailSpec C E).Domain), SchedulerRequest q →
    ∀ (s : Marked D E) (t : Physical C E),
    StateRelation attempts k D s t → ¬ Bad D s →
    RelTriple
      ((markedKernel K circuits settings attempts k D keys h prims q).run s)
      ((rawKernel K circuits settings attempts k D keys h prims false q).run t)
      (fun a b => Bad D a.2 ∨ (a.1 = b.1 ∧ StateRelation attempts k D a.2 b.2))

theorem kernelCoupling_of_scheduler
    (coupled : SchedulerKernelCoupling K circuits settings attempts D k) :
    KernelCoupling K circuits settings attempts D k := by
  intro prims keys h q s t related clean
  rcases q with (q | q) | forgery
  · exact local_coupling K circuits settings attempts D k keys h prims q s t related
  · cases q with
    | publicKey => exact publicKey_coupling K circuits settings attempts D k keys h prims s t related
    | sign q =>
      cases q with
      | corrupt i => exact corrupt_coupling K circuits settings attempts D k keys h prims i s t related
      | tree b => exact coupled prims keys h (.inl (.inr (.sign (.tree b)))) trivial s t related clean
      | round1 i J e message => exact coupled prims keys h (.inl (.inr (.sign (.round1 i J e message)))) trivial s t related clean
      | round2 i J e message parts => exact coupled prims keys h (.inl (.inr (.sign (.round2 i J e message parts)))) trivial s t related clean
    | start tree => exact coupled prims keys h (.inl (.inr (.start tree))) trivial s t related clean
    | round sent => exact coupled prims keys h (.inl (.inr (.round sent))) trivial s t related clean
  · exact coupled prims keys h (.inr forgery) trivial s t related clean

end Scheduler

section Final
variable [Field E] [Algebra Bit E]
variable (K : Constants C E) (settings : Settings) (attempts : ℕ)
variable (aes : Aes) (circuitsOf : (HashInput → HashOutput) → Circuits)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The unchanged slot transport, from fixed local scheduler couplings and actual U4 name counts. -/
theorem slotTransport_of_scheduler_overlap (Q : ℕ)
    (hcompute : ∀ Th, CircuitsCompute (circuitsOf Th) Th) (hshape : FixedShape circuitsOf)
    (hbatch : 0 < settings.batchSize) (hQ : HasLifetimeQueryBoundAll K settings attempts circuitsOf D A Q)
    (coupled : ∀ (values : MpcDomain → HashOutput) (k : Fin (lifetimeRuns attempts)),
      SchedulerKernelCoupling K (circuitsOf (thOf values)) settings attempts D k)
    (bounded : SelectedKeyOverlapBound K settings attempts aes circuitsOf D A Q) :
    SlotTransport K settings attempts aes circuitsOf D A Q :=
  slotTransport_of_kernel_overlap K settings attempts aes circuitsOf D A Q hcompute hshape hbatch hQ
    (fun values k => kernelCoupling_of_scheduler K _ settings attempts D k (coupled values k)) bounded

end Final

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotTransport.slotGame_eq_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slotGame_eq_generic

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotTransport.rawGame_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rawGame_output

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotTransport.markedGame_erase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms markedGame_erase

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotTransport.game_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms game_coupling

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotTransport.local_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms local_coupling

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotTransport.publicKey_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms publicKey_coupling

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotTransport.corrupt_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms corrupt_coupling

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotTransport.overlap_allowance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms overlap_allowance

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSlotTransport.slotTransport_of_scheduler_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms slotTransport_of_scheduler_overlap

end ThresholdLeanXmssSecurity.LifetimeSlotTransport
