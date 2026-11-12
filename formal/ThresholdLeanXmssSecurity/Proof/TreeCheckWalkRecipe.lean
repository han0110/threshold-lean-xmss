import ThresholdLeanXmssSecurity.Proof.TreeCheckWalkDef
import Mathlib.Data.List.GetD

/-!
# A fixed source walk through check boundaries

The first signing batch depends on the result of `treeLockstepPublicChoiceCode`.
That result is computed between two exchanges, in the same local pass as the
signing input queries. A cut at this point retains the result's type. Turning
it into a `Unit` gate before its queries have run would discard the dependency
of the signing jobs on the selected encoding.

`select` stops the ordered local pass at its first successful choice.
`select_split` retains all preceding aborts and resumes the selected party
before touching later parties. It is an equality in any lawful monad, including
the actual logged world with both caches.

The check adapter uses the GS20 coin and peer-reshare simulators and the original
adversary's rounds. Its visible PRSS rows use the checkpoint's cached AES keys.
The functionality supplies the hidden rows.

`decode` recognizes canonical audited callers by equality of one local pass
at the retained world. This equality includes the pending continuations, both
caches and the literal query log. `walkSplit` is unconditional: every failed
recognition executes the original scheduler step. `initial_decode_hit` and
`source_signing_decode_hit` establish recognition of concrete source branches.
The signing result uses common honest public-choice inputs; its successful
selection supplies the replay certificate in the actual final cache.

`family` fixes the walk and adapter once. `sourceConstruction_of_fields`
assembles the original source construction from this family's bad-index,
opening, position and hybrid clauses. Exact splitting, the setup-prefix log,
canonical contexts and prior-key provenance are already supplied by the
compiler. Batch coverage, tuple consistency, opening provenance, query
positions and the remaining hybrid conditions are separate source properties.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeCheckWalkRecipe

attribute [local instance] Classical.propDecidable inhabitedField

section Selection
variable {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}

/-- The first successful local choice, indexed by its position in party order. -/
inductive First (α : Type) : ℕ → Type
  | here {n : ℕ} (value : α) : First α (n + 1)
  | later {n : ℕ} (next : First α n) : First α (n + 1)

def First.value {n : ℕ} : First α n → α
  | .here a => a
  | .later next => next.value

/-- Only rejecting local prefixes precede the selected party. -/
def select : {n : ℕ} → (Fin n → m (Option α)) → m (Option (First α n))
  | 0, _ => pure none
  | n + 1, gate => do
      match ← gate 0 with
      | some value => pure (some (.here value))
      | none => Option.map First.later <$> select (fun i : Fin n => gate i.succ)

/-- A successful choice runs its original continuation; an absent choice aborts. -/
def localContinue (aborted : β) (gate : m (Option α)) (cont : α → m β) : m β := do
  match ← gate with
  | none => pure aborted
  | some value => cont value

/-- Resume the selected party first, then the untouched later local programs. -/
def remainder (aborted : β) : {n : ℕ} → (Fin n → m (Option α)) →
    (Fin n → α → m β) → Option (First α n) → m (Fin n → β)
  | _, _, _, none => pure (fun _ => aborted)
  | n + 1, gate, cont, some (.here value) => do
      let out ← cont 0 value
      let rest ← Concrete.sequenceFin fun i : Fin n =>
        localContinue aborted (gate i.succ) (cont i.succ)
      pure (Fin.cases out rest)
  | n + 1, gate, cont, some (.later next) => do
      let rest ← remainder aborted (fun i : Fin n => gate i.succ)
        (fun i => cont i.succ) (some next)
      pure (Fin.cases aborted rest)

/-- This factorization changes neither query order nor the ambient state. -/
theorem select_split (aborted : β) : ∀ {n : ℕ} (gate : Fin n → m (Option α))
    (cont : Fin n → α → m β),
    Concrete.sequenceFin (fun i => localContinue aborted (gate i) (cont i)) =
      select gate >>= remainder aborted gate cont
  | 0, gate, cont => by
      simp only [Concrete.sequenceFin, select, pure_bind, remainder]
      congr 1
      funext i
      exact i.elim0
  | n + 1, gate, cont => by
      simp only [Concrete.sequenceFin, localContinue, select, bind_assoc]
      apply bind_congr
      intro chosen
      cases chosen with
      | some value => simp only [pure_bind, remainder]; rfl
      | none =>
          simp only [pure_bind, bind_map_left]
          change (Concrete.sequenceFin (fun i : Fin n =>
              localContinue aborted (gate i.succ) (cont i.succ)) >>= fun (rest : Fin n → β) =>
                pure (fun i : Fin (n + 1) => Fin.cases (motive := fun _ => β) aborted rest i)) = _
          rw [select_split aborted (fun i : Fin n => gate i.succ) (fun i => cont i.succ)]
          simp only [bind_assoc]
          apply bind_congr
          intro selected
          cases selected with
          | none =>
              simp only [remainder, pure_bind, Option.map_none]
              congr 1
              funext i
              cases i using Fin.cases <;> rfl
          | some next => rfl

end Selection

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (D : C.Coalition)
variable (A : Adversary C E (Keys C) PEmpty PEmpty)

section PublicReplay

/-- The actual free public-hash handler, with its original log entry. -/
def publicImpl : QueryImpl HashSpec (StateT (TreeSimState C) ProbComp) :=
  fun q => treeSimLoggedWorld prims D (.inr (.inr (.inl (.hash q))))

theorem publicImpl_run (q : HashInput) (s : TreeSimState C) :
    (publicImpl prims D q).run s =
      (fun r : HashOutput × HashCache C =>
        (r.1, (r.2, s.1.2), s.2 ++ [⟨.inr (.inr (.inl (.hash q))), r.1⟩])) <$>
        (hashAnswer prims (.hash q)).run s.1.1 := by
  simp only [publicImpl, treeSimLoggedWorld, streamWorld, onHash, StateT.run_mk,
    localAnswer, QueryImpl.add_apply, Functor.map_map]
  rfl

/-- This is the source public computation, rather than an unlogged evaluator. -/
theorem publicRun_actual {α : Type} (p : OracleComp HashSpec α) :
    simulateQ (publicImpl prims D) p =
      simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (tweakable (C := C) p) (LocalSpec C))) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [tweakable]
  | query_bind q k ih =>
      simp only [tweakable, simulateQ_bind, simulateQ_spec_query, liftComp_bind,
        free_bind, ih]
      have single : simulateQ (treeSimLoggedWorld prims D)
          (free (liftComp (hashQuery (C := C) (.hash q)) (LocalSpec C))) =
            publicImpl prims D q := by
        unfold hashQuery
        erw [simulateQ_spec_query]
        rfl
      rw [single]

/-- A public replay path fixes only the answers that this computation reads.
Fixed `Th` queries need no random-oracle cache cell. -/
inductive CachedPublic (cache : HashCache C) {α : Type} :
    OracleComp HashSpec α → α → TreeSimLog C → Prop
  | pure (a : α) : CachedPublic cache (pure a) a []
  | query_bind (q : HashInput) (k : HashOutput → OracleComp HashSpec α)
      (u : HashOutput) (a : α) (trace : TreeSimLog C)
      (ready : (hashAnswer prims (.hash q)).run cache = pure (u, cache))
      (tail : CachedPublic cache (k u) a trace) :
      CachedPublic cache (OracleComp.lift (OracleSpec.query q) >>= k) a
        (⟨.inr (.inr (.inl (.hash q))), u⟩ :: trace)

theorem CachedPublic.run {cache : HashCache C} {α : Type}
    {p : OracleComp HashSpec α} {a : α} {trace : TreeSimLog C}
    (ready : CachedPublic prims cache p a trace) (hidden : HiddenCache C) (log : TreeSimLog C) :
    (simulateQ (publicImpl prims D) p).run ((cache, hidden), log) =
      Pure.pure (a, (cache, hidden), log ++ trace) := by
  induction ready generalizing log with
  | pure a => simp
  | query_bind q k u a trace head tail ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, publicImpl_run,
        head, map_pure, pure_bind]
      rw [ih]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- Any completed public computation supplies a replay certificate in its
actual final cache and in every extension of that cache. -/
theorem publicRun_replay {α : Type} (p : OracleComp HashSpec α)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (publicImpl prims D) p).run s)) :
    s.1.1 ≤ r.2.1.1 ∧ ∃ trace,
      r.2.2 = s.2 ++ trace ∧ ∀ cache, r.2.1.1 ≤ cache → CachedPublic prims cache p r.1 trace := by
  induction p using OracleComp.inductionOn generalizing s r with
  | pure a =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      subst r
      exact ⟨le_rfl, [], by simp, fun _ _ => .pure a⟩
  | query_bind q k ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, publicImpl_run,
        bind_map_left, mem_support_bind_iff] at run
      obtain ⟨u, hu, run⟩ := run
      obtain ⟨grows, trace, logs, replay⟩ := ih u.1 _ r run
      refine ⟨(grows_hashAnswer prims _ _ u hu).trans grows,
        ⟨.inr (.inr (.inl (.hash q))), u.1⟩ :: trace, ?_, ?_⟩
      · simpa only [List.append_assoc, List.singleton_append] using logs
      · intro cache hc
        refine .query_bind q k u.1 r.1 trace ?_ (replay cache hc)
        by_cases fixed : MpcInput q
        · rw [hashAnswer_of_isFixed prims fixed, StateT.run_pure, mem_support_pure_iff] at hu
          cases hu
          rw [hashAnswer_of_isFixed prims fixed, StateT.run_pure]
        · have random : ¬ IsFixed (Query.hash (C := C) q) := by
            rintro ⟨q', he, hm⟩
            cases he
            exact fixed hm
          exact hashAnswer_run_cached prims random
            (hc (grows (hashAnswer_cached prims random _ u hu)))

/-- Replaying the same public code changes no cache and emits its original
queries in their original positions after the supplied prefix. -/
theorem publicRun_repeat {α : Type} (p : OracleComp HashSpec α)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (run : r ∈ support ((simulateQ (publicImpl prims D) p).run s)) :
    ∃ trace, r.2.2 = s.2 ++ trace ∧
      ∀ (cache : HashCache C), r.2.1.1 ≤ cache →
        ∀ (hidden : HiddenCache C) (log : TreeSimLog C),
          (simulateQ (publicImpl prims D) p).run ((cache, hidden), log) =
            pure (r.1, (cache, hidden), log ++ trace) := by
  obtain ⟨_, trace, logs, replay⟩ := publicRun_replay prims D p s r run
  exact ⟨trace, logs, fun cache grows hidden log =>
    CachedPublic.run (prims := prims) (D := D) (replay cache grows) hidden log⟩

/-- A successful ordered selection ends exactly at one successful original
head. Its final world is that head's actual final world. -/
theorem select_some {α : Type} : ∀ {n : ℕ} (gate : Fin n → OracleComp (WorldSpec C) (Option α))
    (s : TreeSimState C) (chosen : First α n) (after : TreeSimState C),
    (some chosen, after) ∈ support ((simulateQ (treeSimLoggedWorld prims D) (select gate)).run s) →
    ∃ i before, (some chosen.value, after) ∈ support
      ((simulateQ (treeSimLoggedWorld prims D) (gate i)).run before)
  | 0, gate, s, chosen, after, run => by cases chosen
  | n + 1, gate, s, chosen, after, run => by
      simp only [select, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
      obtain ⟨out, ho, run⟩ := run
      cases accepted : out.1 with
      | some a =>
          simp only [accepted, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
          cases run
          exact ⟨0, s, by simpa only [First.value, ← accepted, Prod.mk.eta] using ho⟩
      | none =>
          simp only [accepted, simulateQ_map, StateT.run_map, support_map, Set.mem_image] at run
          obtain ⟨r, hr, he⟩ := run
          cases result : r.1 with
          | none => simp only [result, Option.map_none] at he; cases he
          | some next =>
              simp only [result, Option.map_some] at he
              cases he
              obtain ⟨i, before, hit⟩ := select_some (fun i : Fin n => gate i.succ) out.2 next r.2
                (by simpa only [← result] using hr)
              exact ⟨i.succ, before, hit⟩

end PublicReplay

section ActualSelection

variable {α β : Type}

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem localOption_advance (gate : OracleComp (LocalSpec C) (Option α))
    (cont : α → PartyM C E RealSpec β) :
    free (advance (treeLockstepLocalOption gate >>= cont).run) =
      localContinue (.done none) (free gate) (fun a => free (advance (cont a).run)) := by
  unfold treeLockstepLocalOption localContinue
  rw [bind_assoc, advance_localStep_bind, free_bind]
  apply bind_congr
  intro out
  cases out with
  | none => simp [advance_pure, free_pure]
  | some a => simp only [pure_bind]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The first successful local head is selected in the actual scheduler's
party order. The residual contains the original local `advance` computations. -/
theorem start_select (gate : C.Party → OracleComp (LocalSpec C) (Option α))
    (cont : C.Party → α → PartyM C E RealSpec β) :
    startSteps worldRoles D (fun i => treeLockstepLocalOption (gate i) >>= cont i) =
      select (fun i => if i ∈ D.1 then pure none else free (gate i)) >>=
        remainder (.done none) (fun i => if i ∈ D.1 then pure none else free (gate i))
          (fun i a => free (advance (cont i a).run)) := by
  rw [← select_split]
  unfold startSteps
  congr 1
  funext i
  by_cases corrupt : i ∈ D.1
  · simp [corrupt, localContinue]
  · simp only [if_neg corrupt, worldRoles]
    exact localOption_advance (gate i) (cont i)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The split is literal after the original logged handler; neither cache
nor the order of free public queries is quotiented away. -/
theorem start_select_logged (gate : C.Party → OracleComp (LocalSpec C) (Option α))
    (cont : C.Party → α → PartyM C E RealSpec β) (s : TreeSimState C) :
    (simulateQ (treeSimLoggedWorld prims D)
      (startSteps worldRoles D (fun i => treeLockstepLocalOption (gate i) >>= cont i))).run s =
      (simulateQ (treeSimLoggedWorld prims D)
        (select (fun i => if i ∈ D.1 then pure none else free (gate i)))).run s >>=
      fun selected => (simulateQ (treeSimLoggedWorld prims D)
        (remainder (.done none) (fun i => if i ∈ D.1 then pure none else free (gate i))
          (fun i a => free (advance (cont i a).run)) selected.1)).run selected.2 := by
  rw [start_select, simulateQ_bind, StateT.run_bind]

/-- Raw programs after the selected local head. Earlier parties have aborted,
the selected party starts its caller, and later heads remain untouched. -/
def remainingPrograms : {n : ℕ} → (Fin n → OracleComp (LocalSpec C) (Option α)) →
    (Fin n → α → PartyM C E RealSpec β) → Option (First α n) →
      Fin n → PartyM C E RealSpec β
  | _, _, _, none => fun _ => failure
  | n + 1, gate, cont, some (.here a) =>
      Fin.cases (cont 0 a) (fun i : Fin n => treeLockstepLocalOption (gate i.succ) >>= cont i.succ)
  | n + 1, gate, cont, some (.later next) =>
      Fin.cases failure (remainingPrograms (fun i : Fin n => gate i.succ)
        (fun i => cont i.succ) (some next))

def remainingGates : {n : ℕ} → (Fin n → OracleComp (LocalSpec C) (Option α)) →
    Option (First α n) → Fin n → OracleComp (LocalSpec C) (Option α)
  | _, _, none => fun _ => pure none
  | n + 1, gate, some (.here a) => Fin.cases (pure (some a)) (fun i : Fin n => gate i.succ)
  | n + 1, gate, some (.later next) =>
      Fin.cases (pure none) (remainingGates (fun i : Fin n => gate i.succ) (some next))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem localOption_pure_bind (out : Option α) (cont : α → PartyM C E RealSpec β) :
    (treeLockstepLocalOption (pure out) >>= cont) = out.elim failure cont := by
  apply OptionT.ext
  cases out <;> simp [treeLockstepLocalOption, localStep, OptionT.lift]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem remainingPrograms_typed : ∀ {n : ℕ} (gate : Fin n → OracleComp (LocalSpec C) (Option α))
    (cont : Fin n → α → PartyM C E RealSpec β) (chosen : Option (First α n)) (i : Fin n),
    remainingPrograms gate cont chosen i =
      treeLockstepLocalOption (remainingGates gate chosen i) >>= cont i
  | n, gate, cont, none, i => by simp [remainingPrograms, remainingGates, localOption_pure_bind]
  | n + 1, gate, cont, some (.here a), i => by
      cases i using Fin.cases <;> simp [remainingPrograms, remainingGates, localOption_pure_bind]
  | n + 1, gate, cont, some (.later next), i => by
      cases i using Fin.cases with
      | zero => simp [remainingPrograms, remainingGates, localOption_pure_bind]
      | succ i => exact remainingPrograms_typed _ _ (some next) i

theorem remainingGates_kind : ∀ {n : ℕ} (gate : Fin n → OracleComp (LocalSpec C) (Option α))
    (chosen : First α n) (i : Fin n),
    remainingGates gate (some chosen) i = pure none ∨
      remainingGates gate (some chosen) i = pure (some chosen.value) ∨
      remainingGates gate (some chosen) i = gate i
  | n + 1, gate, .here a, i => by
      cases i using Fin.cases
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  | n + 1, gate, .later next, i => by
      cases i using Fin.cases with
      | zero => exact Or.inl rfl
      | succ i => exact remainingGates_kind (fun i : Fin n => gate i.succ) next i

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem remainingPrograms_pass : ∀ {n : ℕ} (gate : Fin n → OracleComp (LocalSpec C) (Option α))
    (cont : Fin n → α → PartyM C E RealSpec β) (chosen : Option (First α n)),
    Concrete.sequenceFin (fun i => free (advance (remainingPrograms gate cont chosen i).run)) =
      remainder (.done none) (fun i => free (gate i)) (fun i a => free (advance (cont i a).run)) chosen
  | n, gate, cont, none => by
      simp [remainingPrograms, remainder, advance_pure, free_pure, sequenceFin_pure]
  | n + 1, gate, cont, some (.here a) => by
      simp only [remainingPrograms, Concrete.sequenceFin, Fin.cases_zero, Fin.cases_succ,
        remainder, localOption_advance]
  | n + 1, gate, cont, some (.later next) => by
      simp only [remainingPrograms, Concrete.sequenceFin, Fin.cases_zero, Fin.cases_succ,
        advance_run_failure, free_pure, pure_bind, remainder, remainingPrograms_pass]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem remainingPrograms_abort : ∀ {n : ℕ} (gate : Fin n → OracleComp (LocalSpec C) (Option α))
    (cont : Fin n → α → PartyM C E RealSpec β) (chosen : Option (First α n)) (i : Fin n),
    gate i = pure none → (∀ a, cont i a = failure) →
      remainingPrograms gate cont chosen i = failure
  | n, gate, cont, none, i, _, _ => by simp [remainingPrograms]
  | n + 1, gate, cont, some (.here a), i, hg, hc => by
      cases i using Fin.cases with
      | zero => exact hc a
      | succ i =>
          simp only [remainingPrograms, Fin.cases_succ, hg]
          apply OptionT.ext
          simp [treeLockstepLocalOption, localStep, OptionT.lift]
  | n + 1, gate, cont, some (.later next), i, hg, hc => by
      cases i using Fin.cases with
      | zero => rfl
      | succ i => exact remainingPrograms_abort _ _ (some next) i hg hc

def maskedGate (gate : C.Party → OracleComp (LocalSpec C) (Option α)) (i : C.Party) :
    OracleComp (LocalSpec C) (Option α) := if i ∈ D.1 then pure none else gate i

def maskedCont (cont : C.Party → α → PartyM C E RealSpec β) (i : C.Party) (a : α) :
    PartyM C E RealSpec β := if i ∈ D.1 then failure else cont i a

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem remainingPrograms_start (gate : C.Party → OracleComp (LocalSpec C) (Option α))
    (cont : C.Party → α → PartyM C E RealSpec β) (chosen : Option (First α C.n)) :
    startSteps worldRoles D (remainingPrograms (maskedGate D gate) (maskedCont D cont) chosen) =
      remainder (.done none) (fun i => free (maskedGate D gate i))
        (fun i a => free (advance (maskedCont D cont i a).run)) chosen := by
  rw [← remainingPrograms_pass]
  unfold startSteps
  congr 1
  funext i
  by_cases corrupt : i ∈ D.1
  · rw [if_pos corrupt, remainingPrograms_abort _ _ chosen i
      (by simp [maskedGate, corrupt]) (fun _ => by simp [maskedCont, corrupt])]
    simp [advance_pure, free_pure]
  · simp [corrupt, worldRoles]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem start_select_programs (gate : C.Party → OracleComp (LocalSpec C) (Option α))
    (cont : C.Party → α → PartyM C E RealSpec β) :
    startSteps worldRoles D (fun i => treeLockstepLocalOption (gate i) >>= cont i) =
      select (fun i => free (maskedGate D gate i)) >>= fun chosen =>
        startSteps worldRoles D (remainingPrograms (maskedGate D gate) (maskedCont D cont) chosen) := by
  simp_rw [remainingPrograms_start]
  rw [← select_split]
  unfold startSteps
  congr 1
  funext i
  by_cases corrupt : i ∈ D.1
  · simp [corrupt, maskedGate, localContinue, free_pure]
  · simp only [if_neg corrupt, worldRoles, maskedGate, maskedCont]
    exact localOption_advance (gate i) (cont i)

def selectPending (gate : C.Party → OracleComp (LocalSpec C) (Option α))
    (cont : C.Party → α → PartyM C E RealSpec (TreeCheckWalkDef.Output (C := C)))
    (p : TreeCheckWalkDef.Pending A) : ProbComp (TreeCheckWalkDef.Pending A) := do
  let selected ← (simulateQ (treeSimLoggedWorld prims D)
    (select fun i => free (maskedGate D gate i))).run p.world
  pure {p with
    program := remainingPrograms (maskedGate D gate) (maskedCont D cont) selected.1
    world := selected.2}

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Selecting a typed local head is an exact prefix of the same full run. -/
theorem selectPending_finish (Z : Distinguisher C A.State TreeOutput)
    (gate : C.Party → OracleComp (LocalSpec C) (Option α))
    (cont : C.Party → α → PartyM C E RealSpec (TreeCheckWalkDef.Output (C := C)))
    (p : TreeCheckWalkDef.Pending A)
    (source : ∀ i, i ∉ D.1 → p.program i = treeLockstepLocalOption (gate i) >>= cont i) :
    TreeCheckWalkDef.finish prims D Z p =
      selectPending prims D A gate cont p >>= TreeCheckWalkDef.finish prims D Z := by
  have start : startSteps worldRoles D p.program =
      startSteps worldRoles D (fun i => treeLockstepLocalOption (gate i) >>= cont i) := by
    unfold startSteps
    congr 1
    funext i
    by_cases hi : i ∈ D.1 <;> simp [hi, source i]
  unfold TreeCheckWalkDef.finish executePhase selectPending
  rw [start, start_select_programs]
  simp only [simulateQ_bind, StateT.run_bind, bind_assoc, pure_bind]

abbrev PublicChoice := Digest × Randomness × Encoding

attribute [local irreducible] treeLockstepPublicChoiceCode

/-- The actual successful public choice after a pending opening tail. -/
def signingHead (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) (gate : OracleComp (LocalSpec C) (Option Unit)) :
    OracleComp (LocalSpec C) (Option PublicChoice) := do
  match ← gate with
  | none => pure none
  | some _ => liftComp (tweakable (C := C) (treeLockstepPublicChoiceCode parameter b outputs)) (LocalSpec C)

/-- The original audited signing caller, including both batches' records. -/
def signingCont (circuits : Circuits) (settings : Settings) (ctx : Context C)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit))
    (records : List (TreeSimCheckBatchRecord C)) (initial : ℕ × ℕ)
    (choice : PublicChoice) : PartyM C E RealSpec (TreeCheckWalkDef.Output (C := C)) := do
  let result ← (batched settings.batchSize (treeSimCheckBatchAudit K circuits settings ctx)
    (signJobs b choice.2.2)).run.run initial
  treeLockstepBottomFinish ctx.keys.parameter top b outputs choice.1 choice.2.1 result.1.1
    (records ++ result.1.2)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem localOption_oracle_bind (gate : OracleComp (LocalSpec C) (Option Unit))
    (code : OracleComp (RoSpec C) (Option α)) (cont : α → PartyM C E RealSpec β) :
    (treeLockstepLocalPrelude gate >>= fun _ => oracleStep code >>= fun a =>
      match a with | none => failure | some a => cont a) =
    (treeLockstepLocalOption (do match ← gate with
      | none => pure none
      | some _ => liftComp code (LocalSpec C)) >>= cont) := by
  apply OptionT.ext
  unfold treeLockstepLocalPrelude treeLockstepLocalOption
  simp only [localStep, oracleStep, OptionT.run_bind, OptionT.lift, OptionT.run_mk,
    liftComp_bind, bind_assoc, pure_bind, Option.elimM]
  apply bind_congr
  intro accepted
  cases accepted with
  | none => simp [liftComp_pure]
  | some u =>
      simp only [Option.elim, OptionT.run_pure, pure_bind]
      apply bind_congr
      intro choice
      cases choice <;> simp [OptionT.run_pure, pure_bind]

omit [Fintype E] [DecidableEq E] in
/-- The typed head is exactly the source transition to signing. Its encoding
is passed to the batch caller rather than replaced by a fixed value. -/
theorem signingHead_program (circuits : Circuits) (settings : Settings) (ctx : Context C)
    (top : TopTree) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit))
    (records : List (TreeSimCheckBatchRecord C)) (initial : ℕ × ℕ)
    (gate : OracleComp (LocalSpec C) (Option Unit)) :
    (treeLockstepLocalPrelude gate >>= fun _ =>
      treeLockstepFirstRest K circuits settings ctx top (.bottom b) ((some outputs, records), initial)) =
      (treeLockstepLocalOption (signingHead ctx.keys.parameter b outputs gate) >>=
        signingCont K circuits settings ctx top b outputs records initial) := by
  have split := localOption_oracle_bind gate
    (tweakable (treeLockstepPublicChoiceCode ctx.keys.parameter b outputs))
    (signingCont K circuits settings ctx top b outputs records initial)
  convert split using 1
  · apply bind_congr
    intro _
    dsimp only [treeLockstepFirstRest]
    apply bind_congr
    intro choice
    rcases choice with _ | ⟨root, randomness, enc⟩ <;> rfl
  · rfl

/-- Once the same public-choice input has run, a later occurrence repeats
its result and log in every extension of the actual hash cache. -/
theorem signingChoice_repeat (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) (s : TreeSimState C)
    (r : Option PublicChoice × TreeSimState C)
    (run : r ∈ support ((simulateQ (publicImpl prims D)
      (treeLockstepPublicChoiceCode parameter b outputs)).run s)) :
    ∃ trace, r.2.2 = s.2 ++ trace ∧
      ∀ (cache : HashCache C), r.2.1.1 ≤ cache →
        ∀ (hidden : HiddenCache C) (log : TreeSimLog C),
          (simulateQ (treeSimLoggedWorld prims D)
            (free (liftComp (tweakable (C := C)
              (treeLockstepPublicChoiceCode parameter b outputs)) (LocalSpec C)))).run
                ((cache, hidden), log) = pure (r.1, (cache, hidden), log ++ trace) := by
  obtain ⟨trace, logs, again⟩ := publicRun_repeat (α := Option PublicChoice) prims D
    (treeLockstepPublicChoiceCode parameter b outputs) s r run
  refine ⟨trace, logs, ?_⟩
  intro cache grows hidden log
  rw [← publicRun_actual]
  exact again cache grows hidden log

theorem signingHead_fixed (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) (gate : OracleComp (LocalSpec C) (Option Unit))
    (base : HashCache C) (choice : PublicChoice)
    (ready : ∀ cache, base ≤ cache → ∃ trace,
      CachedPublic prims cache (treeLockstepPublicChoiceCode parameter b outputs) (some choice) trace)
    (s : TreeSimState C) (grows : base ≤ s.1.1) (r : Option PublicChoice × TreeSimState C)
    (run : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (signingHead parameter b outputs gate))).run s)) : r.1 = none ∨ r.1 = some choice := by
  unfold signingHead at run
  simp only [free_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨first, hf, run⟩ := run
  have growth := grows.trans (treeSim_logged_grows prims D (free gate) s first hf)
  cases accepted : first.1 with
  | none =>
      simp only [accepted, free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      cases run
      exact Or.inl rfl
  | some u =>
      simp only [accepted] at run
      obtain ⟨trace, cached⟩ := ready first.2.1.1 growth
      rw [← publicRun_actual, CachedPublic.run (prims := prims) (D := D) cached
        first.2.1.2 first.2.2] at run
      simp only [mem_support_pure_iff] at run
      cases run
      exact Or.inr rfl

theorem signingHead_public (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) (gate : OracleComp (LocalSpec C) (Option Unit))
    (s after : TreeSimState C) (choice : PublicChoice)
    (run : (some choice, after) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (signingHead parameter b outputs gate))).run s)) :
    ∃ before, (some choice, after) ∈ support ((simulateQ (publicImpl prims D)
      (treeLockstepPublicChoiceCode parameter b outputs)).run before) := by
  unfold signingHead at run
  simp only [free_bind, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at run
  obtain ⟨first, _, run⟩ := run
  cases accepted : first.1 with
  | none =>
      simp only [accepted, free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      cases run
  | some u =>
      simp only [accepted] at run
      exact ⟨first.2, by simpa only [publicRun_actual] using run⟩

/-- If the public-choice inputs agree, the selector itself establishes the
stable replay certificate in its actual final cache. No eager cache is used. -/
theorem selected_signing_replay (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (s after : TreeSimState C) (chosen : First PublicChoice C.n)
    (run : (some chosen, after) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (select fun i => free (maskedGate D
        (fun i => signingHead parameter b outputs (gate i)) i))).run s)) :
    ∃ trace, ∀ cache, after.1.1 ≤ cache →
      CachedPublic prims cache (treeLockstepPublicChoiceCode parameter b outputs) (some chosen.value) trace := by
  obtain ⟨i, before, hit⟩ := select_some prims D _ s chosen after run
  by_cases hi : i ∈ D.1
  · simp only [maskedGate, if_pos hi, free_pure, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at hit
    cases hit
  · simp only [maskedGate, if_neg hi] at hit
    obtain ⟨before, hp⟩ := signingHead_public prims D parameter b outputs (gate i) before after chosen.value hit
    obtain ⟨_, trace, _, ready⟩ := publicRun_replay prims D
      (treeLockstepPublicChoiceCode parameter b outputs) before (some chosen.value, after) hp
    exact ⟨trace, ready⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem localOption_ignore (gate : OracleComp (LocalSpec C) (Option α))
    (cont : PartyM C E RealSpec β) :
    (treeLockstepLocalOption gate >>= fun _ => cont) =
      (treeLockstepLocalPrelude (Option.map (fun _ => ()) <$> gate) >>= fun _ => cont) := by
  apply OptionT.ext
  unfold treeLockstepLocalOption treeLockstepLocalPrelude
  simp only [localStep, OptionT.run_bind, OptionT.lift, OptionT.run_mk, liftComp_map,
    bind_map_left, bind_assoc, pure_bind, Option.elimM]
  apply bind_congr
  intro out
  cases out <;> rfl

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- Fix only the value carried into the caller. The local head still executes
at the same position and retains every query, abort, cache update and log entry. -/
theorem localOption_fixed (gate : OracleComp (LocalSpec C) (Option α))
    (cont : α → PartyM C E RealSpec β) (value : α) (s : TreeSimState C)
    (fixed : ∀ r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free gate)).run s),
      ∀ a, r.1 = some a → a = value) :
    (simulateQ (treeSimLoggedWorld prims D)
      (free (advance (treeLockstepLocalOption gate >>= cont).run))).run s =
    (simulateQ (treeSimLoggedWorld prims D)
      (free (advance (treeLockstepLocalPrelude (Option.map (fun _ => ()) <$> gate) >>=
        fun _ => cont value).run))).run s := by
  rw [← localOption_ignore, localOption_advance, localOption_advance]
  simp only [localContinue, simulateQ_bind, StateT.run_bind]
  apply bind_congr_of_forall_mem_support
  intro r hr
  cases h : r.1 with
  | none => rfl
  | some a => rw [fixed r hr a h]

/-- Pointwise local-pass equalities at every extension of a retained cache
compose in scheduler order without commuting any queries. -/
theorem localPass_congr {β : Type} (base : HashCache C) :
    ∀ {n : ℕ} (left right : Fin n → OracleComp (WorldSpec C) β)
      (_same : ∀ i s, base ≤ s.1.1 →
        (simulateQ (treeSimLoggedWorld prims D) (left i)).run s =
          (simulateQ (treeSimLoggedWorld prims D) (right i)).run s)
      (s : TreeSimState C), base ≤ s.1.1 →
      (simulateQ (treeSimLoggedWorld prims D) (Concrete.sequenceFin left)).run s =
        (simulateQ (treeSimLoggedWorld prims D) (Concrete.sequenceFin right)).run s
  | 0, left, right, same, s, grows => rfl
  | n + 1, left, right, same, s, grows => by
      simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
      rw [same 0 s grows]
      apply bind_congr_of_forall_mem_support
      intro r hr
      rw [localPass_congr base (fun i : Fin n => left i.succ) (fun i => right i.succ)
        (fun i => same i.succ) r.2
        (grows.trans (treeSim_logged_grows prims D (right 0) s r hr))]

end ActualSelection

/-- The visible term key is read from an honest holder. A visible pair uses
its honest endpoint; the all-corrupt case is unused by `Frand`. -/
def streamKey (prss : C.Party → PrssKeys C) : KeyName C → HashOutput
  | .term T => (prss (refHolder D T)).term T
  | .pair p => if p.1.1 ∉ D.1 then (prss p.1.1).pair p.1.2 else (prss p.1.2).pair p.1.1
  | .parameter => 0

/-- The source cache is read purely; this does not issue a counted query. -/
def fieldRow (prss : C.Party → PrssKeys C) (cache : HashCache C)
    (label idx count : ℕ) (name : KeyName C) : ℕ → E :=
  treeSimElementBlock K count fun g =>
    prims.aes.eval (truncateHash ((cache (.streamKey (streamKey D prss name))).getD 0))
      (label, idx, g)

def bitRow (prss : C.Party → PrssKeys C) (cache : HashCache C)
    (label idx count : ℕ) (name : KeyName C) : ℕ → Bit := fun g =>
  ((List.range count).map fun k =>
    prims.aes.eval (truncateHash ((cache (.streamKey (streamKey D prss name))).getD 0))
      (label, idx, k)).getD g 0

/-- `Frand` reads only known terms and pairs with a corrupt endpoint. -/
def knownRows {R : Type} [Zero R] (row : KeyName C → ℕ → R) :
    Shares C R × (C.Party → C.Party → ℕ → R) :=
  (fun T => if KnownTo D.1 T then row (.term T) else fun _ => 0,
    fun j i => if h : i = j then fun _ => 0 else
      if j ∈ D.1 then row (.pair (C.pairOf i j h)) else fun _ => 0)

/-- The original adversary and one PRSS label supply the standard gadget
simulators. Its `answer` consists only of cached-key evaluation. -/
def randomAdversary (x : C.Party → Keys C) (prss : C.Party → PrssKeys C)
    (cache : HashCache C) (label idx count : ℕ) :
    Adversary C E ℕ Unit (Shares C E × (C.Party → C.Party → ℕ → E)) where
  State := A.State
  start := fun _ z => A.start (corruptInputs D x) z
  round := A.round
  answer := fun state _ => pure (state, knownRows D (fieldRow prims K D prss cache label idx count))

local instance : SampleableType E := SampleableType.ofFintype E

/-- The real adversary's state and the next PRSS label. The count of an
extend call in `checkM` is two; its final bit draw has width 256. -/
def checkAdversary (x : C.Party → Keys C) (prss : C.Party → PrssKeys C)
    (cache : HashCache C) (initialLabel : ℕ) : CheckAdversary C E (List (Tuple C)) where
  State := A.State × ℕ
  start := fun _ z => (fun state => (state, initialLabel)) <$> A.start (corruptInputs D x) z
  round := fun state view => (fun reply => ((reply.1, state.2), reply.2)) <$> A.round state.1 view
  answer := fun state input => match input with
    | .inl (.inl values) => do
        let reply ← coinSimAnswer K D
          (randomAdversary prims K D A x prss cache state.2 1 values.length)
          values.length values state.1
        pure ((reply.1, state.2 + 1), .inl (.inl reply.2))
    | .inl (.inr _) => do
        let reply ← peerSimAnswer K D
          (randomAdversary prims K D A x prss cache state.2 0 2)
          (elementCodec K) 2 state.1
        pure ((reply.1, state.2 + 1), .inl (.inr reply.2))
    | .inr (.inl _) =>
        pure ((state.1, state.2 + 1), .inr (.inl
          (knownRows D (fieldRow prims K D prss cache state.2 1 2))))
    | .inr (.inr _) =>
        pure ((state.1, state.2 + 1), .inr (.inr
          (knownRows D (bitRow prims D prss cache state.2 2 256))))

/-- All keys used by an earlier cached coin, with no choice of an error set. -/
def priorKeys (label : ℕ) (cache : HashCache C) : Finset HashOutput :=
  Finset.univ.filter fun key => ∃ tag previous bits,
    previous < label ∧ cache (.coinKey tag previous bits) = some key

theorem priorKeys_prior (label : ℕ) (cache : HashCache C) :
    TreeSimCheckPriorKeys label cache (priorKeys label cache) := by
  intro key hk
  exact (Finset.mem_filter.mp hk).2

section Compiler

set_option maxRecDepth 2000

open TreeCheckWalkDef

variable (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
variable (x : C.Party → Keys C) (setup : C.Party → Option (PrssKeys C)) (j : ℕ)

/-- Missing setup rows stay behind rejecting tails; present rows retain their keys. -/
def setupKeys (setup : C.Party → Option (PrssKeys C)) (i : C.Party) : PrssKeys C :=
  (setup i).getD ⟨fun _ => 0, fun _ => 0⟩

theorem setupKeys_some (setup : C.Party → Option (PrssKeys C)) (i : C.Party)
    (keys : PrssKeys C) (present : setup i = some keys) : setupKeys setup i = keys := by
  simp only [setupKeys, present, Option.getD_some]

def firstChunks (settings : Settings) (tree : Tree) : List (List Job) :=
  chunks settings.batchSize (treeLockstepFirstJobs tree)

/-- Data saved by the actual batched caller. It contains no arbitrary
continuation: the remaining audited batches and final verification are fixed. -/
structure Caller (C : Committee) where
  encoding : Encoding
  firstOutputs : C.Party → List (List Bit)
  root : C.Party → Digest
  randomness : C.Party → Randomness
  outputs : C.Party → List (Option (List (List Bit)))
  records : C.Party → List (TreeSimCheckBatchRecord C)
  tail : C.Party → OracleComp (LocalSpec C) (Option Unit)

def phaseChunks (caller : Caller C) : List (List Job) :=
  if j < (firstChunks settings tree).length then firstChunks settings tree else
    match tree with
    | .top => []
    | .bottom b => chunks settings.batchSize (signJobs b caller.encoding)

def phaseIndex : ℕ :=
  if j < (firstChunks settings tree).length then j else j - (firstChunks settings tree).length

def callerCont (caller : Caller C) (i : C.Party)
    (a : (Option (List (List Bit)) × List (TreeSimCheckBatchRecord C)) × (ℕ × ℕ)) :
    PartyM C E RealSpec (Output (C := C)) := do
  let rest ← (((phaseChunks settings tree j caller).drop (phaseIndex settings tree j + 1)).mapM
    (treeSimCheckBatchAudit K circuits settings ⟨i, x i, setupKeys setup i⟩)).run.run a.2
  let values := (caller.outputs i ++ a.1.1 :: rest.1.1).foldlM
    (fun acc batch => batch.map (acc ++ ·)) []
  let records := caller.records i ++ a.1.2 ++ rest.1.2
  if j < (firstChunks settings tree).length then
    treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys setup i⟩ top tree
      ((values, records), rest.2)
  else
    match tree with
    | .top =>
        treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys setup i⟩ top tree
          ((values, records), rest.2)
    | .bottom b =>
        treeLockstepBottomFinish (x i).parameter top b (caller.firstOutputs i)
          (caller.root i) (caller.randomness i) values records

def callerBatch (caller : Caller C) : Batch A where
  prss := setupKeys setup
  jobs := (lockstepChunks settings caller.encoding tree).getD j []
  counters := (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
    (lockstepChunks settings caller.encoding tree) j, j)
  tail := caller.tail
  cont := callerCont K circuits settings top tree x setup j caller

/-- The saved records precede exactly batch `j`, and the saved output list
precedes its position inside the current batched call. -/
def CallerLengths (caller : Caller C) : Prop :=
  ∀ i, i ∉ D.1 → (caller.records i).length = j ∧
    (caller.outputs i).length = phaseIndex settings tree j

/-- Recognition compares one local pass in the actual retained world. It
keeps all steps, their continuations, both caches and the literal query log. -/
def Fits (p : Pending A) (caller : Caller C) : Prop :=
  CallerLengths D settings tree j caller ∧
  let b := boundary D K circuits settings x
    (p, callerBatch K D A circuits settings top tree x setup j caller)
  b.batch.rounds circuits settings ≤ p.fuel ∧
    (simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D p.program)).run p.world =
      (simulateQ (treeSimLoggedWorld prims D)
        (startSteps worldRoles D (b.program K circuits settings))).run p.world

/-- Exact recognition of canonical source callers; a failed recognition
leaves the original pending programs for the next scheduler step. -/
def decode (p : Pending A) : Option (Caller C) :=
  if found : ∃ caller, Fits prims K D A circuits settings top tree x setup j p caller then
    some (Classical.choose found) else none

omit [Fintype E] [DecidableEq E] in
theorem decode_sound (c : Decoded (decode prims K D A circuits settings top tree x setup j)) :
    Fits prims K D A circuits settings top tree x setup j c.1.1 c.1.2 := by
  have found := c.2
  unfold decode at found
  split_ifs at found with h
  · rw [← Option.some.inj found]
    exact Classical.choose_spec h

omit [Fintype E] [DecidableEq E] in
theorem decode_hit (p : Pending A) (caller : Caller C)
    (fits : Fits prims K D A circuits settings top tree x setup j p caller) :
    (decode prims K D A circuits settings top tree x setup j p).isSome := by
  have found : ∃ caller, Fits prims K D A circuits settings top tree x setup j p caller := ⟨caller, fits⟩
  simp only [decode, dif_pos found, Option.isSome_some]

omit [Fintype E] [DecidableEq E] in
/-- A single local-pass identity gives the full exact continuation identity. -/
theorem fits_finish (Z : Distinguisher C A.State TreeOutput) (p : Pending A) (caller : Caller C)
    (fits : Fits prims K D A circuits settings top tree x setup j p caller) :
    finish prims D Z p =
      (boundary D K circuits settings x
        (p, callerBatch K D A circuits settings top tree x setup j caller)).run
          prims K circuits settings D Z := by
  obtain ⟨_, room, same⟩ := fits
  unfold finish TreeCheckTailBoundary.run executePhase
  simp only [simulateQ_bind, StateT.run_bind]
  rw [same]
  have fuel : (boundary D K circuits settings x
      (p, callerBatch K D A circuits settings top tree x setup j caller)).batch.rounds circuits settings +
      (boundary D K circuits settings x
        (p, callerBatch K D A circuits settings top tree x setup j caller)).batch.fuel = p.fuel :=
    Nat.add_sub_of_le room
  rw [fuel]
  rfl

/-- The source data at the transition from the first bottom run to signing. -/
structure SigningPoint (C : Committee) where
  outputs : C.Party → List (List Bit)
  records : C.Party → List (TreeSimCheckBatchRecord C)
  tail : C.Party → OracleComp (LocalSpec C) (Option Unit)

def signingInitial : ℕ × ℕ :=
  (lockstepStart circuits (x (refHolder D K.publicTerm)).parameter
    (firstChunks settings tree) (firstChunks settings tree).length,
    (firstChunks settings tree).length)

def SigningMatches (b : Fin (2 ^ layerHeight)) (p : Pending A) (point : SigningPoint C) : Prop :=
  (∀ i, i ∉ D.1 → (point.records i).length = j) ∧
  ∀ i, i ∉ D.1 → p.program i = treeLockstepLocalPrelude (point.tail i) >>= fun _ =>
    treeLockstepFirstRest K circuits settings ⟨i, x i, setupKeys setup i⟩ top (.bottom b)
      ((some (point.outputs i), point.records i), signingInitial K D circuits settings (.bottom b) x)

def prepare (p : Pending A) : ProbComp (Pending A) :=
  match tree with
  | .top => pure p
  | .bottom b =>
      if j = (firstChunks settings (.bottom b)).length then
        if found : ∃ point, SigningMatches K D A circuits settings top x setup j b p point then
          let point := Classical.choose found
          selectPending prims D A
            (fun i => signingHead (x i).parameter b (point.outputs i) (point.tail i))
            (fun i => signingCont K circuits settings ⟨i, x i, setupKeys setup i⟩ top b
              (point.outputs i) (point.records i) (signingInitial K D circuits settings (.bottom b) x)) p
        else pure p
      else pure p

omit [Fintype E] [DecidableEq E] in
theorem prepare_finish (Z : Distinguisher C A.State TreeOutput) (p : Pending A) :
    finish prims D Z p =
      prepare prims K D A circuits settings top tree x setup j p >>= finish prims D Z := by
  unfold prepare
  cases tree with
  | top => simp
  | bottom b =>
      dsimp only
      split_ifs with first found
      · apply selectPending_finish
        intro i hi
        rw [(Classical.choose_spec found).2 i hi, signingHead_program]
      · simp
      · simp

omit [Fintype E] [DecidableEq E] in
theorem prepare_fuel_prefix (p prepared : Pending A)
    (run : prepared ∈ support (prepare prims K D A circuits settings top tree x setup j p)) :
    prepared.fuel = p.fuel ∧ p.world.2 <+: prepared.world.2 := by
  unfold prepare at run
  cases tree with
  | top =>
      simp only [mem_support_pure_iff] at run
      subst prepared
      exact ⟨rfl, List.prefix_refl _⟩
  | bottom b =>
      dsimp only at run
      split_ifs at run with first found
      · unfold selectPending at run
        simp only [mem_support_bind_iff, mem_support_pure_iff] at run
        obtain ⟨selected, hs, rfl⟩ := run
        exact ⟨rfl, treeSimLoggedWorld_prefix prims D _ p.world selected hs⟩
      · simp only [mem_support_pure_iff] at run
        subst prepared
        exact ⟨rfl, List.prefix_refl _⟩
      · simp only [mem_support_pure_iff] at run
        subst prepared
        exact ⟨rfl, List.prefix_refl _⟩

/-- The actual first caller has empty writer/output prefixes and precisely
the setup aborts. Its encoding field is unused by the first phase. -/
def firstCaller (setup : C.Party → Option (PrssKeys C)) : Caller C where
  encoding := fun _ => digit 0
  firstOutputs := fun _ => []
  root := fun _ => 0
  randomness := fun _ => 0
  outputs := fun _ => []
  records := fun _ => []
  tail := fun i => pure ((setup i).map fun _ => ())

omit [Fintype E] [DecidableEq E] in
theorem auditChunks_cons (ctx : Context C) (head : List Job) (rest : List (List Job))
    (initial : ℕ × ℕ) :
    (((head :: rest).mapM (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx)).run.run initial) =
      (do
        let a ← (treeSimCheckBatchAudit K circuits settings ctx head).run.run initial
        let b ← (rest.mapM (treeSimCheckBatchAudit K circuits settings ctx)).run.run a.2
        pure ((a.1.1 :: b.1.1, a.1.2 ++ b.1.2), b.2)) := by
  simp [List.mapM_cons, WriterT.run_bind, StateT.run_bind]

omit [Fintype E] [DecidableEq E] in
theorem auditBatched_run (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    (batched settings.batchSize (treeSimCheckBatchAudit (G := RealSpec) K circuits settings ctx) jobs).run.run initial =
      (do
        let a ← ((chunks settings.batchSize jobs).mapM
          (treeSimCheckBatchAudit K circuits settings ctx)).run.run initial
        pure ((a.1.1.foldlM (fun acc batch => batch.map (acc ++ ·)) [], a.1.2), a.2)) := by
  simp [batched]

theorem firstChunk (encoding : Encoding) (head : List Job) (rest : List (List Job))
    (chunks : firstChunks settings tree = head :: rest) :
    (lockstepChunks settings encoding tree).getD 0 [] = head := by
  cases tree with
  | top => simpa only [firstChunks, treeLockstepFirstJobs, lockstepChunks, List.getD_cons_zero] using
      congrArg (fun xs : List (List Job) => xs.getD 0 []) chunks
  | bottom b =>
      unfold firstChunks treeLockstepFirstJobs at chunks
      simp only [lockstepChunks, chunks, List.cons_append, List.getD_cons_zero]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem localPrelude_some : treeLockstepLocalPrelude (C := C) (E := E) (pure (some ())) = pure () := by
  apply OptionT.ext
  simp [treeLockstepLocalPrelude, localStep, OptionT.lift]

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem localPrelude_none : treeLockstepLocalPrelude (C := C) (E := E) (pure none) = failure := by
  apply OptionT.ext
  simp [treeLockstepLocalPrelude, localStep, OptionT.lift]

theorem initial_program (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (head : List Job) (rest : List (List Job)) (chunks : firstChunks settings tree = head :: rest)
    (i : C.Party) :
    (initial K circuits settings top tree x p).program i =
      (boundary D K circuits settings x (initial K circuits settings top tree x p,
        callerBatch K D A circuits settings top tree x p.1.2 0 (firstCaller p.1.2))).program
          K circuits settings i := by
  have positive : 0 < (firstChunks settings tree).length := by rw [chunks]; simp
  simp only [initial, boundary, TreeCheckTailBoundary.program, callerBatch, firstCaller,
    lockstepStart, List.take_zero, List.map_nil, List.sum_nil]
  rw [firstChunk settings tree (fun _ => digit 0) head rest chunks]
  cases row : p.1.2 i with
  | none => simp only [Option.elim_none, Option.map_none, localPrelude_none, failure_bind]
  | some keys =>
      simp only [row, Option.elim_some, Option.map_some, localPrelude_some, pure_bind,
        setupKeys, Option.getD_some]
      rw [treeLockstep_afterSetup_first, auditBatched_run]
      change ThresholdLeanXmss.chunks settings.batchSize (treeLockstepFirstJobs tree) = head :: rest at chunks
      rw [chunks, auditChunks_cons]
      simp only [bind_assoc, pure_bind]
      apply bind_congr
      intro a
      unfold callerCont
      simp [phaseChunks, phaseIndex, show firstChunks settings tree = head :: rest from chunks,
        setupKeys, row]

/-- The actual after-setup program is recognized whenever its first chunk
fits the remaining round allowance. No program-equality premise is supplied. -/
theorem initial_decode_hit
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (head : List Job) (rest : List (List Job)) (chunks : firstChunks settings tree = head :: rest)
    (room : depth (head.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) *
      settings.mode.rounds + 1 ≤ (initial K circuits settings top tree x p).fuel) :
    (decode prims K D A circuits settings top tree x p.1.2 0
      (initial K circuits settings top tree x p)).isSome := by
  apply decode_hit prims K D A circuits settings top tree x p.1.2 0 _ (firstCaller p.1.2)
  have positive : 0 < (firstChunks settings tree).length := by rw [chunks]; simp
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    simp [firstCaller, phaseIndex, positive]
  · simpa only [boundary, callerBatch, TreeCheckBatchBoundary.rounds,
      firstChunk settings tree (firstCaller p.1.2).encoding head rest chunks] using room
  · congr 1
    congr 1
    unfold startSteps
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi]
    · simp only [if_neg hi, initial_program K D A circuits settings top tree x p head rest chunks i]

/-- The signing caller after its public choice, retaining the entire first
run's audit records. The typed residual head remains in each party's tail. -/
def signingCaller (outputs : C.Party → List (List Bit))
    (records : C.Party → List (TreeSimCheckBatchRecord C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option PublicChoice)) (choice : PublicChoice) : Caller C where
  encoding := choice.2.2
  firstOutputs := outputs
  root := fun _ => choice.1
  randomness := fun _ => choice.2.1
  outputs := fun _ => []
  records := records
  tail := fun i => Option.map (fun _ => ()) <$> gate i

theorem signing_firstChunk (b : Fin (2 ^ layerHeight)) (encoding : Encoding)
    (head : List Job) (rest : List (List Job))
    (hchunks : chunks settings.batchSize (signJobs b encoding) = head :: rest) :
    (lockstepChunks settings encoding (.bottom b)).getD
      (firstChunks settings (.bottom b)).length [] = head := by
  change ((firstChunks settings (.bottom b)) ++ chunks settings.batchSize (signJobs b encoding)).getD
    (firstChunks settings (.bottom b)).length [] = head
  rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, hchunks, List.getD_cons_zero]

theorem signing_start (b : Fin (2 ^ layerHeight)) (encoding : Encoding) (parameter : PublicParameter) :
    lockstepStart circuits parameter (lockstepChunks settings encoding (.bottom b))
      (firstChunks settings (.bottom b)).length =
    lockstepStart circuits parameter (firstChunks settings (.bottom b))
      (firstChunks settings (.bottom b)).length := by
  unfold lockstepStart
  change (((firstChunks settings (.bottom b) ++ chunks settings.batchSize (signJobs b encoding)).take
      (firstChunks settings (.bottom b)).length).map (batchLabels circuits parameter)).sum = _
  rw [List.take_left, List.take_length]

omit [Fintype E] [DecidableEq E] in
theorem signingCont_head (b : Fin (2 ^ layerHeight))
    (outputs : C.Party → List (List Bit)) (records : C.Party → List (TreeSimCheckBatchRecord C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option PublicChoice)) (choice : PublicChoice)
    (head : List Job) (rest : List (List Job))
    (hchunks : chunks settings.batchSize (signJobs b choice.2.2) = head :: rest) (i : C.Party) :
    signingCont K circuits settings ⟨i, x i, setupKeys setup i⟩ top b (outputs i) (records i)
      (signingInitial K D circuits settings (.bottom b) x) choice =
      ((treeSimCheckBatchAudit K circuits settings ⟨i, x i, setupKeys setup i⟩ head).run.run
        (signingInitial K D circuits settings (.bottom b) x) >>=
          callerCont K circuits settings top (.bottom b) x setup
            (firstChunks settings (.bottom b)).length (signingCaller outputs records gate choice) i) := by
  unfold signingCont
  rw [auditBatched_run, hchunks, auditChunks_cons]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro a
  simp [callerCont, phaseChunks, phaseIndex, signingCaller, hchunks, List.append_assoc]

omit [Fintype E] [DecidableEq E] in
/-- A source signing head with a fixed cached choice is accepted by the
concrete semantic decoder. The certificate ranges only over its local heads,
and supplies no whole-execution equality or later bad-event premise. -/
theorem signing_decode_hit (b : Fin (2 ^ layerHeight)) (p : Pending A)
    (outputs : C.Party → List (List Bit)) (records : C.Party → List (TreeSimCheckBatchRecord C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option PublicChoice)) (choice : PublicChoice)
    (head : List Job) (rest : List (List Job))
    (hchunks : chunks settings.batchSize (signJobs b choice.2.2) = head :: rest)
    (lengths : ∀ i, i ∉ D.1 → (records i).length = (firstChunks settings (.bottom b)).length)
    (source : ∀ i, i ∉ D.1 → p.program i = treeLockstepLocalOption (gate i) >>=
      signingCont K circuits settings ⟨i, x i, setupKeys setup i⟩ top b (outputs i) (records i)
        (signingInitial K D circuits settings (.bottom b) x))
    (fixed : ∀ i, i ∉ D.1 → ∀ s : TreeSimState C, p.world.1.1 ≤ s.1.1 →
      ∀ r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free (gate i))).run s),
        ∀ a, r.1 = some a → a = choice)
    (room : depth (head.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) *
      settings.mode.rounds + 1 ≤ p.fuel) :
    (decode prims K D A circuits settings top (.bottom b) x setup
      (firstChunks settings (.bottom b)).length p).isSome := by
  apply decode_hit prims K D A circuits settings top (.bottom b) x setup _ p
    (signingCaller outputs records gate choice)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact ⟨lengths i hi, by simp [signingCaller, phaseIndex]⟩
  · simpa only [boundary, callerBatch, TreeCheckBatchBoundary.rounds, signingCaller,
      signing_firstChunk settings b choice.2.2 head rest hchunks] using room
  · unfold startSteps
    apply localPass_congr prims D p.world.1.1 _ _ ?_ p.world le_rfl
    intro i s hs
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi]
    · simp only [if_neg hi, worldRoles, source i hi, TreeCheckTailBoundary.program,
        boundary, callerBatch, signingCaller, signing_firstChunk settings b choice.2.2 head rest hchunks,
        signing_start circuits settings b choice.2.2]
      have atHead := signingCont_head K D circuits settings top x setup b outputs records gate choice head rest hchunks i
      unfold signingInitial signingCaller at atHead
      rw [← atHead]
      exact localOption_fixed prims D (gate i) _ choice s (fixed i hi s hs)

omit [Fintype E] [DecidableEq E] in
/-- The programs returned by the typed selector fit the signing decoder.
The retained original heads may abort; their successful values must replay
the selected choice at the retained cache. -/
theorem selected_signing_decode_hit (b : Fin (2 ^ layerHeight)) (p : Pending A)
    (outputs : C.Party → List (List Bit)) (records : C.Party → List (TreeSimCheckBatchRecord C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option PublicChoice))
    (chosen : First PublicChoice C.n) (head : List Job) (rest : List (List Job))
    (hchunks : chunks settings.batchSize (signJobs b chosen.value.2.2) = head :: rest)
    (lengths : ∀ i, i ∉ D.1 → (records i).length = (firstChunks settings (.bottom b)).length)
    (source : p.program = remainingPrograms (maskedGate D gate)
      (maskedCont D fun i => signingCont K circuits settings ⟨i, x i, setupKeys setup i⟩ top b
        (outputs i) (records i) (signingInitial K D circuits settings (.bottom b) x)) (some chosen))
    (fixed : ∀ i, i ∉ D.1 → ∀ s : TreeSimState C, p.world.1.1 ≤ s.1.1 →
      ∀ r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free (gate i))).run s),
        ∀ a, r.1 = some a → a = chosen.value)
    (room : depth (head.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) *
      settings.mode.rounds + 1 ≤ p.fuel) :
    (decode prims K D A circuits settings top (.bottom b) x setup
      (firstChunks settings (.bottom b)).length p).isSome := by
  apply signing_decode_hit prims K D A circuits settings top x setup b p outputs records
    (remainingGates (maskedGate D gate) (some chosen)) chosen.value head rest hchunks lengths ?_ ?_ room
  · intro i hi
    rw [source, remainingPrograms_typed]
    congr 1
    funext a
    exact if_neg hi
  · intro i hi s grows r run a ha
    rcases remainingGates_kind (maskedGate D gate) chosen i with none | selected | original
    · rw [none, free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      cases run
      cases ha
    · rw [selected, free_pure, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at run
      cases run
      exact (Option.some.inj ha).symm
    · rw [original] at run
      simp only [maskedGate, if_neg hi] at run
      exact fixed i hi s grows r run a ha

omit [Fintype E] [DecidableEq E] in
/-- A successful source signing selection with common honest public inputs
is a real decoder hit. Its own completed hash queries establish the cache
certificate; later tails keep executing in their original local positions. -/
theorem source_signing_decode_hit (b : Fin (2 ^ layerHeight)) (p : Pending A)
    (outputs : C.Party → List (List Bit)) (records : C.Party → List (TreeSimCheckBatchRecord C))
    (gate : C.Party → OracleComp (LocalSpec C) (Option Unit))
    (parameter : PublicParameter) (commonOutputs : List (List Bit))
    (common : ∀ i, i ∉ D.1 → (x i).parameter = parameter ∧ outputs i = commonOutputs)
    (after : TreeSimState C) (chosen : First PublicChoice C.n)
    (run : (some chosen, after) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (select fun i => free (maskedGate D
        (fun i => signingHead (x i).parameter b (outputs i) (gate i)) i))).run p.world))
    (head : List Job) (rest : List (List Job))
    (hchunks : chunks settings.batchSize (signJobs b chosen.value.2.2) = head :: rest)
    (lengths : ∀ i, i ∉ D.1 → (records i).length = (firstChunks settings (.bottom b)).length)
    (room : depth (head.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) *
      settings.mode.rounds + 1 ≤ p.fuel) :
    let selected : Pending A := {p with
      program := remainingPrograms
        (maskedGate D fun i => signingHead (x i).parameter b (outputs i) (gate i))
        (maskedCont D fun i => signingCont K circuits settings ⟨i, x i, setupKeys setup i⟩ top b
          (outputs i) (records i) (signingInitial K D circuits settings (.bottom b) x)) (some chosen)
      world := after}
    (decode prims K D A circuits settings top (.bottom b) x setup
      (firstChunks settings (.bottom b)).length selected).isSome := by
  have masks : maskedGate D (fun i => signingHead (x i).parameter b (outputs i) (gate i)) =
      maskedGate D (fun i => signingHead parameter b commonOutputs (gate i)) := by
    funext i
    by_cases hi : i ∈ D.1
    · simp only [maskedGate, if_pos hi]
    · simp only [maskedGate, if_neg hi, (common i hi).1, (common i hi).2]
  rw [masks] at run
  obtain ⟨trace, ready⟩ := selected_signing_replay prims D parameter b commonOutputs gate
    p.world after chosen run
  dsimp only
  apply selected_signing_decode_hit prims K D A circuits settings top x setup b _ outputs records
    (fun i => signingHead (x i).parameter b (outputs i) (gate i)) chosen head rest hchunks lengths rfl
  · intro i hi s grows r hr a ha
    rw [(common i hi).1, (common i hi).2] at hr
    rcases signingHead_fixed prims D parameter b commonOutputs (gate i) after.1.1 chosen.value
      (fun cache hc => ⟨trace, ready cache hc⟩) s grows r hr with rejected | accepted
    · rw [ha] at rejected
      cases rejected
    · exact Option.some.inj (ha.symm.trans accepted)
  · exact room

variable (Z : Distinguisher C A.State TreeOutput)

/-- The raw bounded scheduler, with the typed signing selection before its
local recognition test. Every missed cut executes the original next round. -/
def walk : ℕ → Pending A →
    ProbComp (Decoded (decode prims K D A circuits settings top tree x setup j) ⊕ TreeCheckTailResult A)
  | 0, p => do
      let current ← prepare prims K D A circuits settings top tree x setup j {p with fuel := 0}
      if hit : (decode prims K D A circuits settings top tree x setup j current).isSome then
        pure (.inl ⟨(current, (decode prims K D A circuits settings top tree x setup j current).get hit),
          (Option.some_get hit).symm⟩)
      else .inr <$> finish prims D Z current
  | fuel + 1, p => do
      let current ← prepare prims K D A circuits settings top tree x setup j {p with fuel := fuel + 1}
      if hit : (decode prims K D A circuits settings top tree x setup j current).isSome then
        pure (.inl ⟨(current, (decode prims K D A circuits settings top tree x setup j current).get hit),
          (Option.some_get hit).symm⟩)
      else next prims D Z fuel current >>= fun result => match result with
        | .inl pending => walk fuel pending
        | .inr terminal => pure (.inr terminal)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem next_fuel (fuel : ℕ) (p pending : Pending A)
    (run : .inl pending ∈ support (next prims D Z fuel p)) : pending.fuel = fuel := by
  unfold next at run
  rw [mem_support_bind_iff] at run
  obtain ⟨started, _, run⟩ := run
  split_ifs at run
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at run
    obtain ⟨out, _, impossible⟩ := run
    cases impossible
  · simp only [mem_support_bind_iff, mem_support_pure_iff, Sum.inl.injEq] at run
    obtain ⟨reply, _, he⟩ := run
    cases he
    rfl

/-- This is equality of full logged runs, without a bad-event condition. -/
theorem walk_split (fuel : ℕ) (p : Pending A) :
    finish prims D Z {p with fuel := fuel} =
      walk prims K D A circuits settings top tree x setup j Z fuel p >>= fun result =>
        match result with
        | .inl c => finish prims D Z c.1.1
        | .inr terminal => pure terminal := by
  induction fuel generalizing p with
  | zero =>
      rw [prepare_finish prims K D A circuits settings top tree x setup j Z {p with fuel := 0}]
      simp only [walk, bind_assoc]
      apply bind_congr
      intro current
      split_ifs <;> simp only [pure_bind, bind_map_left, bind_pure]
  | succ fuel ih =>
      rw [prepare_finish prims K D A circuits settings top tree x setup j Z {p with fuel := fuel + 1}]
      simp only [walk, bind_assoc]
      apply bind_congr_of_forall_mem_support
      intro current hc
      split_ifs with hit
      · simp only [pure_bind]
      · have currentFuel := (prepare_fuel_prefix prims K D A circuits settings top tree x setup j _ _ hc).1
        have currentEq : {current with fuel := fuel + 1} = current := by
          cases current
          simp_all
        rw [← currentEq, next_split prims D Z fuel current, bind_assoc]
        apply bind_congr_of_forall_mem_support
        intro outcome ho
        cases outcome with
        | inr result => simp only [pure_bind]
        | inl pending =>
            have hp := next_fuel prims D A Z fuel current pending ho
            have eq : {pending with fuel := fuel} = pending := by
              cases pending
              simp_all
            simpa only [eq] using ih pending

theorem walk_prefix (fuel : ℕ) (p : Pending A)
    (c : Decoded (decode prims K D A circuits settings top tree x setup j))
    (run : .inl c ∈ support (walk prims K D A circuits settings top tree x setup j Z fuel p)) :
    p.world.2 <+: c.1.1.world.2 := by
  induction fuel generalizing p with
  | zero =>
      simp only [walk, mem_support_bind_iff] at run
      obtain ⟨current, hc, run⟩ := run
      have hprefix := (prepare_fuel_prefix prims K D A circuits settings top tree x setup j _ _ hc).2
      split_ifs at run
      · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
        cases run
        exact hprefix
      · simp only [support_map, Set.mem_image] at run
        obtain ⟨result, _, impossible⟩ := run
        cases impossible
  | succ fuel ih =>
      simp only [walk, mem_support_bind_iff] at run
      obtain ⟨current, hc, run⟩ := run
      have hprefix := (prepare_fuel_prefix prims K D A circuits settings top tree x setup j _ _ hc).2
      split_ifs at run
      · simp only [mem_support_pure_iff, Sum.inl.injEq] at run
        cases run
        exact hprefix
      · rw [mem_support_bind_iff] at run
        obtain ⟨outcome, ho, run⟩ := run
        cases outcome with
        | inr result => simp only [mem_support_pure_iff] at run; cases run
        | inl pending =>
            exact hprefix.trans ((next_prefix prims D Z fuel current pending ho).trans (ih pending run))

/-- One concrete hybrid seed for every decoded checkpoint. -/
def seed (c : Pending A × Caller C) (o : TreeCheckTailCheckpoint A) :
    HybridSeed (C := C) (E := E) :=
  let batch := callerBatch K D A circuits settings top tree x setup j c.2
  let label := batch.counters.1 + depth (batch.jobs.map (circuits (x (refHolder D K.publicTerm)).parameter ·.kind)) + 1
  { adversary := checkAdversary prims K D A x (setupKeys setup) o.2.1.1 label
    state := (o.1.1, label)
    keys := priorKeys label o.2.1.1 }

abbrev sourceWalk (step : ℕ)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) : TreeCheckTailWalk A where
  β := Decoded (decode prims K D A circuits settings top tree x p.1.2 j)
  pre := walk prims K D A circuits settings top tree x p.1.2 j Z
    (initial K circuits settings top tree x p).fuel (initial K circuits settings top tree x p)
  boundary := fun c => boundary D K circuits settings x
    (c.1.1, callerBatch K D A circuits settings top tree x p.1.2 j c.1.2)
  hybrid := fun c o => hybrid D K circuits settings x step
    (c.1.1, callerBatch K D A circuits settings top tree x p.1.2 j c.1.2) o
    (seed prims K D A circuits settings top tree x p.1.2 j c.1 o)

/-- Every recognized caller uses the original party identity and input keys,
and the PRSS key row retained from setup. -/
theorem sourceWalk_context (step : ℕ)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (c : Decoded (decode prims K D A circuits settings top tree x p.1.2 j)) (i : C.Party) :
    ((sourceWalk prims K D A circuits settings top tree x j Z step p).boundary c).batch.ctx i =
      ⟨i, x i, setupKeys p.1.2 i⟩ := rfl

/-- The adapter's key set consists exactly of cached keys from earlier coin
labels, including at cut states that cannot be live. -/
theorem sourceWalk_prior (step : ℕ) (z : Aux) (index : Fin (treeBatches settings tree))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    ((sourceWalk prims K D A circuits settings top tree x j Z step p).cut prims K circuits settings D Z).Prior
      prims K circuits settings top tree D A x z index := by
  rintro (⟨c, o⟩ | r) _ _
  · exact priorKeys_prior _ _
  · intro key hk
    exact (Finset.notMem_empty key hk).elim

theorem sourceWalk_split (step : ℕ) (z : Aux)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (dealt : DealtInputs D x) (hp : p ∈ support (treeSaltSetup prims D A x z)) :
    (sourceWalk prims K D A circuits settings top tree x j Z step p).Split
      prims K circuits settings D top tree x Z p := by
  constructor
  · rw [initial_split prims D Z K circuits settings top tree x z p hp]
    have cut := walk_split prims K D A circuits settings top tree x p.1.2 j Z
      (initial K circuits settings top tree x p).fuel (initial K circuits settings top tree x p)
    change finish prims D Z (initial K circuits settings top tree x p) = _ at cut
    rw [cut]
    dsimp only [sourceWalk]
    apply bind_congr
    intro outcome
    cases outcome with
    | inr terminal => rfl
    | inl c =>
        exact fits_finish prims K D A circuits settings top tree x p.1.2 j Z c.1.1 c.1.2
          (decode_sound prims K D A circuits settings top tree x p.1.2 j c)
  · intro c i
    obtain ⟨parameter, seeds, pairs, hx⟩ := dealt
    change (x i).parameter = (x (refHolder D K.publicTerm)).parameter
    rw [hx i, hx (refHolder D K.publicTerm)]
    rfl

theorem sourceWalk_standard (step : ℕ)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    (sourceWalk prims K D A circuits settings top tree x j Z step p).StandardTuples circuits D ∧
      ∀ c i, (((sourceWalk prims K D A circuits settings top tree x j Z step p).boundary c).batch.ctx i).self = i :=
  ⟨fun _ _ => ⟨rfl, fun _ _ => rfl⟩, fun _ _ => rfl⟩

set_option linter.constructorNameAsVariable false in
theorem sourceWalk_log_prefix (step : ℕ)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (c : Decoded (decode prims K D A circuits settings top tree x p.1.2 j))
    (o : TreeCheckTailCheckpoint A)
    (run : (.inl (c, o) : (Decoded (decode prims K D A circuits settings top tree x p.1.2 j) ×
        TreeCheckTailCheckpoint A) ⊕ TreeCheckTailResult A) ∈ support
      ((sourceWalk prims K D A circuits settings top tree x j Z step p).cut prims K circuits settings D Z).pre) :
    p.2.2 <+: o.2.2 := by
  let W := sourceWalk prims K D A circuits settings top tree x j Z step p
  have hc : .inl c ∈ support W.pre := by
    with_reducible exact index_support prims D Z K circuits settings W c o run
  have ho : o ∈ support (((sourceWalk prims K D A circuits settings top tree x j Z step p).boundary c).pre
      prims K circuits settings D) := by
    with_reducible exact (TreeCheckTailWalk.mem_support_cut_pre
      (W := W) (prims := prims) (K := K) (circuits := circuits) (settings := settings)
      (D := D) (Z := Z) (c := c) (o := o) run)
  dsimp only [W, sourceWalk] at hc ho
  have before : p.2.2 <+: c.1.1.world.2 := by
    change (initial K circuits settings top tree x p).world.2 <+: c.1.1.world.2
    with_reducible exact (walk_prefix prims K D A circuits settings top tree x p.1.2 j Z
      (initial K circuits settings top tree x p).fuel (initial K circuits settings top tree x p) c hc)
  have after := treeSimLoggedWorld_prefix prims D _ c.1.1.world o ho
  exact before.trans after

end Compiler

section Assembly

variable (circuits : Circuits) (settings : Settings)

/-- The same concrete source family supplies every semantic field. -/
abbrev family (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (bounded : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (j : Fin (treeBatches settings tree))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) : TreeCheckTailWalk A :=
  sourceWalk prims K D A circuits settings top tree x j.val Z (TreeCheckQueryBudget.ofBound bounded).step p

set_option linter.unusedVariables false in
def AtWalk (F : ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (bounded : IsQueryBounded A Z (ceremonyFuel circuits settings) q)
    (j : Fin (treeBatches settings tree))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C), TreeCheckTailWalk A → Prop) : Prop :=
  0 < settings.batchSize →
    ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      DealtInputs D x →
      ∀ bounded : IsQueryBounded A Z (ceremonyFuel circuits settings) q, q < 2 ^ 128 →
      ∀ j : Fin (treeBatches settings tree),
        ∀ p ∈ support (treeSaltSetup prims D A x z),
          F top tree D A x z Z q bounded j p (family prims K circuits settings top tree D A x Z q bounded j p)

def WalkSplit : Prop :=
  AtWalk prims K circuits settings fun top tree D _ x _ Z _ _ _ p W =>
    W.Split prims K circuits settings D top tree x Z p ∧ W.StandardTuples circuits D ∧
      ∀ c i, ((W.boundary c).batch.ctx i).self = i

def WalkBad : Prop :=
  AtWalk prims K circuits settings fun top tree D A x z Z _ _ j _ W =>
    (W.cut prims K circuits settings D Z).Jobs prims K circuits settings top tree D A x z j ∧
      W.Unreached prims K circuits settings D top tree x z j ∧
      W.Consistent prims K circuits settings D top tree x z Z j

def WalkOpening : Prop :=
  AtWalk prims K circuits settings fun top tree D A x z Z _ _ j _ W =>
    W.IndexedOpening prims K circuits settings top tree D A x z Z j

def WalkPositions : Prop :=
  AtWalk prims K circuits settings fun top tree D A x z Z _ bounded j _ W =>
    ∀ c o, (.inl (c, o) : (W.cut prims K circuits settings D Z).σ) ∈
        support (W.cut prims K circuits settings D Z).pre →
      (W.cut prims K circuits settings D Z).Live prims K circuits settings top tree D A x z j (.inl (c, o)) →
      (∃ i, i ∈ D.1) ∧ Nonempty (TreeCheckPrefixPosition prims circuits settings D A x z Z
        (TreeCheckQueryBudget.ofBound bounded) ((W.cut prims K circuits settings D Z).count (.inl (c, o))) o)

def WalkHybrid : Prop :=
  AtWalk prims K circuits settings fun top tree D A x z Z _ _ j _ W =>
    (W.cut prims K circuits settings D Z).Queries prims K circuits settings top tree D A x z j ∧
      (W.cut prims K circuits settings D Z).Cache prims K circuits settings top tree D A x z j ∧
      (W.cut prims K circuits settings D Z).Transport prims K circuits settings top tree D A x z j

theorem walkSplit : WalkSplit prims K circuits settings := by
  intro _ top tree D A x z Z q dealt bounded _ j p hp
  exact ⟨sourceWalk_split prims K D A circuits settings top tree x j.val Z _ z p dealt hp,
    sourceWalk_standard prims K D A circuits settings top tree x j.val Z _ p⟩

set_option maxRecDepth 2000 in
set_option linter.constructorNameAsVariable false in
/-- The semantic clauses all refer to this one source family, with its
concrete decoder, typed selector and GS20 hybrid adapter. -/
theorem sourceConstruction_of_fields
    (bad : WalkBad prims K circuits settings)
    (opening : WalkOpening prims K circuits settings)
    (positions : WalkPositions prims K circuits settings)
    (hybrid : WalkHybrid prims K circuits settings) :
    TreeCheckTailWalkSourceConstruction prims K circuits settings := by
  intro hb top tree D A x z Z q dealt bounded small j p hp
  let W := family prims K circuits settings top tree D A x Z q bounded j p
  obtain ⟨split, standard, self⟩ := walkSplit prims K circuits settings
    hb top tree D A x z Z q dealt bounded small j p hp
  obtain ⟨jobs, unreached, consistent⟩ := bad hb top tree D A x z Z q dealt bounded small j p hp
  obtain ⟨queries, cache, transport⟩ := hybrid hb top tree D A x z Z q dealt bounded small j p hp
  refine ⟨W, {
    split := split
    standard := standard
    self := self
    jobs := jobs
    unreached := unreached
    consistent := consistent
    opening := opening hb top tree D A x z Z q dealt bounded small j p hp
    queries := queries
    cache := cache
    prior := sourceWalk_prior prims K D A circuits settings top tree x j.val Z
      (TreeCheckQueryBudget.ofBound bounded).step z j p
    transport := transport
    logs := ?_ }⟩
  intro c o run live
  have atPosition := positions hb top tree D A x z Z q dealt bounded small j p hp
  with_reducible obtain ⟨corrupt, position⟩ := atPosition c o run live
  refine ⟨rfl, rfl, ?_, corrupt, position⟩
  with_reducible exact (sourceWalk_log_prefix prims K D A circuits settings top tree x j.val Z
    (TreeCheckQueryBudget.ofBound bounded).step p c o run)

end Assembly

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.publicRun_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms publicRun_replay

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.selectPending_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selectPending_finish

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.selected_signing_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected_signing_replay

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.initial_decode_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms initial_decode_hit

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.source_signing_decode_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_signing_decode_hit

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.sourceWalk_prior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceWalk_prior

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.sourceWalk_log_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceWalk_log_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.walkSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms walkSplit

/-- info: 'ThresholdLeanXmssSecurity.TreeCheckWalkRecipe.sourceConstruction_of_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sourceConstruction_of_fields

end TreeCheckWalkRecipe
end ThresholdLeanXmssSecurity

