import ThresholdLeanXmssSecurity.Proof.TreeRawSaltFlow
import ThresholdLeanXmssSecurity.Proof.TreeLockstepSegments

/-!
Compilation of the actual ceremony to salt-digest boundaries.

The compiler retains the original synchronous order and abort branches. Ordinary
local programs are certified by the existing no-salt segment proofs; the only
additional source form fuses `randBits 256` with its actual digest comparison.
Private responses are digest lists, never raw salt bits. The pinned and current
leanVM simulations were searched; their generic simulation laws are reused,
while this coroutine grammar is specific to the threshold program.

`ceremonyBoundaryProgram` proves the exact
`TreeRawSaltFlowProof.CeremonyBoundaryProgram`. The full-state and original
writer-log corollaries instantiate the split-cache law on the actual ceremony,
including adaptive bottom jobs, empty checks, aborts and fuel exhaustion.

The whole-run interface is `TreeRawSaltCeremonyRepresentation`. Its opaque-table
interpretation requires the
mixed hidden/known/pair row law, full-log decoder, lazy-address allocation,
private budget H, charged budget q+H, and event transport under exactly
`¬TreeSimHashCollision`. The generic public boundary also admits programming;
normalizing the chosen actual witness must retain its no-program provenance.
The split-cache law alone proves none of these quantitative obligations.
No stage-independence or setup-fixed salt-address cover is assumed.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section
namespace ThresholdLeanXmssSecurity
namespace TreeRawSaltCompileProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Algebra Bit E]

open TreeRawSaltFlowProof

/-- A compiler returns the original value together with the invariant needed
to compile its continuation. The invariant is proof data, not an oracle answer. -/
def Compiled (D : C.Coalition) {α : Type} (p : OracleComp (WorldSpec C) α)
    (P : α → Prop) : Prop :=
  ∃ q : OracleComp (BoundarySpec D) {a // P a},
    Subtype.val <$> simulateQ (boundarySource (E := E) D) q = p

theorem Compiled.pure (D : C.Coalition) {α : Type} (a : α) (P : α → Prop) (ha : P a) :
    Compiled (E := E) D (pure a) P := by
  exact ⟨Pure.pure ⟨a, ha⟩, by simp⟩

theorem Compiled.bind (D : C.Coalition) {α β : Type}
    {p : OracleComp (WorldSpec C) α} {P : α → Prop}
    {f : α → OracleComp (WorldSpec C) β} {Q : β → Prop}
    (hp : Compiled (E := E) D p P)
    (hf : ∀ a, P a → Compiled (E := E) D (f a) Q) :
    Compiled (E := E) D (p >>= f) Q := by
  obtain ⟨q, hq⟩ := hp
  choose next law using fun a : {a // P a} => hf a.1 a.2
  refine ⟨q >>= next, ?_⟩
  simp only [simulateQ_bind, map_bind, law]
  rw [← bind_map_left, hq]

theorem Compiled.map (D : C.Coalition) {α β : Type}
    {p : OracleComp (WorldSpec C) α} {P : α → Prop} (f : α → β) (Q : β → Prop)
    (hp : Compiled (E := E) D p P) (hf : ∀ a, P a → Q (f a)) :
    Compiled (E := E) D (f <$> p) Q := by
  simpa only [bind_pure_comp] using hp.bind D (fun a ha => Compiled.pure D (f a) Q (hf a ha))

theorem Compiled.public (D : C.Coalition) (t : (WorldSpec C).Domain)
    (safe : NoSaltRead D t) :
    Compiled (E := E) D (OracleComp.lift (OracleSpec.query t)) (fun _ => True) := by
  refine ⟨(fun a => (⟨a, True.intro⟩ : {a : (WorldSpec C).Range t // True})) <$>
    (OracleComp.lift (OracleSpec.query (spec := BoundarySpec D) (.inr ⟨t, safe⟩))), ?_⟩
  simp only [simulateQ_map, simulateQ_spec_query, boundarySource, Functor.map_map]
  exact id_map _

/-- Reify a segment that cannot read a hidden salt position. -/
theorem Compiled.safe (D : C.Coalition) {α : Type} (p : OracleComp (WorldSpec C) α)
    (safe : IsQueryBoundP p (fun t => ¬NoSaltRead D t) 0) :
    Compiled (E := E) D p (fun _ => True) := by
  induction p using OracleComp.inductionOn with
  | pure a => exact Compiled.pure D a _ trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at safe
    exact (Compiled.public D t (by simpa using safe.1)).bind D
      (fun a _ => ih a (by simpa using safe.2 a))

theorem Compiled.digest (D : C.Coalition) (ctx : Context C) (st : RunState C) :
    Compiled (E := E) D (free (liftComp (treeSimHashSaltDigestDraw (E := E) ctx st) (LocalSpec C)))
      (fun _ => True) := by
  refine ⟨(fun a => (⟨a, True.intro⟩ : {a : List HashOutput // True})) <$>
    (OracleComp.lift (OracleSpec.query (spec := BoundarySpec D) (.inl (ctx, st)))), ?_⟩
  simp only [simulateQ_map, simulateQ_spec_query, boundarySource, Functor.map_map]
  exact id_map _

/-- Source programs whose salt reads are consumed at complete digest
boundaries. Exchanges retain their original raw continuation. -/
inductive PartyCode (D : C.Coalition) {α : Type} :
    OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | pure (a : Option α) : PartyCode D (pure a)
  | localQuery (t : (LocalSpec C).Domain) (safe : NoSaltRead D (.inr t))
      (k : (LocalSpec C).Range t → OracleComp (PartySpec C E RealSpec) (Option α))
      (next : ∀ a, PartyCode D (k a)) : PartyCode D (.roll (.inl (.inl t)) k)
  | round (out : Mail C E)
      (k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α))
      (next : ∀ a, PartyCode D (k a)) : PartyCode D (.roll (.inl (.inr out)) k)
  | digest (ctx : Context C) (st : RunState C)
      (k : Unit × RunState C → PartyM C E RealSpec α)
      (next : ∀ a, PartyCode D (k a).run) :
      PartyCode D ((((prssRandomness ctx bitCodec 2 256 >>= fun rnd =>
        compareDigests ctx rnd.1).run st) >>= k).run)

theorem PartyCode.bind (D : C.Coalition) {α β : Type}
    {p : PartyM C E RealSpec α} {k : α → PartyM C E RealSpec β}
    (hp : PartyCode D p.run) (hk : ∀ a, PartyCode D (k a).run) :
    PartyCode D (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change PartyCode D (p.run >>= fun a => a.elim (Pure.pure none) (fun a => (k a).run))
  generalize p.run = oa at hp ⊢
  induction hp with
  | pure a =>
    cases a with
    | none => simpa only [pure_bind, Option.elim_none, Option.elim_some] using PartyCode.pure (D := D) (E := E) (none : Option β)
    | some a => simpa only [pure_bind, Option.elim_none, Option.elim_some] using hk a
  | localQuery t safe f next ih =>
    change PartyCode D (.roll _ _)
    exact .localQuery t safe _ ih
  | round out f next ih =>
    change PartyCode D (.roll _ _)
    exact .round out _ ih
  | digest ctx st f next ih =>
    have h := PartyCode.digest (D := D) ctx st (fun a => f a >>= k)
      (fun a => by simpa only [OptionT.run_bind, Option.elimM] using ih a)
    simpa only [← bind_assoc, OptionT.run_bind, Option.elimM] using h

theorem PartyCode.require (D : C.Coalition) (p : Prop) :
    PartyCode (E := E) D (require (C := C) (E := E) (G := RealSpec) p).run := by
  unfold ThresholdLeanXmss.require
  split_ifs <;> exact .pure _

/-- The previously proved segment certificates supply the ordinary source
cases, including every abort prefix. -/
theorem PartyCode.of_noSalt (D : C.Coalition) {α : Type} {j n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)}
    (hp : TreeSegmentRun (fun _ _ _ _ => False) j n p) : PartyCode D p := by
  induction hp with
  | abort j n => exact .pure _
  | done j a => exact .pure _
  | round j n out k h ih => exact .round out k ih
  | queryLocal j n t k ht h ih =>
    apply PartyCode.localQuery t _ k ih
    rcases t with u | q | x
    · trivial
    · trivial
    · intro hidden
      cases h : saltAt ((x.1, x.2.1), x.2.2) with
      | none => rfl
      | some bg =>
        obtain ⟨b, g⟩ := bg
        have hx := saltAt_sound h
        have he : x = (.term b.1, b.2.1, b.2.2, 2, g.val) := by
          exact congrArg (fun y : HiddenAddress C => (y.1.1, y.1.2, y.2)) hx
        exact (ht x rfl b.1 b.2.1 b.2.2 g.val he).elim

def StepCode (D : C.Coalition) {α : Type} : Step C E RealSpec α → Prop
  | .done _ => True
  | .wait _ resume => ∀ inbox, PartyCode D (resume inbox)
  | .call impossible _ => impossible.elim

theorem exchangeResume_code (D : C.Coalition) {α : Type}
    (k : Mail C E → PartyM C E RealSpec α) (hk : ∀ inbox, PartyCode D (k inbox).run)
    (inbox : Mail C E) : PartyCode D (exchangeResume k inbox) := by
  unfold exchangeResume
  split_ifs
  · exact .pure _
  · exact hk inbox

/-- One actual advance compiles to safe public calls and whole salt-digest
calls, while all returned coroutine continuations remain compilable. -/
theorem PartyCode.advance (D : C.Coalition) (K : Constants C E) {α : Type}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (hp : PartyCode D p) :
    Compiled (E := E) D (free (advance p)) (StepCode D) := by
  induction hp with
  | pure a =>
    exact Compiled.pure D (Step.done a) _ trivial
  | localQuery t safe k next ih =>
    change Compiled (E := E) D (free (OracleComp.lift (OracleSpec.query t) >>= fun a => ThresholdLeanXmss.advance (k a))) _
    rw [free_bind]
    exact (Compiled.public D (.inr t) safe).bind D (fun a _ => ih a)
  | round out k next ih =>
    exact Compiled.pure D (Step.wait out k) _ next
  | digest ctx st k next ih =>
    rw [show free (ThresholdLeanXmss.advance _) = _ from treeSimHash_salt_digest_entry K ctx st k]
    apply (Compiled.digest (E := E) D ctx st).map D _ _
    intro ds _ inbox
    exact exchangeResume_code D _ (fun inbox =>
      (PartyCode.require D _).bind D (fun _ => next ((), nextLabel st))) _

/-- Finite operator order is retained exactly. -/
theorem Compiled.sequenceFin (D : C.Coalition) {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp (WorldSpec C) α) (P : Fin n → α → Prop),
      (∀ i, Compiled (E := E) D (f i) (P i)) →
      Compiled (E := E) D (Concrete.sequenceFin f) (fun a => ∀ i, P i (a i))
  | 0, f, P, h => Compiled.pure D _ _ (fun i => Fin.elim0 i)
  | n + 1, f, P, h => by
    unfold Concrete.sequenceFin
    exact (h 0).bind D fun a ha =>
      (Compiled.sequenceFin D (fun i => f i.succ) (fun i => P i.succ) (fun i => h i.succ)).bind D
        fun as hs => Compiled.pure D _ _ (fun i => Fin.cases ha hs i)

theorem Compiled.adversary (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α) :
    Compiled (E := E) D (worldRoles.adversary p) (fun _ => True) := by
  induction p using OracleComp.inductionOn with
  | pure a => exact Compiled.pure D a _ trivial
  | query_bind t k ih =>
    simp only [worldRoles, counted, liftComp_bind, simulateQ_bind]
    change Compiled (E := E) D (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
      fun a => worldRoles.adversary (k a)) (fun _ => True)
    rw [adversary_query]
    exact (Compiled.public D (.inl (.inl t)) trivial).bind D (fun a _ => ih a)

theorem compiled_roundLocal (D : C.Coalition) (K : Constants C E) {α : Type}
    (steps : C.Party → Step C E RealSpec α) (hs : ∀ i, StepCode D (steps i))
    (sent : C.Party → Mail C E) (i : C.Party) :
    Compiled (E := E) D (free (roundLocal D steps sent i)) (StepCode D) := by
  unfold roundLocal
  have hi := hs i
  cases h : steps i with
  | done out => exact Compiled.pure D _ _ trivial
  | call input k => exact input.elim
  | wait out k =>
    split_ifs
    · exact Compiled.pure D _ _ trivial
    · rw [h] at hi
      exact PartyCode.advance D K (hi _)

theorem compiled_stepRound (D : C.Coalition) (K : Constants C E) {α : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (hs : ∀ i, StepCode D (steps i)) :
    Compiled (E := E) D (stepRound worldRoles D A noFunctionality state steps)
      (fun r => ∀ i, StepCode D (r.2.1 i)) := by
  rw [stepRound_real]
  refine (Compiled.adversary D _).bind D fun r _ => ?_
  dsimp only at *
  rw [free_sequenceFin]
  exact (Compiled.sequenceFin D _ (fun _ => StepCode D)
    (compiled_roundLocal D K steps hs r.2)).bind D fun next hn =>
      Compiled.pure D _ _ hn

theorem compiled_executeRounds (D : C.Coalition) (K : Constants C E) {α : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) :
    ∀ fuel state (steps : C.Party → Step C E RealSpec α), (∀ i, StepCode D (steps i)) →
      Compiled (E := E) D (executeRounds worldRoles D A noFunctionality fuel state steps)
        (fun _ => True)
  | 0, state, steps, hs => Compiled.pure D _ _ trivial
  | fuel + 1, state, steps, hs => by
    rw [executeRounds]
    split_ifs
    · exact Compiled.pure D _ _ trivial
    · exact (compiled_stepRound D K A state steps hs).bind D fun r hr =>
        compiled_executeRounds D K A fuel r.1 r.2.1 hr

theorem compiled_executePhase (D : C.Coalition) (K : Constants C E) {α : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α)
    (hp : ∀ i, PartyCode D (program i).run) :
    Compiled (E := E) D (executePhase worldRoles D A noFunctionality fuel state program)
      (fun _ => True) := by
  unfold executePhase startSteps
  refine (Compiled.sequenceFin D _ (fun _ => StepCode D) ?_).bind D fun steps hs =>
    compiled_executeRounds D K A fuel state steps hs
  intro i
  split_ifs
  · exact Compiled.pure D _ _ trivial
  · exact PartyCode.advance D K (hp i)

theorem PartyCode.map (D : C.Coalition) {α β : Type} (f : α → β)
    {p : PartyM C E RealSpec α} (hp : PartyCode D p.run) :
    PartyCode D (f <$> p).run := by
  rw [map_eq_bind_pure_comp]
  exact hp.bind D fun _ => .pure _

theorem PartyCode.state_bind (D : C.Coalition) {σ α β : Type}
    {p : StateT σ (PartyM C E RealSpec) α} {k : α → StateT σ (PartyM C E RealSpec) β} {s : σ}
    (hp : PartyCode D (p.run s).run)
    (hk : ∀ a s', PartyCode D ((k a).run s').run) :
    PartyCode D ((p >>= k).run s).run := by
  rw [StateT.run_bind]
  exact hp.bind D fun a => hk a.1 a.2

theorem PartyCode.lift (D : C.Coalition) {σ α : Type} {p : PartyM C E RealSpec α}
    (hp : PartyCode D p.run) (s : σ) :
    PartyCode D ((StateT.lift p : StateT σ (PartyM C E RealSpec) α).run s).run := by
  rw [StateT.run_lift]
  exact hp.bind D fun _ => .pure _

theorem PartyCode.foldlM (D : C.Coalition) {σ α β : Type}
    (f : α → β → StateT σ (PartyM C E RealSpec) α)
    (hf : ∀ a b s, PartyCode D ((f a b).run s).run) :
    ∀ (xs : List β) (a : α) (s : σ), PartyCode D ((xs.foldlM f a).run s).run
  | [], a, s => .pure _
  | b :: xs, a, s => by
    rw [List.foldlM_cons]
    exact (hf a b s).state_bind D fun a' s' => PartyCode.foldlM D f hf xs a' s'

theorem PartyCode.state_mapM (D : C.Coalition) {σ α β : Type}
    (f : α → StateT σ (PartyM C E RealSpec) β)
    (hf : ∀ a s, PartyCode D ((f a).run s).run) :
    ∀ (xs : List α) (s : σ), PartyCode D ((xs.mapM f).run s).run
  | [], s => .pure _
  | a :: xs, s => by
    rw [List.mapM_cons]
    exact (hf a s).state_bind D fun b s' =>
      (PartyCode.state_mapM D f hf xs s').state_bind D fun bs s'' => .pure _

/-- All salt bits of this source form remain internal to the digest boundary. -/
theorem PartyCode.digest_tail (D : C.Coalition) (ctx : Context C) (st : RunState C)
    {α : Type} (tail : RunM C E RealSpec α)
    (ht : ∀ s, PartyCode D (tail.run s).run) :
    PartyCode D ((do
      let salts ← prssRandomness ctx bitCodec 2 256
      compareDigests ctx salts.1
      tail).run st).run := by
  rw [← bind_assoc, StateT.run_bind]
  exact .digest ctx st _ (fun a => ht a.2)

section ActualPrograms
variable [Fintype E] [DecidableEq E]
variable (D : C.Coalition) (K : Constants C E)

theorem partyCode_finalStep (ctx : Context C) (p : (ℕ → E) × (ℕ → E) × E) (st : RunState C) :
    PartyCode D ((finalStep K ctx (realCheckGadgets K ctx) p).run st).run := by
  rcases p with ⟨a, b, d⟩
  unfold finalStep
  refine (PartyCode.of_noSalt D (treeSegmentRun_prssRandomness ctx (elementCodec K)
    (fun _ => elementCodec_salts K) 1 2 0 st (by omega))).state_bind D fun w s1 => ?_
  refine (PartyCode.of_noSalt D (treeSegmentRun_extendMult K ctx _ 0 s1)).state_bind D
    fun q s2 => ?_
  apply PartyCode.digest_tail D ctx s2
  intro s3
  refine (PartyCode.of_noSalt D (treeSegmentRun_challenge K ctx 0 s3)).state_bind D fun r s4 => ?_
  refine ((PartyCode.of_noSalt D (treeSegmentRun_openSh K ctx _ 3 0)).lift D s4).state_bind D
    fun opened s5 => ?_
  exact (PartyCode.require D _).lift D s5

/-- Every check, including zero tuples and every failing validation, has the
source boundary grammar. No agreement or successful-output assumption occurs. -/
theorem partyCode_check (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C) :
    PartyCode D ((check K ctx (realCheckGadgets K ctx) tuples).run st).run := by
  by_cases hz : (tuples.map (·.count)).sum = 0
  · simp only [check, hz, ↓reduceIte]
    exact .pure _
  rw [check_eq K ctx _ tuples hz]
  refine (PartyCode.of_noSalt D (treeSegmentRun_coinKey K ctx 0 st)).state_bind D fun key s1 => ?_
  refine (PartyCode.of_noSalt D (treeSegmentRun_expand K key _ 0 s1)).state_bind D fun τ s2 => ?_
  refine ((PartyCode.require D _).lift D s2).state_bind D fun _ s3 => ?_
  refine (PartyCode.foldlM D _ (fun p j s => ?_) _ _ s3).state_bind D fun p s4 => ?_
  · rcases p with ⟨a, b, d⟩
    unfold sliceStep
    exact (PartyCode.of_noSalt D (treeSegmentRun_extendMult K ctx _ 0 s)).state_bind D
      fun t s' => (PartyCode.of_noSalt D (treeSegmentRun_challenge K ctx 0 s')).state_bind D
        fun r s'' => .pure _
  refine (PartyCode.foldlM D _ (fun p j s => ?_) _ _ s4).state_bind D fun p s5 => ?_
  · rcases p with ⟨a, b, d⟩
    unfold halvingStep
    exact (PartyCode.of_noSalt D (treeSegmentRun_extendMult K ctx _ 0 s)).state_bind D
      fun t s' => (PartyCode.of_noSalt D (treeSegmentRun_challenge K ctx 0 s')).state_bind D
        fun r s'' => .pure _
  exact partyCode_finalStep D K ctx p s5

variable (circuits : Circuits) (settings : Settings)

theorem partyCode_ceremonyBatch (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    PartyCode D ((ceremonyBatch K circuits settings ctx jobs :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run initial).run := by
  rw [← treeSimCheckBatchAudit_erase K circuits settings ctx jobs]
  change PartyCode D ((Prod.fst <$> (treeSimCheckBatchAudit K circuits settings ctx jobs).run).run
    initial).run
  rw [StateT.run_map, treeSimCheckBatchAudit_run_prefix]
  apply PartyCode.map
  have hp : PartyCode D (treeSimCheckBatchPrefix K circuits settings ctx jobs initial).run := by
    apply PartyCode.of_noSalt D
    unfold treeSimCheckBatchPrefix
    exact treeSegmentRun_inputs ctx 0 _ jobs _ fun inputs =>
      (treeSegmentRun_beforeVerify K ctx settings.mode _ inputs 0 _).bind fun _ _ =>
        TreeSegmentRun.pure _ _
  refine hp.bind D fun a => ?_
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify
  refine ((partyCode_check D K ctx a.2.1.2 a.2.2).bind D fun x => ?_).bind D fun _ => .pure _
  rcases x with ⟨_, final⟩
  exact (PartyCode.of_noSalt D (treeSegmentRun_openRep K ctx _ _ 0)).bind D fun _ => .pure _

theorem partyCode_batched (ctx : Context C) (jobs : List Job) (s : ℕ × ℕ) :
    PartyCode D ((batched settings.batchSize (ceremonyBatch K circuits settings ctx) jobs :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run s).run := by
  unfold batched
  exact (PartyCode.state_mapM D _ (partyCode_ceremonyBatch D K circuits settings ctx) _ s).state_bind D
    fun _ _ => .pure _

theorem partyCode_ceremonyOutput (ctx : Context C) (top : TopTree) (tree : Tree) (s : ℕ × ℕ) :
    PartyCode D ((ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) ctx.keys.parameter
      (batched settings.batchSize (ceremonyBatch K circuits settings ctx)) top tree).run s).run := by
  cases tree with
  | top =>
    simp only [ceremonyOutput]
    refine (partyCode_batched D K circuits settings ctx _ s).state_bind D fun r s' => ?_
    rcases r with _ | outputs
    · exact .pure _
    exact (PartyCode.of_noSalt D (treeSegmentRun_tweakable _ 0 s')).state_bind D fun _ _ => .pure _
  | bottom b =>
    simp only [ceremonyOutput]
    refine (partyCode_batched D K circuits settings ctx _ s).state_bind D fun r s' => ?_
    rcases r with _ | outputs
    · exact .pure _
    refine (PartyCode.of_noSalt D (treeSegmentRun_tweakable _ 0 s')).state_bind D fun root s1 => ?_
    refine (PartyCode.of_noSalt D (treeSegmentRun_tweakable _ 0 s1)).state_bind D fun base s2 => ?_
    refine (PartyCode.of_noSalt D (treeSegmentRun_tweakable _ 0 s2)).state_bind D fun g s3 => ?_
    rcases g with _ | ⟨randomness, encoding⟩
    · exact .pure _
    refine (partyCode_batched D K circuits settings ctx _ s3).state_bind D fun v s4 => ?_
    rcases v with _ | values
    · exact .pure _
    refine (PartyCode.of_noSalt D (treeSegmentRun_tweakable _ 0 s4)).state_bind D fun path s5 => ?_
    refine (PartyCode.of_noSalt D (treeSegmentRun_tweakable _ 0 s5)).state_bind D fun root' s6 => ?_
    split_ifs <;> exact .pure _

/-- The complete source ceremony, including adaptive bottom-tree job choices,
inhabits the grammar before any oracle is sampled. -/
theorem partyCode_ceremony (i : C.Party) (keys : Keys C) (top : TopTree) (tree : Tree) :
    PartyCode D (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput).run := by
  rw [ceremony_eq_prssSetup_bind]
  refine (PartyCode.of_noSalt D (treeSegmentRun_prssSetup (E := E) i)).bind D fun prss => ?_
  unfold ceremonyAfterSetup
  refine PartyCode.bind D ?_ fun out => ?_
  · rw [StateT.run'_eq]
    exact (partyCode_ceremonyOutput D K circuits settings ⟨i, keys, prss⟩ top tree (0, 0)).map D _
  · cases out <;> exact .pure _

theorem compiled_treeRealGame (top : TopTree) (tree : Tree)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    Compiled (E := E) D (treeRealGame K circuits settings top tree D A x z Z) (fun _ => True) := by
  unfold treeRealGame distinguish realExecution
  refine ((Compiled.adversary D _).bind D fun state _ =>
    compiled_executePhase D K A _ state _ (fun i =>
      partyCode_ceremony D K circuits settings i (x i) top tree)).bind D fun r _ =>
        Compiled.adversary D (Z r)

/-- Exact whole-program compilation. It needs no success or query-bound
assumption and retains the original final result, aborts and scheduler order. -/
theorem ceremonyBoundaryProgram : CeremonyBoundaryProgram K circuits settings := by
  intro _ top tree D A x z Z q _ _ _
  obtain ⟨p, hp⟩ := compiled_treeRealGame D K circuits settings top tree A x z Z
  refine ⟨Subtype.val <$> p, ?_⟩
  simpa only [simulateQ_map] using hp

/-- The actual whole ceremony has the split-cache law from every allowed
complete initial salt cache; the full final cache and log are retained. -/
theorem ceremony_boundary_joint (prims : Primitives) (top : TopTree) (tree : Tree)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    ∃ p : OracleComp (BoundarySpec D) Bool,
      simulateQ (boundarySource (E := E) D) p = treeRealGame K circuits settings top tree D A x z Z ∧
      ∀ s : TreeSimState C, TreeSimHashSaltBlocksComplete s.1.2 →
        𝒟[(simulateQ (treeSimLoggedWorld prims D)
          (treeRealGame K circuits settings top tree D A x z Z)).run s] =
        𝒟[(fun r => (r.1, decodeState r.2)) <$>
          (simulateQ (boundarySplit prims D) p).run (encodeState s)] := by
  obtain ⟨p, hp⟩ := compiled_treeRealGame D K circuits settings top tree A x z Z
  have he : simulateQ (boundarySource (E := E) D) (Subtype.val <$> p) =
      treeRealGame K circuits settings top tree D A x z Z := by
    simpa only [simulateQ_map] using hp
  refine ⟨Subtype.val <$> p, he, fun s complete => ?_⟩
  rw [← he]
  exact boundary_program_from (E := E) prims D _ s complete

/-- Full original writer output, with the same compiled program even if the
ceremony aborts. This does not yet replace the private cache by the finite table. -/
theorem ceremony_boundary_logged (prims : Primitives) (top : TopTree) (tree : Tree)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    ∃ p : OracleComp (BoundarySpec D) Bool,
      simulateQ (boundarySource (E := E) D) p = treeRealGame K circuits settings top tree D A x z Z ∧
      𝒟[treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] =
        𝒟[(fun r => (r.1, r.2.1.2)) <$>
          (simulateQ (boundarySplit prims D) p).run (((∅, ∅), []), ∅)] := by
  obtain ⟨p, hp, _⟩ := ceremony_boundary_joint D K circuits settings prims top tree A x z Z
  refine ⟨p, hp, ?_⟩
  rw [← hp]
  exact boundary_program_logged (E := E) prims D p

end ActualPrograms

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCompileProof.Compiled.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Compiled.bind

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCompileProof.PartyCode.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PartyCode.bind

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCompileProof.PartyCode.of_noSalt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PartyCode.of_noSalt

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCompileProof.PartyCode.advance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PartyCode.advance

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCompileProof.compiled_executePhase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compiled_executePhase

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCompileProof.partyCode_check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms partyCode_check

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCompileProof.partyCode_ceremony' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms partyCode_ceremony

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCompileProof.compiled_treeRealGame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compiled_treeRealGame

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCompileProof.ceremonyBoundaryProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyBoundaryProgram

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCompileProof.ceremony_boundary_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremony_boundary_joint

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCompileProof.ceremony_boundary_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremony_boundary_logged

end TreeRawSaltCompileProof
end ThresholdLeanXmssSecurity
