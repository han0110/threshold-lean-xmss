import ThresholdLeanXmssSecurity.Proof.TreeSaltFirstStage

/-!
# The literal transport of the first stage

This module proves the exact `TreeSaltFirstStage.LiteralTransport` on the fixed compiled first
stage `firstCompiled`. With A130's reductions it gives the unconditional `crossFirstStage`,
`crossHiddenBound` and `pairBoundsGuardedFrom`, all at the unchanged `2^-256`.

## Truth audit

`LiteralTransport` is true for every boundary witness. Honest digest queries occur only in
`compareDigests`, at the salts of term reads. The prefix log has no free entry, and the setup
queries only `.commit` and `.sharedKeys`. A literal digest piece at the read salt of a hidden
entry `a` is counted on a `FirstClean` run, for these reasons.

* A known read of that salt at another stage-1 address is a reuse with `a`.
* A raw digest of the salt of `a` would need bits that the boundary witness never sees.

The argument below counts pieces, so it holds for every witness. It needs neither the shape of
the chosen witness nor a fresh salt.

## Steps

1. `witness` is a boundary witness of `firstProgram` with no raw honest digest. `PartyCode'` adds
   to `PartyCode` that ordinary local queries are not digests. Every ordinary segment has this
   property by the A13 zero-digest bounds (`partyCode'_after`). `witness_law` gives its law.
2. `source_provenance` and `source_count` state facts of every real stage view. For any address
   `a`, if `a` is the only address that reads the salt `v`, the free digests at `v` are at most
   the first-position reads of `a`. The proof decodes the view through `witness`. Its literal
   free digests have their salt read in literal pieces (`KS`), and literal pieces never hold a
   hidden salt read (`SafeLiterals`). In every row each block has as many digest pieces as draw
   pieces (`balanced_program`), and the setup log has no free digest.
3. `literalTransport` takes a reached `FirstClean` run of the fixed `firstCompiled` with an
   uncounted literal digest at the salt `w` of `a`.
   * Programming literals are impossible: real logs have no programming entry
     (`setup_noProgram`, `first_noProgram`).
   * Under `FirstClean`, `a` is the only address that reads `w`, because any other one is a
     stage-1 reuse.
   * In the fixed run the free digests at `w` number at least the digest pieces of `a`, plus one
     for the literal (`digests_ge`). The digest pieces of `a` equal its draw pieces
     (`balanced_program`, any witness), and these are at least the reads of `a`
     (`reads_le_draws`).
   * So the digests exceed the reads, against `source_count`.

The pinned and current leanVM proofs were searched; the grammar and the counts are specific to
the threshold salt compiler and reuse the A13 digest bounds and the A66 segment certificates.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity.TreeSaltLiteralTransport

open TreeSaltGuardedPairBound TreeSaltCrossCoupling TreeSaltFirstStage
open TreeRawSaltFlowProof TreeRawSaltRepresentationProof TreeRawSaltNormalizeProof
open TreeRawSaltCompileProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## Boundary programs with no raw honest digest -/

section Grammar

variable {E : Type} [Field E] [Algebra Bit E]

/-- A raw boundary query that is an honest digest. -/
def RawDigest (D : C.Coalition) : (BoundarySpec D).Domain → Prop
  | .inl _ => False
  | .inr t => TreeRawSaltCertificatesProof.HonestDigest t.1

/-- `Compiled` with a boundary witness that asks no raw honest digest. -/
def Compiled' (D : C.Coalition) {α : Type} (p : OracleComp (WorldSpec C) α) (P : α → Prop) : Prop :=
  ∃ q : OracleComp (BoundarySpec D) {a // P a},
    Subtype.val <$> simulateQ (boundarySource (E := E) D) q = p ∧ IsQueryBoundP q (RawDigest D) 0

theorem Compiled'.pure (D : C.Coalition) {α : Type} (a : α) (P : α → Prop) (ha : P a) :
    Compiled' (E := E) D (pure a) P :=
  ⟨Pure.pure ⟨a, ha⟩, by simp, isQueryBoundP_pure _ _ _⟩

theorem Compiled'.bind (D : C.Coalition) {α β : Type}
    {p : OracleComp (WorldSpec C) α} {P : α → Prop}
    {f : α → OracleComp (WorldSpec C) β} {Q : β → Prop}
    (hp : Compiled' (E := E) D p P)
    (hf : ∀ a, P a → Compiled' (E := E) D (f a) Q) :
    Compiled' (E := E) D (p >>= f) Q := by
  obtain ⟨q, hq, hb⟩ := hp
  choose next law bound using fun a : {a // P a} => hf a.1 a.2
  refine ⟨q >>= next, ?_, qb0_bind hb bound⟩
  simp only [simulateQ_bind, map_bind, law]
  rw [← bind_map_left, hq]

theorem Compiled'.map (D : C.Coalition) {α β : Type}
    {p : OracleComp (WorldSpec C) α} {P : α → Prop} (f : α → β) (Q : β → Prop)
    (hp : Compiled' (E := E) D p P) (hf : ∀ a, P a → Q (f a)) :
    Compiled' (E := E) D (f <$> p) Q := by
  simpa only [bind_pure_comp] using hp.bind D (fun a ha => Compiled'.pure D (f a) Q (hf a ha))

theorem Compiled'.public (D : C.Coalition) (t : (WorldSpec C).Domain)
    (safe : NoSaltRead D t) (hd : ¬ TreeRawSaltCertificatesProof.HonestDigest t) :
    Compiled' (E := E) D (OracleComp.lift (OracleSpec.query t)) (fun _ => True) := by
  refine ⟨(fun a => (⟨a, True.intro⟩ : {a : (WorldSpec C).Range t // True})) <$>
    (OracleComp.lift (OracleSpec.query (spec := BoundarySpec D) (.inr ⟨t, safe⟩))), ?_, ?_⟩
  · simp only [simulateQ_map, simulateQ_spec_query, boundarySource, Functor.map_map]
    exact id_map _
  · rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    exact fun h => (hd h).elim

theorem Compiled'.digest (D : C.Coalition) (ctx : Context C) (st : RunState C) :
    Compiled' (E := E) D (free (liftComp (treeSimHashSaltDigestDraw (E := E) ctx st) (LocalSpec C)))
      (fun _ => True) := by
  refine ⟨(fun a => (⟨a, True.intro⟩ : {a : List HashOutput // True})) <$>
    (OracleComp.lift (OracleSpec.query (spec := BoundarySpec D) (.inl (ctx, st)))), ?_, ?_⟩
  · simp only [simulateQ_map, simulateQ_spec_query, boundarySource, Functor.map_map]
    exact id_map _
  · rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
    exact fun h => h.elim

theorem Compiled'.sequenceFin (D : C.Coalition) {α : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp (WorldSpec C) α) (P : Fin n → α → Prop),
      (∀ i, Compiled' (E := E) D (f i) (P i)) →
      Compiled' (E := E) D (Concrete.sequenceFin f) (fun a => ∀ i, P i (a i))
  | 0, f, P, h => Compiled'.pure D _ _ (fun i => Fin.elim0 i)
  | n + 1, f, P, h => by
    unfold Concrete.sequenceFin
    exact (h 0).bind D fun a ha =>
      (Compiled'.sequenceFin D (fun i => f i.succ) (fun i => P i.succ) (fun i => h i.succ)).bind D
        fun as hs => Compiled'.pure D _ _ (fun i => Fin.cases ha hs i)

theorem Compiled'.adversary (D : C.Coalition) {α : Type} (p : OracleComp (LocalSpec C) α) :
    Compiled' (E := E) D (worldRoles.adversary p) (fun _ => True) := by
  induction p using OracleComp.inductionOn with
  | pure a => exact Compiled'.pure D a _ trivial
  | query_bind t k ih =>
    simp only [worldRoles, counted, liftComp_bind, simulateQ_bind]
    change Compiled' (E := E) D (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
      fun a => worldRoles.adversary (k a)) (fun _ => True)
    rw [adversary_query]
    exact (Compiled'.public D (.inl (.inl t)) trivial (fun h => h)).bind D (fun a _ => ih a)

/-- `PartyCode` whose ordinary local queries are not digests. -/
inductive PartyCode' (D : C.Coalition) {α : Type} :
    OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | pure (a : Option α) : PartyCode' D (pure a)
  | localQuery (t : (LocalSpec C).Domain) (safe : NoSaltRead D (.inr t)) (nd : ¬ DigestQuery t)
      (k : (LocalSpec C).Range t → OracleComp (PartySpec C E RealSpec) (Option α))
      (next : ∀ a, PartyCode' D (k a)) : PartyCode' D (.roll (.inl (.inl t)) k)
  | round (out : Mail C E)
      (k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α))
      (next : ∀ a, PartyCode' D (k a)) : PartyCode' D (.roll (.inl (.inr out)) k)
  | digest (ctx : Context C) (st : RunState C)
      (k : Unit × RunState C → PartyM C E RealSpec α)
      (next : ∀ a, PartyCode' D (k a).run) :
      PartyCode' D ((((prssRandomness ctx bitCodec 2 256 >>= fun rnd =>
        compareDigests ctx rnd.1).run st) >>= k).run)

theorem PartyCode'.bind (D : C.Coalition) {α β : Type}
    {p : PartyM C E RealSpec α} {k : α → PartyM C E RealSpec β}
    (hp : PartyCode' D p.run) (hk : ∀ a, PartyCode' D (k a).run) :
    PartyCode' D (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change PartyCode' D (p.run >>= fun a => a.elim (Pure.pure none) (fun a => (k a).run))
  generalize p.run = oa at hp ⊢
  induction hp with
  | pure a =>
    cases a with
    | none => simpa only [pure_bind, Option.elim_none, Option.elim_some] using
        PartyCode'.pure (D := D) (E := E) (none : Option β)
    | some a => simpa only [pure_bind, Option.elim_none, Option.elim_some] using hk a
  | localQuery t safe nd f next ih =>
    change PartyCode' D (.roll _ _)
    exact .localQuery t safe nd _ ih
  | round out f next ih =>
    change PartyCode' D (.roll _ _)
    exact .round out _ ih
  | digest ctx st f next ih =>
    have h := PartyCode'.digest (D := D) ctx st (fun a => f a >>= k)
      (fun a => by simpa only [OptionT.run_bind, Option.elimM] using ih a)
    simpa only [← bind_assoc, OptionT.run_bind, Option.elimM] using h

theorem PartyCode'.require (D : C.Coalition) (p : Prop) :
    PartyCode' (E := E) D (require (C := C) (E := E) (G := RealSpec) p).run := by
  unfold ThresholdLeanXmss.require
  split_ifs <;> exact .pure _

/-- An ordinary segment with no salt read and no digest query has the refined grammar. -/
theorem PartyCode'.of_segment (D : C.Coalition) {α : Type} {j n : ℕ}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)}
    (hp : TreeSegmentRun (fun _ _ _ _ => False) j n p)
    (hd : IsQueryBoundP p (PartyDigest (E := E) (G := RealSpec)) 0) : PartyCode' D p := by
  induction hp with
  | abort j n => exact .pure _
  | done j a => exact .pure _
  | round j n out k h ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
      (.inl (.inr out))) >>= k) _ 0 at hd
    rw [isQueryBoundP_query_bind_iff] at hd
    exact .round out k fun a => ih a (by simpa using hd.2 a)
  | queryLocal j n t k ht h ih =>
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
      (.inl (.inl t))) >>= k) _ 0 at hd
    rw [isQueryBoundP_query_bind_iff] at hd
    have nd : ¬ DigestQuery t := fun h' => by
      rcases hd.1 with h1 | h1
      · exact h1 h'
      · exact absurd h1 (Nat.lt_irrefl 0)
    refine PartyCode'.localQuery t ?_ nd k fun a => ih a (by simpa [PartyDigest, nd] using hd.2 a)
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

def StepCode' (D : C.Coalition) {α : Type} : Step C E RealSpec α → Prop
  | .done _ => True
  | .wait _ resume => ∀ inbox, PartyCode' D (resume inbox)
  | .call impossible _ => impossible.elim

theorem exchangeResume_code' (D : C.Coalition) {α : Type}
    (k : Mail C E → PartyM C E RealSpec α) (hk : ∀ inbox, PartyCode' D (k inbox).run)
    (inbox : Mail C E) : PartyCode' D (exchangeResume k inbox) := by
  unfold exchangeResume
  split_ifs
  · exact .pure _
  · exact hk inbox

theorem PartyCode'.advance (D : C.Coalition) (K : Constants C E) {α : Type}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (hp : PartyCode' D p) :
    Compiled' (E := E) D (free (advance p)) (StepCode' D) := by
  induction hp with
  | pure a =>
    exact Compiled'.pure D (Step.done a) _ trivial
  | localQuery t safe nd k next ih =>
    change Compiled' (E := E) D (free (OracleComp.lift (OracleSpec.query t) >>=
      fun a => ThresholdLeanXmss.advance (k a))) _
    rw [free_bind]
    exact (Compiled'.public D (.inr t) safe nd).bind D (fun a _ => ih a)
  | round out k next ih =>
    exact Compiled'.pure D (Step.wait out k) _ next
  | digest ctx st k next ih =>
    rw [show free (ThresholdLeanXmss.advance _) = _ from treeSimHash_salt_digest_entry K ctx st k]
    apply (Compiled'.digest (E := E) D ctx st).map D _ _
    intro ds _ inbox
    exact exchangeResume_code' D _ (fun inbox =>
      (PartyCode'.require D _).bind D (fun _ => next ((), nextLabel st))) _

theorem compiled'_roundLocal (D : C.Coalition) (K : Constants C E) {α : Type}
    (steps : C.Party → Step C E RealSpec α) (hs : ∀ i, StepCode' D (steps i))
    (sent : C.Party → Mail C E) (i : C.Party) :
    Compiled' (E := E) D (free (roundLocal D steps sent i)) (StepCode' D) := by
  unfold roundLocal
  have hi := hs i
  cases h : steps i with
  | done out => exact Compiled'.pure D _ _ trivial
  | call input k => exact input.elim
  | wait out k =>
    split_ifs
    · exact Compiled'.pure D _ _ trivial
    · rw [h] at hi
      exact PartyCode'.advance D K (hi _)

theorem compiled'_stepRound (D : C.Coalition) (K : Constants C E) {α : Type}
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (steps : C.Party → Step C E RealSpec α) (hs : ∀ i, StepCode' D (steps i)) :
    Compiled' (E := E) D (stepRound worldRoles D A noFunctionality state steps)
      (fun r => ∀ i, StepCode' D (r.2.1 i)) := by
  rw [stepRound_real]
  refine (Compiled'.adversary D _).bind D fun r _ => ?_
  dsimp only at *
  rw [free_sequenceFin]
  exact (Compiled'.sequenceFin D _ (fun _ => StepCode' D)
    (compiled'_roundLocal D K steps hs r.2)).bind D fun next hn =>
      Compiled'.pure D _ _ hn

theorem compiled'_executeSteps (D : C.Coalition) (K : Constants C E)
    (A : Adversary C E (Keys C) PEmpty PEmpty) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec TreeOutput),
      (∀ i, StepCode' D (steps i)) →
      Compiled' (E := E) D (executeSteps worldRoles D A noFunctionality fuel state steps)
        (fun r => ∀ i, StepCode' D (r.2 i))
  | 0, state, steps, hs => Compiled'.pure D _ _ hs
  | fuel + 1, state, steps, hs => by
    rw [executeSteps]
    split_ifs
    · exact Compiled'.pure D _ _ hs
    · refine (compiled'_stepRound D K A state steps hs).bind D fun r hr => ?_
      obtain ⟨st, sts, o⟩ := r
      exact compiled'_executeSteps D K A fuel st sts hr

theorem PartyCode'.map (D : C.Coalition) {α β : Type} (f : α → β)
    {p : PartyM C E RealSpec α} (hp : PartyCode' D p.run) :
    PartyCode' D (f <$> p).run := by
  rw [map_eq_bind_pure_comp]
  exact hp.bind D fun _ => .pure _

theorem PartyCode'.state_bind (D : C.Coalition) {σ α β : Type}
    {p : StateT σ (PartyM C E RealSpec) α} {k : α → StateT σ (PartyM C E RealSpec) β} {s : σ}
    (hp : PartyCode' D (p.run s).run)
    (hk : ∀ a s', PartyCode' D ((k a).run s').run) :
    PartyCode' D ((p >>= k).run s).run := by
  rw [StateT.run_bind]
  exact hp.bind D fun a => hk a.1 a.2

theorem PartyCode'.lift (D : C.Coalition) {σ α : Type} {p : PartyM C E RealSpec α}
    (hp : PartyCode' D p.run) (s : σ) :
    PartyCode' D ((StateT.lift p : StateT σ (PartyM C E RealSpec) α).run s).run := by
  rw [StateT.run_lift]
  exact hp.bind D fun _ => .pure _

theorem PartyCode'.foldlM (D : C.Coalition) {σ α β : Type}
    (f : α → β → StateT σ (PartyM C E RealSpec) α)
    (hf : ∀ a b s, PartyCode' D ((f a b).run s).run) :
    ∀ (xs : List β) (a : α) (s : σ), PartyCode' D ((xs.foldlM f a).run s).run
  | [], a, s => .pure _
  | b :: xs, a, s => by
    rw [List.foldlM_cons]
    exact (hf a b s).state_bind D fun a' s' => PartyCode'.foldlM D f hf xs a' s'

theorem PartyCode'.state_mapM (D : C.Coalition) {σ α β : Type}
    (f : α → StateT σ (PartyM C E RealSpec) β)
    (hf : ∀ a s, PartyCode' D ((f a).run s).run) :
    ∀ (xs : List α) (s : σ), PartyCode' D ((xs.mapM f).run s).run
  | [], s => .pure _
  | a :: xs, s => by
    rw [List.mapM_cons]
    exact (hf a s).state_bind D fun b s' =>
      (PartyCode'.state_mapM D f hf xs s').state_bind D fun bs s'' => .pure _

theorem PartyCode'.digest_tail (D : C.Coalition) (ctx : Context C) (st : RunState C)
    {α : Type} (tail : RunM C E RealSpec α)
    (ht : ∀ s, PartyCode' D (tail.run s).run) :
    PartyCode' D ((do
      let salts ← prssRandomness ctx bitCodec 2 256
      compareDigests ctx salts.1
      tail).run st).run := by
  rw [← bind_assoc, StateT.run_bind]
  exact .digest ctx st _ (fun a => ht a.2)

end Grammar

/-! ## The actual honest programs have the refined grammar -/

section Honest

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (D : C.Coalition) (K : Constants C E) (circuits : Circuits) (settings : Settings)

theorem partyCode'_finalStep (ctx : Context C) (p : (ℕ → E) × (ℕ → E) × E) (st : RunState C) :
    PartyCode' D ((finalStep K ctx (realCheckGadgets K ctx) p).run st).run := by
  have hg := treeSimHash_real_gadgets_digest (G := RealSpec) K ctx
  rcases p with ⟨a, b, d⟩
  unfold finalStep
  refine (PartyCode'.of_segment D (treeSegmentRun_prssRandomness ctx (elementCodec K)
    (fun _ => elementCodec_salts K) 1 2 0 st (by omega)) (hg.elements 2 st)).state_bind D
    fun w s1 => ?_
  refine (PartyCode'.of_segment D (treeSegmentRun_extendMult K ctx _ 0 s1) (hg.mult _ s1)).state_bind D
    fun q s2 => ?_
  apply PartyCode'.digest_tail D ctx s2
  intro s3
  refine (PartyCode'.of_segment D (treeSegmentRun_challenge K ctx 0 s3)
    (treeSimHash_challenge_digest K _ hg s3)).state_bind D fun r s4 => ?_
  refine ((PartyCode'.of_segment D (treeSegmentRun_openSh K ctx _ 3 0)
    (RunBound.openSh K ctx _ 3).to_digest).lift D s4).state_bind D fun opened s5 => ?_
  exact (PartyCode'.require D _).lift D s5

theorem partyCode'_check (ctx : Context C) (tuples : List (Tuple C)) (st : RunState C) :
    PartyCode' D ((check K ctx (realCheckGadgets K ctx) tuples).run st).run := by
  have hg := treeSimHash_real_gadgets_digest (G := RealSpec) K ctx
  by_cases hz : (tuples.map (·.count)).sum = 0
  · simp only [check, hz, ↓reduceIte]
    exact .pure _
  rw [check_eq K ctx _ tuples hz]
  refine (PartyCode'.of_segment D (treeSegmentRun_coinKey K ctx 0 st)
    (treeSimHash_coinKey_digest K _ hg st)).state_bind D fun key s1 => ?_
  refine (PartyCode'.of_segment D (treeSegmentRun_expand K key _ 0 s1)
    (treeSimHash_expand_digest K key _ s1)).state_bind D fun τ s2 => ?_
  refine ((PartyCode'.require D _).lift D s2).state_bind D fun _ s3 => ?_
  refine (PartyCode'.foldlM D _ (fun p j s => ?_) _ _ s3).state_bind D fun p s4 => ?_
  · rcases p with ⟨a, b, d⟩
    unfold sliceStep
    exact (PartyCode'.of_segment D (treeSegmentRun_extendMult K ctx _ 0 s) (hg.mult _ s)).state_bind D
      fun t s' => (PartyCode'.of_segment D (treeSegmentRun_challenge K ctx 0 s')
        (treeSimHash_challenge_digest K _ hg s')).state_bind D fun r s'' => .pure _
  refine (PartyCode'.foldlM D _ (fun p j s => ?_) _ _ s4).state_bind D fun p s5 => ?_
  · rcases p with ⟨a, b, d⟩
    unfold halvingStep
    exact (PartyCode'.of_segment D (treeSegmentRun_extendMult K ctx _ 0 s) (hg.mult _ s)).state_bind D
      fun t s' => (PartyCode'.of_segment D (treeSegmentRun_challenge K ctx 0 s')
        (treeSimHash_challenge_digest K _ hg s')).state_bind D fun r s'' => .pure _
  exact partyCode'_finalStep D K ctx p s5

theorem beforeVerify_digest (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    TreeSimHashDigestRunBound (treeSimCheckBeforeVerify K ctx mode jobs inputs) 0 := by
  have hm : ∀ x y count, TreeSimHashDigestRunBound
      ((realRunGadgets K ctx mode : RunGadgets C E RealSpec).mult x y count) 0 := by
    intro x y count
    change TreeSimHashDigestRunBound (prssRandomness ctx bitCodec 0 count >>= _) 0
    exact (treeSimHash_prss_digest ctx bitCodec treeSimHash_prg_digest 0 count).bind
      (m := 0) (fun r => treeSimHash_reshareWith_digest K ctx mode r _ count)
  have hr : ∀ v count, TreeSimHashDigestRunBound
      ((realRunGadgets K ctx mode : RunGadgets C E RealSpec).rerand v count) 0 := by
    intro v count
    change TreeSimHashDigestRunBound (prssRandomness ctx bitCodec 0 count >>= _) 0
    exact (treeSimHash_prss_digest ctx bitCodec treeSimHash_prg_digest 0 count).bind
      (m := 0) (fun r => treeSimHash_reshare_no_digest K ctx _ r _ count)
  unfold treeSimCheckBeforeVerify
  refine ((TreeSimHashDigestRunBound.foldlM _ 0 (fun v layer => ?_) _ _).bind (fun p =>
    (hr _ _).bind (fun v => TreeSimHashDigestRunBound.pure _ 0))).mono ?_
  · exact (hm _ _ _).bind (m := 0) (fun z => TreeSimHashDigestRunBound.pure _ 0)
  · simp

theorem partyCode'_ceremonyBatch (ctx : Context C) (jobs : List Job) (initial : ℕ × ℕ) :
    PartyCode' D ((ceremonyBatch K circuits settings ctx jobs :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run initial).run := by
  rw [← treeSimCheckBatchAudit_erase K circuits settings ctx jobs]
  change PartyCode' D ((Prod.fst <$> (treeSimCheckBatchAudit K circuits settings ctx jobs).run).run
    initial).run
  rw [StateT.run_map, treeSimCheckBatchAudit_run_prefix]
  apply PartyCode'.map
  have hp : PartyCode' D (treeSimCheckBatchPrefix K circuits settings ctx jobs initial).run := by
    apply PartyCode'.of_segment D
    · unfold treeSimCheckBatchPrefix
      exact treeSegmentRun_inputs ctx 0 _ jobs _ fun inputs =>
        (treeSegmentRun_beforeVerify K ctx settings.mode _ inputs 0 _).bind fun _ _ =>
          TreeSegmentRun.pure _ _
    · have hi : DigestPartyBound (jobs.mapM (inputShares ctx) : PartyM C E RealSpec _) 0 := by
        simpa using treeSimHash_party_mapM_digest (inputShares ctx) 0
          (treeSimHash_inputShares_digest ctx) jobs
      unfold treeSimCheckBatchPrefix
      exact (hi.bind (m := 0) fun inputs => (beforeVerify_digest K ctx settings.mode _ inputs _).bind
        (m := 0) fun _ => DigestPartyBound.pure _)
  refine hp.bind D fun a => ?_
  unfold treeSimCheckBatchFinish treeSimCheckAfterVerify
  refine ((partyCode'_check D K ctx a.2.1.2 a.2.2).bind D fun x => ?_).bind D fun _ => .pure _
  rcases x with ⟨_, final⟩
  exact (PartyCode'.of_segment D (treeSegmentRun_openRep K ctx _ _ 0)
    (treeSimHash_openRep_digest K ctx _ _)).bind D fun _ => .pure _

theorem partyCode'_batched (ctx : Context C) (jobs : List Job) (s : ℕ × ℕ) :
    PartyCode' D ((batched settings.batchSize (ceremonyBatch K circuits settings ctx) jobs :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run s).run := by
  unfold batched
  exact (PartyCode'.state_mapM D _ (partyCode'_ceremonyBatch D K circuits settings ctx) _ s).state_bind D
    fun _ _ => .pure _

theorem partyCode'_tweakable {δ : Type} (oa : OracleComp HashSpec δ) (j : ℕ) (s : ℕ × ℕ) :
    PartyCode' D ((StateT.lift (oracleStep (tweakable oa)) :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) δ).run s).run :=
  PartyCode'.of_segment D (treeSegmentRun_tweakable _ j s)
    (TreeSimHashDigestRunBound.lift (treeSimHash_oracle_digest (treeSimHash_tweakable_digest oa)) s)

theorem partyCode'_ceremonyOutput (ctx : Context C) (top : TopTree) (tree : Tree) (s : ℕ × ℕ) :
    PartyCode' D ((ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) ctx.keys.parameter
      (batched settings.batchSize (ceremonyBatch K circuits settings ctx)) top tree).run s).run := by
  cases tree with
  | top =>
    simp only [ceremonyOutput]
    refine (partyCode'_batched D K circuits settings ctx _ s).state_bind D fun r s' => ?_
    rcases r with _ | outputs
    · exact .pure _
    exact (partyCode'_tweakable D _ 0 s').state_bind D fun _ _ => .pure _
  | bottom b =>
    simp only [ceremonyOutput]
    refine (partyCode'_batched D K circuits settings ctx _ s).state_bind D fun r s' => ?_
    rcases r with _ | outputs
    · exact .pure _
    refine (partyCode'_tweakable D _ 0 s').state_bind D fun root s1 => ?_
    refine (partyCode'_tweakable D _ 0 s1).state_bind D fun base s2 => ?_
    refine (partyCode'_tweakable D _ 0 s2).state_bind D fun g s3 => ?_
    rcases g with _ | ⟨randomness, encoding⟩
    · exact .pure _
    refine (partyCode'_batched D K circuits settings ctx _ s3).state_bind D fun v s4 => ?_
    rcases v with _ | values
    · exact .pure _
    refine (partyCode'_tweakable D _ 0 s4).state_bind D fun path s5 => ?_
    refine (partyCode'_tweakable D _ 0 s5).state_bind D fun root' s6 => ?_
    split_ifs <;> exact .pure _

theorem partyCode'_after (i : C.Party) (keys : Keys C) (prss : PrssKeys C) (top : TopTree)
    (tree : Tree) :
    PartyCode' D
      (ceremonyAfterSetup K circuits settings ⟨i, keys, prss⟩ top tree : PartyM C E RealSpec TreeOutput).run := by
  unfold ceremonyAfterSetup
  refine PartyCode'.bind D ?_ fun out => ?_
  · rw [StateT.run'_eq]
    exact (partyCode'_ceremonyOutput D K circuits settings ⟨i, keys, prss⟩ top tree (0, 0)).map D _
  · cases out <;> exact .pure _

end Honest

/-! ## A witness of the first stage with no raw honest digest -/

section Witness

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

theorem compiled'_continue (D : C.Coalition) (top : TopTree) (tree : Tree) (x : C.Party → Keys C)
    (keys : C.Party → Option (PrssKeys C)) :
    Compiled' (E := E) D (treeSimContinue (treeSimRealCont K circuits settings top tree x) keys)
      (fun steps => ∀ i, StepCode' D (steps i)) := by
  unfold treeSimContinue
  rw [free_sequenceFin]
  refine Compiled'.sequenceFin D _ (fun _ => StepCode' D) fun i => ?_
  cases hk : keys i with
  | none => exact Compiled'.pure D _ _ trivial
  | some prss =>
    simp only [continueStep]
    exact PartyCode'.advance D K (partyCode'_after D K circuits settings i (x i) prss top tree)

theorem compiled'_first (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    Compiled' (E := E) D (firstProgram K circuits settings top tree D A x p)
      (fun r => ∀ i, StepCode' D (r.2 i)) :=
  (compiled'_continue K circuits settings D top tree x p.1.2).bind D fun next hn =>
    compiled'_executeSteps D K A _ p.1.1 next hn

theorem dropPrograms_raw {α : Type} (D : C.Coalition) (q : OracleComp (BoundarySpec D) α)
    (h : IsQueryBoundP q (RawDigest D) 0) :
    IsQueryBoundP (simulateQ (boundaryDropPrograms D) q) (RawDigest D) 0 := by
  induction q using OracleComp.inductionOn with
  | pure a => simp only [simulateQ_pure]; exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ RawDigest D t := by
      rcases h.1 with h1 | h1
      · exact h1
      · exact absurd h1 (Nat.lt_irrefl 0)
    simp only [simulateQ_bind, simulateQ_spec_query]
    apply qb0_bind _ (fun a => ih a (by simpa [ht] using h.2 a))
    rcases t with row | ⟨t, safe⟩
    · simp only [boundaryDropPrograms]
      rw [isQueryBoundP_query_iff]
      exact fun h' => (ht h').elim
    · rcases t with (t | t) | t
      · simp only [boundaryDropPrograms]
        rw [isQueryBoundP_query_iff]
        exact fun h' => (ht h').elim
      · simp only [boundaryDropPrograms]
        exact isQueryBoundP_pure _ _ _
      · simp only [boundaryDropPrograms]
        rw [isQueryBoundP_query_iff]
        exact fun h' => (ht h').elim

/-- The witness: a boundary program of the first stage with no raw honest digest. -/
def witness (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    OracleComp (BoundarySpec D) (FirstView A) :=
  simulateQ (boundaryDropPrograms D)
    (Subtype.val <$> Classical.choose (compiled'_first K circuits settings top tree D A x p))

theorem witness_source (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    simulateQ (boundarySource (E := E) D) (witness K circuits settings top tree D A x p) =
      firstProgram K circuits settings top tree D A x p := by
  unfold witness
  rw [boundaryDropPrograms_program, simulateQ_map,
    (Classical.choose_spec (compiled'_first K circuits settings top tree D A x p)).1]
  exact dropPrograms_eq _ (first_noProgram K circuits settings top tree D A x p)

theorem witness_raw (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) :
    IsQueryBoundP (witness K circuits settings top tree D A x p) (RawDigest D) 0 := by
  unfold witness
  apply dropPrograms_raw
  rw [isQueryBoundP_map_iff]
  exact (Classical.choose_spec (compiled'_first K circuits settings top tree D A x p)).2

/-- The first stage has the law of the compiled witness. -/
theorem witness_law (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hopen : ∀ y, (saltAt y).isSome → p.2.1.2 y = none) (used : SaltLists) :
    𝒟[TreeSaltPairsFinal.first prims K circuits settings top tree D A x p] =
      𝒟[decodeResult <$> tableRun prims ((simulateQ (boundaryCompiler D)
        (witness K circuits settings top tree D A x p)).run (p.2.1.2, p.2.2.map .literal))
        used p.2.1.1 ∅] := by
  have ready : Ready p.2.1.1 ∅ ((p.2.1.2, p.2.2.map .literal) : CompilerState C) := by
    intro piece hp
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hp
    trivial
  have h := compiler_program_law (E := E) prims D (TreeRawSaltStepsProof.boundaryCompilerSteps prims D)
    (witness K circuits settings top tree D A x p) (boundaryDropPrograms_safe D _)
    used p.2.1.1 ∅ _ ready
  rw [witness_source, decode_start _ _ _ hopen] at h
  rw [first_eq]
  exact h

end Witness

/-! ## Known reads behind the literal digests of the witness -/

section Known

variable (prims : Primitives)

theorem free_liftComp_query (y : PrgInput C) :
    free (liftComp (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inr y))) (LocalSpec C)) =
      OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inr y)))) := by
  rfl

theorem publicDraw_eq (D : C.Coalition) (name : KeyName C) (key : HashOutput) (label : ℕ) :
    publicDraw D name key label = (fun bits => fun g => bits.getD g 0) <$>
      (List.range 256).mapM (fun pos => publicQuery D (.inr (.inr (.inr (name, key, label, 2, pos))))) := by
  have hm : ∀ xs : List ℕ, simulateQ (publicQuery D) (free (liftComp (xs.mapM fun position =>
      (query (spec := RoSpec C) (.inr (name, key, label, 2, position)) : OracleComp (RoSpec C) Bit))
        (LocalSpec C))) =
      xs.mapM (fun pos => publicQuery D (.inr (.inr (.inr (name, key, label, 2, pos))))) := by
    intro xs
    induction xs with
    | nil => simp [free]
    | cons x xs ih =>
      simp only [List.mapM_cons, liftComp_bind, free_bind, simulateQ_bind, ih, liftComp_pure,
        free_pure, simulateQ_pure]
      congr 1
      change simulateQ (publicQuery D) (free (liftComp (OracleComp.lift (OracleSpec.query
        (spec := RoSpec C) (.inr (name, key, label, 2, x)))) (LocalSpec C))) = _
      rw [free_liftComp_query, simulateQ_spec_query]
  unfold publicDraw prgBits
  simp only [liftComp_bind, free_bind, simulateQ_bind, hm, liftComp_pure, free_pure, simulateQ_pure,
    map_eq_bind_pure_comp]
  rfl

/-- The literal log pieces hold the 256 reads of `salt` at one term address. -/
def ReadSalt (st : CompilerState C) (salt : List Bit) : Prop :=
  ∃ c : C.Term × HashOutput × ℕ, ∀ g : Fin 256,
    LogPiece.literal ⟨.inr (.inr (.inr (.term c.1, c.2.1, c.2.2, 2, g.val))), salt.getD g.val 0⟩ ∈ st.2

/-- Every literal free digest, and every salt of `L`, is empty or read in literal pieces. -/
def KS (L : List (List Bit)) (st : CompilerState C) (_used : SaltLists) : Prop :=
  (∀ s hh d, LogPiece.literal ⟨.inr (.inr (.inl (.digest s hh))), d⟩ ∈ st.2 → s = [] ∨ ReadSalt st s) ∧
    ∀ s ∈ L, s = [] ∨ ReadSalt st s

theorem ReadSalt.mono {st st' : CompilerState C} (h : ∀ x ∈ st.2, x ∈ st'.2) {salt : List Bit}
    (hr : ReadSalt st salt) : ReadSalt st' salt := by
  obtain ⟨c, hc⟩ := hr
  exact ⟨c, fun g => h _ (hc g)⟩

/-- A piece that is not a literal free digest keeps `KS`. -/
def NotFreeDigest : LogPiece C → Prop
  | .literal e => ∀ s hh d, e ≠ ⟨.inr (.inr (.inl (.digest s hh))), d⟩
  | _ => True

theorem KS.append {L : List (List Bit)} {st : CompilerState C} {used used' : SaltLists}
    (h : KS L st used) (other : HiddenCache C) (piece : LogPiece C) (hp : NotFreeDigest piece) :
    KS L (other, st.2 ++ [piece]) used' := by
  have mono : ∀ x ∈ st.2, x ∈ (other, st.2 ++ [piece]).2 := fun x hx => List.mem_append_left _ hx
  refine ⟨fun s hh d hm => ?_, fun s hs => (h.2 s hs).imp id (ReadSalt.mono mono)⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact (h.1 s hh d hm).imp id (ReadSalt.mono mono)
  · rw [List.mem_singleton] at hm
    subst hm
    exact (hp s hh d rfl).elim

theorem publicQuery_log (D : C.Coalition) (t : (WorldSpec C).Domain) (st : CompilerState C)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C) r
    (hr : r ∈ support (tableRun prims ((publicQuery D t).run st) used cache blocks)) :
    r.1.1.2.2 = st.2 ++ [.literal ⟨t, r.1.1.1⟩] := by
  simp only [publicQuery, StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hr
  obtain ⟨mid, hm, hr⟩ := hr
  simp only [emit, StateT.run_modify, StateT.run_pure,
    tableRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
  obtain ⟨_, rfl, rfl⟩ := hr
  rw [TreeRawSaltCertificatesProof.publicAnswer_log prims D t st used cache blocks mid hm]

theorem ks_publicQuery (L : List (List Bit)) (D : C.Coalition) (t : (WorldSpec C).Domain)
    (ht : ∀ s hh, t ≠ .inr (.inr (.inl (.digest s hh)))) :
    TreeRawSaltCertificatesProof.Preserves prims (KS L) (publicQuery D t) := by
  intro st used cache blocks h r hr
  have hl := publicQuery_log prims D t st used cache blocks r hr
  have e : r.1.1.2 = (r.1.1.2.1, st.2 ++ [.literal ⟨t, r.1.1.1⟩]) := by
    rw [← hl]
  rw [e]
  refine h.append _ _ ?_
  intro s hh d he
  have := congrArg Sigma.fst he
  exact ht s hh this

theorem ks_emit (L : List (List Bit)) (piece : LogPiece C) (hp : NotFreeDigest piece) :
    TreeRawSaltCertificatesProof.Preserves prims (KS L) (emit piece) := by
  intro st used cache blocks h r hr
  simp only [emit, StateT.run_modify, tableRun, simulateQ_pure, StateT.run_pure,
    mem_support_pure_iff] at hr
  subst r
  exact h.append _ _ hp

theorem ks_lift (L : List (List Bit)) {α : Type} (p : OracleComp (TableSpec C) α) :
    TreeRawSaltCertificatesProof.Preserves prims (KS L) (StateT.lift p : CompilerM C α) := by
  intro st used cache blocks h r hr
  simp only [StateT.run_lift, bind_pure_comp, tableRun_map, support_map, Set.mem_image] at hr
  obtain ⟨out, _, rfl⟩ := hr
  exact ⟨h.1, h.2⟩

theorem ks_publicDraw (L : List (List Bit)) (D : C.Coalition) (name : KeyName C) (key : HashOutput)
    (label : ℕ) : TreeRawSaltCertificatesProof.Preserves prims (KS L) (publicDraw D name key label) := by
  rw [publicDraw_eq]
  exact (TreeRawSaltCertificatesProof.Preserves.mapM prims _ _ fun pos =>
    ks_publicQuery prims L D (.inr (.inr (.inr (name, key, label, 2, pos))))
      (fun s hh h => by simp only [Sum.inr.injEq, reduceCtorEq] at h)).map prims _ _

/-- The bits of a public read sequence are logged as literal pieces. -/
theorem reads_mapM (D : C.Coalition) (y : ℕ → PrgInput C) :
    ∀ (xs : List ℕ) (st : CompilerState C) (used : SaltLists) (cache : HashCache C)
      (blocks : BlockCache C) r,
    r ∈ support (tableRun prims ((xs.mapM fun pos =>
      (publicQuery D (.inr (.inr (.inr (y pos)))) : CompilerM C Bit)).run st) used cache blocks) →
    r.1.1.1.length = xs.length ∧ (∀ x ∈ st.2, x ∈ r.1.1.2.2) ∧
      ∀ i (hi : i < xs.length), (hr : i < r.1.1.1.length) →
        LogPiece.literal ⟨.inr (.inr (.inr (y xs[i]))), r.1.1.1[i]⟩ ∈ r.1.1.2.2
  | [], st, used, cache, blocks, r, hr => by
    simp only [List.mapM_nil, StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hr
    subst hr
    exact ⟨rfl, fun x hx => hx, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | x :: xs, st, used, cache, blocks, r, hr => by
    simp only [List.mapM_cons, StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hm, hr⟩ := hr
    obtain ⟨rest, hrest, hr⟩ := hr
    simp only [StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hr
    subst hr
    have hl := publicQuery_log prims D (.inr (.inr (.inr (y x)))) st used cache blocks mid hm
    obtain ⟨len, grow, at_i⟩ := reads_mapM D y xs _ _ _ _ rest hrest
    refine ⟨by simp [len], fun z hz => grow z (by rw [hl]; exact List.mem_append_left _ hz), ?_⟩
    intro i hi hr
    cases i with
    | zero =>
      exact grow _ (by rw [hl]; exact List.mem_append_right _ (List.mem_singleton_self _))
    | succ i =>
      exact at_i i (by simpa using hi) (by simpa using hr)

theorem publicDraw_read (D : C.Coalition) (T : C.Term) (key : HashOutput) (label : ℕ)
    (st : CompilerState C) (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C) r
    (hr : r ∈ support (tableRun prims ((publicDraw D (.term T) key label).run st) used cache blocks)) :
    ReadSalt r.1.1.2 (vector 256 r.1.1.1) := by
  rw [publicDraw_eq, StateT.run_map, tableRun_map, support_map] at hr
  obtain ⟨z, hz, rfl⟩ := hr
  obtain ⟨len, -, at_i⟩ := reads_mapM prims D (fun pos => (.term T, key, label, 2, pos))
    (List.range 256) st used cache blocks z hz
  refine ⟨(T, key, label), fun g => ?_⟩
  have hg : g.val < (List.range 256).length := by simp
  have hz' : g.val < z.1.1.1.length := by rw [len]; exact hg
  have := at_i g.val hg hz'
  have hidx : (List.range 256)[g.val] = g.val := List.getElem_range _
  have hv : (vector 256 (fun g => z.1.1.1.getD g 0)).getD g.val 0 = z.1.1.1[g.val] := by
    unfold vector
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range,
      List.getD_eq_getElem _ _ hz']
  rw [hidx] at this
  show LogPiece.literal ⟨.inr (.inr (.inr (.term T, key, label, 2, g.val))),
    (vector 256 (fun g => z.1.1.1.getD g 0)).getD g.val 0⟩ ∈ _
  rw [hv]
  exact this

theorem KS.mono_list {L L' : List (List Bit)} {st : CompilerState C} {used : SaltLists}
    (h : KS L st used) (hL : ∀ s ∈ L', s ∈ L) : KS L' st used :=
  ⟨h.1, fun s hs => h.2 s (hL s hs)⟩

theorem ks_publicQuery_digest (L : List (List Bit)) (D : C.Coalition) (salt : List Bit)
    (hh : HashOutput) (hs : salt ∈ L ∨ salt = []) :
    TreeRawSaltCertificatesProof.Preserves prims (KS L)
      (publicQuery D (.inr (.inr (.inl (.digest salt hh))))) := by
  intro st used cache blocks h r hr
  have hl := publicQuery_log prims D _ st used cache blocks r hr
  have mono : ∀ x ∈ st.2, x ∈ r.1.1.2.2 := fun x hx => by rw [hl]; exact List.mem_append_left _ hx
  refine ⟨fun s hh' d hm => ?_, fun s hs' => (h.2 s hs').imp id (ReadSalt.mono mono)⟩
  rw [hl] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact (h.1 s hh' d hm).imp id (ReadSalt.mono mono)
  · rw [List.mem_singleton] at hm
    have he := congrArg (fun p => match p with
      | LogPiece.literal e => some e.1
      | _ => none) hm
    simp only [Option.some.injEq, Sum.inr.injEq, Sum.inl.injEq, Query.digest.injEq] at he
    obtain ⟨rfl, -⟩ := he
    rcases hs with hs | hs
    · exact (h.2 _ hs).imp id (ReadSalt.mono mono)
    · exact Or.inl hs

/-- The salts of the known rows of a term list. -/
def rowSalts (terms : List (Salt C)) : List (List Bit) :=
  terms.filterMap fun x => match x with
    | .inr s => some s
    | .inl _ => none

theorem rowSalts_cons (x : Salt C) (xs : List (Salt C)) :
    rowSalts (x :: xs) = rowSalts [x] ++ rowSalts xs := by
  rcases x with b | salt <;> simp [rowSalts]

theorem prepare_mapM (D : C.Coalition) (ctx : Context C) (label : ℕ) :
    ∀ (xs : List C.Term) (L : List (List Bit)) (st : CompilerState C) (used : SaltLists)
      (cache : HashCache C) (blocks : BlockCache C), KS L st used →
    ∀ r ∈ support (tableRun prims ((xs.mapM (prepareTerm D ctx label)).run st) used cache blocks),
      KS (L ++ rowSalts r.1.1.1) r.1.1.2 r.1.2
  | [], L, st, used, cache, blocks, h, r, hr => by
    simp only [List.mapM_nil, StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hr
    subst hr
    simpa [rowSalts] using h
  | T :: xs, L, st, used, cache, blocks, h, r, hr => by
    simp only [List.mapM_cons, StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hm, hr⟩ := hr
    obtain ⟨rest, hrest, hr⟩ := hr
    simp only [StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hr
    subst hr
    have step : KS (L ++ rowSalts [mid.1.1.1]) mid.1.1.2 mid.1.2 := by
      unfold prepareTerm at hm
      split_ifs at hm with held known
      · rw [StateT.run_map, tableRun_map, support_map] at hm
        obtain ⟨z, hz, rfl⟩ := hm
        have hks := ks_publicDraw prims L D _ _ _ st used cache blocks h z hz
        refine ⟨hks.1, fun s hs => ?_⟩
        rcases List.mem_append.mp hs with hs | hs
        · exact hks.2 s hs
        · simp only [rowSalts, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hs
          subst hs
          exact Or.inr (publicDraw_read prims D T _ _ st used cache blocks z hz)
      · simp only [StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hm
        obtain ⟨e, he, hm⟩ := hm
        have hks := ks_emit prims L (.draw (T, ctx.prss.term T, label)) trivial st used cache blocks h e he
        simp only [StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hm
        subst hm
        simpa [rowSalts] using hks
      · simp only [StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hm
        subst hm
        refine ⟨h.1, fun s hs => ?_⟩
        rcases List.mem_append.mp hs with hs | hs
        · exact h.2 s hs
        · simp only [rowSalts, List.filterMap_cons, List.filterMap_nil, List.mem_singleton] at hs
          exact Or.inl hs
    have := prepare_mapM D ctx label xs _ _ _ _ _ step rest hrest
    refine this.mono_list fun s hs => ?_
    rw [rowSalts_cons, ← List.append_assoc] at hs
    exact hs

theorem ks_preparePairs (L : List (List Bit)) (D : C.Coalition) (ctx : Context C) (label : ℕ) :
    TreeRawSaltCertificatesProof.Preserves prims (KS L) (preparePairs D ctx label) := by
  unfold preparePairs
  refine TreeRawSaltCertificatesProof.Preserves.bind prims (I := KS L) _ _ ?_ ?_
  · apply TreeRawSaltCertificatesProof.Preserves.mapM prims (I := KS L)
    intro j
    split_ifs
    · exact TreeRawSaltCertificatesProof.Preserves.pure prims _
    · exact ks_publicDraw prims L D _ _ _
  · intro _
    exact TreeRawSaltCertificatesProof.Preserves.pure prims _

theorem ks_compileDigest (L : List (List Bit)) (D : C.Coalition) (row : Row C)
    (hrow : ∀ salt, row.1 = .inr salt → salt ∈ L ∨ salt = []) :
    TreeRawSaltCertificatesProof.Preserves prims (KS L) (compileDigest D row) := by
  rcases row with ⟨b | salt, history⟩
  · exact (ks_lift prims L _).bind prims _ _ (fun output =>
      (ks_emit prims L (.digest b history output) trivial).bind prims _ _
        (fun _ => TreeRawSaltCertificatesProof.Preserves.pure prims _))
  · simp only [compileDigest, oneDigestQuery, liftComp_bind, free_bind, simulateQ_bind,
      TreeRawSaltCertificatesProof.free_hash_query, simulateQ_spec_query]
    exact (ks_publicQuery prims L D _ (fun s hh h => by
      simp only [Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at h)).bind prims _ _ fun hh =>
      ks_publicQuery_digest prims L D salt hh (hrow salt rfl)

theorem ks_row (D : C.Coalition) (ctx : Context C) (st : RunState C) :
    TreeRawSaltCertificatesProof.Preserves prims (KS []) (compileBoundaryDigest D ctx st) := by
  intro state used cache blocks h r hr
  unfold compileBoundaryDigest at hr
  simp only [StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hr
  obtain ⟨t1, h1, t2, h2, hr⟩ := hr
  have k1 := prepare_mapM prims D ctx st.label C.terms [] state used cache blocks h t1 h1
  simp only [List.nil_append] at k1
  have k2 := ks_preparePairs prims (rowSalts t1.1.1.1) D ctx st.label _ _ _ _ k1 t2 h2
  have k3 := TreeRawSaltCertificatesProof.Preserves.mapM prims (I := KS (rowSalts t1.1.1.1)) C.terms
    (fun T => if ctx.self ∈ C.holders T then
      compileDigest D (t1.1.1.1.getD (C.terms.idxOf T) (.inr []), st.history T) else pure 0)
    (fun T => by
      split_ifs
      · refine ks_compileDigest prims _ D _ fun salt hs => ?_
        simp only at hs
        rw [List.getD_eq_getElem?_getD] at hs
        cases hx : t1.1.1.1[C.terms.idxOf T]? with
        | none =>
          rw [hx] at hs
          simp only [Option.getD_none, Sum.inr.injEq] at hs
          exact Or.inr hs.symm
        | some x =>
          rw [hx] at hs
          simp only [Option.getD_some] at hs
          subst hs
          left
          exact List.mem_filterMap.mpr ⟨_, List.mem_of_getElem? hx, rfl⟩
      · exact TreeRawSaltCertificatesProof.Preserves.pure prims _) _ _ _ _ k2 r hr
  exact k3.mono_list (fun s hs => absurd hs List.not_mem_nil)

/-- The compiled witness keeps every literal free digest at a literal read, or empty. -/
theorem ks_program {α : Type} (D : C.Coalition) (q : OracleComp (BoundarySpec D) α)
    (hq : IsQueryBoundP q (RawDigest D) 0) :
    TreeRawSaltCertificatesProof.Preserves prims (KS []) (simulateQ (boundaryCompiler D) q) := by
  induction q using OracleComp.inductionOn with
  | pure a => simpa using TreeRawSaltCertificatesProof.Preserves.pure prims a
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hq
    have ht : ¬ RawDigest D t := by
      rcases hq.1 with h1 | h1
      · exact h1
      · exact absurd h1 (Nat.lt_irrefl 0)
    simp only [simulateQ_bind, simulateQ_spec_query]
    refine TreeRawSaltCertificatesProof.Preserves.bind prims _ _ ?_
      (fun a => ih a (by simpa [ht] using hq.2 a))
    rcases t with ⟨ctx, st⟩ | ⟨t, safe⟩
    · exact ks_row prims D ctx st
    · refine ks_publicQuery prims [] D t fun s hh he => ht ?_
      subst he
      simp [RawDigest, TreeRawSaltCertificatesProof.HonestDigest, DigestQuery, digestSaltProjection]

end Known

/-! ## Source provenance of the free digests of a real stage log -/

section Provenance

/-- A free honest digest entry. -/
def NoFreeDigest (log : TreeSimLog C) : Prop :=
  ∀ s hh d, (⟨.inr (.inr (.inl (.digest s hh))), d⟩ :
    (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∉ log

theorem logged_noFreeDigest (prims : Primitives) (D : C.Coalition) {α : Type}
    (W : OracleComp (WorldSpec C) α) (hW : IsQueryBoundP W TreeRawSaltCertificatesProof.HonestDigest 0) :
    ∀ (s : TreeSimState C), NoFreeDigest s.2 →
      ∀ z ∈ support ((simulateQ (treeSimLoggedWorld prims D) W).run s), NoFreeDigest z.2.2 := by
  induction W using OracleComp.inductionOn with
  | pure a =>
    intro s hs z hz
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    exact hs
  | query_bind t k ih =>
    intro s hs z hz
    rw [isQueryBoundP_query_bind_iff] at hW
    have ht : ¬ TreeRawSaltCertificatesProof.HonestDigest t := by
      rcases hW.1 with h1 | h1
      · exact h1
      · exact absurd h1 (Nat.lt_irrefl 0)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨mid, hm, hz⟩ := hz
    refine ih mid.1 (by simpa [ht] using hW.2 mid.1) mid.2 ?_ z hz
    simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hm
    obtain ⟨o, -, rfl⟩ := hm
    intro salt hh d hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · exact hs salt hh d hmem
    · rw [List.mem_singleton] at hmem
      have := congrArg Sigma.fst hmem
      subst this
      exact ht (by simp [TreeRawSaltCertificatesProof.HonestDigest, DigestQuery, digestSaltProjection])

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- The log at the end of the setup has no free digest. -/
theorem setup_noFreeDigest (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2)) :
    NoFreeDigest p.2.2 := by
  have h0 : NoFreeDigest s.2.2 := fun salt hh d hm =>
    TreeRawSaltCertificatesFromProof.prefix_no_free prims D pre s hs _ _ hm
  simp only [LifetimeSaltFrom.treeSaltSetupFrom, mem_support_bind_iff] at hp
  obtain ⟨start, hstart, hp⟩ := hp
  have h1 := logged_noFreeDigest prims D _ (TreeRawSaltCertificatesProof.HonestDigestCount.adversary_zero _)
    s.2 h0 start hstart
  rw [treeSimRealRoles, ← simulateQ_executePhase] at hp
  have hb := TreeRawSaltCertificatesProof.HonestDigestCount.executePhase_bound D A setupRounds start.1
    (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))) (fun _ => 0)
    (fun i _ => treeSimHash_setup_digest i)
  simp only [Finset.sum_const_zero] at hb
  exact logged_noFreeDigest prims D _ hb start.2 h1 p hp

/-- A block of a compiled outcome whose decoded state is a real stage view is a hidden read of
its salt in the decoded log, at a stage-1 address when the log has no budget collision. -/
theorem block_read (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux) {α : Type}
    (pre : OracleComp (LocalSpec C) α) (s : α × TreeSimState C)
    (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (TreeSaltPairsFinal.first prims K circuits settings top tree D A x p))
    (blocks : BlockCache C) (other : HiddenCache C) (hrest : m.2.1.2 = restore blocks other)
    (b : C.Term × HashOutput × ℕ) (w : Fin 256 → Bit) (hbw : blocks b = some w) :
    ¬ KnownTo D.1 b.1 ∧ TreeSaltAt m.2.2 b (List.ofFn w) := by
  have hcoh := hiddenCoherent_first prims K circuits settings top tree D A x p
    (hiddenCoherent_setup prims D A x z pre s hs p hp) _ hm
  have honly : HiddenOnly D m.2 := by
    have h0 := setup_inv prims D (HiddenOnly D) (fun y hy => (hy rfl).elim)
      (fun oa s hs => hiddenOnly_run prims D oa s hs) A x z pre s hs p hp
    rw [first_eq] at hm
    exact hiddenOnly_run prims D _ p.2 h0 _ hm
  have cached : ∀ g : Fin 256, m.2.1.2 (saltPoint b g) = some (w g) := by
    intro g
    rw [hrest]
    change restore blocks other (treeSimHashSaltAddress b g) = some (w g)
    rw [restore_address, hbw]
    rfl
  have hid : ¬ KnownTo D.1 b.1 := honly (saltPoint b ⟨0, by decide⟩) (by rw [cached]; simp)
  refine ⟨hid, fun g => ?_⟩
  rw [ofFn_getD]
  exact (hcoh (.term b.1, b.2.1, b.2.2, 2, g.val) (w g) hid).mpr (cached g)

theorem witness_ready (D : C.Coalition) (_A : Adversary C E (Keys C) PEmpty PEmpty) {β : Type}
    (q : OracleComp (BoundarySpec D) β) (hq : IsQueryBoundP q (BoundaryProgramCall D) 0)
    (st : CompilerState C) (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (ready : Ready cache blocks st) :
    ∀ r ∈ support (tableRun prims ((simulateQ (boundaryCompiler D) q).run st) used cache blocks),
      Ready r.2.1 r.2.2 r.1.1.2 := by
  have steps := TreeRawSaltStepsProof.boundaryCompilerSteps (E := E) prims D
  induction q using OracleComp.inductionOn generalizing used cache blocks st with
  | pure value =>
    intro r hr
    simp only [simulateQ_pure, StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hr
    subst hr
    exact ready
  | query_bind t k ih =>
    intro r hr
    rw [isQueryBoundP_query_bind_iff] at hq
    have ht : ¬ BoundaryProgramCall D t := by
      rcases hq.1 with h1 | h1
      · exact h1
      · exact absurd h1 (Nat.lt_irrefl 0)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tableRun_bind,
      mem_support_bind_iff] at hr
    obtain ⟨mid, hm, hr⟩ := hr
    exact ih mid.1.1.1 (by simpa [ht] using hq.2 mid.1.1.1) mid.1.1.2 mid.1.2 mid.2.1 mid.2.2
      ((steps t ht used cache blocks st ready).2 mid hm) r hr

/-- Source provenance: in every real stage view, every free digest has an empty salt or a salt
read at one term address of the log. -/
theorem source_provenance (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux) {α : Type}
    (pre : OracleComp (LocalSpec C) α) (s : α × TreeSimState C)
    (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (TreeSaltPairsFinal.first prims K circuits settings top tree D A x p))
    (salt : List Bit) (hh d : HashOutput)
    (he : (⟨.inr (.inr (.inl (.digest salt hh))), d⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ m.2.2) :
    salt = [] ∨ ∃ c, TreeSaltAt m.2.2 c salt := by
  have hopen := setup_open prims D A x z pre s hs p hp
  have hlaw := witness_law prims K circuits settings top tree D A x p hopen ([], [])
  have hm' := hm
  rw [mem_support_iff, probOutput_congr rfl hlaw, ← mem_support_iff, support_map] at hm'
  obtain ⟨r, hr, rfl⟩ := hm'
  have ready0 : Ready p.2.1.1 ∅ ((p.2.1.2, p.2.2.map .literal) : CompilerState C) := by
    intro piece hp'
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hp'
    trivial
  have ready := witness_ready prims D A (witness K circuits settings top tree D A x p)
    (boundaryDropPrograms_safe D _) (p.2.1.2, p.2.2.map .literal) ([], []) p.2.1.1 ∅ ready0 r hr
  have noFree := setup_noFreeDigest prims D A x z pre s hs p hp
  have ks0 : KS [] ((p.2.1.2, p.2.2.map .literal) : CompilerState C) ([], []) := by
    refine ⟨fun salt' hh' d' hm0 => ?_, fun s hs => absurd hs List.not_mem_nil⟩
    obtain ⟨e, he0, hee⟩ := List.mem_map.mp hm0
    cases hee
    exact (noFree _ _ _ he0).elim
  have ks := ks_program prims D _ (witness_raw K circuits settings top tree D A x p) _ _ _ _ ks0 r hr
  obtain ⟨piece, hpiece, hdec⟩ := List.mem_flatMap.mp he
  cases piece with
  | literal e =>
    simp only [LogPiece.decode, List.mem_singleton] at hdec
    subst hdec
    rcases ks.1 salt hh d hpiece with h | ⟨c, hc⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, fun g => List.mem_flatMap.mpr ⟨_, hc g, List.mem_singleton_self _⟩⟩
  | draw b =>
    simp only [LogPiece.decode, treeSimHiddenLog, List.mem_ofFn] at hdec
    obtain ⟨g, hg⟩ := hdec
    cases hg
  | digest b history output =>
    obtain ⟨⟨w, hbw⟩, -⟩ := ready _ hpiece
    simp only [LogPiece.decode, TreeRawSaltCeremonyProof.digestLog,
      TreeRawSaltCeremonyProof.digestEntries, List.mem_cons,
      List.not_mem_nil, or_false] at hdec
    rcases hdec with hdec | hdec
    · cases hdec
    · simp only [Sigma.mk.inj_iff, Sum.inr.injEq, Sum.inl.injEq, Query.digest.injEq] at hdec
      obtain ⟨⟨rfl, -⟩, -⟩ := hdec
      right
      refine ⟨b, ?_⟩
      have := (block_read prims K circuits settings top tree D A x z pre s hs p hp _ hm r.2.2
        r.1.1.2.1 rfl b w hbw).2
      simpa only [TreeRawSaltCeremonyProof.blockValues, hbw, Option.getD_some] using this

end Provenance

/-! ## Draw and digest pieces balance in every compiled row -/

section Balance

variable (prims : Primitives)

/-- The draw pieces of a block. -/
def drawCount (b : TreeSimHashSaltBlock C) (pieces : List (LogPiece C)) : ℕ :=
  pieces.countP fun x => decide (x = .draw b)

/-- The digest pieces of a block. -/
def digestCount (b : TreeSimHashSaltBlock C) (pieces : List (LogPiece C)) : ℕ :=
  pieces.countP fun x => decide (∃ h o, x = .digest b h o)

/-- The counts of draw and digest pieces are fixed functions. -/
def CountsAt (d g : TreeSimHashSaltBlock C → ℕ) (st : CompilerState C) (_used : SaltLists) : Prop :=
  ∀ b, drawCount b st.2 = d b ∧ digestCount b st.2 = g b

theorem counts_literal (pieces : List (LogPiece C)) (e : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t)
    (b : TreeSimHashSaltBlock C) :
    drawCount b (pieces ++ [.literal e]) = drawCount b pieces ∧
      digestCount b (pieces ++ [.literal e]) = digestCount b pieces := by
  simp [drawCount, digestCount, List.countP_append]

theorem countsAt_publicQuery (d g : TreeSimHashSaltBlock C → ℕ) (D : C.Coalition)
    (t : (WorldSpec C).Domain) :
    TreeRawSaltCertificatesProof.Preserves prims (CountsAt d g) (publicQuery D t) := by
  intro st used cache blocks h r hr
  have hl := publicQuery_log prims D t st used cache blocks r hr
  intro b
  show drawCount b r.1.1.2.2 = d b ∧ digestCount b r.1.1.2.2 = g b
  rw [hl, (counts_literal st.2 _ b).1, (counts_literal st.2 _ b).2]
  exact h b

theorem countsAt_publicDraw (d g : TreeSimHashSaltBlock C → ℕ) (D : C.Coalition) (name : KeyName C)
    (key : HashOutput) (label : ℕ) :
    TreeRawSaltCertificatesProof.Preserves prims (CountsAt d g) (publicDraw D name key label) :=
  TreeRawSaltCertificatesProof.Preserves.simulateQ prims _ _ (countsAt_publicQuery prims d g D)

theorem countsAt_preparePairs (d g : TreeSimHashSaltBlock C → ℕ) (D : C.Coalition)
    (ctx : Context C) (label : ℕ) :
    TreeRawSaltCertificatesProof.Preserves prims (CountsAt d g) (preparePairs D ctx label) := by
  unfold preparePairs
  refine TreeRawSaltCertificatesProof.Preserves.bind prims (I := CountsAt d g) _ _ ?_ ?_
  · apply TreeRawSaltCertificatesProof.Preserves.mapM prims (I := CountsAt d g)
    intro j
    split_ifs
    · exact TreeRawSaltCertificatesProof.Preserves.pure prims _
    · exact countsAt_publicDraw prims d g D _ _ _
  · intro _
    exact TreeRawSaltCertificatesProof.Preserves.pure prims _

/-- The block of a hidden held term in a row. -/
def heldBlock (D : C.Coalition) (ctx : Context C) (label : ℕ) (b : TreeSimHashSaltBlock C)
    (T : C.Term) : Prop :=
  ctx.self ∈ C.holders T ∧ ¬ KnownTo D.1 T ∧ (T, ctx.prss.term T, label) = b

/-- `TermSalt` under the table run. -/
theorem prepareTerm_table (D : C.Coalition) (ctx : Context C) (label : ℕ) (T : C.Term)
    (st : CompilerState C) (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C) r
    (hr : r ∈ support (tableRun prims ((prepareTerm D ctx label T).run st) used cache blocks)) :
    TreeRawSaltStepsProof.TermSalt D ctx label T r.1.1.1 ∧
      ∀ b, drawCount b r.1.1.2.2 = drawCount b st.2 + (if heldBlock D ctx label b T then 1 else 0) ∧
        digestCount b r.1.1.2.2 = digestCount b st.2 := by
  unfold prepareTerm at hr
  by_cases held : ctx.self ∈ C.holders T
  · by_cases known : KnownTo D.1 T
    · rw [if_pos held, if_pos known, StateT.run_map, tableRun_map, support_map] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      refine ⟨by simp [TreeRawSaltStepsProof.TermSalt, held, known, vector], fun b => ?_⟩
      have := countsAt_publicDraw prims (fun b => drawCount b st.2) (fun b => digestCount b st.2) D _ _ _
        st used cache blocks (fun b => ⟨rfl, rfl⟩) z hz b
      simp only [heldBlock, known, not_true_eq_false, false_and, and_false, if_false, Nat.add_zero]
      exact this
    · rw [if_pos held, if_neg known] at hr
      simp only [StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hr
      obtain ⟨e, he, hr⟩ := hr
      simp only [emit, StateT.run_modify, tableRun, simulateQ_pure, StateT.run_pure,
        mem_support_pure_iff] at he
      subst he
      simp only [StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hr
      subst hr
      refine ⟨by simp [TreeRawSaltStepsProof.TermSalt, held, known], fun b => ?_⟩
      simp only [drawCount, digestCount, List.countP_append, List.countP_singleton, heldBlock]
      constructor
      · by_cases hb : (T, ctx.prss.term T, label) = b
        · simp [hb, held, known]
        · simp [hb, held, known]
      · simp
  · rw [if_neg held] at hr
    simp only [StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hr
    subst hr
    refine ⟨by simp [TreeRawSaltStepsProof.TermSalt, held], fun b => ?_⟩
    simp [heldBlock, held]

theorem prepare_counts (D : C.Coalition) (ctx : Context C) (label : ℕ) :
    ∀ (xs : List C.Term) (st : CompilerState C) (used : SaltLists) (cache : HashCache C)
      (blocks : BlockCache C) r,
    r ∈ support (tableRun prims ((xs.mapM (prepareTerm D ctx label)).run st) used cache blocks) →
    List.Forall₂ (TreeRawSaltStepsProof.TermSalt D ctx label) xs r.1.1.1 ∧
      ∀ b, drawCount b r.1.1.2.2 = drawCount b st.2 + xs.countP (fun T => decide (heldBlock D ctx label b T)) ∧
        digestCount b r.1.1.2.2 = digestCount b st.2
  | [], st, used, cache, blocks, r, hr => by
    simp only [List.mapM_nil, StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hr
    subst hr
    exact ⟨.nil, fun b => by simp⟩
  | T :: xs, st, used, cache, blocks, r, hr => by
    simp only [List.mapM_cons, StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hm, hr⟩ := hr
    obtain ⟨rest, hrest, hr⟩ := hr
    simp only [StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hr
    subst hr
    obtain ⟨shape, step⟩ := prepareTerm_table prims D ctx label T st used cache blocks mid hm
    obtain ⟨shapes, steps⟩ := prepare_counts D ctx label xs _ _ _ _ rest hrest
    refine ⟨.cons shape shapes, fun b => ⟨?_, ?_⟩⟩
    · rw [(steps b).1, (step b).1, List.countP_cons]
      split_ifs <;> (simp_all; try omega)
    · rw [(steps b).2, (step b).2]

theorem digests_counts (D : C.Coalition) (ctx : Context C) (st0 : RunState C)
    (terms : List (Salt C))
    (hterms : ∀ T, TreeRawSaltStepsProof.TermSalt D ctx st0.label T
      (terms.getD (C.terms.idxOf T) (.inr []))) :
    ∀ (xs : List C.Term) (st : CompilerState C) (used : SaltLists) (cache : HashCache C)
      (blocks : BlockCache C) r,
    r ∈ support (tableRun prims ((xs.mapM fun T => if ctx.self ∈ C.holders T then
      compileDigest D (terms.getD (C.terms.idxOf T) (.inr []), st0.history T) else pure 0).run st)
        used cache blocks) →
    ∀ b, drawCount b r.1.1.2.2 = drawCount b st.2 ∧
      digestCount b r.1.1.2.2 = digestCount b st.2 +
        xs.countP (fun T => decide (heldBlock D ctx st0.label b T))
  | [], st, used, cache, blocks, r, hr => by
    simp only [List.mapM_nil, StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hr
    subst hr
    exact fun b => by simp
  | T :: xs, st, used, cache, blocks, r, hr => by
    simp only [List.mapM_cons, StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hm, hr⟩ := hr
    obtain ⟨rest, hrest, hr⟩ := hr
    simp only [StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hr
    subst hr
    have steps := digests_counts D ctx st0 terms hterms xs _ _ _ _ rest hrest
    have step : ∀ b, drawCount b mid.1.1.2.2 = drawCount b st.2 ∧
        digestCount b mid.1.1.2.2 = digestCount b st.2 +
          (if heldBlock D ctx st0.label b T then 1 else 0) := by
      have hT := hterms T
      by_cases held : ctx.self ∈ C.holders T
      · rw [if_pos held] at hm
        simp only [TreeRawSaltStepsProof.TermSalt, if_pos held] at hT
        by_cases known : KnownTo D.1 T
        · rw [if_pos known] at hT
          obtain ⟨bits, hbits, -⟩ := hT
          rw [hbits] at hm
          have := TreeRawSaltCertificatesProof.Preserves.simulateQ prims (publicQuery D) _
            (countsAt_publicQuery prims (fun b => drawCount b st.2) (fun b => digestCount b st.2) D)
            st used cache blocks (fun b => ⟨rfl, rfl⟩) mid hm
          intro b
          simp only [heldBlock, known, not_true_eq_false, false_and, and_false, if_false,
            Nat.add_zero]
          exact this b
        · rw [if_neg known] at hT
          rw [hT] at hm
          simp only [compileDigest, StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hm
          obtain ⟨o, ho, e, he, hm⟩ := hm
          simp only [StateT.run_lift, bind_pure_comp, tableRun_map, support_map, Set.mem_image] at ho
          obtain ⟨o', -, rfl⟩ := ho
          simp only [emit, StateT.run_modify, tableRun, simulateQ_pure, StateT.run_pure,
            mem_support_pure_iff] at he
          subst he
          simp only [StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hm
          subst hm
          intro b
          simp only [drawCount, digestCount, List.countP_append, List.countP_singleton, heldBlock]
          refine ⟨by simp, ?_⟩
          by_cases hb : (T, ctx.prss.term T, st0.label) = b
          · subst hb
            simp [held, known]
          · simp [hb, held, known]
      · rw [if_neg held] at hm
        simp only [StateT.run_pure, tableRun_pure_eq, mem_support_pure_iff] at hm
        subst hm
        intro b
        simp [heldBlock, held]
    intro b
    refine ⟨(steps b).1.trans (step b).1, ?_⟩
    rw [(steps b).2, (step b).2, List.countP_cons]
    split_ifs <;> (simp_all; try omega)

/-- Every block has as many digest pieces as draw pieces. -/
def Balanced (st : CompilerState C) (_used : SaltLists) : Prop :=
  ∀ b, drawCount b st.2 = digestCount b st.2

theorem balanced_row (D : C.Coalition) (ctx : Context C) (st0 : RunState C) :
    TreeRawSaltCertificatesProof.Preserves prims Balanced (compileBoundaryDigest D ctx st0) := by
  intro st used cache blocks h r hr
  unfold compileBoundaryDigest at hr
  simp only [StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hr
  obtain ⟨t1, h1, t2, h2, hr⟩ := hr
  obtain ⟨shape, c1⟩ := prepare_counts prims D ctx st0.label C.terms st used cache blocks t1 h1
  have c2 := countsAt_preparePairs prims (fun b => drawCount b t1.1.1.2.2)
    (fun b => digestCount b t1.1.1.2.2) D ctx st0.label _ _ _ _ (fun b => ⟨rfl, rfl⟩) t2 h2
  have c3 := digests_counts prims D ctx st0 t1.1.1.1
    (TreeRawSaltStepsProof.termSalt_getD D ctx st0.label _ shape) C.terms _ _ _ _ r hr
  have c2' : ∀ b, drawCount b t2.1.1.2.2 = drawCount b t1.1.1.2.2 ∧
      digestCount b t2.1.1.2.2 = digestCount b t1.1.1.2.2 := c2
  intro b
  show drawCount b r.1.1.2.2 = digestCount b r.1.1.2.2
  rw [(c3 b).1, (c3 b).2, (c2' b).1, (c2' b).2, (c1 b).1, (c1 b).2, h b]

theorem balanced_program {α : Type} (D : C.Coalition) (q : OracleComp (BoundarySpec D) α) :
    TreeRawSaltCertificatesProof.Preserves prims Balanced (simulateQ (boundaryCompiler D) q) := by
  refine TreeRawSaltCertificatesProof.Preserves.simulateQ prims _ _ fun t => ?_
  rcases t with ⟨ctx, st0⟩ | ⟨t, safe⟩
  · exact balanced_row prims D ctx st0
  · intro st used cache blocks h r hr
    have hl := publicQuery_log prims D t st used cache blocks r hr
    intro b
    show drawCount b r.1.1.2.2 = digestCount b r.1.1.2.2
    rw [hl, (counts_literal st.2 _ b).1, (counts_literal st.2 _ b).2]
    exact h b

end Balance

/-! ## Counting digests against reads -/

section Count

theorem countP_flatMap_le {α β : Type} (l : List α) (f : α → List β) (q : β → Bool) (r : α → Bool)
    (h : ∀ x ∈ l, (f x).countP q ≤ if r x then 1 else 0) :
    (l.flatMap f).countP q ≤ l.countP r := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.countP_append, List.countP_cons]
    have hx := h x List.mem_cons_self
    have hl := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    split_ifs at hx ⊢ <;> omega

theorem countP_flatMap_ge {α β : Type} (l : List α) (f : α → List β) (q : β → Bool)
    (r r' : α → Bool) (h : ∀ x ∈ l, (if r x then 1 else 0) + (if r' x then 1 else 0) ≤ (f x).countP q) :
    l.countP r + l.countP r' ≤ (l.flatMap f).countP q := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons, List.countP_append, List.countP_cons, List.countP_cons]
    have hx := h x List.mem_cons_self
    have hl := ih fun y hy => h y (List.mem_cons_of_mem _ hy)
    split_ifs at hx ⊢ <;> omega

/-- The free digests at `v` in a log. -/
def digestsAt (v : List Bit) (log : TreeSimLog C) : ℕ :=
  log.countP fun e =>
    @decide (∃ hh d, e = ⟨.inr (.inr (.inl (.digest v hh))), d⟩) (Classical.propDecidable _)

/-- The first-position reads of the address `a` in a log. -/
def readsOf (a : C.Term × HashOutput × ℕ) (log : TreeSimLog C) : ℕ :=
  log.countP fun e =>
    @decide (∃ bit, e = ⟨.inr (.inr (.inr (.term a.1, a.2.1, a.2.2, 2, 0))), bit⟩)
      (Classical.propDecidable _)

theorem safe_not_read (D : C.Coalition) (st : CompilerState C) (used : SaltLists)
    (safe : TreeRawSaltCertificatesProof.SafeLiterals D st used) (a : C.Term × HashOutput × ℕ)
    (ha : ¬ KnownTo D.1 a.1) (g : ℕ) (hg : g < 256) (bit : Bit)
    (h : LogPiece.literal ⟨.inr (.inr (.inr (.term a.1, a.2.1, a.2.2, 2, g))), bit⟩ ∈ st.2) : False := by
  have hn := safe _ h ha
  change saltAt (((.term a.1, a.2.1), a.2.2, 2, g) : HiddenAddress C) = none at hn
  simp [saltAt, hg] at hn

theorem length_le_one_of_eq {α : Type} (l : List α) (hl : l.Nodup) (c : α) (h : ∀ x ∈ l, x = c) :
    l.length ≤ 1 := by
  match l, hl, h with
  | [], _, _ => simp
  | [_], _, _ => simp
  | x :: y :: l, hl, h =>
    exfalso
    have hx := h x List.mem_cons_self
    have hy := h y (List.mem_cons_of_mem _ List.mem_cons_self)
    exact (List.nodup_cons.mp hl).1 (hx ▸ hy ▸ List.mem_cons_self)

/-- A draw piece holds one first-position read, of its own block. -/
theorem draw_reads (a b : TreeSimHashSaltBlock C) (cache : HashCache C) (blocks : BlockCache C) :
    readsOf a ((LogPiece.draw b).decode cache blocks) = if b = a then 1 else 0 := by
  unfold readsOf
  simp only [LogPiece.decode, treeSimHiddenLog, List.ofFn_eq_map, List.countP_map]
  rw [List.countP_eq_length_filter]
  set l := (List.finRange 256).filter _ with hl
  have hmem : ∀ i ∈ l, b = a ∧ i = (0 : Fin 256) := by
    intro i hi
    rw [hl, List.mem_filter] at hi
    obtain ⟨-, hi⟩ := hi
    simp only [Function.comp_apply, decide_eq_true_eq] at hi
    obtain ⟨bit, he⟩ := hi
    have hx := congrArg Sigma.fst he
    rcases a with ⟨A, ak, al⟩
    rcases b with ⟨B, bk, bl⟩
    simp only [treeSimHashSaltAddress, Sum.inr.injEq, Prod.mk.injEq, KeyName.term.injEq] at hx
    obtain ⟨rfl, rfl, rfl, -, hg⟩ := hx
    exact ⟨rfl, Fin.ext hg⟩
  by_cases hab : b = a
  · rw [if_pos hab]
    apply le_antisymm
    · exact length_le_one_of_eq l ((List.nodup_finRange 256).filter _) 0 fun i hi => (hmem i hi).2
    · apply List.length_pos_of_mem (a := (0 : Fin 256))
      rw [hl, List.mem_filter]
      refine ⟨List.mem_finRange _, ?_⟩
      simp only [Function.comp_apply, decide_eq_true_eq]
      subst hab
      exact ⟨_, rfl⟩
  · rw [if_neg hab, List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
    exact fun i hi => hab (hmem i hi).1

theorem digest_digests_le (v : List Bit) (b : TreeSimHashSaltBlock C) (h : List Bit) (o : HashOutput)
    (cache : HashCache C) (blocks : BlockCache C) :
    digestsAt v ((LogPiece.digest b h o).decode cache blocks) ≤
      if List.ofFn (TreeRawSaltCeremonyProof.blockValues blocks b) = v then 1 else 0 := by
  unfold digestsAt
  simp only [LogPiece.decode, TreeRawSaltCeremonyProof.digestLog,
    TreeRawSaltCeremonyProof.digestEntries, List.countP_cons, List.countP_nil]
  have h0 : ¬ (∃ hh d, (⟨.inr (.inr (.inl (.history h))), (cache (.history h)).getD 0⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) = ⟨.inr (.inr (.inl (.digest v hh))), d⟩) := by
    rintro ⟨hh, d, he⟩
    have := congrArg Sigma.fst he
    simp only [Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at this
  rw [if_neg (fun hd => h0 (@of_decide_eq_true _ (Classical.propDecidable _) hd))]
  by_cases hv : List.ofFn (TreeRawSaltCeremonyProof.blockValues blocks b) = v
  · rw [if_pos hv]
    split_ifs <;> omega
  · rw [if_neg hv, if_neg]
    intro hd
    obtain ⟨hh, d, he⟩ := @of_decide_eq_true _ (Classical.propDecidable _) hd
    have := congrArg Sigma.fst he
    simp only [Sum.inr.injEq, Sum.inl.injEq, Query.digest.injEq] at this
    exact hv this.1

theorem digest_digests_ge (v : List Bit) (b : TreeSimHashSaltBlock C) (h : List Bit) (o : HashOutput)
    (cache : HashCache C) (blocks : BlockCache C)
    (hv : List.ofFn (TreeRawSaltCeremonyProof.blockValues blocks b) = v) :
    1 ≤ digestsAt v ((LogPiece.digest b h o).decode cache blocks) := by
  subst hv
  unfold digestsAt
  apply List.countP_pos_iff.mpr
  refine ⟨⟨.inr (.inr (.inl (.digest (List.ofFn (TreeRawSaltCeremonyProof.blockValues blocks b))
    ((cache (.history h)).getD 0)))), o⟩, ?_,
    @decide_eq_true _ (Classical.propDecidable _) ⟨_, o, rfl⟩⟩
  simp only [LogPiece.decode, TreeRawSaltCeremonyProof.digestLog,
    TreeRawSaltCeremonyProof.digestEntries]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

/-- On a compiled state whose literals carry known reads, the free digests at a salt with one
read address `a` are at most the digest pieces of `a`. -/
theorem digestsAt_le (D : C.Coalition) (st : CompilerState C) (used : SaltLists)
    (cache : HashCache C) (blocks : BlockCache C) (ks : KS [] st used)
    (safe : TreeRawSaltCertificatesProof.SafeLiterals D st used) (ready : Ready cache blocks st)
    (a : C.Term × HashOutput × ℕ) (ha : ¬ KnownTo D.1 a.1) (v : List Bit) (hv : v ≠ [])
    (huniq : ∀ c, TreeSaltAt (st.2.flatMap (LogPiece.decode cache blocks)) c v → c = a)
    (hblocks : ∀ b w, blocks b = some w →
      TreeSaltAt (st.2.flatMap (LogPiece.decode cache blocks)) b (List.ofFn w)) :
    digestsAt v (st.2.flatMap (LogPiece.decode cache blocks)) ≤ digestCount a st.2 := by
  unfold digestsAt digestCount
  apply countP_flatMap_le
  intro x hx
  cases x with
  | literal e =>
    simp only [LogPiece.decode, List.countP_singleton]
    split_ifs with he he'
    · exact le_refl _
    · exfalso
      simp only [decide_eq_true_eq] at he
      obtain ⟨hh, d, rfl⟩ := he
      rcases ks.1 v hh d hx with h0 | ⟨c, hc⟩
      · exact hv h0
      · have hca := huniq c fun g => List.mem_flatMap.mpr ⟨_, hc g, List.mem_singleton_self _⟩
        subst hca
        exact safe_not_read D st used safe c ha 0 (by norm_num) _ (hc ⟨0, by norm_num⟩)
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  | draw b =>
    simp only [LogPiece.decode, treeSimHiddenLog, List.ofFn_eq_map, List.countP_map]
    rw [List.countP_eq_zero.mpr]
    · exact Nat.zero_le _
    · intro i _
      simp only [Function.comp_apply, decide_eq_true_eq, not_exists]
      intro hh d he
      cases congrArg Sigma.fst he
  | digest b h o =>
    have := digest_digests_le v b h o cache blocks
    unfold digestsAt at this
    refine this.trans ?_
    split_ifs with h1 h2
    · exact le_refl _
    · exfalso
      obtain ⟨⟨w, hw⟩, -⟩ := ready _ hx
      have hb := hblocks b w hw
      simp only [TreeRawSaltCeremonyProof.blockValues, hw, Option.getD_some] at h1
      rw [h1] at hb
      exact h2 (@decide_eq_true _ (Classical.propDecidable _) ⟨h, o, by rw [huniq b hb]⟩)
    · exact Nat.zero_le _
    · exact Nat.zero_le _

theorem draws_le_reads (st : CompilerState C) (cache : HashCache C) (blocks : BlockCache C)
    (a : C.Term × HashOutput × ℕ) :
    drawCount a st.2 ≤ readsOf a (st.2.flatMap (LogPiece.decode cache blocks)) := by
  have h := countP_flatMap_ge st.2 (LogPiece.decode cache blocks)
    (fun e => @decide (∃ bit, e = ⟨.inr (.inr (.inr (.term a.1, a.2.1, a.2.2, 2, 0))), bit⟩)
      (Classical.propDecidable _))
    (fun x => decide (x = .draw a)) (fun _ => false) (by
      intro x _
      simp only [Bool.false_eq_true, if_false, Nat.add_zero]
      split_ifs with hx
      · simp only [decide_eq_true_eq] at hx
        subst hx
        have := draw_reads a a cache blocks
        unfold readsOf at this
        rw [this, if_pos rfl]
      · exact Nat.zero_le _)
  simpa [drawCount, readsOf] using h

theorem reads_le_draws (D : C.Coalition) (st : CompilerState C) (used : SaltLists)
    (cache : HashCache C) (blocks : BlockCache C)
    (safe : TreeRawSaltCertificatesProof.SafeLiterals D st used)
    (a : C.Term × HashOutput × ℕ) (ha : ¬ KnownTo D.1 a.1) :
    readsOf a (st.2.flatMap (LogPiece.decode cache blocks)) ≤ drawCount a st.2 := by
  unfold readsOf drawCount
  apply countP_flatMap_le
  intro x hx
  cases x with
  | literal e =>
    simp only [LogPiece.decode, List.countP_singleton]
    split_ifs with he he'
    · exact le_refl _
    · exfalso
      simp only [decide_eq_true_eq] at he
      obtain ⟨bit, rfl⟩ := he
      exact safe_not_read D st used safe a ha 0 (by norm_num) bit hx
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  | draw b =>
    have := draw_reads a b cache blocks
    unfold readsOf at this
    rw [this]
    by_cases hb : b = a
    · subst hb
      simp
    · simp [hb]
  | digest b h o =>
    rw [List.countP_eq_zero.mpr]
    · exact Nat.zero_le _
    · intro e he hd
      obtain ⟨bit, rfl⟩ := @of_decide_eq_true _ (Classical.propDecidable _) hd
      simp only [LogPiece.decode, TreeRawSaltCeremonyProof.digestLog,
        TreeRawSaltCeremonyProof.digestEntries, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with he | he <;>
      · have := congrArg Sigma.fst he
        simp only [Sum.inr.injEq, reduceCtorEq] at this

theorem digests_ge (st : CompilerState C) (cache : HashCache C) (blocks : BlockCache C)
    (a : C.Term × HashOutput × ℕ) (w : Fin 256 → Bit) (hw : blocks a = some w) (hh d : HashOutput)
    (hX : LogPiece.literal ⟨.inr (.inr (.inl (.digest (List.ofFn w) hh))), d⟩ ∈ st.2) :
    digestCount a st.2 + 1 ≤ digestsAt (List.ofFn w) (st.2.flatMap (LogPiece.decode cache blocks)) := by
  let X : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t :=
    ⟨.inr (.inr (.inl (.digest (List.ofFn w) hh))), d⟩
  let isX : LogPiece C → Bool := fun x => @decide (x = .literal X) (Classical.propDecidable _)
  have h := countP_flatMap_ge st.2 (LogPiece.decode cache blocks)
    (fun e => @decide (∃ hh d, e = ⟨.inr (.inr (.inl (.digest (List.ofFn w) hh))), d⟩)
      (Classical.propDecidable _))
    (fun x => decide (∃ h o, x = .digest a h o)) isX (by
      intro x _
      cases x with
      | literal e =>
        have h1 : decide (∃ h o, LogPiece.literal e = LogPiece.digest a h o) = false :=
          decide_eq_false (by rintro ⟨_, _, h⟩; cases h)
        rw [h1, if_neg Bool.false_ne_true, Nat.zero_add]
        rcases Classical.em (e = X) with he | he
        · subst he
          have h2 : isX (.literal X) = true := @decide_eq_true _ (Classical.propDecidable _) rfl
          rw [if_pos h2]
          apply List.countP_pos_iff.mpr
          exact ⟨X, List.mem_singleton_self _, @decide_eq_true _ (Classical.propDecidable _) ⟨hh, d, rfl⟩⟩
        · have h2 : isX (.literal e) = false :=
            @decide_eq_false _ (Classical.propDecidable _) (fun h' => he (LogPiece.literal.inj h'))
          rw [if_neg (by rw [h2]; exact Bool.false_ne_true)]
          exact Nat.zero_le _
      | draw b =>
        have h1 : decide (∃ h o, LogPiece.draw b = LogPiece.digest a h o) = false :=
          decide_eq_false (by rintro ⟨_, _, h⟩; cases h)
        have h2 : isX (.draw b) = false :=
          @decide_eq_false _ (Classical.propDecidable _) (fun h' => by cases h')
        rw [h1, h2, if_neg Bool.false_ne_true]
        exact Nat.zero_le _
      | digest b h o =>
        have h2 : isX (.digest b h o) = false :=
          @decide_eq_false _ (Classical.propDecidable _) (fun h' => by cases h')
        rw [h2, if_neg Bool.false_ne_true, Nat.add_zero]
        by_cases hb : b = a
        · subst hb
          have h1 : decide (∃ h' o', LogPiece.digest b h o = LogPiece.digest b h' o') = true :=
            decide_eq_true ⟨h, o, rfl⟩
          rw [if_pos h1]
          exact digest_digests_ge _ b h o cache blocks (by
            simp only [TreeRawSaltCeremonyProof.blockValues, hw, Option.getD_some])
        · have h1 : decide (∃ h' o', LogPiece.digest b h o = LogPiece.digest a h' o') = false :=
            decide_eq_false (by rintro ⟨_, _, h'⟩; cases h'; exact hb rfl)
          rw [if_neg (by rw [h1]; exact Bool.false_ne_true)]
          exact Nat.zero_le _)
  have hpos : 1 ≤ st.2.countP isX :=
    List.countP_pos_iff.mpr ⟨_, hX, @decide_eq_true _ (Classical.propDecidable _) rfl⟩
  unfold digestCount digestsAt
  omega

end Count

/-! ## The literal transport -/

section Final

/-- No programming entry in a log. -/
def NoProgram (log : TreeSimLog C) : Prop :=
  ∀ e ∈ log, ∀ y, e.1 ≠ .inl (.inr y)

theorem logged_noProgram (prims : Primitives) (D : C.Coalition) {α : Type}
    (W : OracleComp (WorldSpec C) α) (hW : IsQueryBoundP W AimedProgramCall 0) :
    ∀ (s : TreeSimState C), NoProgram s.2 →
      ∀ z ∈ support ((simulateQ (treeSimLoggedWorld prims D) W).run s), NoProgram z.2.2 := by
  induction W using OracleComp.inductionOn with
  | pure a =>
    intro s hs z hz
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hz
    subst hz
    exact hs
  | query_bind t k ih =>
    intro s hs z hz
    rw [isQueryBoundP_query_bind_iff] at hW
    have ht : ¬ AimedProgramCall t := by
      rcases hW.1 with h1 | h1
      · exact h1
      · exact absurd h1 (Nat.lt_irrefl 0)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨mid, hm, hz⟩ := hz
    refine ih mid.1 (by simpa [ht] using hW.2 mid.1) mid.2 ?_ z hz
    simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hm
    obtain ⟨o, -, rfl⟩ := hm
    intro e he y hy
    rcases List.mem_append.mp he with he | he
    · exact hs e he y hy
    · rw [List.mem_singleton] at he
      subst he
      exact ht (by simp only at hy; subst hy; trivial)

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

theorem setup_noProgram (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2)) :
    NoProgram p.2.2 := by
  have h0 := logged_noProgram prims D _ (aimed_noProgram_adversary pre) ((∅, ∅), [])
    (fun e he => by simp at he) s hs
  simp only [LifetimeSaltFrom.treeSaltSetupFrom, mem_support_bind_iff] at hp
  obtain ⟨start, hstart, hp⟩ := hp
  have h1 := logged_noProgram prims D _ (aimed_noProgram_adversary _) s.2 h0 start hstart
  rw [treeSimRealRoles, ← simulateQ_executePhase] at hp
  refine logged_noProgram prims D _ ?_ start.2 h1 p hp
  unfold executePhase startSteps
  apply qb0_bind
  · apply isQueryBoundP_sequenceFin
    intro i
    split_ifs
    · simp
    · exact aimed_noProgram_free _
  · intro steps
    exact aimed_noProgram_rounds D A _ _ steps

theorem safe_initial (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) {α : Type} (pre : OracleComp (LocalSpec C) α)
    (s : α × TreeSimState C) (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2)) (used : SaltLists) :
    TreeRawSaltCertificatesProof.SafeLiterals D ((p.2.1.2, p.2.2.map .literal) : CompilerState C) used := by
  intro entry hm
  obtain ⟨⟨t, v⟩, he, hee⟩ := List.mem_map.mp hm
  cases hee
  have noSalt := TreeSaltPairsFinal.setup_from_noSalt prims D A x z pre s hs p hp
  rcases t with t | (t | t | y)
  · trivial
  · trivial
  · trivial
  · intro hidden
    cases h : saltAt ((y.1, y.2.1), y.2.2) with
    | none => rfl
    | some bg =>
      obtain ⟨b, g⟩ := bg
      have hx := saltAt_sound h
      have hy : y = (.term b.1, b.2.1, b.2.2, 2, g.val) :=
        congrArg (fun y : HiddenAddress C => (y.1.1, y.1.2, y.2)) hx
      exact (noSalt y v he b.1 b.2.1 b.2.2 g.val hy).elim

theorem balanced_initial (log : TreeSimLog C) (other : HiddenCache C) (used : SaltLists) :
    Balanced ((other, log.map .literal) : CompilerState C) used := by
  intro b
  simp only [drawCount, digestCount, List.countP_map]
  rw [List.countP_eq_zero.mpr, List.countP_eq_zero.mpr]
  · intro e _
    simp only [Function.comp_apply, decide_eq_true_eq, not_exists]
    intro h o he
    cases he
  · intro e _
    simp only [Function.comp_apply, decide_eq_true_eq]
    intro he
    cases he

/-- Source count: in a real stage view, if `a` is the only address that reads the salt `v`, the
free digests at `v` are at most the first-position reads of `a`. -/
theorem source_count (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux) {α : Type}
    (pre : OracleComp (LocalSpec C) α) (s : α × TreeSimState C)
    (hs : s ∈ support (LifetimeSaltFrom.prefixState prims D pre))
    (p : (A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C)
    (hp : p ∈ support (LifetimeSaltFrom.treeSaltSetupFrom prims D A x z s.2))
    (m : TreeSimConfig A (TreeSimState C))
    (hm : m ∈ support (TreeSaltPairsFinal.first prims K circuits settings top tree D A x p))
    (a : C.Term × HashOutput × ℕ) (ha : ¬ KnownTo D.1 a.1) (w : Fin 256 → Bit)
    (huniq : ∀ c, TreeSaltAt m.2.2 c (List.ofFn w) → c = a) :
    digestsAt (List.ofFn w) m.2.2 ≤ readsOf a m.2.2 := by
  have hopen := setup_open prims D A x z pre s hs p hp
  have hlaw := witness_law prims K circuits settings top tree D A x p hopen ([], [])
  have hm' := hm
  rw [mem_support_iff, probOutput_congr rfl hlaw, ← mem_support_iff, support_map] at hm'
  obtain ⟨r, hr, rfl⟩ := hm'
  have ready0 : Ready p.2.1.1 ∅ ((p.2.1.2, p.2.2.map .literal) : CompilerState C) := by
    intro piece hp'
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hp'
    trivial
  have ready := witness_ready prims D A (witness K circuits settings top tree D A x p)
    (boundaryDropPrograms_safe D _) (p.2.1.2, p.2.2.map .literal) ([], []) p.2.1.1 ∅ ready0 r hr
  have noFree := setup_noFreeDigest prims D A x z pre s hs p hp
  have ks0 : KS [] ((p.2.1.2, p.2.2.map .literal) : CompilerState C) ([], []) := by
    refine ⟨fun salt' hh' d' hm0 => ?_, fun s hs => absurd hs List.not_mem_nil⟩
    obtain ⟨e, he0, hee⟩ := List.mem_map.mp hm0
    cases hee
    exact (noFree _ _ _ he0).elim
  have ks := ks_program prims D _ (witness_raw K circuits settings top tree D A x p) _ _ _ _ ks0 r hr
  have safe := TreeRawSaltCertificatesProof.Preserves.simulateQ prims _ _
    (TreeRawSaltCertificatesProof.safe_boundaryCompiler prims D) _ _ _ _
    (safe_initial prims D A x z pre s hs p hp ([], [])) r hr
  have bal := balanced_program prims D (witness K circuits settings top tree D A x p) _ _ _ _
    (balanced_initial p.2.2 p.2.1.2 ([], [])) r hr
  have hblocks : ∀ b w', r.2.2 b = some w' → TreeSaltAt (decodeResult r).2.2 b (List.ofFn w') :=
    fun b w' hbw => (block_read prims K circuits settings top tree D A x z pre s hs p hp _ hm r.2.2
      r.1.1.2.1 rfl b w' hbw).2
  have hle := digestsAt_le D r.1.1.2 r.1.2 r.2.1 r.2.2 ks safe ready a ha (List.ofFn w)
    (List.ne_nil_of_length_pos (by rw [List.length_ofFn]; norm_num)) huniq hblocks
  have hdr := draws_le_reads r.1.1.2 r.2.1 r.2.2 a
  have hb := bal a
  change digestsAt (List.ofFn w) (r.1.1.2.2.flatMap (LogPiece.decode r.2.1 r.2.2)) ≤
    readsOf a (r.1.1.2.2.flatMap (LogPiece.decode r.2.1 r.2.2))
  omega

/-- The exact `TreeSaltFirstStage.LiteralTransport` on the fixed compiled first stage. -/
theorem literalTransport : LiteralTransport prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall α pre s hs p hp i hi ka r hr clean w hav e he hes
  have hopen := setup_open prims D A x z pre s hs p hp
  have hlaw := first_law prims K circuits settings top tree D A x p hopen ([], logSalts p.2.2)
  have hm : decodeResult r ∈
      support (TreeSaltPairsFinal.first prims K circuits settings top tree D A x p) := by
    rw [mem_support_iff, probOutput_congr rfl hlaw, ← mem_support_iff, support_map]
    exact ⟨r, hr, rfl⟩
  have hdec : ∀ e', LogPiece.literal e' ∈ r.1.1.2.2 → e' ∈ (decodeResult r).2.2 :=
    fun e' h' => List.mem_flatMap.mpr ⟨_, h', List.mem_singleton_self _⟩
  obtain ⟨t, out⟩ := e
  rcases t with (u | y) | u
  · exact ⟨u, rfl⟩
  · exfalso
    have noProg : NoProgram (decodeResult r).2.2 := by
      have hm' := hm
      rw [first_eq] at hm'
      exact logged_noProgram prims D _ (first_noProgram K circuits settings top tree D A x p) p.2
        (setup_noProgram prims D A x z pre s hs p hp) _ hm'
    exact noProg _ (hdec _ he) y rfl
  · exfalso
    obtain ⟨hh, rfl⟩ := projection_some u _ hes
    have read_a := block_read prims K circuits settings top tree D A x z pre s hs p hp _ hm r.2.2
      r.1.1.2.1 rfl (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) ⟨i, hi⟩) w hav
    have agree := TreeSaltPairsFinal.first_agreement_from prims K circuits settings top tree D A x z hx
      pre s hs p hp _ hm clean.1
    have huniq : ∀ c, TreeSaltAt (decodeResult r).2.2 c (List.ofFn w) → c = (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) ⟨i, hi⟩) := by
      intro c hc
      by_contra hca
      have hcF : c ∈ (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) :=
        TreeSaltPairsFinal.agreement_mem _ _ _ agree c.1 c.2.1 c.2.2 0 _ (hc ⟨0, by decide⟩)
      obtain ⟨k, hk⟩ := TreeSaltPairsFinal.mem_enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) c hcF
      have hne : (⟨i, hi⟩ : Fin (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2).card) ≠ k := fun h => hca (by rw [← hk, ← h])
      exact clean_no_reuse D (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) _ clean ⟨i, hi⟩ k hne ka _ List.length_ofFn read_a.2
        (by rw [hk]; exact hc)
    have hsrc := source_count prims K circuits settings top tree D A x z pre s hs p hp _ hm (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) ⟨i, hi⟩) ka w huniq
    have safe := TreeRawSaltCertificatesProof.Preserves.simulateQ prims _ _
      (TreeRawSaltCertificatesProof.safe_boundaryCompiler prims D) _ _ _ _
      (safe_initial prims D A x z pre s hs p hp ([], logSalts p.2.2)) r hr
    have bal := balanced_program prims D (firstBoundary K circuits settings top tree D A x p) _ _ _ _
      (balanced_initial p.2.2 p.2.1.2 _) r hr
    have hrd := reads_le_draws D r.1.1.2 r.1.2 r.2.1 r.2.2 safe (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) ⟨i, hi⟩) ka
    have hge := digests_ge r.1.1.2 r.2.1 r.2.2 (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) ⟨i, hi⟩) w hav hh out he
    have hb := bal (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) ⟨i, hi⟩)
    change digestsAt (List.ofFn w) (r.1.1.2.2.flatMap (LogPiece.decode r.2.1 r.2.2)) ≤
      readsOf (TreeSaltPairsFinal.enumerate (TreeSaltPairsFinal.firstSet circuits settings tree x p.1.2) ⟨i, hi⟩) (r.1.1.2.2.flatMap (LogPiece.decode r.2.1 r.2.2)) at hsrc
    omega

/-- The exact first-stage bound `CrossFirstStage` (A130). -/
theorem crossFirstStage : CrossFirstStage prims K circuits settings :=
  crossFirstStage_of_literal prims K circuits settings (literalTransport prims K circuits settings)

/-- The exact cross-pair bound `CrossHiddenBound` (A118, A127). -/
theorem crossHiddenBound : CrossHiddenBound prims K circuits settings :=
  crossHiddenBound_of_literal prims K circuits settings (literalTransport prims K circuits settings)

/-- The original guarded pair bounds `PairBoundsGuardedFrom` (A117). -/
theorem pairBoundsGuardedFrom : LifetimeSaltGuarded.PairBoundsGuardedFrom prims K circuits settings :=
  pairBoundsGuardedFrom_of_literal prims K circuits settings (literalTransport prims K circuits settings)

end Final

end ThresholdLeanXmssSecurity.TreeSaltLiteralTransport

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.source_provenance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.source_provenance

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.source_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.source_count

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.balanced_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.balanced_program

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.literalTransport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.literalTransport

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.crossFirstStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.crossFirstStage

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.crossHiddenBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.crossHiddenBound

/-- info: 'ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.pairBoundsGuardedFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeSaltLiteralTransport.pairBoundsGuardedFrom
