import ThresholdLeanXmssSecurity.Proof.TreeLockstepStages
import ThresholdLeanXmssSecurity.Proof.TreeSetupKeys
import ThresholdLeanXmssSecurity.Proof.TreeLockstepRun

/-!
# The lockstep on the reachable configurations

`TreeLockstepStagesGoal` asks for one cut `k₀` between the salt reads of the log and the salt
reads of the next round. This file moves the next-round half from the round to the honest steps.

* `SegmentSalts P p` states that each `PRG` input that the program `p` reads before its next
  exchange satisfies `P`. `SegmentSaltsStep` lifts it to a suspended step. A step that is done
  satisfies it at once, so an operator that aborted needs no output.
* `WorldSalts` carries it through the logged world, and `worldSalts_round` through one real round.
* `treeLockstepStagesGoal_of_segments` proves `TreeLockstepStagesGoal` from
  `TreeLockstepSegmentsGoal`, and `treeTwinDigestGoal3_of_segments` gives `TreeTwinDigestGoal3`.
* `treeStagesReach_setupKeys` moves `treeSetup_phase_agree` to `TreeStagesReach`. Each reachable
  configuration runs from a PRSS setup whose honest keys agree, and it extends the setup log.
* `treeLockstepSalts_first` moves the salts of the first run from one encoding to any other.

`TreeLockstepSegmentsGoal` asks for common keys, one encoding and a cut `k₀` on each
reachable configuration with no budget collision, such that the log reads lie below `k₀` and the
next segment of each honest step reads from `k₀` on. Its proof needs these parts.

* After `n` exchanges, the post-setup program of an operator with the chunks `js` is at a
  position that only `js` and `n` fix. `TreeTwinWithin` gives only upper bounds on the exchanges,
  so each sub-protocol needs its exact count.
* The honest operators agree on the encoding of the second run also on aborted prefixes.
  `TreeLockstepOpenedGoal` covers complete outputs only, so it does not give this part.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

section Segment

/-- Each `PRG` input that the program reads before its next exchange satisfies `P`. -/
inductive SegmentSalts {α : Type} (P : PrgInput C → Prop) :
    OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | pure (out : Option α) : SegmentSalts P (pure out)
  | queryLocal (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) (Option α))
      (hq : ∀ x, q = .inr (.inr x) → P x) (h : ∀ r, SegmentSalts P (k r)) :
      SegmentSalts P (.roll (.inl (.inl q)) k)
  | round (out : Mail C E) (k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α)) :
      SegmentSalts P (.roll (.inl (.inr out)) k)

/-- A suspended honest step whose resumption satisfies `SegmentSalts P` for each inbox. -/
def SegmentSaltsStep {α : Type} (P : PrgInput C → Prop) : Step C E RealSpec α → Prop
  | .done _ => True
  | .wait _ resume => ∀ inbox, SegmentSalts P (resume inbox)
  | .call input _ => input.elim

variable (circuits : Circuits)

/-- The `PRG` inputs that `TreeLockstepSalts keys parameter js lo hi` admits. -/
def LockstepSaltInput (keys : C.Term → HashOutput) (parameter : PublicParameter)
    (js : List (List Job)) (lo hi : ℕ) (x : PrgInput C) : Prop :=
  ∀ (T : C.Term) (key : HashOutput) (label g : ℕ), x = (.term T, key, label, 2, g) →
    key = keys T ∧ ∃ k, lo ≤ k ∧ k < hi ∧ k < js.length ∧
      batchCount circuits parameter (js.getD k []) ≠ 0 ∧
      label = lockstepSaltLabel circuits parameter js k

/-- The salts of the first run of a bottom tree follow the lockstep for every encoding. -/
theorem treeLockstepSalts_first (settings : Settings) (keys : C.Term → HashOutput)
    (parameter : PublicParameter) (enc enc' : Encoding) (tree : Tree) (lo hi : ℕ) (log : TreeSimLog C)
    (h : TreeLockstepSalts circuits keys parameter (lockstepChunks settings enc tree) lo hi log)
    (hhi : ∀ b, tree = .bottom b → hi ≤ (chunks settings.batchSize (bottomJobs b)).length) :
    TreeLockstepSalts circuits keys parameter (lockstepChunks settings enc' tree) lo hi log := by
  intro T key label g b mem
  obtain ⟨hkey, k, hlo, hk, hlen, hcount, hlabel⟩ := h T key label g b mem
  have hfirst : ∀ b, tree = .bottom b → k < (chunks settings.batchSize (bottomJobs b)).length :=
    fun b hb => hk.trans_le (hhi b hb)
  have hjobs := lockstepChunks_getD_first settings enc enc' tree k hfirst
  refine ⟨hkey, k, hlo, hk, ?_, hjobs ▸ hcount, ?_⟩
  · rwa [lockstepChunks_length] at hlen ⊢
  · rw [hlabel]
    unfold lockstepSaltLabel
    rw [hjobs, lockstepStart_first circuits settings parameter enc enc' tree k fun b hb => (hfirst b hb).le]

end Segment

section World

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (prims : Primitives) (D : C.Coalition)

/-- Each honest `PRG` entry that a run of `p` appends to the log satisfies `P`. -/
def WorldSalts {β : Type} (P : PrgInput C → Prop) (p : OracleComp (WorldSpec C) β) : Prop :=
  ∀ (s : TreeSimState C) r, r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s) →
    ∃ l, r.2.2 = s.2 ++ l ∧ ∀ x b,
      (⟨.inr (.inr (.inr x)), b⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ l → P x

theorem WorldSalts.pure {β : Type} (P : PrgInput C → Prop) (b : β) :
    WorldSalts prims D P (Pure.pure b) := by
  intro s r hr
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst r
  exact ⟨[], by simp, fun _ _ h => by simp at h⟩

theorem WorldSalts.bind {β γ : Type} {P : PrgInput C → Prop} {p : OracleComp (WorldSpec C) β}
    {k : β → OracleComp (WorldSpec C) γ} (hp : WorldSalts prims D P p)
    (hk : ∀ b, WorldSalts prims D P (k b)) : WorldSalts prims D P (p >>= k) := by
  intro s r hr
  rw [simulateQ_bind, StateT.run_bind] at hr
  obtain ⟨x, hx, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  obtain ⟨l₁, hl₁, h₁⟩ := hp s x hx
  obtain ⟨l₂, hl₂, h₂⟩ := hk x.1 x.2 r hr
  refine ⟨l₁ ++ l₂, by rw [hl₂, hl₁, List.append_assoc], fun y b hmem => ?_⟩
  rcases List.mem_append.mp hmem with hm | hm
  · exact h₁ y b hm
  · exact h₂ y b hm

theorem WorldSalts.query_bind {β : Type} {P : PrgInput C → Prop} (t : (WorldSpec C).Domain)
    (k : (WorldSpec C).Range t → OracleComp (WorldSpec C) β)
    (ht : ∀ x, t = .inr (.inr (.inr x)) → P x) (hk : ∀ u, WorldSalts prims D P (k u)) :
    WorldSalts prims D P (OracleComp.lift (OracleSpec.query t) >>= k) := by
  intro s r hr
  rw [simulateQ_bind, StateT.run_bind] at hr
  obtain ⟨x, hx, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  have hx' : x ∈ support ((treeSimLoggedWorld prims D t).run s) := by simpa using hx
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hx'
  obtain ⟨y, _, rfl⟩ := hx'
  obtain ⟨l, hl, h⟩ := hk y.1 _ r hr
  refine ⟨⟨t, y.1⟩ :: l, by rw [hl]; simp, fun z b hmem => ?_⟩
  rcases List.mem_cons.mp hmem with he | hm
  · exact ht z (congrArg Sigma.fst he).symm
  · exact h z b hm

theorem worldSalts_counted {β : Type} (P : PrgInput C → Prop) (oa : OracleComp (SimulatorSpec C) β) :
    WorldSalts prims D P (counted oa) := by
  induction oa using OracleComp.inductionOn with
  | pure b =>
    have : counted (Pure.pure b : OracleComp (SimulatorSpec C) β) = Pure.pure b := simulateQ_pure _ _
    rw [this]
    exact WorldSalts.pure prims D P b
  | query_bind q f ih =>
    simp only [counted] at ih ⊢
    exact WorldSalts.query_bind prims D _ _ (fun _ h => by cases h) ih

theorem worldSalts_free_advance {α : Type} {P : PrgInput C → Prop}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : SegmentSalts P p) :
    WorldSalts prims D P (free (advance p)) := by
  induction h with
  | pure out =>
    change WorldSalts prims D P (free (Pure.pure (Step.done out)))
    rw [free_pure]
    exact WorldSalts.pure prims D P _
  | queryLocal q k hq h ih =>
    change WorldSalts prims D P
      (free (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (k r)))
    rw [free_bind]
    simp only [free]
    exact WorldSalts.query_bind prims D _ _ (fun x he => hq x (by cases he; rfl)) ih
  | round out k =>
    simpa only [advance, free_pure] using WorldSalts.pure prims D P _

theorem worldSalts_sequenceFin {γ : Type} {P : PrgInput C → Prop} :
    ∀ {n : ℕ} (f : Fin n → OracleComp (WorldSpec C) γ), (∀ i, WorldSalts prims D P (f i)) →
      WorldSalts prims D P (Concrete.sequenceFin f)
  | 0, f, _ => by
    simp only [Concrete.sequenceFin]
    exact WorldSalts.pure prims D P _
  | n + 1, f, hf => by
    simp only [Concrete.sequenceFin]
    exact WorldSalts.bind prims D (hf 0) fun _ => WorldSalts.bind prims D
      (worldSalts_sequenceFin (fun i : Fin n => f i.succ) fun i => hf i.succ) fun _ =>
        WorldSalts.pure prims D P _

/-- A real round of honest steps whose next segments satisfy `P` appends a log whose honest `PRG`
entries satisfy `P`. -/
theorem worldSalts_round {α : Type} (P : PrgInput C → Prop) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (hs : ∀ i, i ∉ D.1 → SegmentSaltsStep P (steps i)) :
    WorldSalts prims D P (stepRound worldRoles D A noFunctionality state steps) := by
  rw [stepRound_real]
  refine WorldSalts.bind prims D (worldSalts_counted prims D P _) fun x => ?_
  obtain ⟨state', sent⟩ := x
  refine WorldSalts.bind prims D ?_ fun _ => WorldSalts.pure prims D P _
  rw [free_sequenceFin]
  refine worldSalts_sequenceFin prims D _ fun i => ?_
  unfold roundLocal
  cases he : steps i with
  | done out =>
    simp only [free_pure]
    exact WorldSalts.pure prims D P _
  | call input _ => exact input.elim
  | wait out resume =>
    simp only
    split_ifs with hi
    · simp only [free_pure]
      exact WorldSalts.pure prims D P _
    · have h := hs i hi
      rw [he] at h
      exact worldSalts_free_advance prims D (h _)

end World

section Reach

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- A real round extends the log. -/
theorem treeStages_round_prefix {α : Type} (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec α) (s : TreeSimState C)
    (u : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) × TreeSimState C)
    (hu : u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality state steps).run s)) :
    s.2 <+: u.2.2 := by
  rw [show stepRound (treeSimRealRoles prims D) D A noFunctionality state steps =
      simulateQ (treeSimLoggedWorld prims D) (stepRound worldRoles D A noFunctionality state steps) by
    rw [simulateQ_stepRound]; rfl] at hu
  exact treeSimLoggedWorld_prefix prims D _ s u hu

/-- Real rounds extend the log. -/
theorem treeStages_steps_prefix (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) :
    ∀ (fuel : ℕ) (state : A.State) (steps : C.Party → Step C E RealSpec TreeOutput)
      (s : TreeSimState C) (a : TreeSimConfig A (TreeSimState C)),
      a ∈ support ((executeSteps (treeSimRealRoles prims D) D A noFunctionality fuel state steps).run s) →
      s.2 <+: a.2.2
  | 0, state, steps, s, a, ha => by
    simp only [executeSteps, StateT.run_pure, support_pure, Set.mem_singleton_iff] at ha
    subst a
    exact List.prefix_refl _
  | fuel + 1, state, steps, s, a, ha => by
    simp only [executeSteps] at ha
    split_ifs at ha with hdone
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at ha
      subst a
      exact List.prefix_refl _
    · simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at ha
      obtain ⟨u, hu, ha⟩ := ha
      exact (treeStages_round_prefix prims D A state steps s u hu).trans
        (treeStages_steps_prefix D A fuel u.1.1 u.1.2.1 u.2 a ha)

/-- Each reachable configuration runs from a supported PRSS setup and its continuation. It extends
the log of the setup, and the honest outputs of the setup agree on the key of each common term when
the configuration has no budget collision. -/
theorem treeStagesReach_setupKeys (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (state : A.State)
    (s : TreeSimState C) (n : ℕ) (a : TreeSimConfig A (TreeSimState C))
    (reach : TreeStagesReach prims K circuits settings top tree D A x state s n a) :
    ∃ p ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality setupRounds state
        (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s),
    ∃ next ∈ support ((simulateQ (treeSimLoggedWorld prims D)
        (treeSimContinue (treeSimRealCont K circuits settings top tree x) p.1.2)).run p.2),
      a ∈ support ((executeSteps (treeSimRealRoles prims D) D A noFunctionality n p.1.1 next.1).run
        next.2) ∧
      p.2.2 <+: a.2.2 ∧ (¬ TreeSimHashBudgetCollision a.2.2 →
        ∀ (i j : C.Party) (ki kj : PrssKeys C), p.1.2 i = some ki → p.1.2 j = some kj →
          ∀ T, i ∈ C.holders T → j ∈ C.holders T → ki.term T = kj.term T) := by
  simp only [TreeStagesReach, treeStagesTrace, StateT.run_bind, support_bind,
    Set.mem_iUnion] at reach
  obtain ⟨p, hp, next, hnext, ha⟩ := reach
  have hpre : p.2.2 <+: a.2.2 := (treeSimLoggedWorld_prefix prims D _ p.2 next hnext).trans
    (treeStages_steps_prefix prims D A n p.1.1 next.1 next.2 a ha)
  exact ⟨p, hp, next, hnext, ha, hpre, fun good =>
    treeSetup_phase_agree prims D A state s p hp
      (fun hc => good (treeSimHashBudgetCollision_mono hpre hc))⟩

end Reach

section Goal

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (circuits : Circuits) (prims : Primitives) (K : Constants C E) (settings : Settings)

/-- The lockstep on the honest steps of the reachable configurations of `TreeLockstepStagesGoal`.
Without a budget collision in the log so far, the salts of the log lie at the batches below some
`k₀`, and the next segment of each honest step reads salts only at the batches from `k₀`. It holds
the agreement on the keys and on the encoding, and the label schedule of one operator indexed by
the round. -/
def TreeLockstepSegmentsGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux),
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ∀ (padding : OracleComp (LocalSpec C) Unit),
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∀ n (a : TreeSimConfig A (TreeSimState C)),
      TreeStagesReach prims K circuits settings top tree D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      ¬ TreeSimHashBudgetCollision a.2.2 →
      ∃ (keys : C.Term → HashOutput) (enc : Encoding) (k₀ : ℕ),
        TreeLockstepSalts circuits keys parameter (lockstepChunks settings enc tree) 0 k₀ a.2.2 ∧
        ∀ i, i ∉ D.1 → SegmentSaltsStep (LockstepSaltInput circuits keys parameter
          (lockstepChunks settings enc tree) k₀ (lockstepChunks settings enc tree).length) (a.1.2 i)

/-- The round log of honest steps whose next segments read at the admitted inputs follows the
lockstep. -/
theorem treeLockstepSalts_round (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (keys : C.Term → HashOutput) (parameter : PublicParameter) (js : List (List Job)) (lo hi : ℕ)
    (a : TreeSimConfig A (TreeSimState C))
    (hs : ∀ i, i ∉ D.1 → SegmentSaltsStep (LockstepSaltInput circuits keys parameter js lo hi) (a.1.2 i))
    (u : (A.State × (C.Party → Step C E RealSpec TreeOutput) × (C.Party → C.Party → Option (Msg E))) ×
      TreeSimState C)
    (hu : u ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2))
    (l : TreeSimLog C) (hl : u.2.2 = a.2.2 ++ l) :
    TreeLockstepSalts circuits keys parameter js lo hi l := by
  have hround : (stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2) =
      simulateQ (treeSimLoggedWorld prims D) (stepRound worldRoles D A noFunctionality a.1.1 a.1.2) := by
    rw [simulateQ_stepRound]
    rfl
  rw [hround] at hu
  obtain ⟨l', hl', h⟩ := worldSalts_round prims D _ A a.1.1 a.1.2 hs a.2 u hu
  have hll : l = l' := List.append_cancel_left (hl.symm.trans hl')
  subst hll
  intro T key label g b mem
  exact h _ b mem T key label g rfl

/-- `TreeLockstepStagesGoal` from the lockstep on the honest steps. -/
theorem treeLockstepStagesGoal_of_segments
    (segments : TreeLockstepSegmentsGoal circuits prims K settings) :
    TreeLockstepStagesGoal circuits prims K settings := by
  intro hbatch top tree D A parameter seeds pairs z p hp padding r hr n a reach good
  obtain ⟨keys, enc, k₀, before, steps⟩ :=
    segments hbatch top tree D A parameter seeds pairs z p hp padding r hr n a reach good
  exact ⟨keys, enc, k₀, before, fun u hu l hl =>
    treeLockstepSalts_round circuits prims D A keys parameter _ k₀ _ a steps u hu l hl⟩

/-- `TreeTwinDigestGoal3` from the lockstep on the honest steps. -/
theorem treeTwinDigestGoal3_of_segments
    (segments : TreeLockstepSegmentsGoal circuits prims K settings) :
    TreeTwinDigestGoal3 prims K circuits settings :=
  treeTwinDigestGoal3_of_lockstepStages circuits prims K settings
    (treeLockstepStagesGoal_of_segments circuits prims K settings segments)

end Goal

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepStagesGoal_of_segments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepStagesGoal_of_segments

/-- info: 'ThresholdLeanXmssSecurity.treeStagesReach_setupKeys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeStagesReach_setupKeys

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepSalts_first' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepSalts_first

/-- info: 'ThresholdLeanXmssSecurity.treeTwinDigestGoal3_of_segments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinDigestGoal3_of_segments

end ThresholdLeanXmssSecurity
