import ThresholdLeanXmssSecurity.Proof.TreeLockstepSegments
import ThresholdLeanXmssSecurity.Proof.TreeLockstepOpenedRest

/-!
# Encoding and the salt schedule on partial runs

The top-tree case of `TreeLockstepEncodingGoal` holds for every prefix.
For bottom trees, all salts through two exchanges after the first run use an
encoding-independent schedule. The first possible second-run salt is later.
`treeLockstepEncodingGoal_of_late_bottom` and its converse therefore identify
the corresponding interface with `TreeLockstepEncodingLateBottomGoal`.

The actual `ceremonyOutput` factors at its grind-selected encoding. Its entire
second-run continuation follows that fixed encoding, including later aborts.
The public selection makes no exchanges or salt queries, and its encoding is
`treeLockstepBottomEncoding` of the first-run outputs under coherent actual
hash replies, without requiring any successful second run or final output.

The bottom-tree interface requires common first-run outputs and one coherent selection witness
for every reached late prefix, then retain those witnesses through the joint
round induction. Successful final records alone do not cover aborted prefixes.

The pinned and working leanVM proof libraries were searched for schedule and
encoding lemmas. The synchronous MPC schedule is specific to this protocol;
the existing threshold schedule and public replay lemmas are reused below.
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
variable (circuits : Circuits) (settings : Settings)

/-- An encoding change preserves a salt read belonging to the first run. -/
theorem lockstepSchedule_first (mode : ReshareMode) (parameter : PublicParameter)
    (keys : C.Term → HashOutput) (self : C.Party) (b : Fin (2 ^ layerHeight))
    (enc enc' : Encoding) (j : ℕ) (T : C.Term) (key : HashOutput) (label k : ℕ)
    (hk : k < (chunks settings.batchSize (bottomJobs b)).length)
    (hcount : batchCount circuits parameter
      ((lockstepChunks settings enc (.bottom b)).getD k []) ≠ 0)
    (hkey : key = keys T) (hheld : self ∈ C.holders T)
    (hlabel : label = lockstepSaltLabel circuits parameter
      (lockstepChunks settings enc (.bottom b)) k)
    (hround : j = lockstepSaltRound circuits mode parameter
      (lockstepChunks settings enc (.bottom b)) k) :
    LockstepSchedule circuits mode parameter keys self
      (lockstepChunks settings enc' (.bottom b)) j T key label := by
  have hjobs := lockstepChunks_getD_first settings enc enc' (.bottom b) k
    (fun b' hb => by cases hb; exact hk)
  have hstart := lockstepStart_first circuits settings parameter enc enc' (.bottom b) k
    (fun b' hb => by cases hb; exact hk.le)
  have hroundStart := lockstepRoundStart_first circuits settings mode parameter enc enc'
    (.bottom b) k (fun b' hb => by cases hb; exact hk.le)
  refine ⟨hkey, hheld, k, ?_, ?_, ?_, ?_⟩
  · simp only [lockstepChunks, List.length_append]
    omega
  · rwa [← hjobs]
  · simpa only [lockstepSaltLabel, hjobs, hstart] using hlabel
  · simpa only [lockstepSaltRound, hjobs, hroundStart] using hround

/-- No second-run salt can occur before three further exchanges. This also
covers the transition that computes the encoding, without assuming it succeeds. -/
theorem ceremonySchedule_before_second (mode : ReshareMode) (parameter : PublicParameter)
    (keys : C.Term → HashOutput) (self : C.Party) (b : Fin (2 ^ layerHeight))
    (enc : Encoding) (j : ℕ) (T : C.Term) (key : HashOutput) (label : ℕ)
    (early : j ≤ lockstepRoundStart circuits mode parameter
      (lockstepChunks settings enc (.bottom b))
      (chunks settings.batchSize (bottomJobs b)).length + 2)
    (h : CeremonySchedule circuits settings mode parameter keys self (.bottom b) j T key label) :
    LockstepSchedule circuits mode parameter keys self
      (lockstepChunks settings enc (.bottom b)) j T key label := by
  obtain ⟨enc', hkey, hheld, k, hklen, hc, hl, hj⟩ := h
  have first : k < (chunks settings.batchSize (bottomJobs b)).length := by
    by_contra hn
    have hm := lockstepRoundStart_mono circuits mode parameter
      (lockstepChunks settings enc' (.bottom b)) (show
        (chunks settings.batchSize (bottomJobs b)).length ≤ k by omega)
    have he := lockstepRoundStart_first circuits settings mode parameter enc' enc (.bottom b)
      (chunks settings.batchSize (bottomJobs b)).length (fun b' hb => by cases hb; rfl)
    rw [he] at hm
    unfold lockstepSaltRound at hj
    omega
  exact lockstepSchedule_first circuits settings mode parameter keys self b enc' enc j T key label k
    first hc hkey hheld hl hj

/-- The top-tree schedule has no encoding-dependent jobs. -/
theorem ceremonySchedule_top (mode : ReshareMode) (parameter : PublicParameter)
    (keys : C.Term → HashOutput) (self : C.Party) (enc : Encoding)
    (j : ℕ) (T : C.Term) (key : HashOutput) (label : ℕ)
    (h : CeremonySchedule circuits settings mode parameter keys self .top j T key label) :
    LockstepSchedule circuits mode parameter keys self
      (lockstepChunks settings enc .top) j T key label := by
  obtain ⟨enc', h⟩ := h
  exact h

/-- The exact retained-log and next-segment conclusion of the global goal. -/
def TreeEncodingScheduleAt {α : Type} (x : C.Party → Keys C) (tree : Tree)
    (keysOf : C.Party → Option (PrssKeys C)) (D : C.Coalition) (n : ℕ)
    (steps : C.Party → Step C E RealSpec α) (log : TreeSimLog C) : Prop :=
  ∃ enc : Encoding,
    (∀ y b, (⟨.inr (.inr (.inr y)), b⟩ : (t : (WorldSpec C).Domain) ×
        (WorldSpec C).Range t) ∈ log →
      ∃ i, i ∉ D.1 ∧ ∃ j ≤ n,
        SaltRead (OpScheduleEnc circuits settings x tree enc keysOf i j) y) ∧
    ∀ i, i ∉ D.1 → SegmentSaltsStep
      (SaltRead (OpScheduleEnc circuits settings x tree enc keysOf i (n + 1))) (steps i)

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- A schedule conversion through the current exchange preserves both the
retained log and the next segment, including already aborted operators. -/
theorem treeEncodingScheduleAt_of_uniform {α : Type} (x : C.Party → Keys C) (tree : Tree)
    (keysOf : C.Party → Option (PrssKeys C)) (D : C.Coalition) (n : ℕ)
    (steps : C.Party → Step C E RealSpec α) (log : TreeSimLog C) (enc : Encoding)
    (uniform : ∀ i, i ∉ D.1 → ∀ j ≤ n + 1, ∀ T key label,
      OpSchedule circuits settings x tree keysOf i j T key label →
      OpScheduleEnc circuits settings x tree enc keysOf i j T key label)
    (hsteps : ∀ i, i ∉ D.1 →
      SegmentsStep (OpSchedule circuits settings x tree keysOf i) (n + 1) (steps i))
    (hlog : ∀ y b, (⟨.inr (.inr (.inr y)), b⟩ : (t : (WorldSpec C).Domain) ×
        (WorldSpec C).Range t) ∈ log →
      ∃ i, i ∉ D.1 ∧ ∃ j ≤ n,
        SaltRead (OpSchedule circuits settings x tree keysOf i j) y) :
    TreeEncodingScheduleAt circuits settings x tree keysOf D n steps log := by
  refine ⟨enc, ?_, ?_⟩
  · intro y b hy
    obtain ⟨i, hi, j, hj, h⟩ := hlog y b hy
    exact ⟨i, hi, j, hj, fun T key label g he =>
      uniform i hi j (by omega) T key label (h T key label g he)⟩
  · intro i hi
    have h := hsteps i hi
    revert h
    cases steps i with
    | done out => intro _; trivial
    | call input _ => exact input.elim
    | wait out resume =>
      intro h inbox
      exact (h inbox).segmentSalts fun y hy T key label g he =>
        uniform i hi (n + 1) le_rfl T key label (hy T key label g he)

/-- Top-tree encoding agreement holds on every prefix, irrespective of final
outputs. It follows from the actual partial-run schedules. -/
theorem treeEncodingScheduleAt_top {α : Type} (x : C.Party → Keys C)
    (keysOf : C.Party → Option (PrssKeys C)) (D : C.Coalition) (n : ℕ)
    (steps : C.Party → Step C E RealSpec α) (log : TreeSimLog C)
    (hsteps : ∀ i, i ∉ D.1 →
      SegmentsStep (OpSchedule circuits settings x .top keysOf i) (n + 1) (steps i))
    (hlog : ∀ y b, (⟨.inr (.inr (.inr y)), b⟩ : (t : (WorldSpec C).Domain) ×
        (WorldSpec C).Range t) ∈ log →
      ∃ i, i ∉ D.1 ∧ ∃ j ≤ n,
        SaltRead (OpSchedule circuits settings x .top keysOf i j) y) :
    TreeEncodingScheduleAt circuits settings x .top keysOf D n steps log := by
  refine treeEncodingScheduleAt_of_uniform circuits settings x .top keysOf D n steps log
    (fun _ => digit 0) ?_ hsteps hlog
  intro i hi j hj T key label h
  obtain ⟨prss, hp, h⟩ := h
  exact ⟨prss, hp, ceremonySchedule_top circuits settings settings.mode (x i).parameter
    prss.term i _ j T key label h⟩

/-- Before the first possible second-run salt, a bottom-tree prefix and its
next segments share any chosen encoding's schedule. No success assumption is
made about an operator's final output. -/
theorem treeEncodingScheduleAt_before_second {α : Type} (x : C.Party → Keys C)
    (keysOf : C.Party → Option (PrssKeys C)) (D : C.Coalition) (n : ℕ)
    (steps : C.Party → Step C E RealSpec α) (log : TreeSimLog C)
    (b : Fin (2 ^ layerHeight)) (enc : Encoding)
    (early : ∀ i, i ∉ D.1 → n + 1 ≤
      lockstepRoundStart circuits settings.mode (x i).parameter
        (lockstepChunks settings enc (.bottom b))
        (chunks settings.batchSize (bottomJobs b)).length + 2)
    (hsteps : ∀ i, i ∉ D.1 →
      SegmentsStep (OpSchedule circuits settings x (.bottom b) keysOf i) (n + 1) (steps i))
    (hlog : ∀ y v, (⟨.inr (.inr (.inr y)), v⟩ : (t : (WorldSpec C).Domain) ×
        (WorldSpec C).Range t) ∈ log →
      ∃ i, i ∉ D.1 ∧ ∃ j ≤ n,
        SaltRead (OpSchedule circuits settings x (.bottom b) keysOf i j) y) :
    TreeEncodingScheduleAt circuits settings x (.bottom b) keysOf D n steps log := by
  refine treeEncodingScheduleAt_of_uniform circuits settings x (.bottom b) keysOf D n steps log
    enc ?_ hsteps hlog
  intro i hi j hj T key label h
  obtain ⟨prss, hp, h⟩ := h
  exact ⟨prss, hp, ceremonySchedule_before_second circuits settings settings.mode (x i).parameter
    prss.term i b enc j T key label (hj.trans (early i hi)) h⟩

variable (prims : Primitives) (K : Constants C E)

/-- The remaining exact bottom-tree obligation after the encoding-independent
prefix. It retains every original reach, setup, log and collision premise. -/
def TreeLockstepEncodingLateBottomGoal : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (b : Fin (2 ^ layerHeight)) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux),
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top (.bottom b) D A parameter seeds pairs z),
    ∀ (padding : OracleComp (LocalSpec C) Unit),
    ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
    ∀ n (a : TreeSimConfig A (TreeSimState C)),
      TreeStagesReach prims K circuits settings top (.bottom b) D A (dealtKeys parameter seeds pairs)
        p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) n a →
      ¬ TreeSimHashBudgetCollision a.2.2 →
      ∀ ps ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality setupRounds p.2.1
        (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run ((r.2, p.2.2.1.2), p.2.2.2)),
      ∀ l, a.2.2 = ps.2.2 ++ l →
      (∀ i, i ∉ D.1 → SegmentsStep (OpSchedule circuits settings (dealtKeys parameter seeds pairs) (.bottom b)
        ps.1.2 i) (n + 1) (a.1.2 i)) →
      (∀ y v, (⟨.inr (.inr (.inr y)), v⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ l →
        ∃ i, i ∉ D.1 ∧ ∃ j ≤ n,
          SaltRead (OpSchedule circuits settings (dealtKeys parameter seeds pairs) (.bottom b) ps.1.2 i j) y) →
      lockstepRoundStart circuits settings.mode parameter
        (lockstepChunks settings (fun _ => digit 0) (.bottom b))
        (chunks settings.batchSize (bottomJobs b)).length + 2 < n + 1 →
      TreeEncodingScheduleAt circuits settings (dealtKeys parameter seeds pairs) (.bottom b)
        ps.1.2 D n a.1.2 l

/-- The complete goal reduces to the late bottom-tree prefixes. The top-tree
case and the first bottom run, including the gap before the next salt, are proved. -/
theorem treeLockstepEncodingGoal_of_late_bottom
    (late : TreeLockstepEncodingLateBottomGoal circuits settings prims K) :
    TreeLockstepEncodingGoal circuits prims K settings := by
  intro hbatch top tree D A parameter seeds pairs z p hp padding r hr n a reach good ps hps
    l hl hsteps hlog
  cases tree with
  | top =>
    exact treeEncodingScheduleAt_top circuits settings (dealtKeys parameter seeds pairs)
      ps.1.2 D n a.1.2 l hsteps hlog
  | bottom b =>
    by_cases early : n + 1 ≤ lockstepRoundStart circuits settings.mode parameter
        (lockstepChunks settings (fun _ => digit 0) (.bottom b))
        (chunks settings.batchSize (bottomJobs b)).length + 2
    · exact treeEncodingScheduleAt_before_second circuits settings (dealtKeys parameter seeds pairs)
        ps.1.2 D n a.1.2 l b (fun _ => digit 0) (fun _ _ => early) hsteps hlog
    · exact late hbatch top b D A parameter seeds pairs z p hp padding r hr n a reach good ps hps
        l hl hsteps hlog (by omega)

/-- The late-prefix statement is exactly a restriction of the original goal. -/
theorem treeLockstepEncodingLateBottomGoal_of_goal
    (all : TreeLockstepEncodingGoal circuits prims K settings) :
    TreeLockstepEncodingLateBottomGoal circuits settings prims K := by
  intro hbatch top b D A parameter seeds pairs z p hp padding r hr n a reach good ps hps
    l hl hsteps hlog _
  exact all hbatch top (.bottom b) D A parameter seeds pairs z p hp padding r hr n a reach good ps hps
    l hl hsteps hlog


/-- The actual second-run continuation of `ceremonyOutput`. The encoding is
an argument selected by the preceding grind, and is kept for every later branch. -/
def treeEncodingBottomTail {m : Type → Type} [Monad m]
    (lift : ∀ {α : Type}, OracleComp HashSpec α → m α) (parameter : PublicParameter)
    (run : List Job → m (Option (List (List Bit)))) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (root : Digest)
    (randomness : Randomness) (encoding : Encoding) : m (Option TreeOutput) := do
  let keys := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
    (List.finRange numChains).map fun l => (bottomKey b k, l)
  let cpk := fun (e : KeyIndex) (l : ChainIndex) =>
    let bits := outputs.getD (keys.idxOf (e, l)) []
    (digestAt bits 0, digestAt bits 1, digestAt bits 2)
  let commitment := fun (e : KeyIndex) =>
    digestAt (outputs.getD (keys.length + e.val % 2 ^ layerHeight) []) 0
  let message := bytesLE 16 root
  let some values ← run (signJobs b encoding) | pure none
  let path ← lift (merklePath parameter topLayer top.chainEnd (topKey b))
  let signature : LayerSignature := ⟨randomness, fun l => digestAt (values.getD l.val []) 0, path⟩
  let topRoot ← lift (Concrete.layerRoot parameter topLayer (topKey b) message signature)
  if topRoot ≠ some top.root then pure none else
    pure (some (.bottom ⟨cpk, commitment, root, signature⟩))

/-- Definitional factorization of the real public ceremony at its selected
encoding. The first-run outputs and grind result are the original ones. -/
theorem ceremonyOutput_bottom_tail {m : Type → Type} [Monad m]
    (lift : ∀ {α : Type}, OracleComp HashSpec α → m α) (parameter : PublicParameter)
    (run : List Job → m (Option (List (List Bit)))) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) :
    ceremonyOutput lift parameter run top (.bottom b) = (do
      let keys := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
        (List.finRange numChains).map fun l => (bottomKey b k, l)
      let some outputs ← run (bottomJobs b) | pure none
      let cpk := fun (e : KeyIndex) (l : ChainIndex) =>
        let bits := outputs.getD (keys.idxOf (e, l)) []
        (digestAt bits 0, digestAt bits 1, digestAt bits 2)
      let ρ := digestAt (outputs.getD (keys.length + 2 ^ layerHeight) []) 0
      let root ← lift (merkleNode parameter bottomLayer (fun e l => (cpk e l).2.2) layerHeight b.val)
      let message := bytesLE 16 root
      let base ← lift (truncateHash <$> Concrete.oracleHash
        (randomizerInput parameter topLayer (topKey b) ρ message))
      let some (randomness, encoding) ← lift
        (grind parameter topLayer (topKey b) message base randomizerAttemptLimit 0) | pure none
      treeEncodingBottomTail lift parameter run top b outputs root randomness encoding) := rfl

/-- The entire actual second-run continuation follows its selected encoding,
including branches that later abort. This strengthens the bottom case of
`treeSegmentsFrom_ceremonyAfterSetup`, whose `CeremonySchedule` forgets it. -/
theorem treeSegmentRun_bottom_tail (ctx : Context C) (top : TopTree)
    (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) (root : Digest)
    (randomness : Randomness) (enc : Encoding) (tag : ℕ) :
    let js := lockstepChunks settings enc (.bottom b)
    let first := (chunks settings.batchSize (bottomJobs b)).length
    TreeSegmentRun
      (LockstepSchedule circuits settings.mode ctx.keys.parameter ctx.prss.term ctx.self js)
      (lockstepRoundStart circuits settings.mode ctx.keys.parameter js first)
      (lockstepRoundStart circuits settings.mode ctx.keys.parameter js js.length)
      ((treeEncodingBottomTail
        (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
        (fun oa => StateT.lift (oracleStep (tweakable oa))) ctx.keys.parameter
        (batched settings.batchSize (ceremonyBatch K circuits settings ctx))
        top b outputs root randomness enc).run
        (lockstepStart circuits ctx.keys.parameter js first, tag)).run := by
  dsimp only
  unfold treeEncodingBottomTail
  refine treeSegmentRun_batched_bind K circuits settings ctx _ (signJobs b enc) [] _ tag _
    (by simp [lockstepChunks]) (fun _ _ _ _ h => h) _ fun v tag' => ?_
  have hlen : (chunks settings.batchSize (bottomJobs b)).length +
      (chunks settings.batchSize (signJobs b enc)).length =
      (lockstepChunks settings enc (.bottom b)).length := by simp [lockstepChunks]
  rw [hlen]
  cases v with
  | none => exact TreeSegmentRun.pure _ _
  | some values =>
    refine TreeSegmentRun.tweakable_bind _ fun path => ?_
    refine TreeSegmentRun.tweakable_bind _ fun topRoot => ?_
    split_ifs <;> exact TreeSegmentRun.pure _ _


/-- The public computations between the two bottom runs, retaining the root
and the actual successful grind result. It makes no network exchange. -/
def treeEncodingPublicChoice (parameter : PublicParameter) (b : Fin (2 ^ layerHeight))
    (outputs : List (List Bit)) : PartyM C E RealSpec (Option (Digest × Randomness × Encoding)) := do
  let keys := (List.finRange (2 ^ layerHeight)).flatMap fun k =>
    (List.finRange numChains).map fun l => (bottomKey b k, l)
  let chainEnd := fun (e : KeyIndex) (l : ChainIndex) =>
    digestAt (outputs.getD (keys.idxOf (e, l)) []) 2
  let root ← oracleStep (tweakable (merkleNode parameter bottomLayer chainEnd layerHeight b.val))
  let message := bytesLE 16 root
  let ρ := digestAt (outputs.getD (keys.length + 2 ^ layerHeight) []) 0
  let base ← oracleStep (tweakable (truncateHash <$> Concrete.oracleHash
    (randomizerInput parameter topLayer (topKey b) ρ message)))
  let g ← oracleStep (tweakable
    (grind parameter topLayer (topKey b) message base randomizerAttemptLimit 0))
  pure (g.map fun r => (root, r))

/-- Selection already fixes the encoding at the boundary. No successful
second run or final ceremony output is needed. The shared hash function must
agree with the actual public replies in this prefix. -/
theorem treeEncodingPublicChoice_encoding
    (allowed : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Prop)
    (hash : Query C → HashOutput)
    (hhash : ∀ q u, allowed (.inl (.inl (.inr (.inl q)))) u → hash q = u)
    (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit))
    (root : Digest) (randomness : Randomness) (enc : Encoding)
    (choice : TreeSimCheckAllowed allowed
      (treeEncodingPublicChoice (C := C) (E := E) parameter b outputs).run
      (some (some (root, randomness, enc)))) :
    treeLockstepBottomEncoding prims hash parameter b outputs = enc := by
  unfold treeEncodingPublicChoice at choice
  obtain ⟨root', hr, choice⟩ := choice.option_bind_inv _ _ _
  obtain ⟨base, hb, choice⟩ := choice.option_bind_inv _ _ _
  obtain ⟨g, hg, choice⟩ := choice.option_bind_inv _ _ _
  have he := Option.some.inj choice.pure_inv
  cases g with
  | none => cases he
  | some g =>
    obtain ⟨r, e⟩ := g
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    have hroot := treeSimCheck_public_replay prims allowed hash hhash _ _ hr
    have hbase := treeSimCheck_public_replay prims allowed hash hhash _ _ hb
    have hgrind := treeSimCheck_public_replay prims allowed hash hhash _ _ hg
    unfold treeLockstepBottomEncoding
    dsimp only
    rw [← hroot, ← hbase, ← hgrind]
    rfl


/-- The public selection makes neither exchanges nor salt queries. -/
theorem treeSegmentRun_publicChoice
    (S : ℕ → C.Term → HashOutput → ℕ → Prop) (j : ℕ)
    (parameter : PublicParameter) (b : Fin (2 ^ layerHeight)) (outputs : List (List Bit)) :
    TreeSegmentRun S j j (treeEncodingPublicChoice (C := C) (E := E) parameter b outputs).run := by
  unfold treeEncodingPublicChoice
  refine TreeSegmentRun.oracle_bind (RoSalts.tweakable (fun _ _ _ => False) _)
    (fun _ _ _ h => h.elim) _ fun root => ?_
  refine TreeSegmentRun.oracle_bind (RoSalts.tweakable (fun _ _ _ => False) _)
    (fun _ _ _ h => h.elim) _ fun base => ?_
  refine TreeSegmentRun.oracle_bind (RoSalts.tweakable (fun _ _ _ => False) _)
    (fun _ _ _ h => h.elim) _ fun g => ?_
  exact TreeSegmentRun.pure _ _


/-- info: 'ThresholdLeanXmssSecurity.treeLockstepEncodingGoal_of_late_bottom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepEncodingGoal_of_late_bottom

/-- info: 'ThresholdLeanXmssSecurity.treeLockstepEncodingLateBottomGoal_of_goal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeLockstepEncodingLateBottomGoal_of_goal

/-- info: 'ThresholdLeanXmssSecurity.treeEncodingScheduleAt_before_second' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeEncodingScheduleAt_before_second

/-- info: 'ThresholdLeanXmssSecurity.treeSegmentRun_bottom_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSegmentRun_bottom_tail

/-- info: 'ThresholdLeanXmssSecurity.treeEncodingPublicChoice_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeEncodingPublicChoice_encoding

/-- info: 'ThresholdLeanXmssSecurity.treeSegmentRun_publicChoice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSegmentRun_publicChoice

end ThresholdLeanXmssSecurity
