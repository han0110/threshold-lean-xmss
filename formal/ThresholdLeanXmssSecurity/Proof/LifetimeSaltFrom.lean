import ThresholdLeanXmssSecurity.Proof.LifetimeJointSimStages
import ThresholdLeanXmssSecurity.Proof.TreeRawSaltSteps
import ThresholdLeanXmssSecurity.Proof.LifetimeJointSalt
import ThresholdLeanXmssSecurity.Proof.TreeSaltPairs

/-!
# Salt estimates after a counted selecting prefix

The compiler begins with the retained public cache and its literal transcript. The
initial guess list contains the counted digest salts of that transcript. Start-state
table estimates and two-stage pair certificates can therefore be applied to each
selected continuation without resampling its prefix.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section
namespace ThresholdLeanXmssSecurity.LifetimeSaltFrom

open LifetimeBridge LifetimeJointSim LifetimeJointSimStages
open TreeRawSaltFlowProof TreeRawSaltRepresentationProof TreeRawSaltNormalizeProof
attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The state after a counted local prefix from the empty state. -/
def prefixState (prims : Primitives) (D : C.Coalition) {α : Type}
    (pre : OracleComp (LocalSpec C) α) : ProbComp (α × TreeSimState C) :=
  (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary pre)).run ((∅, ∅), [])

theorem loggedPrefix_eq (prims : Primitives) (D : C.Coalition) (pre : Selector C) :
    loggedPrefix prims D pre = prefixState prims D (jointPrefix pre) := rfl

/-- The salts of the counted digest entries of a log. -/
def logDigestSalts (log : TreeSimLog C) : List (List Bit) :=
  log.filterMap fun e => match e.1 with
    | .inl (.inl t) => digestSaltProjection t
    | _ => none

/-- The opaque table estimate with a public cache covered by an initial guess list. -/
def StartTableBound (prims : Primitives) : Prop :=
  ∀ {α : Type} (H n : ℕ), 0 < H →
    ∀ p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α,
    IsQueryBoundP p TreeSimHashSaltPrivate H →
    IsQueryBoundP p treeSimHashSaltTableCharged n →
    ∀ (guesses : List (List Bit)) (cache : HashCache C),
    DigestSaltsCovered cache guesses.toFinset →
    Pr[AddressHit | tableRun prims p ([], guesses) cache ∅] ≤
      ((2 * H * (guesses.length + n) : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- A counted prefix covers cached digest salts and bounds the guess-list length. -/
def PrefixSaltState (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) {α : Type} (pre : OracleComp (LocalSpec C) α) (q0 : ℕ),
    IsQueryBoundP pre Counted q0 → ∀ s ∈ support (prefixState prims D pre),
    DigestSaltsCovered s.2.1.1 (logDigestSalts s.2.2).toFinset ∧
      (logDigestSalts s.2.2).length ≤ q0

def ceremonyProgramFrom (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (log : TreeSimLog C) :
    OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) (Bool × CompilerState C) :=
  (simulateQ (boundaryCompiler D)
    (ceremonyBoundary K circuits settings top tree D A x z Z)).run (∅, log.map .literal)

omit [Fintype E] [DecidableEq E] in
theorem ceremonyProgramFrom_nil (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    ceremonyProgramFrom K circuits settings top tree D A x z Z [] =
      ceremonyProgram K circuits settings top tree D A x z Z := rfl

/-- Compiler budgets and event transport from an actual counted prefix state. -/
def CeremonyCompilerCertificatesFrom (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ {α : Type} (pre : OracleComp (LocalSpec C) α), ∀ s ∈ support (prefixState prims D pre),
    let H := treeBatches settings tree * (C.t * termCount C)
    let p := ceremonyProgramFrom K circuits settings top tree D A x z Z s.2.2
    IsQueryBoundP p TreeSimHashSaltPrivate H ∧
    IsQueryBoundP p treeSimHashSaltTableCharged (q + H) ∧
    ∀ r ∈ support (tableRun prims p ([], logDigestSalts s.2.2) s.2.1.1 ∅),
      ¬ TreeSimHashCollision (ceremonyDecode r).2.2 →
      TreeSimSaltGuess D (ceremonyDecode r).2.2 → AddressHit r

omit [Fintype E] [DecidableEq E] in
theorem certificates_of_from (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (h : CeremonyCompilerCertificatesFrom prims K circuits settings) :
    CeremonyCompilerCertificates prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hs
  have := h hb top tree D A x z Z q hx hq hs (pure ()) (((), ((∅, ∅), [])))
    (by change _ ∈ support (pure _ : ProbComp _); simp)
  simpa [ceremonyProgramFrom_nil, logDigestSalts] using this

/-- The setup of `treeSaltSetup` from a start state. -/
def treeSaltSetupFrom (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (s : TreeSimState C) :
    ProbComp ((A.State × (C.Party → Option (PrssKeys C))) × TreeSimState C) := do
  let start ← (simulateQ (treeSimLoggedWorld prims D)
    (worldRoles.adversary (A.start (corruptInputs D x) z))).run s
  (executePhase (treeSimRealRoles prims D) D A noFunctionality setupRounds start.1
    (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run start.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem treeSaltSetupFrom_empty (prims : Primitives) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux) :
    treeSaltSetupFrom prims D A x z ((∅, ∅), []) = treeSaltSetup prims D A x z := rfl

variable {prims : Primitives} {K : Constants C E} {circuits : Circuits} {settings : Settings}

/-- The same two-stage salt-pair certificate after a retained counted prefix. -/
def TreeSaltStagesPairsFrom (splits : TreeSaltStageSplits prims K circuits settings) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ {α : Type} (pre : OracleComp (LocalSpec C) α), ∀ s ∈ support (prefixState prims D pre),
    ∀ p ∈ support (treeSaltSetupFrom prims D A x z s.2),
    ∃ (n₁ : ℕ) (addr₁ : Fin n₁ → C.Term × HashOutput × ℕ)
      (n₂ : (splits top tree D A x Z p).View → ℕ)
      (addr₂ : (m : (splits top tree D A x Z p).View) → Fin (n₂ m) → C.Term × HashOutput × ℕ),
      TreeSaltStagesCover (splits top tree D A x Z p) (treeBatches settings tree * termCount C)
        n₁ addr₁ n₂ addr₂ ∧
      ∀ i j : ℕ, i < j →
        Pr[fun r => ¬ TreeSimHashBudgetCollision r.2.2 ∧
            TreeSaltPairReuse D (Fin.append addr₁ (addr₂ r.1)) i j r.2.2 |
          (splits top tree D A x Z p).paired] ≤ (2 ^ 256 : ℝ≥0∞)⁻¹

omit [Fintype E] [DecidableEq E] in
theorem pairs_of_from (splits : TreeSaltStageSplits prims K circuits settings)
    (h : TreeSaltStagesPairsFrom splits) : TreeSaltStagesPairs splits := by
  intro hb top tree D A x z Z q hx hq hs p hp
  exact h hb top tree D A x z Z q hx hq hs (pure ()) (((), ((∅, ∅), [])))
    (by change _ ∈ support (pure _ : ProbComp _); simp) p (by simpa [treeSaltSetupFrom_empty] using hp)

end ThresholdLeanXmssSecurity.LifetimeSaltFrom

namespace ThresholdLeanXmssSecurity.LifetimeSaltFrom
open TreeRawSaltFlowProof TreeRawSaltRepresentationProof TreeRawSaltNormalizeProof
variable {C : Committee}

theorem literal_ready (cache : HashCache C) (log : TreeSimLog C) :
    Ready cache ∅ ((∅, log.map .literal) : CompilerState C) := by
  intro piece hp
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hp
  trivial

theorem literal_decode (cache : HashCache C) (log : TreeSimLog C) :
    decodeCompiler cache ∅ ((∅, log.map .literal) : CompilerState C) = ((cache, ∅), log) := by
  have hl : (log.map LogPiece.literal).flatMap (LogPiece.decode cache (∅ : BlockCache C)) = log := by
    induction log with
    | nil => rfl
    | cons e l ih => simpa [LogPiece.decode] using ih
  simp only [decodeCompiler, hl]
  congr 2
  funext x
  cases h : saltAt x <;> simp [restore, h]

end ThresholdLeanXmssSecurity.LifetimeSaltFrom

namespace ThresholdLeanXmssSecurity.LifetimeSaltFrom
open LifetimeBridge LifetimeJointSim LifetimeJointSimStages LifetimeJointSalt
open TreeRawSaltFlowProof TreeRawSaltRepresentationProof TreeRawSaltNormalizeProof
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

omit [Fintype E] [DecidableEq E] in
/-- The compiled ceremony retains the initial public cache and every prefix log entry. -/
theorem ceremonyProgramFrom_law (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (cache : HashCache C) (log : TreeSimLog C) :
    𝒟[(simulateQ (treeSimLoggedWorld prims D)
      (treeRealGame K circuits settings top tree D A x z Z)).run ((cache, ∅), log)] =
    𝒟[ceremonyDecode <$> tableRun prims
      (ceremonyProgramFrom K circuits settings top tree D A x z Z log)
      ([], logDigestSalts log) cache ∅] := by
  have h := compiler_program_law (E := E) prims D (TreeRawSaltStepsProof.boundaryCompilerSteps prims D)
    (ceremonyBoundary K circuits settings top tree D A x z Z)
    (ceremonyBoundary_safe K circuits settings top tree D A x z Z)
    ([], logDigestSalts log) cache ∅ (∅, log.map .literal) (literal_ready cache log)
  rw [literal_decode, ceremonyBoundary_source] at h
  exact h

/-- The setup/continuation decomposition holds with an arbitrary retained state. -/
theorem treeSaltSetupFrom_split (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (s : TreeSimState C) :
    (fun r => (r.1, r.2.2)) <$> (simulateQ (treeSimLoggedWorld prims D)
      (treeRealGame K circuits settings top tree D A x z Z)).run s =
    treeSaltSetupFrom prims D A x z s >>= treeSaltAfterSetup prims K circuits settings top tree D A x Z := by
  obtain ⟨fuel, hf⟩ : ∃ fuel, ceremonyFuel circuits settings = fuel + 3 :=
    ⟨ceremonyFuel circuits settings - 3, by simp only [ceremonyFuel, setupRounds]; omega⟩
  have hs : ceremonyFuel circuits settings - setupRounds = fuel := by
    simp only [hf, setupRounds]; omega
  have hc : (fun i => ceremony K circuits settings i (x i) top tree) =
      fun i => prssSetup i >>= treeSimRealCont K circuits settings top tree x i := rfl
  unfold treeRealGame distinguish realExecution treeSaltSetupFrom treeSaltAfterSetup
  simp only [simulateQ_bind, StateT.run_bind, map_bind, bind_assoc, hs]
  apply bind_congr
  intro start
  rw [simulateQ_executePhase, hf, hc, treeSim_prssSetup_split]
  simp only [treeSimRealRoles, treeSimRealObserve, StateT.run_bind, bind_assoc]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- A start-state compiler certificate bounds the guess event on that same retained transcript. -/
theorem guess_from (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (tables : StartTableBound (C := C) prims)
    (certificates : CeremonyCompilerCertificatesFrom prims K circuits settings)
    (hb : 0 < settings.batchSize) (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q0 q : ℕ) (hx : DealtInputs D x)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) (hsmall : q < 2 ^ 128)
    {α : Type} (pre : OracleComp (LocalSpec C) α) (s : α × TreeSimState C)
    (hs : s ∈ support (prefixState prims D pre))
    (hcover : DigestSaltsCovered s.2.1.1 (logDigestSalts s.2.2).toFinset)
    (hlen : (logDigestSalts s.2.2).length ≤ q0) :
    (Pr[fun r => ¬ TreeSimHashCollision r.2.2 ∧ TreeSimSaltGuess D r.2.2 |
      (simulateQ (treeSimLoggedWorld prims D)
        (treeRealGame K circuits settings top tree D A x z Z)).run ((s.2.1.1, ∅), s.2.2)]).toReal ≤
      saltGuessBudget (C := C) settings (q0 + q) tree := by
  obtain ⟨hp, hc, he⟩ := certificates hb top tree D A x z Z q hx hq hsmall pre s hs
  let H := treeBatches settings tree * (C.t * termCount C)
  have law := ceremonyProgramFrom_law prims K circuits settings top tree D A x z Z s.2.1.1 s.2.2
  have hprob := OracleComp.probEvent_congr'
    (p := fun r => ¬TreeSimHashCollision r.2.2 ∧ TreeSimSaltGuess D r.2.2)
    (q := fun r => ¬TreeSimHashCollision r.2.2 ∧ TreeSimSaltGuess D r.2.2)
    (fun _ _ => Iff.rfl) law
  rw [hprob, probEvent_map]
  have hle : Pr[(fun r => ¬TreeSimHashCollision r.2.2 ∧ TreeSimSaltGuess D r.2.2) ∘ ceremonyDecode |
      tableRun prims (ceremonyProgramFrom K circuits settings top tree D A x z Z s.2.2)
        ([], logDigestSalts s.2.2) s.2.1.1 ∅] ≤
      ((2 * H * (q0 + q + H) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    refine (probEvent_mono (fun r hr hh => he r hr hh.1 hh.2)).trans ?_
    refine (tables H (q + H) (treeRawSalt_capacity_pos settings hb tree) _ hp hc
      (logDigestSalts s.2.2) s.2.1.1 hcover).trans ?_
    have hn : 2 * H * ((logDigestSalts s.2.2).length + (q + H)) ≤
        2 * H * (q0 + q + H) := Nat.mul_le_mul_left _ (by omega)
    gcongr 1
    exact_mod_cast hn
  refine (ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)) hle).trans_eq ?_
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  simp [saltGuessBudget, H, Nat.cast_mul, Nat.cast_add]

/-- Pair certificates after the same prefix bound the full-log reuse event. -/
theorem reuse_from (prims : Primitives) (K : Constants C E) (circuits : Circuits)
    (settings : Settings) (splits : TreeSaltStageSplits prims K circuits settings)
    (pairs : TreeSaltStagesPairsFrom splits) (hb : 0 < settings.batchSize)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ) (hx : DealtInputs D x)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) (hsmall : q < 2 ^ 128)
    {α : Type} (pre : OracleComp (LocalSpec C) α) (s : α × TreeSimState C)
    (hs : s ∈ support (prefixState prims D pre)) :
    (Pr[fun r => ¬TreeSimHashBudgetCollision r.2.2 ∧ TreeSimSaltReuse D r.2.2 |
      (simulateQ (treeSimLoggedWorld prims D)
        (treeRealGame K circuits settings top tree D A x z Z)).run s.2]).toReal ≤
      saltReuseBudget (C := C) settings tree := by
  have hle : Pr[fun r => ¬TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 |
      (fun r => (r.1, r.2.2)) <$> (simulateQ (treeSimLoggedWorld prims D)
        (treeRealGame K circuits settings top tree D A x z Z)).run s.2] ≤
      (((treeBatches settings tree * termCount C) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 257 := by
    rw [treeSaltSetupFrom_split]
    apply probEvent_bind_le_of_forall_le
    intro p hp
    obtain ⟨n₁, addr₁, n₂, addr₂, hcover, hpair⟩ := pairs hb top tree D A x z Z q hx hq hsmall pre s hs p hp
    exact treeSaltStages_reuse_le (splits top tree D A x Z p) D hcover hpair
  rw [probEvent_map] at hle
  refine (ENNReal.toReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp)) hle).trans_eq ?_
  simp [saltReuseBudget, ENNReal.toReal_div]

end ThresholdLeanXmssSecurity.LifetimeSaltFrom

namespace ThresholdLeanXmssSecurity.LifetimeSaltFrom
open LifetimeBridge LifetimeJointSim LifetimeJointSimStages LifetimeJointSalt
attribute [local instance] Classical.propDecidable
variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- Start-state compiler and pair certificates imply the original adaptive lifetime salt bounds. -/
theorem jointSaltBounds_of_from (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (tables : StartTableBound (C := C) prims) (prefixes : PrefixSaltState (C := C) prims)
    (certificates : CeremonyCompilerCertificatesFrom prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings) (pairs : TreeSaltStagesPairsFrom splits) :
    JointSaltBounds prims K circuits settings := by
  intro hb D pre A Z q0 q hpre hadv
  have bounds (p : JointInput C × TreeSimState C) (hp : p ∈ support (loggedPrefix prims D pre))
      (small : tailBudget (C := C) circuits settings q p.1.2.2.1 < 2 ^ 128) :
      (Pr[fun r => ¬TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2 |
        continuation prims K circuits settings D A Z p]).toReal ≤
          saltGuessBudget (C := C) settings (q0 + q) p.1.2.2.1 ∧
      (Pr[fun r => ¬TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2 |
        continuation prims K circuits settings D A Z p]).toReal ≤
          saltReuseBudget (C := C) settings p.1.2.2.1 := by
    have hx := loggedPrefix_dealt prims D pre p hp
    have hs : p ∈ support (prefixState prims D (jointPrefix pre)) := hp
    obtain ⟨covered, length⟩ := prefixes D (jointPrefix pre) q0 hpre p hs
    have hq : q < 2 ^ 128 := lt_of_le_of_lt (Nat.le_add_right q _) small
    have hempty := loggedPrefix_private_empty prims D pre p hp
    have hstate : ((p.2.1.1, ∅), p.2.2) = p.2 := by
      rw [← hempty]
    have guess := guess_from prims K circuits settings tables certificates hb
      p.1.2.1 p.1.2.2.1 D A p.1.1 p.1.2.2.2 Z q0 q hx hadv hq
      (jointPrefix pre) p hs covered length
    rw [hstate] at guess
    have reuse := reuse_from prims K circuits settings splits pairs hb
      p.1.2.1 p.1.2.2.1 D A p.1.1 p.1.2.2.2 Z q hx hadv hq (jointPrefix pre) p hs
    simpa only [continuation, selectedGame, Bool.false_eq_true, if_false,
      probEvent_map, Function.comp_def] using And.intro guess reuse
  constructor
  · apply trace_event_le prims K circuits settings D pre A Z
      (fun input r => tailBudget (C := C) circuits settings q input.2.2.1 < 2 ^ 128 ∧
        ¬TreeSimHashCollision r.2 ∧ TreeSimSaltGuess D r.2)
    intro p hp
    by_cases small : tailBudget (C := C) circuits settings q p.1.2.2.1 < 2 ^ 128
    · simpa only [small, true_and, if_pos] using (bounds p hp small).1
    · simp only [small, false_and, if_false]
      rw [probEvent_False]
      exact le_refl 0
  · apply trace_event_le prims K circuits settings D pre A Z
      (fun input r => tailBudget (C := C) circuits settings q input.2.2.1 < 2 ^ 128 ∧
        ¬TreeSimHashBudgetCollision r.2 ∧ TreeSimSaltReuse D r.2)
    intro p hp
    by_cases small : tailBudget (C := C) circuits settings q p.1.2.2.1 < 2 ^ 128
    · simpa only [small, true_and, if_pos] using (bounds p hp small).2
    · simp only [small, false_and, if_false]
      rw [probEvent_False]
      exact le_refl 0

end ThresholdLeanXmssSecurity.LifetimeSaltFrom

namespace ThresholdLeanXmssSecurity.LifetimeSaltFrom
variable {C : Committee} {α : Type}

set_option backward.isDefEq.respectTransparency false in
/-- The reversed counted salt log is the query projection of the same local run. -/
theorem prefix_projected_support (prims : Primitives) (D : C.Coalition)
    (oa : OracleComp (LocalSpec C) α) (s : TreeSimState C) (r : α × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (worldRoles.adversary oa)).run s)) :
    (r.1, r.2.1.1, (logDigestSalts r.2.2).reverse) ∈ support
      ((simulateQ (projectQueries (localAnswer prims) digestSaltProjection) oa).run
        (s.1.1, (logDigestSalts s.2).reverse)) := by
  induction oa using OracleComp.inductionOn generalizing s r with
  | pure a =>
    change r ∈ support (pure (a, s) : ProbComp _) at hr
    simp only [support_pure, Set.mem_singleton_iff] at hr
    subst r
    simp
  | query_bind t k ih =>
    rw [show worldRoles.adversary (OracleComp.lift (OracleSpec.query t) >>= k) =
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun a => worldRoles.adversary (k a)
      from rfl, adversary_query] at hr
    simp only [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    have he := simulateQ_spec_query (treeSimLoggedWorld prims D) (.inl (.inl t))
    erw [he] at hmid
    simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hmid
    obtain ⟨u, hu, rfl⟩ := hmid
    simp only [streamWorld, onHash, StateT.run_mk, support_map, Set.mem_image] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, projectQueries_run,
      bind_map_left, mem_support_bind_iff]
    refine ⟨v, hv, ?_⟩
    have h := ih v.1 _ r hr
    cases hp : digestSaltProjection t <;>
      simpa [logDigestSalts, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
        List.reverse_append, hp] using h

/-- Every retained digest cache entry is covered by a counted prefix salt query. -/
theorem prefixSaltState (prims : Primitives) : PrefixSaltState (C := C) prims := by
  classical
  intro D α pre q0 hpre s hs
  have h := prefix_projected_support prims D pre ((∅, ∅), []) s hs
  have covered := projectQueries_digest_covered prims pre ∅ []
    (by intro salt h he; simp at he) _ h
  have length := projectQueries_length (localAnswer prims) Counted digestSaltProjection
    digestSaltProjection_counted hpre ∅ [] h
  constructor
  · intro salt digest hd
    exact List.mem_toFinset.mpr (List.mem_reverse.mp (covered salt digest hd))
  · simpa using length

end ThresholdLeanXmssSecurity.LifetimeSaltFrom

namespace ThresholdLeanXmssSecurity.LifetimeSaltFrom
variable {C : Committee} {α : Type}
attribute [local instance] Classical.propDecidable

set_option backward.isDefEq.respectTransparency false in
/-- The projected salt flag starts with the retained public guesses. -/
theorem salt_coordinate_public_from {κ : Type} [DecidableEq κ]
    (prims : Primitives) (i : κ) (table : κ → List Bit) (salt : List Bit)
    (p : OracleComp (TreeSimHashSaltTableSpec κ C) α) (cache : HashCache C) (guesses : List (List Bit)) :
    Pr[fun r => salt ∈ r.2.2 |
      (simulateQ (projectQueries (treeSimHashSaltTableAnswer prims (Function.update table i salt))
        treeSimHashSaltTablePublic) p).run (cache, guesses)] ≤
    Pr[fun r => r.2.2 = true |
      (simulateQ (flagQueries (treeSimHashSaltTableAnswer prims (Function.update table i salt))
        (treeSimHashSaltCoordinateHit i table salt)) p).run (cache, decide (salt ∈ guesses))] := by
  have he := projectQueries_flag (treeSimHashSaltTableAnswer prims (Function.update table i salt))
    treeSimHashSaltTablePublic salt p cache guesses
  have hmono := treeSimHash_flag_mono (treeSimHashSaltTableAnswer prims (Function.update table i salt))
    (fun t => decide (treeSimHashSaltTablePublic t = some salt))
    (treeSimHashSaltCoordinateHit i table salt) (by
      intro t ht
      cases t with
      | inl t => simp [treeSimHashSaltTablePublic] at ht
      | inr t =>
        simp only [decide_eq_true_eq] at ht
        change digestSaltHit salt t = true
        rw [digestSaltHit_projection]
        simpa only [decide_eq_true_eq, treeSimHashSaltTablePublic] using ht) p cache (decide (salt ∈ guesses)) (decide (salt ∈ guesses)) (fun h => h)
  have he' : (simulateQ (flagQueries (treeSimHashSaltTableAnswer prims (Function.update table i salt))
      (fun t => decide (treeSimHashSaltTablePublic t = some salt))) p).run (cache, decide (salt ∈ guesses)) =
      (fun z : α × HashCache C × List (List Bit) => (z.1, z.2.1, decide (salt ∈ z.2.2))) <$>
      (simulateQ (projectQueries (treeSimHashSaltTableAnswer prims (Function.update table i salt))
        treeSimHashSaltTablePublic) p).run (cache, guesses) := by
    convert he.symm using 1 <;> congr
    · funext t
      by_cases h : treeSimHashSaltTablePublic t = some salt <;> simp only [h, decide_true, decide_false]
    · funext z
      by_cases h : salt ∈ z.2.2 <;> simp only [h, decide_true, decide_false]
  rw [he', probEvent_map] at hmono
  simpa only [Function.comp_def, decide_eq_true_eq] using hmono


/-- Resampling one coordinate pays for both old and new public guesses. -/
theorem salt_table_one_bound_from {κ : Type} [Fintype κ] [DecidableEq κ]
    [SampleableType (κ → Fin 256 → Bit)] (prims : Primitives) (i : κ)
    (p : OracleComp (TreeSimHashSaltTableSpec κ C) α) (n : ℕ)
    (hn : IsQueryBoundP p treeSimHashSaltTableCharged n)
    (cache : HashCache C) (guesses : List (List Bit))
    (hc : DigestSaltsCovered cache guesses.toFinset) :
    Pr[fun z => List.ofFn (z.1 i) ∈ z.2.2.2 | (do
      let table ← $ᵗ (κ → Fin 256 → Bit)
      let r ← (simulateQ (projectQueries (treeSimHashSaltTableAnswer prims (fun j => List.ofFn (table j)))
        treeSimHashSaltTablePublic) p).run (cache, guesses)
      pure (table, r))] ≤ ((guesses.length + n : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let run := fun table : κ → Fin 256 → Bit => do
    let r ← (simulateQ (projectQueries (treeSimHashSaltTableAnswer prims (fun j => List.ofFn (table j)))
      treeSimHashSaltTablePublic) p).run (cache, guesses)
    pure (table, r)
  change Pr[fun z => List.ofFn (z.1 i) ∈ z.2.2.2 | ($ᵗ (κ → Fin 256 → Bit)) >>= run] ≤ _
  rw [← treeSimHash_uniform_coordinate_event i run]
  apply probEvent_bind_le_of_forall_le
  intro table _
  have he (salt : Fin 256 → Bit) :
      (fun j => List.ofFn (Function.update table i salt j)) =
        Function.update (fun j => List.ofFn (table j)) i (List.ofFn salt) := by
    funext j
    by_cases h : j = i
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne h]
  have hb := treeSimHash_salt_coordinate_bound prims i (fun j => List.ofFn (table j))
    cache guesses.toFinset hc p n hn
  have hb' : ((guesses.toFinset.card + n : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((guesses.length + n : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
    apply ENNReal.div_le_div_right
    exact_mod_cast Nat.add_le_add_right (List.toFinset_card_le guesses) n
  refine le_trans ?_ (hb.trans hb')
  simp only [run, bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def,
    Function.update_self, he]
  apply ENNReal.tsum_le_tsum
  intro salt
  apply mul_le_mul_right
  simpa only [List.mem_toFinset] using
    salt_coordinate_public_from prims i (fun j => List.ofFn (table j)) (List.ofFn salt) p cache guesses


/-- A finite salt table has one shared retained public cache. -/
theorem salt_table_bound_from {κ : Type} [Fintype κ] [DecidableEq κ]
    [SampleableType (κ → Fin 256 → Bit)] (prims : Primitives)
    (p : OracleComp (TreeSimHashSaltTableSpec κ C) α) (n : ℕ)
    (hn : IsQueryBoundP p treeSimHashSaltTableCharged n)
    (cache : HashCache C) (guesses : List (List Bit))
    (hc : DigestSaltsCovered cache guesses.toFinset) :
    Pr[fun z => ∃ i, List.ofFn (z.1 i) ∈ z.2.2.2 | (do
      let table ← $ᵗ (κ → Fin 256 → Bit)
      let r ← (simulateQ (projectQueries (treeSimHashSaltTableAnswer prims (fun j => List.ofFn (table j)))
        treeSimHashSaltTablePublic) p).run (cache, guesses)
      pure (table, r))] ≤ ((Fintype.card κ * (guesses.length + n) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  let run := do
    let table ← $ᵗ (κ → Fin 256 → Bit)
    let r ← (simulateQ (projectQueries (treeSimHashSaltTableAnswer prims (fun j => List.ofFn (table j)))
      treeSimHashSaltTablePublic) p).run (cache, guesses)
    pure (table, r)
  have hb := probEvent_exists_finset_le_sum Finset.univ run
    (fun i z => List.ofFn (z.1 i) ∈ z.2.2.2)
  simp only [Finset.mem_univ, true_and] at hb
  refine hb.trans ((Finset.sum_le_sum (fun i _ =>
    salt_table_one_bound_from prims i p n hn cache guesses hc)).trans_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_mul, mul_div_assoc]


/-- Lazy private salts obey the retained-cache bound by eager table sampling. -/
theorem lazy_salt_bound_from {κ : Type} [Fintype κ] [DecidableEq κ]
    [SampleableType (κ → Fin 256 → Bit)] (prims : Primitives)
    (p : OracleComp (TreeSimHashSaltTableSpec κ C) α) (n : ℕ)
    (hn : IsQueryBoundP p treeSimHashSaltTableCharged n)
    (cache : HashCache C) (guesses : List (List Bit))
    (hc : DigestSaltsCovered cache guesses.toFinset) :
    Pr[fun r => ∃ salt, salt ∈ r.1.2.1 ∧ salt ∈ r.1.2.2 |
      (simulateQ (treeSimHashBlockCacheAnswer (localAnswer prims))
        ((simulateQ treeSimHashSaltRead p).run ([], guesses))).run (cache, ∅)] ≤
      ((Fintype.card κ * (guesses.length + n) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  have he := treeSimHash_block_eager (localAnswer prims)
    ((simulateQ treeSimHashSaltRead p).run ([], guesses)) cache ∅
  have hp := OracleComp.probEvent_congr'
    (p := fun r => ∃ salt, salt ∈ r.1.2.1 ∧ salt ∈ r.1.2.2)
    (q := fun r => ∃ salt, salt ∈ r.1.2.1 ∧ salt ∈ r.1.2.2)
    (fun _ _ => Iff.rfl) he
  simp only [probEvent_map, Function.comp_def, tableExtending_empty] at hp
  rw [hp]
  apply le_trans _ (salt_table_bound_from prims p n hn cache guesses hc)
  simp only [bind_pure_comp, probEvent_bind_eq_tsum, probEvent_map, Function.comp_def]
  apply ENNReal.tsum_le_tsum
  intro table
  apply mul_le_mul_right
  rw [← treeSimHash_salt_read_erase prims table p ([], guesses) cache, probEvent_map]
  apply probEvent_mono
  intro r hr hs
  obtain ⟨salt, hu, hg⟩ := hs
  obtain ⟨i, hi⟩ := treeSimHash_salt_read_values prims table p ([], guesses)
    (by intro salt h; cases h) cache r hr salt hu
  exact ⟨i, hi ▸ hg⟩


end ThresholdLeanXmssSecurity.LifetimeSaltFrom

namespace ThresholdLeanXmssSecurity.LifetimeSaltFrom
open TreeRawSaltRepresentationProof
variable {C : Committee}
attribute [local instance] Classical.propDecidable

/-- Finite allocation preserves the retained public state and fits the raw salt coefficient. -/
theorem startTableBound (prims : Primitives) : StartTableBound (C := C) prims := by
  intro α H n hH p hprivate hcharged guesses cache hcovered
  have allocation := allocate_program_joint prims H p H hprivate [] ([], guesses) cache ∅
    (fun _ _ => rfl) (by simp)
  have empty : addressCache H ([] : List (TreeSimHashSaltBlock C)) ∅ = ∅ := by
    funext b
    simp [addressCache]
  rw [empty] at allocation
  rw [allocation, probEvent_map]
  have bound := lazy_salt_bound_from prims ((simulateQ (treeSimHashSaltAllocate H) p).run []) n
    (treeSimHash_salt_allocate_count H p n hcharged []) cache guesses hcovered
  change Pr[fun r : TreeRawSaltOutcome C H α => ∃ salt, salt ∈ r.1.2.1 ∧ salt ∈ r.1.2.2 |
    allocatedRun prims H p [] ([], guesses) cache ∅] ≤ _
  apply bound.trans
  simp only [Fintype.card_fin]
  apply ENNReal.div_le_div_right
  exact_mod_cast Nat.mul_le_mul_right (guesses.length + n) (show H + 1 ≤ 2 * H by omega)

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-- The two ceremony-specific certificates suffice for the adaptive lifetime salt estimates. -/
theorem jointSaltBounds_of_certificates (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (certificates : CeremonyCompilerCertificatesFrom prims K circuits settings)
    (splits : TreeSaltStageSplits prims K circuits settings) (pairs : TreeSaltStagesPairsFrom splits) :
    LifetimeJointSimStages.JointSaltBounds prims K circuits settings :=
  jointSaltBounds_of_from prims K circuits settings (startTableBound prims) (prefixSaltState prims)
    certificates splits pairs

end ThresholdLeanXmssSecurity.LifetimeSaltFrom

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltFrom.ceremonyProgramFrom_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeSaltFrom.ceremonyProgramFrom_law

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltFrom.guess_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeSaltFrom.guess_from

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltFrom.reuse_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeSaltFrom.reuse_from

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltFrom.jointSaltBounds_of_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeSaltFrom.jointSaltBounds_of_from

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltFrom.prefixSaltState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeSaltFrom.prefixSaltState

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltFrom.lazy_salt_bound_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeSaltFrom.lazy_salt_bound_from

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltFrom.startTableBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeSaltFrom.startTableBound

/-- info: 'ThresholdLeanXmssSecurity.LifetimeSaltFrom.jointSaltBounds_of_certificates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms ThresholdLeanXmssSecurity.LifetimeSaltFrom.jointSaltBounds_of_certificates
