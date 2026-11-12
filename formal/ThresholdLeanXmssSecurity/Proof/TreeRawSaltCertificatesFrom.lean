import ThresholdLeanXmssSecurity.Proof.LifetimeSaltFrom
import ThresholdLeanXmssSecurity.Proof.TreeRawSaltCertificates

/-!
# Ceremony certificates with a retained counted prefix

The compiler appends to its symbolic log without reading the existing entries.
Consequently an initial transcript changes neither its oracle calls nor its
query budgets. Counted prefix salts populate the initial public guess list;
ordinary prefix entries cannot introduce a hidden salt into the decoded log.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof
open TreeRawSaltFlowProof TreeRawSaltRepresentationProof TreeRawSaltNormalizeProof
open TreeRawSaltCertificatesProof LifetimeSaltFrom
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- A compiler action appends its output log independently of an existing prefix. -/
def LogPrefix {α : Type} (p : CompilerM C α) : Prop :=
  ∀ (pref : List (LogPiece C)) (state : CompilerState C),
    p.run (state.1, pref ++ state.2) =
      (fun r => (r.1, r.2.1, pref ++ r.2.2)) <$> p.run state

theorem LogPrefix.pure {α : Type} (a : α) : LogPrefix (pure a : CompilerM C α) := by
  intro pref state
  simp

theorem LogPrefix.bind {α β : Type} (p : CompilerM C α) (k : α → CompilerM C β)
    (hp : LogPrefix p) (hk : ∀ a, LogPrefix (k a)) : LogPrefix (p >>= k) := by
  intro pref state
  simp only [StateT.run_bind, hp pref state, bind_map_left, map_bind]
  apply bind_congr
  intro r
  exact hk r.1 pref r.2

theorem LogPrefix.map {α β : Type} (f : α → β) (p : CompilerM C α)
    (hp : LogPrefix p) : LogPrefix (f <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact hp.bind _ _ fun a => LogPrefix.pure (f a)

theorem LogPrefix.lift {α : Type}
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α) :
    LogPrefix (StateT.lift p : CompilerM C α) := by
  intro pref state
  simp [StateT.run_lift, bind_pure_comp, Functor.map_map]

theorem LogPrefix.mapM {α β : Type} (xs : List α) (f : α → CompilerM C β)
    (hf : ∀ a, LogPrefix (f a)) : LogPrefix (xs.mapM f) := by
  induction xs with
  | nil => exact LogPrefix.pure []
  | cons a xs ih =>
    rw [List.mapM_cons]
    exact (hf a).bind _ _ fun b => ih.map (List.cons b) _

theorem LogPrefix.simulateQ {ι α : Type} {S : OracleSpec ι}
    (impl : QueryImpl S (CompilerM C)) (p : OracleComp S α)
    (h : ∀ t, LogPrefix (impl t)) : LogPrefix (simulateQ impl p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa using LogPrefix.pure a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact (h t).bind _ _ ih

theorem emit_prefix (piece : LogPiece C) : LogPrefix (emit piece) := by
  intro pref state
  simp [emit, StateT.run_modify, List.append_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem publicAnswer_prefix (D : C.Coalition) (t : (WorldSpec C).Domain) :
    LogPrefix (publicAnswer D t) := by
  rcases t with (u | p) | (u | (q | x))
  all_goals simp only [publicAnswer]
  all_goals try exact LogPrefix.lift _
  · exact LogPrefix.pure false
  · split_ifs
    · intro pref state
      simp [StateT.run_bind, StateT.run_get, StateT.run_set,
        StateT.run_lift, bind_pure_comp, Functor.map_map]
    · exact LogPrefix.lift _

theorem publicQuery_prefix (D : C.Coalition) (t : (WorldSpec C).Domain) :
    LogPrefix (publicQuery D t) :=
  (publicAnswer_prefix D t).bind _ _ fun a =>
    (emit_prefix (.literal ⟨t, a⟩)).bind _ _ fun _ => LogPrefix.pure a

theorem publicDraw_prefix (D : C.Coalition) (name : KeyName C) (key : HashOutput) (label : ℕ) :
    LogPrefix (publicDraw D name key label) :=
  LogPrefix.simulateQ _ _ (publicQuery_prefix D)

theorem prepareTerm_prefix (D : C.Coalition) (ctx : Context C) (label : ℕ) (T : C.Term) :
    LogPrefix (prepareTerm D ctx label T) := by
  unfold prepareTerm
  split_ifs
  · exact (publicDraw_prefix D _ _ _).map _ _
  · exact (emit_prefix _).bind _ _ fun _ => LogPrefix.pure _
  · exact LogPrefix.pure _

theorem preparePairs_prefix (D : C.Coalition) (ctx : Context C) (label : ℕ) :
    LogPrefix (preparePairs D ctx label) := by
  apply LogPrefix.bind
  · apply LogPrefix.mapM
    intro j
    split_ifs
    · exact LogPrefix.pure _
    · exact publicDraw_prefix D _ _ _
  · intro _
    exact LogPrefix.pure ()

theorem compileDigest_prefix (D : C.Coalition) (row : Row C) :
    LogPrefix (compileDigest D row) := by
  rcases row with ⟨b | salt, history⟩
  · exact (LogPrefix.lift _).bind _ _ fun output =>
      (emit_prefix _).bind _ _ fun _ => LogPrefix.pure output
  · exact LogPrefix.simulateQ _ _ (publicQuery_prefix D)

theorem boundaryCompiler_prefix (D : C.Coalition) (t : (BoundarySpec D).Domain) :
    LogPrefix (boundaryCompiler D t) := by
  rcases t with ⟨ctx, st⟩ | t
  · apply LogPrefix.bind
    · exact LogPrefix.mapM _ _ (prepareTerm_prefix D ctx st.label)
    · intro terms
      apply LogPrefix.bind _ _ (preparePairs_prefix D ctx st.label)
      intro _
      apply LogPrefix.mapM
      intro T
      split_ifs
      · exact compileDigest_prefix D _
      · exact LogPrefix.pure _
  · exact publicQuery_prefix D t.1

variable {E : Type} [Field E] [Algebra Bit E]

/-- An initial transcript changes only the returned symbolic log. -/
theorem ceremonyProgramFrom_map (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (log : TreeSimLog C) :
    ceremonyProgramFrom K circuits settings top tree D A x z Z log =
      (fun r => (r.1, r.2.1, log.map LogPiece.literal ++ r.2.2)) <$>
        ceremonyProgram K circuits settings top tree D A x z Z := by
  simpa only [ceremonyProgramFrom, ceremonyProgram, List.append_nil] using
    LogPrefix.simulateQ (boundaryCompiler D) (ceremonyBoundary K circuits settings top tree D A x z Z)
      (boundaryCompiler_prefix D) (log.map LogPiece.literal) (∅, [])

/-- Every syntactic query budget is invariant under retaining the counted prefix log. -/
theorem ceremonyProgramFrom_bound_iff (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (log : TreeSimLog C)
    (P : (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C).Domain → Prop)
    [DecidablePred P] (n : ℕ) :
    IsQueryBoundP (ceremonyProgramFrom K circuits settings top tree D A x z Z log) P n ↔
      IsQueryBoundP (ceremonyProgram K circuits settings top tree D A x z Z) P n := by
  rw [ceremonyProgramFrom_map, isQueryBoundP_map_iff]

end ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof

namespace ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof
open TreeRawSaltFlowProof TreeRawSaltRepresentationProof TreeRawSaltNormalizeProof
open TreeRawSaltCertificatesProof LifetimeSaltFrom
attribute [local instance] Classical.propDecidable
variable {C : Committee}

/-- An arbitrary counted local prefix creates no free entry. -/
theorem prefix_no_free (prims : Primitives) (D : C.Coalition) {α : Type}
    (pre : OracleComp (LocalSpec C) α) (s : α × TreeSimState C)
    (hs : s ∈ support (prefixState prims D pre)) :
    ∀ (t : (LocalSpec C).Domain) (v : (LocalSpec C).Range t),
      (⟨.inr t, v⟩ : (u : (WorldSpec C).Domain) × (WorldSpec C).Range u) ∉ s.2.2 := by
  apply logged_adversary_inv prims D
    (fun state => ∀ t v, (⟨.inr t, v⟩ : (u : (WorldSpec C).Domain) × (WorldSpec C).Range u) ∉ state.2)
    ?_ pre ((∅, ∅), []) (by simp) s hs
  intro t state hstate r hr u v hv
  rw [logged_step_log prims D _ state r hr, List.mem_append, List.mem_singleton] at hv
  rcases hv with old | last
  · exact hstate u v old
  · cases last

/-- Literal counted digest entries are covered by the initial public guess list. -/
theorem prefix_recorded (log : TreeSimLog C) :
    Recorded (∅, log.map LogPiece.literal) ([], logDigestSalts log) := by
  intro salt history output hm
  obtain ⟨entry, he, eq⟩ := List.mem_map.mp hm
  have eq := LogPiece.literal.inj eq
  subst entry
  exact List.mem_filterMap.mpr ⟨_, he, rfl⟩

/-- A retained counted prefix has no literal hidden salt request. -/
theorem prefix_safe (prims : Primitives) (D : C.Coalition) {α : Type}
    (pre : OracleComp (LocalSpec C) α) (s : α × TreeSimState C)
    (hs : s ∈ support (prefixState prims D pre)) :
    SafeLiterals D (∅, s.2.2.map LogPiece.literal) ([], logDigestSalts s.2.2) := by
  intro entry hm
  obtain ⟨e, he, eq⟩ := List.mem_map.mp hm
  have eq := LogPiece.literal.inj eq
  subst e
  rcases entry with ⟨t, value⟩
  cases t with
  | inl t => trivial
  | inr t => exact False.elim (prefix_no_free prims D pre s hs t value he)

variable {E : Type} [Field E] [Algebra Bit E]

/-- Counted salts in the full decoded transcript, including its prefix, stay in the public list. -/
theorem ceremonyFrom_counted_recorded (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput)
    (cache : HashCache C) (log : TreeSimLog C)
    (r) (hr : r ∈ support (tableRun prims
      (ceremonyProgramFrom K circuits settings top tree D A x z Z log)
      ([], logDigestSalts log) cache ∅))
    (salt : List Bit) (history : HashOutput) (output : HashOutput)
    (hm : (⟨.inl (.inl (.inr (.inl (.digest salt history)))), output⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ (ceremonyDecode r).2.2) :
    salt ∈ r.1.2.2 := by
  have h := Preserves.simulateQ prims (boundaryCompiler D)
    (ceremonyBoundary K circuits settings top tree D A x z Z)
    (preserves_boundaryCompiler prims D) (∅, log.map .literal)
    ([], logDigestSalts log) cache ∅ (prefix_recorded log) r hr
  exact h salt history output (counted_mem_decode _ _ _ salt history output hm)

/-- Hidden salts are recorded in the private list of that same retained-prefix execution. -/
theorem ceremonyFrom_hidden_recorded (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput)
    {α : Type} (pre : OracleComp (LocalSpec C) α) (s : α × TreeSimState C)
    (hs : s ∈ support (prefixState prims D pre))
    (r) (hr : r ∈ support (tableRun prims
      (ceremonyProgramFrom K circuits settings top tree D A x z Z s.2.2)
      ([], logDigestSalts s.2.2) s.2.1.1 ∅))
    (salt : List Bit) (hidden : TreeSimHiddenSalt D (ceremonyDecode r).2.2 salt) :
    salt ∈ r.1.2.1 := by
  have safe := Preserves.simulateQ prims (boundaryCompiler D)
    (ceremonyBoundary K circuits settings top tree D A x z Z)
    (safe_boundaryCompiler prims D) (∅, s.2.2.map .literal)
    ([], logDigestSalts s.2.2) s.2.1.1 ∅ (prefix_safe prims D pre s hs) r hr
  have ready := TreeRawSaltStepsProof.compiler_program_ready prims D
    (ceremonyBoundary K circuits settings top tree D A x z Z)
    (ceremonyBoundary_safe K circuits settings top tree D A x z Z)
    ([], logDigestSalts s.2.2) s.2.1.1 ∅ (∅, s.2.2.map .literal)
    (literal_ready s.2.1.1 s.2.2) r hr
  obtain ⟨b, values, hv, rfl⟩ := hiddenSalt_cached D r.1.1.2 r.1.2 r.2.1 r.2.2 safe ready salt hidden
  exact tableRun_private_recorded prims _ ([], logDigestSalts s.2.2) s.2.1.1 ∅
    (by intro b values h; cases h) r hr b values hv

/-- Salt guessing after an actual counted prefix is the same-run table intersection event. -/
theorem ceremonyFrom_saltGuess_hit (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput)
    {α : Type} (pre : OracleComp (LocalSpec C) α) (s : α × TreeSimState C)
    (hs : s ∈ support (prefixState prims D pre))
    (r) (hr : r ∈ support (tableRun prims
      (ceremonyProgramFrom K circuits settings top tree D A x z Z s.2.2)
      ([], logDigestSalts s.2.2) s.2.1.1 ∅))
    (guess : TreeSimSaltGuess D (ceremonyDecode r).2.2) : AddressHit r := by
  obtain ⟨salt, history, output, hidden, counted⟩ := guess
  exact ⟨salt, ceremonyFrom_hidden_recorded prims K circuits settings top tree D A x z Z pre s hs r hr salt hidden,
    ceremonyFrom_counted_recorded prims K circuits settings top tree D A x z Z s.2.1.1 s.2.2
      r hr salt history output counted⟩

/-- Original global compiler budgets suffice after every retained counted prefix. -/
theorem ceremonyCompilerCertificatesFrom_of_budgets (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (budgets : CeremonyCompilerBudgets K circuits settings) :
    CeremonyCompilerCertificatesFrom prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall α pre s hs
  obtain ⟨hprivate, charged⟩ := budgets hb top tree D A x z Z q hx hq hsmall
  refine ⟨(ceremonyProgramFrom_bound_iff K circuits settings top tree D A x z Z s.2.2 _ _).mpr hprivate,
    (ceremonyProgramFrom_bound_iff K circuits settings top tree D A x z Z s.2.2 _ _).mpr charged, ?_⟩
  intro r hr _ guess
  exact ceremonyFrom_saltGuess_hit prims K circuits settings top tree D A x z Z pre s hs r hr guess

/-- The reached-prefix and empty-prefix certificates are equivalent for this fixed compiler. -/
theorem ceremonyCompilerCertificatesFrom_iff (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) :
    CeremonyCompilerCertificatesFrom prims K circuits settings ↔
      CeremonyCompilerCertificates prims K circuits settings := by
  constructor
  · exact certificates_of_from prims K circuits settings
  · intro certificates
    apply ceremonyCompilerCertificatesFrom_of_budgets prims K circuits settings
    intro hb top tree D A x z Z q hx hq hs
    exact (certificates hb top tree D A x z Z q hx hq hs).imp_right And.left

/-- The fixed compiler supplies its certificates after every retained counted prefix. -/
theorem ceremonyCompilerCertificatesFrom (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) :
    CeremonyCompilerCertificatesFrom prims K circuits settings :=
  ceremonyCompilerCertificatesFrom_of_budgets prims K circuits settings
    (ceremonyCompilerBudgets K circuits settings)

end ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.boundaryCompiler_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.boundaryCompiler_prefix

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.ceremonyProgramFrom_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.ceremonyProgramFrom_map

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.ceremonyProgramFrom_bound_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.ceremonyProgramFrom_bound_iff

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.ceremonyFrom_saltGuess_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.ceremonyFrom_saltGuess_hit

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.ceremonyCompilerCertificatesFrom_of_budgets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.ceremonyCompilerCertificatesFrom_of_budgets

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.ceremonyCompilerCertificatesFrom_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.ceremonyCompilerCertificatesFrom_iff

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.ceremonyCompilerCertificatesFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.TreeRawSaltCertificatesFromProof.ceremonyCompilerCertificatesFrom
