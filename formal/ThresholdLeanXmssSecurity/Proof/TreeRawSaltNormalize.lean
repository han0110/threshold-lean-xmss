import ThresholdLeanXmssSecurity.Proof.TreeRawSaltRepresentation

/-!
# Mixed opaque salt rows

A digest pass can contain hidden block handles and known salts together.
Delaying the hidden block draws until their digest calls preserves the joint
public and private caches. Known salts remain literal inputs, and repeated
handles retain their original lazy-cache sharing.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section
namespace ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof

open TreeRawSaltCeremonyProof TreeRawSaltRepresentationProof
attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-- A hidden address or an already evaluated known-stream salt. -/
abbrev Salt (C : Committee) := TreeSimHashSaltBlock C ⊕ List Bit

abbrev Row (C : Committee) := Salt C × List Bit

def sampleSalt : Salt C → StateT (BlockCache C) ProbComp (List Bit)
  | .inl b => List.ofFn <$> (TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle b
  | .inr salt => pure salt

def samples (rows : List (Row C)) : StateT (BlockCache C) ProbComp (List (List Bit × List Bit)) :=
  rows.mapM fun row => (fun salt => (salt, row.2)) <$> sampleSalt row.1

/-- One opaque hidden digest or one ordinary digest with a known salt. -/
def mixedDigest (prims : Primitives) (row : Row C) :
    StateT (HashCache C × BlockCache C) ProbComp HashOutput :=
  StateT.mk fun s => do
    let salt ← (sampleSalt row.1).run s.2
    (fun r => (r.1, r.2, salt.2)) <$> (saltedDigestAnswer prims salt.1 row.2).run s.1

def mixedRows (prims : Primitives) (rows : List (Row C)) :
    StateT (HashCache C × BlockCache C) ProbComp (List HashOutput) :=
  rows.mapM (mixedDigest prims)

/-- Local deferred sampling applies to any interleaving of hidden and known
rows. The assertion concerns the complete joint cache distribution. -/
theorem mixedRows_eager (prims : Primitives) (rows : List (Row C))
    (cache : HashCache C) (blocks : BlockCache C) :
    𝒟[(mixedRows prims rows).run (cache, blocks)] =
      𝒟[(do
        let salts ← (samples rows).run blocks
        let result ← (hashRows prims salts.1).run cache
        pure (result.1, result.2, salts.2))] := by
  induction rows generalizing cache blocks with
  | nil => simp [mixedRows, samples, hashRows]
  | cons row rows ih =>
    simp only [mixedRows, samples, List.mapM_cons, StateT.run_bind,
      StateT.run_pure, mixedDigest, StateT.run_mk,
      bind_assoc, bind_map_left, pure_bind]
    apply evalDist_bind_congr'
    intro salt
    simp only [evalDist_bind]
    have tail (r : HashOutput × HashCache C) :
        𝒟[(do
          let rest ← (mixedRows prims rows).run (r.2, salt.2)
          pure (r.1 :: rest.1, rest.2))] =
        𝒟[(do
          let salts ← (samples rows).run salt.2
          let rest ← (hashRows prims salts.1).run r.2
          pure (r.1 :: rest.1, rest.2, salts.2))] := by
      rw [evalDist_bind, ih]
      simp only [← evalDist_bind, bind_assoc, pure_bind]
    simp only [← evalDist_bind]
    calc
      _ = 𝒟[(do
        let r ← (saltedDigestAnswer prims salt.1 row.2).run cache
        let salts ← (samples rows).run salt.2
        let rest ← (hashRows prims salts.1).run r.2
        pure (r.1 :: rest.1, rest.2, salts.2))] := by
          apply evalDist_bind_congr'
          intro r
          exact tail r
      _ = _ := by
        rw [evalDist_bind_bind_swap]
        simp only [hashRows, List.mapM_cons, StateT.run_bind, StateT.run_pure,
          bind_assoc, pure_bind]
        rfl

/-- A mixed row is an opaque private call or two ordinary hash calls.
Only its digest is returned to the enclosing program. -/
def rowProgram (row : Row C) :
    OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) HashOutput :=
  match row.1 with
  | .inl b => OracleComp.lift (OracleSpec.query (spec := TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) (.inl (b, row.2)))
  | .inr salt => do
    let h ← OracleComp.lift (OracleSpec.query (spec := TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) (.inr (.inr (.inl (.history row.2)))))
    OracleComp.lift (OracleSpec.query (spec := TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) (.inr (.inr (.inl (.digest salt h)))))

def program (rows : List (Row C)) :
    OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) (List HashOutput) :=
  rows.mapM rowProgram

set_option backward.isDefEq.respectTransparency false in
theorem rowProgram_run (prims : Primitives) (row : Row C) :
    simulateQ (opaqueAnswer prims) (rowProgram row) = mixedDigest prims row := by
  rcases row with ⟨b | salt, history⟩
  · apply StateT.ext
    intro s
    rcases s with ⟨cache, blocks⟩
    simp only [rowProgram, simulateQ_spec_query, opaqueAnswer, opaqueDigest_run,
      mixedDigest, StateT.run_mk, sampleSalt, StateT.run_map, bind_map_left]
  · apply StateT.ext
    intro s
    rcases s with ⟨cache, blocks⟩
    simp only [rowProgram, simulateQ_bind, simulateQ_spec_query, opaqueAnswer,
      treeSimHashBlockCacheAnswer, StateT.run_mk, StateT.run_bind,
      mixedDigest, sampleSalt, StateT.run_pure, pure_bind,
      saltedDigestAnswer, map_bind, bind_map_left]
    rfl

theorem program_run (prims : Primitives) (rows : List (Row C)) :
    simulateQ (opaqueAnswer prims) (program rows) = mixedRows prims rows := by
  simp only [program, simulateQ_list_mapM, rowProgram_run, mixedRows]

/-- The existing lazy reader runs the very same concrete mixed program. -/
theorem program_eager (prims : Primitives) (rows : List (Row C)) (used : SaltLists)
    (cache : HashCache C) (blocks : BlockCache C) :
    𝒟[(fun r => (r.1.1, r.2)) <$> tableRun prims (program rows) used cache blocks] =
      𝒟[(do
        let salts ← (samples rows).run blocks
        let result ← (hashRows prims salts.1).run cache
        pure (result.1, result.2, salts.2))] := by
  rw [tableRun, read_program_erase, program_run]
  exact mixedRows_eager prims rows cache blocks

set_option backward.isDefEq.respectTransparency false in
theorem rowProgram_private (row : Row C) :
    IsQueryBoundP (rowProgram row) TreeSimHashSaltPrivate 1 := by
  rcases row with ⟨b | salt, history⟩
  · simp [rowProgram, isQueryBoundP_query_iff, TreeSimHashSaltPrivate]
  · simp [rowProgram, isQueryBoundP_query_bind_iff, isQueryBoundP_query_iff,
      TreeSimHashSaltPrivate]

set_option backward.isDefEq.respectTransparency false in
theorem rowProgram_charged (row : Row C) :
    IsQueryBoundP (rowProgram row) treeSimHashSaltTableCharged 1 := by
  rcases row with ⟨b | salt, history⟩
  · simp [rowProgram, isQueryBoundP_query_iff, treeSimHashSaltTableCharged]
  · simp [rowProgram, isQueryBoundP_query_bind_iff, isQueryBoundP_query_iff,
      treeSimHashSaltTableCharged, DigestQuery, digestSaltProjection]

theorem program_private (rows : List (Row C)) :
    IsQueryBoundP (program rows) TreeSimHashSaltPrivate rows.length := by
  simpa only [program, Nat.mul_one] using
    queryBound_mapM TreeSimHashSaltPrivate rowProgram 1 rows (fun row _ => rowProgram_private row)

theorem program_charged (rows : List (Row C)) :
    IsQueryBoundP (program rows) treeSimHashSaltTableCharged rows.length := by
  simpa only [program, Nat.mul_one] using
    queryBound_mapM treeSimHashSaltTableCharged rowProgram 1 rows (fun row _ => rowProgram_charged row)

/-- The compiler records private salt entries symbolically. They are
expanded only by the final decoder, never by the caller. -/
inductive LogPiece (C : Committee) where
  | literal (entry : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t)
  | draw (block : TreeSimHashSaltBlock C)
  | digest (block : TreeSimHashSaltBlock C) (history : List Bit) (output : HashOutput)

def LogPiece.decode (cache : HashCache C) (blocks : BlockCache C) : LogPiece C → TreeSimLog C
  | .literal entry => [entry]
  | .draw b => treeSimHiddenLog (treeSimHashSaltAddress b) (blockValues blocks b)
  | .digest b history output => digestLog (List.ofFn (blockValues blocks b)) history output cache

abbrev CompilerState (C : Committee) := HiddenCache C × List (LogPiece C)
abbrev CompilerM (C : Committee) :=
  StateT (CompilerState C) (OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C))

def emit (piece : LogPiece C) : CompilerM C Unit :=
  modify fun s => (s.1, s.2 ++ [piece])

def localQuery (t : (LocalSpec C).Domain) : CompilerM C ((LocalSpec C).Range t) :=
  StateT.lift (OracleComp.lift (OracleSpec.query
    (spec := TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) (.inr t)))

/-- Ordinary free hidden streams keep their own lazy table. The boundary
syntax forbids a hidden salt request at this ordinary entry point. -/
def publicAnswer (D : C.Coalition) : QueryImpl (WorldSpec C) (CompilerM C)
  | .inl (.inl u) => localQuery u
  | .inl (.inr _) => pure false
  | .inr (.inr (.inr x)) =>
    if Hidden D x.1 then do
      let state ← get
      let r ← StateT.lift (liftComp
        (((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle
          ((x.1, x.2.1), x.2.2)).run state.1)
        (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C))
      set (r.2, state.2)
      pure r.1
    else localQuery (.inr (.inr x))
  | .inr u => localQuery u

def publicQuery (D : C.Coalition) : QueryImpl (WorldSpec C) (CompilerM C) := fun t => do
  let answer ← publicAnswer D t
  emit (.literal ⟨t, answer⟩)
  pure answer

/-- Honest known streams and pair streams retain their real query order. -/
def publicDraw (D : C.Coalition) (name : KeyName C) (key : HashOutput) (label : ℕ) :
    CompilerM C (ℕ → Bit) :=
  simulateQ (publicQuery D) (free (liftComp (prgBits name key label 2 256) (LocalSpec C)))

def prepareTerm (D : C.Coalition) (ctx : Context C) (label : ℕ) (T : C.Term) :
    CompilerM C (Salt C) :=
  if ctx.self ∈ C.holders T then
    if KnownTo D.1 T then
      (fun bits => Sum.inr (vector 256 bits)) <$> publicDraw D (.term T) (ctx.prss.term T) label
    else do
      let b := (T, ctx.prss.term T, label)
      emit (.draw b)
      pure (.inl b)
  else pure (.inr [])

/-- The pair PRGs are executed even though the digest consumes only terms. -/
def preparePairs (D : C.Coalition) (ctx : Context C) (label : ℕ) : CompilerM C Unit := do
  let _ ← C.parties.mapM fun j =>
    if h : j = ctx.self then pure (fun _ : ℕ => (0 : Bit))
    else publicDraw D (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) label
  pure ()

def compileDigest (D : C.Coalition) (row : Row C) : CompilerM C HashOutput :=
  match row.1 with
  | .inl b => do
    let output ← StateT.lift (rowProgram row)
    emit (.digest b row.2 output)
    pure output
  | .inr salt =>
    simulateQ (publicQuery D) (free (liftComp (oneDigestQuery (C := C) salt row.2) (LocalSpec C)))

/-- A fixed mixed interpreter for the actual complete digest boundary. -/
def compileBoundaryDigest (D : C.Coalition) (ctx : Context C) (st : RunState C) :
    CompilerM C (List HashOutput) := do
  let terms ← C.terms.mapM (prepareTerm D ctx st.label)
  preparePairs D ctx st.label
  C.terms.mapM fun T => if ctx.self ∈ C.holders T then
    compileDigest D (terms.getD (C.terms.idxOf T) (.inr []), st.history T)
    else pure 0

def boundaryCompiler (D : C.Coalition) :
    QueryImpl (TreeRawSaltFlowProof.BoundarySpec D) (CompilerM C) :=
  fun t => match t with
  | .inl (ctx, st) => compileBoundaryDigest D ctx st
  | .inr u => publicQuery D u.1

variable {E : Type} [Field E] [Algebra Bit E]

/-- The opaque source is fixed by the actual ceremony boundary program. -/
def ceremonyProgram (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) (Bool × CompilerState C) :=
  (simulateQ (boundaryCompiler D)
    (ceremonyBoundary K circuits settings top tree D A x z Z)).run (∅, [])

/-- Both caches and the original-order writer log are reconstructed from
the complete opaque result. No private salt is exposed during execution. -/
def decodeResult {α : Type} (r : TableOutcome (C := C) (TreeSimHashSaltBlock C) (α × CompilerState C)) :
    α × TreeSimState C :=
  (r.1.1.1, (r.2.1, TreeRawSaltFlowProof.restore r.2.2 r.1.1.2.1),
    r.1.1.2.2.flatMap (LogPiece.decode r.2.1 r.2.2))


def ceremonyDecode := @decodeResult C Bool

set_option backward.isDefEq.respectTransparency false in
theorem block_read_update (b : TreeSimHashSaltBlock C) (blocks : BlockCache C)
    (r : (Fin 256 → Bit) × BlockCache C)
    (hr : r ∈ support (((TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle b).run blocks)) :
    r.2 = blocks.cacheQuery b r.1 := by
  cases h : blocks b with
  | none =>
    rw [QueryImpl.withCaching_run_none _ h, support_map] at hr
    obtain ⟨values, _, rfl⟩ := hr
    rfl
  | some values =>
    rw [QueryImpl.withCaching_run_some _ h, mem_support_pure_iff] at hr
    subst r
    change blocks = blocks.cacheQuery b values
    symm
    funext a
    by_cases ha : a = b
    · subst a
      rw [QueryCache.cacheQuery_self, h]
    · exact QueryCache.cacheQuery_of_ne _ _ ha

set_option backward.isDefEq.respectTransparency false in
/-- The symbolic private fragment has the exact full real state and log,
including an already cached block. -/
theorem compileDigest_private_joint (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (hidden : ¬KnownTo D.1 b.1) (history : List Bit)
    (cache : HashCache C) (other : HiddenCache C) (blocks : BlockCache C) (used : SaltLists) :
    𝒟[(simulateQ (treeSimLoggedWorld prims D) (saltDigest b history)).run
      ((cache, TreeRawSaltFlowProof.restore blocks other), [])] =
    𝒟[decodeResult <$> tableRun prims
      ((do emit (.draw b); compileDigest D (.inl b, history)).run (other, [])) used cache blocks] := by
  rw [saltDigest_joint prims D b hidden history cache _ []
    (TreeRawSaltFlowProof.restore_complete blocks other), TreeRawSaltFlowProof.restore_lookup]
  simp only [compileDigest, emit, StateT.run_bind, StateT.run_modify,
    pure_bind, StateT.run_lift, StateT.run_pure, List.nil_append]
  change _ = 𝒟[decodeResult <$> tableRun prims
    ((fun output => (output, other, [LogPiece.draw b, LogPiece.digest b history output])) <$>
      rowProgram (.inl b, history)) used cache blocks]
  have mapLaw {α β : Type} (f : α → β)
      (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α) :
      tableRun prims (f <$> p) used cache blocks =
        (fun r => ((f r.1.1, r.1.2), r.2)) <$> tableRun prims p used cache blocks := by
    simp only [tableRun, simulateQ_map, StateT.run_map]
  rw [mapLaw]
  simp only [rowProgram]
  erw [tableRun_private prims b history used cache blocks]
  simp only [opaqueDigest_run, map_bind, Functor.map_map]
  apply evalDist_bind_congr
  intro salt hsalt
  have cached := DeterministicSigning.query_caches b blocks salt hsalt
  have update := block_read_update b blocks salt hsalt
  apply congrArg evalDist
  apply map_congr
  intro result
  dsimp only [decodeResult, saltDigestDecode, Function.comp_def, LogPiece.decode,
    List.flatMap_cons, List.flatMap_nil, blockValues]
  simp only [List.nil_append, cached, Option.getD_some,
    ← TreeRawSaltFlowProof.restore_cache_block, ← update]
  simp only [List.flatMap_cons, LogPiece.decode, List.flatMap_nil, List.append_nil,
    blockValues, cached, Option.getD_some]

/-- Every symbolic reference in an emitted prefix already has its cache
value; literal public entries require no private reference. -/
def LogPiece.Ready (cache : HashCache C) (blocks : BlockCache C) : LogPiece C → Prop
  | .literal _ => True
  | .draw b => ∃ values, blocks b = some values
  | .digest b history _ => (∃ values, blocks b = some values) ∧ ∃ h, cache (.history history) = some h

def Ready (cache : HashCache C) (blocks : BlockCache C) (state : CompilerState C) : Prop :=
  ∀ piece ∈ state.2, piece.Ready cache blocks

def decodeCompiler (cache : HashCache C) (blocks : BlockCache C) (state : CompilerState C) :
    TreeSimState C :=
  ((cache, TreeRawSaltFlowProof.restore blocks state.1),
    state.2.flatMap (LogPiece.decode cache blocks))

theorem LogPiece.decode_mono (piece : LogPiece C) {cache cache' : HashCache C}
    {blocks blocks' : BlockCache C} (hc : cache ≤ cache') (hb : blocks ≤ blocks')
    (ready : piece.Ready cache blocks) : piece.decode cache blocks = piece.decode cache' blocks' := by
  cases piece with
  | literal entry => rfl
  | draw b =>
    obtain ⟨values, h⟩ := ready
    simp only [LogPiece.decode, blockValues, h, hb h]
  | digest b history output =>
    obtain ⟨⟨values, hv⟩, h, hh⟩ := ready
    simp only [LogPiece.decode, blockValues, hv, hb hv]
    exact digestLog_mono _ _ _ hc h hh

theorem Ready.log_mono {cache cache' : HashCache C} {blocks blocks' : BlockCache C}
    (state : CompilerState C) (hc : cache ≤ cache') (hb : blocks ≤ blocks')
    (ready : Ready cache blocks state) :
    state.2.flatMap (LogPiece.decode cache blocks) = state.2.flatMap (LogPiece.decode cache' blocks') := by
  apply List.flatMap_congr
  intro piece hp
  exact piece.decode_mono hc hb (ready piece hp)

/-- Single complete boundary operations, including their invariant for the
next operation. Both clauses refer to the same fixed compiler execution. -/
def BoundaryCompilerSteps (prims : Primitives) (D : C.Coalition) : Prop :=
  ∀ (t : (TreeRawSaltFlowProof.BoundarySpec D).Domain),
    ¬ BoundaryProgramCall D t → ∀ (used : SaltLists) (cache : HashCache C)
      (blocks : BlockCache C) (state : CompilerState C), Ready cache blocks state →
    𝒟[(simulateQ (treeSimLoggedWorld prims D)
      (TreeRawSaltFlowProof.boundarySource (E := E) D t)).run (decodeCompiler cache blocks state)] =
      𝒟[decodeResult <$> tableRun prims ((boundaryCompiler D t).run state) used cache blocks] ∧
    ∀ r ∈ support (tableRun prims ((boundaryCompiler D t).run state) used cache blocks),
      Ready r.2.1 r.2.2 r.1.1.2

omit [Field E] [Algebra Bit E] in
/-- The boundary step law composes through the actual adaptive source code,
with the same auxiliary state and both caches passed to each continuation. -/
theorem compiler_program_law (prims : Primitives) (D : C.Coalition)
    (steps : BoundaryCompilerSteps (E := E) prims D) {α : Type}
    (p : OracleComp (TreeRawSaltFlowProof.BoundarySpec D) α)
    (safe : IsQueryBoundP p (BoundaryProgramCall D) 0)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (state : CompilerState C) (ready : Ready cache blocks state) :
    𝒟[(simulateQ (treeSimLoggedWorld prims D)
      (simulateQ (TreeRawSaltFlowProof.boundarySource (E := E) D) p)).run
        (decodeCompiler cache blocks state)] =
      𝒟[decodeResult <$> tableRun prims ((simulateQ (boundaryCompiler D) p).run state) used cache blocks] := by
  induction p using OracleComp.inductionOn generalizing used cache blocks state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, tableRun,
      map_pure, decodeResult, decodeCompiler]
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at safe
    have ht : ¬ BoundaryProgramCall D t := by simpa using safe.1
    have step := steps t ht used cache blocks state ready
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tableRun_bind,
      map_bind]
    rw [evalDist_bind, step.1]
    simp only [← evalDist_bind, bind_map_left]
    apply evalDist_bind_congr
    intro r hr
    simpa only [decodeResult, decodeCompiler] using
      ih r.1.1.1 (by simpa only [ht, if_false, Nat.sub_zero] using safe.2 r.1.1.1)
        r.1.2 r.2.1 r.2.2 r.1.1.2 (step.2 r hr)

/-- Global counts and event transport for the one fixed compiler. The
source, decoder and intermediate state are already selected definitions. -/
def CeremonyCompilerCertificates (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    let H := treeBatches settings tree * (C.t * termCount C)
    let p := ceremonyProgram K circuits settings top tree D A x z Z
    IsQueryBoundP p TreeSimHashSaltPrivate H ∧
    IsQueryBoundP p treeSimHashSaltTableCharged (q + H) ∧
    ∀ r ∈ support (tableRun prims p ([], []) ∅ ∅),
      ¬ TreeSimHashCollision (ceremonyDecode r).2.2 →
      TreeSimSaltGuess D (ceremonyDecode r).2.2 → AddressHit r

/-- The original whole-ceremony opaque normalization follows from local
boundary simulation and the fixed compiler's global certificates. -/
theorem ceremonyOpaqueNormalization_of_compiler (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (steps : ∀ D : C.Coalition, BoundaryCompilerSteps (E := E) prims D)
    (certificates : CeremonyCompilerCertificates prims K circuits settings) :
    CeremonyOpaqueNormalization prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  obtain ⟨privateBound, charged, event⟩ := certificates hb top tree D A x z Z q hx hq hsmall
  refine ⟨Bool × CompilerState C, ceremonyProgram K circuits settings top tree D A x z Z,
    ceremonyDecode, privateBound, charged, ?_, event⟩
  have law := compiler_program_law prims D (steps D)
    (ceremonyBoundary K circuits settings top tree D A x z Z)
    (ceremonyBoundary_safe K circuits settings top tree D A x z Z)
    ([], []) ∅ ∅ (∅, []) (by simp [Ready])
  have empty : decodeCompiler (∅ : HashCache C) ∅ (∅, []) = ((∅, ∅), []) := by
    change ((∅, TreeRawSaltFlowProof.restore ∅ ∅), []) = ((∅, ∅), [])
    congr 2
    funext a
    cases h : TreeRawSaltFlowProof.saltAt a <;> simp [TreeRawSaltFlowProof.restore, h]
  rw [empty, ceremonyBoundary_source] at law
  exact (ceremonyBoundary_run prims K circuits settings top tree D A x z Z).symm.trans law

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.mixedRows_eager' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixedRows_eager

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.rowProgram_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rowProgram_run

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.program_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms program_run

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.program_eager' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms program_eager

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.rowProgram_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rowProgram_private

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.rowProgram_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rowProgram_charged

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.program_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms program_private

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.program_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms program_charged

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.block_read_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms block_read_update

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.compileDigest_private_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compileDigest_private_joint

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.LogPiece.decode_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LogPiece.decode_mono

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.Ready.log_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Ready.log_mono

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.compiler_program_law' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compiler_program_law

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof.ceremonyOpaqueNormalization_of_compiler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyOpaqueNormalization_of_compiler

end ThresholdLeanXmssSecurity.TreeRawSaltNormalizeProof
