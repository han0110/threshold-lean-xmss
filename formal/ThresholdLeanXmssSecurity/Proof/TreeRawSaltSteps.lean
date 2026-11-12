import ThresholdLeanXmssSecurity.Proof.TreeRawSaltNormalize
import VCVio.OracleComp.SimSemantics.StateT.StateSeparating
import Mathlib.Data.List.GetD

/-!
# Boundary steps for the opaque salt compiler

The fixed compiler retains the actual term draws, pair draws and digests in
their original transcript order. Silent lazy-block prefetch commutes with both
the source and compiler, including repeated handles. With those blocks cached,
the concrete term and digest loops have the same decoded joint law. Pending
draw references become ready in that same digest pass, and cache growth keeps
earlier decoded entries stable.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity.TreeRawSaltStepsProof

open TreeRawSaltCeremonyProof TreeRawSaltRepresentationProof TreeRawSaltNormalizeProof
attribute [local instance] Classical.propDecidable
variable {C : Committee}

set_option backward.isDefEq.respectTransparency false in
theorem opaque_lift_prob (prims : Primitives) {α : Type} (p : ProbComp α)
    (cache : HashCache C) (blocks : BlockCache C) :
    (simulateQ (opaqueAnswer prims)
      (liftComp p (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C))).run (cache, blocks) =
      (fun a => (a, cache, blocks)) <$> p := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro t s
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem publicAnswer_run (prims : Primitives) (D : C.Coalition)
    (t : (WorldSpec C).Domain) (safe : ¬ AimedProgramCall t)
    (cache : HashCache C) (blocks : BlockCache C) (state : CompilerState C) :
    (simulateQ (opaqueAnswer prims) ((publicAnswer D t).run state)).run (cache, blocks) =
      (fun r => ((r.1, r.2.2, state.2), r.2.1, blocks)) <$>
        (streamWorld prims D t).run (cache, state.1) := by
  rcases t with (u | p) | (u | q | x)
  · simp only [publicAnswer, localQuery, StateT.run_lift, bind_pure_comp, simulateQ_map,
      simulateQ_spec_query, opaqueAnswer, treeSimHashBlockCacheAnswer, StateT.run_mk,
      StateT.run_map, streamWorld, onHash, Functor.map_map]
    rfl
  · exact (safe trivial).elim
  · simp only [publicAnswer, localQuery, StateT.run_lift, bind_pure_comp, simulateQ_map,
      simulateQ_spec_query, opaqueAnswer, treeSimHashBlockCacheAnswer, StateT.run_mk,
      StateT.run_map, streamWorld, onHash, Functor.map_map]
    rfl
  · simp only [publicAnswer, localQuery, StateT.run_lift, bind_pure_comp, simulateQ_map,
      simulateQ_spec_query, opaqueAnswer, treeSimHashBlockCacheAnswer, StateT.run_mk,
      StateT.run_map, streamWorld, onHash, Functor.map_map]
    rfl
  · by_cases hidden : Hidden D x.1
    · simp only [publicAnswer, if_pos hidden, StateT.run_bind, StateT.run_get,
        pure_bind, StateT.run_lift, StateT.run_set,
        map_pure, bind_pure_comp, simulateQ_map, StateT.run_map,
        opaque_lift_prob, streamWorld, StateT.run_mk, Functor.map_map]
    · simp only [publicAnswer, if_neg hidden, localQuery, StateT.run_lift, bind_pure_comp,
        simulateQ_map, simulateQ_spec_query, opaqueAnswer, treeSimHashBlockCacheAnswer,
        StateT.run_mk, StateT.run_map, streamWorld, onHash, Functor.map_map]
      rfl

theorem publicQuery_run (prims : Primitives) (D : C.Coalition)
    (t : (WorldSpec C).Domain) (safe : ¬ AimedProgramCall t)
    (cache : HashCache C) (blocks : BlockCache C) (state : CompilerState C) :
    (simulateQ (opaqueAnswer prims) ((publicQuery D t).run state)).run (cache, blocks) =
      (fun r => ((r.1, r.2.2, state.2 ++ [.literal ⟨t, r.1⟩]), r.2.1, blocks)) <$>
        (streamWorld prims D t).run (cache, state.1) := by
  have run : (publicQuery D t).run state =
      (fun r => (r.1, r.2.1, r.2.2 ++ [LogPiece.literal ⟨t, r.1⟩])) <$>
        (publicAnswer D t).run state := by
    simp only [publicQuery, emit, StateT.run_bind, StateT.run_map, StateT.run_modify,
      map_pure, bind_pure_comp]
  rw [run, simulateQ_map, StateT.run_map, publicAnswer_run prims D t safe]
  simp only [Functor.map_map]

/-- Erasing the ghost salt lists does not change the concrete compiler
result, including its symbolic transcript and both random-oracle caches. -/
theorem publicQuery_erase (prims : Primitives) (D : C.Coalition)
    (t : (WorldSpec C).Domain) (safe : ¬ AimedProgramCall t)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (state : CompilerState C) :
    (fun r => (r.1.1, r.2)) <$>
        tableRun prims ((publicQuery D t).run state) used cache blocks =
      (fun r => ((r.1, r.2.2, state.2 ++ [.literal ⟨t, r.1⟩]), r.2.1, blocks)) <$>
        (streamWorld prims D t).run (cache, state.1) := by
  rw [tableRun, read_program_erase, publicQuery_run prims D t safe]

theorem ready_mono {cache cache' : HashCache C} {blocks blocks' : BlockCache C}
    {state : CompilerState C} (hc : cache ≤ cache') (hb : blocks ≤ blocks')
    (ready : Ready cache blocks state) : Ready cache' blocks' state := by
  intro piece hp
  have h := ready piece hp
  cases piece with
  | literal entry => trivial
  | draw b => obtain ⟨v, hv⟩ := h; exact ⟨v, hb hv⟩
  | digest b history output =>
    obtain ⟨⟨v, hv⟩, h, hh⟩ := h
    exact ⟨⟨v, hb hv⟩, h, hc hh⟩

/-- A public compiler call keeps every previously emitted reference valid. -/
theorem publicQuery_ready (prims : Primitives) (D : C.Coalition)
    (t : (WorldSpec C).Domain) (safe : ¬ AimedProgramCall t)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (state : CompilerState C) (ready : Ready cache blocks state)
    (r : TableOutcome (C := C) (TreeSimHashSaltBlock C) ((WorldSpec C).Range t × CompilerState C))
    (hr : r ∈ support (tableRun prims ((publicQuery D t).run state) used cache blocks)) :
    Ready r.2.1 r.2.2 r.1.1.2 := by
  have erased : (r.1.1, r.2) ∈ support ((fun r => (r.1.1, r.2)) <$>
      tableRun prims ((publicQuery D t).run state) used cache blocks) := by
    rw [support_map]; exact ⟨r, hr, rfl⟩
  rw [publicQuery_erase prims D t safe, support_map] at erased
  obtain ⟨out, hout, he⟩ := erased
  have grown := treeSim_streamWorld_grows prims D t (cache, state.1) out hout
  have old := ready_mono grown (le_refl blocks) ready
  have target : Ready out.2.1 blocks (out.2.2, state.2 ++ [.literal ⟨t, out.1⟩]) := by
    intro piece hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact old piece hp
    · trivial
  exact (congrArg (fun z => Ready z.2.1 z.2.2 z.1.2) he).mp target

/-- Every nonprogramming public boundary has the exact decoded joint law. -/
theorem publicQuery_joint (prims : Primitives) (D : C.Coalition)
    (t : (WorldSpec C).Domain) (safe : ¬ AimedProgramCall t)
    (noSalt : TreeRawSaltFlowProof.NoSaltRead D t)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (state : CompilerState C) (ready : Ready cache blocks state) :
    𝒟[(treeSimLoggedWorld prims D t).run (decodeCompiler cache blocks state)] =
      𝒟[decodeResult <$> tableRun prims ((publicQuery D t).run state) used cache blocks] := by
  have decode : decodeResult <$> tableRun prims ((publicQuery D t).run state) used cache blocks =
      (fun r => (r.1.1, decodeCompiler r.2.1 r.2.2 r.1.2)) <$>
        ((fun r => (r.1.1, r.2)) <$>
          tableRun prims ((publicQuery D t).run state) used cache blocks) := by
    rw [Functor.map_map]
    rfl
  rw [decode, publicQuery_erase prims D t safe]
  simp only [treeSimLoggedWorld, StateT.run_mk, decodeCompiler,
    TreeRawSaltFlowProof.stream_query_restore prims D t noSalt, Functor.map_map]
  simp only [map_eq_bind_pure_comp]
  apply evalDist_bind_congr
  intro out hout
  have grown := treeSim_streamWorld_grows prims D t (cache, state.1) out hout
  have stable := Ready.log_mono state grown (le_refl blocks) ready
  simp only [Function.comp_def, List.flatMap_append, List.flatMap_cons,
    LogPiece.decode, List.flatMap_nil, List.append_nil, stable]

/-- Safe public segments preserve the complete joint law and the validity
of the symbolic prefix. The continuation may adapt to every public answer. -/
theorem public_program_steps (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (WorldSpec C) α)
    (noProgram : IsQueryBoundP p AimedProgramCall 0)
    (noSalt : IsQueryBoundP p (fun t => ¬TreeRawSaltFlowProof.NoSaltRead D t) 0)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (state : CompilerState C) (ready : Ready cache blocks state) :
    𝒟[(simulateQ (treeSimLoggedWorld prims D) p).run (decodeCompiler cache blocks state)] =
      𝒟[decodeResult <$> tableRun prims ((simulateQ (publicQuery D) p).run state) used cache blocks] ∧
    ∀ r ∈ support (tableRun prims ((simulateQ (publicQuery D) p).run state) used cache blocks),
      Ready r.2.1 r.2.2 r.1.1.2 := by
  induction p using OracleComp.inductionOn generalizing used cache blocks state with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, tableRun, map_pure]
    constructor
    · rfl
    · intro r hr
      simp only [mem_support_pure_iff] at hr
      subst r
      exact ready
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at noProgram noSalt
    have ht : ¬ AimedProgramCall t := by simpa using noProgram.1
    have hs : TreeRawSaltFlowProof.NoSaltRead D t := by simpa using noSalt.1
    have next (r) (hr : r ∈ support (tableRun prims ((publicQuery D t).run state) used cache blocks)) :=
      ih r.1.1.1 (by simpa [ht] using noProgram.2 r.1.1.1)
        (by simpa [hs] using noSalt.2 r.1.1.1)
        r.1.2 r.2.1 r.2.2 r.1.1.2
        (publicQuery_ready prims D t ht used cache blocks state ready r hr)
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tableRun_bind, map_bind]
    constructor
    · rw [evalDist_bind, publicQuery_joint prims D t ht hs used cache blocks state ready]
      simp only [← evalDist_bind, bind_map_left]
      apply evalDist_bind_congr
      intro r hr
      exact (next r hr).1
    · intro r hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨mid, hmid, hr⟩ := hr
      exact (next mid hmid).2 r hr

set_option backward.isDefEq.respectTransparency false in
theorem compileDigest_private_run (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (history : List Bit)
    (cache : HashCache C) (blocks : BlockCache C) (state : CompilerState C) :
    (simulateQ (opaqueAnswer prims) ((compileDigest D (.inl b, history)).run state)).run (cache, blocks) =
      (fun r => ((r.1, state.1, state.2 ++ [.digest b history r.1]), r.2)) <$>
        (opaqueDigest prims b history).run (cache, blocks) := by
  simp only [compileDigest, StateT.run_bind, StateT.run_lift, StateT.run_map,
    emit, StateT.run_modify, map_pure, bind_pure_comp,
    TreeRawSaltNormalizeProof.rowProgram, simulateQ_map, simulateQ_spec_query,
    opaqueAnswer, StateT.run_map, Functor.map_map]

/-- A proof-only silent prefetch updates just the existing private block
cache. It does not emit a log entry or expose a salt to the compiler. -/
def blockRead (b : TreeSimHashSaltBlock C) :
    StateT (HashCache C × BlockCache C) ProbComp (Fin 256 → Bit) :=
  StateT.mk fun s => (fun r => (r.1, s.1, r.2)) <$>
    ((TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle b).run s.2

theorem blockRead_commutes (b a : TreeSimHashSaltBlock C) :
    Commutes (blockRead b) (blockRead a) := by
  intro s
  have h := evalDist_map_eq_of_evalDist_eq (commutes_randomOracle_randomOracle b a s.2)
    (fun r => (r.1, s.1, r.2))
  simpa only [blockRead, StateT.run_mk, StateT.run_bind, StateT.run_pure,
    map_bind, bind_map_left, map_pure] using h

theorem blockRead_commutes_public (prims : Primitives) (b : TreeSimHashSaltBlock C)
    (t : (LocalSpec C).Domain) :
    Commutes (blockRead b) (treeSimHashBlockCacheAnswer (localAnswer prims) (.inr t)) := by
  intro s
  simp only [blockRead, treeSimHashBlockCacheAnswer, StateT.run_mk,
    StateT.run_bind, StateT.run_pure, bind_map_left]
  rw [evalDist_bind_bind_swap]

/-- Silent block prefetch commutes even with an opaque digest at the same
handle: both reads use the same lazy cache entry. -/
theorem blockRead_commutes_opaque (prims : Primitives) (b : TreeSimHashSaltBlock C)
    (t : (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C).Domain) :
    Commutes (blockRead b) (opaqueAnswer prims t) := by
  cases t with
  | inl row =>
    change Commutes (blockRead b) (blockRead row.1 >>= fun salt =>
      treeSimHashBlockCacheAnswer (localAnswer prims) (.inr (.inr (.inl (.history row.2)))) >>= fun h =>
      treeSimHashBlockCacheAnswer (localAnswer prims) (.inr (.inr (.inl (.digest (List.ofFn salt) h)))))
    exact (blockRead_commutes b row.1).bind_right fun _ =>
      (blockRead_commutes_public prims b _).bind_right fun _ => blockRead_commutes_public prims b _
  | inr t => exact blockRead_commutes_public prims b t

/-- The actual opaque program may adapt to its answers. Its complete result
and the two caches commute with a silent block prefetch. -/
theorem blockRead_commutes_program (prims : Primitives) (b : TreeSimHashSaltBlock C)
    {α : Type} (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α) :
    Commutes (blockRead b) (simulateQ (opaqueAnswer prims) p) := by
  induction p using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure]; exact commutes_pure _ a
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query]
    exact (blockRead_commutes_opaque prims b t).bind_right ih

/-- A handle that the opaque program always reads can be prefetched without
changing its full result or either final cache. -/
theorem opaque_prefetch (prims : Primitives) (b : TreeSimHashSaltBlock C)
    {α : Type} (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (cache : HashCache C) (blocks : BlockCache C)
    (cached : ∀ r ∈ support ((simulateQ (opaqueAnswer prims) p).run (cache, blocks)),
      ∃ values, r.2.2 b = some values) :
    𝒟[(simulateQ (opaqueAnswer prims) p).run (cache, blocks)] =
      𝒟[(do let _ ← blockRead b; simulateQ (opaqueAnswer prims) p).run (cache, blocks)] := by
  have commute := (blockRead_commutes_program prims b p).bind
    (fun _ result => pure result) (cache, blocks)
  simp only [bind_pure] at commute
  rw [commute]
  simp only [StateT.run_bind, StateT.run_pure]
  conv_lhs => rw [← bind_pure ((simulateQ (opaqueAnswer prims) p).run (cache, blocks))]
  apply evalDist_bind_congr
  intro r hr
  obtain ⟨values, hv⟩ := cached r hr
  simp only [blockRead, StateT.run_mk, QueryImpl.withCaching_run_some _ hv,
    map_pure, pure_bind]

abbrev CompilerOutcome (C : Committee) (α : Type) :=
  (α × CompilerState C) × HashCache C × BlockCache C

def compilerRun (prims : Primitives) {α : Type} (p : CompilerM C α)
    (state : CompilerState C) (cache : HashCache C) (blocks : BlockCache C) :
    ProbComp (CompilerOutcome C α) :=
  (simulateQ (opaqueAnswer prims) (p.run state)).run (cache, blocks)

theorem compilerRun_bind (prims : Primitives) {α β : Type} (p : CompilerM C α)
    (k : α → CompilerM C β) (state : CompilerState C)
    (cache : HashCache C) (blocks : BlockCache C) :
    compilerRun prims (p >>= k) state cache blocks =
      (compilerRun prims p state cache blocks >>= fun r =>
        compilerRun prims (k r.1.1) r.1.2 r.2.1 r.2.2) := by
  simp only [compilerRun, StateT.run_bind, simulateQ_bind]

set_option backward.isDefEq.respectTransparency false in
theorem opaque_grows (prims : Primitives)
    {α : Type} (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (cache : HashCache C) (blocks : BlockCache C) (r : α × HashCache C × BlockCache C)
    (hr : r ∈ support ((simulateQ (opaqueAnswer prims) p).run (cache, blocks))) :
    cache ≤ r.2.1 ∧ blocks ≤ r.2.2 := by
  induction p using OracleComp.inductionOn generalizing cache blocks r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact ⟨le_rfl, le_rfl⟩
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    have next := ih mid.1 mid.2.1 mid.2.2 r hr
    have step : cache ≤ mid.2.1 ∧ blocks ≤ mid.2.2 := by
      cases t with
      | inl row =>
        have h := opaqueDigest_cached prims row.1 row.2 cache blocks mid hmid
        exact ⟨h.1, h.2.1⟩
      | inr t =>
        simp only [opaqueAnswer, treeSimHashBlockCacheAnswer, StateT.run_mk, support_map] at hmid
        obtain ⟨out, hout, rfl⟩ := hmid
        exact ⟨grows_localAnswer prims t cache out hout, le_rfl⟩
    exact ⟨step.1.trans next.1, step.2.trans next.2⟩

theorem compilerRun_mapM_rel (prims : Primitives) {ι α : Type}
    (xs : List ι) (f : ι → CompilerM C α) (R : ι → α → Prop)
    (each : ∀ i ∈ xs, ∀ state cache blocks r,
      r ∈ support (compilerRun prims (f i) state cache blocks) → R i r.1.1)
    (state : CompilerState C) (cache : HashCache C) (blocks : BlockCache C)
    (r : CompilerOutcome C (List α))
    (hr : r ∈ support (compilerRun prims (xs.mapM f) state cache blocks)) :
    List.Forall₂ R xs r.1.1 := by
  induction xs generalizing state cache blocks r with
  | nil =>
    simp only [List.mapM_nil, compilerRun, StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at hr
    subst r
    exact .nil
  | cons x xs ih =>
    simp only [List.mapM_cons, compilerRun_bind, mem_support_bind_iff] at hr
    obtain ⟨head, hhead, tail, htail, hr⟩ := hr
    simp only [compilerRun, StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at hr
    subst r
    exact .cons (each x (by simp) _ _ _ head hhead)
      (ih (fun i hi => each i (by simp [hi])) _ _ _ tail htail)

/-- The symbolic address of every hidden held term is fixed by the actual
context; known rows carry literal salts and unheld terms carry no draw. -/
def TermSalt (D : C.Coalition) (ctx : Context C) (label : ℕ)
    (T : C.Term) (salt : Salt C) : Prop :=
  if ctx.self ∈ C.holders T then
    if KnownTo D.1 T then ∃ bits, salt = .inr bits ∧ bits.length = 256
    else salt = .inl (T, ctx.prss.term T, label)
  else salt = .inr []

theorem prepareTerm_shape (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label : ℕ) (T : C.Term)
    (state : CompilerState C) (cache : HashCache C) (blocks : BlockCache C)
    (r : CompilerOutcome C (Salt C))
    (hr : r ∈ support (compilerRun prims (prepareTerm D ctx label T) state cache blocks)) :
    TermSalt D ctx label T r.1.1 := by
  by_cases held : ctx.self ∈ C.holders T
  · by_cases known : KnownTo D.1 T
    · simp only [compilerRun, prepareTerm, if_pos held, if_pos known,
        StateT.run_map, simulateQ_map, StateT.run_map, support_map] at hr
      obtain ⟨out, _, rfl⟩ := hr
      simp [TermSalt, held, known, vector]
    · simp only [compilerRun, prepareTerm, if_pos held, if_neg known, emit,
        StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        simulateQ_pure, mem_support_pure_iff] at hr
      subst r
      simp [TermSalt, held, known]
  · simp only [compilerRun, prepareTerm, if_neg held, StateT.run_pure,
      simulateQ_pure, mem_support_pure_iff] at hr
    subst r
    simp [TermSalt, held]

theorem prepareTerms_shape (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label : ℕ) (state : CompilerState C)
    (cache : HashCache C) (blocks : BlockCache C) (r : CompilerOutcome C (List (Salt C)))
    (hr : r ∈ support (compilerRun prims (C.terms.mapM (prepareTerm D ctx label)) state cache blocks)) :
    List.Forall₂ (TermSalt D ctx label) C.terms r.1.1 :=
  compilerRun_mapM_rel prims C.terms (prepareTerm D ctx label) (TermSalt D ctx label)
    (fun T _ => prepareTerm_shape prims D ctx label T) state cache blocks r hr

theorem termSalt_getD (D : C.Coalition) (ctx : Context C) (label : ℕ)
    (salts : List (Salt C)) (shape : List.Forall₂ (TermSalt D ctx label) C.terms salts)
    (T : C.Term) : TermSalt D ctx label T (salts.getD (C.terms.idxOf T) (.inr [])) := by
  have hi := List.idxOf_lt_length_of_mem (mem_terms T)
  have hj : C.terms.idxOf T < salts.length := shape.length_eq ▸ hi
  have h := shape.get hi hj
  simpa only [List.get_eq_getElem, List.getElem_idxOf hi,
    List.getD, List.getElem?_eq_getElem hj, Option.getD_some] using h

theorem compilerRun_mapM_caches (prims : Primitives) {ι α : Type}
    (xs : List ι) (f : ι → CompilerM C α) (i : ι) (hi : i ∈ xs)
    (b : TreeSimHashSaltBlock C)
    (each : ∀ state cache blocks r, r ∈ support (compilerRun prims (f i) state cache blocks) →
      ∃ values, r.2.2 b = some values)
    (state : CompilerState C) (cache : HashCache C) (blocks : BlockCache C)
    (r : CompilerOutcome C (List α))
    (hr : r ∈ support (compilerRun prims (xs.mapM f) state cache blocks)) :
    ∃ values, r.2.2 b = some values := by
  induction xs generalizing state cache blocks r with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [List.mapM_cons, compilerRun_bind, mem_support_bind_iff] at hr
    obtain ⟨head, hhead, tail, htail, hr⟩ := hr
    simp only [compilerRun, StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at hr
    subst r
    rcases List.mem_cons.mp hi with rfl | hi
    · obtain ⟨v, hv⟩ := each state cache blocks head hhead
      have grows := opaque_grows prims ((xs.mapM f).run head.1.2) head.2.1 head.2.2 tail htail
      exact ⟨v, grows.2 hv⟩
    · exact ih hi _ _ _ tail htail

theorem compileDigest_private_caches (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (history : List Bit)
    (state : CompilerState C) (cache : HashCache C) (blocks : BlockCache C)
    (r : CompilerOutcome C HashOutput)
    (hr : r ∈ support (compilerRun prims (compileDigest D (.inl b, history)) state cache blocks)) :
    ∃ values, r.2.2 b = some values := by
  rw [compilerRun, compileDigest_private_run, support_map] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  obtain ⟨_, _, values, _, hv, _⟩ := opaqueDigest_cached prims b history cache blocks out hout
  exact ⟨values, hv⟩

/-- Every held hidden term handle is actually queried by the final digest
pass, regardless of intervening known-term and pair-stream draws. -/
theorem compileBoundaryDigest_caches (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (st : RunState C) (T : C.Term)
    (held : ctx.self ∈ C.holders T) (hidden : ¬ KnownTo D.1 T)
    (state : CompilerState C) (cache : HashCache C) (blocks : BlockCache C)
    (r : CompilerOutcome C (List HashOutput))
    (hr : r ∈ support (compilerRun prims (compileBoundaryDigest D ctx st) state cache blocks)) :
    ∃ values, r.2.2 (T, ctx.prss.term T, st.label) = some values := by
  simp only [compileBoundaryDigest, compilerRun_bind, mem_support_bind_iff] at hr
  obtain ⟨terms, hterms, pairs, _, hr⟩ := hr
  have shape := prepareTerms_shape prims D ctx st.label state cache blocks terms hterms
  have row := termSalt_getD D ctx st.label terms.1.1 shape T
  simp only [TermSalt, if_pos held, if_neg hidden] at row
  apply compilerRun_mapM_caches prims C.terms _ T (mem_terms T)
    (T, ctx.prss.term T, st.label) _ _ _ _ r hr
  intro state' cache' blocks' out hout
  simp only [if_pos held, row] at hout
  exact compileDigest_private_caches prims D _ _ state' cache' blocks' out hout

/-- Pending draws are symbolic references that the fixed digest pass will
fill. All other symbolic entries already have their decoder inputs cached. -/
def Pending (allowed : TreeSimHashSaltBlock C → Prop)
    (cache : HashCache C) (blocks : BlockCache C) (state : CompilerState C) : Prop :=
  ∀ piece ∈ state.2, piece.Ready cache blocks ∨ ∃ b, piece = .draw b ∧ allowed b

theorem pending_mono (allowed : TreeSimHashSaltBlock C → Prop)
    {cache cache' : HashCache C} {blocks blocks' : BlockCache C} {state : CompilerState C}
    (hc : cache ≤ cache') (hb : blocks ≤ blocks')
    (pending : Pending allowed cache blocks state) : Pending allowed cache' blocks' state := by
  intro piece hp
  rcases pending piece hp with ready | deferred
  · left
    exact ready_mono hc hb (state := (state.1, [piece]))
      (by intro p hp; have he := List.mem_singleton.mp hp; subst p; exact ready) piece (by simp)
  · exact Or.inr deferred

def PreservesPending (prims : Primitives) (allowed : TreeSimHashSaltBlock C → Prop)
    {α : Type} (p : CompilerM C α) : Prop :=
  ∀ state cache blocks, Pending allowed cache blocks state →
    ∀ r ∈ support (compilerRun prims p state cache blocks), Pending allowed r.2.1 r.2.2 r.1.2

theorem pending_pure (prims : Primitives) (allowed : TreeSimHashSaltBlock C → Prop)
    {α : Type} (a : α) : PreservesPending prims allowed (pure a) := by
  intro state cache blocks h r hr
  simp only [compilerRun, StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at hr
  subst r
  exact h

theorem pending_bind (prims : Primitives) (allowed : TreeSimHashSaltBlock C → Prop)
    {α β : Type} {p : CompilerM C α} {k : α → CompilerM C β}
    (first : PreservesPending prims allowed p) (next : ∀ a, PreservesPending prims allowed (k a)) :
    PreservesPending prims allowed (p >>= k) := by
  intro state cache blocks h r hr
  rw [compilerRun_bind, mem_support_bind_iff] at hr
  obtain ⟨mid, hmid, hr⟩ := hr
  exact next mid.1.1 _ _ _ (first state cache blocks h mid hmid) r hr

theorem pending_mapM (prims : Primitives) (allowed : TreeSimHashSaltBlock C → Prop)
    {ι α : Type} (xs : List ι) (f : ι → CompilerM C α)
    (each : ∀ i ∈ xs, PreservesPending prims allowed (f i)) :
    PreservesPending prims allowed (xs.mapM f) := by
  induction xs with
  | nil => simpa only [List.mapM_nil] using pending_pure prims allowed ([] : List α)
  | cons x xs ih =>
    rw [List.mapM_cons]
    apply pending_bind prims allowed (each x (by simp))
    intro a
    apply pending_bind prims allowed (ih (fun i hi => each i (by simp [hi])))
    intro as
    exact pending_pure prims allowed (a :: as)

theorem publicQuery_pending (prims : Primitives) (D : C.Coalition)
    (allowed : TreeSimHashSaltBlock C → Prop) (t : (WorldSpec C).Domain)
    (safe : ¬ AimedProgramCall t) : PreservesPending prims allowed (publicQuery D t) := by
  intro state cache blocks pending r hr
  rw [compilerRun, publicQuery_run prims D t safe, support_map] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  have grown := treeSim_streamWorld_grows prims D t (cache, state.1) out hout
  have old := pending_mono allowed grown (le_refl blocks) pending
  intro piece hp
  simp only [List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact old piece hp
  · exact Or.inl trivial

theorem public_program_pending (prims : Primitives) (D : C.Coalition)
    (allowed : TreeSimHashSaltBlock C → Prop) {α : Type}
    (p : OracleComp (WorldSpec C) α) (safe : IsQueryBoundP p AimedProgramCall 0) :
    PreservesPending prims allowed (simulateQ (publicQuery D) p) := by
  induction p using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure]; exact pending_pure prims allowed a
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at safe
    have ht : ¬ AimedProgramCall t := by simpa using safe.1
    rw [simulateQ_bind, simulateQ_spec_query]
    exact pending_bind prims allowed (publicQuery_pending prims D allowed t ht)
      (fun a => ih a (by simpa [ht] using safe.2 a))

theorem compileDigest_pending (prims : Primitives) (D : C.Coalition)
    (allowed : TreeSimHashSaltBlock C → Prop) (row : Row C) :
    PreservesPending prims allowed (compileDigest D row) := by
  rcases row with ⟨b | salt, history⟩
  · intro state cache blocks pending r hr
    rw [compilerRun, compileDigest_private_run, support_map] at hr
    obtain ⟨out, hout, rfl⟩ := hr
    obtain ⟨hc, hb, values, h, hv, hh, _⟩ := opaqueDigest_cached prims b history cache blocks out hout
    have old := pending_mono allowed hc hb pending
    intro piece hp
    simp only [List.mem_append, List.mem_singleton] at hp
    rcases hp with hp | rfl
    · exact old piece hp
    · exact Or.inl ⟨⟨values, hv⟩, h, hh⟩
  · exact public_program_pending prims D allowed _ (aimed_noProgram_free _)

def HiddenTermBlock (D : C.Coalition) (ctx : Context C) (label : ℕ)
    (b : TreeSimHashSaltBlock C) : Prop :=
  ∃ T, ctx.self ∈ C.holders T ∧ ¬ KnownTo D.1 T ∧ b = (T, ctx.prss.term T, label)

theorem prepareTerm_pending (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label : ℕ) (T : C.Term) :
    PreservesPending prims (HiddenTermBlock D ctx label) (prepareTerm D ctx label T) := by
  by_cases held : ctx.self ∈ C.holders T
  · by_cases known : KnownTo D.1 T
    · simp only [prepareTerm, if_pos held, if_pos known, map_eq_bind_pure_comp]
      exact pending_bind prims _ (public_program_pending prims D _ _ (aimed_noProgram_free _))
        (fun _ => pending_pure prims _ _)
    · intro state cache blocks pending r hr
      simp only [compilerRun, prepareTerm, if_pos held, if_neg known, emit,
        StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        simulateQ_pure, mem_support_pure_iff] at hr
      subst r
      intro piece hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact pending piece hp
      · exact Or.inr ⟨_, rfl, T, held, known, rfl⟩
  · simp only [prepareTerm, if_neg held]
    exact pending_pure prims _ _

theorem preparePairs_pending (prims : Primitives) (D : C.Coalition)
    (allowed : TreeSimHashSaltBlock C → Prop) (ctx : Context C) (label : ℕ) :
    PreservesPending prims allowed (preparePairs D ctx label) := by
  unfold preparePairs
  apply pending_bind prims allowed
  · apply pending_mapM prims allowed
    intro j _
    split_ifs
    · exact pending_pure prims allowed _
    · exact public_program_pending prims D allowed _ (aimed_noProgram_free _)
  · intro _; exact pending_pure prims allowed ()

/-- Pending draw references are filled by this same boundary's digest pass.
The invariant does not require them to be cached during the pair draws. -/
theorem compileBoundaryDigest_ready (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (st : RunState C) (used : SaltLists)
    (cache : HashCache C) (blocks : BlockCache C) (state : CompilerState C)
    (ready : Ready cache blocks state)
    (r : TableOutcome (C := C) (TreeSimHashSaltBlock C) (List HashOutput × CompilerState C))
    (hr : r ∈ support (tableRun prims ((compileBoundaryDigest D ctx st).run state) used cache blocks)) :
    Ready r.2.1 r.2.2 r.1.1.2 := by
  have run : (r.1.1, r.2) ∈ support (compilerRun prims (compileBoundaryDigest D ctx st) state cache blocks) := by
    rw [compilerRun, ← read_program_erase prims _ used cache blocks, support_map]
    exact ⟨r, hr, rfl⟩
  have preserves : PreservesPending prims (HiddenTermBlock D ctx st.label)
      (compileBoundaryDigest D ctx st) := by
    unfold compileBoundaryDigest
    apply pending_bind prims _ (pending_mapM prims _ C.terms _ (fun T _ => prepareTerm_pending prims D ctx st.label T))
    intro terms
    apply pending_bind prims _ (preparePairs_pending prims D _ ctx st.label)
    intro _
    apply pending_mapM prims _ C.terms
    intro T _
    split_ifs
    · exact compileDigest_pending prims D _ _
    · exact pending_pure prims _ _
  have final := preserves state cache blocks (fun piece hp => Or.inl (ready piece hp)) (r.1.1, r.2) run
  intro piece hp
  rcases final piece hp with h | ⟨b, rfl, T, held, hidden, rfl⟩
  · exact h
  · exact compileBoundaryDigest_caches prims D ctx st T held hidden state cache blocks (r.1.1, r.2) run

theorem compileBoundaryDigest_prefetch (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (st : RunState C) (T : C.Term)
    (held : ctx.self ∈ C.holders T) (hidden : ¬ KnownTo D.1 T)
    (state : CompilerState C) (cache : HashCache C) (blocks : BlockCache C) :
    𝒟[compilerRun prims (compileBoundaryDigest D ctx st) state cache blocks] =
      𝒟[(do
        let _ ← blockRead (T, ctx.prss.term T, st.label)
        simulateQ (opaqueAnswer prims) ((compileBoundaryDigest D ctx st).run state)).run (cache, blocks)] :=
  opaque_prefetch prims _ _ cache blocks
    (compileBoundaryDigest_caches prims D ctx st T held hidden state cache blocks)

open TreeRawSaltFlowProof in
def splitRead (b : TreeSimHashSaltBlock C) : StateT (SplitState C) ProbComp (Fin 256 → Bit) :=
  StateT.mk fun s => (fun r => (r.1, s.1, r.2)) <$>
    ((TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle b).run s.2

open TreeRawSaltFlowProof in
theorem splitRead_commutes_public (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) {α : Type} (p : OracleComp (WorldSpec C) α) :
    Commutes (splitRead b) (publicRun prims D p) := by
  intro s
  simp only [splitRead, publicRun, StateT.run_mk, StateT.run_bind,
    StateT.run_pure, bind_map_left]
  rw [evalDist_bind_bind_swap]

open TreeRawSaltFlowProof in
theorem splitRead_commutes_block (b a : TreeSimHashSaltBlock C) :
    Commutes (splitRead b) (blockRun a) := by
  intro s
  have h := evalDist_map_eq_of_evalDist_eq (commutes_randomOracle_randomOracle b a s.2)
    (fun r => ((r.1.1, fun g => (List.ofFn r.1.2).getD g 0),
      ((s.1.1, s.1.2 ++ treeSimHiddenLog (treeSimHashSaltAddress a) r.1.2), r.2)))
  simpa only [splitRead, blockRun, StateT.run_mk, StateT.run_bind, StateT.run_pure,
    map_bind, bind_map_left, map_pure] using h

open TreeRawSaltFlowProof in
theorem splitRead_commutes_draw (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (name : KeyName C) (key : HashOutput) (label : ℕ) :
    Commutes (splitRead b) (splitDraw prims D name key label) := by
  cases name with
  | term T =>
    by_cases known : KnownTo D.1 T
    · simpa only [splitDraw, if_pos known] using splitRead_commutes_public prims D b _
    · simpa only [splitDraw, if_neg known] using splitRead_commutes_block b (T, key, label)
  | pair p => exact splitRead_commutes_public prims D b _
  | parameter => exact splitRead_commutes_public prims D b _

theorem commutes_mapM_right {σ ι α β : Type} (x : StateT σ ProbComp α)
    (xs : List ι) (f : ι → StateT σ ProbComp β)
    (each : ∀ i ∈ xs, Commutes x (f i)) : Commutes x (xs.mapM f) := by
  induction xs with
  | nil => simpa only [List.mapM_nil] using commutes_pure x ([] : List β)
  | cons i xs ih =>
    rw [List.mapM_cons]
    exact (each i (by simp)).bind_right fun a =>
      (ih (fun j hj => each j (by simp [hj]))).bind_right fun as => commutes_pure x (a :: as)

open TreeRawSaltFlowProof in
theorem splitRead_commutes_digest (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (ctx : Context C) (st : RunState C) :
    Commutes (splitRead b) (splitDigest prims D ctx st) := by
  unfold splitDigest splitPrss
  apply Commutes.bind_right
  · apply Commutes.bind_right
    · unfold splitTerms
      apply commutes_mapM_right
      intro T _
      split_ifs
      · exact splitRead_commutes_draw prims D b _ _ _
      · exact commutes_pure _ _
    · intro terms
      apply Commutes.bind_right
      · unfold splitPairs
        apply commutes_mapM_right
        intro j _
        split_ifs
        · exact commutes_pure _ _
        · exact splitRead_commutes_draw prims D b _ _ _
      · intro pairs
        exact commutes_pure _ _
  · intro rnd
    exact splitRead_commutes_public prims D b _

open TreeRawSaltFlowProof in
theorem splitDraw_grows (prims : Primitives) (D : C.Coalition)
    (name : KeyName C) (key : HashOutput) (label : ℕ)
    (s : SplitState C) (r : (ℕ → Bit) × SplitState C)
    (hr : r ∈ support ((splitDraw prims D name key label).run s)) : s.2 ≤ r.2.2 := by
  have pub {α : Type} (p : OracleComp (WorldSpec C) α) (r : α × SplitState C)
      (hr : r ∈ support ((publicRun prims D p).run s)) : s.2 ≤ r.2.2 := by
    simp only [publicRun, StateT.run_mk, support_map] at hr
    obtain ⟨_, _, rfl⟩ := hr
    exact le_rfl
  cases name with
  | term T =>
    by_cases known : KnownTo D.1 T
    · simp only [splitDraw, if_pos known] at hr
      exact pub _ r hr
    · simp only [splitDraw, if_neg known, blockRun, StateT.run_mk, support_map] at hr
      obtain ⟨out, hout, rfl⟩ := hr
      exact QueryImpl.withCaching_cache_le _ _ _ out hout
  | pair p => exact pub _ r hr
  | parameter => exact pub _ r hr

theorem state_mapM_eventually {ι α σ : Type} (P : σ → Prop)
    (xs : List ι) (f : ι → StateT σ ProbComp α) (i : ι) (hi : i ∈ xs)
    (preserves : ∀ j ∈ xs, ∀ s r, P s → r ∈ support ((f j).run s) → P r.2)
    (establishes : ∀ s r, r ∈ support ((f i).run s) → P r.2)
    (s : σ) (r : List α × σ) (hr : r ∈ support ((xs.mapM f).run s)) : P r.2 := by
  induction xs generalizing s r with
  | nil => simp at hi
  | cons j xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure, mem_support_bind_iff,
      mem_support_pure_iff] at hr
    obtain ⟨head, hhead, tail, htail, rfl⟩ := hr
    rcases List.mem_cons.mp hi with rfl | hi
    · exact treeSimHash_state_mapM_invariant P f xs
        (fun k hk => preserves k (by simp [hk])) head.2 (establishes s head hhead) tail htail
    · exact ih hi (fun k hk => preserves k (by simp [hk])) head.2 tail htail

open TreeRawSaltFlowProof in
theorem splitTerms_caches (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label : ℕ) (T : C.Term)
    (held : ctx.self ∈ C.holders T) (hidden : ¬ KnownTo D.1 T)
    (s : SplitState C) (r : List (ℕ → Bit) × SplitState C)
    (hr : r ∈ support ((splitTerms prims D ctx label).run s)) :
    ∃ values, r.2.2 (T, ctx.prss.term T, label) = some values := by
  apply state_mapM_eventually (fun s : SplitState C =>
    ∃ values, s.2 (T, ctx.prss.term T, label) = some values) C.terms _ T (mem_terms T) _ _ s r hr
  · intro U _ before after hbefore hafter
    by_cases hu : ctx.self ∈ C.holders U
    · simp only [if_pos hu] at hafter
      obtain ⟨v, hv⟩ := hbefore
      exact ⟨v, splitDraw_grows prims D _ _ _ before after hafter hv⟩
    · simp only [if_neg hu, StateT.run_pure, mem_support_pure_iff] at hafter
      subst after
      exact hbefore
  · intro before after hafter
    simp only [if_pos held, splitDraw, if_neg hidden, blockRun, StateT.run_mk, support_map] at hafter
    obtain ⟨out, hout, rfl⟩ := hafter
    exact ⟨out.1, DeterministicSigning.query_caches _ _ out hout⟩

open TreeRawSaltFlowProof in
theorem splitDigest_caches (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (st : RunState C) (T : C.Term)
    (held : ctx.self ∈ C.holders T) (hidden : ¬ KnownTo D.1 T)
    (s : SplitState C) (r : List HashOutput × SplitState C)
    (hr : r ∈ support ((splitDigest prims D ctx st).run s)) :
    ∃ values, r.2.2 (T, ctx.prss.term T, st.label) = some values := by
  simp only [splitDigest, splitPrss, StateT.run_bind,
    bind_assoc, pure_bind, mem_support_bind_iff] at hr
  obtain ⟨terms, hterms, pairs, hpairs, hr⟩ := hr
  have cached := splitTerms_caches prims D ctx st.label T held hidden s terms hterms
  have kept : ∃ values, pairs.2.2 (T, ctx.prss.term T, st.label) = some values := by
    apply treeSimHash_state_mapM_invariant (fun s : SplitState C =>
      ∃ values, s.2 (T, ctx.prss.term T, st.label) = some values) _ C.parties _ terms.2 cached pairs hpairs
    intro j _ before after hbefore hafter
    by_cases hj : j = ctx.self
    · simp only [dif_pos hj, StateT.run_pure, mem_support_pure_iff] at hafter
      subst after
      exact hbefore
    · simp only [dif_neg hj] at hafter
      obtain ⟨v, hv⟩ := hbefore
      exact ⟨v, splitDraw_grows prims D _ _ _ before after hafter hv⟩
  simp only [publicRun, StateT.run_mk, support_map] at hr
  obtain ⟨out, _, rfl⟩ := hr
  exact kept

open TreeRawSaltFlowProof in
/-- The real split boundary admits the same silent block prefetch, retaining
its actual draw/pair/digest transcript in its original order. -/
theorem splitDigest_prefetch (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (st : RunState C) (T : C.Term)
    (held : ctx.self ∈ C.holders T) (hidden : ¬ KnownTo D.1 T) (s : SplitState C) :
    𝒟[(splitDigest prims D ctx st).run s] =
      𝒟[(do let _ ← splitRead (T, ctx.prss.term T, st.label); splitDigest prims D ctx st).run s] := by
  have commute := (splitRead_commutes_digest prims D (T, ctx.prss.term T, st.label) ctx st).bind
    (fun _ result => pure result) s
  simp only [bind_pure] at commute
  rw [commute]
  simp only [StateT.run_bind, StateT.run_pure]
  conv_lhs => rw [← bind_pure ((splitDigest prims D ctx st).run s)]
  apply evalDist_bind_congr
  intro r hr
  obtain ⟨values, hv⟩ := splitDigest_caches prims D ctx st T held hidden s r hr
  simp only [splitRead, StateT.run_mk, QueryImpl.withCaching_run_some _ hv, map_pure, pure_bind]

def boundaryBlocks (D : C.Coalition) (ctx : Context C) (label : ℕ) : List (TreeSimHashSaltBlock C) :=
  (C.terms.filter (fun T => decide (ctx.self ∈ C.holders T ∧ ¬ KnownTo D.1 T))).map
    (fun T => (T, ctx.prss.term T, label))

theorem boundaryBlocks_mem (D : C.Coalition) (ctx : Context C) (label : ℕ)
    (b : TreeSimHashSaltBlock C) : b ∈ boundaryBlocks D ctx label ↔ HiddenTermBlock D ctx label b := by
  simp only [boundaryBlocks, List.mem_map, List.mem_filter, decide_eq_true_eq, HiddenTermBlock]
  constructor
  · rintro ⟨T, ⟨_, held, hidden⟩, rfl⟩
    exact ⟨T, held, hidden, rfl⟩
  · rintro ⟨T, held, hidden, rfl⟩
    exact ⟨T, ⟨mem_terms T, held, hidden⟩, rfl⟩

def sampleBlocks (bs : List (TreeSimHashSaltBlock C)) (blocks : BlockCache C) :
    ProbComp (List (Fin 256 → Bit) × BlockCache C) :=
  (bs.mapM (TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle).run blocks

theorem sampleBlocks_grows (bs : List (TreeSimHashSaltBlock C)) (blocks : BlockCache C)
    (r : List (Fin 256 → Bit) × BlockCache C) (hr : r ∈ support (sampleBlocks bs blocks)) : blocks ≤ r.2 := by
  exact treeSimHash_state_mapM_invariant (fun cache => blocks ≤ cache) _ bs
    (fun b _ s out hs hout => hs.trans (QueryImpl.withCaching_cache_le _ b s out hout)) blocks le_rfl r hr

theorem sampleBlocks_caches (bs : List (TreeSimHashSaltBlock C)) (blocks : BlockCache C)
    (r : List (Fin 256 → Bit) × BlockCache C) (hr : r ∈ support (sampleBlocks bs blocks))
    (b : TreeSimHashSaltBlock C) (hb : b ∈ bs) : ∃ values, r.2 b = some values := by
  apply state_mapM_eventually (fun cache : BlockCache C => ∃ values, cache b = some values)
    bs _ b hb _ _ blocks r hr
  · intro a _ s out hs hout
    obtain ⟨v, hv⟩ := hs
    exact ⟨v, QueryImpl.withCaching_cache_le _ a s out hout hv⟩
  · intro s out hout
    exact ⟨out.1, DeterministicSigning.query_caches b s out hout⟩

theorem prefetch_list {α : Type} (bs : List (TreeSimHashSaltBlock C))
    (run : BlockCache C → ProbComp α)
    (each : ∀ b ∈ bs, ∀ blocks,
      𝒟[run blocks] = 𝒟[((TreeSimHashSaltBlock C →ₒ (Fin 256 → Bit)).randomOracle b).run blocks >>= fun r => run r.2])
    (blocks : BlockCache C) :
    𝒟[run blocks] = 𝒟[sampleBlocks bs blocks >>= fun r => run r.2] := by
  induction bs generalizing blocks with
  | nil => simp [sampleBlocks]
  | cons b bs ih =>
    rw [each b (by simp) blocks]
    simp only [sampleBlocks, List.mapM_cons, StateT.run_bind, StateT.run_pure,
      bind_assoc, pure_bind]
    apply evalDist_bind_congr'
    intro first
    simpa only [sampleBlocks] using ih (fun a ha => each a (by simp [ha])) first.2

/-- Prefetching exactly the held hidden handles preserves the complete
concrete compiler execution, before any decoder projection. -/
theorem compileBoundaryDigest_prefetch_all (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (st : RunState C) (state : CompilerState C)
    (cache : HashCache C) (blocks : BlockCache C) :
    𝒟[compilerRun prims (compileBoundaryDigest D ctx st) state cache blocks] =
      𝒟[sampleBlocks (boundaryBlocks D ctx st.label) blocks >>= fun r =>
        compilerRun prims (compileBoundaryDigest D ctx st) state cache r.2] := by
  apply prefetch_list
  intro b hb blocks'
  obtain ⟨T, held, hidden, rfl⟩ := (boundaryBlocks_mem D ctx st.label b).mp hb
  have h := compileBoundaryDigest_prefetch prims D ctx st T held hidden state cache blocks'
  simpa only [compilerRun, StateT.run_bind, blockRead, StateT.run_mk, bind_map_left] using h

open TreeRawSaltFlowProof in
/-- The same finite prefetch preserves the complete real split execution,
including the original-order transcript. -/
theorem splitDigest_prefetch_all (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (st : RunState C) (s : TreeSimState C) (blocks : TreeRawSaltCeremonyProof.BlockCache C) :
    𝒟[(splitDigest prims D ctx st).run (s, blocks)] =
      𝒟[sampleBlocks (boundaryBlocks D ctx st.label) blocks >>= fun r =>
        (splitDigest prims D ctx st).run (s, r.2)] := by
  apply prefetch_list (boundaryBlocks D ctx st.label) (fun blocks => (splitDigest prims D ctx st).run (s, blocks))
  intro b hb blocks'
  obtain ⟨T, held, hidden, rfl⟩ := (boundaryBlocks_mem D ctx st.label b).mp hb
  have h := splitDigest_prefetch prims D ctx st T held hidden (s, blocks')
  simpa only [StateT.run_bind, splitRead, StateT.run_mk, bind_map_left] using h

/-- Every safe fixed boundary preserves decoder readiness, independently
of the distribution-law proof. -/
theorem boundaryCompiler_ready (prims : Primitives) (D : C.Coalition)
    (t : (TreeRawSaltFlowProof.BoundarySpec D).Domain) (safe : ¬ BoundaryProgramCall D t)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (state : CompilerState C) (ready : Ready cache blocks state)
    (r : TableOutcome (C := C) (TreeSimHashSaltBlock C)
      ((TreeRawSaltFlowProof.BoundarySpec D).Range t × CompilerState C))
    (hr : r ∈ support (tableRun prims ((boundaryCompiler D t).run state) used cache blocks)) :
    Ready r.2.1 r.2.2 r.1.1.2 := by
  rcases t with ⟨ctx, st⟩ | ⟨t, ht⟩
  · exact compileBoundaryDigest_ready prims D ctx st used cache blocks state ready r hr
  · exact publicQuery_ready prims D t safe used cache blocks state ready r hr

/-- Readiness composes through every adaptive safe boundary program, using
the concrete compiler and its actual table execution. -/
theorem compiler_program_ready (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (TreeRawSaltFlowProof.BoundarySpec D) α)
    (safe : IsQueryBoundP p (BoundaryProgramCall D) 0)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (state : CompilerState C) (ready : Ready cache blocks state)
    (r : TableOutcome (C := C) (TreeSimHashSaltBlock C) (α × CompilerState C))
    (hr : r ∈ support (tableRun prims ((simulateQ (boundaryCompiler D) p).run state) used cache blocks)) :
    Ready r.2.1 r.2.2 r.1.1.2 := by
  induction p using OracleComp.inductionOn generalizing used cache blocks state r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, tableRun, mem_support_pure_iff] at hr
    subst r
    exact ready
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at safe
    have ht : ¬ BoundaryProgramCall D t := by simpa using safe.1
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
      tableRun_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    exact ih mid.1.1.1 (by simpa [ht] using safe.2 mid.1.1.1)
      mid.1.2 mid.2.1 mid.2.2 mid.1.1.2
      (boundaryCompiler_ready prims D t ht used cache blocks state ready mid hmid) r hr

theorem compilerRun_decode (prims : Primitives) {α : Type} (p : CompilerM C α)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C) (state : CompilerState C) :
    decodeResult <$> tableRun prims (p.run state) used cache blocks =
      (fun r => (r.1.1, decodeCompiler r.2.1 r.2.2 r.1.2)) <$>
        compilerRun prims p state cache blocks := by
  rw [compilerRun, ← read_program_erase prims _ used cache blocks, Functor.map_map]
  rfl

/-- The fixed boundary expansion when all its held hidden blocks are
already cached. Hidden draws are deterministic reads in this assertion;
known and pair streams, history hashing and the ordered transcript remain
those of the actual source and the fixed compiler. -/
def CachedDigestCompilerLaw (prims : Primitives) (D : C.Coalition) : Prop :=
  ∀ (ctx : Context C) (st : RunState C) (cache : HashCache C)
    (blocks : BlockCache C) (state : CompilerState C), Ready cache blocks state →
    (∀ b ∈ boundaryBlocks D ctx st.label, ∃ values, blocks b = some values) →
    𝒟[(fun r => (r.1, TreeRawSaltFlowProof.decodeState r.2)) <$>
      (TreeRawSaltFlowProof.splitDigest prims D ctx st).run
        (((cache, state.1), state.2.flatMap (LogPiece.decode cache blocks)), blocks)] =
      𝒟[(fun r => (r.1.1, decodeCompiler r.2.1 r.2.2 r.1.2)) <$>
        compilerRun prims (compileBoundaryDigest D ctx st) state cache blocks]

variable {E : Type} [Field E] [Algebra Bit E]

/-- Silent prefetch removes the cached-block premise, using the same finite
sample on both sides and preserving the complete original-order log. -/
theorem digestCompiler_joint_of_cached (prims : Primitives) (D : C.Coalition)
    (cachedLaw : CachedDigestCompilerLaw prims D)
    (ctx : Context C) (st : RunState C) (used : SaltLists)
    (cache : HashCache C) (blocks : BlockCache C) (state : CompilerState C)
    (ready : Ready cache blocks state) :
    𝒟[(simulateQ (treeSimLoggedWorld prims D)
      (TreeRawSaltFlowProof.boundarySource (E := E) D (.inl (ctx, st)))).run
        (decodeCompiler cache blocks state)] =
      𝒟[decodeResult <$> tableRun prims ((compileBoundaryDigest D ctx st).run state) used cache blocks] := by
  have source := TreeRawSaltFlowProof.splitDigest_joint (E := E) prims D ctx st
    (((cache, state.1), state.2.flatMap (LogPiece.decode cache blocks)), blocks)
  change 𝒟[(simulateQ (treeSimLoggedWorld prims D)
      (TreeRawSaltFlowProof.boundarySource (E := E) D (.inl (ctx, st)))).run
        (decodeCompiler cache blocks state)] = _ at source
  rw [source, compilerRun_decode]
  have left := evalDist_map_eq_of_evalDist_eq
    (splitDigest_prefetch_all prims D ctx st
      ((cache, state.1), state.2.flatMap (LogPiece.decode cache blocks)) blocks)
    (fun r => (r.1, TreeRawSaltFlowProof.decodeState r.2))
  have right := evalDist_map_eq_of_evalDist_eq
    (compileBoundaryDigest_prefetch_all prims D ctx st state cache blocks)
    (fun r => (r.1.1, decodeCompiler r.2.1 r.2.2 r.1.2))
  rw [left, right]
  simp only [map_bind]
  apply evalDist_bind_congr
  intro sampled hsampled
  have grows := sampleBlocks_grows _ blocks sampled hsampled
  have stable := Ready.log_mono state (le_refl cache) grows ready
  have law := cachedLaw ctx st cache sampled.2 state (ready_mono (le_refl cache) grows ready)
    (sampleBlocks_caches _ blocks sampled hsampled)
  simpa only [stable] using law

set_option backward.isDefEq.respectTransparency false in
/-- The fixed compiler's full boundary target follows from its expansion on
cached blocks. Public boundaries and readiness require no residual premise. -/
theorem boundaryCompilerSteps_of_cached (prims : Primitives) (D : C.Coalition)
    (cachedLaw : CachedDigestCompilerLaw prims D) : BoundaryCompilerSteps (E := E) prims D := by
  intro t safe used cache blocks state ready
  constructor
  · rcases t with ⟨ctx, st⟩ | ⟨t, ht⟩
    · exact digestCompiler_joint_of_cached prims D cachedLaw ctx st used cache blocks state ready
    · simpa only [TreeRawSaltFlowProof.boundarySource, simulateQ_spec_query, boundaryCompiler] using
        publicQuery_joint prims D t safe ht used cache blocks state ready
  · exact boundaryCompiler_ready prims D t safe used cache blocks state ready



omit [Field E] [Algebra Bit E] in
/-- Pair draws keep the real party order and discard only their returned
values; their random choices and per-bit transcript are still executed. -/
theorem preparePairs_eq (D : C.Coalition) (ctx : Context C) (label : ℕ) :
    preparePairs D ctx label = simulateQ (publicQuery D)
      (free (liftComp (pairDraws ctx (bitCodec (E := E)) label 2 256) (LocalSpec C)) >>= fun _ => pure ()) := by
  simp only [preparePairs, simulateQ_bind, simulateQ_pure, pairDraws, treeSimHash_mapM_ro]
  congr 1
  congr 1
  funext j
  by_cases hj : j = ctx.self
  · simp only [dif_pos hj, liftComp_pure, free_pure, simulateQ_pure]
  · simp only [dif_neg hj, bitCodec, publicDraw]

omit [Field E] [Algebra Bit E] in
theorem preparePairs_noSalt (D : C.Coalition) (ctx : Context C) (label : ℕ) :
    IsQueryBoundP (free (liftComp (pairDraws ctx (bitCodec (E := E)) label 2 256) (LocalSpec C)))
      (fun t => ¬TreeRawSaltFlowProof.NoSaltRead D t) 0 := by
  apply TreeRawSaltFlowProof.ro_noSalt
  unfold pairDraws
  have law := queryBound_mapM (fun t => ¬TreeRawSaltFlowProof.NoSaltRead D (.inr (.inr t)))
    (fun j => if hj : j = ctx.self then pure fun _ : ℕ => (0 : Bit)
      else (bitCodec (E := E)).draw (.pair (C.pairOf ctx.self j (Ne.symm hj)))
        (ctx.prss.pair j) label 2 256) 0 C.parties (fun j _ => ?_)
  · simpa using law
  · split_ifs
    · exact isQueryBoundP_pure _ _ _
    · apply TreeRawSaltFlowProof.prg_noSalt_ro
      intro _ g
      exact TreeRawSaltFlowProof.saltAt_pair _ _ _ _ _

omit [Field E] [Algebra Bit E] in
theorem public_program_blocks (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (WorldSpec C) α) (safe : IsQueryBoundP p AimedProgramCall 0)
    (state : CompilerState C) (cache : HashCache C) (blocks : BlockCache C)
    (r : CompilerOutcome C α)
    (hr : r ∈ support (compilerRun prims (simulateQ (publicQuery D) p) state cache blocks)) :
    r.2.2 = blocks := by
  induction p using OracleComp.inductionOn generalizing state cache blocks r with
  | pure a =>
    simp only [simulateQ_pure, compilerRun, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    rfl
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at safe
    have ht : ¬ AimedProgramCall t := by simpa using safe.1
    simp only [simulateQ_bind, simulateQ_spec_query, compilerRun_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    have hm : mid.2.2 = blocks := by
      rw [compilerRun, publicQuery_run prims D t ht, support_map] at hmid
      obtain ⟨_, _, rfl⟩ := hmid
      rfl
    exact (ih mid.1.1 (by simpa [ht] using safe.2 mid.1.1) _ _ _ r hr).trans hm

omit [Field E] [Algebra Bit E] in
theorem compileDigest_private_cached_joint (prims : Primitives) (D : C.Coalition)
    (b : TreeSimHashSaltBlock C) (history : List Bit) (values : Fin 256 → Bit)
    (cache : HashCache C) (blocks : BlockCache C) (state : CompilerState C)
    (present : blocks b = some values) (ready : Ready cache blocks state) :
    𝒟[(simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (oneDigestQuery (C := C) (List.ofFn values) history) (LocalSpec C)))).run
        (decodeCompiler cache blocks state)] =
      𝒟[(fun r => (r.1.1, decodeCompiler r.2.1 r.2.2 r.1.2)) <$>
        compilerRun prims (compileDigest D (.inl b, history)) state cache blocks] := by
  rw [decodeCompiler, oneDigest_logged, compilerRun, compileDigest_private_run,
    opaqueDigest_run, QueryImpl.withCaching_run_some _ present, pure_bind]
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
  apply evalDist_bind_congr
  intro out hout
  have grown := (saltedDigest_cached prims (List.ofFn values) history cache out hout).1
  have stable := Ready.log_mono state grown (le_refl blocks) ready
  simp only [decodeCompiler, List.flatMap_append, List.flatMap_cons,
    List.flatMap_nil, LogPiece.decode, blockValues, present, Option.getD_some,
    List.append_nil, stable]

/-- A local decoded law with a fixed private cache and possibly different
representations of the returned value. -/
def FixedLaw (prims : Primitives) (blocks : BlockCache C) {α β : Type}
    (source : StateT (TreeSimState C) ProbComp α) (p : CompilerM C β) (value : β → α) : Prop :=
  ∀ cache state, Ready cache blocks state →
    𝒟[source.run (decodeCompiler cache blocks state)] =
      𝒟[(fun r => (value r.1.1, decodeCompiler r.2.1 r.2.2 r.1.2)) <$>
        compilerRun prims p state cache blocks] ∧
    ∀ r ∈ support (compilerRun prims p state cache blocks),
      r.2.2 = blocks ∧ Ready r.2.1 r.2.2 r.1.2

omit [Field E] [Algebra Bit E] in
theorem fixedLaw_pure (prims : Primitives) (blocks : BlockCache C) {α β : Type}
    (b : β) (value : β → α) : FixedLaw prims blocks (pure (value b)) (pure b) value := by
  intro cache state ready
  simp only [StateT.run_pure, compilerRun, simulateQ_pure, map_pure]
  constructor
  · trivial
  · intro r hr
    simp only [mem_support_pure_iff] at hr
    subst r
    exact ⟨rfl, ready⟩

omit [Field E] [Algebra Bit E] in
theorem fixedLaw_bind (prims : Primitives) (blocks : BlockCache C)
    {α β γ δ : Type} {source : StateT (TreeSimState C) ProbComp α} {p : CompilerM C β}
    {value : β → α} {tail : α → StateT (TreeSimState C) ProbComp γ}
    {k : β → CompilerM C δ} {output : δ → γ}
    (first : FixedLaw prims blocks source p value)
    (next : ∀ b, FixedLaw prims blocks (tail (value b)) (k b) output) :
    FixedLaw prims blocks (source >>= tail) (p >>= k) output := by
  intro cache state ready
  have initial := first cache state ready
  constructor
  · simp only [StateT.run_bind, compilerRun_bind, map_bind]
    rw [evalDist_bind, initial.1]
    simp only [← evalDist_bind, bind_map_left]
    apply evalDist_bind_congr
    intro r hr
    obtain ⟨hb, ready'⟩ := initial.2 r hr
    rw [hb] at ready' ⊢
    exact (next r.1.1 r.2.1 r.1.2 ready').1
  · intro r hr
    rw [compilerRun_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hmid, hr⟩ := hr
    obtain ⟨hb, ready'⟩ := initial.2 mid hmid
    rw [hb] at ready' hr
    exact (next mid.1.1 mid.2.1 mid.1.2 ready').2 r hr

omit [Field E] [Algebra Bit E] in
theorem fixedLaw_mapM (prims : Primitives) (blocks : BlockCache C) {ι α β : Type}
    (xs : List ι) (source : ι → StateT (TreeSimState C) ProbComp α)
    (p : ι → CompilerM C β) (value : β → α)
    (each : ∀ i ∈ xs, FixedLaw prims blocks (source i) (p i) value) :
    FixedLaw prims blocks (xs.mapM source) (xs.mapM p) (List.map value) := by
  induction xs with
  | nil => simpa only [List.mapM_nil, List.map_nil] using fixedLaw_pure prims blocks ([] : List β) (List.map value)
  | cons i xs ih =>
    simp only [List.mapM_cons]
    apply fixedLaw_bind prims blocks (each i (by simp))
    intro b
    apply fixedLaw_bind prims blocks (ih (fun j hj => each j (by simp [hj])))
    intro bs
    exact fixedLaw_pure prims blocks (b :: bs) (List.map value)

omit [Field E] [Algebra Bit E] in
theorem fixedLaw_public (prims : Primitives) (D : C.Coalition) (blocks : BlockCache C)
    {α : Type} (p : OracleComp (WorldSpec C) α)
    (noProgram : IsQueryBoundP p AimedProgramCall 0)
    (noSalt : IsQueryBoundP p (fun t => ¬ TreeRawSaltFlowProof.NoSaltRead D t) 0) :
    FixedLaw prims blocks (simulateQ (treeSimLoggedWorld prims D) p)
      (simulateQ (publicQuery D) p) id := by
  intro cache state ready
  have step := public_program_steps prims D p noProgram noSalt ([], []) cache blocks state ready
  constructor
  · simpa only [compilerRun_decode, id_eq] using step.1
  · intro r hr
    have hb := public_program_blocks prims D p noProgram state cache blocks r hr
    have erased := hr
    rw [compilerRun, ← read_program_erase prims _ ([], []) cache blocks, support_map] at erased
    obtain ⟨table, htable, he⟩ := erased
    refine ⟨hb, ?_⟩
    exact (congrArg (fun out => Ready out.2.1 out.2.2 out.1.2) he).mp (step.2 table htable)

def saltFunction (blocks : BlockCache C) : Salt C → (ℕ → Bit)
  | .inl b => fun g => (List.ofFn (blockValues blocks b)).getD g 0
  | .inr bits => fun g => bits.getD g 0

omit [Field E] [Algebra Bit E] in
theorem vector_getD_list (bits : List Bit) (count : ℕ) (length : bits.length = count) :
    vector count (fun g => bits.getD g 0) = bits := by
  apply List.ext_getElem
  · simp [vector, length]
  · intro k hk hk'
    simp [vector, List.getD, hk']

set_option backward.isDefEq.respectTransparency false in
omit [Field E] [Algebra Bit E] in
theorem publicDraw_shape (prims : Primitives) (D : C.Coalition)
    (name : KeyName C) (key : HashOutput) (label : ℕ)
    (state : CompilerState C) (cache : HashCache C) (blocks : BlockCache C)
    (r : CompilerOutcome C (ℕ → Bit))
    (hr : r ∈ support (compilerRun prims (publicDraw D name key label) state cache blocks)) :
    ∃ bits : List Bit, bits.length = 256 ∧ r.1.1 = fun g => bits.getD g 0 := by
  simp only [publicDraw, prgBits, liftComp_bind, free_bind, simulateQ_bind,
    liftComp_pure, free_pure, simulateQ_pure, treeSimHash_mapM_ro,
    compilerRun_bind, mem_support_bind_iff] at hr
  obtain ⟨draws, hdraws, hr⟩ := hr
  simp only [compilerRun, StateT.run_pure, simulateQ_pure, mem_support_pure_iff] at hr
  subst r
  refine ⟨draws.1.1, ?_, rfl⟩
  have rel := compilerRun_mapM_rel prims (List.range 256) _ (fun _ _ => True)
    (fun _ _ _ _ _ _ _ => trivial) state cache blocks draws hdraws
  simpa using rel.length_eq.symm

omit [Field E] [Algebra Bit E] in
theorem fixedLaw_map_compiler (prims : Primitives) (blocks : BlockCache C)
    {α β γ : Type} {source : StateT (TreeSimState C) ProbComp α} {p : CompilerM C β}
    (value : β → α) (f : β → γ) (output : γ → α)
    (law : FixedLaw prims blocks source p value)
    (same : ∀ state cache r, r ∈ support (compilerRun prims p state cache blocks) →
      output (f r.1.1) = value r.1.1) :
    FixedLaw prims blocks source (f <$> p) output := by
  intro cache state ready
  have first := law cache state ready
  have run : compilerRun prims (f <$> p) state cache blocks =
      (fun r => ((f r.1.1, r.1.2), r.2)) <$> compilerRun prims p state cache blocks := by
    simp only [compilerRun, StateT.run_map, simulateQ_map]
  rw [run]
  constructor
  · rw [first.1]
    simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_def, pure_bind]
    apply evalDist_bind_congr
    intro r hr
    simp only [same state cache r hr]
  · intro r hr
    rw [support_map] at hr
    obtain ⟨out, hout, rfl⟩ := hr
    exact first.2 out hout

omit [Field E] [Algebra Bit E] in
def realTerm (prims : Primitives) (D : C.Coalition) (ctx : Context C) (label : ℕ)
    (T : C.Term) : StateT (TreeSimState C) ProbComp (ℕ → Bit) :=
  if ctx.self ∈ C.holders T then
    simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prgBits (.term T) (ctx.prss.term T) label 2 256) (LocalSpec C)))
  else pure fun _ => 0

omit [Field E] [Algebra Bit E] in
theorem prepareTerm_fixed (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label : ℕ) (blocks : BlockCache C)
    (covered : ∀ b ∈ boundaryBlocks D ctx label, ∃ values, blocks b = some values)
    (T : C.Term) :
    FixedLaw prims blocks (realTerm prims D ctx label T)
      (prepareTerm D ctx label T) (saltFunction blocks) := by
  by_cases held : ctx.self ∈ C.holders T
  · by_cases known : KnownTo D.1 T
    · simp only [realTerm, prepareTerm, if_pos held, if_pos known]
      apply fixedLaw_map_compiler prims blocks id
        (fun bits => Sum.inr (vector 256 bits)) (saltFunction blocks)
      · exact fixedLaw_public prims D blocks _ (aimed_noProgram_free _)
          (TreeRawSaltFlowProof.prg_noSalt D (.term T) (ctx.prss.term T) label 2 256
            (fun hidden => (hidden known).elim))
      · intro state cache r hr
        obtain ⟨bits, hlen, hvalue⟩ := publicDraw_shape prims D (.term T) (ctx.prss.term T) label state cache blocks r hr
        simp only [saltFunction, hvalue, vector_getD_list bits 256 hlen, id_eq]
    · obtain ⟨values, present⟩ := covered (T, ctx.prss.term T, label)
        ((boundaryBlocks_mem D ctx label _).mpr ⟨T, held, known, rfl⟩)
      intro cache state ready
      have source := TreeRawSaltFlowProof.blockRun_joint prims D (T, ctx.prss.term T, label) known
        (((cache, state.1), state.2.flatMap (LogPiece.decode cache blocks)), blocks)
      simp only [TreeRawSaltFlowProof.blockRun, StateT.run_mk,
        QueryImpl.withCaching_run_some _ present, map_pure] at source
      constructor
      · simpa only [realTerm, if_pos held, prepareTerm, if_neg known, compilerRun,
          emit, StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
          simulateQ_pure, map_pure, decodeCompiler, saltFunction, blockValues, present,
          Option.getD_some, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          LogPiece.decode, List.append_nil, TreeRawSaltFlowProof.decodeState,
          TreeRawSaltFlowProof.restoreState] using source
      · intro r hr
        simp only [compilerRun, prepareTerm, if_pos held, if_neg known, emit,
          StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
          simulateQ_pure, mem_support_pure_iff] at hr
        subst r
        refine ⟨rfl, ?_⟩
        intro piece hp
        simp only [List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact ready piece hp
        · exact ⟨values, present⟩
  · simpa only [realTerm, prepareTerm, if_neg held, saltFunction, List.getD_nil] using
      fixedLaw_pure prims blocks (.inr ([] : List Bit)) (saltFunction blocks)

omit [Field E] [Algebra Bit E] in
theorem compileDigest_fixed (prims : Primitives) (D : C.Coalition) (blocks : BlockCache C)
    (row : Row C)
    (cached : ∀ b, row.1 = .inl b → ∃ values, blocks b = some values)
    (length : ∀ bits, row.1 = .inr bits → bits.length = 256) :
    FixedLaw prims blocks
      (simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (oneDigestQuery (C := C) (vector 256 (saltFunction blocks row.1)) row.2) (LocalSpec C))))
      (compileDigest D row) id := by
  rcases row with ⟨b | bits, history⟩
  · obtain ⟨values, present⟩ := cached b rfl
    intro cache state ready
    constructor
    · simpa only [saltFunction, blockValues, present, Option.getD_some, vector_getD_ofFn, id_eq] using
        compileDigest_private_cached_joint prims D b history values cache blocks state present ready
    · intro r hr
      simp only [compilerRun, compileDigest_private_run, opaqueDigest_run,
        QueryImpl.withCaching_run_some _ present, pure_bind, map_eq_bind_pure_comp,
        bind_assoc, pure_bind, Function.comp_def, mem_support_bind_iff, mem_support_pure_iff] at hr
      obtain ⟨out, hout, rfl⟩ := hr
      obtain ⟨grow, h, hh⟩ := saltedDigest_cached prims (List.ofFn values) history cache out hout
      have old := ready_mono grow (le_refl blocks) ready
      refine ⟨rfl, ?_⟩
      intro piece hp
      simp only [List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | rfl
      · exact old piece hp
      · exact ⟨⟨values, present⟩, h, hh⟩
  · simp only [saltFunction, vector_getD_list bits 256 (length bits rfl), compileDigest]
    apply fixedLaw_public prims D blocks _ (aimed_noProgram_free _)
    apply TreeRawSaltFlowProof.ro_noSalt
    exact isQueryBoundP_bind (TreeRawSaltFlowProof.hash_noSalt_ro D _)
      (fun _ _ => TreeRawSaltFlowProof.hash_noSalt_ro D _)

omit [Field E] [Algebra Bit E] in
theorem termSalt_held (D : C.Coalition) (ctx : Context C) (label : ℕ)
    (blocks : BlockCache C)
    (covered : ∀ b ∈ boundaryBlocks D ctx label, ∃ values, blocks b = some values)
    (T : C.Term) (held : ctx.self ∈ C.holders T) (salt : Salt C)
    (shape : TermSalt D ctx label T salt) :
    (∀ b, salt = .inl b → ∃ values, blocks b = some values) ∧
      (∀ bits, salt = .inr bits → bits.length = 256) := by
  by_cases known : KnownTo D.1 T
  · simp only [TermSalt, if_pos held, if_pos known] at shape
    obtain ⟨bits, rfl, hlen⟩ := shape
    constructor
    · intro _ h; cases h
    · intro _ h; exact Sum.inr.inj h ▸ hlen
  · simp only [TermSalt, if_pos held, if_neg known] at shape
    subst salt
    constructor
    · intro b hb
      have he := Sum.inl.inj hb
      subst b
      exact covered _ ((boundaryBlocks_mem D ctx label _).mpr ⟨T, held, known, rfl⟩)
    · intro _ h
      cases h

omit [Field E] [Algebra Bit E] in
theorem preparePairs_fixed (prims : Primitives) (D : C.Coalition) (blocks : BlockCache C)
    (ctx : Context C) (label : ℕ) :
    FixedLaw prims blocks
      (simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (pairDraws ctx (bitCodec (E := E)) label 2 256) (LocalSpec C)) >>= fun _ => pure ()))
      (preparePairs D ctx label) id := by
  rw [preparePairs_eq (E := E)]
  apply fixedLaw_public prims D blocks
  · exact isQueryBoundP_bind (n := 0) (m := 0) (aimed_noProgram_free _) (fun _ _ => isQueryBoundP_pure _ _ _)
  · exact isQueryBoundP_bind (n := 0) (m := 0) (preparePairs_noSalt (E := E) D ctx label)
      (fun _ _ => isQueryBoundP_pure _ _ _)

set_option backward.isDefEq.respectTransparency false in
omit [Field E] [Algebra Bit E] in
theorem digestRows_fixed (prims : Primitives) (D : C.Coalition) (blocks : BlockCache C)
    (ctx : Context C) (st : RunState C)
    (covered : ∀ b ∈ boundaryBlocks D ctx st.label, ∃ values, blocks b = some values)
    (salts : List (Salt C)) (shape : List.Forall₂ (TermSalt D ctx st.label) C.terms salts) :
    FixedLaw prims blocks
      (simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (digestQuery ctx.self
          (fun T => (salts.map (saltFunction blocks)).getD (C.terms.idxOf T) (fun _ => 0)) st.history) (LocalSpec C))))
      (C.terms.mapM fun T => if ctx.self ∈ C.holders T then
        compileDigest D (salts.getD (C.terms.idxOf T) (.inr []), st.history T) else pure 0) id := by
  simp only [digestQuery, treeSimHash_mapM_ro]
  have law := fixedLaw_mapM prims blocks C.terms
    (fun T => simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (if ctx.self ∈ C.holders T then do
        hashQuery (C := C) (.digest (vector 256 ((salts.map (saltFunction blocks)).getD (C.terms.idxOf T) (fun _ => 0)))
          (← hashQuery (C := C) (.history (st.history T)))) else pure 0) (LocalSpec C))))
    (fun T => if ctx.self ∈ C.holders T then
      compileDigest D (salts.getD (C.terms.idxOf T) (.inr []), st.history T) else pure 0) id (fun T _ => ?_)
  · simpa only [List.map_id_fun] using law
  · by_cases held : ctx.self ∈ C.holders T
    · simp only [if_pos held]
      have hf : (salts.map (saltFunction blocks)).getD (C.terms.idxOf T) (fun _ => 0) =
          saltFunction blocks (salts.getD (C.terms.idxOf T) (.inr [])) := by
        exact List.getD_map salts (.inr []) (saltFunction blocks)
      rw [hf]
      have h := termSalt_held D ctx st.label blocks covered T held _
        (termSalt_getD D ctx st.label salts shape T)
      simpa only [oneDigestQuery] using
        compileDigest_fixed prims D blocks (salts.getD (C.terms.idxOf T) (.inr []), st.history T) h.1 h.2
    · simp only [if_neg held, liftComp_pure, free_pure, simulateQ_pure]
      exact fixedLaw_pure prims blocks 0 id

omit [Field E] [Algebra Bit E] in
theorem realTerms_eq (prims : Primitives) (D : C.Coalition) (ctx : Context C) (label : ℕ) :
    simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (termDraws ctx (bitCodec (E := E)) label 2 256) (LocalSpec C))) =
      C.terms.mapM (realTerm prims D ctx label) := by
  simp only [termDraws, treeSimHash_mapM_ro]
  congr 1
  funext T
  by_cases held : ctx.self ∈ C.holders T
  · simp only [if_pos held, bitCodec, realTerm]
  · simp only [if_neg held, realTerm, liftComp_pure, free_pure, simulateQ_pure]

omit [Field E] [Algebra Bit E] in
theorem realBoundary_eq (prims : Primitives) (D : C.Coalition) (ctx : Context C) (st : RunState C) :
    simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (treeSimHashSaltDigestDraw (E := E) ctx st) (LocalSpec C))) = (do
        let terms ← C.terms.mapM (realTerm prims D ctx st.label)
        let _ ← simulateQ (treeSimLoggedWorld prims D)
          (free (liftComp (pairDraws ctx (bitCodec (E := E)) st.label 2 256) (LocalSpec C)) >>= fun _ => pure ())
        simulateQ (treeSimLoggedWorld prims D)
          (free (liftComp (digestQuery ctx.self (fun T => terms.getD (C.terms.idxOf T) (fun _ => 0)) st.history) (LocalSpec C)))) := by
  simp only [treeSimHashSaltDigestDraw, prssDraw, liftComp_bind,
    free_bind, simulateQ_bind, simulateQ_pure, bind_assoc, pure_bind,
    realTerms_eq]

/-- The real boundary and the fixed compiler agree when their hidden term
blocks are already cached. Known terms and unused pairs retain their real
query order, and only the digest responses leave the boundary. -/
theorem cachedDigestCompilerLaw (E : Type) [Field E] [Algebra Bit E] (prims : Primitives) (D : C.Coalition) :
    CachedDigestCompilerLaw prims D := by
  intro ctx st cache blocks state ready covered
  have split := TreeRawSaltFlowProof.splitDigest_joint (E := E) prims D ctx st
    (((cache, state.1), state.2.flatMap (LogPiece.decode cache blocks)), blocks)
  rw [← split, realBoundary_eq]
  have termsLaw := fixedLaw_mapM prims blocks C.terms
    (realTerm prims D ctx st.label) (prepareTerm D ctx st.label) (saltFunction blocks)
    (fun T _ => prepareTerm_fixed prims D ctx st.label blocks covered T)
  have first := termsLaw cache state ready
  change 𝒟[(do
      let terms ← C.terms.mapM (realTerm prims D ctx st.label)
      let _ ← simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (pairDraws ctx (bitCodec (E := E)) st.label 2 256) (LocalSpec C)) >>= fun _ => pure ())
      simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (digestQuery ctx.self (fun T => terms.getD (C.terms.idxOf T) (fun _ => 0)) st.history) (LocalSpec C)))).run
      (decodeCompiler cache blocks state)] = _
  simp only [StateT.run_bind, compileBoundaryDigest, compilerRun_bind, map_bind]
  rw [evalDist_bind, first.1]
  simp only [← evalDist_bind, bind_map_left]
  apply evalDist_bind_congr
  intro terms hterms
  obtain ⟨hb, ready'⟩ := first.2 terms hterms
  have shape := prepareTerms_shape prims D ctx st.label state cache blocks terms hterms
  let digestSource := simulateQ (treeSimLoggedWorld prims D)
    (free (liftComp (digestQuery ctx.self
      (fun T => (terms.1.1.map (saltFunction blocks)).getD (C.terms.idxOf T) (fun _ => 0)) st.history) (LocalSpec C)))
  let digestCompiler := C.terms.mapM fun T => if ctx.self ∈ C.holders T then
    compileDigest D (terms.1.1.getD (C.terms.idxOf T) (.inr []), st.history T) else pure 0
  have tailLaw : FixedLaw prims blocks
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (pairDraws ctx (bitCodec (E := E)) st.label 2 256) (LocalSpec C)) >>= fun _ => pure ())) >>=
        fun _ => digestSource)
      (preparePairs D ctx st.label >>= fun _ => digestCompiler) id :=
    fixedLaw_bind prims blocks (preparePairs_fixed (E := E) prims D blocks ctx st.label)
      (fun _ => digestRows_fixed prims D blocks ctx st covered terms.1.1 shape)
  rw [hb] at ready' ⊢
  simpa only [StateT.run_bind, compilerRun_bind, map_bind, id_eq, digestSource, digestCompiler] using
    (tailLaw terms.2.1 terms.1.2 ready').1

/-- Every public or complete digest boundary of the fixed ceremony compiler
has the exact joint source law and preserves decoder readiness. -/
theorem boundaryCompilerSteps (prims : Primitives) (D : C.Coalition) :
    BoundaryCompilerSteps (E := E) prims D :=
  boundaryCompilerSteps_of_cached prims D (cachedDigestCompilerLaw (E := E) prims D)

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltStepsProof.cachedDigestCompilerLaw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cachedDigestCompilerLaw

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltStepsProof.boundaryCompilerSteps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundaryCompilerSteps

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltStepsProof.public_program_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms public_program_steps

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltStepsProof.compileBoundaryDigest_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compileBoundaryDigest_ready

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltStepsProof.compiler_program_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compiler_program_ready

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltStepsProof.opaque_prefetch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms opaque_prefetch

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltStepsProof.splitDigest_prefetch_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms splitDigest_prefetch_all

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltStepsProof.compileBoundaryDigest_prefetch_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compileBoundaryDigest_prefetch_all

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltStepsProof.boundaryCompilerSteps_of_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundaryCompilerSteps_of_cached

end ThresholdLeanXmssSecurity.TreeRawSaltStepsProof
