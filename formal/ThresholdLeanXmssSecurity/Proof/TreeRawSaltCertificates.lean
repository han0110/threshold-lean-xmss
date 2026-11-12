import ThresholdLeanXmssSecurity.Proof.TreeRawSaltSteps

/-!
# Salt-list certificates for the fixed ceremony compiler

The two salt lists record every hidden salt and counted digest in the decoded
writer log. A salt guess therefore gives their intersection on the same run.
Each complete digest boundary spends at most one private and one charged
query per held term. Every compiler-produced digest vector is realizable by
the abstract source with the same held-term cost. The scheduler carries each
honest party's remaining digest budget across rounds, giving the complete
private budget H and charged budget q + H. Public forwarding preserves its
ordinary digest count. The statements retain the actual compiler state, lazy block table, and hash
cache, including executions that terminate before all ceremony rounds.

-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section
namespace ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof

open TreeRawSaltCeremonyProof TreeRawSaltRepresentationProof TreeRawSaltNormalizeProof
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

variable {C : Committee}

/-- A counted digest has its salt in the public event list. -/
def Recorded (state : CompilerState C) (used : SaltLists) : Prop :=
  ∀ salt history output,
    LogPiece.literal ⟨.inl (.inl (.inr (.inl (.digest salt history)))), output⟩ ∈ state.2 →
      salt ∈ used.2

def Preserves (prims : Primitives) (I : CompilerState C → SaltLists → Prop) {α : Type} (p : CompilerM C α) : Prop :=
  ∀ state used cache blocks, I state used →
    ∀ r ∈ support (tableRun prims (p.run state) used cache blocks),
      I r.1.1.2 r.1.2

theorem tableRun_public_mono (prims : Primitives) {α : Type}
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (r) (hr : r ∈ support (tableRun prims p used cache blocks)) : used.2 ⊆ r.1.2.2 := by
  induction p using OracleComp.inductionOn generalizing used cache blocks with
  | pure value =>
    simpa [tableRun] using hr ▸ List.Subset.refl used.2
  | query_bind t k ih =>
    rw [tableRun_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hm, hr⟩ := hr
    apply List.Subset.trans (l₂ := mid.1.2.2) _ (ih _ _ _ _ hr)
    cases t with
    | inl row =>
      rcases row with ⟨b, history⟩
      rw [tableRun_private, mem_support_bind_iff] at hm
      obtain ⟨salt, _, hm⟩ := hm
      simp only [support_map, Set.mem_image] at hm
      obtain ⟨out, _, rfl⟩ := hm
      exact List.Subset.refl _
    | inr t =>
      rw [tableRun_public, support_map] at hm
      obtain ⟨out, _, rfl⟩ := hm
      exact List.subset_append_right _ _

theorem Preserves.pure (prims : Primitives) {I : CompilerState C → SaltLists → Prop} {α : Type} (a : α) :
    Preserves prims I (pure a : CompilerM C α) := by
  intro state used cache blocks h r hr
  simpa [tableRun] using hr ▸ h

theorem Preserves.bind (prims : Primitives) {I : CompilerState C → SaltLists → Prop} {α β : Type} (p : CompilerM C α)
    (k : α → CompilerM C β) (hp : Preserves prims I p) (hk : ∀ a, Preserves prims I (k a)) :
    Preserves prims I (p >>= k) := by
  intro state used cache blocks h r hr
  simp only [StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hr
  obtain ⟨mid, hm, hr⟩ := hr
  exact hk mid.1.1.1 _ _ _ _ (hp _ _ _ _ h mid hm) r hr

theorem Preserves.map (prims : Primitives) {I : CompilerState C → SaltLists → Prop} {α β : Type} (f : α → β)
    (p : CompilerM C α) (hp : Preserves prims I p) : Preserves prims I (f <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact hp.bind prims _ _ (fun a => Preserves.pure prims (f a))

theorem Preserves.mapM (prims : Primitives) {I : CompilerState C → SaltLists → Prop} {α β : Type} (xs : List α)
    (f : α → CompilerM C β) (hf : ∀ a, Preserves prims I (f a)) :
    Preserves prims I (xs.mapM f) := by
  induction xs with
  | nil => exact Preserves.pure prims []
  | cons a xs ih =>
    rw [List.mapM_cons]
    exact (hf a).bind prims _ _ (fun b => ih.map prims (List.cons b) _)

theorem Preserves.simulateQ (prims : Primitives) {I : CompilerState C → SaltLists → Prop} {ι : Type} {spec : OracleSpec ι} {α : Type}
    (impl : QueryImpl spec (CompilerM C)) (p : OracleComp spec α)
    (hi : ∀ t, Preserves prims I (impl t)) : Preserves prims I (simulateQ impl p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa using Preserves.pure prims a
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact (hi t).bind prims _ _ ih

theorem preserves_lift (prims : Primitives) {α : Type}
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α) :
    Preserves prims Recorded (StateT.lift p : CompilerM C α) := by
  intro state used cache blocks h r hr
  simp only [StateT.run_lift, bind_pure_comp, tableRun_map, support_map, Set.mem_image] at hr
  obtain ⟨out, hout, rfl⟩ := hr
  intro salt history output hm
  exact tableRun_public_mono prims p used cache blocks out hout (h _ _ _ hm)

theorem preserves_emit_draw (prims : Primitives) (b : TreeSimHashSaltBlock C) :
    Preserves prims Recorded (emit (.draw b)) := by
  intro state used cache blocks h r hr
  simp only [emit, StateT.run_modify, tableRun, simulateQ_pure, StateT.run_pure,
    mem_support_pure_iff] at hr
  subst r
  intro salt history output hm
  simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
  exact h _ _ _ hm

theorem preserves_emit_digest (prims : Primitives) (b : TreeSimHashSaltBlock C)
    (history : List Bit) (output : HashOutput) : Preserves prims Recorded (emit (.digest b history output)) := by
  intro state used cache blocks h r hr
  simp only [emit, StateT.run_modify, tableRun, simulateQ_pure, StateT.run_pure,
    mem_support_pure_iff] at hr
  subst r
  intro salt history output hm
  simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hm
  exact h _ _ _ hm


theorem publicAnswer_log (prims : Primitives) (D : C.Coalition)
    (t : (WorldSpec C).Domain) (state : CompilerState C) (used : SaltLists)
    (cache : HashCache C) (blocks : BlockCache C) r
    (hr : r ∈ support (tableRun prims ((publicAnswer D t).run state) used cache blocks)) :
    r.1.1.2.2 = state.2 := by
  rcases t with (u | prog) | (u | (q | x))
  all_goals simp only [publicAnswer] at hr
  all_goals
    try
      simp only [localQuery, StateT.run_lift, bind_pure_comp,
        tableRun_map, support_map, Set.mem_image] at hr
      obtain ⟨out, _, rfl⟩ := hr
      rfl
  · simp only [StateT.run_pure, tableRun, simulateQ_pure, StateT.run_pure,
      mem_support_pure_iff] at hr
    subst r
    rfl
  · split_ifs at hr
    · simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift,
        StateT.run_set, StateT.run_map, map_pure, bind_pure_comp,
        tableRun_map, support_map, Set.mem_image] at hr
      obtain ⟨out, _, rfl⟩ := hr
      rfl
    · simp only [localQuery, StateT.run_lift, bind_pure_comp,
        tableRun_map, support_map, Set.mem_image] at hr
      obtain ⟨out, _, rfl⟩ := hr
      rfl

theorem publicAnswer_counted (prims : Primitives) (D : C.Coalition)
    (salt : List Bit) (history : HashOutput) (state : CompilerState C) (used : SaltLists)
    (cache : HashCache C) (blocks : BlockCache C) r
    (hr : r ∈ support (tableRun prims
      ((publicAnswer D (.inl (.inl (.inr (.inl (.digest salt history)))))).run state)
      used cache blocks)) : salt ∈ r.1.2.2 := by
  simp only [publicAnswer, localQuery, StateT.run_lift, bind_pure_comp,
    tableRun_map, support_map, Set.mem_image] at hr
  obtain ⟨mid, hm, rfl⟩ := hr
  erw [tableRun_public, support_map] at hm
  obtain ⟨out, _, rfl⟩ := hm
  simp [digestSaltProjection]

theorem preserves_publicQuery (prims : Primitives) (D : C.Coalition)
    (t : (WorldSpec C).Domain) : Preserves prims Recorded (publicQuery D t) := by
  intro state used cache blocks h r hr
  simp only [publicQuery, StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hr
  obtain ⟨mid, hm, hr⟩ := hr
  simp only [emit, StateT.run_modify, StateT.run_pure,
    tableRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
  obtain ⟨_, rfl, rfl⟩ := hr
  intro salt history output hin
  simp only [List.mem_append, List.mem_singleton] at hin
  rcases hin with hin | hin
  · rw [publicAnswer_log prims D t state used cache blocks mid hm] at hin
    exact tableRun_public_mono prims _ _ _ _ mid hm (h _ _ _ hin)
  · have he := congrArg (fun p => match p with
        | LogPiece.literal entry => some entry.1
        | _ => none) hin
    simp only [Option.some.injEq] at he
    subst t
    exact publicAnswer_counted prims D salt history state used cache blocks mid hm


theorem preserves_publicDraw (prims : Primitives) (D : C.Coalition)
    (name : KeyName C) (key : HashOutput) (label : ℕ) :
    Preserves prims Recorded (publicDraw D name key label) :=
  Preserves.simulateQ prims _ _ (preserves_publicQuery prims D)

theorem preserves_prepareTerm (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label : ℕ) (T : C.Term) :
    Preserves prims Recorded (prepareTerm D ctx label T) := by
  unfold prepareTerm
  split_ifs
  · exact (preserves_publicDraw prims D _ _ _).map prims _ _
  · exact (preserves_emit_draw prims _).bind prims _ _
      (fun _ => Preserves.pure prims _)
  · exact Preserves.pure prims _

theorem preserves_preparePairs (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label : ℕ) : Preserves prims Recorded (preparePairs D ctx label) := by
  unfold preparePairs
  refine Preserves.bind prims (I := Recorded) _ _ ?_ ?_
  · apply Preserves.mapM prims (I := Recorded)
    intro j
    split_ifs
    · exact Preserves.pure prims _
    · exact preserves_publicDraw prims D _ _ _
  · intro _
    exact Preserves.pure prims _

theorem preserves_compileDigest (prims : Primitives) (D : C.Coalition) (row : Row C) :
    Preserves prims Recorded (compileDigest D row) := by
  rcases row with ⟨b | salt, history⟩
  · exact (preserves_lift prims _).bind prims _ _ (fun output =>
      (preserves_emit_digest prims b history output).bind prims _ _
        (fun _ => Preserves.pure prims _))
  · exact Preserves.simulateQ prims _ _ (preserves_publicQuery prims D)

theorem preserves_compileBoundaryDigest (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (st : RunState C) :
    Preserves prims Recorded (compileBoundaryDigest D ctx st) := by
  unfold compileBoundaryDigest
  refine Preserves.bind prims (I := Recorded) _ _ ?_ ?_
  · exact Preserves.mapM prims _ _ (preserves_prepareTerm prims D ctx st.label)
  · intro terms
    apply (preserves_preparePairs prims D ctx st.label).bind prims
    intro _
    apply Preserves.mapM prims (I := Recorded)
    intro T
    split_ifs
    · exact preserves_compileDigest prims D _
    · exact Preserves.pure prims _

theorem preserves_boundaryCompiler (prims : Primitives) (D : C.Coalition)
    (t : (TreeRawSaltFlowProof.BoundarySpec D).Domain) :
    Preserves prims Recorded (boundaryCompiler D t) := by
  cases t with
  | inl row => exact preserves_compileBoundaryDigest prims D row.1 row.2
  | inr t => exact preserves_publicQuery prims D t.1

/-- Private log pieces contain only honest entries, so counted entries have
an actual literal occurrence in the symbolic writer. -/
theorem counted_mem_decode (cache : HashCache C) (blocks : BlockCache C)
    (pieces : List (LogPiece C)) (salt : List Bit) (history : HashOutput) (output : HashOutput)
    (h : (⟨.inl (.inl (.inr (.inl (.digest salt history)))), output⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈
        pieces.flatMap (LogPiece.decode cache blocks)) :
    LogPiece.literal ⟨.inl (.inl (.inr (.inl (.digest salt history)))), output⟩ ∈ pieces := by
  obtain ⟨piece, hp, he⟩ := List.mem_flatMap.mp h
  cases piece with
  | literal entry =>
    simp only [LogPiece.decode, List.mem_singleton] at he
    exact he ▸ hp
  | draw b =>
    simp only [LogPiece.decode, treeSimHiddenLog, List.mem_ofFn] at he
    obtain ⟨g, he⟩ := he
    cases he
  | digest b history digest =>
    simp [LogPiece.decode, digestLog, digestEntries] at he

/-- Literal entries never expose a hidden salt position. -/
def SafeLiterals (D : C.Coalition) (state : CompilerState C) (_used : SaltLists) : Prop :=
  ∀ entry, LogPiece.literal entry ∈ state.2 → TreeRawSaltFlowProof.NoSaltRead D entry.1

theorem safe_lift (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α) :
    Preserves prims (SafeLiterals D) (StateT.lift p : CompilerM C α) := by
  intro state used cache blocks h r hr
  simp only [StateT.run_lift, bind_pure_comp, tableRun_map, support_map, Set.mem_image] at hr
  obtain ⟨out, _, rfl⟩ := hr
  exact h

theorem safe_emit (prims : Primitives) (D : C.Coalition) (piece : LogPiece C)
    (safe : ∀ entry, piece = .literal entry → TreeRawSaltFlowProof.NoSaltRead D entry.1) :
    Preserves prims (SafeLiterals D) (emit piece) := by
  intro state used cache blocks h r hr
  simp only [emit, StateT.run_modify, tableRun, simulateQ_pure, StateT.run_pure,
    mem_support_pure_iff] at hr
  subst r
  intro entry hm
  rcases List.mem_append.mp hm with hm | hm
  · exact h entry hm
  · exact safe entry (List.mem_singleton.mp hm).symm

theorem safe_publicQuery (prims : Primitives) (D : C.Coalition)
    (t : (WorldSpec C).Domain) (safe : TreeRawSaltFlowProof.NoSaltRead D t) :
    Preserves prims (SafeLiterals D) (publicQuery D t) := by
  intro state used cache blocks h r hr
  simp only [publicQuery, StateT.run_bind, tableRun_bind, mem_support_bind_iff] at hr
  obtain ⟨mid, hm, hr⟩ := hr
  simp only [emit, StateT.run_modify, StateT.run_pure,
    tableRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
  obtain ⟨_, rfl, rfl⟩ := hr
  intro entry hin
  rcases List.mem_append.mp hin with hin | hin
  · rw [publicAnswer_log prims D t state used cache blocks mid hm] at hin
    exact h entry hin
  · have he := LogPiece.literal.inj (List.mem_singleton.mp hin)
    subst entry
    exact safe

theorem safe_publicProgram (prims : Primitives) (D : C.Coalition) {α : Type}
    (p : OracleComp (WorldSpec C) α)
    (safe : IsQueryBoundP p (fun t => ¬TreeRawSaltFlowProof.NoSaltRead D t) 0) :
    Preserves prims (SafeLiterals D) (simulateQ (publicQuery D) p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa using Preserves.pure prims (I := SafeLiterals D) a
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at safe
    have ht : TreeRawSaltFlowProof.NoSaltRead D t := by simpa using safe.1
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact (safe_publicQuery prims D t ht).bind prims _ _
      (fun a => ih a (by simpa [ht] using safe.2 a))

theorem safe_publicDraw (prims : Primitives) (D : C.Coalition)
    (name : KeyName C) (key : HashOutput) (label : ℕ)
    (safe : Hidden D name → ∀ g, TreeRawSaltFlowProof.saltAt ((name, key), label, 2, g) = none) :
    Preserves prims (SafeLiterals D) (publicDraw D name key label) :=
  safe_publicProgram prims D _ (TreeRawSaltFlowProof.prg_noSalt D name key label 2 256 safe)

theorem safe_prepareTerm (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label : ℕ) (T : C.Term) :
    Preserves prims (SafeLiterals D) (prepareTerm D ctx label T) := by
  unfold prepareTerm
  split_ifs with held known
  · exact (safe_publicDraw prims D (.term T) (ctx.prss.term T) label (fun hidden => False.elim (hidden known))).map prims _ _
  · exact (safe_emit prims D (.draw _) (by intro entry he; cases he)).bind prims _ _
      (fun _ => Preserves.pure prims _)
  · exact Preserves.pure prims _

theorem safe_preparePairs (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (label : ℕ) : Preserves prims (SafeLiterals D) (preparePairs D ctx label) := by
  unfold preparePairs
  refine Preserves.bind prims (I := SafeLiterals D) _ _ ?_ ?_
  · apply Preserves.mapM prims (I := SafeLiterals D)
    intro j
    split_ifs
    · exact Preserves.pure prims _
    · exact safe_publicDraw prims D _ _ _
        (fun _ g => TreeRawSaltFlowProof.saltAt_pair _ _ _ _ g)
  · intro _
    exact Preserves.pure prims _

theorem safe_compileDigest (prims : Primitives) (D : C.Coalition) (row : Row C) :
    Preserves prims (SafeLiterals D) (compileDigest D row) := by
  rcases row with ⟨b | salt, history⟩
  · exact (safe_lift prims D _).bind prims _ _ (fun output =>
      (safe_emit prims D (.digest b history output) (by intro entry he; cases he)).bind prims _ _
        (fun _ => Preserves.pure prims _))
  · apply safe_publicProgram
    apply TreeRawSaltFlowProof.ro_noSalt
    unfold oneDigestQuery
    exact isQueryBoundP_bind (TreeRawSaltFlowProof.hash_noSalt_ro D _)
      (fun _ _ => TreeRawSaltFlowProof.hash_noSalt_ro D _)

theorem safe_compileBoundaryDigest (prims : Primitives) (D : C.Coalition)
    (ctx : Context C) (st : RunState C) :
    Preserves prims (SafeLiterals D) (compileBoundaryDigest D ctx st) := by
  unfold compileBoundaryDigest
  refine Preserves.bind prims (I := SafeLiterals D) _ _ ?_ ?_
  · exact Preserves.mapM prims _ _ (safe_prepareTerm prims D ctx st.label)
  · intro terms
    apply (safe_preparePairs prims D ctx st.label).bind prims
    intro _
    apply Preserves.mapM prims (I := SafeLiterals D)
    intro T
    split_ifs
    · exact safe_compileDigest prims D _
    · exact Preserves.pure prims _

theorem safe_boundaryCompiler (prims : Primitives) (D : C.Coalition)
    (t : (TreeRawSaltFlowProof.BoundarySpec D).Domain) :
    Preserves prims (SafeLiterals D) (boundaryCompiler D t) := by
  cases t with
  | inl row => exact safe_compileBoundaryDigest prims D row.1 row.2
  | inr t => exact safe_publicQuery prims D t.1 t.2

theorem hiddenLog_member (a b : TreeSimHashSaltBlock C) (values : Fin 256 → Bit)
    (g : Fin 256) (value : Bit)
    (h : (⟨.inr (.inr (.inr (.term b.1, b.2.1, b.2.2, 2, g.val))), value⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈
        treeSimHiddenLog (treeSimHashSaltAddress a) values) : a = b ∧ values g = value := by
  simp only [treeSimHiddenLog, List.mem_ofFn] at h
  obtain ⟨j, he⟩ := h
  have hx := congrArg Sigma.fst he
  rcases a with ⟨A, ak, al⟩
  rcases b with ⟨B, bk, bl⟩
  simp only [treeSimHashSaltAddress, Sum.inr.injEq, Prod.mk.injEq, KeyName.term.injEq] at hx
  obtain ⟨rfl, rfl, rfl, _, hj⟩ := hx
  have hjg : j = g := Fin.ext hj
  subst j
  exact ⟨rfl, by simpa only [treeSimHashSaltAddress, Sigma.mk.inj_iff, heq_eq_eq, true_and] using he⟩

/-- A decoded hidden salt bit comes from the one block at its PRSS address. -/
theorem hidden_mem_decode (D : C.Coalition) (state : CompilerState C) (used : SaltLists)
    (cache : HashCache C) (blocks : BlockCache C) (safe : SafeLiterals D state used)
    (ready : Ready cache blocks state) (b : TreeSimHashSaltBlock C)
    (hidden : ¬KnownTo D.1 b.1) (g : Fin 256) (value : Bit)
    (h : (⟨.inr (.inr (.inr (.term b.1, b.2.1, b.2.2, 2, g.val))), value⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈
        state.2.flatMap (LogPiece.decode cache blocks)) :
    (∃ values, blocks b = some values) ∧ value = blockValues blocks b g := by
  obtain ⟨piece, hp, he⟩ := List.mem_flatMap.mp h
  cases piece with
  | literal entry =>
    simp only [LogPiece.decode, List.mem_singleton] at he
    subst entry
    have hn := safe _ hp hidden
    change TreeRawSaltFlowProof.saltAt (treeSimHashSaltAddress b g) = none at hn
    have hy := TreeRawSaltFlowProof.saltAt_address b g
    exact False.elim (by rw [hn] at hy; cases hy)
  | draw a =>
    obtain ⟨hab, hv⟩ := hiddenLog_member a b (blockValues blocks a) g value he
    subst a
    exact ⟨ready _ hp, hv.symm⟩
  | digest a history output =>
    simp [LogPiece.decode, digestLog, digestEntries] at he

/-- All 256 entries of a hidden salt reconstruct the actual cached vector. -/
theorem hiddenSalt_cached (D : C.Coalition) (state : CompilerState C) (used : SaltLists)
    (cache : HashCache C) (blocks : BlockCache C) (safe : SafeLiterals D state used)
    (ready : Ready cache blocks state) (salt : List Bit)
    (hs : TreeSimHiddenSalt D (state.2.flatMap (LogPiece.decode cache blocks)) salt) :
    ∃ b values, blocks b = some values ∧ salt = List.ofFn values := by
  obtain ⟨hlen, T, key, label, hidden, hbits⟩ := hs
  let b : TreeSimHashSaltBlock C := (T, key, label)
  have bits := fun g => hidden_mem_decode D state used cache blocks safe ready b hidden g _ (hbits g)
  obtain ⟨values, hv⟩ := (bits ⟨0, by decide⟩).1
  refine ⟨b, values, hv, ?_⟩
  apply List.ext_getElem
  · simpa using hlen
  · intro k hk hk'
    have hkn : k < 256 := by omega
    have he := (bits ⟨k, hkn⟩).2
    rw [List.getElem_ofFn]
    simpa only [List.getD, List.getElem?_eq_getElem hk, Option.getD_some, blockValues, hv] using he

/-- Every occupied private block was consumed by a private digest call. -/
def PrivateRecorded (blocks : BlockCache C) (used : SaltLists) : Prop :=
  ∀ b values, blocks b = some values → List.ofFn values ∈ used.1

theorem tableRun_private_recorded (prims : Primitives) {α : Type}
    (p : OracleComp (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C) α)
    (used : SaltLists) (cache : HashCache C) (blocks : BlockCache C)
    (h : PrivateRecorded blocks used) (r)
    (hr : r ∈ support (tableRun prims p used cache blocks)) :
    PrivateRecorded r.2.2 r.1.2 := by
  induction p using OracleComp.inductionOn generalizing used cache blocks with
  | pure value =>
    simp only [tableRun, simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact h
  | query_bind t k ih =>
    rw [tableRun_bind, mem_support_bind_iff] at hr
    obtain ⟨mid, hm, hr⟩ := hr
    apply ih _ _ _ _ _ hr
    cases t with
    | inl row =>
      rcases row with ⟨b, history⟩
      rw [tableRun_private, mem_support_bind_iff] at hm
      obtain ⟨salt, hs, hm⟩ := hm
      simp only [support_map, Set.mem_image] at hm
      obtain ⟨out, _, rfl⟩ := hm
      intro a values hv
      rw [block_read_update b blocks salt hs] at hv
      by_cases hab : a = b
      · subst a
        rw [QueryCache.cacheQuery_self] at hv
        cases Option.some.inj hv
        exact List.mem_append_right _ (List.mem_singleton_self _)
      · rw [QueryCache.cacheQuery_of_ne _ _ hab] at hv
        exact List.mem_append_left _ (h a values hv)
    | inr t =>
      rw [tableRun_public, support_map] at hm
      obtain ⟨out, _, rfl⟩ := hm
      exact h

/-- A compiler computation's predicate budget holds at every auxiliary state. -/
def CompilerBound (P : (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C).Domain → Prop)
    {α : Type} (p : CompilerM C α) (n : ℕ) : Prop := ∀ state, IsQueryBoundP (p.run state) P n

theorem CompilerBound.pure (P) {α : Type} (a : α) (n : ℕ) :
    CompilerBound P (pure a : CompilerM C α) n := by
  intro state
  exact isQueryBoundP_pure _ _ _

theorem CompilerBound.bind {P} {α β : Type} {p : CompilerM C α} {k : α → CompilerM C β}
    {n m : ℕ} (hp : CompilerBound P p n) (hk : ∀ a, CompilerBound P (k a) m) :
    CompilerBound P (p >>= k) (n + m) := by
  intro state
  simp only [StateT.run_bind]
  exact isQueryBoundP_bind (hp state) (fun r _ => hk r.1 r.2)

theorem CompilerBound.zero_bind {P} {α β : Type} {p : CompilerM C α} {k : α → CompilerM C β}
    {n : ℕ} (hp : CompilerBound P p 0) (hk : ∀ a, CompilerBound P (k a) n) :
    CompilerBound P (p >>= k) n := by
  simpa only [Nat.zero_add] using hp.bind hk

theorem CompilerBound.map {P} {α β : Type} (f : α → β) {p : CompilerM C α}
    {n : ℕ} (hp : CompilerBound P p n) : CompilerBound P (f <$> p) n := by
  intro state
  simpa only [StateT.run_map, isQueryBoundP_map_iff] using hp state

theorem CompilerBound.mapM {P} {α β : Type} (xs : List α) (f : α → CompilerM C β)
    (cost : α → ℕ) (hf : ∀ a, CompilerBound P (f a) (cost a)) :
    CompilerBound P (xs.mapM f) (xs.map cost).sum := by
  induction xs with
  | nil => exact CompilerBound.pure P [] 0
  | cons a xs ih =>
    simpa only [List.mapM_cons, List.map_cons, List.sum_cons, bind_pure_comp] using
      (hf a).bind (fun b => ih.map (List.cons b))

theorem emit_bound (P) (piece : LogPiece C) : CompilerBound P (emit piece) 0 := by
  intro state
  simp only [emit, StateT.run_modify]
  exact isQueryBoundP_pure _ _ _

theorem table_prob_private {α : Type} (p : ProbComp α) :
    IsQueryBoundP (liftComp p (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C))
      TreeSimHashSaltPrivate 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, liftComp_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (.inr (.inl t))) >>= fun u =>
      liftComp (k u) (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C)) TreeSimHashSaltPrivate 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [TreeSimHashSaltPrivate]), fun u => by
      simpa only [TreeSimHashSaltPrivate, if_false, Nat.sub_zero] using ih u⟩

theorem publicAnswer_private (D : C.Coalition) (t : (WorldSpec C).Domain) :
    CompilerBound TreeSimHashSaltPrivate (publicAnswer D t) 0 := by
  intro state
  rcases t with (u | prog) | (u | (q | x))
  all_goals simp only [publicAnswer]
  all_goals try
    simp only [localQuery, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
      isQueryBoundP_query_iff, TreeSimHashSaltPrivate, false_implies]
  · exact isQueryBoundP_pure _ _ _
  · split_ifs
    · simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift,
        StateT.run_set, StateT.run_map, map_pure, bind_pure_comp, isQueryBoundP_map_iff]
      exact table_prob_private _
    · simp only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
        isQueryBoundP_query_iff, TreeSimHashSaltPrivate, false_implies]

theorem publicQuery_private (D : C.Coalition) (t : (WorldSpec C).Domain) :
    CompilerBound TreeSimHashSaltPrivate (publicQuery D t) 0 := by
  exact (publicAnswer_private D t).bind
    (fun output => (emit_bound _ (.literal ⟨t, output⟩)).bind (fun _ => CompilerBound.pure _ output 0))

theorem publicProgram_private (D : C.Coalition) {α : Type} (p : OracleComp (WorldSpec C) α) :
    CompilerBound TreeSimHashSaltPrivate (simulateQ (publicQuery D) p) 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simpa using CompilerBound.pure TreeSimHashSaltPrivate a 0
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact (publicQuery_private D t).bind ih

theorem prepareTerm_private (D : C.Coalition) (ctx : Context C) (label : ℕ) (T : C.Term) :
    CompilerBound TreeSimHashSaltPrivate (prepareTerm D ctx label T) 0 := by
  unfold prepareTerm
  split_ifs
  · exact (publicProgram_private D _).map _
  · exact (emit_bound _ _).bind (fun _ => CompilerBound.pure _ _ 0)
  · exact CompilerBound.pure _ _ 0

theorem preparePairs_private (D : C.Coalition) (ctx : Context C) (label : ℕ) :
    CompilerBound TreeSimHashSaltPrivate (preparePairs D ctx label) 0 := by
  unfold preparePairs
  have h : CompilerBound TreeSimHashSaltPrivate
      (C.parties.mapM fun j => if h : j = ctx.self then pure (fun _ : ℕ => (0 : Bit))
        else publicDraw D (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) label) 0 := by
    have h := CompilerBound.mapM C.parties
      (fun j => if h : j = ctx.self then pure (fun _ : ℕ => (0 : Bit))
        else publicDraw D (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) label)
      (fun _ => 0) (P := TreeSimHashSaltPrivate) (fun j => ?_)
    · simpa using h
    · split_ifs
      · exact CompilerBound.pure _ _ 0
      · exact publicProgram_private D _
  exact h.bind (fun _ => CompilerBound.pure _ () 0)

theorem compileDigest_private (D : C.Coalition) (row : Row C) :
    CompilerBound TreeSimHashSaltPrivate (compileDigest D row) 1 := by
  rcases row with ⟨b | salt, history⟩
  · apply CompilerBound.bind (n := 1) (m := 0)
    · intro state
      simp only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
      exact TreeRawSaltNormalizeProof.rowProgram_private _
    · intro output
      exact (emit_bound _ _).bind (fun _ => CompilerBound.pure _ output 0)
  · intro state
    exact (publicProgram_private D _ state).mono (by omega)

/-- Each complete digest boundary spends at most one private query per
held term, including every possible answer of its public and private calls. -/
theorem compileBoundaryDigest_private (D : C.Coalition) (ctx : Context C) (st : RunState C) :
    CompilerBound TreeSimHashSaltPrivate (compileBoundaryDigest D ctx st)
      (treeSimHashHeld ctx.self) := by
  have hterms : CompilerBound TreeSimHashSaltPrivate
      (C.terms.mapM (prepareTerm D ctx st.label)) 0 := by
    simpa using CompilerBound.mapM C.terms _ (fun _ => 0) (prepareTerm_private D ctx st.label)
  unfold compileBoundaryDigest
  apply hterms.zero_bind
  intro terms
  apply (preparePairs_private D ctx st.label).zero_bind
  intro _
  rw [show treeSimHashHeld ctx.self =
    (C.terms.map fun T => if ctx.self ∈ C.holders T then 1 else 0).sum by
      simp [treeSimHashHeld, Committee.terms, Finset.sum_map_toList]]
  apply CompilerBound.mapM
  intro T
  split_ifs
  · exact compileDigest_private D _
  · exact CompilerBound.pure _ _ 0

/-- Public forwarding charges precisely its ordinary digest calls. -/
def PublicDigest : (WorldSpec C).Domain → Prop
  | .inl (.inl t) | .inr t => DigestQuery t
  | .inl (.inr _) => False

theorem table_prob_charged {α : Type} (p : ProbComp α) :
    IsQueryBoundP (liftComp p (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C))
      treeSimHashSaltTableCharged 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    rw [liftComp_bind, liftComp_query]
    simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (.inr (.inl t))) >>= fun u =>
      liftComp (k u) (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C)) treeSimHashSaltTableCharged 0
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [treeSimHashSaltTableCharged, DigestQuery, digestSaltProjection]), fun u => by
      simpa only [treeSimHashSaltTableCharged, DigestQuery, digestSaltProjection,
        Option.isSome_none, Bool.false_eq_true, if_false, Nat.sub_zero] using ih u⟩

theorem localQuery_charged (t : (LocalSpec C).Domain) :
    CompilerBound treeSimHashSaltTableCharged (localQuery t) (if DigestQuery t then 1 else 0) := by
  intro state
  simp only [localQuery, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff,
    isQueryBoundP_query_iff, treeSimHashSaltTableCharged]
  split_ifs with ht <;> simp [ht]

theorem publicAnswer_charged (D : C.Coalition) (t : (WorldSpec C).Domain) :
    CompilerBound treeSimHashSaltTableCharged (publicAnswer D t) (if PublicDigest t then 1 else 0) := by
  rcases t with (u | prog) | (u | (q | x))
  · exact localQuery_charged u
  · exact CompilerBound.pure treeSimHashSaltTableCharged false 0
  · exact localQuery_charged (.inl u)
  · exact localQuery_charged (.inr (.inl q))
  · intro state
    simp only [publicAnswer, PublicDigest, DigestQuery, digestSaltProjection,
      Option.isSome_none, Bool.false_eq_true, if_false]
    split_ifs
    · simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift,
        StateT.run_set, StateT.run_map, map_pure, bind_pure_comp, isQueryBoundP_map_iff]
      exact table_prob_charged _
    · simpa only [DigestQuery, digestSaltProjection, Option.isSome_none, Bool.false_eq_true, if_false]
        using localQuery_charged (.inr (.inr x)) state

theorem publicQuery_charged (D : C.Coalition) (t : (WorldSpec C).Domain) :
    CompilerBound treeSimHashSaltTableCharged (publicQuery D t) (if PublicDigest t then 1 else 0) := by
  simpa only [Nat.add_zero, publicQuery] using (publicAnswer_charged D t).bind
    (fun output => (emit_bound _ (.literal ⟨t, output⟩)).bind (fun _ => CompilerBound.pure _ output 0))

theorem publicProgram_charged (D : C.Coalition) {α : Type} (p : OracleComp (WorldSpec C) α)
    (n : ℕ) (h : IsQueryBoundP p PublicDigest n) :
    CompilerBound treeSimHashSaltTableCharged (simulateQ (publicQuery D) p) n :=
  h.simulateQ_run_StateT_of_step (publicQuery_charged D)

theorem free_ro_digest {α : Type} (p : OracleComp (RoSpec C) α) (n : ℕ)
    (h : IsQueryBoundP p (fun t => DigestQuery (C := C) (.inr t)) n) :
    IsQueryBoundP (free (liftComp p (LocalSpec C))) PublicDigest n := by
  induction p using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [liftComp_bind, free_bind]
    change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr (.inr t))) >>= fun u =>
      free (liftComp (k u) (LocalSpec C))) PublicDigest n
    rw [isQueryBoundP_query_bind_iff]
    exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

theorem publicDraw_charged (D : C.Coalition) (name : KeyName C) (key : HashOutput) (label : ℕ) :
    CompilerBound treeSimHashSaltTableCharged (publicDraw D name key label) 0 :=
  publicProgram_charged D _ 0 (free_ro_digest _ 0 (treeSimHash_prg_digest name key label 2 256))

theorem prepareTerm_charged (D : C.Coalition) (ctx : Context C) (label : ℕ) (T : C.Term) :
    CompilerBound treeSimHashSaltTableCharged (prepareTerm D ctx label T) 0 := by
  unfold prepareTerm
  split_ifs
  · exact (publicDraw_charged D _ _ _).map _
  · exact (emit_bound _ _).bind (fun _ => CompilerBound.pure _ _ 0)
  · exact CompilerBound.pure _ _ 0

theorem preparePairs_charged (D : C.Coalition) (ctx : Context C) (label : ℕ) :
    CompilerBound treeSimHashSaltTableCharged (preparePairs D ctx label) 0 := by
  unfold preparePairs
  have h : CompilerBound treeSimHashSaltTableCharged
      (C.parties.mapM fun j => if h : j = ctx.self then pure (fun _ : ℕ => (0 : Bit))
        else publicDraw D (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) label) 0 := by
    have h := CompilerBound.mapM C.parties
      (fun j => if h : j = ctx.self then pure (fun _ : ℕ => (0 : Bit))
        else publicDraw D (.pair (C.pairOf ctx.self j (Ne.symm h))) (ctx.prss.pair j) label)
      (fun _ => 0) (P := treeSimHashSaltTableCharged) (fun j => ?_)
    · simpa using h
    · split_ifs
      · exact CompilerBound.pure _ _ 0
      · exact publicDraw_charged D _ _ _
  exact h.bind (fun _ => CompilerBound.pure _ () 0)

theorem compileDigest_charged (D : C.Coalition) (row : Row C) :
    CompilerBound treeSimHashSaltTableCharged (compileDigest D row) 1 := by
  rcases row with ⟨b | salt, history⟩
  · apply CompilerBound.bind (n := 1) (m := 0)
    · intro state
      simp only [StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff]
      exact TreeRawSaltNormalizeProof.rowProgram_charged _
    · intro output
      exact (emit_bound _ _).bind (fun _ => CompilerBound.pure _ output 0)
  · apply publicProgram_charged
    apply free_ro_digest
    unfold oneDigestQuery
    refine isQueryBoundP_bind (n := 0) (m := 1) ?_ (fun _ _ => ?_)
    · exact treeSimHash_hash_no_digest _ (by simp [DigestQuery, digestSaltProjection])
    · change IsQueryBoundP (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inl (.digest salt _))))
        (fun t => DigestQuery (C := C) (.inr t)) 1
      simp only [isQueryBoundP_query_iff]
      intro _
      omega

/-- Known and hidden salts together spend one charged call per held term;
the pair and preparation PRGs add no charged calls. -/
theorem compileBoundaryDigest_charged (D : C.Coalition) (ctx : Context C) (st : RunState C) :
    CompilerBound treeSimHashSaltTableCharged (compileBoundaryDigest D ctx st)
      (treeSimHashHeld ctx.self) := by
  have hterms : CompilerBound treeSimHashSaltTableCharged
      (C.terms.mapM (prepareTerm D ctx st.label)) 0 := by
    simpa using CompilerBound.mapM C.terms _ (fun _ => 0) (prepareTerm_charged D ctx st.label)
  unfold compileBoundaryDigest
  apply hterms.zero_bind
  intro terms
  apply (preparePairs_charged D ctx st.label).zero_bind
  intro _
  rw [show treeSimHashHeld ctx.self =
    (C.terms.map fun T => if ctx.self ∈ C.holders T then 1 else 0).sum by
      simp [treeSimHashHeld, Committee.terms, Finset.sum_map_toList]]
  apply CompilerBound.mapM
  intro T
  split_ifs
  · exact compileDigest_charged D _
  · exact CompilerBound.pure _ _ 0

/-- Reflection at a forwarded source query only needs the source's
all-answer continuation bounds, regardless of auxiliary compiler state. -/
theorem public_budget_reflect (D : C.Coalition)
    (P : (WorldSpec C).Domain → Prop)
    (Q : (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C).Domain → Prop)
    {α : Type} (t : (WorldSpec C).Domain)
    (source : (WorldSpec C).Range t → OracleComp (WorldSpec C) α)
    (target : (WorldSpec C).Range t → CompilerM C α)
    (step : CompilerBound Q (publicQuery D t) (if P t then 1 else 0))
    (next : ∀ a n, IsQueryBoundP (source a) P n → CompilerBound Q (target a) n)
    (n : ℕ) (h : IsQueryBoundP
      (OracleComp.lift (OracleSpec.query t) >>= source) P n) :
    CompilerBound Q (publicQuery D t >>= target) n := by
  rw [isQueryBoundP_query_bind_iff] at h
  have hc := step.bind (fun a => next a _ (h.2 a))
  intro state
  apply (hc state).mono
  by_cases ht : P t
  · have hn := h.1.resolve_left (fun hh => hh ht)
    simp only [if_pos ht]
    omega
  · simp only [if_neg ht, Nat.zero_add, Nat.le_refl]

variable {E : Type} [Field E] [Algebra Bit E]

/-- Local all-answer budget reflection reduces to residual source bounds
at the concrete compiler's reachable digest vectors. -/
theorem boundary_budget_reflect
    (D : C.Coalition)
    (P : (WorldSpec C).Domain → Prop)
    (Q : (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C).Domain → Prop)
    {α : Type} (ctx : Context C) (st : RunState C)
    (source : List HashOutput → OracleComp (WorldSpec C) α)
    (target : List HashOutput → CompilerM C α)
    (step : CompilerBound Q (compileBoundaryDigest D ctx st) (treeSimHashHeld ctx.self))
    (next : ∀ a n, IsQueryBoundP (source a) P n → CompilerBound Q (target a) n)
    (n : ℕ)
    (residual : treeSimHashHeld ctx.self ≤ n ∧
      ∀ state r, r ∈ support ((compileBoundaryDigest D ctx st).run state) →
        IsQueryBoundP (source r.1) P (n - treeSimHashHeld ctx.self)) :
    CompilerBound Q (compileBoundaryDigest D ctx st >>= target) n := by
  intro state
  simp only [StateT.run_bind]
  have h := isQueryBoundP_bind (step state)
    (fun r hr => next r.1 _ (residual.2 state r hr) r.2)
  exact h.mono (by omega)

omit [Field E] [Algebra Bit E] in
/-- A continuation-aware boundary law transports bounds from the exact
expanded source. It needs feasibility only for compiler-produced answers,
not for arbitrary lists returned by the abstract boundary oracle. -/
theorem compiler_program_budget_of_boundary
    (D : C.Coalition)
    (P : (WorldSpec C).Domain → Prop)
    (Q : (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C).Domain → Prop)
    (forward : ∀ t, CompilerBound Q (publicQuery D t) (if P t then 1 else 0))
    (boundary : ∀ {α : Type} (ctx : Context C) (st : RunState C)
      (source : List HashOutput → OracleComp (WorldSpec C) α)
      (target : List HashOutput → CompilerM C α),
      (∀ a n, IsQueryBoundP (source a) P n → CompilerBound Q (target a) n) →
      ∀ n, IsQueryBoundP
        (TreeRawSaltFlowProof.boundarySource (E := E) D (.inl (ctx, st)) >>= source) P n →
      CompilerBound Q (compileBoundaryDigest D ctx st >>= target) n)
    {α : Type} (p : OracleComp (TreeRawSaltFlowProof.BoundarySpec D) α) (n : ℕ)
    (bound : IsQueryBoundP (simulateQ (TreeRawSaltFlowProof.boundarySource (E := E) D) p) P n) :
    CompilerBound Q (simulateQ (boundaryCompiler D) p) n := by
  induction p using OracleComp.inductionOn generalizing n with
  | pure a => simpa using CompilerBound.pure Q a n
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query] at bound ⊢
    cases t with
    | inl row =>
      exact boundary row.1 row.2 _ _ (fun a m h => ih a m h) n bound
    | inr t =>
      exact public_budget_reflect D P Q t.1 _ _ (forward t.1)
        (fun a m h => ih a m h) n bound


/-- A realizable answer consumes at least this many predicate queries before
any continuation, measured by its structural all-answer budget. -/
structure ResidualCost {ι α : Type} {S : OracleSpec ι} (P : ι → Prop)
    (p : OracleComp S α) (a : α) (spent : ℕ) : Prop where
  residual : ∀ {β : Type} (k : α → OracleComp S β) (n : ℕ),
    IsQueryBoundP (p >>= k) P n → spent ≤ n ∧ IsQueryBoundP (k a) P (n - spent)

namespace ResidualCost
variable {ι α β : Type} {S : OracleSpec ι} {P : ι → Prop}

theorem pure (a : α) : ResidualCost P (pure a : OracleComp S α) a 0 := by
  constructor
  intro β k n h
  exact ⟨Nat.zero_le _, by simpa using h⟩

theorem bind {p : OracleComp S α} {f : α → OracleComp S β}
    {a : α} {b : β} {m n : ℕ}
    (hp : ResidualCost P p a m) (hf : ResidualCost P (f a) b n) :
    ResidualCost P (p >>= f) b (m + n) := by
  constructor
  intro γ k budget h
  rw [bind_assoc] at h
  obtain ⟨hm, tail⟩ := hp.residual _ _ h
  obtain ⟨hn, tail⟩ := hf.residual _ _ tail
  exact ⟨by omega, by simpa only [Nat.sub_sub] using tail⟩

theorem query (t : S.Domain) (a : S.Range t) :
    ResidualCost P (OracleComp.lift (OracleSpec.query t)) a (if P t then 1 else 0) := by
  constructor
  intro β k n h
  rw [isQueryBoundP_query_bind_iff] at h
  constructor
  · split_ifs with ht
    · exact h.1.resolve_left (fun hn => hn ht)
    · exact Nat.zero_le _
  · by_cases ht : P t <;> simpa only [ht, if_true, if_false, Nat.sub_zero] using h.2 a

/-- A supported prefix can always be discarded without increasing the bound. -/
theorem of_support {p : OracleComp S α} {a : α} (ha : a ∈ support p) :
    ResidualCost P p a 0 := by
  induction p using OracleComp.inductionOn with
  | pure x =>
    have eq : a = x := by simpa using ha
    subst a
    exact pure x
  | query_bind t f ih =>
    obtain ⟨u, _, hu⟩ := (mem_support_bind_iff _ _ _).mp ha
    constructor
    intro β k n h
    rw [bind_assoc, isQueryBoundP_query_bind_iff] at h
    have tail := (ih u hu).residual k _ (h.2 u)
    exact ⟨Nat.zero_le _, tail.2.mono (by split_ifs <;> omega)⟩

end ResidualCost

/-- Abstract oracle answers need not be consistent with a hash cache. -/
theorem support_nonempty {ι α : Type} {S : OracleSpec ι}
    [∀ t, Inhabited (S.Range t)] (p : OracleComp S α) : (support p).Nonempty := by
  induction p using OracleComp.inductionOn with
  | pure a => exact ⟨a, by simp⟩
  | query_bind t k ih =>
    obtain ⟨a, ha⟩ := ih default
    exact ⟨a, (mem_support_bind_iff _ _ _).mpr ⟨default, mem_support_query _ _, ha⟩⟩

/-- Stateful traversal preserves the entrywise result shape. -/
theorem compiler_mapM_shape {α β : Type} (xs : List α) (f : α → CompilerM C β)
    (R : α → β → Prop)
    (step : ∀ a state r, r ∈ support ((f a).run state) → R a r.1)
    (state : CompilerState C) (r)
    (hr : r ∈ support ((xs.mapM f).run state)) : List.Forall₂ R xs r.1 := by
  induction xs generalizing state r with
  | nil =>
    have eq : r = ([], state) := by simpa using hr
    subst r
    exact List.Forall₂.nil
  | cons a xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨head, hh, tail, ht, hr⟩ := hr
    simp only [StateT.run_pure, mem_support_pure_iff] at hr
    subst r
    exact .cons (step a state head hh) (ih head.2 tail ht)

def DigestShape (i : C.Party) : List C.Term → List HashOutput → Prop :=
  List.Forall₂ (fun T value => i ∉ C.holders T → value = 0)

theorem compileBoundaryDigest_shape (D : C.Coalition) (ctx : Context C) (st : RunState C)
    (state : CompilerState C) (r)
    (hr : r ∈ support ((compileBoundaryDigest D ctx st).run state)) :
    DigestShape ctx.self C.terms r.1 := by
  simp only [compileBoundaryDigest, StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨terms, _, pairs, _, hr⟩ := hr
  apply compiler_mapM_shape _ _ _ (fun T state r hr => ?_) _ _ hr
  intro hn
  simp only [if_neg hn, StateT.run_pure, mem_support_pure_iff] at hr
  exact congrArg Prod.fst hr

/-- Honest digest queries only; adversarial queries consume no private slot. -/
def HonestDigest : (WorldSpec C).Domain → Prop
  | .inr t => DigestQuery t
  | .inl _ => False

theorem free_hash_query (q : Query C) :
    free (liftComp (hashQuery q) (LocalSpec C)) =
      OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr (.inr (.inl q)))) := by
  rfl

/-- Every digest vector of the right shape is an all-answer source path.
The history queries are free and the digest replies can be chosen independently. -/
theorem digest_source_residual (P : (WorldSpec C).Domain → Prop)
    (hashCost : ∀ q : Query C, P (.inr (.inr (.inl q))) ↔
      DigestQuery (C := C) (.inr (.inl q)))
    (i : C.Party) (salts : Shares C Bit) (history : C.Term → List Bit)
    (xs : List C.Term) (ys : List HashOutput) (shape : DigestShape i xs ys) :
    ResidualCost P
      (free (liftComp (xs.mapM fun T => if i ∈ C.holders T then do
        hashQuery (C := C) (.digest (vector 256 (salts T)) (← hashQuery (.history (history T))))
        else pure 0) (LocalSpec C))) ys
      (xs.map fun T => if i ∈ C.holders T then 1 else 0).sum := by
  induction shape with
  | nil => simpa using ResidualCost.pure (P := P) (S := WorldSpec C) ([] : List HashOutput)
  | @cons T value xs ys hT hs ih =>
    simp only [List.mapM_cons, liftComp_bind, free_bind, liftComp_pure, free_pure,
      List.map_cons, List.sum_cons]
    apply ResidualCost.bind (a := value)
    · split_ifs with held
      · simp only [liftComp_bind, free_bind, free_hash_query]
        have historyCost : ¬ P (.inr (.inr (.inl (.history (history T))))) := by
          rw [hashCost]
          simp [DigestQuery, digestSaltProjection]
        have digestCost : P (.inr (.inr (.inl (.digest (vector 256 (salts T)) 0)))) := by
          rw [hashCost]
          simp [DigestQuery, digestSaltProjection]
        have h := ResidualCost.bind
          (f := fun hist => (OracleComp.lift (OracleSpec.query
            (spec := WorldSpec C) (.inr (.inr (.inl (.digest (vector 256 (salts T)) hist)))))))
          (ResidualCost.query (P := P) (S := WorldSpec C)
            (.inr (.inr (.inl (.history (history T))))) (0 : HashOutput))
          (ResidualCost.query (P := P) (S := WorldSpec C)
            (.inr (.inr (.inl (.digest (vector 256 (salts T)) 0)))) value)
        simpa only [if_neg historyCost, if_pos digestCost, Nat.zero_add] using h
      · simpa only [liftComp_pure, free_pure, hT held] using
          ResidualCost.pure (P := P) (S := WorldSpec C) (0 : HashOutput)
    · simpa only [bind_pure_comp, Nat.add_zero] using
        (ResidualCost.bind (f := fun zs => pure (value :: zs)) ih
          (ResidualCost.pure (P := P) (S := WorldSpec C) (value :: ys)))

omit [Field E] [Algebra Bit E] in
/-- Complete source boundaries account for every compiler-produced answer. -/
theorem boundary_source_residual (D : C.Coalition)
    (P : (WorldSpec C).Domain → Prop)
    (hashCost : ∀ q : Query C, P (.inr (.inr (.inl q))) ↔
      DigestQuery (C := C) (.inr (.inl q)))
    (ctx : Context C) (st : RunState C) (state : CompilerState C) (r)
    (hr : r ∈ support ((compileBoundaryDigest D ctx st).run state)) :
    ResidualCost P (TreeRawSaltFlowProof.boundarySource (E := E) D (.inl (ctx, st)))
      r.1 (treeSimHashHeld ctx.self) := by
  obtain ⟨rnd, supported⟩ := support_nonempty
    (free (liftComp (prssDraw ctx (bitCodec (E := E)) st.label 2 256) (LocalSpec C)))
  have shape := compileBoundaryDigest_shape D ctx st state r hr
  rw [show treeSimHashHeld ctx.self =
    (C.terms.map fun T => if ctx.self ∈ C.holders T then 1 else 0).sum by
      simp [treeSimHashHeld, Committee.terms, Finset.sum_map_toList]]
  change ResidualCost P (free (liftComp (treeSimHashSaltDigestDraw (E := E) ctx st)
    (LocalSpec C))) r.1 _
  simp only [treeSimHashSaltDigestDraw, liftComp_bind, free_bind]
  have hp := ResidualCost.of_support (P := P) supported
  have hd := digest_source_residual P hashCost ctx.self rnd.1 st.history C.terms r.1 shape
  have hd' : ResidualCost P
      (free (liftComp (digestQuery ctx.self rnd.1 st.history) (LocalSpec C))) r.1
      (C.terms.map fun T => if ctx.self ∈ C.holders T then 1 else 0).sum := by
    exact hd
  simpa only [Nat.zero_add] using ResidualCost.bind (a := rnd) (b := r.1)
    (f := fun rnd => free (liftComp (digestQuery ctx.self rnd.1 st.history) (LocalSpec C))) hp hd' 

omit [Field E] [Algebra Bit E] in
/-- The concrete source boundary reflects the compiler cost for every
continuation, without a feasibility or source-residual hypothesis. -/
theorem boundary_budget_reflect_source (D : C.Coalition)
    (P : (WorldSpec C).Domain → Prop)
    (Q : (TreeSimHashSaltTableSpec (TreeSimHashSaltBlock C) C).Domain → Prop)
    (hashCost : ∀ q : Query C, P (.inr (.inr (.inl q))) ↔
      DigestQuery (C := C) (.inr (.inl q)))
    {α : Type} (ctx : Context C) (st : RunState C)
    (source : List HashOutput → OracleComp (WorldSpec C) α)
    (target : List HashOutput → CompilerM C α)
    (step : CompilerBound Q (compileBoundaryDigest D ctx st) (treeSimHashHeld ctx.self))
    (next : ∀ a n, IsQueryBoundP (source a) P n → CompilerBound Q (target a) n)
    (n : ℕ) (h : IsQueryBoundP
      (TreeRawSaltFlowProof.boundarySource (E := E) D (.inl (ctx, st)) >>= source) P n) :
    CompilerBound Q (compileBoundaryDigest D ctx st >>= target) n := by
  apply boundary_budget_reflect D P Q ctx st source target step next n
  constructor
  · obtain ⟨r, hr⟩ := support_nonempty ((compileBoundaryDigest D ctx st).run (∅, []))
    exact ((boundary_source_residual D P hashCost ctx st _ r hr).residual source n h).1
  · intro state r hr
    exact ((boundary_source_residual D P hashCost ctx st state r hr).residual source n h).2

omit [Field E] [Algebra Bit E] in
theorem compiler_program_private {α : Type} (D : C.Coalition)
    (p : OracleComp (TreeRawSaltFlowProof.BoundarySpec D) α) (n : ℕ)
    (h : IsQueryBoundP (simulateQ (TreeRawSaltFlowProof.boundarySource (E := E) D) p)
      HonestDigest n) :
    CompilerBound TreeSimHashSaltPrivate (simulateQ (boundaryCompiler D) p) n := by
  apply compiler_program_budget_of_boundary D HonestDigest TreeSimHashSaltPrivate
    (fun t state => (publicQuery_private D t state).mono (Nat.zero_le _)) _ p n h
  intro α ctx st source target next n bound
  exact boundary_budget_reflect_source D HonestDigest TreeSimHashSaltPrivate
    (fun _ => Iff.rfl) ctx st source target (compileBoundaryDigest_private D ctx st) next n bound

omit [Field E] [Algebra Bit E] in
theorem compiler_program_charged {α : Type} (D : C.Coalition)
    (p : OracleComp (TreeRawSaltFlowProof.BoundarySpec D) α) (n : ℕ)
    (h : IsQueryBoundP (simulateQ (TreeRawSaltFlowProof.boundarySource (E := E) D) p)
      PublicDigest n) :
    CompilerBound treeSimHashSaltTableCharged (simulateQ (boundaryCompiler D) p) n := by
  apply compiler_program_budget_of_boundary D PublicDigest treeSimHashSaltTableCharged
    (publicQuery_charged D) _ p n h
  intro α ctx st source target next n bound
  exact boundary_budget_reflect_source D PublicDigest treeSimHashSaltTableCharged
    (fun _ => Iff.rfl) ctx st source target (compileBoundaryDigest_charged D ctx st) next n bound

theorem publicDigest_local_iff {α : Type}
    (p : OracleComp (LocalSpec C + LocalSpec C) α) (n : ℕ) :
    IsQueryBoundP (simulateQ treeSimLocalWorld p) PublicDigest n ↔
      IsQueryBoundP p TreeSimHashDigest n := by
  induction p using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    cases t with
    | inl t =>
      change IsQueryBoundP (OracleComp.lift (OracleSpec.query
        (spec := WorldSpec C) (.inl (.inl t))) >>= _) PublicDigest n ↔ _
      simp only [isQueryBoundP_query_bind_iff, PublicDigest, TreeSimHashDigest, ih]
      rfl
    | inr t =>
      change IsQueryBoundP (OracleComp.lift (OracleSpec.query
        (spec := WorldSpec C) (.inr t)) >>= _) PublicDigest n ↔ _
      simp only [isQueryBoundP_query_bind_iff, PublicDigest, TreeSimHashDigest, ih]
      rfl

theorem ceremony_source_charged (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) :
    IsQueryBoundP (treeRealGame K circuits settings top tree D A x z Z) PublicDigest
      (q + treeBatches settings tree * (C.t * termCount C)) := by
  letI : Fintype E := Fintype.ofEquiv (Fin elementBits → Bit) K.encode.symm
  letI : DecidableEq E := Classical.decEq E
  rw [← treeSim_localReal_eq, publicDigest_local_iff, ← treeSimHash_merge_bound]
  exact treeSimHash_game_digest K circuits settings top tree D A x z Z q hq

/-- The full charged compiler budget includes all adversarial digest calls
and every honest held-term digest, including aborted prefixes. -/
theorem ceremonyProgram_charged (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ)
    (hq : IsQueryBounded A Z (ceremonyFuel circuits settings) q) :
    IsQueryBoundP (ceremonyProgram K circuits settings top tree D A x z Z)
      treeSimHashSaltTableCharged (q + treeBatches settings tree * (C.t * termCount C)) := by
  apply compiler_program_charged (E := E) D _ _ _ (∅, [])
  rw [ceremonyBoundary_source]
  exact ceremony_source_charged K circuits settings top tree D A x z Z q hq

namespace HonestDigestCount
open TreeSimHashCount
variable {ι α β : Type} {G : OracleSpec ι}

theorem adversary_zero (p : OracleComp (LocalSpec C) α) :
    IsQueryBoundP (worldRoles.adversary p) HonestDigest 0 := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [worldRoles, counted]
  | query_bind t k ih =>
    rw [adversary_bind, adversary_query, isQueryBoundP_query_bind_iff]
    exact ⟨Or.inl (by simp [HonestDigest]), fun a => by simpa [HonestDigest] using ih a⟩

omit [Field E] [Algebra Bit E] in
theorem advance_bind_bound (oa : OracleComp (PartySpec C E G) (Option α))
    (k : Step C E G α → OracleComp (WorldSpec C) β) (extra : ℕ) :
    ∀ n, IsQueryBoundP oa (PartyQuery DigestQuery (E := E) (G := G)) n →
      (∀ st b, b ≤ n → StepBudget DigestQuery st b →
        IsQueryBoundP (k st) HonestDigest (extra + b)) →
      IsQueryBoundP (free (advance oa) >>= k) HonestDigest (extra + n) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ hk
    rw [advance_pure, free_pure, pure_bind]
    exact hk (.done a) n le_rfl trivial
  | query_bind t f ih =>
    intro n h hk
    rw [isQueryBoundP_query_bind_iff] at h
    rcases t with (q | outbox) | input
    · rw [advance_query_bind, free_bind, bind_assoc]
      change IsQueryBoundP (OracleComp.lift (OracleSpec.query
        (spec := WorldSpec C) (.inr q)) >>= _) HonestDigest (extra + n)
      rw [isQueryBoundP_query_bind_iff]
      constructor
      · by_cases hc : DigestQuery q
        · right
          have hn := h.1.resolve_left (fun hn => hn hc)
          omega
        · exact Or.inl hc
      · intro u
        have hb : (if PartyQuery DigestQuery (E := E) (G := G)
            (.inl (.inl q)) then n - 1 else n) ≤ n := by split_ifs <;> omega
        have hi := ih u _ (h.2 u) (fun st b hb' hs => hk st b (hb'.trans hb) hs)
        apply hi.mono
        by_cases hq : DigestQuery q
        · have hn := h.1.resolve_left (fun hn => hn hq)
          simp only [HonestDigest, PartyQuery, if_pos hq]
          omega
        · simp only [HonestDigest, PartyQuery, if_neg hq, Nat.le_refl]
    · change IsQueryBoundP (k (.wait outbox f)) HonestDigest (extra + n)
      apply hk _ n le_rfl
      simpa [StepBudget, PartyQuery] using h.2
    · change IsQueryBoundP (k (.call input f)) HonestDigest (extra + n)
      apply hk _ n le_rfl
      simpa [StepBudget, PartyQuery] using h.2

omit [Field E] [Algebra Bit E] in
theorem sequenceFin_advance_bind_bound : ∀ {N : ℕ}
    (oa : Fin N → OracleComp (PartySpec C E G) (Option α)) (budget : Fin N → ℕ)
    (_h : ∀ i, IsQueryBoundP (oa i) (PartyQuery DigestQuery (E := E) (G := G)) (budget i))
    (k : (Fin N → Step C E G α) → OracleComp (WorldSpec C) β) (extra : ℕ),
    (∀ st (b : Fin N → ℕ), (∀ i, b i ≤ budget i) →
      (∀ i, StepBudget DigestQuery (st i) (b i)) →
      IsQueryBoundP (k st) HonestDigest (extra + ∑ i, b i)) →
    IsQueryBoundP ((Concrete.sequenceFin fun i => free (advance (oa i))) >>= k) HonestDigest
      (extra + ∑ i, budget i)
  | 0, oa, budget, _h, k, extra, hk => by
    simp only [Concrete.sequenceFin, pure_bind, Fin.sum_univ_zero, Nat.add_zero]
    simpa using hk Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | N + 1, oa, budget, h, k, extra, hk => by
    simp only [Concrete.sequenceFin, bind_assoc, pure_bind]
    rw [Fin.sum_univ_succ]
    have he : extra + (budget 0 + ∑ i : Fin N, budget i.succ) =
        (extra + ∑ i : Fin N, budget i.succ) + budget 0 := by omega
    rw [he]
    refine advance_bind_bound (oa 0) _ _ (budget 0) (h 0) (fun st0 b0 hb0 hs0 => ?_)
    have he' : (extra + ∑ i : Fin N, budget i.succ) + b0 =
        (extra + b0) + ∑ i : Fin N, budget i.succ := by omega
    rw [he']
    refine sequenceFin_advance_bind_bound (fun i : Fin N => oa i.succ) (fun i => budget i.succ)
      (fun i => h i.succ) (fun st => k (Fin.cases st0 st)) (extra + b0) (fun st b hb hs => ?_)
    have hp := hk (Fin.cases st0 st) (Fin.cases b0 b)
      (fun i => Fin.cases hb0 hb i) (fun i => Fin.cases hs0 hs i)
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hp

variable {I : Type} (D : C.Coalition) (A : Adversary C E I PEmpty PEmpty)

theorem stepRound_bind_bound
    (state : A.State) (steps : C.Party → Step C E RealSpec α) (budget : C.Party → ℕ)
    (h : ∀ j, StepBudget DigestQuery (steps j) (budget j))
    (k : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → Mail C E)) → OracleComp (WorldSpec C) β)
    (extra : ℕ)
    (hk : ∀ st (b : C.Party → ℕ), (∀ j, b j ≤ budget j) →
      (∀ j, StepBudget DigestQuery (st.2.1 j) (b j)) →
      IsQueryBoundP (k st) HonestDigest (extra + ∑ j, b j)) :
    IsQueryBoundP (stepRound worldRoles D A noFunctionality state steps >>= k)
      HonestDigest (extra + ∑ j, budget j) := by
  unfold stepRound
  split_ifs with hcall
  · obtain ⟨i, _, hi⟩ := hcall.1
    cases hs : steps i with
    | done out => simp [hs, Step.callInput] at hi
    | wait out resume => simp [hs, Step.callInput] at hi
    | call input resume => exact PEmpty.elim input
  · simp only [bind_assoc, pure_bind]
    apply (isQueryBoundP_bind (m := extra + ∑ j, budget j)
      (adversary_zero (A.round state _)) (fun result _ => ?_)).mono (by omega)
    have he : (fun j => match steps j with
        | .done out => pure (Step.done out)
        | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else free (advance
            (resume fun k => if k ∈ D.1 then result.2 k j else (steps k).delivered j))
        | .call _ _ => pure (Step.done none)) = fun j => free (advance (roundResume D result.2 steps j)) := by
      funext j
      cases hs : steps j with
      | done out => simp only [roundResume, hs]; rfl
      | call input f => simp only [roundResume, hs]; rfl
      | wait out f => simp only [roundResume, hs]; split_ifs <;> rfl
    have hseq := sequenceFin_advance_bind_bound
      (fun j => roundResume D result.2 steps j) budget
      (roundResume_regionBound (P := DigestQuery) D result.2 steps budget h)
      (fun st => k (result.1, st, result.2)) extra
      (fun st b hb hs => hk (result.1, st, result.2) b hb hs)
    convert (congrArg (fun f : C.Party → OracleComp (WorldSpec C) (Step C E RealSpec α) =>
      IsQueryBoundP (Concrete.sequenceFin f >>= fun st => k (result.1, st, result.2))
        HonestDigest (extra + ∑ j, budget j)) he).mpr hseq using 1
    congr 2
    funext j
    cases steps j <;> rfl

theorem executeRounds_bound :
    ∀ fuel state (steps : C.Party → Step C E RealSpec α) (budget : C.Party → ℕ),
      (∀ j, StepBudget DigestQuery (steps j) (budget j)) →
      IsQueryBoundP (executeRounds worldRoles D A noFunctionality fuel state steps)
        HonestDigest (∑ j, budget j)
  | 0, state, steps, budget, h => isQueryBoundP_pure _ _ _
  | fuel + 1, state, steps, budget, h => by
    unfold executeRounds
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · apply (stepRound_bind_bound D A state steps budget h
        (fun st => executeRounds worldRoles D A noFunctionality fuel st.1 st.2.1) 0
        (fun st b _ hs => ?_)).mono (by omega)
      simpa only [Nat.zero_add] using executeRounds_bound fuel _ _ _ hs

theorem executePhase_bound (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) (budget : C.Party → ℕ)
    (hp : ∀ j, j ∉ D.1 → DigestPartyBound (program j) (budget j)) :
    IsQueryBoundP (executePhase worldRoles D A noFunctionality fuel state program)
      HonestDigest (∑ j, budget j) := by
  unfold executePhase startSteps
  simp only [worldRoles]
  have he : (fun i => if i ∈ D.1 then pure (Step.done none) else free (advance (program i).run)) =
      fun i => free (advance (if i ∈ D.1 then pure none else (program i).run)) := by
    funext i
    split_ifs <;> rfl
  change IsQueryBoundP ((Concrete.sequenceFin _) >>= _) _ _
  rw [he]
  have h := sequenceFin_advance_bind_bound
    (fun i => if i ∈ D.1 then pure none else (program i).run) budget
    (fun j => ?_) (fun st => executeRounds worldRoles D A noFunctionality fuel state st) 0
    (fun st b hb hs => by simpa only [Nat.zero_add] using executeRounds_bound D A fuel state st b hs)
  · simpa only [Nat.zero_add, worldRoles] using h
  · split_ifs with hj
    · exact isQueryBoundP_pure _ _ _
    · exact hp j hj
end HonestDigestCount

/-- Honest digest calls in the exact real syntax are bounded independently
of the adversary's own query budget. -/
theorem ceremony_source_private (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    IsQueryBoundP (treeRealGame K circuits settings top tree D A x z Z) HonestDigest
      (treeBatches settings tree * (C.t * termCount C)) := by
  unfold treeRealGame distinguish realExecution
  rw [bind_assoc]
  apply (isQueryBoundP_bind (HonestDigestCount.adversary_zero (A.start _ _))
    (fun state _ => isQueryBoundP_bind
      (HonestDigestCount.executePhase_bound D A (ceremonyFuel circuits settings) state
        (fun i => ceremony K circuits settings i (x i) top tree)
        (fun i => treeBatches settings tree * treeSimHashHeld i)
        (fun i _ => treeSimHash_ceremony_digest K circuits settings i (x i) top tree))
      (fun out _ => HonestDigestCount.adversary_zero (Z out)))).mono
  rw [← Finset.mul_sum, treeSimHashHeld_total]
  omega

theorem ceremonyProgram_private (K : Constants C E) (circuits : Circuits) (settings : Settings)
    (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    IsQueryBoundP (ceremonyProgram K circuits settings top tree D A x z Z)
      TreeSimHashSaltPrivate (treeBatches settings tree * (C.t * termCount C)) := by
  apply compiler_program_private (E := E) D _ _ _ (∅, [])
  rw [ceremonyBoundary_source]
  exact ceremony_source_private K circuits settings top tree D A x z Z

/-- Every counted digest in the complete decoded ceremony is present in
that execution's public salt list. No collision hypothesis is needed. -/
theorem ceremony_counted_recorded (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput)
    (r) (hr : r ∈ support (tableRun prims
      (ceremonyProgram K circuits settings top tree D A x z Z) ([], []) ∅ ∅))
    (salt : List Bit) (history : HashOutput) (output : HashOutput)
    (hm : (⟨.inl (.inl (.inr (.inl (.digest salt history)))), output⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ (ceremonyDecode r).2.2) :
    salt ∈ r.1.2.2 := by
  have hinv := Preserves.simulateQ prims (boundaryCompiler D)
    (ceremonyBoundary K circuits settings top tree D A x z Z)
    (preserves_boundaryCompiler prims D)
    (∅, []) ([], []) ∅ ∅ (by simp [Recorded]) r hr
  exact hinv salt history output (counted_mem_decode _ _ _ salt history output hm)

/-- A hidden salt in the decoded ceremony belongs to the private event list
of that same table execution. Repeated PRSS addresses use the same block. -/
theorem ceremony_hidden_recorded (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput)
    (r) (hr : r ∈ support (tableRun prims
      (ceremonyProgram K circuits settings top tree D A x z Z) ([], []) ∅ ∅))
    (salt : List Bit) (hs : TreeSimHiddenSalt D (ceremonyDecode r).2.2 salt) :
    salt ∈ r.1.2.1 := by
  have safe := Preserves.simulateQ prims (boundaryCompiler D)
    (ceremonyBoundary K circuits settings top tree D A x z Z)
    (safe_boundaryCompiler prims D)
    (∅, []) ([], []) ∅ ∅ (by simp [SafeLiterals]) r hr
  have ready := TreeRawSaltStepsProof.compiler_program_ready prims D
    (ceremonyBoundary K circuits settings top tree D A x z Z)
    (ceremonyBoundary_safe K circuits settings top tree D A x z Z)
    ([], []) ∅ ∅ (∅, []) (by simp [Ready]) r hr
  obtain ⟨b, values, hv, rfl⟩ := hiddenSalt_cached D r.1.1.2 r.1.2 r.2.1 r.2.2 safe ready salt hs
  exact tableRun_private_recorded prims _ ([], []) ∅ ∅
    (by simp [PrivateRecorded]) r hr b values hv

/-- The fixed decoder transports salt guessing to the reader's intersection
without requiring a collision-free transcript. -/
theorem ceremony_saltGuess_hit (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput)
    (r) (hr : r ∈ support (tableRun prims
      (ceremonyProgram K circuits settings top tree D A x z Z) ([], []) ∅ ∅))
    (hs : TreeSimSaltGuess D (ceremonyDecode r).2.2) : AddressHit r := by
  obtain ⟨salt, history, output, hidden, counted⟩ := hs
  exact ⟨salt, ceremony_hidden_recorded prims K circuits settings top tree D A x z Z r hr salt hidden,
    ceremony_counted_recorded prims K circuits settings top tree D A x z Z r hr salt history output counted⟩

/-- Both all-answer query budgets for the selected compiler. The private
budget is H and the charged budget is q + H from the ceremony statement. -/
def CeremonyCompilerBudgets (K : Constants C E) (circuits : Circuits) (settings : Settings) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    let H := treeBatches settings tree * (C.t * termCount C)
    let p := ceremonyProgram K circuits settings top tree D A x z Z
    IsQueryBoundP p TreeSimHashSaltPrivate H ∧
    IsQueryBoundP p treeSimHashSaltTableCharged (q + H)

/-- Exact global all-answer budgets for the fixed ceremony compiler. -/
theorem ceremonyCompilerBudgets (K : Constants C E) (circuits : Circuits) (settings : Settings) :
    CeremonyCompilerBudgets K circuits settings := by
  intro _ top tree D A x z Z q _ hq _
  exact ⟨ceremonyProgram_private K circuits settings top tree D A x z Z,
    ceremonyProgram_charged K circuits settings top tree D A x z Z q hq⟩

/-- The budgets alone supply the original fixed-compiler certificates. -/
theorem ceremonyCompilerCertificates_of_budgets (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings)
    (budgets : CeremonyCompilerBudgets K circuits settings) :
    CeremonyCompilerCertificates prims K circuits settings := by
  intro hb top tree D A x z Z q hx hq hsmall
  obtain ⟨hp, hc⟩ := budgets hb top tree D A x z Z q hx hq hsmall
  exact ⟨hp, hc, fun r hr _ hs => ceremony_saltGuess_hit prims K circuits settings top tree D A x z Z r hr hs⟩

/-- The selected compiler supplies the original certificates with no residual
boundary, feasibility, or counting assumptions. -/
theorem ceremonyCompilerCertificates (prims : Primitives) (K : Constants C E)
    (circuits : Circuits) (settings : Settings) :
    CeremonyCompilerCertificates prims K circuits settings :=
  ceremonyCompilerCertificates_of_budgets prims K circuits settings
    (ceremonyCompilerBudgets K circuits settings)

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.tableRun_public_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableRun_public_mono

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.counted_mem_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms counted_mem_decode

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.tableRun_private_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tableRun_private_recorded

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.hiddenSalt_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hiddenSalt_cached

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.publicProgram_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms publicProgram_private

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.compileBoundaryDigest_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compileBoundaryDigest_private

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.publicProgram_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms publicProgram_charged

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.compileBoundaryDigest_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compileBoundaryDigest_charged

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.ceremony_counted_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremony_counted_recorded

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.ceremony_hidden_recorded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremony_hidden_recorded

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.ceremony_saltGuess_hit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremony_saltGuess_hit

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.ceremonyCompilerCertificates_of_budgets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyCompilerCertificates_of_budgets

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.compiler_program_budget_of_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms compiler_program_budget_of_boundary

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.boundary_budget_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_budget_reflect

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.boundary_source_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_source_residual

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.boundary_budget_reflect_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boundary_budget_reflect_source

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.ceremony_source_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremony_source_private

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.ceremonyProgram_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyProgram_private

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.ceremonyProgram_charged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyProgram_charged

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.ceremonyCompilerBudgets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyCompilerBudgets

/-- info: 'ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof.ceremonyCompilerCertificates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceremonyCompilerCertificates

end ThresholdLeanXmssSecurity.TreeRawSaltCertificatesProof
