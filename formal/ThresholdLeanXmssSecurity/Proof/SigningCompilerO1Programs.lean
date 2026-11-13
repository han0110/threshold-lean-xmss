import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Calls
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Events
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncSuffix

/-! # Coupled honest PRF computations of the O1 coupling

- `prfVirtual_sync` couples the PRF value of a tree build with the virtual reads of its terms.
- `prfValue_sync` couples the PRF value of a signing step on both sides.
- `eval_sync` couples the part of an honest signer, which reads its terms and its masks.
- `callPost_bind` composes the posts of two parts of a run. `virtualList_sync` and
  `slotList_sync` read a list of terms or slots, one call at a time.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Programs
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync SigningCompilerO1Frame SigningCompilerO1Calls
open SigningCompilerSyncBackend SigningCompilerSyncRealRead SigningCompilerSyncLocalRead
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

section Programs
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-! ## Runs of programs -/

/-- The real run of a bind is the bind of the real runs. -/
theorem realHonest_bind {α β : Type} (oa : OracleComp (RoSpec C) α) (f : α → OracleComp (RoSpec C) β) :
    realHonest prims x s pads u rest (oa >>= f) =
      realHonest prims x s pads u rest oa >>= fun v => realHonest prims x s pads u rest (f v) := by
  rw [realHonest, SigningSecurityProof.liftFree, liftComp_bind, free_bind, simulateQ_bind]

/-- The real run of a pure value is pure. -/
theorem realHonest_pure {α : Type} (v : α) :
    realHonest prims x s pads u rest (pure v : OracleComp (RoSpec C) α) = pure v := by
  rw [realHonest, SigningSecurityProof.liftFree, liftComp_pure]
  rfl

/-- The real run of one query of `H` is one honest call. -/
theorem realHonest_hashQuery (input : Query C) :
    realHonest prims x s pads u rest (hashQuery input) = realCall prims x s pads u rest input := by
  rw [realHonest, SigningSecurityProof.liftFree, hashQuery, free]
  erw [liftComp_query, simulateQ_query]
  simp only [OracleQuery.input_query, OracleQuery.cont_query, id_map]
  rfl

/-- A result of a real bind is a result of the second part from a result of the first part. -/
theorem realHonest_bind_support {α β : Type} (oa : OracleComp (RoSpec C) α)
    (f : α → OracleComp (RoSpec C) β) (a : RealState C) (r : β × RealState C)
    (hr : r ∈ support ((realHonest prims x s pads u rest (oa >>= f)).run a)) :
    ∃ r1 ∈ support ((realHonest prims x s pads u rest oa).run a),
      r ∈ support ((realHonest prims x s pads u rest (f r1.1)).run r1.2) := by
  rw [realHonest_bind, StateT.run_bind, mem_support_bind_iff] at hr
  exact hr

/-- A real read of a truncated hash is the truncated answer of one honest call. -/
theorem realHonest_read (input : Query C) :
    realHonest prims x s pads u rest (truncateHash <$> hashQuery input) =
      truncateHash <$> realCall prims x s pads u rest input := by
  rw [map_eq_bind_pure_comp, realHonest_bind, realHonest_hashQuery, map_eq_bind_pure_comp]
  simp only [Function.comp_def, realHonest_pure]

/-- A result of a real read of a truncated hash is the truncated result of one honest call. -/
theorem realHonest_read_support (input : Query C) (a : RealState C) (r : Digest × RealState C)
    (hr : r ∈ support ((realHonest prims x s pads u rest
      (truncateHash <$> hashQuery input)).run a)) :
    ∃ r1 ∈ support ((realCall prims x s pads u rest input).run a), r = (truncateHash r1.1, r1.2) := by
  revert hr
  rw [realHonest_read, StateT.run_map, support_map]
  intro h
  obtain ⟨r1, h1, h2⟩ := h
  exact ⟨r1, by with_reducible exact h1, h2.symm⟩

/-- A result of a real `mapM` over a nonempty list splits at the head. -/
theorem realHonest_cons_support {ι β : Type} (k : ι) (l : List ι) (f : ι → OracleComp (RoSpec C) β)
    (a : RealState C) (r : List β × RealState C)
    (hr : r ∈ support ((realHonest prims x s pads u rest ((k :: l).mapM f)).run a)) :
    ∃ r1 ∈ support ((realHonest prims x s pads u rest (f k)).run a),
      ∃ r2 ∈ support ((realHonest prims x s pads u rest (l.mapM f)).run r1.2),
        r = (r1.1 :: r2.1, r2.2) := by
  rw [List.mapM_cons] at hr
  obtain ⟨r1, h1, h2⟩ := realHonest_bind_support prims x s pads u rest _ _ a r hr
  obtain ⟨r2, h3, h4⟩ := realHonest_bind_support prims x s pads u rest _ _ r1.2 r h2
  rw [realHonest_pure, StateT.run_pure, mem_support_pure_iff] at h4
  exact ⟨r1, h1, r2, h3, h4⟩

/-- A result of a compiler bind is a result of the second part from a result of the first part. -/
theorem runX_bind_support {α β : Type} (oa : SourceMX C α) (f : α → SourceMX C β)
    (src : SourceState C) (st : CompState C) (r : (β × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise) (oa >>= f) src st)) :
    ∃ r1 ∈ support (runX (compBackend x q s pads u rest noise) oa src st),
      r ∈ support (runX (compBackend x q s pads u rest noise) (f r1.1.1) r1.1.2 r1.2) := by
  rw [runX_bind, mem_support_bind_iff] at hr
  exact hr

/-- A result of a compiler `mapM` over a nonempty list splits at the head. -/
theorem runX_cons_support {ι β : Type} (k : ι) (l : List ι) (f : ι → SourceMX C β)
    (src : SourceState C) (st : CompState C) (r : (List β × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise) ((k :: l).mapM f) src st)) :
    ∃ r1 ∈ support (runX (compBackend x q s pads u rest noise) (f k) src st),
      ∃ r2 ∈ support (runX (compBackend x q s pads u rest noise) (l.mapM f) r1.1.2 r1.2),
        r = ((r1.1.1 :: r2.1.1, r2.1.2), r2.2) := by
  rw [List.mapM_cons] at hr
  obtain ⟨r1, h1, h2⟩ := runX_bind_support x q s pads u rest noise _ _ src st r hr
  obtain ⟨r2, h3, h4⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ r h2
  rw [runX_pure, mem_support_pure_iff] at h4
  exact ⟨r1, h1, r2, h3, h4⟩

/-- A result of a compiler read of a truncated hash is the truncated result of one source read. -/
theorem runX_read_support (input : Query C) (src : SourceState C) (st : CompState C)
    (r : (Digest × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise)
      (sourceRoProgramX prims x.1 x.2.1 (truncateHash <$> hashQuery input)) src st)) :
    ∃ r1 ∈ support (runX (compBackend x q s pads u rest noise) (sourceHashX x.1 x.2.1 input) src st),
      r = ((truncateHash r1.1.1, r1.1.2), r1.2) := by
  have he : sourceRoProgramX prims x.1 x.2.1 (truncateHash <$> hashQuery input) =
      sourceHashX x.1 x.2.1 input >>= fun v => pure (truncateHash v) := by
    simp [sourceRoProgramX, hashQuery, sourceRoX, map_eq_bind_pure_comp]
  rw [he] at hr
  obtain ⟨r1, h1, h2⟩ := runX_bind_support x q s pads u rest noise _ _ src st r hr
  rw [runX_pure, mem_support_pure_iff] at h2
  exact ⟨r1, h1, h2⟩

/-- The stop of the real side persists over an honest computation. -/
theorem realHonest_stop {α : Type} (oa : OracleComp (RoSpec C) α) (a : RealState C)
    (h : RealStop q a) (r : α × RealState C)
    (hr : r ∈ support ((realHonest prims x s pads u rest oa).run a)) : RealStop q r.2 :=
  simulateQ_sticky _ (RealStop q) (fun t st hst r hr => realStop_world prims x (gOf s pads u) rest q
    t st hst r hr) _ a h r hr

/-- The stop of the compiler side persists over a run. -/
theorem runX_compStop {α : Type} (oa : SourceMX C α) (src : SourceState C) (st : CompState C)
    (h : Stop st) (r : (α × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise) oa src st)) : Stop r.2 :=
  SigningCompilerSyncSuffix.runX_stop x q s pads (tauOf s pads) (gOf s pads u) noise rest oa src st
    h r hr

/-! ## Composition of posts -/

/-- A post passes to results with the same states and a weaker value relation. -/
theorem callPost_map {α β α' β' : Type} (cCore : Carried C) (seen : Query C → Prop)
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (value : α → β → Prop) (value' : α' → β' → Prop)
    (ra : α × RealState C) (rb : (β × SourceState C) × CompState C)
    (ra' : α' × RealState C) (rb' : (β' × SourceState C) × CompState C)
    (h : CallPost x q s pads u rest noise cCore seen a src st value ra rb)
    (hra : ra'.2 = ra.2) (hrb1 : rb'.1.2 = rb.1.2) (hrb2 : rb'.2 = rb.2)
    (hv : value ra.1 rb.1.1 → value' ra'.1 rb'.1.1) :
    CallPost x q s pads u rest noise cCore seen a src st value' ra' rb' := by
  unfold CallPost at h ⊢
  rw [hra, hrb1, hrb2]
  rcases h with h | h | ⟨h1, h2, h3, h4⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hv h1, h2, h3, h4⟩)

/-- The posts of two parts of a run compose. The second part starts from the states after the
first part. -/
theorem callPost_bind {α β α' β' : Type} (cCore : Carried C) (seen1 seen2 : Query C → Prop)
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (value1 : α → β → Prop) (value2 : α' → β' → Prop)
    (r1 : α × RealState C) (rb1 : (β × SourceState C) × CompState C)
    (r2 : α' × RealState C) (rb2 : (β' × SourceState C) × CompState C)
    (h1 : CallPost x q s pads u rest noise cCore seen1 a src st value1 r1 rb1)
    (hstopa : RealStop q r1.2 → RealStop q r2.2) (hstopb : Stop rb1.2 → Stop rb2.2)
    (h2 : SyncCore x s pads noise (gOf s pads u) rest (withCarried r1.2 cCore) (rb1.1.2, rb1.2) →
      ¬RealStop q r1.2 → ¬Stop rb1.2 → rb1.2.1.2 = false →
      CallPost x q s pads u rest noise cCore seen2 r1.2 rb1.1.2 rb1.2 value2 r2 rb2) :
    RealStop q r2.2 ∨ Stop rb2.2 ∨
      (value1 r1.1 rb1.1.1 ∧ CallFrame x seen1 a r1.2 (src, st) (rb1.1.2, rb1.2) ∧
        value2 r2.1 rb2.1.1 ∧ CallFrame x seen2 r1.2 r2.2 (rb1.1.2, rb1.2) (rb2.1.2, rb2.2) ∧
        SyncCore x s pads noise (gOf s pads u) rest (withCarried r2.2 cCore) (rb2.1.2, rb2.2) ∧
        CallFrame x (fun query => seen1 query ∨ seen2 query) a r2.2 (src, st) (rb2.1.2, rb2.2) ∧
        rb2.2.1.2 = false) := by
  by_cases ha : RealStop q r1.2
  · exact Or.inl (hstopa ha)
  by_cases hb : Stop rb1.2
  · exact Or.inr (Or.inl (hstopb hb))
  rcases h1 with h | h | ⟨hv1, hs1, hf1, hm1⟩
  · exact (ha h).elim
  · exact (hb h).elim
  rcases h2 hs1 ha hb hm1 with h | h | ⟨hv2, hs2, hf2, hm2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  exact Or.inr (Or.inr ⟨hv1, hf1, hv2, hf2, hs2,
    CallFrame.trans x seen1 seen2 a r1.2 r2.2 _ _ _ hf1 hf2, hm2⟩)

/-! ## Lists of reads -/

/-- The virtual reads of a list of terms at a constrained point. The real side returns the
truncated table values. Each term becomes virtual. When the list is not empty and each term is
virtual at the end, a bound key has a revealed opening. -/
theorem virtualList_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (cCore : Carried C)
    (p : CPoint) (l : List C.Term) (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (ha : ¬RealStop q a) (hb : ¬Stop st) (hmark : st.1.2 = false)
    (ra : List Digest × RealState C)
    (hra : ra ∈ support ((realHonest prims x s pads u rest
      (l.mapM fun T => truncateHash <$> hashQuery (.prf (x.2.1 T) p.val))).run a))
    (rb : (List Unit × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (l.mapM fun T => sourceVirtualX x.1 x.2.1 T p.val) src st)) :
    CallPost x q s pads u rest noise cCore (fun query => ∃ T, query = .prf (x.2.1 T) p.val) a src st
      (fun va _ => va = l.map (fun T => truncateHash (gOf s pads u (T, p))) ∧
        (∀ T ∈ l, (T, p.val) ∈ (dataOf x rb.2).virtual) ∧
        (l ≠ [] → ∀ e, p.val = .randomizer bottomLayer e → src.signing.bound e ≠ none →
          (∀ T', (T', p.val) ∈ (dataOf x rb.2).virtual) →
            rb.1.2.revealed (.opening bottomLayer e) ≠ none)) ra rb := by
  induction l generalizing a src st ra rb with
  | nil =>
    revert hra hrb
    rw [List.mapM_nil, List.mapM_nil, realHonest_pure, StateT.run_pure, mem_support_pure_iff,
      runX_pure, mem_support_pure_iff]
    rintro rfl rfl
    exact Or.inr (Or.inr ⟨⟨rfl, fun T hT => (List.not_mem_nil hT).elim, fun h => (h rfl).elim⟩,
      hs, CallFrame.weaken x _ _ a a _ _ (CallFrame.refl x a (src, st)) (fun _ h => h.elim), hmark⟩)
  | cons T l ih =>
    obtain ⟨r1, h1, r2, h2, rfl⟩ := realHonest_cons_support prims x s pads u rest T l
      (fun T => truncateHash <$> hashQuery (.prf (x.2.1 T) p.val)) a ra (by with_reducible exact hra)
    obtain ⟨rb1, hb1, rb2, hb2, rfl⟩ := runX_cons_support x q s pads u rest noise T l
      (fun T => sourceVirtualX x.1 x.2.1 T p.val) src st rb hrb
    obtain ⟨r0, h0, rfl⟩ := realHonest_read_support prims x s pads u rest _ a r1
      (by with_reducible exact h1)
    have hv := virtualRead_sync prims x q s pads u rest noise hkeys cCore T p a src st hs ha hb hmark
      r0 (by with_reducible exact h0) rb1 hb1
    have hc := callPost_bind x q s pads u rest noise cCore _ _ a src st _ _ r0 rb1 r2 rb2 hv
      (fun h => realHonest_stop prims x q s pads u rest _ r0.2 h r2 (by with_reducible exact h2))
      (fun h => runX_compStop x q s pads u rest noise _ rb1.1.2 rb1.2 h rb2 hb2)
      (fun hs1 ha1 hb1' hm1 => ih r0.2 rb1.1.2 rb1.2 hs1 ha1 hb1' hm1 r2
        (by with_reducible exact h2) rb2 hb2)
    unfold CallPost
    rcases hc with h | h | ⟨⟨hv0, hvT, hrev⟩, hf1, ⟨hv2, hvl, hrevl⟩, hf2, hs2, hf, hm2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    refine Or.inr (Or.inr ⟨⟨?_, ?_, ?_⟩, hs2, CallFrame.weaken x _ _ a r2.2 _ _ hf ?_, hm2⟩)
    · simp only [List.map_cons, hv0, hv2]
    · intro T' hT'
      rcases List.mem_cons.1 hT' with rfl | hT'
      · exact hf2.virtual _ _ hvT
      · exact hvl T' hT'
    · intro _ e he hbound hall
      cases l with
      | nil =>
        revert hb2
        rw [List.mapM_nil, runX_pure, mem_support_pure_iff]
        rintro rfl
        exact hrev e he hbound hall
      | cons T'' l =>
        exact hrevl (List.cons_ne_nil _ _) e he (by rw [hf1.signing]; exact hbound) hall
    · rintro query (rfl | ⟨T', rfl⟩)
      · exact ⟨T, rfl⟩
      · exact ⟨T', rfl⟩

/-- A result of a compiler run of a `mapM` program over a nonempty list splits at the head. -/
theorem runX_roCons_support {ι β : Type} (k : ι) (l : List ι) (f : ι → OracleComp (RoSpec C) β)
    (src : SourceState C) (st : CompState C) (r : (List β × SourceState C) × CompState C)
    (hr : r ∈ support (runX (compBackend x q s pads u rest noise)
      (sourceRoProgramX prims x.1 x.2.1 ((k :: l).mapM f)) src st)) :
    ∃ r1 ∈ support (runX (compBackend x q s pads u rest noise)
        (sourceRoProgramX prims x.1 x.2.1 (f k)) src st),
      ∃ r2 ∈ support (runX (compBackend x q s pads u rest noise)
          (sourceRoProgramX prims x.1 x.2.1 (l.mapM f)) r1.1.2 r1.2),
        r = ((r1.1.1 :: r2.1.1, r2.1.2), r2.2) := by
  rw [List.mapM_cons, sourceRoProgramX, simulateQ_bind] at hr
  obtain ⟨r1, h1, h2⟩ := runX_bind_support x q s pads u rest noise _ _ src st r hr
  rw [simulateQ_bind] at h2
  obtain ⟨r2, h3, h4⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ r h2
  rw [simulateQ_pure, runX_pure, mem_support_pure_iff] at h4
  exact ⟨r1, h1, r2, h3, h4⟩

/-- The slot reads of a list of slots on both sides. Both sides return the truncated table
values. -/
theorem slotList_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (cCore : Carried C)
    {ι : Type} (l : List ι) (slot : ι → TprfSecurityProof.Slot C)
    (f : ι → OracleComp (RoSpec C) Digest)
    (hf : ∀ k ∈ l, f k = truncateHash <$> hashQuery (TprfSecurityProof.slotInput x.2.1 x.2.2 (slot k)))
    (seen : Query C → Prop) (hseen : ∀ k ∈ l, seen (TprfSecurityProof.slotInput x.2.1 x.2.2 (slot k)))
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (ha : ¬RealStop q a) (hb : ¬Stop st) (hmark : st.1.2 = false)
    (ra : List Digest × RealState C)
    (hra : ra ∈ support ((realHonest prims x s pads u rest (l.mapM f)).run a))
    (rb : (List Digest × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (sourceRoProgramX prims x.1 x.2.1 (l.mapM f)) src st)) :
    CallPost x q s pads u rest noise cCore seen a src st
      (fun va vb => va = vb ∧ va = l.map fun k => truncateHash (realTable (gOf s pads u) rest (slot k)))
      ra rb := by
  induction l generalizing a src st ra rb with
  | nil =>
    revert hra hrb
    rw [List.mapM_nil, realHonest_pure, StateT.run_pure, mem_support_pure_iff, sourceRoProgramX,
      simulateQ_pure, runX_pure, mem_support_pure_iff]
    rintro rfl rfl
    exact Or.inr (Or.inr ⟨⟨rfl, rfl⟩, hs,
      CallFrame.weaken x _ _ a a _ _ (CallFrame.refl x a (src, st)) (fun _ h => h.elim), hmark⟩)
  | cons k l ih =>
    obtain ⟨r1, h1, r2, h2, rfl⟩ := realHonest_cons_support prims x s pads u rest k l f a ra
      (by with_reducible exact hra)
    obtain ⟨rb1, hb1, rb2, hb2, rfl⟩ := runX_roCons_support prims x q s pads u rest noise k l f
      src st rb hrb
    have hk := hf k List.mem_cons_self
    rw [hk] at hb1
    revert h1
    rw [hk]
    intro h1
    obtain ⟨r0, h0, rfl⟩ := realHonest_read_support prims x s pads u rest _ a r1
      (by with_reducible exact h1)
    obtain ⟨rb0, hb0, rfl⟩ := runX_read_support prims x q s pads u rest noise _ src st rb1 hb1
    have hv0 := slotRead_sync prims x q s pads u rest noise hkeys false cCore (slot k) a src st hs ha
      hb hmark r0 (by rw [readCall, if_neg Bool.false_ne_true]; with_reducible exact h0) rb0 hb0
    have hv := callPost_map x q s pads u rest noise cCore _ a src st _
      (fun (va vb : Digest) => va = vb ∧
        va = truncateHash (realTable (gOf s pads u) rest (slot k)))
      r0 rb0 (truncateHash r0.1, r0.2) ((truncateHash rb0.1.1, rb0.1.2), rb0.2) hv0 rfl rfl rfl
      (fun ⟨h1, h2⟩ => ⟨congrArg truncateHash h1, congrArg truncateHash h2⟩)
    have hc := callPost_bind x q s pads u rest noise cCore _ _ a src st _ _ _ _ r2 rb2 hv
      (fun h => realHonest_stop prims x q s pads u rest _ r0.2 h r2 (by with_reducible exact h2))
      (fun h => runX_compStop x q s pads u rest noise _ rb0.1.2 rb0.2 h rb2 hb2)
      (fun hs1 ha1 hb1' hm1 => ih (fun k hk => hf k (List.mem_cons_of_mem _ hk))
        (fun k hk => hseen k (List.mem_cons_of_mem _ hk)) r0.2 rb0.1.2 rb0.2 hs1 ha1 hb1' hm1 r2
        (by with_reducible exact h2) rb2 hb2)
    unfold CallPost
    rcases hc with h | h | ⟨⟨hv1, hv1'⟩, -, ⟨hv2, hv2'⟩, -, hs2, hf2, hm2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    refine Or.inr (Or.inr ⟨⟨?_, ?_⟩, hs2, CallFrame.weaken x _ _ a r2.2 _ _ hf2 ?_, hm2⟩)
    · exact congrArg₂ List.cons hv1 hv2
    · rw [List.map_cons]
      exact congrArg₂ List.cons hv1' hv2'
    · rintro query (rfl | h)
      · exact hseen k List.mem_cons_self
      · exact h

/-! ## Coupled programs -/

/-- The fold of the truncated table values of all terms at a constrained point is its target. -/
theorem terms_fold (p : CPoint) :
    (C.terms.map fun T => truncateHash (gOf s pads u (T, p))).foldl (· ^^^ ·) 0 = tauOf s pads p := by
  rw [SigningCompilerO1Events.foldl_xor_eq, List.foldr_map]
  refine (BitVec.zero_xor (x := _)).trans ?_
  obtain ⟨T, _⟩ := lackedTerm_empty (C := C)
  exact SigningShareLazy.fiberTable_sum C.terms terms_nodup mem_terms
    (SigningCompilerShare.NoFalse.tau s pads) _
    (SigningShareLazy.good_init _ _ (Or.inl (List.ne_nil_of_mem (mem_terms T)))) u p

/-- The real run of the PRF value reads the truncated hash of each term, then folds them. -/
theorem realHonest_prfValue (p : Point) :
    realHonest prims x s pads u rest (prfValue x.2.1 p) =
      realHonest prims x s pads u rest (C.terms.mapM fun T => truncateHash <$> hashQuery (.prf (x.2.1 T) p))
        >>= fun ts => pure (ts.foldl (· ^^^ ·) 0) := by
  unfold prfValue prf
  rw [realHonest_bind]
  simp only [realHonest_pure]

/-- The PRF value reads the truncated hash of each term, then folds them. -/
theorem prfValue_eq (seeds : C.Term → HashOutput) (p : Point) :
    prfValue seeds p = (C.terms.mapM fun T => truncateHash <$> hashQuery (.prf (seeds T) p))
      >>= fun ts => pure (ts.foldl (· ^^^ ·) 0) := rfl

/-- The compiler program of a bind is the bind of the compiler programs. -/
theorem sourceRoProgramX_bind {α β : Type} (oa : OracleComp (RoSpec C) α)
    (g : α → OracleComp (RoSpec C) β) :
    sourceRoProgramX prims x.1 x.2.1 (oa >>= g) =
      sourceRoProgramX prims x.1 x.2.1 oa >>= fun v => sourceRoProgramX prims x.1 x.2.1 (g v) :=
  simulateQ_bind _ _ _

/-- The compiler program of a pure value is pure. -/
theorem sourceRoProgramX_pure {α : Type} (v : α) :
    sourceRoProgramX prims x.1 x.2.1 (pure v : OracleComp (RoSpec C) α) = pure v :=
  simulateQ_pure _ _

/-- The PRF value of a tree build. The real side reads each term and returns the fixed target. The
compiler side records each term as virtual. -/
theorem prfVirtual_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (cCore : Carried C)
    (p : CPoint) (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (ha : ¬RealStop q a) (hb : ¬Stop st) (hmark : st.1.2 = false)
    (ra : Digest × RealState C)
    (hra : ra ∈ support ((realHonest prims x s pads u rest (prfValue x.2.1 p.val)).run a))
    (rb : (List Unit × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (C.terms.mapM fun T => sourceVirtualX x.1 x.2.1 T p.val) src st)) :
    CallPost x q s pads u rest noise cCore (fun query => ∃ T, query = .prf (x.2.1 T) p.val) a src st
      (fun va _ => va = tauOf s pads p ∧ (∀ T, (T, p.val) ∈ (dataOf x rb.2).virtual) ∧
        ∀ e, p.val = .randomizer bottomLayer e → src.signing.bound e ≠ none →
          rb.1.2.revealed (.opening bottomLayer e) ≠ none) ra rb := by
  revert hra
  rw [realHonest_prfValue, StateT.run_bind, mem_support_bind_iff]
  rintro ⟨r1, h1, h2⟩
  rw [StateT.run_pure, mem_support_pure_iff] at h2
  subst h2
  have hl := virtualList_sync prims x q s pads u rest noise hkeys cCore p C.terms a src st hs ha hb
    hmark r1 (by with_reducible exact h1) rb hrb
  obtain ⟨T0, _⟩ := lackedTerm_empty (C := C)
  refine callPost_map x q s pads u rest noise cCore _ a src st _ _ r1 rb _ rb hl rfl rfl rfl ?_
  rintro ⟨hv, hvirt, hrev⟩
  have hall : ∀ T, (T, p.val) ∈ (dataOf x rb.2).virtual := fun T => hvirt T (mem_terms T)
  refine ⟨?_, hall, fun e he hbound => hrev (List.ne_nil_of_mem (mem_terms T0)) e he hbound hall⟩
  change r1.1.foldl (· ^^^ ·) 0 = tauOf s pads p
  rw [hv]
  exact terms_fold s pads u p

/-- The PRF value of a signing step. Both sides read each term and return the fixed target. -/
theorem prfValue_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (cCore : Carried C)
    (p : CPoint) (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (ha : ¬RealStop q a) (hb : ¬Stop st) (hmark : st.1.2 = false)
    (ra : Digest × RealState C)
    (hra : ra ∈ support ((realHonest prims x s pads u rest (prfValue x.2.1 p.val)).run a))
    (rb : (Digest × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (sourceRoProgramX prims x.1 x.2.1 (prfValue x.2.1 p.val)) src st)) :
    CallPost x q s pads u rest noise cCore (fun query => ∃ T, query = .prf (x.2.1 T) p.val) a src st
      (fun va vb => va = vb ∧ va = tauOf s pads p) ra rb := by
  revert hra hrb
  rw [realHonest_prfValue, StateT.run_bind, mem_support_bind_iff, prfValue_eq,
    sourceRoProgramX_bind, runX_bind, mem_support_bind_iff]
  rintro ⟨r1, h1, h2⟩ ⟨rb1, hb1, hb2⟩
  rw [StateT.run_pure, mem_support_pure_iff] at h2
  rw [sourceRoProgramX_pure, runX_pure, mem_support_pure_iff] at hb2
  subst h2 hb2
  have hl := slotList_sync prims x q s pads u rest noise hkeys cCore C.terms
    (fun T => .inl (T, p.val)) (fun T => truncateHash <$> hashQuery (.prf (x.2.1 T) p.val))
    (fun _ _ => rfl) (fun query => ∃ T, query = .prf (x.2.1 T) p.val) (fun T _ => ⟨T, rfl⟩)
    a src st hs ha hb hmark r1
    (by with_reducible exact h1) rb1 hb1
  refine callPost_map x q s pads u rest noise cCore _ a src st _ _ r1 rb1 _ _ hl rfl rfl rfl ?_
  rintro ⟨hv, hv'⟩
  refine ⟨congrArg (fun ts : List Digest => ts.foldl (· ^^^ ·) 0) hv, ?_⟩
  change r1.1.foldl (· ^^^ ·) 0 = tauOf s pads p
  simp only [hv', realTable_constrained]
  exact terms_fold s pads u p

/-- The part of an honest signer. Both sides read the terms of the signer and its masks. -/
theorem eval_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (cCore : Carried C)
    (i : C.Party) (J : C.Quorum) (p : Point) (message : Message)
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (ha : ¬RealStop q a) (hb : ¬Stop st) (hmark : st.1.2 = false)
    (ra : Digest × RealState C)
    (hra : ra ∈ support ((realHonest prims x s pads u rest
      (eval (dealtKeys x.1 x.2.1 x.2.2 i) i J p message)).run a))
    (rb : (Digest × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (sourcePartX prims x i J p message) src st)) :
    CallPost x q s pads u rest noise cCore
      (fun query => (∃ T, query = .prf (x.2.1 T) p) ∨ ∃ seed J', query = .mask seed p message J')
      a src st (fun va vb => va = vb) ra rb := by
  obtain ⟨T0, _⟩ := lackedTerm_empty (C := C)
  revert hra hrb
  unfold sourcePartX eval
  rw [realHonest_bind, StateT.run_bind, mem_support_bind_iff, sourceRoProgramX_bind, runX_bind,
    mem_support_bind_iff]
  rintro ⟨r1, h1, h2⟩ ⟨rb1, hb1, hb2⟩
  revert h2 hb2
  rw [realHonest_bind, StateT.run_bind, mem_support_bind_iff, sourceRoProgramX_bind, runX_bind,
    mem_support_bind_iff]
  rintro ⟨r2, h2, h3⟩ ⟨rb2, hb2, hb3⟩
  rw [realHonest_pure, StateT.run_pure, mem_support_pure_iff] at h3
  rw [sourceRoProgramX_pure, runX_pure, mem_support_pure_iff] at hb3
  subst h3 hb3
  have hterms := slotList_sync prims x q s pads u rest noise hkeys cCore _ (fun T => .inl (T, p))
    _ (fun T hT => by
      have hL := of_decide_eq_true (List.mem_filter.1 hT).2
      show truncateHash <$> hashQuery (.prf ((dealtKeys x.1 x.2.1 x.2.2 i).seed T) p) = _
      rw [show (dealtKeys x.1 x.2.1 x.2.2 i).seed T = x.2.1 T from
        if_pos (TprfCorrectnessProof.mem_holders_of_mem_L hL)]
      rfl)
    (fun query => (∃ T, query = .prf (x.2.1 T) p) ∨ ∃ seed J', query = .mask seed p message J')
    (fun T _ => Or.inl ⟨T, rfl⟩) a src st hs ha hb hmark r1 (by with_reducible exact h1) rb1 hb1
  let slot : C.Party → TprfSecurityProof.Slot C := fun j =>
    if h : j = i then .inl (T0, p) else .inr (C.pairOf i j (Ne.symm h), p, message, J)
  have hmasks := fun hs1 ha1 hb1' hm1 => slotList_sync prims x q s pads u rest noise hkeys cCore _
    slot _ (fun j hj => by
      have hji := (of_decide_eq_true (List.mem_filter.1 hj).2).2
      simp only [slot, dealtKeys, dif_neg hji, TprfSecurityProof.slotInput])
    (fun query => (∃ T, query = .prf (x.2.1 T) p) ∨ ∃ seed J', query = .mask seed p message J')
    (fun j hj => by
      have hji := (of_decide_eq_true (List.mem_filter.1 hj).2).2
      simp only [slot, dif_neg hji, TprfSecurityProof.slotInput]
      exact Or.inr ⟨_, _, rfl⟩)
    r1.2 rb1.1.2 rb1.2 hs1 ha1 hb1' hm1 r2 (by with_reducible exact h2) rb2 hb2
  have hc := callPost_bind x q s pads u rest noise cCore _ _ a src st _ _ r1 rb1 r2 rb2 hterms
    (fun h => realHonest_stop prims x q s pads u rest _ r1.2 h r2 (by with_reducible exact h2))
    (fun h => runX_compStop x q s pads u rest noise _ rb1.1.2 rb1.2 h rb2 hb2) hmasks
  unfold CallPost
  rcases hc with h | h | ⟨⟨hv1, -⟩, -, ⟨hv2, -⟩, -, hs2, hf2, hm2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  refine Or.inr (Or.inr ⟨?_, hs2, CallFrame.weaken x _ _ a r2.2 _ _ hf2 (fun _ h => h.elim id id),
    hm2⟩)
  change (r1.1 ++ r2.1).foldl (· ^^^ ·) 0 = (rb1.1.1 ++ rb2.1.1).foldl (· ^^^ ·) 0
  rw [hv1, hv2]

end Programs

end ThresholdLeanXmssSecurity.SigningCompilerO1Programs

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_pure

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_hashQuery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_hashQuery

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_bind_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_bind_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_read' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_read

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_read_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_read_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_cons_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_cons_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.runX_bind_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.runX_bind_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.runX_cons_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.runX_cons_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.runX_read_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.runX_read_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_stop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_stop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.runX_compStop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.runX_compStop

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.callPost_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.callPost_map

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.callPost_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.callPost_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.virtualList_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.virtualList_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.runX_roCons_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.runX_roCons_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.slotList_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.slotList_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.terms_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.terms_fold

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_prfValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.realHonest_prfValue

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.prfValue_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.prfValue_eq

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.sourceRoProgramX_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.sourceRoProgramX_bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.sourceRoProgramX_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.sourceRoProgramX_pure

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.prfVirtual_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.prfVirtual_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.prfValue_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.prfValue_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Programs.eval_sync' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Programs.eval_sync
