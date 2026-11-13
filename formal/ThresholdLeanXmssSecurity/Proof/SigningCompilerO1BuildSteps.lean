import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Pre
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Programs
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1ChainPending
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1RealBuild

/-! # The steps of the bottom tree build

- `row_sync` couples one row of a build. Both sides give the same row, and no key is revealed.
- `topValue_sync` couples one chain value of the top signature of a build. The compiler value is
  symbolic, and the real value is its reading at the secrets.
- `topRecover_sync` couples the verification walk of one top chain of a build.
- `walk_sync` couples a chain walk with the pending calls of `walkCalls`. The three lemmas above use it.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open SigningCompilerO1Sync
open XmssSecurity.CappedChain
open SigningCompilerO1Frame SigningCompilerO1Pre SigningCompilerO1Programs SigningCompilerO1RealBuild
open SigningCompilerSyncBackend SigningCompilerSyncSuffix
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

/-! ## The reveal map of the source -/

/-- A virtual call at a chain point keeps the reveal map of the source. -/
theorem keepsRevealed_virtual (P : PublicParameter) (seeds : C.Term → HashOutput) (T : C.Term)
    (lay : Layer) (e : KeyIndex) (l : ChainIndex) (d : Digit) :
    SourceKeepsX (fun src : SourceState C => src.revealed)
      (sourceVirtualX P seeds T (.chain lay e l d)) := by
  unfold sourceVirtualX
  exact (SourceKeepsX.lift _).bind _ fun _ => SourceKeepsX.pure ()

/-- A pending call keeps the reveal map of the source. -/
theorem keepsRevealed_pending (P : PublicParameter) (p : PendingInput) :
    SourceKeepsX (fun src : SourceState C => src.revealed) (sourcePendingX P p) := by
  have tail (prior : Option DeferredOutput) : SourceKeepsX (fun src : SourceState C => src.revealed)
      (do
        let value ← liftM (deferredQueryX (C := C) (.pending p))
        if prior.isNone then
          modify fun (source : SourceState C) => { source with allocated := source.allocated ++ [p] }
        pure value : SourceMX C DeferredOutput) := by
    refine (SourceKeepsX.lift (deferredQueryX (.pending p))).bind _ fun value => ?_
    split
    · exact (SourceKeepsX.modify (fun st => { st with allocated := st.allocated ++ [p] })
        (fun _ => rfl)).bind _ (fun _ => SourceKeepsX.pure value)
    · exact SourceKeepsX.pure value
  unfold sourcePendingX
  refine (SourceKeepsX.lift (deferredQueryX (.inspect p))).bind _ fun prior => ?_
  refine SourceKeepsX.get.bind _ fun source => ?_
  dsimp only
  split
  · refine (SourceKeepsX.lift (deferredQueryX (.hash (.hash _)))).bind _ fun value => ?_
    refine (SourceKeepsX.lift (deferredQueryX (.record p value))).bind _ fun _ => ?_
    exact (SourceKeepsX.modify (fun st => { st with allocated := st.allocated ++ [p] })
      (fun _ => rfl)).bind _ (fun _ => SourceKeepsX.pure _)
  · rename_i original priorCopy known next hmiss
    split
    · exact (SourceKeepsX.modify (fun st => { st with consistent := false }) (fun _ => rfl)).bind _
        (fun _ => tail original)
    · simpa only [pure_bind] using tail original

/-! ## Chain walks -/

/-- The pending inputs of a chain walk of `n` steps from position `start`. -/
def walkCalls (side : XmssSecurity.LeafIndex ⊕ XmssSecurity.TopIndex) (l : ChainIndex)
    (start : ℕ) : ℕ → List PendingInput
  | 0 => []
  | n + 1 => walkCalls side l start n ++
      if h : start + n < chainLength - 1 then [chainPending (l, side, ⟨start + n, h⟩)] else []

/-- Each input of a walk is a chain input of its side. -/
theorem mem_walkCalls (side : XmssSecurity.LeafIndex ⊕ XmssSecurity.TopIndex) (l : ChainIndex)
    (start n : ℕ) (p : PendingInput) (hp : p ∈ walkCalls side l start n) :
    ∃ k : ChainStep, p = chainPending (l, side, k) := by
  induction n with
  | zero => cases hp
  | succ n ih =>
    rcases List.mem_append.mp hp with hp | hp
    · exact ih hp
    · split at hp
      · exact ⟨_, List.mem_singleton.mp hp⟩
      · cases hp

/-- A walk is the map of its positions over `List.finRange`. -/
theorem walkCalls_eq_map (side : XmssSecurity.LeafIndex ⊕ XmssSecurity.TopIndex) (l : ChainIndex)
    (start n : ℕ) (pos : Fin n → ChainStep) (hpos : ∀ i, (pos i).val = start + i.val) :
    walkCalls side l start n = (List.finRange n).map fun i => chainPending (l, side, pos i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : start + n < chainLength - 1 := by
      have h1 := hpos (Fin.last n)
      have h2 := (pos (Fin.last n)).isLt
      simp only [Fin.val_last] at h1
      omega
    have hlast : pos (Fin.last n) = ⟨start + n, hlt⟩ := Fin.ext (hpos _)
    rw [walkCalls, dif_pos hlt, ih (fun i => pos i.castSucc) (fun i => hpos i.castSucc),
      List.finRange_succ_last, List.map_append, List.map_map, List.map_singleton, hlast]
    rfl

/-- The pending calls of a top walk of the compiler are the calls of `walkCalls`. -/
theorem mapM_walkCalls_top (P : PublicParameter) (b : XmssSecurity.TopIndex) (l : ChainIndex)
    (start n : ℕ) (pos : Fin n → ChainStep) (hpos : ∀ i, (pos i).val = start + i.val) :
    (List.finRange n).mapM (fun i => sourcePendingX (C := C) P (.top b l (pos i))) =
      (walkCalls (.inr b) l start n).mapM (sourcePendingX P) := by
  rw [walkCalls_eq_map (.inr b) l start n pos hpos, List.mapM_map]
  rfl

/-- The verification walk of a top chain keeps the reveal map of the source. -/
theorem keepsRevealed_topRecover (P : PublicParameter) (b : XmssSecurity.TopIndex) (l : ChainIndex)
    (p : Digit) (initial : DeferredDigest) :
    SourceKeepsX (fun src : SourceState C => src.revealed) (sourceTopRecoverX P b l p initial) := by
  unfold sourceTopRecoverX
  refine (SourceKeepsX.mapM _ _ (fun i _ => keepsRevealed_pending P (.top b l _))).bind _
    fun values => ?_
  dsimp only
  split
  · exact SourceKeepsX.pure _
  · exact (SourceKeepsX.modify (fun st => { st with consistent := false }) (fun _ => rfl)).bind _
      (fun _ => SourceKeepsX.pure _)

/-- A chain value of the top signature keeps the reveal map of the source. -/
theorem keepsRevealed_topValue (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (p : Digit) :
    SourceKeepsX (fun src : SourceState C => src.revealed) (sourceTopValueX P seeds b l p) := by
  unfold sourceTopValueX
  refine (SourceKeepsX.mapM _ _ (fun T _ => keepsRevealed_virtual P seeds T _ _ _ _)).bind _
    fun _ => ?_
  exact (SourceKeepsX.mapM _ _ (fun i _ => keepsRevealed_pending P (.top b l _))).bind _
    (fun _ => SourceKeepsX.pure _)

/-- An inner chain edge names the key of the next position. -/
theorem chainPending_next_some (side : XmssSecurity.LeafIndex ⊕ XmssSecurity.TopIndex)
    (l : ChainIndex) (j : ℕ) (hj : j < chainLength - 1) (h : j + 1 < chainLength - 1) :
    (chainPending (l, side, ⟨j, hj⟩)).next = some (chainPending (l, side, ⟨j + 1, h⟩)).key := by
  rcases side with e | b <;>
    simp [chainPending, PendingInput.next, PendingInput.key, show j + 1 < 3 from h]

/-- The last chain edge names no key. -/
theorem chainPending_next_none (side : XmssSecurity.LeafIndex ⊕ XmssSecurity.TopIndex)
    (l : ChainIndex) (j : ℕ) (hj : j < chainLength - 1) (h : j + 1 = chainLength - 1) :
    (chainPending (l, side, ⟨j, hj⟩)).next = none := by
  rcases side with e | b <;>
    simp [chainPending, PendingInput.next, show ¬j + 1 < 3 by change j + 1 = 3 at h; omega]

/-- The truncation of an answer is the reading of its low half. -/
theorem truncateHash_interpret (s : HiddenKey → Digest) (v : DeferredOutput) :
    truncateHash (v.interpret s) = v.low.interpret s :=
  congrArg Prod.snd (XmssSecurity.Rom.hashOutputEquivDigestPair.apply_symm_apply _)

/-- A walk of `n + 1` steps is the walk of `n` steps and one more step. -/
theorem chainWalk_step {m : Type → Type} [Monad m] [HasQuery HashSpec m] (P : PublicParameter)
    (lay : Layer) (key : KeyIndex) (l : ChainIndex) (start n : ℕ) (v : Digest)
    (h : start + n < chainLength - 1) :
    Concrete.chainWalk (m := m) P lay key l start (n + 1) v =
      Concrete.chainWalk P lay key l start n v >>= fun previous =>
        Concrete.tweakableHash P (.chain lay key ⟨start + n, h⟩) (Concrete.chainPayload l previous) := by
  simp only [Concrete.chainWalk, dif_pos h]

/-- One step of `Th` on the domain of `H` is the truncated answer of one query. -/
theorem tweakable_tweakableHash (P : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    tweakable (C := C) (Concrete.tweakableHash P domain payload : OracleComp HashSpec Digest) =
      truncateHash <$> hashQuery (.hash (tweakableHashInput P domain payload)) := by
  simp [Concrete.tweakableHash, tweakable_bind, tweakable_oracleHash, tweakable_pure,
    map_eq_bind_pure_comp]

/-- A `mapM` over a list with one more element at the end. -/
theorem mapM_snoc {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type} (f : α → m β)
    (xs : List α) (y : α) :
    (xs ++ [y]).mapM f = (do
      let values ← xs.mapM f
      let value ← f y
      pure (values ++ [value])) := by
  simp [List.mapM_append]

/-- A nonempty list has a last element. -/
theorem exists_getLast {α : Type} (xs : List α) (n : ℕ) (h : xs.length = n + 1) :
    ∃ last, xs.getLast? = some last := by
  cases hl : xs.getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hl
    subst hl
    simp at h
  | some last => exact ⟨last, rfl⟩

/-- The fixed target of a bottom chain start is its secret. -/
theorem tau_row_start (s : HiddenKey → Digest) (pads : Point → Digest) (e : KeyIndex)
    (l : ChainIndex) (d : XmssSecurity.ChainStep) (hd : d.val = 0) :
    tauOf s pads ⟨.chain bottomLayer e l (chainStepDigit d), constrained_bottom_chain e l _ d.isLt⟩ =
      s (.bottomChain e l d) := by
  refine (SigningCompilerShare.NoFalse.tau_bottom_chain s pads e l d).trans ?_
  rw [if_pos hd]
  exact BitVec.xor_zero

/-- The fixed target of an inner bottom chain point is its secret with the pad. -/
theorem tau_row_pad (s : HiddenKey → Digest) (pads : Point → Digest) (e : KeyIndex)
    (l : ChainIndex) (d : XmssSecurity.ChainStep) (hd : d.val ≠ 0) :
    tauOf s pads ⟨.chain bottomLayer e l (chainStepDigit d), constrained_bottom_chain e l _ d.isLt⟩ =
      s (.bottomChain e l d) ^^^ pads (.chain bottomLayer e l (chainStepDigit d)) := by
  refine (SigningCompilerShare.NoFalse.tau_bottom_chain s pads e l d).trans ?_
  rw [if_neg hd]

/-- The six pending calls of a row are the three walks from position 0. -/
theorem bottomRowCalls_walks (e : KeyIndex) (l : ChainIndex) :
    bottomRowCalls e l =
      walkCalls (.inl e) l 0 1 ++ walkCalls (.inl e) l 0 2 ++ walkCalls (.inl e) l 0 3 := rfl

/-- Each pending call of a row is at a chain edge of the row. -/
theorem mem_bottomRowCalls (e : KeyIndex) (l : ChainIndex) (p : PendingInput)
    (hp : p ∈ bottomRowCalls e l) : ∃ k : ChainStep, p = chainPending (l, .inl e, k) := by
  rw [bottomRowCalls_walks] at hp
  simp only [List.mem_append] at hp
  rcases hp with (hp | hp) | hp <;> exact mem_walkCalls _ _ _ _ _ hp

/-- The compiler row in the order of `realRow`. It reads the terms of the three chain points, the
two pads, and walks three times from position 0. -/
theorem sourceBottomRowX_walks (P : PublicParameter) (seeds : C.Term → HashOutput) (e : KeyIndex)
    (l : ChainIndex) :
    sourceBottomRowX P seeds e l = (do
      let _ ← C.terms.mapM fun T => sourceVirtualX P seeds T (.chain bottomLayer e l (digit 0))
      let _ ← C.terms.mapM fun T => sourceVirtualX P seeds T (.chain bottomLayer e l (digit 1))
      let _ ← C.terms.mapM fun T => sourceVirtualX P seeds T (.chain bottomLayer e l (digit 2))
      let cpk₁ ← liftM (deferredQueryX (C := C) (.pad (.chain bottomLayer e l (digit 1))))
      let cpk₂ ← liftM (deferredQueryX (C := C) (.pad (.chain bottomLayer e l (digit 2))))
      let w₁ ← (walkCalls (.inl e) l 0 1).mapM (sourcePendingX P)
      let w₂ ← (walkCalls (.inl e) l 0 2).mapM (sourcePendingX P)
      let w₃ ← (walkCalls (.inl e) l 0 3).mapM (sourcePendingX P)
      pure (cpk₁, cpk₂, match (w₁ ++ w₂ ++ w₃).getLast?.map (fun a : DeferredOutput => a.low) with
        | some (DeferredDigest.known value) => value
        | _ => 0)) := by
  rw [sourceBottomRowX_eq, bottomRowCalls_walks]
  simp [bottomRowPrfCalls, List.mapM_append, sourceBackendX, Function.comp_def]
  rfl

/-- A compiler row keeps the reveal map of the source. -/
theorem keepsRevealed_row (P : PublicParameter) (seeds : C.Term → HashOutput) (e : KeyIndex)
    (l : ChainIndex) :
    SourceKeepsX (fun src : SourceState C => src.revealed) (sourceBottomRowX P seeds e l) := by
  have hv (d : Digit) := SourceKeepsX.mapM (field := fun src : SourceState C => src.revealed) C.terms
    (fun T => sourceVirtualX P seeds T (.chain bottomLayer e l d))
    (fun T _ => keepsRevealed_virtual P seeds T bottomLayer e l d)
  have hw (n : ℕ) := SourceKeepsX.mapM (field := fun src : SourceState C => src.revealed)
    (walkCalls (.inl e) l 0 n) (sourcePendingX P) (fun p _ => keepsRevealed_pending P p)
  rw [sourceBottomRowX_walks]
  exact (hv _).bind _ fun _ => (hv _).bind _ fun _ => (hv _).bind _ fun _ =>
    (SourceKeepsX.lift _).bind _ fun _ => (SourceKeepsX.lift _).bind _ fun _ =>
    (hw 1).bind _ fun _ => (hw 2).bind _ fun _ => (hw 3).bind _ fun _ => SourceKeepsX.pure _

section Steps
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The posts of two parts of a run compose into one post. -/
theorem callPost_trans {α β α' β' : Type} (cCore : Carried C) (seen1 seen2 : Query C → Prop)
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (value1 : α → β → Prop) (value2 : α' → β' → Prop)
    (r1 : α × RealState C) (rb1 : (β × SourceState C) × CompState C)
    (r2 : α' × RealState C) (rb2 : (β' × SourceState C) × CompState C)
    (h1 : CallPost x q s pads u rest noise cCore seen1 a src st value1 r1 rb1)
    (hstopa : RealStop q r1.2 → RealStop q r2.2) (hstopb : Stop rb1.2 → Stop rb2.2)
    (h2 : value1 r1.1 rb1.1.1 →
      SyncCore x s pads noise (gOf s pads u) rest (withCarried r1.2 cCore) (rb1.1.2, rb1.2) →
      ¬RealStop q r1.2 → ¬Stop rb1.2 → rb1.2.1.2 = false →
      CallPost x q s pads u rest noise cCore seen2 r1.2 rb1.1.2 rb1.2 value2 r2 rb2) :
    CallPost x q s pads u rest noise cCore (fun query => seen1 query ∨ seen2 query) a src st
      (fun va vb => value1 r1.1 rb1.1.1 ∧ value2 va vb) r2 rb2 := by
  rcases h1 with h | h | ⟨hv1, hs1, hf1, hm1⟩
  · exact Or.inl (hstopa h)
  · exact Or.inr (Or.inl (hstopb h))
  by_cases ha : RealStop q r1.2
  · exact Or.inl (hstopa ha)
  by_cases hb : Stop rb1.2
  · exact Or.inr (Or.inl (hstopb hb))
  rcases h2 hv1 hs1 ha hb hm1 with h | h | ⟨hv2, hs2, hf2, hm2⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨⟨hv1, hv2⟩, hs2,
      CallFrame.trans x seen1 seen2 a r1.2 r2.2 _ _ _ hf1 hf2, hm2⟩)

/-- A post holds for a larger set of seen queries. -/
theorem callPost_weaken {α β : Type} (cCore : Carried C) (seen seen' : Query C → Prop)
    (a : RealState C) (src : SourceState C) (st : CompState C) (value : α → β → Prop)
    (ra : α × RealState C) (rb : (β × SourceState C) × CompState C)
    (h : CallPost x q s pads u rest noise cCore seen a src st value ra rb)
    (hsub : ∀ query, seen query → seen' query) :
    CallPost x q s pads u rest noise cCore seen' a src st value ra rb := by
  rcases h with h | h | ⟨hv, hs, hf, hm⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hv, hs, CallFrame.weaken x seen seen' a ra.2 _ _ hf hsub, hm⟩)

/-- A result of a real bind of a lifted honest computation splits at the first part. -/
theorem realWorld_bind_support {α β : Type} (oa : OracleComp (RoSpec C) α)
    (f : α → OracleComp (WorldSpec C) β) (a : RealState C) (r : β × RealState C)
    (hr : r ∈ support ((simulateQ (realWorld prims x s pads u rest) (liftFree oa >>= f)).run a)) :
    ∃ r1 ∈ support ((realHonest prims x s pads u rest oa).run a),
      r ∈ support ((simulateQ (realWorld prims x s pads u rest) (f r1.1)).run r1.2) := by
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hr
  exact hr

/-- A pad query. The real side makes no call. The compiler returns the fixed pad. -/
theorem pad_sync (cCore : Carried C) (p : Point) (a : RealState C) (src : SourceState C)
    (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (hpads : PadsFixed x pads st) (hmark : st.1.2 = false)
    (rb : (Digest × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (liftM (deferredQueryX (C := C) (.pad p))) src st)) :
    CallPost x q s pads u rest noise cCore (fun _ => False) a src st
      (fun (_ : Unit) vb => vb = pads p) ((), a) rb := by
  rw [runX_pad x q s pads (tauOf s pads) (gOf s pads u) noise rest p src st hs.1.1.restFree,
    mem_support_pure_iff] at hrb
  subst hrb
  have hframe : CallFrame x (fun _ => False) a a (src, st) (src, st) :=
    CallFrame.weaken x _ _ a a _ _ (CallFrame.refl x a (src, st)) (fun _ h => h.elim)
  cases hp : st.1.1.1.1.data.pads p with
  | some w =>
    simp only [padStep, hp]
    exact Or.inr (Or.inr ⟨hpads p w hp, hs, hframe, hmark⟩)
  | none =>
    simp only [padStep, hp]
    obtain ⟨⟨hF, hC⟩, hcnt⟩ := hs
    refine Or.inr (Or.inr ⟨rfl, ⟨⟨{ hF with opening := ⟨hF.opening.1, hF.opening.2⟩ },
      ⟨hC.agree, hC.pending⟩⟩, hcnt⟩, ⟨rfl, le_rfl, fun _ h => Or.inl h, le_rfl, id, rfl, rfl, rfl,
      rfl, rfl, fun _ _ => rfl, fun _ h1 h2 => (h2 h1).elim, fun _ h => h, fun _ _ h => h⟩, hmark⟩)

/-- A chain walk of `n` steps from position `start`. The real side walks from `v`, and the compiler
side makes the pending calls of `walkCalls`. The last answer gives the real value. -/
theorem walk_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (cCore : Carried C)
    (side : XmssSecurity.LeafIndex ⊕ XmssSecurity.TopIndex) (lay : Layer) (key : KeyIndex)
    (l : ChainIndex)
    (hinput : ∀ (k : ChainStep) (w : Digest),
      tweakableHashInput x.1 (.chain lay key k) (Concrete.chainPayload l w) =
        (chainPending (l, side, k)).input x.1 w)
    (start n : ℕ) (hn : start + n ≤ chainLength - 1) (v : Digest)
    (hv : 0 < n → ∀ h : start < chainLength - 1, v = s (chainPending (l, side, ⟨start, h⟩)).key)
    (a : RealState C) (src : SourceState C) (st : CompState C)
    (hs : SyncCore x s pads noise (gOf s pads u) rest (withCarried a cCore) (src, st))
    (hmark : st.1.2 = false)
    (ra : Digest × RealState C)
    (hra : ra ∈ support ((realHonest prims x s pads u rest
      (tweakable (Concrete.chainWalk x.1 lay key l start n v))).run a))
    (rb : (List DeferredOutput × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      ((walkCalls side l start n).mapM (sourcePendingX x.1)) src st)) :
    CallPost x q s pads u rest noise cCore
      (fun query => ∃ p ∈ walkCalls side l start n, query = .hash (p.input x.1 (s p.key))) a src st
      (fun va vbs => vbs.length = n ∧ (vbs = [] → va = v) ∧
        (∀ p ∈ walkCalls side l start n, (dataOf x rb.2).pending p ≠ none) ∧
        ∀ last, vbs.getLast? = some last → va = last.low.interpret s ∧
          (∀ h : start + n < chainLength - 1,
            last.low = .secret (chainPending (l, side, ⟨start + n, h⟩)).key) ∧
          (start + n = chainLength - 1 → ∃ d, last.low = .known d)) ra rb := by
  induction n generalizing ra rb with
  | zero =>
    rw [show (Concrete.chainWalk x.1 lay key l start 0 v : OracleComp HashSpec Digest) = pure v
      from rfl, tweakable_pure, realHonest_pure, StateT.run_pure, mem_support_pure_iff] at hra
    rw [show walkCalls side l start 0 = [] from rfl, List.mapM_nil, runX_pure,
      mem_support_pure_iff] at hrb
    subst hra hrb
    exact Or.inr (Or.inr ⟨⟨rfl, fun _ => rfl, (fun p hp => by cases hp), (fun last h => by cases h)⟩, hs,
      CallFrame.weaken x _ _ a a _ _ (CallFrame.refl x a (src, st)) (fun _ h => h.elim), hmark⟩)
  | succ n ih =>
    have hlt : start + n < chainLength - 1 := by omega
    have hcalls : walkCalls side l start (n + 1) =
        walkCalls side l start n ++ [chainPending (l, side, ⟨start + n, hlt⟩)] := by
      simp only [walkCalls, dif_pos hlt]
    rw [chainWalk_step _ _ _ _ _ _ _ hlt, tweakable_bind, realHonest_bind, StateT.run_bind,
      mem_support_bind_iff] at hra
    obtain ⟨r1, h1, h2⟩ := hra
    rw [tweakable_tweakableHash] at h2
    obtain ⟨r0, h0, rfl⟩ := realHonest_read_support prims x s pads u rest _ r1.2 _
      (by with_reducible exact h2)
    rw [hcalls, mapM_snoc, runX_bind, mem_support_bind_iff] at hrb
    obtain ⟨rb1, hb1, hb2⟩ := hrb
    rw [runX_bind, mem_support_bind_iff] at hb2
    obtain ⟨rb2, hb2, hb3⟩ := hb2
    rw [runX_pure, mem_support_pure_iff] at hb3
    subst hb3
    rw [hcalls]
    have hstopa : RealStop q r1.2 → RealStop q r0.2 := fun h =>
      realHonest_stop prims x q s pads u rest (truncateHash <$> hashQuery (.hash (tweakableHashInput
        x.1 (.chain lay key ⟨start + n, hlt⟩) (Concrete.chainPayload l r1.1)))) r1.2 h _
        (by with_reducible exact h2)
    have hstopb : Stop rb1.2 → Stop rb2.2 := fun h =>
      runX_compStop x q s pads u rest noise _ rb1.1.2 rb1.2 h rb2 hb2
    have ih1 := ih (by omega) (fun _ h => hv (by omega) h) r1 (by with_reducible exact h1) rb1 hb1
    by_cases ha1 : RealStop q r1.2
    · exact Or.inl (hstopa ha1)
    by_cases hb1' : Stop rb1.2
    · exact Or.inr (Or.inl (hstopb hb1'))
    have hpost := ih1
    rcases ih1 with h | h | ⟨hv1, hs1, hf1, hm1⟩
    · exact (ha1 h).elim
    · exact (hb1' h).elim
    have hprev : r1.1 = s (chainPending (l, side, ⟨start + n, hlt⟩)).key := by
      cases hl : rb1.1.1.getLast? with
      | none =>
        have hnil := List.getLast?_eq_none_iff.mp hl
        have hn0 : n = 0 := by rw [← hv1.1, hnil]; rfl
        subst hn0
        exact (hv1.2.1 hnil).trans (hv (by omega) hlt)
      | some last =>
        obtain ⟨hval, hsec, -⟩ := hv1.2.2.2 last hl
        rw [hval, hsec hlt]
        rfl
    have heq : tweakableHashInput x.1 (.chain lay key ⟨start + n, hlt⟩) (Concrete.chainPayload l r1.1) =
        (chainPending (l, side, ⟨start + n, hlt⟩)).input x.1
          (s (chainPending (l, side, ⟨start + n, hlt⟩)).key) := by
      rw [hinput, hprev]
    have h0' : r0 ∈ support ((realCall prims x s pads u rest
        (.hash ((chainPending (l, side, ⟨start + n, hlt⟩)).input x.1
          (s (chainPending (l, side, ⟨start + n, hlt⟩)).key)))).run r1.2) := by
      rw [← heq]
      with_reducible exact h0
    have hstep := SigningCompilerO1ChainPending.chainPending_sync prims x q s pads u rest noise hkeys
      cCore (l, side, ⟨start + n, hlt⟩) r1.2 rb1.1.2 rb1.2 hs1 ha1 hb1' hm1 r0
      (by with_reducible exact h0') rb2 hb2
    rcases callPost_bind x q s pads u rest noise cCore _ _ a src st _ _ r1 rb1 r0 rb2
      hpost hstopa hstopb (fun _ _ _ _ => hstep) with
      h | h | ⟨-, -, hv2, hf2, hsF, hfF, hmF⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    refine Or.inr (Or.inr ⟨⟨?_, ?_, ?_, ?_⟩, hsF, CallFrame.weaken x _ _ a r0.2 _ _ hfF ?_, hmF⟩)
    · simp [hv1.1]
    · intro h
      simp at h
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hf2.pending p (hv1.2.2.1 p hp)
      · rw [List.mem_singleton.mp hp, hv2.2]
        exact Option.some_ne_none _
    · intro last hl
      simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.some.injEq] at hl
      subst hl
      refine ⟨?_, ?_, ?_⟩
      · change truncateHash r0.1 = _
        rw [hv2.1, truncateHash_interpret]
      · intro h
        rcases hsF.1.1.pendingValid _ _ hv2.2 with ⟨k, hk, hlow⟩ | ⟨hk, -⟩
        · rw [chainPending_next_some side l (start + n) hlt h] at hk
          exact hlow.trans (congrArg DeferredDigest.secret (Option.some.inj hk).symm)
        · rw [chainPending_next_some side l (start + n) hlt h] at hk
          cases hk
      · intro h
        rcases hsF.1.1.pendingValid _ _ hv2.2 with ⟨k, hk, -⟩ | ⟨-, hd⟩
        · rw [chainPending_next_none side l (start + n) hlt (by omega)] at hk
          cases hk
        · exact hd
    · rintro query (⟨p, hp, rfl⟩ | rfl)
      · exact ⟨p, List.mem_append_left _ hp, rfl⟩
      · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩

/-- A post of calls from the state of a handler gives the post inside the handler, when the calls
keep the reveal map and meet the premises of `ExtraOpen.frame`. -/
theorem inPost_of_callPost (top : TopTree) (cCore cTime : Carried C) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    {α β : Type} (seen : Query C → Prop) (value : α → β → Prop)
    (ra : α × RealState C) (rb : (β × SourceState C) × CompState C)
    (h : CallPost x q s pads u rest noise cCore seen a b.1.base b.2 value ra rb)
    (hpads : PadsFixed x pads rb.2) (hrev : rb.1.2.revealed = b.1.base.revealed)
    (hbase : ∀ e ρ message, ¬seen (.hash (randomizerInput x.1 bottomLayer e ρ message)))
    (hguess : ∀ p : PendingInput, (dataOf x rb.2).pending p = none →
      ¬seen (.hash (p.input x.1 (s p.key))))
    (hprf : ∀ T p, seen (.prf (x.2.1 T) p) → Constrained p)
    (hrow : ∀ T e l (d : XmssSecurity.ChainStep),
      seen (.prf (x.2.1 T) (.chain bottomLayer e l (chainStepDigit d))) →
        ∀ d' : XmssSecurity.ChainStep, (dataOf x rb.2).pending (.bottom e l d') ≠ none) :
    InPost prims x q s pads u rest noise top cCore cTime a b (fun rb => rb.1.2.revealed)
      value ra rb := by
  rcases h with h | h | ⟨hv, hcore, hf, hm⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  have hx := ExtraOpen.frame prims x top s seen (fun _ _ => False) (fun _ _ => False)
    b.1.base.revealed rb.1.2.revealed cTime a ra.2 b (⟨rb.1.2, b.1.starts⟩, rb.2) hs.2.1 hf rfl
    (fun k hk => by rw [hrev]; exact hk) (fun k hk => Or.inl (by rw [← hrev]; exact hk)) hbase
    (fun p _ hp => hguess p hp) (fun T p hp => Or.inr (hprf T p hp))
    (fun T e l d hp => Or.inr (Or.inr (hrow T e l d hp))) (fun _ _ h => h)
  exact Or.inr (Or.inr ⟨hv, ⟨hcore, hx, TopO1.frame prims x top seen a ra.2 b
    (⟨rb.1.2, b.1.starts⟩, rb.2) hs.2.2.1 hf, hpads⟩, hf.signing, hf.trees, hf.exposed,
    hf.candidates, hm, hf.carried, hf.log⟩)

end Steps

/-! ## The bottom tree build -/

section Build
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- One row of a build. Both sides give the same row, no key is revealed, and the row has its
virtual terms and its pending answers. -/
theorem row_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (e : KeyIndex) (l : ChainIndex) (a : RealState C)
    (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htime : cTime.1.1.bound = cCore.1.1.bound)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false)
    (ra : (Digest × Digest × Digest) × RealState C)
    (hra : ra ∈ support ((simulateQ (realWorld prims x s pads u rest) (realRow x.1 x.2.1 e l)).run a))
    (rb : ((Digest × Digest × Digest) × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (sourceBottomRowX x.1 x.2.1 e l) b.1.base b.2)) :
    InPost prims x q s pads u rest noise top cCore cTime a b (fun rb => rb.1.2.revealed)
      (fun va vb => va = vb ∧ rb.1.2.revealed = b.1.base.revealed ∧
        ∀ d : XmssSecurity.ChainStep,
          (∀ T, (T, Point.chain bottomLayer e l (chainStepDigit d)) ∈ (dataOf x rb.2).virtual) ∧
            (dataOf x rb.2).pending (.bottom e l d) ≠ none) ra rb := by
  have hrows := sourceBottomRowX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest e l
    b.1.base b.2 rb hrb
  have hpadsF := backend_padsFixed x q s pads u rest noise _ b.2 hs.2.2.2 rb hrb
  have hrevF := SourceKeepsX.run (keepsRevealed_row x.1 x.2.1 e l) (compBackend x q s pads u rest noise)
    b.1.base b.2 rb hrb
  unfold realRow at hra
  obtain ⟨r0, h0, hra⟩ := realWorld_bind_support prims x s pads u rest _ _ a ra hra
  obtain ⟨r1, h1, hra⟩ := realWorld_bind_support prims x s pads u rest _ _ r0.2 ra hra
  obtain ⟨r2, h2, hra⟩ := realWorld_bind_support prims x s pads u rest _ _ r1.2 ra hra
  obtain ⟨y1, hy1, hra⟩ := realWorld_bind_support prims x s pads u rest
    (tweakable (Concrete.chainWalk x.1 bottomLayer e l 0 1 r0.1)) _ r2.2 ra
    (by with_reducible exact hra)
  obtain ⟨y2, hy2, hra⟩ := realWorld_bind_support prims x s pads u rest
    (tweakable (Concrete.chainWalk x.1 bottomLayer e l 0 2 r0.1)) _ y1.2 ra
    (by with_reducible exact hra)
  obtain ⟨y3, hy3, hra⟩ := realWorld_bind_support prims x s pads u rest
    (tweakable (Concrete.chainWalk x.1 bottomLayer e l 0 3 r0.1)) _ y2.2 ra
    (by with_reducible exact hra)
  rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at hra
  subst hra
  have hrb' := hrb
  rw [sourceBottomRowX_walks] at hrb'
  obtain ⟨rb0, hb0, hrb'⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb'
  obtain ⟨rb1, hb1, hrb'⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb'
  obtain ⟨rb2, hb2, hrb'⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb'
  obtain ⟨rb3, hb3, hrb'⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb'
  obtain ⟨rb4, hb4, hrb'⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb'
  obtain ⟨rb5, hb5, hrb'⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb'
  obtain ⟨rb6, hb6, hrb'⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb'
  obtain ⟨rb7, hb7, hrb'⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb'
  rw [runX_pure, mem_support_pure_iff] at hrb'
  subst hrb'
  let p0 : CPoint := ⟨.chain bottomLayer e l (digit 0), constrained_bottom_chain e l _ (by decide)⟩
  let p1 : CPoint := ⟨.chain bottomLayer e l (digit 1), constrained_bottom_chain e l _ (by decide)⟩
  let p2 : CPoint := ⟨.chain bottomLayer e l (digit 2), constrained_bottom_chain e l _ (by decide)⟩
  have hpads0 := backend_padsFixed x q s pads u rest noise _ b.2 hs.2.2.2 rb0 hb0
  have hpads1 := backend_padsFixed x q s pads u rest noise _ rb0.2 hpads0 rb1 hb1
  have hpads2 := backend_padsFixed x q s pads u rest noise _ rb1.2 hpads1 rb2 hb2
  have hpads3 := backend_padsFixed x q s pads u rest noise _ rb2.2 hpads2 rb3 hb3
  have hinput : ∀ (k : ChainStep) (w : Digest),
      tweakableHashInput x.1 (.chain bottomLayer e k) (Concrete.chainPayload l w) =
        (chainPending (l, .inl e, k)).input x.1 w := fun k w =>
    (SigningGuessLinkProof.chainInput_eq_bridge x.1 e l k w).symm
  have hstart : r0.1 = tauOf s pads p0 →
      ∀ h : 0 < chainLength - 1, r0.1 = s (chainPending (l, .inl e, ⟨0, h⟩)).key :=
    fun hv _ => hv.trans (tau_row_start s pads e l ⟨0, by decide⟩ rfl)
  have c0 := prfVirtual_sync prims x q s pads u rest noise hkeys cCore p0 a b.1.base b.2 hs.1 ha hb
    hmark r0 (by with_reducible exact h0) rb0 hb0
  have c1 := callPost_trans x q s pads u rest noise cCore _ _ a b.1.base b.2 _ _ r0 rb0 r1 rb1 c0
    (fun h => realHonest_stop prims x q s pads u rest (prfValue x.2.1 p1.val) r0.2 h r1
      (by with_reducible exact h1))
    (fun h => runX_compStop x q s pads u rest noise _ rb0.1.2 rb0.2 h rb1 hb1)
    (fun _ hs' ha' hb' hm' => prfVirtual_sync prims x q s pads u rest noise hkeys cCore p1 r0.2
      rb0.1.2 rb0.2 hs' ha' hb' hm' r1 (by with_reducible exact h1) rb1 hb1)
  have c2 := callPost_trans x q s pads u rest noise cCore _ _ a b.1.base b.2 _ _ r1 rb1 r2 rb2 c1
    (fun h => realHonest_stop prims x q s pads u rest (prfValue x.2.1 p2.val) r1.2 h r2
      (by with_reducible exact h2))
    (fun h => runX_compStop x q s pads u rest noise _ rb1.1.2 rb1.2 h rb2 hb2)
    (fun _ hs' ha' hb' hm' => prfVirtual_sync prims x q s pads u rest noise hkeys cCore p2 r1.2
      rb1.1.2 rb1.2 hs' ha' hb' hm' r2 (by with_reducible exact h2) rb2 hb2)
  have c3 := callPost_trans x q s pads u rest noise cCore _ _ a b.1.base b.2 _ _ r2 rb2 ((), r2.2) rb3
    c2 (fun h => h) (fun h => runX_compStop x q s pads u rest noise _ rb2.1.2 rb2.2 h rb3 hb3)
    (fun _ hs' _ _ hm' => pad_sync x q s pads u rest noise cCore _ r2.2 rb2.1.2 rb2.2 hs' hpads2 hm'
      rb3 hb3)
  have c4 := callPost_trans x q s pads u rest noise cCore _ _ a b.1.base b.2 _ _ ((), r2.2) rb3
    ((), r2.2) rb4 c3 (fun h => h)
    (fun h => runX_compStop x q s pads u rest noise _ rb3.1.2 rb3.2 h rb4 hb4)
    (fun _ hs' _ _ hm' => pad_sync x q s pads u rest noise cCore _ r2.2 rb3.1.2 rb3.2 hs' hpads3 hm'
      rb4 hb4)
  have c5 := callPost_trans x q s pads u rest noise cCore _ _ a b.1.base b.2 _ _ ((), r2.2) rb4 y1 rb5
    c4 (fun h => realHonest_stop prims x q s pads u rest _ r2.2 h y1 (by with_reducible exact hy1))
    (fun h => runX_compStop x q s pads u rest noise _ rb4.1.2 rb4.2 h rb5 hb5)
    (fun hv hs' _ _ hm' => walk_sync prims x q s pads u rest noise hkeys cCore (.inl e) bottomLayer e l
      hinput 0 1 (by decide) r0.1 (fun _ => hstart hv.1.1.1.1.1) r2.2 rb4.1.2 rb4.2 hs' hm' y1
      (by with_reducible exact hy1) rb5 hb5)
  have c6 := callPost_trans x q s pads u rest noise cCore _ _ a b.1.base b.2 _ _ y1 rb5 y2 rb6 c5
    (fun h => realHonest_stop prims x q s pads u rest _ y1.2 h y2 (by with_reducible exact hy2))
    (fun h => runX_compStop x q s pads u rest noise _ rb5.1.2 rb5.2 h rb6 hb6)
    (fun hv hs' _ _ hm' => walk_sync prims x q s pads u rest noise hkeys cCore (.inl e) bottomLayer e l
      hinput 0 2 (by decide) r0.1 (fun _ => hstart hv.1.1.1.1.1.1) y1.2 rb5.1.2 rb5.2 hs' hm' y2
      (by with_reducible exact hy2) rb6 hb6)
  have c7 := callPost_trans x q s pads u rest noise cCore _ _ a b.1.base b.2 _ _ y2 rb6 y3 rb7 c6
    (fun h => realHonest_stop prims x q s pads u rest _ y2.2 h y3 (by with_reducible exact hy3))
    (fun h => runX_compStop x q s pads u rest noise _ rb6.1.2 rb6.2 h rb7 hb7)
    (fun hv hs' _ _ hm' => walk_sync prims x q s pads u rest noise hkeys cCore (.inl e) bottomLayer e l
      hinput 0 3 (by decide) r0.1 (fun _ => hstart hv.1.1.1.1.1.1.1) y2.2 rb6.1.2 rb6.2 hs' hm' y3
      (by with_reducible exact hy3) rb7 hb7)
  refine inPost_of_callPost prims x q s pads u rest noise top cCore cTime a b hs
    (fun query => (∃ T, ∃ d : XmssSecurity.ChainStep,
        query = .prf (x.2.1 T) (.chain bottomLayer e l (chainStepDigit d))) ∨
      ∃ p ∈ bottomRowCalls e l, query = .hash (p.input x.1 (s p.key))) _ _ _
    (callPost_map x q s pads u rest noise cCore _ a b.1.base b.2 _ _ y3 rb7 _ _
      (callPost_weaken x q s pads u rest noise cCore _ _ a b.1.base b.2 _ y3 rb7 c7 ?_)
      rfl rfl rfl ?_) hpadsF hrevF ?_ ?_ ?_ ?_
  · rw [bottomRowCalls_walks]
    rintro query (((((((⟨T, rfl⟩ | ⟨T, rfl⟩) | ⟨T, rfl⟩) | hf) | hf) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩) |
      ⟨p, hp, rfl⟩)
    · exact Or.inl ⟨T, ⟨0, by decide⟩, rfl⟩
    · exact Or.inl ⟨T, ⟨1, by decide⟩, rfl⟩
    · exact Or.inl ⟨T, ⟨2, by decide⟩, rfl⟩
    · exact hf.elim
    · exact hf.elim
    · exact Or.inr ⟨p, by simp [hp], rfl⟩
    · exact Or.inr ⟨p, by simp [hp], rfl⟩
    · exact Or.inr ⟨p, by simp [hp], rfl⟩
  · rintro ⟨⟨⟨⟨⟨⟨⟨hv0, hv1⟩, hv2⟩, hpd1⟩, hpd2⟩, hw1⟩, hw2⟩, hw3⟩
    refine ⟨?_, hrevF, hrows⟩
    obtain ⟨last1, hl1⟩ := exists_getLast _ 0 hw1.1
    obtain ⟨last2, hl2⟩ := exists_getLast _ 1 hw2.1
    obtain ⟨last3, hl3⟩ := exists_getLast _ 2 hw3.1
    obtain ⟨hval1, hsec1, -⟩ := hw1.2.2.2 last1 hl1
    obtain ⟨hval2, hsec2, -⟩ := hw2.2.2.2 last2 hl2
    obtain ⟨hval3, -, hknown⟩ := hw3.2.2.2 last3 hl3
    obtain ⟨d, hd⟩ := hknown rfl
    have hr1 := hv1.1.trans (tau_row_pad s pads e l ⟨1, by decide⟩ (by decide))
    have hr2 := hv2.1.trans (tau_row_pad s pads e l ⟨2, by decide⟩ (by decide))
    rw [hsec1 (by decide)] at hval1
    rw [hsec2 (by decide)] at hval2
    rw [hd] at hval3
    have hlast : (rb5.1.1 ++ rb6.1.1 ++ rb7.1.1).getLast? = some last3 := by
      simp [List.getLast?_append, hl3]
    have hy1 : y1.1 = s (.bottomChain e l ⟨1, by decide⟩) := hval1
    have hy2 : y2.1 = s (.bottomChain e l ⟨2, by decide⟩) := hval2
    have hy3 : y3.1 = d := hval3
    rw [hlast, hpd1, hpd2, hy1, hy2, hr1, hr2, hy3, ← BitVec.xor_assoc, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.xor_self, BitVec.zero_xor, BitVec.zero_xor]
    simp only [Option.map_some, hd]
    rfl
  · rintro e' ρ message (⟨T, d, h⟩ | ⟨p, hp, h⟩)
    · cases h
    · have h' := Query.hash.inj h
      obtain ⟨k, rfl⟩ := mem_bottomRowCalls e l p hp
      exact SigningCompilerO1ChainPending.chainInput_ne_randomizer x.1 (l, .inl e, k) _ bottomLayer e'
        ρ message h'.symm
  · rintro p' hnone (⟨T, d, h⟩ | ⟨p, hp, h⟩)
    · cases h
    · have hp' := pendingInput_injective x.1 p' p _ _ (Query.hash.inj h)
      subst hp'
      obtain ⟨k, rfl⟩ := mem_bottomRowCalls e l p' hp
      exact (hrows k).2 hnone
  · rintro T p' (⟨T', d, h⟩ | ⟨p, hp, h⟩)
    · obtain ⟨-, rfl⟩ := Query.prf.inj h
      exact constrained_bottom_chain e l _ d.isLt
    · cases h
  · rintro T e' l' d (⟨T', d', h⟩ | ⟨p, hp, h⟩) d''
    · obtain ⟨-, rfl, rfl, -⟩ := Point.chain.inj (Query.prf.inj h).2
      exact (hrows d'').2
    · cases h

/-- One chain value of the top signature of a build. The compiler value is symbolic, and the real
value is its reading at the secrets. -/
theorem topValue_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (bi : Fin (2 ^ layerHeight)) (l : ChainIndex) (p : Digit)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htime : cTime.1.1.bound = cCore.1.1.bound)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false)
    (ra : Digest × RealState C)
    (hra : ra ∈ support ((simulateQ (realWorld prims x s pads u rest)
      (realTopValue x.1 x.2.1 bi l p)).run a))
    (rb : (DeferredDigest × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (sourceTopValueX x.1 x.2.1 bi l p) b.1.base b.2)) :
    InPost prims x q s pads u rest noise top cCore cTime a b (fun rb => rb.1.2.revealed)
      (fun va vb => va = vb.interpret s ∧ rb.1.2.revealed = b.1.base.revealed ∧
        (∀ h : p.val < 3, vb = .secret (.topChain bi l ⟨p.val, h⟩)) ∧
        (p.val = 3 → ∃ w, vb = .known w) ∧
        ∀ T, (T, Point.chain topLayer (topKey bi) l (digit 0)) ∈ (dataOf x rb.2).virtual) ra rb := by
  have hpadsF := backend_padsFixed x q s pads u rest noise _ b.2 hs.2.2.2 rb hrb
  have hrevF := SourceKeepsX.run (keepsRevealed_topValue x.1 x.2.1 bi l p)
    (compBackend x q s pads u rest noise) b.1.base b.2 rb hrb
  have hp := p.isLt
  have hL : chainLength = 4 := rfl
  have hinput : ∀ (k : ChainStep) (w : Digest),
      tweakableHashInput x.1 (.chain topLayer (topKey bi) k) (Concrete.chainPayload l w) =
        (chainPending (l, .inr bi, k)).input x.1 w := fun k w =>
    (SigningGuessLinkProof.topChainInput_eq_bridge x.1 bi l k w).symm
  let p0 : CPoint := ⟨.chain topLayer (topKey bi) l (digit 0), constrained_top_chain bi l⟩
  unfold realTopValue at hra
  obtain ⟨r0, h0, hra⟩ := realWorld_bind_support prims x s pads u rest _ _ a ra hra
  unfold sourceTopValueX at hrb
  obtain ⟨rb0, hb0, hrb⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb
  obtain ⟨rb1, hb1, hrb⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb
  rw [runX_pure, mem_support_pure_iff] at hrb
  subst hrb
  have hb1' : rb1 ∈ support (runX (compBackend x q s pads u rest noise)
      ((walkCalls (.inr bi) l 0 p.val).mapM (sourcePendingX x.1)) rb0.1.2 rb0.2) := by
    rw [← mapM_walkCalls_top x.1 bi l 0 p.val (fun i => ⟨i.val, by omega⟩)
      (fun i => (Nat.zero_add i.val).symm)]
    exact hb1
  have hvirt := (runX_rows capTag x q s pads (tauOf s pads) (gOf s pads u) noise rest _ _ _ rb1 hb1).1
  have c0 := prfVirtual_sync prims x q s pads u rest noise hkeys cCore p0 a b.1.base b.2 hs.1 ha hb
    hmark r0 (by with_reducible exact h0) rb0 hb0
  have c1 := callPost_trans x q s pads u rest noise cCore _ _ a b.1.base b.2 _ _ r0 rb0 ra rb1 c0
    (fun h => realHonest_stop prims x q s pads u rest _ r0.2 h ra (by with_reducible exact hra))
    (fun h => runX_compStop x q s pads u rest noise _ rb0.1.2 rb0.2 h rb1 hb1)
    (fun hv hs' _ _ hm' => walk_sync prims x q s pads u rest noise hkeys cCore (.inr bi) topLayer
      (topKey bi) l hinput 0 p.val (by omega) r0.1
      (fun _ _ => hv.1.trans (SigningCompilerShare.NoFalse.tau_top_start s pads bi l)) r0.2 rb0.1.2
      rb0.2 hs' hm' ra (by with_reducible exact hra) rb1 hb1')
  rcases c1 with h | h | ⟨⟨hv0, hw⟩, hsF, hfF, hmF⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  have hvalue : ra.1 = ((rb1.1.1.getLast?.map (fun o : DeferredOutput => o.low)).getD
        (DeferredDigest.secret (.topChain bi l ⟨0, by decide⟩))).interpret s ∧
      (∀ h : p.val < 3, (rb1.1.1.getLast?.map (fun o : DeferredOutput => o.low)).getD
        (DeferredDigest.secret (.topChain bi l ⟨0, by decide⟩)) = .secret (.topChain bi l ⟨p.val, h⟩)) ∧
      (p.val = 3 → ∃ w, (rb1.1.1.getLast?.map (fun o : DeferredOutput => o.low)).getD
        (DeferredDigest.secret (.topChain bi l ⟨0, by decide⟩)) = .known w) := by
    cases hl : rb1.1.1.getLast? with
    | none =>
      have hnil := List.getLast?_eq_none_iff.mp hl
      have hp0 : p.val = 0 := by rw [← hw.1, hnil]; rfl
      refine ⟨(hw.2.1 hnil).trans (hv0.1.trans (SigningCompilerShare.NoFalse.tau_top_start s pads bi l)),
        fun h => ?_, fun h => absurd h (by omega)⟩
      exact congrArg DeferredDigest.secret (congrArg (HiddenKey.topChain bi l) (Fin.ext hp0.symm))
    | some last =>
      obtain ⟨hva, hs3, hk3⟩ := hw.2.2.2 last hl
      refine ⟨hva, fun h => ?_, fun h => ?_⟩
      · exact (hs3 (by omega)).trans
          (congrArg DeferredDigest.secret (congrArg (HiddenKey.topChain bi l) (Fin.ext (Nat.zero_add _))))
      · exact hk3 (by omega)
  refine inPost_of_callPost prims x q s pads u rest noise top cCore cTime a b hs _ _ ra _
    (Or.inr (Or.inr ⟨⟨hvalue.1, hrevF, hvalue.2.1, hvalue.2.2, fun T => hvirt (hv0.2.1 T)⟩, hsF, hfF,
      hmF⟩)) hpadsF hrevF ?_ ?_ ?_ ?_
  · rintro e ρ message (⟨T, h⟩ | ⟨p', hp', h⟩)
    · cases h
    · have h' := Query.hash.inj h
      obtain ⟨k, rfl⟩ := mem_walkCalls _ _ _ _ _ hp'
      exact SigningCompilerO1ChainPending.chainInput_ne_randomizer x.1 (l, .inr bi, k) _ bottomLayer e
        ρ message h'.symm
  · rintro p' hnone (⟨T, h⟩ | ⟨p'', hp'', h⟩)
    · cases h
    · have hp' := pendingInput_injective x.1 p' p'' _ _ (Query.hash.inj h)
      subst hp'
      exact hw.2.2.1 p' hp'' hnone
  · rintro T p' (⟨T', h⟩ | ⟨_, _, h⟩)
    · obtain ⟨-, rfl⟩ := Query.prf.inj h
      exact p0.2
    · cases h
  · rintro T e l' d (⟨T', h⟩ | ⟨_, _, h⟩)
    · obtain ⟨hlay, -⟩ := Point.chain.inj (Query.prf.inj h).2
      exact absurd hlay (by decide)
    · cases h

/-- The verification walk of one top chain of a build, from the value of `topValue_sync`. -/
theorem topRecover_sync (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree)
    (cCore cTime : Carried C) (bi : Fin (2 ^ layerHeight)) (l : ChainIndex) (p : Digit)
    (v : Digest) (dv : DeferredDigest) (hv : v = dv.interpret s)
    (hlow : ∀ h : p.val < 3, dv = .secret (.topChain bi l ⟨p.val, h⟩))
    (hend : p.val = 3 → ∃ w, dv = .known w)
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncIn prims x s pads u rest noise top cCore cTime a b)
    (htime : cTime.1.1.bound = cCore.1.1.bound)
    (ha : ¬RealStop q a) (hb : ¬Stop b.2) (hmark : b.2.1.2 = false)
    (ra : Digest × RealState C)
    (hra : ra ∈ support ((realHonest prims x s pads u rest
      (tweakable (Concrete.recoverChain x.1 topLayer (topKey bi) l p v))).run a))
    (rb : (Digest × SourceState C) × CompState C)
    (hrb : rb ∈ support (runX (compBackend x q s pads u rest noise)
      (sourceTopRecoverX x.1 bi l p dv) b.1.base b.2)) :
    InPost prims x q s pads u rest noise top cCore cTime a b (fun rb => rb.1.2.revealed)
      (fun va vb => va = vb ∧ rb.1.2.revealed = b.1.base.revealed) ra rb := by
  have hpadsF := backend_padsFixed x q s pads u rest noise _ b.2 hs.2.2.2 rb hrb
  have hrevF := SourceKeepsX.run (keepsRevealed_topRecover x.1 bi l p dv)
    (compBackend x q s pads u rest noise) b.1.base b.2 rb hrb
  have hp := p.isLt
  have hinput : ∀ (k : ChainStep) (w : Digest),
      tweakableHashInput x.1 (.chain topLayer (topKey bi) k) (Concrete.chainPayload l w) =
        (chainPending (l, .inr bi, k)).input x.1 w := fun k w =>
    (SigningGuessLinkProof.topChainInput_eq_bridge x.1 bi l k w).symm
  have hra' : ra ∈ support ((realHonest prims x s pads u rest (tweakable
      (Concrete.chainWalk x.1 topLayer (topKey bi) l p.val (chainLength - 1 - p.val) v))).run a) := by
    unfold Concrete.recoverChain at hra
    with_reducible exact hra
  unfold sourceTopRecoverX at hrb
  obtain ⟨rb1, hb1, hrb⟩ := runX_bind_support x q s pads u rest noise _ _ _ _ rb hrb
  have hb1' : rb1 ∈ support (runX (compBackend x q s pads u rest noise)
      ((walkCalls (.inr bi) l p.val (chainLength - 1 - p.val)).mapM (sourcePendingX x.1))
      b.1.base b.2) := by
    rw [← mapM_walkCalls_top x.1 bi l p.val _ (fun i => ⟨p.val + i.val, by omega⟩) (fun _ => rfl)]
    exact hb1
  have c := walk_sync prims x q s pads u rest noise hkeys cCore (.inr bi) topLayer (topKey bi) l
    hinput p.val (chainLength - 1 - p.val) (by omega) v
    (fun _ h => hv.trans (by rw [hlow h]; rfl)) a b.1.base b.2 hs.1 hmark ra hra' rb1 hb1'
  rcases c with h | h | ⟨hval, hsF, hfF, hmF⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl (runX_compStop x q s pads u rest noise _ rb1.1.2 rb1.2 h rb hrb))
  have hL : chainLength = 4 := rfl
  obtain ⟨d, hlast, hd⟩ : ∃ d, (rb1.1.1.getLast?.map (·.low)).getD dv = .known d ∧ ra.1 = d := by
    cases hl : rb1.1.1.getLast? with
    | none =>
      have hnil := List.getLast?_eq_none_iff.mp hl
      have hn0 : chainLength - 1 - p.val = 0 := by rw [← hval.1, hnil]; rfl
      obtain ⟨w, hw⟩ := hend (by omega)
      exact ⟨w, by simp [hw], by rw [hval.2.1 hnil, hv, hw]; rfl⟩
    | some last =>
      obtain ⟨hva, -, hknown⟩ := hval.2.2.2 last hl
      obtain ⟨d, hd⟩ := hknown (by omega)
      exact ⟨d, by simp [hd], by rw [hva, hd]; rfl⟩
  simp only [hlast] at hrb
  rw [runX_pure, mem_support_pure_iff] at hrb
  subst hrb
  refine inPost_of_callPost prims x q s pads u rest noise top cCore cTime a b hs _ _ ra
    ((d, rb1.1.2), rb1.2) (Or.inr (Or.inr ⟨⟨hd, hrevF⟩, hsF, hfF, hmF⟩)) hpadsF hrevF ?_ ?_ ?_ ?_
  · rintro e ρ message ⟨p', hp', h⟩
    have h' := Query.hash.inj h
    obtain ⟨k, rfl⟩ := mem_walkCalls _ _ _ _ _ hp'
    exact SigningCompilerO1ChainPending.chainInput_ne_randomizer x.1 (l, .inr bi, k) _ bottomLayer e
      ρ message h'.symm
  · rintro p' hnone ⟨p'', hp'', h⟩
    have hp' := pendingInput_injective x.1 p' p'' _ _ (Query.hash.inj h)
    subst hp'
    exact hval.2.2.1 p' hp'' hnone
  · rintro T p' ⟨_, _, h⟩
    cases h
  · rintro T e l' d' ⟨_, _, h⟩
    cases h

end Build

end ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.keepsRevealed_virtual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.keepsRevealed_virtual

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.keepsRevealed_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.keepsRevealed_pending

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.mem_walkCalls' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.mem_walkCalls

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.walkCalls_eq_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.walkCalls_eq_map

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.mapM_walkCalls_top' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.mapM_walkCalls_top

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.keepsRevealed_topRecover' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.keepsRevealed_topRecover

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.keepsRevealed_topValue' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.keepsRevealed_topValue

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.chainPending_next_some' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.chainPending_next_some

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.chainPending_next_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.chainPending_next_none

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.truncateHash_interpret' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.truncateHash_interpret

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.chainWalk_step' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.chainWalk_step

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.tweakable_tweakableHash' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.tweakable_tweakableHash

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.mapM_snoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.mapM_snoc

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.exists_getLast' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.exists_getLast

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.tau_row_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.tau_row_start

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.tau_row_pad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.tau_row_pad

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.bottomRowCalls_walks' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.bottomRowCalls_walks

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.mem_bottomRowCalls' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.mem_bottomRowCalls

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.sourceBottomRowX_walks' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.sourceBottomRowX_walks

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.keepsRevealed_row' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.keepsRevealed_row

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.callPost_trans' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.callPost_trans

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.callPost_weaken' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.callPost_weaken

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.realWorld_bind_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.realWorld_bind_support

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.pad_sync' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.pad_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.walk_sync' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.walk_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.inPost_of_callPost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.inPost_of_callPost

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.row_sync' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.row_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.topValue_sync' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.topValue_sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.topRecover_sync' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1BuildSteps.topRecover_sync
