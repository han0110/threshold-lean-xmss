import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareNoFalse

/-!
# The real signing trace over constrained and free tables

The coordinate swap retains old aggregates in their original target slots.
The real source reads the resulting share table and the installed chain cache;
its complete traced outcome and original query count remain joint.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss ENNReal
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerRealTables
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

abbrev RestSlot (C : Committee) :=
  {z : TprfSecurityProof.Slot C // ∀ T (p : CPoint), z ≠ .inl (T, p.val)}

private theorem rest_inl (T : C.Term) (p : Point) (h : ¬Constrained p) :
    ∀ U (q : CPoint), (Sum.inl (T, p) : TprfSecurityProof.Slot C) ≠ .inl (U, q.val) := by
  intro U q he
  have hp : p = q.val := (Prod.mk.inj (Sum.inl.inj he)).2
  exact h (hp ▸ q.property)

/-- Join a constrained table and all remaining slots. -/
def realTable (g : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) :
    TprfSecurityProof.Slot C → HashOutput
  | .inl (T, p) => if h : Constrained p then g (T, ⟨p, h⟩)
      else rest ⟨.inl (T, p), rest_inl T p h⟩
  | .inr m => rest ⟨.inr m, by intros; simp⟩

@[simp] theorem realTable_constrained (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (T : C.Term) (p : CPoint) :
    realTable g rest (.inl (T, p.val)) = g (T, p) := by
  simp [realTable, p.property]

@[simp] theorem realTable_rest (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (z : RestSlot C) :
    realTable g rest z.val = rest z := by
  rcases z with ⟨(⟨T, p⟩ | m), hz⟩
  · have hp : ¬Constrained p := fun hp => hz T ⟨p, hp⟩ rfl
    simp [realTable, hp]
  · rfl

/-- Split the entire private table without dropping any slot. -/
def slotSplit : (TprfSecurityProof.Slot C → HashOutput) ≃
    (C.Term × CPoint → HashOutput) × (RestSlot C → HashOutput) where
  toFun t := (fun y => t (.inl (y.1, y.2.val)), fun z => t z.val)
  invFun pair := realTable pair.1 pair.2
  left_inv t := by
    funext z
    rcases z with ⟨T, p⟩ | m
    · by_cases hp : Constrained p <;> simp [realTable, hp]
    · rfl
  right_inv pair := by
    apply Prod.ext
    · funext y; exact realTable_constrained pair.1 pair.2 y.1 y.2
    · funext z; exact realTable_rest pair.1 pair.2 z

def installed (s : HiddenKey → Digest) (F : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) : PrfChainTables :=
  installHiddenCoordinates (maskPrfChainTables s (F, noiseLabels noise)) s

def theta (s : HiddenKey → Digest) (F : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) : Point → Digest :=
  refreshChainStarts (installed s F noise).1
    (XmssSecurity.CappedChain.globalChainTableSeedTargets (installed s F noise).2)

def realCache (x : Keys3 C) (s : HiddenKey → Digest) (pads : Point → Digest)
    (noise : ChainNoiseIndex → HashOutput) :=
  embedHashCache (C := C) (chainTableCache x.1 (installed s pads noise).2 (noiseHigh noise))

def realRunRaw (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (s : HiddenKey → Digest) (pads : Point → Digest) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput) :=
  (simulateQ SigningGuessProof.privateRoImpl
    (simulateQ (resolveSlots x.2.1 x.2.2 (realTable g rest))
      (rawTraceProgram prims A x))).run (realCache x s pads noise)

def realRun (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (s : HiddenKey → Digest) (pads : Point → Digest) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput) :=
  Prod.fst <$> realRunRaw prims A x s pads g rest noise

theorem installed_snd_congr (s s' : HiddenKey → Digest) (F F' : Point → Digest)
    (n : ChainNoiseIndex → HashOutput)
    (hb : ∀ e l p, s (.bottomChain e l p) = s' (.bottomChain e l p))
    (ht : ∀ b l p, s (.topChain b l p) = s' (.topChain b l p)) :
    (installed s F n).2 = (installed s' F' n).2 := by
  funext index
  rcases index with ⟨l, key, p⟩
  cases key <;> simp [installed, installHiddenCoordinates, maskPrfChainTables, hb, ht]

theorem chainStart_constrained (i : XmssSecurity.ChainKey × ChainIndex) :
    Constrained (chainStartPoint i) := by
  rcases i with ⟨e | b, l⟩
  · exact constrained_bottom_chain e l _ (by decide)
  · exact constrained_top_chain b l

def freeTarget (s : HiddenKey → Digest) (F : Point → Digest) : Point → Digest
  | .randomizer lay e => s (.opening lay e)
  | .chain lay e l p => F (.chain lay e l p)

theorem theta_free (s : HiddenKey → Digest) (F : Point → Digest)
    (n : ChainNoiseIndex → HashOutput) (p : Point) (hp : ¬Constrained p) :
    theta s F n p = freeTarget s F p := by
  have hn : ¬∃ i, chainStartPoint i = p := by
    rintro ⟨i, rfl⟩; exact hp (chainStart_constrained i)
  simp only [theta, refreshChainStarts, dif_neg hn]
  cases p with
  | randomizer lay e => rfl
  | chain lay e l d =>
      have hoff : bottomPrfOffset s (.chain lay e l d) = 0 := by
        by_cases hl : lay = bottomLayer
        · have hd : ¬d.val < 3 := fun hd => hp (Or.inl ⟨hl, hd⟩)
          simp [bottomPrfOffset, hl, show d.val ≠ 1 by omega, show d.val ≠ 2 by omega]
        · simp [bottomPrfOffset, hl]
      simp [installed, installHiddenCoordinates, maskPrfChainTables, hoff, freeTarget]

private theorem theta_start (s : HiddenKey → Digest) (F : Point → Digest)
    (n : ChainNoiseIndex → HashOutput) (i : XmssSecurity.ChainKey × ChainIndex) :
    theta s F n (chainStartPoint i) = match i.1 with
      | .inl e => s (.bottomChain e i.2 ⟨0, by decide⟩)
      | .inr b => s (.topChain b i.2 ⟨0, by decide⟩) := by
  have h := congrFun (congrFun (refreshChainStarts_value (installed s F n).1
    (XmssSecurity.CappedChain.globalChainTableSeedTargets (installed s F n).2)) i.1) i.2
  rw [prfChainStarts_point _ i] at h
  rw [theta, h]
  rcases i with ⟨e | b, l⟩ <;>
    simp [XmssSecurity.CappedChain.globalChainTableSeedTargets, installed,
      installHiddenCoordinates, maskPrfChainTables, XmssSecurity.chainLength,
      XmssSecurity.winternitzBits]

theorem theta_constrained (s : HiddenKey → Digest) (F : Point → Digest)
    (n : ChainNoiseIndex → HashOutput) (p : CPoint) :
    theta s F n p.val = NoFalse.tau s F p := by
  induction p using NoFalse.constrained_cases with
  | ho e =>
      have hn : ¬∃ i, chainStartPoint i = .randomizer bottomLayer e := by
        rintro ⟨⟨k, l⟩, h⟩; cases k <;> cases h
      simp [theta, refreshChainStarts, hn, installed, installHiddenCoordinates,
        NoFalse.tau]
  | hto b =>
      have hn : ¬∃ i, chainStartPoint i = .randomizer topLayer (topKey b) := by
        rintro ⟨⟨k, l⟩, h⟩; cases k <;> cases h
      simp [theta, refreshChainStarts, hn, installed, installHiddenCoordinates,
        NoFalse.tau]
  | htc b l =>
      rw [NoFalse.tau_top_start]
      exact theta_start s F n (.inr b, l)
  | hc e l pos =>
      rw [NoFalse.tau_bottom_chain]
      by_cases hz : pos.val = 0
      · have he : pos = ⟨0, by decide⟩ := Fin.ext hz
        subst pos
        simpa [XmssSecurity.CappedChain.chainStepDigit, chainStartPoint, digit] using
          theta_start s F n (.inl e, l)
      · have hn : ¬∃ i, chainStartPoint i =
            .chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos) := by
          rintro ⟨⟨k, l'⟩, h⟩
          have hd := congrArg (fun p : Point => match p with
            | .chain _ _ _ d => d.val | .randomizer .. => 0) h
          cases k <;> simp [chainStartPoint, digit,
            XmssSecurity.CappedChain.chainStepDigit] at hd
          all_goals omega
        fin_cases pos <;>
          simp_all [theta, refreshChainStarts, installed, installHiddenCoordinates,
            maskPrfChainTables, bottomPrfOffset, XmssSecurity.CappedChain.chainStepDigit,
            BitVec.xor_comm, chainLength, winternitzBits]

theorem refreshAllPrf_inl (b : C.Term) (t : TprfSecurityProof.Slot C → HashOutput)
    (θ : Point → Digest) (T : C.Term) (p : Point) :
    refreshAllPrf b t θ (.inl (T, p)) = if T = b then
      t (.inl (b, p)) ^^^ (TprfSecurityProof.prfSum t p +
        TprfCorrectnessProof.toXor (θ p)).setWidth hashOutputBits else t (.inl (T, p)) := by
  by_cases h : T = b <;>
    simp [refreshAllPrf, TprfSecurityProof.shiftTable, TprfSecurityProof.shiftOf, h]

@[simp] theorem refreshAllPrf_inr (b : C.Term) (t : TprfSecurityProof.Slot C → HashOutput)
    (θ : Point → Digest) (m : C.Pair × Point × Message × C.Quorum) :
    refreshAllPrf b t θ (.inr m) = t (.inr m) := by
  simp [refreshAllPrf, TprfSecurityProof.shiftTable, TprfSecurityProof.shiftOf,
    TprfSecurityProof.Shifted, TprfSecurityProof.recordQueriers]

def freeTheta (sh : TprfSecurityProof.Slot C → HashOutput)
    (F : Point → Digest) (s : HiddenKey → Digest) (p : Point) : Digest :=
  if Constrained p then tablePrf sh p else freeTarget s F p

def freePads (sh : TprfSecurityProof.Slot C → HashOutput) (F : Point → Digest) : Point → Digest
  | .randomizer lay e => F (.randomizer lay e)
  | .chain lay e l d => if Constrained (.chain lay e l d) then F (.chain lay e l d)
      else tablePrf sh (.chain lay e l d)

def freeSecrets (sh : TprfSecurityProof.Slot C → HashOutput)
    (s : HiddenKey → Digest) : HiddenKey → Digest
  | .opening lay e => if Constrained (.randomizer lay e) then s (.opening lay e)
      else tablePrf sh (.randomizer lay e)
  | .bottomChain e l p => s (.bottomChain e l p)
  | .topChain b l p => s (.topChain b l p)

/-- Preserve each overwritten aggregate in its actual target coordinate. -/
def swapFree (b : C.Term)
    (z : (TprfSecurityProof.Slot C → HashOutput) × (Point → Digest) × (HiddenKey → Digest)) :=
  (refreshAllPrf b z.1 (freeTheta z.1 z.2.1 z.2.2),
    freePads z.1 z.2.1, freeSecrets z.1 z.2.2)

theorem freeTarget_swap (sh : TprfSecurityProof.Slot C → HashOutput)
    (F : Point → Digest) (s : HiddenKey → Digest) (p : Point) (hp : ¬Constrained p) :
    freeTarget (freeSecrets sh s) (freePads sh F) p = tablePrf sh p := by
  cases p <;> simp [freeTarget, freeSecrets, freePads, hp]

theorem swapFree_involutive (b : C.Term) : Function.Involutive (swapFree b) := by
  rintro ⟨sh, F, s⟩
  have hv := refreshAllPrf_value b sh (freeTheta sh F s)
  have hθ : freeTheta (refreshAllPrf b sh (freeTheta sh F s))
      (freePads sh F) (freeSecrets sh s) = tablePrf sh := by
    funext p
    by_cases hp : Constrained p
    · simp [freeTheta, hp, congrFun hv p]
    · simp [freeTheta, hp, freeTarget_swap sh F s p hp]
  apply Prod.ext
  · change refreshAllPrf b (refreshAllPrf b sh (freeTheta sh F s))
      (freeTheta (refreshAllPrf b sh (freeTheta sh F s)) (freePads sh F) (freeSecrets sh s)) = sh
    rw [hθ, refreshAllPrf_twice]
  · apply Prod.ext
    · funext p
      cases p with
      | randomizer lay e => rfl
      | chain lay e l d =>
        dsimp only [swapFree]
        by_cases hp : Constrained (.chain lay e l d) <;>
          simp [freePads, hp, congrFun hv, freeTheta, freeTarget]
    · funext k
      cases k with
      | bottomChain e l p => rfl
      | topChain b l p => rfl
      | opening lay e =>
        dsimp only [swapFree]
        by_cases hp : Constrained (.randomizer lay e) <;>
          simp [freeSecrets, hp, congrFun hv, freeTheta, freeTarget]

theorem tau_congr (s s' : HiddenKey → Digest) (F F' : Point → Digest)
    (ho : ∀ lay e, Constrained (.randomizer lay e) →
      s (.opening lay e) = s' (.opening lay e))
    (hb : ∀ e l p, s (.bottomChain e l p) = s' (.bottomChain e l p))
    (ht : ∀ b l p, s (.topChain b l p) = s' (.topChain b l p))
    (hF : ∀ p : CPoint, F p.val = F' p.val) :
    NoFalse.tau s F = NoFalse.tau s' F' := by
  funext p
  induction p using NoFalse.constrained_cases with
  | ho e => exact ho _ e (constrained_bottom_randomizer e)
  | hto b => exact ho _ _ (constrained_top_randomizer b)
  | htc b l => simp only [NoFalse.tau_top_start, ht]
  | hc e l pos =>
      have hp := hF ⟨.chain bottomLayer e l (XmssSecurity.CappedChain.chainStepDigit pos),
        constrained_bottom_chain e l (XmssSecurity.CappedChain.chainStepDigit pos) pos.isLt⟩
      simp only [NoFalse.tau_bottom_chain, hb, hp]

theorem tau_swap (sh : TprfSecurityProof.Slot C → HashOutput)
    (F : Point → Digest) (s : HiddenKey → Digest) :
    NoFalse.tau (freeSecrets sh s) (freePads sh F) = NoFalse.tau s F := by
  funext p
  induction p using NoFalse.constrained_cases with
  | ho e => simp [NoFalse.tau_bottom_opening, freeSecrets]
  | hto b => simp [NoFalse.tau_top_opening, freeSecrets]
  | htc b l => simp [NoFalse.tau_top_start, freeSecrets]
  | hc e l pos =>
      have hp := constrained_bottom_chain e l
        (XmssSecurity.CappedChain.chainStepDigit pos) pos.isLt
      simp [NoFalse.tau_bottom_chain, freeSecrets, freePads, hp]

/-- XOR by an extended digest preserves the high half of the full output. -/
theorem xor_setWidth_pair (v : HashOutput) (d : XmssSecurity.Digest) :
    v ^^^ d.setWidth hashOutputBits = SigningShareLazy.pair.symm
      ((SigningShareLazy.pair v).1, (SigningShareLazy.pair v).2 ^^^ d) := by
  apply SigningShareLazy.pair.injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · change (v ^^^ d.setWidth hashOutputBits).extractLsb' digestBits digestBits =
      v.extractLsb' digestBits digestBits
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, BitVec.getLsbD_setWidth]
    have hd : d.getLsbD (digestBits + k) = false :=
      BitVec.getLsbD_of_ge d _ (by change digestBits ≤ digestBits + k; omega)
    simp [hk, hd]
  · exact TprfSecurityProof.truncateHash_xor_setWidth v d

private theorem tablePrf_split (t : TprfSecurityProof.Slot C → HashOutput)
    (p : Point) (b : C.Term) : tablePrf t p =
      otherTermSum (fun T => truncateHash (t (.inl (T, p)))) b ^^^
        truncateHash (t (.inl (b, p))) := by
  change TprfSecurityProof.prfSum t p =
    TprfCorrectnessProof.toXor (otherTermSum (fun T => truncateHash (t (.inl (T, p)))) b) +
      TprfCorrectnessProof.toXor (truncateHash (t (.inl (b, p))))
  exact (Finset.sum_erase_add _ _ (Finset.mem_univ b)).symm

theorem refresh_constrained_fiber {B : Type} (b : C.Term) (bs : List C.Term)
    (hb : C.terms = b :: bs) (t : TprfSecurityProof.Slot C → HashOutput)
    (θ : Point → Digest) (τ : CPoint → Digest) (T : C.Term) (p : CPoint)
    (hθ : θ p.val = τ p) :
    refreshAllPrf b t θ (.inl (T, p.val)) =
      SigningShareLazy.fiberTable C.terms τ (SigningShareLazy.init (B := B))
        (slotSplit t).1 (T, p) := by
  rw [refreshAllPrf_inl, hb, SigningShareLazy.fiberTable_init_cons]
  by_cases hT : T = b
  · subst T
    simp only [↓reduceIte]
    change t (.inl (b, p.val)) ^^^ (tablePrf t p.val ^^^ θ p.val).setWidth hashOutputBits = _
    rw [xor_setWidth_pair, ← hb, xorSum_otherTerms]
    apply congrArg (SigningShareLazy.pair.symm)
    apply Prod.ext
    · rfl
    change truncateHash (t (.inl (b, p.val))) ^^^ (tablePrf t p.val ^^^ θ p.val) = _
    rw [hθ, tablePrf_split t p.val b, ← BitVec.xor_assoc]
    change truncateHash (t (.inl (b, p.val))) ^^^
      ((otherTermSum (fun T => truncateHash (t (.inl (T, p.val)))) b ^^^
        truncateHash (t (.inl (b, p.val))))) ^^^ τ p = _
    rw [BitVec.xor_comm (otherTermSum _ b), ← BitVec.xor_assoc]
    simp [BitVec.xor_comm, slotSplit, SigningShareLazy.lowHash]
    rfl
  · simp [hT, slotSplit]

theorem swap_constrained (b : C.Term) (sh : TprfSecurityProof.Slot C → HashOutput)
    (F : Point → Digest) (s : HiddenKey → Digest) (T : C.Term) (p : CPoint) :
    refreshAllPrf b sh (freeTheta sh F s) (.inl (T, p.val)) = sh (.inl (T, p.val)) := by
  rw [refreshAllPrf_inl]
  by_cases h : T = b
  · subst T
    simp only [↓reduceIte, freeTheta, p.property, ↓reduceIte]
    change sh (.inl (b, p.val)) ^^^ (tablePrf sh p.val ^^^ tablePrf sh p.val).setWidth _ = _
    simp
  · simp [h]

/-- Replaying the swapped coordinates produces precisely the independent rest
table and the constrained fiber table of the original coordinates. -/
theorem swap_table {B : Type} (b : C.Term) (bs : List C.Term)
    (hb : C.terms = b :: bs) (sh : TprfSecurityProof.Slot C → HashOutput)
    (F : Point → Digest) (s : HiddenKey → Digest) (n : ChainNoiseIndex → HashOutput) :
    refreshAllPrf b (swapFree b (sh, F, s)).1
      (theta (swapFree b (sh, F, s)).2.2 (swapFree b (sh, F, s)).2.1 n) =
    realTable (SigningShareLazy.fiberTable C.terms (NoFalse.tau s F)
      (SigningShareLazy.init (B := B)) (slotSplit sh).1) (slotSplit sh).2 := by
  funext z
  rcases z with ⟨T, p⟩ | m
  · by_cases hp : Constrained p
    · let cp : CPoint := ⟨p, hp⟩
      dsimp only [swapFree]
      rw [show p = cp.val from rfl, realTable_constrained,
        refresh_constrained_fiber b bs hb _ _ _ T cp
          ((theta_constrained _ _ n cp).trans (congrFun (tau_swap sh F s) cp))]
      congr 1
      funext y
      exact swap_constrained b sh F s y.1 y.2
    · have hv := congrFun (refreshAllPrf_value b sh (freeTheta sh F s)) p
      have ht : theta (freeSecrets sh s) (freePads sh F) n p = tablePrf sh p :=
        (theta_free _ _ n p hp).trans (freeTarget_swap sh F s p hp)
      dsimp only [swapFree]
      rw [refreshAllPrf_inl, ht]
      by_cases hT : T = b
      · subst T
        simp only [↓reduceIte]
        change refreshAllPrf b sh (freeTheta sh F s) (.inl (b, p)) ^^^
          (tablePrf (refreshAllPrf b sh (freeTheta sh F s)) p ^^^ tablePrf sh p).setWidth _ = _
        rw [hv, refreshAllPrf_inl]
        simp only [↓reduceIte]
        change sh (.inl (b, p)) ^^^ (tablePrf sh p ^^^ freeTheta sh F s p).setWidth _ ^^^
          (freeTheta sh F s p ^^^ tablePrf sh p).setWidth _ = _
        rw [BitVec.xor_comm (freeTheta sh F s p) (tablePrf sh p)]
        simp [realTable, hp, slotSplit, BitVec.xor_assoc]
      · simp [hT, refreshAllPrf_inl, realTable, hp, slotSplit]
  · simp [swapFree, realTable, slotSplit]

theorem realCache_swap (x : Keys3 C) (sh : TprfSecurityProof.Slot C → HashOutput)
    (F : Point → Digest) (s : HiddenKey → Digest) (n : ChainNoiseIndex → HashOutput) :
    realCache x (freeSecrets sh s) (freePads sh F) n = realCache x s F n := by
  unfold realCache
  rw [installed_snd_congr (freeSecrets sh s) s (freePads sh F) F n
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)]

theorem eagerTraceRaw_swap {B : Type} (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (b : C.Term) (bs : List C.Term) (hb : C.terms = b :: bs)
    (sh : TprfSecurityProof.Slot C → HashOutput) (F : Point → Digest)
    (s : HiddenKey → Digest) (n : ChainNoiseIndex → HashOutput) :
    (simulateQ SigningGuessProof.privateRoImpl
      (simulateQ (resolveSlots x.2.1 x.2.2
        (refreshAllPrf b (swapFree b (sh, F, s)).1
          (theta (swapFree b (sh, F, s)).2.2 (swapFree b (sh, F, s)).2.1 n)))
        (rawTraceProgram prims A x))).run
      (realCache x (swapFree b (sh, F, s)).2.2 (swapFree b (sh, F, s)).2.1 n) =
    realRunRaw prims A x s F
      (SigningShareLazy.fiberTable C.terms (NoFalse.tau s F)
        (SigningShareLazy.init (B := B)) (slotSplit sh).1) (slotSplit sh).2 n := by
  rw [swap_table (B := B) b bs hb]
  rw [show realCache x (swapFree b (sh, F, s)).2.2 (swapFree b (sh, F, s)).2.1 n =
      realCache x s F n from realCache_swap x sh F s n]
  rfl

theorem eagerTrace_swap {B : Type} (prims : Primitives) (A : TsigAdversary C)
    (x : Keys3 C) (b : C.Term) (bs : List C.Term) (hb : C.terms = b :: bs)
    (sh : TprfSecurityProof.Slot C → HashOutput) (F : Point → Digest)
    (s : HiddenKey → Digest) (n : ChainNoiseIndex → HashOutput) :
    eagerTrace prims A x b (swapFree b (sh, F, s)).1
      (installed (swapFree b (sh, F, s)).2.2 (swapFree b (sh, F, s)).2.1 n)
      (noiseHigh n) =
    realRun prims A x s F
      (SigningShareLazy.fiberTable C.terms (NoFalse.tau s F)
        (SigningShareLazy.init (B := B)) (slotSplit sh).1) (slotSplit sh).2 n :=
  congrArg (fun m => Prod.fst <$> m) (eagerTraceRaw_swap (B := B) prims A x b bs hb sh F s n)

private theorem uniform_prod_bind {α β γ : Type} [Fintype α] [Fintype β]
    [SampleableType α] [SampleableType β] (next : α → β → ProbComp γ) :
    𝒟[do let a ← $ᵗ α; let b ← $ᵗ β; next a b] =
      𝒟[($ᵗ (α × β)) >>= fun z => next z.1 z.2] := by
  have h := congrArg (fun d => d >>= fun z => 𝒟[next z.1 z.2])
    (XmssSecurity.evalDist_independent_uniform_pair (α := α) (β := β))
  simpa only [← evalDist_bind, bind_assoc, pure_bind] using h

private theorem uniform_triple_bind {α β γ δ : Type} [Fintype α] [Fintype β]
    [Fintype γ] [SampleableType α] [SampleableType β] [SampleableType γ]
    (next : α → β → γ → ProbComp δ) :
    𝒟[do let c ← $ᵗ γ; let a ← $ᵗ α; let b ← $ᵗ β; next a b c] =
      𝒟[($ᵗ (α × β × γ)) >>= fun z => next z.1 z.2.1 z.2.2] := by
  calc
    _ = 𝒟[do let a ← $ᵗ α; let c ← $ᵗ γ; let b ← $ᵗ β; next a b c] :=
      OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[do let a ← $ᵗ α; let b ← $ᵗ β; let c ← $ᵗ γ; next a b c] := by
      apply evalDist_bind_congr
      intro a _
      exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
    _ = 𝒟[do let a ← $ᵗ α; let bc ← $ᵗ (β × γ); next a bc.1 bc.2] := by
      apply evalDist_bind_congr
      intro a _
      exact uniform_prod_bind (next a)
    _ = _ := uniform_prod_bind _

/-- Exact joint law of the original trace, with independent free slots and a
fiber table at every constrained point. -/
theorem traceRun_eq_realRun (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) :
    𝒟[SigningLaneUnionProof.traceRun prims A x] =
    𝒟[do
      let s ← $ᵗ (HiddenKey → Digest)
      let pads ← $ᵗ (Point → Digest)
      let u ← $ᵗ (C.Term × CPoint → HashOutput)
      let rest ← $ᵗ (RestSlot C → HashOutput)
      let noise ← $ᵗ (ChainNoiseIndex → HashOutput)
      realRun prims A x s pads (SigningShareLazy.fiberTable C.terms (NoFalse.tau s pads)
        (SigningShareLazy.init : Table.FrozenState C) u) rest noise] := by
  obtain ⟨T, _⟩ := lackedTerm_empty (C := C)
  obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem (mem_terms T))
  rw [traceRun_eq_symbolic_noise prims A x hkeys b]
  let old := fun (sh : TprfSecurityProof.Slot C → HashOutput) (F : Point → Digest)
      (s : HiddenKey → Digest) => do
    let n ← $ᵗ (ChainNoiseIndex → HashOutput)
    eagerTrace prims A x b sh (installed s F n) (noiseHigh n)
  let new := fun (sh : TprfSecurityProof.Slot C → HashOutput) (F : Point → Digest)
      (s : HiddenKey → Digest) => do
    let n ← $ᵗ (ChainNoiseIndex → HashOutput)
    realRun prims A x s F (SigningShareLazy.fiberTable C.terms (NoFalse.tau s F)
      (SigningShareLazy.init : Table.FrozenState C) (slotSplit sh).1) (slotSplit sh).2 n
  change 𝒟[do let s ← $ᵗ (HiddenKey → Digest)
               let sh ← $ᵗ (TprfSecurityProof.Slot C → HashOutput)
               let F ← $ᵗ (Point → Digest); old sh F s] = _
  rw [uniform_triple_bind old]
  have hu := evalDist_map_bijective_uniform_cross
    (α := (TprfSecurityProof.Slot C → HashOutput) × (Point → Digest) × (HiddenKey → Digest))
    (swapFree b) (swapFree_involutive b).bijective
  have hm := congrArg (fun d => d >>= fun z => 𝒟[old z.1 z.2.1 z.2.2]) hu
  simp only [← evalDist_bind, bind_map_left] at hm
  rw [← hm]
  trans 𝒟[($ᵗ ((TprfSecurityProof.Slot C → HashOutput) × (Point → Digest) ×
    (HiddenKey → Digest))) >>= fun z => new z.1 z.2.1 z.2.2]
  · apply evalDist_bind_congr
    rintro ⟨sh, F, s⟩ _
    apply evalDist_bind_congr
    intro n _
    rw [eagerTrace_swap (B := SigningShareLazy.FrozenBad Bool) prims A x b bs hb]
  rw [← uniform_triple_bind new]
  apply evalDist_bind_congr
  intro s _
  trans 𝒟[do let F ← $ᵗ (Point → Digest)
             let sh ← $ᵗ (TprfSecurityProof.Slot C → HashOutput); new sh F s]
  · exact OracleComp.DeferredSampling.evalDist_bind_comm _ _ _
  apply evalDist_bind_congr
  intro F _
  have hs := evalDist_map_bijective_uniform_cross (α := TprfSecurityProof.Slot C → HashOutput)
    (slotSplit (C := C)) slotSplit.bijective
  have hs' := congrArg (fun d => d >>= fun pair =>
    𝒟[new (slotSplit.symm pair) F s]) hs
  simp only [← evalDist_bind, bind_map_left, Equiv.symm_apply_apply] at hs'
  rw [hs', ← uniform_prod_bind (fun u rest => new (slotSplit.symm (u, rest)) F s)]
  simp only [new, Equiv.apply_symm_apply]

set_option linter.constructorNameAsVariable false in
/-- Every fixed sampled table obeys the original support-wise query budget. -/
theorem realRun_count_le (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (gameAfter A x)), r.2 ≤ q)
    (s : HiddenKey → Digest) (pads : Point → Digest) (u : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)
    (r : SigningLaneUnionProof.TraceOutcome C)
    (hr : r ∈ support (realRun prims A x s pads
      (SigningShareLazy.fiberTable C.terms (NoFalse.tau s pads)
        (SigningShareLazy.init : Table.FrozenState C) u) rest noise)) :
    (SigningLaneUnionProof.observed r).2.1 ≤ q := by
  apply SigningLaneUnionProof.traceRun_count_le prims A q x hq r
  rw [← mem_support_evalDist_iff, traceRun_eq_realRun prims A x hkeys,
    mem_support_evalDist_iff, mem_support_bind_iff]
  refine ⟨s, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨pads, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨u, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨rest, by simp, ?_⟩
  rw [mem_support_bind_iff]
  refine ⟨noise, by simp, ?_⟩
  with_reducible exact hr

set_option linter.constructorNameAsVariable false in
theorem realRunRaw_count_le (prims : Primitives) (A : TsigAdversary C) (x : Keys3 C)
    (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (q : ℕ)
    (hq : ∀ r ∈ support (runSigningWorld prims (gameAfter A x)), r.2 ≤ q)
    (s : HiddenKey → Digest) (pads : Point → Digest) (u : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)
    (r : SigningLaneUnionProof.TraceOutcome C × HashCache C)
    (hr : r ∈ support (realRunRaw prims A x s pads
      (SigningShareLazy.fiberTable C.terms (NoFalse.tau s pads)
        (SigningShareLazy.init : Table.FrozenState C) u) rest noise)) :
    (SigningLaneUnionProof.observed r.1).2.1 ≤ q := by
  apply realRun_count_le prims A x hkeys q hq s pads u rest noise r.1
  rw [realRun, support_map, Set.mem_image]
  refine ⟨r, ?_, rfl⟩
  with_reducible exact hr

end ThresholdLeanXmssSecurity.SigningCompilerRealTables

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerRealTables.swapFree_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerRealTables.swapFree_involutive

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerRealTables.theta_constrained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerRealTables.theta_constrained

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerRealTables.refresh_constrained_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerRealTables.refresh_constrained_fiber

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerRealTables.swap_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerRealTables.swap_table

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerRealTables.eagerTraceRaw_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerRealTables.eagerTraceRaw_swap

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerRealTables.traceRun_eq_realRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerRealTables.traceRun_eq_realRun

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerRealTables.realRun_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerRealTables.realRun_count_le

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerRealTables.realRunRaw_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerRealTables.realRunRaw_count_le
