import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncTreeRows

/-! # Source control and stored bottom-tree row preservation

Structural ports of SigningCompilerCoupling.SourceKeeps and its sourceControl
lemmas to SourceMX; their oracle answers and control fields are unchanged.
-/
open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningCompilerCouplingProof SigningCompilerShare SigningCompilerShareTag
open SigningCompilerShareTables SigningCompilerRealTables
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeRows
variable {C : Committee} {Tag : Type}
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
set_option linter.constructorNameAsVariable false

def SourceKeepsX {α β : Type} (field : SourceState C → β) (oa : SourceMX C α) : Prop :=
  ∀ source r, r ∈ support (oa.run source) → field r.2 = field source

theorem SourceKeepsX.pure {α β : Type} {field : SourceState C → β} (value : α) :
    SourceKeepsX field (pure value) := by
  intro source r hr
  simp only [StateT.run_pure, mem_support_pure_iff] at hr
  subst r
  rfl

theorem SourceKeepsX.get {β : Type} {field : SourceState C → β} :
    SourceKeepsX field (get : SourceMX C (SourceState C)) := by
  intro source r hr
  simp only [StateT.run_get, mem_support_pure_iff] at hr
  subst r
  rfl

theorem SourceKeepsX.modify {β : Type} {field : SourceState C → β}
    (f : SourceState C → SourceState C) (hf : ∀ source, field (f source) = field source) :
    SourceKeepsX field (modify f : SourceMX C Unit) := by
  intro source r hr
  simp only [StateT.run_modify, mem_support_pure_iff] at hr
  subst r
  exact hf source

theorem SourceKeepsX.lift {α β : Type} {field : SourceState C → β}
    (oa : OracleComp (SpecX C) α) :
    SourceKeepsX field (liftM oa : SourceMX C α) := by
  intro source r hr
  change r ∈ support (oa >>= fun value => Pure.pure (value, source)) at hr
  simp only [mem_support_bind_iff, mem_support_pure_iff] at hr
  obtain ⟨_, _, rfl⟩ := hr
  rfl

theorem SourceKeepsX.bind {α β γ : Type} {field : SourceState C → γ}
    {oa : SourceMX C α} (h : SourceKeepsX field oa) (next : α → SourceMX C β)
    (hn : ∀ value, SourceKeepsX field (next value)) : SourceKeepsX field (oa >>= next) := by
  intro source r hr
  simp only [StateT.run_bind, mem_support_bind_iff] at hr
  obtain ⟨a, ha, hr⟩ := hr
  exact (hn a.1 a.2 r hr).trans (h source a ha)

theorem SourceKeepsX.mapM {α β γ : Type} {field : SourceState C → γ}
    (items : List α) (oa : α → SourceMX C β)
    (h : ∀ a ∈ items, SourceKeepsX field (oa a)) : SourceKeepsX field (items.mapM oa) := by
  induction items with
  | nil => exact SourceKeepsX.pure []
  | cons a items ih =>
      rw [List.mapM_cons]
      refine (h a (List.mem_cons_self ..)).bind _ fun value => ?_
      exact (ih (fun b hb => h b (List.mem_cons_of_mem _ hb))).bind _
        (fun values => SourceKeepsX.pure (value :: values))

theorem SourceKeepsX.sequenceFin {α β : Type} {field : SourceState C → β} :
    ∀ n (oa : Fin n → SourceMX C α), (∀ i, SourceKeepsX field (oa i)) →
      SourceKeepsX field (Concrete.sequenceFin oa) := by
  intro n
  induction n with
  | zero => intro oa _; exact SourceKeepsX.pure Fin.elim0
  | succ n ih =>
      intro oa h
      change SourceKeepsX field (oa 0 >>= fun head =>
        Concrete.sequenceFin (fun i : Fin n => oa i.succ) >>= fun tail => Pure.pure (Fin.cases head tail : Fin (n + 1) → α))
      exact (h 0).bind _ (fun head => (ih _ (fun i => h i.succ)).bind _
        (fun tail => SourceKeepsX.pure (Fin.cases head tail : Fin (n + 1) → α)))

theorem SourceKeepsX.simulateQ {ι α β : Type} {spec : OracleSpec ι} {field : SourceState C → β}
    (impl : QueryImpl spec (SourceMX C)) (step : ∀ t, SourceKeepsX field (impl t))
    (oa : OracleComp spec α) : SourceKeepsX field (simulateQ impl oa) := by
  induction oa using OracleComp.inductionOn with
  | pure value => simpa only [simulateQ_pure] using SourceKeepsX.pure (field := field) value
  | query_bind t next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query]
      exact (step t).bind _ ih

/-- A field property proved for all source answers applies to the actual capped
interpreter by VCVio's support inclusion for stateful simulation. -/
theorem SourceKeepsX.run {α β : Type} {field : SourceState C → β} {oa : SourceMX C α}
    (h : SourceKeepsX field oa)
    (B : QueryImpl (SpecX C) (StateT (FullState C Tag) ProbComp))
    (src : SourceState C) (st : FullState C Tag)
    (r : (α × SourceState C) × FullState C Tag)
    (hr : r ∈ support (runX B oa src st)) : field r.1.2 = field src := by
  apply h src r.1
  apply support_simulateQ_run'_subset B (oa.run src) st
  rw [StateT.run'_eq, support_map]
  exact ⟨r, hr, rfl⟩

theorem sourceControl_sourceReveal (key : HiddenKey) :
    SourceKeepsX (sourceControl (C := C)) (sourceRevealX key) := by
  unfold sourceRevealX
  refine SourceKeepsX.get.bind _ fun source => ?_
  cases source.revealed key with
  | some value => exact SourceKeepsX.pure value
  | none =>
      refine (SourceKeepsX.lift (revealQueryX key)).bind _ fun value => ?_
      exact (SourceKeepsX.modify (fun st => { st with revealed := Function.update st.revealed key (some value) }) (fun _ => rfl)).bind _ (fun _ => SourceKeepsX.pure value)

theorem sourceControl_sourceRevealDigest (value : DeferredDigest) :
    SourceKeepsX (sourceControl (C := C)) (sourceRevealDigestX value) := by
  cases value with
  | known digest => exact SourceKeepsX.pure digest
  | secret key => exact sourceControl_sourceReveal key

theorem sourceControl_sourcePlant (P : PublicParameter) (p : PendingInput) :
    SourceKeepsX (sourceControl (C := C)) (sourcePlantX P p) := by
  unfold sourcePlantX
  refine (SourceKeepsX.lift (deferredQueryX (.inspect p))).bind _ fun answer => ?_
  cases answer with
  | none => exact SourceKeepsX.pure ()
  | some answer =>
      refine (sourceControl_sourceReveal p.key).bind _ fun input => ?_
      refine (sourceControl_sourceRevealDigest answer.low).bind _ fun low => ?_
      exact (SourceKeepsX.lift (deferredQueryX (.plant (.pending P p input)
        (XmssSecurity.Rom.hashOutputEquivDigestPair.symm (answer.high, low))))).bind _
          (fun ok => SourceKeepsX.modify (fun st => { st with consistent := st.consistent && ok }) (fun _ => rfl))

theorem sourceControl_sourceReleaseOpening (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : SourceKeepsX sourceControl (sourceReleaseOpeningX P seeds e) := by
  unfold sourceReleaseOpeningX
  refine SourceKeepsX.get.bind _ fun source => ?_
  split
  · refine (sourceControl_sourceReveal (.opening bottomLayer e)).bind _ fun value => ?_
    refine (SourceKeepsX.lift (completeQ (.randomizer bottomLayer e) value)).bind _ fun ok => ?_
    refine (SourceKeepsX.modify (fun st => { st with consistent := st.consistent && ok }) (fun _ => rfl)).bind _ fun _ => ?_
    refine SourceKeepsX.get.bind _ fun current => ?_
    exact (SourceKeepsX.mapM _ (sourcePlantX P) (fun p _ => sourceControl_sourcePlant P p)).bind _
      (fun _ => SourceKeepsX.pure ())
  · exact SourceKeepsX.pure ()

set_option backward.isDefEq.respectTransparency false in
theorem sourceControl_sourceHash (P : PublicParameter) (seeds : C.Term → HashOutput) (query : Query C) :
    SourceKeepsX sourceControl (sourceHashX P seeds query) := by
  have hquery (query : Query C) :
      SourceKeepsX sourceControl (liftM (deferredQueryX (.hash query)) : SourceMX C HashOutput) := SourceKeepsX.lift _
  unfold sourceHashX
  cases query with
  | prf seed point =>
      cases point with
      | randomizer lay e =>
          dsimp only
          split
          · refine (SourceKeepsX.lift (deferredQueryX .snapshot)).bind _ fun backend => ?_
            refine SourceKeepsX.get.bind _ fun source => ?_
            split
            · exact (sourceControl_sourceReleaseOpening P seeds e).bind _ (fun _ => hquery _)
            · simpa only [pure_bind] using hquery (.prf seed (.randomizer lay e))
          · simpa only [pure_bind] using hquery (.prf seed (.randomizer lay e))
      | _ => simpa only [pure_bind] using hquery _
  | _ => simpa only [pure_bind] using hquery _

set_option backward.isDefEq.respectTransparency false in
theorem sourceControl_sourceVirtual (P : PublicParameter) (seeds : C.Term → HashOutput)
    (T : C.Term) (point : Point) : SourceKeepsX sourceControl (sourceVirtualX P seeds T point) := by
  unfold sourceVirtualX
  refine (SourceKeepsX.lift (deferredQueryX (.virtual T point))).bind _ fun _ => ?_
  cases point with
  | randomizer lay e =>
      dsimp only
      split
      · refine (SourceKeepsX.lift (deferredQueryX .snapshot)).bind _ fun backend => ?_
        refine SourceKeepsX.get.bind _ fun source => ?_
        split
        · exact sourceControl_sourceReleaseOpening P seeds e
        · exact SourceKeepsX.pure ()
      · exact SourceKeepsX.pure ()
  | _ => exact SourceKeepsX.pure ()

set_option backward.isDefEq.respectTransparency false in
theorem sourceControl_sourcePending (P : PublicParameter) (p : PendingInput) :
    SourceKeepsX (sourceControl (C := C)) (sourcePendingX P p) := by
  have tail (prior : Option DeferredOutput) : SourceKeepsX sourceControl (do
      let value ← liftM (deferredQueryX (C := C) (.pending p))
      if prior.isNone then modify fun (source : SourceState C) => { source with allocated := source.allocated ++ [p] }
      pure value : SourceMX C DeferredOutput) := by
    refine (SourceKeepsX.lift (deferredQueryX (.pending p))).bind _ fun value => ?_
    split
    · exact (SourceKeepsX.modify (fun st => { st with allocated := st.allocated ++ [p] }) (fun _ => rfl)).bind _ (fun _ => SourceKeepsX.pure value)
    · exact SourceKeepsX.pure value
  unfold sourcePendingX
  refine (SourceKeepsX.lift (deferredQueryX (.inspect p))).bind _ fun prior => ?_
  refine SourceKeepsX.get.bind _ fun source => ?_
  dsimp only
  split
  · refine (SourceKeepsX.lift (deferredQueryX (.hash (.hash _)))).bind _ fun value => ?_
    refine (SourceKeepsX.lift (deferredQueryX (.record p value))).bind _ fun _ => ?_
    exact (SourceKeepsX.modify (fun st => { st with allocated := st.allocated ++ [p] }) (fun _ => rfl)).bind _ (fun _ => SourceKeepsX.pure _)
  · rename_i original priorCopy known next hmiss
    split
    · exact (SourceKeepsX.modify (fun st => { st with consistent := false }) (fun _ => rfl)).bind _ (fun _ => tail original)
    · simpa only [pure_bind] using tail original

/-- Every concrete backend source handler keeps these source-owned control fields. -/
theorem sourceControl_sourceBackend (P : PublicParameter) (seeds : C.Term → HashOutput)
    (t : DeferredQuery C) : SourceKeepsX sourceControl (sourceBackendX P seeds t) := by
  cases t with
  | hash query => exact sourceControl_sourceHash P seeds query
  | pending p => exact sourceControl_sourcePending P p
  | virtual T point => exact sourceControl_sourceVirtual P seeds T point
  | _ => exact SourceKeepsX.lift _

theorem sourceControl_sourceHashProgram {α : Type} (P : PublicParameter) (seeds : C.Term → HashOutput)
    (oa : OracleComp HashSpec α) : SourceKeepsX sourceControl (sourceHashProgramX P seeds oa) :=
  SourceKeepsX.simulateQ (sourceBackendX P seeds) (sourceControl_sourceBackend P seeds) (deferredHash oa)

theorem sourceControl_sourceBottomRow (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) (l : ChainIndex) : SourceKeepsX sourceControl (sourceBottomRowX P seeds e l) :=
  SourceKeepsX.simulateQ (sourceBackendX P seeds) (sourceControl_sourceBackend P seeds) (deferredBottomRow e l)

theorem sourceControl_sourceTopTree (P : PublicParameter) (seeds : C.Term → HashOutput) :
    SourceKeepsX sourceControl (sourceTopTreeX P seeds) :=
  SourceKeepsX.simulateQ (sourceBackendX P seeds) (sourceControl_sourceBackend P seeds) (deferredTopTree P)

theorem sourceControl_sourceCommitment (P : PublicParameter) (seeds : C.Term → HashOutput)
    (e : KeyIndex) : SourceKeepsX sourceControl (sourceCommitmentX P seeds e) := by
  unfold sourceCommitmentX
  refine (SourceKeepsX.mapM _ _ (fun T _ => sourceControl_sourceVirtual P seeds T _)).bind _ fun _ => ?_
  exact (sourceControl_sourcePending P (.commitment e)).bind _ (fun _ => SourceKeepsX.pure _)

theorem sourceControl_sourceTopValue (P : PublicParameter) (seeds : C.Term → HashOutput)
    (b : XmssSecurity.TopIndex) (l : ChainIndex) (pos : Digit) :
    SourceKeepsX sourceControl (sourceTopValueX P seeds b l pos) := by
  unfold sourceTopValueX
  refine (SourceKeepsX.mapM _ _ (fun T _ => sourceControl_sourceVirtual P seeds T _)).bind _ fun _ => ?_
  exact (SourceKeepsX.mapM _ _ (fun i _ => sourceControl_sourcePending P (.top b l _))).bind _
    (fun _ => SourceKeepsX.pure _)

theorem sourceControl_sourceTopRecover (P : PublicParameter) (b : XmssSecurity.TopIndex)
    (l : ChainIndex) (pos : Digit) (initial : DeferredDigest) :
    SourceKeepsX (sourceControl (C := C)) (sourceTopRecoverX P b l pos initial) := by
  unfold sourceTopRecoverX
  refine (SourceKeepsX.mapM _ _ (fun i _ => sourceControl_sourcePending P (.top b l _))).bind _
    fun values => ?_
  dsimp only
  split
  · exact SourceKeepsX.pure _
  · exact (SourceKeepsX.modify (field := sourceControl) (fun st => { st with consistent := false }) (fun _ => rfl)).bind _
      (fun _ => SourceKeepsX.pure _)

set_option backward.isDefEq.respectTransparency false in
/-- A full actual bottom build preserves binding, stored trees and adversary
control fields, on success as well as every early failure. -/
theorem sourceControl_sourceBottomTree (P : PublicParameter) (seeds : C.Term → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex) :
    SourceKeepsX sourceControl (sourceBottomTreeX P seeds top b) := by
  unfold sourceBottomTreeX
  refine (SourceKeepsX.mapM _ _ (fun el _ => sourceControl_sourceBottomRow P seeds el.1 el.2)).bind _
    fun rows => ?_
  refine (SourceKeepsX.mapM _ _ (fun key _ => sourceControl_sourceCommitment P seeds _)).bind _
    fun commitments => ?_
  refine (SourceKeepsX.mapM _ _ (fun T _ => sourceControl_sourceVirtual P seeds T _)).bind _ fun _ => ?_
  refine (sourceControl_sourceHashProgram P seeds _).bind _ fun root => ?_
  refine (sourceControl_sourcePending P (.base topLayer (topKey b) (bytesLE 16 root))).bind _ fun base => ?_
  refine (sourceControl_sourceHashProgram P seeds _).bind _ fun found => ?_
  cases found with
  | none => exact SourceKeepsX.pure none
  | some answer =>
      rcases answer with ⟨randomness, encoding⟩
      refine (SourceKeepsX.sequenceFin _ _ (fun l => sourceControl_sourceTopValue P seeds b l (encoding l))).bind _
        fun values => ?_
      refine (sourceControl_sourceHashProgram P seeds _).bind _ fun path => ?_
      refine (sourceControl_sourceHashProgram P seeds _).bind _ fun digest => ?_
      cases hd : Codeword.decode digest with
      | none =>
          dsimp only
          exact SourceKeepsX.pure none
      | some checked =>
          dsimp only
          split
          · exact (SourceKeepsX.modify (field := sourceControl) (fun st => { st with consistent := false }) (fun _ => rfl)).bind _
              (fun _ => SourceKeepsX.pure none)
          · refine (SourceKeepsX.sequenceFin _ _
              (fun l => sourceControl_sourceTopRecover P b l (encoding l) (values l))).bind _ fun ends => ?_
            refine (sourceControl_sourceHashProgram P seeds _).bind _ fun leaf => ?_
            refine (sourceControl_sourceHashProgram P seeds _).bind _ fun root => ?_
            split <;> exact SourceKeepsX.pure _


/-- Every stored successful or failed tree has its complete allocated row domain. -/
def TreeRows (x : Keys3 C) (src : SourceState C) (st : FullState C Tag) : Prop :=
  ∀ b, src.trees b ≠ none → BottomRows x b st

/-- Source initialization has no stored bottom tree. -/
theorem treeRows_initial (x : Keys3 C) (st : FullState C Tag) :
    TreeRows x sourceInit st := by
  intro b hb
  simp [sourceInit] at hb

/-- Any computation retaining the stored-tree map preserves its row invariant. -/
theorem treeRows_of_keeps {α : Type}
    (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (oa : SourceMX C α) (hk : SourceKeepsX (fun src => src.trees) oa)
    (src : SourceState C) (st : FullState C Tag) (h : TreeRows x src st)
    (r : (α × SourceState C) × FullState C Tag)
    (hr : r ∈ support (runX
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest) oa src st)) :
    TreeRows x r.1.2 r.2 := by
  have ht := hk.run _ src st r hr
  have hm := runX_rows tagOf x q s pads τ g noise rest oa src st r hr
  intro b hb k l d
  have old := h b (ht ▸ hb) k l d
  exact ⟨fun T => hm.1 (old.1 T), hm.2 _ old.2⟩

/-- D17 preserves the row invariant for all trees when storing a first result. -/
theorem sourceBottomOnceX_treeRows
    (tagOf : CappedCompilerState C × Bool → Tag) (x : Keys3 C)
    (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
    (τ : CPoint → Digest) (g : C.Term × CPoint → HashOutput)
    (noise : ChainNoiseIndex → HashOutput) (rest : RestSlot C → HashOutput)
    (top : TopTree) (b : XmssSecurity.TopIndex)
    (src : SourceState C) (st : FullState C Tag) (h : TreeRows x src st)
    (r : (Option DeferredBottomTree × SourceState C) × FullState C Tag)
    (hr : r ∈ support (runX
      (shareBackendTagT tagOf x.1 x.2.1 x.2.2 q s pads τ g noise rest)
      (sourceBottomOnceX x.1 x.2.1 top b) src st)) :
    TreeRows x r.1.2 r.2 := by
  simp only [sourceBottomOnceX, runX_bind, runX_get, pure_bind] at hr
  cases ht : src.trees b with
  | some tree =>
    simp only [ht, runX_pure, mem_support_pure_iff] at hr
    subst r
    exact h
  | none =>
    simp only [ht, runX_bind, runX_modify, runX_pure, pure_bind,
      mem_support_bind_iff, mem_support_pure_iff] at hr
    obtain ⟨a, ha, rfl⟩ := hr
    have hc := (sourceControl_sourceBottomTree x.1 x.2.1 top b).run _ src st a ha
    have htrees : a.1.2.trees = src.trees := congrArg (fun c => c.2.1) hc
    have hm := runX_rows tagOf x q s pads τ g noise rest _ src st a ha
    intro other hother
    by_cases he : other = b
    · subst other
      exact sourceBottomTreeX_rows tagOf x q s pads τ g noise rest top b src st a ha
    · have hold : src.trees other ≠ none := by
        simpa only [Function.update_of_ne he, htrees] using hother
      intro k l d
      have old := h other hold k l d
      exact ⟨fun T => hm.1 (old.1 T), hm.2 _ old.2⟩

end ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.pure

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.get

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.modify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.modify

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.lift

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.bind

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.mapM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.mapM

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.sequenceFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.sequenceFin

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.simulateQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.simulateQ

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.SourceKeepsX.run

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceReveal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceReveal

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceRevealDigest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceRevealDigest

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourcePlant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourcePlant

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceReleaseOpening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceReleaseOpening

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceHash' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceHash

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceVirtual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceVirtual

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourcePending' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourcePending

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceBackend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceBackend

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceHashProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceHashProgram

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceBottomRow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceBottomRow

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceTopTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceTopTree

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceCommitment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceCommitment

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceTopValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceTopValue

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceTopRecover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceTopRecover

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceBottomTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceControl_sourceBottomTree

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.treeRows_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.treeRows_initial

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.treeRows_of_keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.treeRows_of_keeps

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceBottomOnceX_treeRows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerSyncTreeControl.sourceBottomOnceX_treeRows
