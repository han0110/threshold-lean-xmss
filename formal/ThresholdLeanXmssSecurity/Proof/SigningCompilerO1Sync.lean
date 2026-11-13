import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncSuffix
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncTreeControl
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncTrigger
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncBackend
import ThresholdLeanXmssSecurity.Proof.SigningCompilerSyncRealRead
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Release
import ThresholdLeanXmssSecurity.Proof.SigningCompilerO1Cost
import ThresholdLeanXmssSecurity.Proof.SigningCompilerPotential
import ThresholdLeanXmssSecurity.Proof.SigningCompilerShareGuarded
import ThresholdLeanXmssSecurity.Proof.SigningReleasedAlign

/-! # The boundary relation of the O1 coupling

`SyncO1` relates the real state and the O1 compiler state at each handler boundary of the forger
phase. `SyncMid`, `SyncVerify` and `SyncFinal` are its forms inside a signing handler, during the
verification and after the honest-signature tail. `syncBase_init` states that the relation before
the setup holds at the initial states, and `syncFinal_of_verify` states that the relation after the
verification gives the relation after the tail.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational
noncomputable section
namespace ThresholdLeanXmssSecurity.SigningCompilerO1Sync
open SigningOpeningProof SigningSecurityProof SigningLaneHybridCapProof
open SigningLaneHybridCapO1Proof SigningCompilerCouplingProof
open SigningCompilerShare SigningCompilerShareTag SigningCompilerShareTables
open SigningCompilerRealTables SigningCompilerShareCap
open SigningCompilerSyncFrame SigningCompilerSyncReal SigningCompilerSyncStop
open SigningCompilerSyncRelease SigningCompilerSyncTreeControl SigningCompilerSyncTreeRows
open SigningCompilerO1SourceProof SigningCompilerO1Basics SigningCompilerUntil
open XmssSecurity.CappedChain
variable {C : Committee}
attribute [local instance] Classical.propDecidable
set_option linter.constructorNameAsVariable false

/-! ## Views of the real state -/

/-- The signing state that the real handler carries. -/
abbrev realSigning (a : RealState C) : TsigState C := a.1.2.1.1

/-- The hidden-key flag of the real run. -/
abbrev realFlag (a : RealState C) : Bool := a.1.2.1.2

/-- The trees that a `.tree` request named. -/
abbrev realExposed (a : RealState C) : Finset (Fin (2 ^ layerHeight)) := a.1.2.2.1

/-- The cache of the call log. The final events read this cache. -/
abbrev realLog (a : RealState C) : HashCache C := SigningCacheLogProof.logCache a.1.1.1.1.1.2

/-- The real state with another candidate list. The verification keeps its candidates outside the state. -/
def withCandidates (a : RealState C) (cs : List (HiddenKey × Digest)) : RealState C :=
  ((a.1.1, (a.1.2.1, a.1.2.2.1, cs)), a.2)

/-- The real state with another signing state. A handler holds its own signing state until it returns. -/
def withSigning (a : RealState C) (sig : TsigState C) : RealState C :=
  ((a.1.1, ((sig, a.1.2.1.2), a.1.2.2)), a.2)

/-! ## The stored trees -/

/-- The real tree of a symbolic tree of index `bi`, with each chain value read at the secrets `s`. -/
def interpretTree (s : HiddenKey → Digest) (bi : Fin (2 ^ layerHeight))
    (tree : DeferredBottomTree) : BottomTree :=
  ⟨patchCpk bi tree.commitment tree.cpk, tree.commitment, tree.root,
    ⟨tree.topSignature.randomness, fun l => (tree.topSignature.chainValue l).interpret s,
      tree.topSignature.path⟩⟩

/-- The setup run of the top tree has a counted run below the cache. -/
def TopRun (prims : Primitives) (x : Keys3 C) (top : TopTree) (cache : HashCache C) : Prop :=
  ∃ (start : HashCache C × ℕ) (result : Option TreeOutput × HashCache C × ℕ),
    result ∈ support ((simulateQ (SigningCacheProof.countImpl prims)
      (SigningSecurityProof.liftFree (referenceTree tweakable (prfValue x.2.1) x.1 emptyTop .top))).run start) ∧
    result.1 = some (.top top) ∧ result.2.1 ≤ cache

/-! ## The relation -/

/-- The O1 clauses. `rev` is the reveal map that the timing clauses read. At a handler boundary it is
the reveal map of the source. After the honest-signature tail it is the map before the tail. -/
structure ExtraO1 (prims : Primitives) (x : Keys3 C) (top : TopTree) (s : HiddenKey → Digest)
    (rev : HiddenKey → Option Digest) (a : RealState C) (b : SourceStateO1 C × CompState C) : Prop where
  /-- Each stored tree has its row domain. `releaseSuffix_sync` reads it. -/
  treeRows : TreeRows x b.1.base b.2
  /-- The real store is the symbolic store read at `s`. -/
  storedTrees : ∀ bi, (realSigning a).trees bi = (b.1.base.trees bi).map (Option.map (interpretTree s bi))
  /-- The log cache holds the top digest input of each stored tree, and it decodes to the stored
  top codeword. -/
  storedTopDigit : ∀ bi tree, b.1.base.trees bi = some (some tree) →
    (SigningDescentProof.thView (realLog a) (XmssSecurity.Concrete.CacheView.topEncodingInput x.1 bi
      (tree.root, tree.topSignature.randomness))).isSome ∧
    XmssSecurity.TargetSum.decodeDigest (XmssSecurity.Concrete.CacheView.topEncodingHash
      (SigningDescentProof.thView (realLog a)) x.1 bi (tree.root, tree.topSignature.randomness)) =
        some tree.topSignature.encoding
  /-- A recorded digit has a successful stored tree. -/
  startsTreed : ∀ e l, b.1.starts e l ≠ ∅ → ∃ tree, b.1.base.trees (treeOf e) = some (some tree)
  /-- A bound key of a stored tree has a revealed opening. The release P ran at the later of the
  two steps. -/
  boundTreeRevealed : ∀ e, b.1.base.signing.bound e ≠ none → b.1.base.trees (treeOf e) ≠ none →
    b.1.base.revealed (.opening bottomLayer e) ≠ none
  /-- An opening reveal is not before the real release. -/
  revealedReleased : ∀ lay e, rev (.opening lay e) ≠ none →
    Released (realSigning a) (realExposed a) (.opening lay e)
  /-- A bottom chain reveal has `t` signers and a recorded digit at or below it. -/
  revealedCovered : ∀ e l (p : XmssSecurity.ChainStep), rev (.bottomChain e l p) ≠ none →
    ∃ m, (realSigning a).bound e = some m ∧ C.t ≤ (signersAt (realSigning a) e m).card ∧
      ∃ d ∈ b.1.starts e l, d.val ≤ p.val
  /-- A top chain reveal has a returned tree and a top digit at or below it. -/
  revealedTop : ∀ bi l (p : XmssSecurity.ChainStep), rev (.topChain bi l p) ≠ none →
    bi ∈ realExposed a ∧ ∃ tree, b.1.base.trees bi = some (some tree) ∧
      (tree.topSignature.encoding l).val ≤ p.val
  /-- A candidate that carries its secret had a revealed key at `rev`. -/
  candidatesPaid : ∀ c ∈ b.1.base.candidates, c.2 = s c.1 → rev c.1 ≠ none
  /-- A logged opening candidate never carries its secret. -/
  openingFresh : ∀ c ∈ b.1.base.candidates, ∀ lay e, c.1 = .opening lay e → c.2 ≠ s c.1
  /-- The stale bit is down. -/
  staleFree : a.1.1.2.2 = false
  /-- No visible base input carries the opening of an unrevealed key. -/
  noEarlyGuess : ∀ e message, b.1.base.revealed (.opening bottomLayer e) = none →
    visibleOf a (.hash (randomizerInput x.1 bottomLayer e (s (.opening bottomLayer e)) message)) = none
  /-- The visible cache has no input of a pending point with an unrevealed key and no answer. A
  fresh commitment answer and a fresh top base answer need it. -/
  guessFree : ∀ p : PendingInput, b.1.base.revealed p.key = none →
    (dataOf x b.2).pending p = none → visibleOf a (.hash (p.input x.1 (s p.key))) = none
  /-- A stored tree has the virtual terms of each of its commitments and of its top randomizer. The
  release at a later bind and the release at a tree request read them. -/
  treeTerms : ∀ bi, b.1.base.trees bi ≠ none →
    (∀ k T, (T, Point.randomizer bottomLayer (bottomKey bi k)) ∈ (dataOf x b.2).virtual) ∧
      ∀ T, (T, Point.randomizer topLayer (topKey bi)) ∈ (dataOf x b.2).virtual
  /-- A stored successful tree has the virtual terms of each top chain start of its top key. -/
  treeStarts : ∀ bi tree, b.1.base.trees bi = some (some tree) →
    ∀ T l, (T, Point.chain topLayer (topKey bi) l (digit 0)) ∈ (dataOf x b.2).virtual
  /-- A chain value of a stored top signature is the secret at the digit of the top codeword, or a
  known chain end at digit 3. The release at a tree request reveals no other key. -/
  treeValues : ∀ bi tree, b.1.base.trees bi = some (some tree) → ∀ l,
    (∀ h : (tree.topSignature.encoding l).val < 3, tree.topSignature.chainValue l =
      .secret (.topChain bi l ⟨(tree.topSignature.encoding l).val, h⟩)) ∧
    ((tree.topSignature.encoding l).val = 3 → ∃ w, tree.topSignature.chainValue l = .known w)
  /-- A visible base input at the bound message has a trace entry. -/
  baseTraced : ∀ e message, (realSigning a).bound e = some message →
    visibleOf a (.hash (randomizerInput x.1 bottomLayer e (s (.opening bottomLayer e))
      (bytesLE 32 message))) ≠ none → e ∈ a.1.1.2.1.leafIndices
  /-- The log cache is below the visible cache and equals it outside the trial inputs. -/
  logAgreement : SigningPartnerCompareProof.LogAgreement x.1 a.1.1.1.1.1
  /-- Each stored real tree has a counted run below the log cache. -/
  storedRuns : SigningGuessProof.StoredTreeRuns prims x top (realLog a) (realSigning a)
  /-- Each recorded digit is the digit of a successful codeword search below the log cache. -/
  startsTraced : ∀ e l d, d ∈ b.1.starts e l → ∃ receipt : SigningGuessProof.Round2Receipt C,
    receipt.key = e ∧ (realSigning a).bound e = some receipt.message ∧ receipt.encoding l = d ∧
      SigningGuessProof.ReceiptRuns prims x top (realLog a) receipt
  /-- At most `t - 1` operators are corrupt. -/
  corruptBound : (realSigning a).corrupt.card ≤ C.t - 1
  /-- Each release record is at the bound message of its key. -/
  releasedBound : SigningGuessProof.ReleasedBound (realSigning a)
  /-- With the flag down, a visible PRF entry is at a constrained point or at a corrupt term. -/
  prfSeen : realFlag a = false → ∀ T p, visibleOf a (.prf (x.2.1 T) p) ≠ none →
    TprfSecurityProof.Revealed (realSigning a).corrupt (.inl T) ∨ Constrained p
  /-- With the flag down, a visible bottom chain entry of a lacked term has its row of pending answers. -/
  bottomSeen : realFlag a = false → ∀ T e l (d : XmssSecurity.ChainStep),
    visibleOf a (.prf (x.2.1 T) (.chain bottomLayer e l (chainStepDigit d))) ≠ none →
      TprfSecurityProof.Revealed (realSigning a).corrupt (.inl T) ∨
        ∀ d' : XmssSecurity.ChainStep, (dataOf x b.2).pending (.bottom e l d') ≠ none

/-- The relation before the setup. No clause reads the top tree in a state with no stored tree. -/
def SyncBase (prims : Primitives) (x : Keys3 C) (top : TopTree) (s : HiddenKey → Digest)
    (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (a : RealState C) (b : SourceStateO1 C × CompState C) : Prop :=
  SyncCore x s pads noise g rest a (b.1.base, b.2) ∧ ExtraO1 prims x top s b.1.base.revealed a b

/-- The top clauses, which the setup establishes. -/
structure TopO1 (prims : Primitives) (x : Keys3 C) (top : TopTree)
    (a : RealState C) (b : SourceStateO1 C × CompState C) : Prop where
  /-- The setup allocated each top chain edge. -/
  topRows : ∀ (bi : XmssSecurity.TopIndex) (l : ChainIndex) (d : XmssSecurity.ChainStep),
    (dataOf x b.2).pending (.top bi l d) ≠ none
  /-- The setup run is below the log cache. -/
  topRun : TopRun prims x top (realLog a)

/-- The relation at each handler boundary of the adversary phase. -/
def SyncO1 (prims : Primitives) (x : Keys3 C) (top : TopTree) (s : HiddenKey → Digest)
    (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (a : RealState C) (b : SourceStateO1 C × CompState C) : Prop :=
  SyncBase prims x top s pads noise g rest a b ∧ TopO1 prims x top a b

/-- The relation during the verification. `vlog` holds the candidates of the verification calls. -/
def SyncVerify (prims : Primitives) (x : Keys3 C) (top : TopTree) (s : HiddenKey → Digest)
    (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (vlog : List (HiddenKey × Digest))
    (a : RealState C) (b : SourceStateO1 C × CompState C) : Prop :=
  SyncO1 prims x top s pads noise g rest (withCandidates a (a.1.2.2.2 ++ vlog)) b

/-- The relation after the honest-signature tail. The timing clauses read a reveal map `rev` from
before the tail. -/
def SyncFinal (prims : Primitives) (x : Keys3 C) (top : TopTree) (s : HiddenKey → Digest)
    (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (vlog : List (HiddenKey × Digest))
    (a : RealState C) (b : SourceStateO1 C × CompState C) : Prop :=
  SyncCore x s pads noise g rest (withCandidates a (a.1.2.2.2 ++ vlog)) (b.1.base, b.2) ∧
    TopO1 prims x top a b ∧
    ∃ rev : HiddenKey → Option Digest, (∀ k, rev k ≠ none → b.1.base.revealed k ≠ none) ∧
      ExtraO1 prims x top s rev (withCandidates a (a.1.2.2.2 ++ vlog)) b

/-- The relation inside a signing handler. The real handler holds the signing state `sigCore`, which
the compiler state matches. The timing clauses read `sigTime`, the signing state at the return of
the handler. In round 2 it holds the release record of the call. -/
def SyncMid (prims : Primitives) (x : Keys3 C) (top : TopTree) (s : HiddenKey → Digest)
    (pads : Point → Digest) (noise : ChainNoiseIndex → HashOutput) (g : C.Term × CPoint → HashOutput)
    (rest : RestSlot C → HashOutput) (sigCore sigTime : TsigState C)
    (a : RealState C) (b : SourceStateO1 C × CompState C) : Prop :=
  SyncCore x s pads noise g rest (withSigning a sigCore) (b.1.base, b.2) ∧
    ExtraO1 prims x top s b.1.base.revealed (withSigning a sigTime) b ∧ TopO1 prims x top a b

/-! ## The handlers -/

section Handlers
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- The fixed targets and the fiber table of the coupling. -/
abbrev tauOf : CPoint → Digest := NoFalse.tau s pads
abbrev gOf : C.Term × CPoint → HashOutput :=
  SigningShareLazy.fiberTable C.terms (NoFalse.tau s pads) (SigningShareLazy.init : Table.FrozenState C) u

/-- The real oracles of the forger over the fixed tables. -/
abbrev realOracles (top : TopTree) : QueryImpl (LocalSpec C + TsigSpec C) (StateT (RealState C) ProbComp) :=
  SigningCompilerUntil.fuse (rawTraceFlatWith prims x (openingOracles x (SigningJointEagerProof.dealtOf x top)))
    (realImpl x (gOf s pads u) rest)

/-- The eager backend of the compiler over the fixed tables. -/
abbrev compBackend : QueryImpl (SpecX C) (StateT (CompState C) ProbComp) :=
  shareBackendTagT capTag x.1 x.2.1 x.2.2 q s pads (tauOf s pads) (gOf s pads u) noise rest

/-- The O1 oracles of the forger over the eager backend. -/
abbrev compOracles (top : TopTree) :
    QueryImpl (LocalSpec C + TsigSpec C) (StateT (SourceStateO1 C × CompState C) ProbComp) :=
  SigningCompilerUntil.fuse (sourceOraclesO1X prims x top) (compBackend x q s pads u rest noise)

/-- The stop of the compiler side on a joint state. -/
abbrev CompStop (b : SourceStateO1 C × CompState C) : Prop := Stop b.2

/-- The contract of one oracle call of the forger. -/
def StepO1 (top : TopTree) (t : (LocalSpec C + TsigSpec C).Domain) : Prop :=
  ∀ (a : RealState C) (b : SourceStateO1 C × CompState C),
    SyncO1 prims x top s pads noise (gOf s pads u) rest a b → ¬RealStop q a → ¬Stop b.2 →
    RelTriple ((realOracles prims x s pads u rest top t).run a)
      ((compOracles prims x q s pads u rest noise top t).run b)
      (Until (RealStop q) CompStop (SyncO1 prims x top s pads noise (gOf s pads u) rest))

/-- The initial real state of the run. -/
def realInit : RealState C :=
  ((((SigningOneRunProof.monitoredInit.1, fun _ => false), ([], false)),
    SigningOneRunProof.monitoredInit.2), realCache x s pads noise)

/-- The initial compiler state of the run. -/
def compInit : SourceStateO1 C × CompState C := (sourceInitO1, SigningCompilerShareTables.initial)

/-- The relation before the setup holds at the initial states, for every top tree. -/
theorem syncBase_init (hkeys : ¬TprfSecurityProof.KeyCollision x.2.1 x.2.2) (top : TopTree) :
    SyncBase prims x top s pads noise (gOf s pads u) rest (realInit x s pads noise) compInit := by
  have hdata : dataOf x (compInit (C := C)).2 = deferredInit := by
    change (withCache ((compilerInit, 0), fun _ => none, false)
      (merge x.2.1 ∅ (fun _ => none))).1.1.data = _
    rw [merge_empty]
    rfl
  have hframe := initial_frame (Tag := Bool × Bool) x rest (gOf s pads u)
  refine ⟨⟨⟨?_, ?_⟩, rfl⟩, ?_⟩
  · refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, revealRelation_initial s, ?_, ?_, ?_, ?_, ?_,
      rfl, rfl, rfl, hframe.2, hframe.1.1, hframe.1.2.1, realPrivate_init x s pads noise _ rest, ?_,
      ?_, ?_⟩
    · intro p answer h
      cases h
    · refine ⟨fun e h => ?_, fun e h => absurd rfl h⟩
      obtain ⟨output, houtput⟩ := h (someTerm C)
      cases houtput
    · change PendingValid (dataOf x (compInit (C := C)).2)
      rw [hdata]
      exact pendingValid_init
    · intro p h
      exact absurd rfl h
    · intro T p h
      exact absurd h (Finset.notMem_empty _)
    · intro edge _
      rfl
    · intro c hc
      cases hc
    · intro p hp
      exact absurd hp (Finset.notMem_empty _)
  · change CacheRelation x.1 x.2.1 s (dataOf x (compInit (C := C)).2) ∅
    rw [hdata]
    exact cacheRelation_initial _ _ _
  · refine ⟨treeRows_initial x _, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro bi tree h
      cases h
    · intro e l h
      exact absurd rfl h
    · intro e h
      exact absurd rfl h
    · intro lay e h
      exact absurd rfl h
    · intro e l p h
      exact absurd rfl h
    · intro bi l p h
      exact absurd rfl h
    · intro c hc
      cases hc
    · intro c hc
      cases hc
    · intro e message _
      rfl
    · intro p _ _
      rfl
    · intro bi h
      exact absurd rfl h
    · intro bi tree h
      cases h
    · intro bi tree h
      cases h
    · intro e message h
      cases h
    · refine ⟨fun q v h => ?_, fun q _ => rfl⟩
      cases h
    · intro bi tree h
      cases h
    · intro e l d h
      exact absurd h (Finset.notMem_empty _)
    · exact Nat.zero_le _
    · intro e message i h
      cases h
    · intro _ T p h
      exact absurd rfl h
    · intro _ T e l d h
      exact absurd rfl h

/-- The relation after the verification gives the relation after the tail when no tail runs. -/
theorem syncFinal_of_verify (top : TopTree) (vlog : List (HiddenKey × Digest))
    (a : RealState C) (b : SourceStateO1 C × CompState C)
    (hs : SyncVerify prims x top s pads noise (gOf s pads u) rest vlog a b) :
    SyncFinal prims x top s pads noise (gOf s pads u) rest vlog a b := by
  obtain ⟨⟨hcore, hextra⟩, htop⟩ := hs
  exact ⟨hcore, ⟨htop.topRows, htop.topRun⟩, b.1.base.revealed, fun _ h => h, hextra⟩

end Handlers

/-! ## The end of the runs -/

section Final
variable (prims : Primitives) (x : Keys3 C) (q : ℕ) (s : HiddenKey → Digest) (pads : Point → Digest)
  (u : C.Term × CPoint → HashOutput) (rest : RestSlot C → HashOutput) (noise : ChainNoiseIndex → HashOutput)

/-- An outcome of the raw real run, with its private cache. -/
abbrev RealFinal (C : Committee) := SigningLaneUnionProof.TraceOutcome C × HashCache C

/-- An outcome of the O1 program on the eager backend, before the caches merge. -/
abbrev CompFinal (C : Committee) := ((Bool × TopTree × Forgery) × SourceStateO1 C) × CompState C

/-- The real state at the end. -/
def realEnd (z : RealFinal C) : RealState C := (z.1.2, z.2)

/-- The facts at the end of two runs that did not stop. The real result holds the top tree and the
forgery of the compiler, the signing state and the flag of the real state, and all candidates. -/
def FinalFacts (z : RealFinal C) (c : CompFinal C) : Prop :=
  ∃ (vlog : List (HiddenKey × Digest)) (win : Bool),
    z.1.1 = (((win, realFlag (realEnd z)),
        some (c.1.1.2.1, realSigning (realEnd z), c.1.1.2.2)), (realEnd z).1.2.2.2 ++ vlog) ∧
      SyncFinal prims x c.1.1.2.1 s pads noise (gOf s pads u) rest vlog (realEnd z) (c.1.2, c.2)

/-- The real event of `CompilerCouplingO1`. -/
def RealEvent (z : SigningLaneUnionProof.TraceOutcome C) : Prop :=
  SigningLaneUnionProof.NoFlag (SigningLaneUnionProof.observed z) ∧
    SigningLaneUnionProof.NotChargedLogged prims x (SigningLaneUnionProof.observed z) ∧
    (SigningLaneUnionProof.LoggedInputHit prims x (SigningLaneUnionProof.observed z) ∨
      SigningLaneUnionProof.StaleBaseAt z ∨ SigningLaneUnionProof.GhostAt x z)

/-- The logged outcome that the input-side events read. -/
abbrev loggedOf (z : SigningLaneUnionProof.TraceOutcome C) : SigningGuessLinkProof.LoggedOutcome C :=
  ((SigningLaneUnionProof.observed z).1,
    (SigningCacheLogProof.logCache (SigningLaneUnionProof.observed z).2.2,
      (SigningLaneUnionProof.observed z).2.1))

/-- The good event of the compiler outcome, with the hidden-key flag down. -/
def CompGood (o : CompilerOutcomeO1 C) : Prop :=
  o.1.2.base.hiddenFlag = false ∧ (o.2.2.2 = true ∨ compilerEvent x.1 q o.2.1)

end Final

end ThresholdLeanXmssSecurity.SigningCompilerO1Sync

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Sync.syncBase_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Sync.syncBase_init

/-- info: 'ThresholdLeanXmssSecurity.SigningCompilerO1Sync.syncFinal_of_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.SigningCompilerO1Sync.syncFinal_of_verify
