import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Games
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.Partition
import ThresholdLeanXmssSecurity.Proof.SeedGenSecurity

/-!
# The two ends of the seed generation claim, general over the rest

A rest is a program of the world with one more query, a read of the stream state. The read gives
the blind view of the state, with no cell of the class of the seed generation. So a rest that runs
on the private table of `tableWorld` and a rest that runs on the full cache of `streamWorld` read the
same view.

* `SeedRealGeneral` says that the real seed generation with the table adversary and then a rest on
  `tableWorld` has the law of the real seed generation with `net` and then the same rest in
  `streamWorld`.
* `SeedIdealGeneral` says the same for `FseedGen` with the simulator of the table adversary and for
  `worldSeedGen`. The rest gets the keys of the dealer of each emulated operator with keys.

Both need a rest with no programming query, because `tableWorld` answers such a query with `false`
and `streamWorld` writes the cell.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

/-! ## The world with a read of the blind view -/

/-- The world with one read of the stream state. -/
abbrev PeekSpec (C : Committee) := WorldSpec C + (Unit →ₒ StreamState C)

/-- A programming query of the world in `PeekSpec`. -/
def PeekProgramQuery : (PeekSpec C).Domain → Prop
  | .inl t => WorldProgramQuery t
  | .inr _ => False

/-- The cache with no cell of the class of the seed generation. -/
def eraseSeedGen (cache : HashCache C) : HashCache C :=
  QueryCache.ofFn fun q => if isSeedGenQuery q then none else cache q

/-- The stream state with no cell of the class of the seed generation. -/
def blind (w : StreamState C) : StreamState C := (eraseSeedGen w.1, w.2)

/-- A handler of the world with the read of the blind view of its state. -/
def withPeek {W : Type} {M : Type → Type} [Monad M] (impl : QueryImpl (WorldSpec C) (StateT W M))
    (view : W → StreamState C) : QueryImpl (PeekSpec C) (StateT W M) :=
  impl + ((fun _ => (fun w => blind (view w)) <$> get : QueryImpl (Unit →ₒ StreamState C) (StateT W M)))

/-- A handler of the world in a program with reads. Each query of the world is followed by a read,
and the state keeps the last read. -/
def peekHandler : QueryImpl (WorldSpec C) (StateT (StreamState C) (OracleComp (PeekSpec C))) := fun t =>
  StateT.mk fun _ => do
    let r ← OracleComp.lift (OracleSpec.query (spec := PeekSpec C) (.inl t))
    let w ← OracleComp.lift (OracleSpec.query (spec := PeekSpec C) (.inr ()))
    pure (r, w)

/-- A computation of the world on a state that is a read, as a program with reads. -/
def programOf {α : Type} (R : StateT (StreamState C) (OracleComp (PeekSpec C)) α) : OracleComp (PeekSpec C) α := do
  let w ← OracleComp.lift (OracleSpec.query (spec := PeekSpec C) (.inr ()))
  R.run' w

theorem allQueries_map {ι : Type} {spec : OracleSpec ι} {P : ι → Prop} {α β : Type} (f : α → β)
    {oa : OracleComp spec α} (h : AllQueriesSatisfy oa P) : AllQueriesSatisfy (f <$> oa) P := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind h fun _ => allQueriesSatisfy_pure _ _

/-- Two continuations with one probability of their events on each possible output of a draw give
one probability after the draw. -/
theorem prEvent_bind_congr_support {α β γ : Type} (mx : ProbComp α) (f : α → ProbComp β) (g : α → ProbComp γ)
    (p : β → Prop) (q : γ → Prop) (h : ∀ a ∈ support mx, Pr{let y ← f a}[p y] = Pr{let y ← g a}[q y]) :
    Pr{let y ← mx >>= f}[p y] = Pr{let y ← mx >>= g}[q y] :=
  le_antisymm (prEvent_bind_mono_of_forall_le_of_support mx f g p q fun a ha => (h a ha).le)
    (prEvent_bind_mono_of_forall_le_of_support mx g f q p fun a ha => (h a ha).ge)

/-! ## The general statements -/

/-- The real end of the seed generation claim, general over the rest. -/
def SeedRealGeneral (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (β : Type)
    (rest : net.State → (C.Party → Option (Keys C)) → OracleComp (PeekSpec C) β),
    (∀ state keys, AllQueriesSatisfy (rest state keys) fun t => ¬ PeekProgramQuery t) →
    (simulateQ (worldAnswer prims) (realExecution D (tableNet prims net) noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [] >>= fun r =>
          worldRoles.adversary ((simulateQ (withPeek (tableWorld prims D) id) (rest r.1.1 r.2)).run' (r.1.2, ∅)))).run' ∅ =ᵈ
      ((simulateQ (streamWorld prims D) (realExecution D net noFunctionality setupRounds
        (fun i (_ : Unit) => (seedGen i : PartyM C E RealSpec (Keys C))) (fun _ => ()) [])).run (∅, ∅) >>= fun r =>
          (simulateQ (withPeek (streamWorld prims D) id) (rest r.1.1 r.1.2)).run' r.2)

/-- The ideal end of the seed generation claim, general over the rest. An honest operator gets the
keys of the dealer when its emulated operator ends with keys. -/
def SeedIdealGeneral (prims : Primitives) : Prop :=
  ∀ (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (β : Type)
    (rest : net.State → (C.Party → Option (Keys C)) → OracleComp (PeekSpec C) β),
    (∀ state keys, AllQueriesSatisfy (rest state keys) fun t => ¬ PeekProgramQuery t) →
    (simulateQ (worldAnswer prims) (idealExecution (fun oa => oa) D FseedGen
        (seedGenSimulator D (tableNet prims net)) (fun _ => ()) [] >>= fun r =>
          worldRoles.adversary ((simulateQ (withPeek (tableWorld prims D) id) (rest r.1.1 r.2)).run' (r.1.2, ∅)))).run' ∅ =ᵈ
      ((simulateQ (streamWorld prims D) (worldSeedGen D net)).run (∅, ∅) >>= fun r =>
          (simulateQ (withPeek (streamWorld prims D) id)
            (rest r.1.1 fun i => (r.1.2.2.2.2 i).map fun _ => r.1.2.2.2.1 i)).run' r.2)

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.prEvent_bind_congr_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.prEvent_bind_congr_support
