import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Table.WorldForger

/-!
# The coupling of the table of the forger with the world

`Couple x y` says that the computation `x` of the forger on its table and the computation `y` in the
world give the same run. The run of `y` in `streamWorld` from the cache with the table of the forger
merged in (`tableImage`) is the run of `x` in `tsigGame`, with the final table merged in the same way.

* `Couple.pure`, `Couple.bind`, `Couple.simulateQ` and `Couple.forIn` build a coupling along the code.
* `CoupleS` is the same on a state above both monads.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The relation -/

/-- The streams of the forger as the cache of the hidden streams of `streamWorld`. -/
def curryStreams (c : StreamCache C) : HiddenCache C := QueryCache.ofFn fun x => c (x.1.1, x.1.2, x.2)

/-- The cache of the world for the state `ts` of the forger and its cache `s` in `tsigGame`. -/
def tableImage (ts : TableState C) (s : HashCache C) : HashCache C × HiddenCache C :=
  (SeedPartition.merge isSetupQuery s ts.table, curryStreams ts.streams)

variable (prims : Primitives) (D : C.Coalition) (dealt : Dealt C (OracleComp (WorldSpec C)))

/-- The run of a computation of the forger in `tsigGame`. -/
def semR {α : Type} (x : TableM C α) (ts : TableState C) (st : TsigState C) (s : HashCache C) :
    ProbComp (((α × TableState C) × TsigState C) × HashCache C) :=
  (simulateQ (baseAnswer prims) ((simulateQ (SigningCoreProof.gameOracles dealt) (x.run ts)).run st)).run s

/-- The run of a computation of the world forger in `streamWorld`. -/
def semW {α : Type} (y : WorldM C α) (log : CallLog C) (st : TsigState C) (c : HashCache C × HiddenCache C) :
    ProbComp (((α × CallLog C) × TsigState C) × (HashCache C × HiddenCache C)) :=
  (simulateQ (streamWorld prims D) ((y.run log).run st)).run c

/-- The end of a run of the forger seen in the world. -/
def image {α : Type} (z : ((α × TableState C) × TsigState C) × HashCache C) :
    ((α × CallLog C) × TsigState C) × (HashCache C × HiddenCache C) :=
  (((z.1.1.1, z.1.1.2.log), z.1.2), tableImage z.1.1.2 z.2)

/-- The two computations give the same run. -/
def Couple {α : Type} (x : TableM C α) (y : WorldM C α) : Prop :=
  ∀ ts st s, semW prims D y ts.log st (tableImage ts s) = image <$> semR prims dealt x ts st s

variable {prims D dealt}

theorem semR_bind {α β : Type} (x : TableM C α) (f : α → TableM C β) (ts : TableState C) (st : TsigState C)
    (s : HashCache C) :
    semR prims dealt (x >>= f) ts st s =
      semR prims dealt x ts st s >>= fun z => semR prims dealt (f z.1.1.1) z.1.1.2 z.1.2 z.2 := by
  simp [semR, StateT.run_bind, simulateQ_bind]

theorem semW_bind {α β : Type} (y : WorldM C α) (g : α → WorldM C β) (log : CallLog C) (st : TsigState C)
    (c : HashCache C × HiddenCache C) :
    semW prims D (y >>= g) log st c =
      semW prims D y log st c >>= fun z => semW prims D (g z.1.1.1) z.1.1.2 z.1.2 z.2 := by
  simp [semW, StateT.run_bind, simulateQ_bind]

theorem Couple.pure {α : Type} (a : α) : Couple prims D dealt (Pure.pure a) (Pure.pure a) := by
  intro ts st s
  simp [semW, semR, image]

theorem Couple.bind {α β : Type} {x : TableM C α} {y : WorldM C α} {f : α → TableM C β} {g : α → WorldM C β}
    (hxy : Couple prims D dealt x y) (hfg : ∀ a, Couple prims D dealt (f a) (g a)) :
    Couple prims D dealt (x >>= f) (y >>= g) := by
  intro ts st s
  rw [semW_bind, hxy, semR_bind, bind_map_left, map_bind]
  exact bind_congr fun z => hfg z.1.1.1 z.1.1.2 z.1.2 z.2

theorem Couple.map {α β : Type} {x : TableM C α} {y : WorldM C α} (h : Couple prims D dealt x y) (f : α → β) :
    Couple prims D dealt (f <$> x) (f <$> y) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact h.bind fun a => Couple.pure (f a)

theorem Couple.simulateQ {ι : Type} {spec : OracleSpec ι} {implR : QueryImpl spec (TableM C)}
    {implW : QueryImpl spec (WorldM C)} (h : ∀ t, Couple prims D dealt (implR t) (implW t)) {α : Type}
    (oa : OracleComp spec α) : Couple prims D dealt (simulateQ implR oa) (simulateQ implW oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using Couple.pure a
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    exact (h t).bind ih

theorem Couple.forIn {γ β : Type} (l : List γ) (init : β) {f : γ → β → TableM C (ForInStep β)}
    {g : γ → β → WorldM C (ForInStep β)} (h : ∀ a b, Couple prims D dealt (f a b) (g a b)) :
    Couple prims D dealt (forIn l init f) (forIn l init g) := by
  induction l generalizing init with
  | nil => simpa using Couple.pure init
  | cons a l ih =>
    rw [List.forIn_cons, List.forIn_cons]
    refine (h a init).bind fun r => ?_
    cases r with
    | done b => exact Couple.pure b
    | yield b => exact ih b

theorem Couple.sequenceFin {α : Type} : ∀ {k : ℕ} {f : Fin k → TableM C α} {g : Fin k → WorldM C α},
    (∀ i, Couple prims D dealt (f i) (g i)) →
      Couple prims D dealt (OverPermutation.sequenceFin f) (OverPermutation.sequenceFin g)
  | 0, _, _, _ => by simpa [OverPermutation.sequenceFin] using Couple.pure _
  | _ + 1, _, _, h => by
    simp only [OverPermutation.sequenceFin]
    exact (h 0).bind fun a => (Couple.sequenceFin fun i => h i.succ).bind fun r => Couple.pure _

/-! ## A state above both monads -/

/-- `Couple` from each start of the state `σ`. -/
def CoupleS (prims : Primitives) (D : C.Coalition) (dealt : Dealt C (OracleComp (WorldSpec C))) {σ α : Type}
    (x : StateT σ (TableM C) α) (y : StateT σ (WorldM C) α) : Prop :=
  ∀ r, Couple prims D dealt (x.run r) (y.run r)

theorem CoupleS.pure {σ α : Type} (a : α) :
    CoupleS prims D dealt (Pure.pure a : StateT σ (TableM C) α) (Pure.pure a) :=
  fun r => by simpa using Couple.pure (a, r)

theorem CoupleS.bind {σ α β : Type} {x : StateT σ (TableM C) α} {y : StateT σ (WorldM C) α}
    {f : α → StateT σ (TableM C) β} {g : α → StateT σ (WorldM C) β}
    (hxy : CoupleS prims D dealt x y) (hfg : ∀ a, CoupleS prims D dealt (f a) (g a)) :
    CoupleS prims D dealt (x >>= f) (y >>= g) := fun r => by
  rw [StateT.run_bind, StateT.run_bind]
  exact (hxy r).bind fun p => hfg p.1 p.2

theorem CoupleS.lift {σ α : Type} {x : TableM C α} {y : WorldM C α} (h : Couple prims D dealt x y) :
    CoupleS prims D dealt (StateT.lift x : StateT σ (TableM C) α) (StateT.lift y) := fun r => by
  rw [StateT.run_lift, StateT.run_lift]
  exact h.bind fun a => Couple.pure (a, r)

theorem CoupleS.get {σ : Type} : CoupleS prims D dealt (get : StateT σ (TableM C) σ) get := fun r => by
  simpa using Couple.pure (r, r)

theorem CoupleS.set {σ : Type} (r' : σ) : CoupleS prims D dealt (set r' : StateT σ (TableM C) PUnit) (set r') :=
  fun r => by simpa using Couple.pure (PUnit.unit, r')

theorem CoupleS.modify {σ : Type} (f : σ → σ) :
    CoupleS prims D dealt (modify f : StateT σ (TableM C) PUnit) (modify f) := fun r => by
  simpa using Couple.pure (PUnit.unit, f r)

theorem CoupleS.map {σ α β : Type} {x : StateT σ (TableM C) α} {y : StateT σ (WorldM C) α}
    (h : CoupleS prims D dealt x y) (f : α → β) : CoupleS prims D dealt (f <$> x) (f <$> y) := by
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp]
  exact h.bind fun a => CoupleS.pure (f a)

theorem CoupleS.simulateQ {σ ι : Type} {spec : OracleSpec ι} {implR : QueryImpl spec (StateT σ (TableM C))}
    {implW : QueryImpl spec (StateT σ (WorldM C))} (h : ∀ t, CoupleS prims D dealt (implR t) (implW t)) {α : Type}
    (oa : OracleComp spec α) : CoupleS prims D dealt (simulateQ implR oa) (simulateQ implW oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using CoupleS.pure a
  | query_bind t k ih =>
    rw [simulateQ_query_bind, simulateQ_query_bind]
    exact (h t).bind ih

theorem CoupleS.run' {σ α : Type} {x : StateT σ (TableM C) α} {y : StateT σ (WorldM C) α}
    (h : CoupleS prims D dealt x y) (r : σ) : Couple prims D dealt (x.run' r) (y.run' r) := by
  rw [StateT.run'_eq, StateT.run'_eq]
  exact (h r).map _

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.CoupleS.run'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.CoupleS.run'
