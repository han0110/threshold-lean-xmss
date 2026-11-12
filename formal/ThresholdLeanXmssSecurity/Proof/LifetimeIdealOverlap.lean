import ThresholdLeanXmssSecurity.Proof.LifetimeIdealBad
import ThresholdLeanXmssSecurity.Proof.LifetimeRealBad

/-!
# The lifetime budget on the four-copy program

`HasLifetimeQueryBound` bounds every answer path of the real `lifetimeGame`. This module moves
that bound to `program4`, the program that `leftImpl` interprets in `HiddenKeyOverlapBound`.

* `program5` is the lifetime with five copies of the local oracles. The first four copies are
  those of `program4`. The honest operators of the runs after run `n` use the fifth copy.
* `collapse_program5` merges the adversary copy into the counted copy and the other four copies
  into the free copy. This gives `lifetimeGame`.
* `relabel_program5` moves the fifth copy into the adversary copy. This gives `program4`.
* `program4Budget` follows. Each query of `program4` costs `LocalCounted` of its local query,
  which is the `LifetimeCounted` charge of that query on either copy of the real lifetime. So
  every answer path of `program4` makes at most `Q` calls of `H` and `PRG`, for each `Th`.

The transport keeps `HasLifetimeQueryBound` as its only premise. No support restriction and no
probability enters it.

## The argument for `HiddenKeyOverlapBound` on paper

Fix run `n` and a hidden name.

1. The PRG takes a key only in `prssRandomness` (`Scheme.lean:461`), and the key is
   `ctx.prss`. The ceremony sets `ctx.prss` from its own `prssSetup` (`Scheme.lean:1194`).
2. All holders of a hidden term are honest, and so are both members of a hidden pair. The
   coalition sees only `toCoalition` messages. An honest message to an honest operator arrives
   unchanged (`roundInbox`, `Execution.lean:136`). `readReveal` reads at the index where
   `revealTo` writes. So all honest holders of the name in one run that reach `deriveKeys` query
   the same `.derive` input, and they get one key for each run.
3. `.start` needs `running = none`, and a round uses the roles of run `runCount - 1`. So every
   emulated query comes before every query of run `n`, and the first table holds at most `n` keys
   of the name when run `n` derives its key.
4. The `.derive` input of run `n` holds parts that run `n` samples freshly. The coalition sees no
   such part before the derivation. So the input is already in the hash cache with probability at
   most `Q / 2^256` (`program4Budget` counts every query on the path), and an equal input of an
   earlier run is one of these queries. Otherwise the fresh answer equals one of at most `n` earlier
   keys with probability at most `n / 2^256`, and `n ≤ lifetimeRuns attempts - 1`.
-/

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss

noncomputable section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace ThresholdLeanXmssSecurity.LifetimeIdealOverlap

open LifetimeEmulatedBudget LifetimePrfTransportProof LifetimeIdealBad

attribute [local instance] Classical.propDecidable

section Copies

variable {C : Committee}

/-- The charge of a local query. Private sampling is free, and each call of `H` or `PRG` costs
one. -/
def LocalCounted (t : (LocalSpec C).Domain) : Prop := LifetimeCounted (C := C) (.inr t)

/-- The local query under a query of the four-copy program. -/
def localOf4 : (Spec4 C).Domain → (LocalSpec C).Domain
  | .inl (.inl (.inl t)) => t
  | .inl (.inl (.inr t)) => t
  | .inl (.inr t) => t
  | .inr t => t

/-- The charge of a query of the four-copy program. -/
def Counted4 (t : (Spec4 C).Domain) : Prop := LocalCounted (localOf4 t)

/-- The four copies of `program4` and a fifth copy for the honest operators of the later runs. -/
abbrev Spec5 (C : Committee) := Spec4 C + LocalSpec C

def lift5 {α : Type} (p : OracleComp (Spec4 C) α) : OracleComp (Spec5 C) α :=
  simulateQ (fun t => (liftM ((Spec5 C).query (.inl t)) : OracleComp (Spec5 C) _)) p

def lateCopy5 {α : Type} (p : OracleComp (LocalSpec C) α) : OracleComp (Spec5 C) α :=
  simulateQ (fun t => (liftM ((Spec5 C).query (.inr t)) : OracleComp (Spec5 C) _)) p

/-- The run roles of `program5`. The roles of `roles4` stay, except that the honest operators of
the runs after run `n` use the fifth copy. -/
def roles5 (n r : ℕ) : Roles C (OracleComp (Spec5 C)) :=
  if r ≤ n then ⟨fun p => lift5 ((roles4 n r).adversary p), fun p => lift5 ((roles4 n r).honest p)⟩
  else ⟨fun p => lift5 (advCopy4 p), lateCopy5⟩

def base5 : Roles C (OracleComp (Spec5 C)) :=
  ⟨fun p => lift5 (advCopy4 p), fun p => lift5 (freeCopy4 p)⟩

/-- The fifth copy goes to the adversary copy. -/
def relabel5 : QueryImpl (Spec5 C) (OracleComp (Spec4 C))
  | .inl t => (liftM ((Spec4 C).query t) : OracleComp (Spec4 C) _)
  | .inr t => (liftM ((Spec4 C).query (.inl (.inl (.inl t)))) : OracleComp (Spec4 C) _)

/-- The adversary copy goes to the counted copy, and the other copies go to the free copy. -/
def collapse5 : QueryImpl (Spec5 C) (OracleComp (WorldSpec C))
  | .inl (.inl (.inl (.inl t))) => (liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _)
  | .inl (.inl (.inl (.inr t))) => (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _)
  | .inl (.inl (.inr t)) => (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _)
  | .inl (.inr t) => (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _)
  | .inr t => (liftM ((WorldSpec C).query (.inr t)) : OracleComp (WorldSpec C) _)

/-- The charge of a query of the five-copy program. -/
def Counted5 : (Spec5 C).Domain → Prop
  | .inl t => Counted4 t
  | .inr t => LocalCounted t

theorem counted_adversary (t : (LocalSpec C).Domain) :
    LifetimeCounted (C := C) (.inl (.inl t)) ↔ LocalCounted t := by
  rcases t with u | q | x <;> rfl

theorem relabel_lift5 {α : Type} (p : OracleComp (Spec4 C) α) :
    simulateQ relabel5 (lift5 p) = p := by
  rw [lift5, simulateQ_comp]
  refine (congrArg (fun f : QueryImpl (Spec4 C) (OracleComp (Spec4 C)) => simulateQ f p) ?_).trans
    (simulateQ_query_self p)
  funext t
  exact simulateQ_spec_query relabel5 (Sum.inl t)

theorem relabel_lateCopy5 {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ relabel5 (lateCopy5 p) = advCopy4 p := by
  rw [lateCopy5, simulateQ_comp, advCopy4]
  exact congrArg (fun f : QueryImpl (LocalSpec C) (OracleComp (Spec4 C)) => simulateQ f p)
    (funext fun t => simulateQ_spec_query relabel5 (Sum.inr t))

theorem collapse_lift5 {α : Type} (p : OracleComp (Spec4 C) α) :
    simulateQ collapse5 (lift5 p) = simulateQ (fun t => collapse5 (.inl t)) p := by
  rw [lift5, simulateQ_comp]
  exact congrArg (fun f : QueryImpl (Spec4 C) (OracleComp (WorldSpec C)) => simulateQ f p)
    (funext fun t => simulateQ_spec_query collapse5 (Sum.inl t))

theorem collapse_advCopy4 {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ collapse5 (lift5 (advCopy4 p)) = worldRoles.adversary p := by
  rw [collapse_lift5, advCopy4, LifetimeRealBad.worldAdversary_eq_simulateQ p]
  refine (simulateQ_comp _ _ p).trans ?_
  refine congrArg (fun f : QueryImpl (LocalSpec C) (OracleComp (WorldSpec C)) => simulateQ f p)
    (funext fun t => ?_)
  rw [LifetimeRealBad.adversary_query]
  exact simulateQ_spec_query _ _

theorem collapse_emulCopy4 {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ collapse5 (lift5 (emulCopy4 p)) = free p := by
  rw [collapse_lift5, emulCopy4, free]
  refine (simulateQ_comp _ _ p).trans ?_
  exact congrArg (fun f : QueryImpl (LocalSpec C) (OracleComp (WorldSpec C)) => simulateQ f p)
    (funext fun t => simulateQ_spec_query _ _)

theorem collapse_freeCopy4 {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ collapse5 (lift5 (freeCopy4 p)) = free p := by
  rw [collapse_lift5, freeCopy4, free]
  refine (simulateQ_comp _ _ p).trans ?_
  exact congrArg (fun f : QueryImpl (LocalSpec C) (OracleComp (WorldSpec C)) => simulateQ f p)
    (funext fun t => simulateQ_spec_query _ _)

theorem collapse_targetCopy4 {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ collapse5 (lift5 (targetCopy4 p)) = free p := by
  rw [collapse_lift5, targetCopy4, free]
  refine (simulateQ_comp _ _ p).trans ?_
  exact congrArg (fun f : QueryImpl (LocalSpec C) (OracleComp (WorldSpec C)) => simulateQ f p)
    (funext fun t => simulateQ_spec_query _ _)

theorem collapse_lateCopy5 {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ collapse5 (lateCopy5 p) = free p := by
  rw [lateCopy5, simulateQ_comp, free]
  exact congrArg (fun f : QueryImpl (LocalSpec C) (OracleComp (WorldSpec C)) => simulateQ f p)
    (funext fun t => simulateQ_spec_query collapse5 (Sum.inr t))

theorem collapse_roles5 (n r : ℕ) :
    RolesHom (simulateQ' (collapse5 (C := C))) (roles5 n r) worldRoles := by
  unfold roles5
  by_cases hle : r ≤ n
  · rw [if_pos hle]
    by_cases hlt : r < n
    · simp only [roles4, if_pos hlt]
      exact ⟨fun p => collapse_advCopy4 p, fun p => collapse_emulCopy4 p⟩
    · simp only [roles4, if_neg hlt, if_pos (show r = n by omega)]
      exact ⟨fun p => collapse_advCopy4 p, fun p => collapse_targetCopy4 p⟩
  · rw [if_neg hle]
    exact ⟨fun p => collapse_advCopy4 p, fun p => collapse_lateCopy5 p⟩

theorem collapse_base5 : RolesHom (simulateQ' (collapse5 (C := C))) base5 worldRoles :=
  ⟨fun p => collapse_advCopy4 p, fun p => collapse_freeCopy4 p⟩

theorem relabel_roles5 (n r : ℕ) :
    RolesHom (simulateQ' (relabel5 (C := C))) (roles5 n r) (roles4 n r) := by
  unfold roles5
  split
  · exact ⟨fun _ => relabel_lift5 _, fun _ => relabel_lift5 _⟩
  · rename_i h
    have hr : roles4 (C := C) n r = ⟨advCopy4, advCopy4⟩ := by
      simp [roles4, show ¬ r < n by omega, show r ≠ n by omega]
    rw [hr]
    exact ⟨fun _ => relabel_lift5 _, fun p => relabel_lateCopy5 p⟩

theorem relabel_base5 : RolesHom (simulateQ' (relabel5 (C := C))) base5 base4 :=
  ⟨fun _ => relabel_lift5 _, fun _ => relabel_lift5 _⟩

/-- Merging the copies charges each five-copy query its real lifetime charge. -/
theorem bound5_of_collapse {α : Type} (p : OracleComp (Spec5 C) α) (Q : ℕ)
    (h : IsQueryBoundP (simulateQ collapse5 p) LifetimeCounted Q) :
    IsQueryBoundP p Counted5 Q := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query] at h
    rw [isQueryBoundP_query_bind_iff]
    rcases t with (((t | t) | t) | t) | t
    · change IsQueryBoundP ((liftM ((WorldSpec C).query (.inl (.inl t))) : OracleComp (WorldSpec C) _) >>= _)
        LifetimeCounted Q at h
      rw [isQueryBoundP_query_bind_iff,
        show LifetimeCounted (C := C) (.inl (.inl t)) = Counted5 (.inl (.inl (.inl (.inl t)))) from
          propext (counted_adversary t)] at h
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩
    all_goals
      change IsQueryBoundP ((liftM ((WorldSpec C).query (.inr _)) : OracleComp (WorldSpec C) _) >>= _)
        LifetimeCounted Q at h
      rw [isQueryBoundP_query_bind_iff] at h
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

/-- Relabelling the fifth copy keeps the charge of each query. -/
theorem bound4_of_relabel {α : Type} (p : OracleComp (Spec5 C) α) (Q : ℕ)
    (h : IsQueryBoundP p Counted5 Q) :
    IsQueryBoundP (simulateQ relabel5 p) Counted4 Q := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure a => trivial
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at h
    rw [simulateQ_bind, simulateQ_spec_query]
    rcases t with t | t
    · change IsQueryBoundP ((liftM ((Spec4 C).query t) : OracleComp (Spec4 C) _) >>= _) Counted4 Q
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩
    · change IsQueryBoundP ((liftM ((Spec4 C).query (.inl (.inl (.inl t)))) : OracleComp (Spec4 C) _) >>= _)
        Counted4 Q
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨h.1, fun u => ih u _ (h.2 u)⟩

end Copies

section Budget

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (attempts : ℕ)
variable (D : C.Coalition) (A : LifetimeAdversary C E)

/-- The lifetime of hop `n` with the honest operators of the later runs on the fifth copy. -/
def program5 (n : ℕ) : OracleComp (Spec5 C) Bool :=
  lifetimeGameWith K circuits settings attempts (roles5 n) base5 D A

/-- Merging the copies gives the real lifetime. -/
theorem collapse_program5 (n : ℕ) :
    simulateQ collapse5 (program5 K circuits settings attempts D A n) =
      lifetimeGame K circuits settings attempts D A :=
  hom_lifetimeGameWith (simulateQ' collapse5) K circuits settings attempts
    (roles5 n) base5 (fun _ => worldRoles) worldRoles (collapse_roles5 n) collapse_base5 D A

/-- Moving the fifth copy into the adversary copy gives `program4`. -/
theorem relabel_program5 (n : ℕ) :
    simulateQ relabel5 (program5 K circuits settings attempts D A n) =
      program4 D K circuits settings attempts A n :=
  hom_lifetimeGameWith (simulateQ' relabel5) K circuits settings attempts
    (roles5 n) base5 (roles4 n) base4 (relabel_roles5 n) relabel_base5 D A

/-- Every answer path of `program4` costs at most the all-answer budget of the real lifetime at
the same circuits. -/
theorem program4Budget_of_real (Q n : ℕ)
    (hQ : IsQueryBoundP (lifetimeGame K circuits settings attempts D A) LifetimeCounted Q) :
    IsQueryBoundP (program4 D K circuits settings attempts A n) Counted4 Q := by
  rw [← collapse_program5 K circuits settings attempts D A n] at hQ
  rw [← relabel_program5 K circuits settings attempts D A n]
  exact bound4_of_relabel _ Q (bound5_of_collapse _ Q hQ)

variable (circuitsOf : (HashInput → HashOutput) → Circuits)

/-- `HasLifetimeQueryBound` bounds every answer path of `program4` by `Q`, for each `Th`. This is
the program that `leftImpl` interprets in `HiddenKeyOverlapBound`. -/
theorem program4Budget (Q : ℕ) (hQ : HasLifetimeQueryBound K settings attempts circuitsOf D A Q)
    (n : ℕ) (values : MpcDomain → HashOutput) :
    IsQueryBoundP (program4 D K (circuitsOf (thOf values)) settings attempts A n) Counted4 Q :=
  program4Budget_of_real K (circuitsOf (thOf values)) settings attempts D A Q n (hQ values)

end Budget

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealOverlap.collapse_program5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms collapse_program5

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealOverlap.relabel_program5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms relabel_program5

/-- info: 'ThresholdLeanXmssSecurity.LifetimeIdealOverlap.program4Budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms program4Budget

end ThresholdLeanXmssSecurity.LifetimeIdealOverlap
