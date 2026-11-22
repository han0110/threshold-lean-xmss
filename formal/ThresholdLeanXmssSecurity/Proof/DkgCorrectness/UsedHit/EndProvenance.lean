import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.UsedHit.EndTable
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Draws.OneKey
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Collision.SetupBudgets

/-!
# The hidden keys at the end of the game with a table

`TableAllows F` allows under a name the entries of the table `F` of that name. In the game with the
table `F`, each honest call of `PRG` under a hidden name has a key that `TableAllows F` allows
(`tableGame_noBad`). An operator reads a fresh key only as the key of its hidden name
(`nameKey_overlay_hidden`), and each ceremony of an allowed run has a slot below `gameSetups`. The
private table of `jointKeyWorld` gets an entry only from such a call, so `keyProvenance` proves
`KeyProvenance`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

open DigestBudgets (ClassBound StateBound)
open Draws (NoBad NoBadS)
open UsedHit (Entry Table entryName tableFresh)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_sequenceFin)

attribute [local instance] Classical.propDecidable

attribute [local irreducible] wrongOutput

/-! ## The keys of an overlay -/

section Overlay

variable {C : Committee}

/-- The table `F` allows under the name `N` each entry of `F` of that name. -/
def TableAllows {n : ℕ} (F : Table C n) (N : KeyName C) (k : HashOutput) : Prop :=
  ∃ x : Entry C n, entryName x.2 = N ∧ F x = k

/-- A key of the overlay of the fresh keys `fresh` under a hidden name is a fresh key of that name. -/
theorem nameKey_overlay_hidden (D : C.Coalition) (i : C.Party) (prss : PrssKeys C) (fresh : FreshKeys C)
    (N : KeyName C) (k : HashOutput) (h : NameKey i (prssOverlay D i prss fresh) N k) (hN : Hidden D N) :
    (∃ T, N = .term T ∧ k = fresh.1 T) ∨ (∃ p, N = .pair p ∧ k = fresh.2 p) := by
  rcases h with ⟨T, hi, rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩
  · refine Or.inl ⟨T, rfl, ?_⟩
    have hT : ¬ KnownTo D.1 T := hN
    simp [prssOverlay, seedGenHiddenOverlay, dealtKeys, hT, hi]
  · refine Or.inr ⟨_, rfl, ?_⟩
    have hij : i ∉ D.1 ∧ j ∉ D.1 := by
      obtain ⟨h1, h2⟩ := hN
      rcases Draws.pairOf_ends i j (Ne.symm hj) with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1] at h1
        rw [e2] at h2
        exact ⟨h1, h2⟩
      · rw [e1] at h1
        rw [e2] at h2
        exact ⟨h2, h1⟩
    simp [prssOverlay, seedGenHiddenOverlay, dealtKeys, hij.1, hij.2, hj]

end Overlay

/-! ## The draws of the programs of a run -/

section Programs

variable {C : Committee} {E : Type} (D : C.Coalition) (S : KeyName C → HashOutput → Prop)

/-- A program with no bad draw for `A` has no bad draw for `A'`, when `A'` allows each key that `A`
allows under a hidden name. -/
theorem noBad_mono {A : KeyName C → HashOutput → Prop} {α : Type} {p : PartyM C E RealSpec α}
    (hA : ∀ N k, Hidden D N → A N k → S N k) (h : NoBad D A p) : NoBad D S p :=
  IsQueryBoundP.of_imp (fun t ht => by
    rcases t with ((_ | _ | x) | _) | _
    · exact ht.elim
    · exact ht.elim
    · exact ⟨ht.1, fun hA' => ht.2 (hA _ _ ht.1 hA')⟩
    · exact ht.elim
    · exact ht.elim) h

theorem noBad_bind_supp {α β : Type} {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β}
    (h : NoBad D S p) (hf : ∀ a, NoBad D S (f a)) : NoBad D S (p >>= f) :=
  Draws.NoBad.bind h hf

theorem noBad_map {α β : Type} {p : PartyM C E RealSpec α} (f : α → β) (h : NoBad D S p) :
    NoBad D S (f <$> p) := by
  rw [map_eq_bind_pure_comp]
  exact Draws.NoBad.bind h fun _ => isQueryBoundP_pure _ _ _

/-- A program on the counters of a run and of the ceremonies that moves the ceremony counter from `n`
to `m` and has no bad draw for `S`. -/
def Steps {α : Type} (x : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α) (n m : ℕ) : Prop :=
  ∀ s, ∃ Y : PartyM C E RealSpec (α × (ℕ × ℕ)), (x.run s).run n = (fun p => (p, m)) <$> Y ∧ NoBad D S Y

/-- A program on the counters with no bad draw for `S` from the ceremony counter `n`. -/
def NoBadAt {α : Type} (x : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α) (n : ℕ) : Prop :=
  ∀ s, NoBad D S ((x.run s).run n)

variable {D S}

theorem Steps.pure {α : Type} (a : α) (n : ℕ) :
    Steps D S (pure a : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α) n n := fun s =>
  ⟨Pure.pure (a, s), by simp, isQueryBoundP_pure _ _ _⟩

theorem Steps.lift {α : Type} {y : PartyM C E RealSpec α} (h : NoBad D S y) (n : ℕ) :
    Steps D S (StateT.lift (StateT.lift y) : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α) n n := fun s =>
  ⟨(fun a => (a, s)) <$> y, by simp, noBad_map D S _ h⟩

theorem Steps.get (n : ℕ) :
    Steps D S (get : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) (ℕ × ℕ)) n n := fun s =>
  ⟨Pure.pure (s, s), by simp, isQueryBoundP_pure _ _ _⟩

theorem Steps.set (s' : ℕ × ℕ) (n : ℕ) :
    Steps D S (set s' : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) PUnit) n n := fun s =>
  ⟨Pure.pure (PUnit.unit, s'), by simp, isQueryBoundP_pure _ _ _⟩

theorem Steps.bind {α β : Type} {x : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α}
    {f : α → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) β} {n m k : ℕ} (hx : Steps D S x n m)
    (hf : ∀ a, Steps D S (f a) m k) : Steps D S (x >>= f) n k := fun s => by
  obtain ⟨Y, hY, hYb⟩ := hx s
  choose G hG hGb using fun (p : α × (ℕ × ℕ)) => hf p.1 p.2
  refine ⟨Y >>= G, ?_, Draws.NoBad.bind hYb hGb⟩
  rw [StateT.run_bind, StateT.run_bind, hY, bind_map_left, map_bind]
  exact bind_congr fun p => hG p

theorem NoBadAt.bind {α β : Type} {x : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α}
    {f : α → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) β} {n m : ℕ} (hx : Steps D S x n m)
    (hf : ∀ a, NoBadAt D S (f a) m) : NoBadAt D S (x >>= f) n := fun s => by
  obtain ⟨Y, hY, hYb⟩ := hx s
  rw [StateT.run_bind, StateT.run_bind, hY, bind_map_left]
  exact Draws.NoBad.bind hYb fun p => hf p.1 p.2

theorem NoBadAt.of_steps {α : Type} {x : StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α} {n m : ℕ}
    (hx : Steps D S x n m) : NoBadAt D S x n := fun s => by
  obtain ⟨Y, hY, hYb⟩ := hx s
  rw [hY]
  exact noBad_map D S _ hYb

theorem Steps.mapM {α β : Type} (f : α → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) β) (n : ℕ)
    (hf : ∀ a, Steps D S (f a) n n) : ∀ xs : List α, Steps D S (xs.mapM f) n n
  | [] => by simpa using Steps.pure (D := D) (S := S) ([] : List β) n
  | a :: xs => by
    rw [List.mapM_cons]
    exact (hf a).bind fun b => (Steps.mapM f n hf xs).bind fun bs => Steps.pure _ _

theorem steps_get_bind {β : Type} {f : ℕ → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) β} {n k : ℕ}
    (hf : Steps D S (f n) n k) :
    Steps D S (StateT.lift (get : StateT ℕ (PartyM C E RealSpec) ℕ) >>= f) n k := fun s => by
  obtain ⟨Y, hY, hYb⟩ := hf s
  exact ⟨Y, by simpa using hY, hYb⟩

theorem steps_set_bind {β : Type} {f : PUnit → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) β} {n m k : ℕ}
    (hf : Steps D S (f PUnit.unit) m k) :
    Steps D S (StateT.lift (set m : StateT ℕ (PartyM C E RealSpec) PUnit) >>= f) n k := fun s => by
  obtain ⟨Y, hY, hYb⟩ := hf s
  refine ⟨Y, ?_, hYb⟩
  rw [← hY]
  rfl

variable [Field E] [Algebra Bit E] (K : Constants C E) (circuits : Circuits) (settings : Settings)

attribute [local instance] inhabitedField

/-- A slot ceremony at the ceremony counter `c` with fresh keys `fk` moves the counter to `c + 1`. It has
no bad draw for `S` when `S` allows each key of the overlay of `fk` under a hidden name. -/
theorem slotCeremony_steps (fresh : ℕ → Option (FreshKeys C)) (i : C.Party) (keys : Keys C) (jobs : List Job)
    (c : ℕ) (fk : FreshKeys C) (hc : fresh c = some fk)
    (hgood : ∀ prss N k, Hidden D N → NameKey i (prssOverlay D i prss fk) N k → S N k) :
    Steps D S (slotCeremony K circuits settings D fresh i keys jobs) c (c + 1) := by
  unfold slotCeremony
  refine steps_get_bind (steps_set_bind ?_)
  refine Steps.bind (Steps.lift (Draws.NoBad.of_class (DigestBudgets.prssSetup_bound (c := .stream) nofun i)) _)
    fun prss => ?_
  simp only [hc, Option.map_some, Option.getD_some]
  unfold batched
  refine Steps.bind (Steps.mapM _ _ (fun js => ?_) _) fun _ => Steps.pure _ _
  refine Steps.bind (Steps.get _) fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine Steps.bind (Steps.lift (Draws.NoBad.of_class ((ClassBound.mapM _ 0
    (fun job => DigestBudgets.inputShares_bound (c := .stream) _ nofun job) _).mono (by simp))) _) fun inputs => ?_
  refine Steps.bind (Steps.lift (noBad_mono D S (fun N k hN hk => hgood prss N k hN hk)
    (Draws.runJobs_noBad (ctx := ⟨i, keys, prssOverlay D i prss fk⟩) K _ _ _ _)) _) fun r => ?_
  rcases r with ⟨outputs, state⟩
  exact Steps.bind (Steps.set _ _) fun _ => Steps.pure _ _

omit [Field E] [Algebra Bit E] in
/-- The ceremonies of a tree have no bad draw, when each ceremony of index below `treeSetups tree`
moves the counter by one with no bad draw and the local steps have none. -/
theorem noBadAt_ceremonyOutput
    (lift : ∀ {α : Type}, OracleComp HashSpec α → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) α)
    (hlift : ∀ {α : Type} (oa : OracleComp HashSpec α) (n : ℕ), Steps D S (lift oa) n n) (parameter : PublicParameter)
    (run : List Job → StateT (ℕ × ℕ) (StateT ℕ (PartyM C E RealSpec)) (Option (List (List Bit)))) (top : TopTree)
    (tree : Tree) (hrun : ∀ jobs c, c < treeSetups tree → Steps D S (run jobs) c (c + 1)) :
    NoBadAt D S (ceremonyOutput lift parameter run top tree) 0 := by
  cases tree with
  | top =>
    unfold ceremonyOutput
    refine NoBadAt.bind (hrun _ 0 (by simp [treeSetups])) fun o => ?_
    rcases o with _ | outputs
    · exact NoBadAt.of_steps (Steps.pure _ _)
    · exact NoBadAt.of_steps (Steps.bind (hlift _ _) fun _ => Steps.pure _ _)
  | bottom b =>
    unfold ceremonyOutput
    refine NoBadAt.bind (hrun _ 0 (by simp [treeSetups])) fun o => ?_
    rcases o with _ | outputs
    · exact NoBadAt.of_steps (Steps.pure _ _)
    refine NoBadAt.bind (hlift _ _) fun root => ?_
    refine NoBadAt.bind (hlift _ _) fun base => ?_
    refine NoBadAt.bind (hlift _ _) fun found => ?_
    rcases found with _ | ⟨randomness, encoding⟩
    · exact NoBadAt.of_steps (Steps.pure _ _)
    refine NoBadAt.bind (hrun _ 1 (by simp [treeSetups])) fun out => ?_
    rcases out with _ | values
    · exact NoBadAt.of_steps (Steps.pure _ _)
    refine NoBadAt.bind (hlift _ _) fun path => ?_
    refine NoBadAt.bind (hlift _ _) fun topRoot => ?_
    split_ifs
    · exact NoBadAt.of_steps (Steps.pure _ _)
    · exact NoBadAt.of_steps (Steps.pure _ _)

/-- The fresh keys `fk` are entries of the table `F` under their names. -/
def GoodFor {n : ℕ} (F : Table C n) (fk : FreshKeys C) : Prop :=
  (∀ T, TableAllows F (.term T) (fk.1 T)) ∧ ∀ p, TableAllows F (.pair p) (fk.2 p)

omit [Field E] [Algebra Bit E] in
theorem goodFor_tableFresh {n : ℕ} (F : Table C n) (slot : ℕ) (h : slot < n) :
    ∃ fk, tableFresh F slot = some fk ∧ GoodFor F fk :=
  ⟨(fun T => F (⟨slot, h⟩, .inl T), fun p => F (⟨slot, h⟩, .inr p)), by simp [tableFresh, h],
    fun T => ⟨(⟨slot, h⟩, .inl T), rfl, rfl⟩, fun p => ⟨(⟨slot, h⟩, .inr p), rfl, rfl⟩⟩

/-- The program of an operator in a run of `tree` has no bad draw for the table `F`, when each
ceremony of the run has fresh keys from `F`. -/
theorem slotProgram_noBad {n : ℕ} (F : Table C n) (fresh : ℕ → Option (FreshKeys C)) (tree : Tree)
    (hfresh : ∀ c, c < treeSetups tree → ∃ fk, fresh c = some fk ∧ GoodFor F fk) (i : C.Party)
    (operator : OperatorState C) :
    NoBad D (TableAllows F) (slotProgram K circuits settings D fresh i operator tree) := by
  have htree : ∀ keys top, NoBad D (TableAllows F) (slotTree K circuits settings D fresh i keys top tree) := by
    intro keys top
    have hX := noBadAt_ceremonyOutput (D := D) (S := TableAllows F)
      (fun oa => StateT.lift (StateT.lift (oracleStep (tweakable oa))))
      (fun oa n => Steps.lift (Draws.NoBad.of_class (DigestBudgets.ClassBound.oracleStep_zero
        (DigestBudgets.noCall_of_onlySign (c := .stream) nofun (GameCount.onlySign_tweakable oa)))) n)
      keys.parameter (slotCeremony K circuits settings D fresh i keys) top tree (fun jobs c hc => by
        obtain ⟨fk, hfk, hgood⟩ := hfresh c hc
        refine slotCeremony_steps K circuits settings fresh i keys jobs c fk hfk fun prss N k hN hk => ?_
        rcases nameKey_overlay_hidden D i prss fk N k hk hN with ⟨T, rfl, rfl⟩ | ⟨p, rfl, rfl⟩
        · exact hgood.1 T
        · exact hgood.2 p)
    unfold slotTree
    refine noBad_bind_supp D _ ?_ fun o => ?_
    · simp only [StateT.run'_eq, StateT.run_map]
      exact noBad_map D _ _ (noBad_map D _ _ (hX (0, 0)))
    · rcases o with _ | output
      · exact isQueryBoundP_pure _ _ _
      · exact isQueryBoundP_pure _ _ _
  cases tree with
  | top =>
    unfold slotProgram
    rcases operator.keys with _ | keys
    · exact isQueryBoundP_pure _ _ _
    · exact htree keys _
  | bottom b =>
    unfold slotProgram
    rcases operator.keys with _ | keys <;> rcases operator.top with _ | top
    · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_pure _ _ _
    · exact isQueryBoundP_pure _ _ _
    · exact htree keys top

end Programs

/-! ## The private table of `jointKeyWorld` -/

section World

variable {C : Committee} (prims : Primitives) (D : C.Coalition)

/-- An honest call of `PRG` under a hidden name with a key that `A` does not allow. -/
abbrev WorldBad (A : KeyName C → HashOutput → Prop) : (WorldSpec C).Domain → Prop :=
  SetupBudgets.HonestP (Draws.BadDraw D A)

/-- The keys of the private table lie in `A`. -/
def KeysIn (A : KeyName C → HashOutput → Prop) (s : KeyJointState C) : Prop :=
  ∀ n k, s.keys (n, k) ≠ none → A n k

/-- One call of the ideal joint world keeps `KeysIn A` when it is no bad honest call. -/
theorem jointKeyWorld_keysIn (A : KeyName C → HashOutput → Prop) (t : (WorldSpec C).Domain)
    (ht : ¬ WorldBad D A t) (s : KeyJointState C) (hs : KeysIn A s) :
    ∀ r ∈ support ((jointKeyWorld prims D false t).run s), KeysIn A r.2 := by
  intro r hr
  simp only [jointKeyWorld, StateT.run_mk, support_map, Set.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  show KeysIn A p.2
  have hhash : ∀ (m : StateT (HashCache C) ProbComp ((WorldSpec C).Range t)),
      p ∈ support ((onJointHash m).run s) → KeysIn A p.2 := fun m hm => by
    obtain ⟨z, -, rfl⟩ := onJointHash_support _ s p hm
    exact hs
  rcases t with ((u | q | x) | ⟨q, v⟩) | (u | q | x)
  · exact hhash (localAnswer prims (.inl u)) (by rw [← jointLocal_false]; exact hp)
  · exact hhash _ (by rw [← jointHash_false]; exact hp)
  · exact hhash (localAnswer prims (.inr (.inr x))) (by rw [← jointLocal_false]; exact hp)
  · exact hhash _ (by rw [← jointProgram_false]; exact hp)
  · exact hhash (localAnswer prims (.inl u)) (by rw [← jointLocal_false]; exact hp)
  · exact hhash _ (by rw [← jointHash_false]; exact hp)
  · by_cases hh : Hidden D x.1
    · have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) = (do
          let h ← jointHidden false (x.1, x.2.1)
          pure (prims.aes.eval (truncateHash h) x.2.2)) := by
        simp only [jointKeyWorldCore, hh, ↓reduceIte]
      rw [hc] at hp
      simp only [StateT.run_bind, StateT.run_pure, support_bind, support_pure, Set.mem_iUnion,
        Set.mem_singleton_iff] at hp
      obtain ⟨w, hw, rfl⟩ := hp
      have hA : A x.1 x.2.1 := by
        by_contra hn
        exact ht ⟨hh, hn⟩
      rcases hk : s.keys (x.1, x.2.1) with _ | v
      · have hrun : (jointHidden false (x.1, x.2.1)).run s = (do
            let v ← $ᵗ HashOutput
            pure (v, (⟨s.hash, s.keys.cacheQuery (x.1, x.2.1) v,
              (if (s.used x.2.1).isSome then s.used else Function.update s.used x.2.1 (some x.1)),
              s.bad⟩ : KeyJointState C))) := by
          simp only [jointHidden, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, StateT.run_mk, hk]
        rw [hrun] at hw
        simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hw
        obtain ⟨v, -, rfl⟩ := hw
        intro n k hnk
        by_cases he : (n, k) = (x.1, x.2.1)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          exact hA
        · exact hs n k (by simpa [QueryCache.cacheQuery_of_ne _ _ he] using hnk)
      · have hrun : (jointHidden false (x.1, x.2.1)).run s = pure (v, s) := by
          simp only [jointHidden, Bool.false_eq_true, ↓reduceIte, bind_pure_comp, StateT.run_mk, hk]
        rw [hrun, support_pure, Set.mem_singleton_iff] at hw
        subst hw
        exact hs
    · have hc : jointKeyWorldCore prims D false (.inr (.inr (.inr x))) = jointLocal prims false (.inr (.inr x)) := by
        simp only [jointKeyWorldCore, hh, ↓reduceIte]
      rw [hc] at hp
      exact hhash (localAnswer prims (.inr (.inr x))) (by rw [← jointLocal_false]; exact hp)

/-- A computation of the world with no bad honest call keeps `KeysIn A` in the ideal joint world. -/
theorem simulateQ_keysIn (A : KeyName C → HashOutput → Prop) {α : Type} (oa : OracleComp (WorldSpec C) α)
    (h : IsQueryBoundP oa (WorldBad D A) 0) :
    ∀ s, KeysIn A s → ∀ r ∈ support ((simulateQ (jointKeyWorld prims D false) oa).run s), KeysIn A r.2 := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro s hs r hr
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst hr
    exact hs
  | query_bind t k ih =>
    intro s hs r hr
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hr
    obtain ⟨y, hy, hr⟩ := hr
    have ht : ¬ WorldBad D A t := by
      rcases h.1 with h1 | h1
      · exact h1
      · omega
    have hk := h.2 y.1
    simp only [ht, ↓reduceIte] at hk
    exact ih y.1 hk y.2 (jointKeyWorld_keysIn prims D A t ht s hs y hy) r hr

end World

/-! ## The walk of the game with a table -/

section Game

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)
  (D : C.Coalition) (F : Table C (gameSetups runLimit))

attribute [local instance] inhabitedField

/-- Each tree has at most `runLimit` runs. -/
def RunsIn {σ : Type} (s : RealState C σ) : Prop := ∀ tree, s.runs tree ≤ runLimit

/-- From each state with at most `runLimit` runs of each tree, `m` makes no bad honest call for the
table `F`, and it ends in such a state. -/
def RKeeps {σ α : Type} (m : RealM C σ α) : Prop :=
  ∀ s, RunsIn runLimit s → IsQueryBoundP (m.run s) (WorldBad D (TableAllows F)) 0 ∧
    ∀ z ∈ support (m.run s), RunsIn runLimit z.2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A ceremony of an allowed run has a slot below `gameSetups`. -/
theorem setupsBefore_add_lt (runs : Tree → ℕ) (hruns : ∀ tree, runs tree ≤ runLimit) (tree : Tree)
    (hrun : runs tree < runLimit) (c : ℕ) (hc : c < treeSetups tree) :
    setupsBefore runs + c < gameSetups runLimit := by
  have hsum : ∀ T : Finset (Fin (2 ^ layerHeight)),
      ∑ b ∈ T, runs (.bottom b) * treeSetups (.bottom b) ≤ T.card * (runLimit * 2) := fun T => by
    rw [Finset.card_eq_sum_ones, Finset.sum_mul]
    exact Finset.sum_le_sum fun b _ => by simp only [treeSetups, one_mul]; nlinarith [hruns (.bottom b)]
  have hcard : (Finset.univ : Finset (Fin (2 ^ layerHeight))).card = 2 ^ layerHeight := by simp
  have hpos : 0 < 2 ^ layerHeight := by positivity
  unfold setupsBefore gameSetups
  cases tree with
  | top =>
    simp only [treeSetups, Nat.lt_one_iff] at hc ⊢
    subst hc
    have := hsum Finset.univ
    rw [hcard] at this
    simp only [treeSetups] at this
    nlinarith
  | bottom b =>
    simp only [treeSetups] at hc ⊢
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
    have := hsum (Finset.univ.erase b)
    rw [Finset.card_erase_of_mem (Finset.mem_univ b), hcard] at this
    have htop := hruns .top
    simp only [treeSetups] at this
    generalize ∑ x ∈ Finset.univ.erase b, runs (Tree.bottom x) * 2 = X at this ⊢
    obtain ⟨N, hN⟩ : ∃ N, 2 ^ layerHeight = N + 1 := ⟨2 ^ layerHeight - 1, by omega⟩
    rw [hN, Nat.add_sub_cancel] at this
    rw [hN]
    nlinarith

omit [Fintype E] [DecidableEq E] in
/-- The fresh keys of the ceremonies of an allowed run are entries of the table. -/
theorem runFresh_good (runs : Tree → ℕ) (hruns : ∀ tree, runs tree ≤ runLimit) (tree : Tree)
    (hrun : runs tree < runLimit) (c : ℕ) (hc : c < treeSetups tree) :
    ∃ fk, (List.map (fun x => tableFresh F (setupsBefore runs + x)) (List.range (treeSetups tree))).getD c none =
      some fk ∧ GoodFor F fk := by
  obtain ⟨fk, hfk, hgood⟩ := goodFor_tableFresh F _ (setupsBefore_add_lt runLimit runs hruns tree hrun c hc)
  refine ⟨fk, ?_, hgood⟩
  rw [← hfk, List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range]

omit [Fintype E] [DecidableEq E] in
/-- The honest programs of an allowed run make no bad call. -/
theorem runPrograms_noBad {σ : Type} (s : RealState C σ) (hs : RunsIn runLimit s) (tree : Tree)
    (hrun : s.runs tree < runLimit) (j : C.Party) :
    IsQueryBoundP (slotProgram K circuits settings D
      (fun c => (List.map (fun x => tableFresh F (setupsBefore s.runs + x)) (List.range (treeSetups tree))).getD c none)
      j (s.operators j) tree).run (SetupBudgets.PartyP (E := E) (Draws.BadDraw D (TableAllows F))) 0 :=
  IsQueryBoundP.of_imp (fun t ht => by
    rcases t with (t | _) | _
    · exact ht
    · exact ht.elim
    · exact ht.elim) (slotProgram_noBad (D := D) K circuits settings F _ tree
      (runFresh_good runLimit F s.runs hs tree hrun) j _)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The monitor makes no bad call. -/
theorem wrongOutput_noBad (keys : C.Party → Option (Keys C)) (tree : Tree) (outputs : C.Party → Option TreeOutput) :
    IsQueryBoundP (wrongOutput D keys tree outputs) (WorldBad D (TableAllows F)) 0 :=
  (noCall_iff _ _).1 (GameCount.wrongOutput_noCall D _ (fun t ht hp => by
    rcases t with (_ | _) | (_ | _ | x)
    · exact ht
    · exact ht
    · exact ht
    · exact hp
    · exact ht) _ _ _)

omit [Fintype E] [DecidableEq E] in
/-- An allowed run of `tree` makes no bad call, and it keeps the bound on the runs. -/
theorem drawTreeRun_keeps (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree)
    (s : RealState C net.State) (hs : RunsIn runLimit s) (hrun : s.runs tree < runLimit) :
    IsQueryBoundP ((UsedHit.drawTreeRun K circuits settings (fun slot => pure (tableFresh F slot)) (wrongOutput D) D
      net tree).run s) (WorldBad D (TableAllows F)) 0 ∧
      ∀ z ∈ support ((UsedHit.drawTreeRun K circuits settings (fun slot => pure (tableFresh F slot)) (wrongOutput D) D
        net tree).run s), RunsIn runLimit z.2 := by
  unfold UsedHit.drawTreeRun
  simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_assoc, StateT.run_set,
    List.mapM_pure, liftComp_pure, free_pure]
  refine ⟨(isQueryBoundP_bind (n := 0) (m := 0) ((SetupBudgets.executePhase_boundP _ D net _ _ _ (fun _ => 0)
    fun j _ => runPrograms_noBad K circuits settings runLimit D F s hs tree hrun j).mono (by simp)) fun r _ =>
      (isQueryBoundP_bind (n := 0) (m := 0) (wrongOutput_noBad runLimit D F _ _ _) fun _ _ =>
        isQueryBoundP_pure _ _ _).mono le_rfl).mono le_rfl, fun z hz => ?_⟩
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨r, -, y, -, rfl⟩ := hz
  intro tree'
  by_cases ht : tree' = tree
  · subst ht
    simp only [Function.update_self]
    omega
  · simp only [Function.update_of_ne ht]
    exact hs tree'

end Game

section Walk

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (K : Constants C E) (circuits : Circuits) (settings : Settings) {runLimit : ℕ}
  {D : C.Coalition} {F : Table C (gameSetups runLimit)}

attribute [local instance] inhabitedField

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A bad call is an honest call in class `stream`. -/
theorem worldBad_of_honestIn {β : Type} {oa : OracleComp (WorldSpec C) β}
    (h : IsQueryBoundP oa (HonestIn .stream) 0) : IsQueryBoundP oa (WorldBad D (TableAllows F)) 0 :=
  IsQueryBoundP.of_imp (fun t ht => by
    rcases t with _ | (_ | _ | _)
    · exact ht.elim
    · exact ht.elim
    · exact ht.elim
    · rfl) h

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- A bad call is a call of `Adds .stream`. -/
theorem worldBad_of_adds {β : Type} {oa : OracleComp (WorldSpec C) β}
    (h : IsQueryBoundP oa (FirstCounts.Adds .stream) 0) : IsQueryBoundP oa (WorldBad D (TableAllows F)) 0 :=
  IsQueryBoundP.of_imp (fun t ht => by
    rcases t with _ | (_ | _ | _)
    · exact ht.elim
    · exact ht.elim
    · exact ht.elim
    · rfl) h

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem rkeeps_pure {σ α : Type} (a : α) : RKeeps runLimit D F (pure a : RealM C σ α) := fun s hs =>
  ⟨by rw [StateT.run_pure]; exact isQueryBoundP_pure _ _ _, fun z hz => by
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hs⟩

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem rkeeps_bind {σ α β : Type} {x : RealM C σ α} {f : α → RealM C σ β} (hx : RKeeps runLimit D F x)
    (hf : ∀ a, RKeeps runLimit D F (f a)) : RKeeps runLimit D F (x >>= f) := fun s hs => by
  rw [StateT.run_bind]
  refine ⟨(isQueryBoundP_bind (n := 0) (m := 0) (hx s hs).1 fun y hy =>
    (hf y.1 y.2 ((hx s hs).2 y hy)).1).mono le_rfl, fun z hz => ?_⟩
  rw [mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  exact (hf y.1 y.2 ((hx s hs).2 y hy)).2 z hz

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem rkeeps_map {σ α β : Type} {x : RealM C σ α} (g : α → β) (hx : RKeeps runLimit D F x) :
    RKeeps runLimit D F (g <$> x) := by
  rw [map_eq_bind_pure_comp]
  exact rkeeps_bind hx fun _ => rkeeps_pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem rkeeps_get {σ : Type} : RKeeps runLimit D F (get : RealM C σ _) := fun s hs => by
  rw [StateT.run_get]
  refine ⟨isQueryBoundP_pure _ _ _, fun z hz => ?_⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact hs

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem rkeeps_get_bind {σ β : Type} {f : RealState C σ → RealM C σ β}
    (hf : ∀ s, RunsIn runLimit s → RKeeps runLimit D F (f s)) : RKeeps runLimit D F (get >>= f) := fun s hs => by
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  exact hf s hs s hs

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem rkeeps_lift {σ α : Type} {oa : OracleComp (WorldSpec C) α}
    (h : IsQueryBoundP oa (WorldBad D (TableAllows F)) 0) : RKeeps runLimit D F (StateT.lift oa : RealM C σ α) :=
  fun s hs => by
  rw [StateT.run_lift]
  refine ⟨(isQueryBoundP_bind (n := 0) (m := 0) h fun _ _ => isQueryBoundP_pure _ _ _).mono le_rfl, fun z hz => ?_⟩
  simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨_, _, rfl⟩ := hz
  exact hs

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem rkeeps_realLift {σ α : Type} {oa : OracleComp (RoSpec C) α} (h : GameCount.OnlySign oa) :
    RKeeps runLimit D F (realLift oa : RealM C σ α) :=
  rkeeps_lift (worldBad_of_adds (FirstCounts.free_noAdds (c := .stream) nofun h))

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem rkeeps_modify {σ : Type} (f : RealState C σ → RealState C σ) (hf : ∀ s, (f s).runs = s.runs) :
    RKeeps runLimit D F (modify f : RealM C σ Unit) := fun s hs => by
  rw [StateT.run_modify]
  refine ⟨isQueryBoundP_pure _ _ _, fun z hz => ?_⟩
  simp only [support_pure, Set.mem_singleton_iff] at hz
  subst hz
  intro tree
  rw [hf]
  exact hs tree

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem rkeeps_tlift {σ α : Type} {x : RealM C σ α} (hx : RKeeps runLimit D F x) (t : TsigState C) :
    RKeeps runLimit D F ((StateT.lift x : StateT (TsigState C) (RealM C σ) α).run t) := by
  rw [StateT.run_lift]
  exact rkeeps_bind hx fun _ => rkeeps_pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem rkeeps_simulateQ {σ ι : Type} {spec : OracleSpec ι} (impl : QueryImpl spec (StateT (TsigState C) (RealM C σ)))
    (h : ∀ q t, RKeeps runLimit D F ((impl q).run t)) {α : Type} (oa : OracleComp spec α) :
    ∀ t, RKeeps runLimit D F ((simulateQ impl oa).run t) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro t
    rw [simulateQ_pure, StateT.run_pure]
    exact rkeeps_pure _
  | query_bind q k ih =>
    intro t
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind]
    exact rkeeps_bind (h q t) fun y => ih y.1 y.2

omit [Fintype E] [DecidableEq E] in
/-- The allowed runs of `tree` make no bad call and keep the bound on the runs. -/
theorem drawTreeRuns_keeps (net : Adversary C E Unit PEmpty PEmpty) (tree : Tree) : ∀ count,
    RKeeps runLimit D F (UsedHit.drawTreeRuns K circuits settings runLimit (fun slot => pure (tableFresh F slot))
      (wrongOutput D) D net tree count)
  | 0 => rkeeps_pure _
  | count + 1 => by
    intro s hs
    simp only [UsedHit.drawTreeRuns, StateT.run_bind, StateT.run_get, pure_bind]
    split_ifs with hmay
    · have h1 := drawTreeRun_keeps K circuits settings runLimit D F net tree s hs (FirstCounts.mayRun_lt runLimit hmay)
      rw [StateT.run_bind]
      refine ⟨(isQueryBoundP_bind (n := 0) (m := 0) h1.1 fun y hy =>
        (drawTreeRuns_keeps net tree count y.2 (h1.2 y hy)).1).mono le_rfl, fun z hz => ?_⟩
      rw [mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      exact (drawTreeRuns_keeps net tree count y.2 (h1.2 y hy)).2 z hz
    · exact rkeeps_pure _ s hs

omit [Fintype E] [DecidableEq E] in
theorem drawTreeRequest_keeps (net : Adversary C E Unit PEmpty PEmpty) (b : Fin (2 ^ layerHeight)) :
    RKeeps runLimit D F (UsedHit.drawTreeRequest K circuits settings runLimit (fun slot => pure (tableFresh F slot))
      (wrongOutput D) D net b) := by
  unfold UsedHit.drawTreeRequest
  refine rkeeps_bind (drawTreeRuns_keeps K circuits settings net _ 1) fun _ => rkeeps_get_bind fun s _ => ?_
  split
  · exact rkeeps_bind (rkeeps_realLift (GameCount.onlySign_prfValue _ _)) fun _ => rkeeps_pure _
  · exact rkeeps_pure _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The answer of an honest operator makes no bad call. It is `tsigOracles` on the free copy. -/
theorem operatorAnswer_keeps {σ : Type} (operators : C.Party → OperatorState C) (operator : OperatorState C)
    (e : KeyIndex) (q : TsigQuery C) (t : TsigState C) :
    RKeeps runLimit D F ((operatorAnswer (m := RealM C σ) realLift (gameValue D operators) operator e q).run t) := by
  have hom := hom_operatorAnswer (realHom σ) (fun oa => free (liftComp oa (LocalSpec C)))
    (fun x => free (liftComp (prfValue (gameSeeds D fun i => (operators i).keys) x) (LocalSpec C))) operator e q t
  change RKeeps runLimit D F ((operatorAnswer (fun oa => realHom σ (free (liftComp oa (LocalSpec C))))
    (fun x => realHom σ (free (liftComp (prfValue (gameSeeds D fun i => (operators i).keys) x) (LocalSpec C))))
      operator e q).run t)
  rw [← hom]
  refine rkeeps_lift ?_
  unfold operatorAnswer
  split
  · rename_i keys top _ _ _ _
    rw [ownAnswer_run]
    exact worldBad_of_adds (DigestBudgets.signQuiet (c := .stream) nofun D operators keys top q _)
  · exact isQueryBoundP_pure _ _ _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem signRequest_keeps {σ : Type} (i : C.Party) (e : KeyIndex) (q : TsigQuery C) (t : TsigState C) :
    RKeeps runLimit D F ((signRequest D i e q : StateT (TsigState C) (RealM C σ) _).run t) := by
  unfold signRequest
  simp only [StateT.run_bind]
  exact rkeeps_bind (rkeeps_tlift (rkeeps_modify (fun s : RealState C σ =>
    { s with closed := Function.update s.closed (treeOf e) true }) fun _ => rfl) t) fun y =>
    rkeeps_bind (rkeeps_tlift rkeeps_get y.2) fun z => operatorAnswer_keeps _ _ _ _ _

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The win test on the free copy makes no call in class `stream`. -/
theorem noCall_forgeryWins (operators : C.Party → OperatorState C) (parameter : PublicParameter) (top : TopTree)
    (st : TsigState C) (forgery : Forgery) :
    NoCall (FirstCounts.Adds (C := C) .stream)
      (forgeryWins (fun oa => free (liftComp oa _)) (worldDealt D operators parameter top) st forgery) := by
  have hfree : ∀ {α : Type} {oa : OracleComp (RoSpec C) α}, GameCount.OnlySign oa →
      NoCall (FirstCounts.Adds (C := C) .stream) (free (liftComp oa (LocalSpec C))) := fun h =>
    (noCall_iff _ _).2 (FirstCounts.free_noAdds (c := .stream) nofun h)
  unfold forgeryWins
  refine noCall_bind _ (hfree (GameCount.onlySign_tweakable _)) fun _ => ?_
  dsimp only
  split_ifs
  · exact noCall_bind _ (noCall_pure _ _) fun _ => noCall_pure _ _
  · refine noCall_bind _ ?_ fun _ => noCall_bind _ (noCall_pure _ _) fun _ => noCall_pure _ _
    unfold honestSignature
    refine noCall_bind _ (noCall_pure _ _) fun o => ?_
    rcases o with _ | tree
    · exact noCall_pure _ _
    · refine noCall_bind _ (hfree (GameCount.onlySign_prfValue _ _)) fun ρ => noCall_bind _
        (hfree (by unfold signCodeword; exact GameCount.onlySign_tweakable _)) fun r => ?_
      rcases r with _ | ⟨randomness, encoding⟩
      · exact noCall_pure _ _
      · refine noCall_bind _ (noCall_sequenceFin _ _ fun l => ?_) fun _ =>
          noCall_bind _ (hfree (GameCount.onlySign_tweakable _)) fun _ => noCall_pure _ _
        split
        · exact hfree (GameCount.onlySign_prfValue _ _)
        · exact noCall_pure _ _
        · exact noCall_bind _ (hfree (GameCount.onlySign_prfValue _ _)) fun _ => noCall_pure _ _

omit [Fintype E] [DecidableEq E] in
/-- The signing phase makes no bad call and keeps the bound on the runs. -/
theorem drawSigning_keeps (A : DkgTsigAdversary C E) :
    RKeeps runLimit D F (UsedHit.drawSigning K circuits settings runLimit (fun slot => pure (tableFresh F slot))
      (wrongOutput D) D A) := by
  unfold UsedHit.drawSigning
  refine rkeeps_get_bind fun s _ => ?_
  split
  · refine rkeeps_bind (rkeeps_simulateQ _ (fun q t => ?_) _ _) fun p => ?_
    · rcases q with t' | q | q
      · exact rkeeps_tlift (rkeeps_lift (worldBad_of_honestIn (DigestBudgets.honestIn_adversary .stream _))) t
      · rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
        · exact rkeeps_pure _
        · exact rkeeps_tlift (drawTreeRequest_keeps K circuits settings A.net b) t
        · exact signRequest_keeps _ _ _ t
        · exact signRequest_keeps _ _ _ t
      · rcases q with _ | state
        · exact rkeeps_tlift (rkeeps_map _ rkeeps_get) t
        · exact rkeeps_tlift (rkeeps_modify (fun s : RealState C A.net.State => { s with adversary := state })
            fun _ => rfl) t
    · obtain ⟨forgery, st⟩ := p
      refine rkeeps_get_bind fun s' _ => ?_
      rw [forgeryWins_canonicalDealt]
      exact rkeeps_lift (worldBad_of_adds ((noCall_iff _ _).1 (noCall_forgeryWins _ _ _ _ _)))
  · exact rkeeps_pure _

omit [Fintype E] [DecidableEq E] in
/-- The game with the table `F` makes no bad call. -/
theorem tableGame_noBad (A : DkgTsigAdversary C E) :
    IsQueryBoundP (UsedHit.tableGame K circuits settings runLimit F D A) (WorldBad D (TableAllows F)) 0 := by
  unfold UsedHit.tableGame UsedHit.drawGame UsedHit.drawRun
  rw [isQueryBoundP_map_iff]
  refine (isQueryBoundP_bind (n := 0) (m := 0) (worldBad_of_honestIn ((GameCount.bound_iff _ _ _).1
    (DigestBudgets.seedHonest (C := C) (E := E) (c := .stream) nofun D A.net))) fun y _ => ?_).mono le_rfl
  obtain ⟨state, keys⟩ := y
  have hrun := (rkeeps_bind (drawTreeRuns_keeps K circuits settings (D := D) (F := F) A.net .top runLimit)
    fun _ => drawSigning_keeps K circuits settings A) (startState D state keys) fun _ => Nat.zero_le _
  exact (isQueryBoundP_bind (n := 0) (m := 0) hrun.1 fun _ _ => isQueryBoundP_pure _ _ _).mono le_rfl

end Walk

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

omit [Fintype E] [DecidableEq E] in
/-- Each key of the private table at the end of the game with the table `F` is an entry of `F` under
its name. -/
theorem keyProvenance : UsedHit.KeyProvenance K circuits settings runLimit prims := by
  intro D A F r hr n k hk
  refine simulateQ_keysIn prims D (TableAllows F) _ (tableGame_noBad K circuits settings A) keyJointInitial
    (fun n k h => ?_) r hr n k hk
  exact absurd rfl h
end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.keyProvenance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.keyProvenance
