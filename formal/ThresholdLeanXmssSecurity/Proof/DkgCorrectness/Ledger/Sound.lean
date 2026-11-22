import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.Ceremony.Statements
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.HonestBudgets
import ThresholdLeanXmssSecurity.Proof.DkgCorrectness.CutWalk

/-!
# The ledger of the coin keys and of the expansion keys of one ceremony

`ProgramFlow Q oa n last` states that the program `oa` of one operator makes at most `n` calls of `H` on a
coin key input, and that each of its calls of `H` on an expansion input has the key `last`, the
answer of its last coin call. `WorldFlow oa n keys` is the same for the honest calls of a computation of
the world, with a set `keys` of allowed expansion keys that each honest coin call extends by its
answer. `worldFlow_executePhase` lifts the flows of the honest programs to a phase, `WorldFlow.bind` joins
two computations, and `worldFlow_of_noHonestChallenge` covers a computation with no honest call in class
`challenge`. `simulateQ_soundCache` charges a computation of the world in `streamWorld`. Each counted
coin or expansion input goes to `seen`. Each honest coin input goes to `seen` and its answer to
`keys`, also on a cache hit. `phase_soundCache` is the ledger of one phase.

`flows_ceremonyRun` gives the coin calls of one honest operator in one ceremony of admissible jobs,
and `ledgerSound` proves `LedgerSound`.
-/

section
open ThresholdLeanXmss

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgCorrectnessProof

open FirstCounts DigestBudgets
open GameCount (CellIn)
open ThresholdLeanXmssSecurity.SigningSelectionProof (NoCall noCall_iff noCall_pure noCall_bind noCall_map noCall_mapM
  noCall_query)

attribute [local instance] Classical.propDecidable

/-! ## The coin calls and the expansion calls -/

section Calls

variable {C : Committee}

/-- A local call of `H` on a coin key input. -/
def IsCoin : (LocalSpec C).Domain → Prop
  | .inr (.inl (.coinKey ..)) => True
  | _ => False

/-- The key of a local call of `H` on an expansion input. -/
def expandKeyOf : (LocalSpec C).Domain → Option HashOutput
  | .inr (.inl (.expand key _)) => some key
  | _ => none

/-- The answer of a local call of `H` as a key. -/
def answerKey : (t : (LocalSpec C).Domain) → (LocalSpec C).Range t → HashOutput
  | .inr (.inl _), u => u
  | _, _ => 0

end Calls

/-! ## The flow of one program -/

section Program

variable {C : Committee} {E : Type}

/-- The condition of one call of a program at the budget `n` and the last coin answer `last`. -/
def ProgramStep : (PartySpec C E RealSpec).Domain → ℕ → Option HashOutput → Prop
  | .inl (.inl t), n, last => (IsCoin t → 0 < n) ∧ ∀ key, expandKeyOf t = some key → last = some key
  | _, _, _ => True

/-- The budget after one call of a program. -/
def programBudget : (PartySpec C E RealSpec).Domain → ℕ → ℕ
  | .inl (.inl t), n => if IsCoin t then n - 1 else n
  | _, n => n

/-- The last coin answer after one call of a program. -/
def programLast : (t : (PartySpec C E RealSpec).Domain) → (PartySpec C E RealSpec).Range t → Option HashOutput →
    Option HashOutput
  | .inl (.inl t), u, last => if IsCoin t then some (answerKey t u) else last
  | _, _, last => last

/-- The program `oa` makes at most `n` coin calls, each expansion call has the key of the last coin
answer, and each end with the last coin answer `last'` has `Q a last'`. -/
def ProgramFlow {β : Type} (Q : β → Option HashOutput → Prop) (oa : OracleComp (PartySpec C E RealSpec) β) :
    ℕ → Option HashOutput → Prop :=
  OracleComp.construct (C := fun _ => ℕ → Option HashOutput → Prop) (fun a _ last => Q a last)
    (fun t _ ih n last => ProgramStep t n last ∧ ∀ u, ih u (programBudget t n) (programLast t u last)) oa

theorem programFlow_pure {β : Type} (Q : β → Option HashOutput → Prop) (a : β) (n : ℕ) (last : Option HashOutput) :
    ProgramFlow Q (pure a : OracleComp (PartySpec C E RealSpec) β) n last ↔ Q a last := Iff.rfl

theorem programFlow_query_bind {β : Type} (Q : β → Option HashOutput → Prop) (t : (PartySpec C E RealSpec).Domain)
    (k : (PartySpec C E RealSpec).Range t → OracleComp (PartySpec C E RealSpec) β) (n : ℕ)
    (last : Option HashOutput) :
    ProgramFlow Q ((liftM (OracleSpec.query t) : OracleComp (PartySpec C E RealSpec) _) >>= k) n last ↔ ProgramStep t n last ∧ ∀ u, ProgramFlow Q (k u) (programBudget t n) (programLast t u last) :=
  Iff.rfl

theorem programBudget_le (t : (PartySpec C E RealSpec).Domain) (n : ℕ) : programBudget t n ≤ n := by
  rcases t with (t | _) | _
  · simp only [programBudget]
    split_ifs <;> omega
  · exact le_rfl
  · exact le_rfl

theorem ProgramFlow.mono {β : Type} {Q : β → Option HashOutput → Prop} {oa : OracleComp (PartySpec C E RealSpec) β} :
    ∀ {n m : ℕ} {last : Option HashOutput}, ProgramFlow Q oa n last → n ≤ m → ProgramFlow Q oa m last := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n m last h _; exact h
  | query_bind t k ih =>
    intro n m last h hnm
    rw [programFlow_query_bind] at h ⊢
    rcases t with (t | _) | _
    · refine ⟨⟨fun hc => (h.1.1 hc).trans_le hnm, h.1.2⟩, fun u => ih u (h.2 u) ?_⟩
      simp only [programBudget]
      split_ifs <;> omega
    · exact ⟨trivial, fun u => ih u (h.2 u) hnm⟩
    · exact ⟨trivial, fun u => ih u (h.2 u) hnm⟩

theorem ProgramFlow.post {β : Type} {Q R : β → Option HashOutput → Prop} {oa : OracleComp (PartySpec C E RealSpec) β}
    (hQR : ∀ a last, Q a last → R a last) :
    ∀ {n : ℕ} {last : Option HashOutput}, ProgramFlow Q oa n last → ProgramFlow R oa n last := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n last h; exact hQR a last h
  | query_bind t k ih =>
    intro n last h
    rw [programFlow_query_bind] at h ⊢
    exact ⟨h.1, fun u => ih u (h.2 u)⟩

/-- The bind rule. The second program runs from each end of the first, at its last coin answer. -/
theorem ProgramFlow.bind {β γ : Type} {Q : β → Option HashOutput → Prop} {R : γ → Option HashOutput → Prop}
    {p : OracleComp (PartySpec C E RealSpec) β} {f : β → OracleComp (PartySpec C E RealSpec) γ} {m : ℕ} :
    ∀ {n : ℕ} {last : Option HashOutput}, ProgramFlow Q p n last →
      (∀ a last', a ∈ support p → Q a last' → ProgramFlow R (f a) m last') → ProgramFlow R (p >>= f) (n + m) last := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    intro n last hp hf
    rw [pure_bind]
    exact (hf a last (by simp) hp).mono (Nat.le_add_left _ _)
  | query_bind t k ih =>
    intro n last hp hf
    rw [bind_assoc, programFlow_query_bind]
    rw [programFlow_query_bind] at hp
    refine ⟨?_, fun u => ?_⟩
    · rcases t with (t | _) | _
      · exact ⟨fun hc => (hp.1.1 hc).trans_le (Nat.le_add_right _ _), hp.1.2⟩
      · trivial
      · trivial
    · have h := ih u (hp.2 u) fun a last' ha hq => hf a last' (by
        rw [mem_support_bind_iff]
        exact ⟨u, by simp, ha⟩) hq
      refine h.mono ?_
      rcases t with (t | _) | _
      · simp only [programBudget]
        have := hp.1.1
        split_ifs with hc
        · have := this hc
          omega
        · exact le_rfl
      · exact le_rfl
      · exact le_rfl

/-- A program with no call in class `challenge` makes no coin call and no expansion call. -/
theorem programFlow_of_noChallenge {β : Type} (oa : OracleComp (PartySpec C E RealSpec) β)
    (h : IsQueryBoundP oa (PartyIn (C := C) (E := E) .challenge) 0) :
    ∀ n last, ProgramFlow (fun _ last' => last' = last) oa n last := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro n last; exact rfl
  | query_bind t k ih =>
    intro n last
    rw [isQueryBoundP_query_bind_iff] at h
    rw [programFlow_query_bind]
    have ht : ¬ PartyIn (C := C) (E := E) .challenge t := by
      rcases h.1 with h1 | h1
      · exact h1
      · omega
    rcases t with (t | _) | _
    · have hcoin : ¬ IsCoin t := by
        rcases t with _ | q | _
        · exact id
        · cases q <;> simp_all [IsCoin, PartyIn, InClass, queryClass]
        · exact id
      have hexp : expandKeyOf t = none := by
        rcases t with _ | q | _
        · rfl
        · cases q <;> simp_all [expandKeyOf, PartyIn, InClass, queryClass]
        · rfl
      refine ⟨⟨fun hc => absurd hc hcoin, fun key hk => by rw [hexp] at hk; cases hk⟩, fun u => ?_⟩
      have hk := h.2 u
      simp only [ht, ↓reduceIte] at hk
      simpa [programBudget, programLast, hcoin] using ih u hk n last
    · refine ⟨trivial, fun u => ?_⟩
      have hk := h.2 u
      simp only [ht, ↓reduceIte] at hk
      exact ih u hk n last
    · refine ⟨trivial, fun u => ?_⟩
      have hk := h.2 u
      simp only [ht, ↓reduceIte] at hk
      exact ih u hk n last

end Program

/-! ## The flow of the honest calls of the world -/

section World

variable {C : Committee}

/-- The condition of one call of the world at the budget `n` and the allowed keys `keys`. -/
def WorldStep : (WorldSpec C).Domain → ℕ → Finset HashOutput → Prop
  | .inr t, n, keys => (IsCoin t → 0 < n) ∧ ∀ key, expandKeyOf t = some key → key ∈ keys
  | _, _, _ => True

/-- The budget after one call of the world. -/
def worldBudget : (WorldSpec C).Domain → ℕ → ℕ
  | .inr t, n => if IsCoin t then n - 1 else n
  | _, n => n

/-- The allowed keys after one call of the world. -/
def worldKeys : (t : (WorldSpec C).Domain) → (WorldSpec C).Range t → Finset HashOutput → Finset HashOutput
  | .inr t, u, keys => if IsCoin t then insert (answerKey t u) keys else keys
  | _, _, keys => keys

/-- The honest calls of `oa` make at most `n` coin calls, and each honest expansion call has an
allowed key. Each honest coin call allows its answer. -/
def WorldFlow {β : Type} (oa : OracleComp (WorldSpec C) β) : ℕ → Finset HashOutput → Prop :=
  OracleComp.construct (C := fun _ => ℕ → Finset HashOutput → Prop) (fun _ _ _ => True)
    (fun t _ ih n keys => WorldStep t n keys ∧ ∀ u, ih u (worldBudget t n) (worldKeys t u keys)) oa

theorem worldFlow_query_bind {β : Type} (t : (WorldSpec C).Domain) (k : (WorldSpec C).Range t → OracleComp (WorldSpec C) β)
    (n : ℕ) (keys : Finset HashOutput) :
    WorldFlow ((liftM (OracleSpec.query t) : OracleComp (WorldSpec C) _) >>= k) n keys ↔ WorldStep t n keys ∧ ∀ u, WorldFlow (k u) (worldBudget t n) (worldKeys t u keys) :=
  Iff.rfl

theorem worldKeys_mono (t : (WorldSpec C).Domain) (u : (WorldSpec C).Range t) {keys keys' : Finset HashOutput}
    (h : keys ⊆ keys') : worldKeys t u keys ⊆ worldKeys t u keys' := by
  rcases t with _ | t
  · exact h
  · simp only [worldKeys]
    split_ifs
    · exact Finset.insert_subset_insert _ h
    · exact h

theorem WorldFlow.mono {β : Type} {oa : OracleComp (WorldSpec C) β} :
    ∀ {n m : ℕ} {keys keys' : Finset HashOutput}, WorldFlow oa n keys → n ≤ m → keys ⊆ keys' → WorldFlow oa m keys' := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro _ _ _ _ _ _ _; trivial
  | query_bind t k ih =>
    intro n m keys keys' h hnm hk
    rw [worldFlow_query_bind] at h ⊢
    rcases t with _ | t
    · exact ⟨trivial, fun u => ih u (h.2 u) hnm (worldKeys_mono _ u hk)⟩
    · refine ⟨⟨fun hc => (h.1.1 hc).trans_le hnm, fun key hkey => hk (h.1.2 key hkey)⟩,
        fun u => ih u (h.2 u) ?_ (worldKeys_mono _ u hk)⟩
      simp only [worldBudget]
      split_ifs <;> omega

theorem subset_worldKeys (t : (WorldSpec C).Domain) (u : (WorldSpec C).Range t) (keys : Finset HashOutput) :
    keys ⊆ worldKeys t u keys := by
  rcases t with _ | t
  · exact subset_rfl
  · simp only [worldKeys]
    split_ifs
    · exact Finset.subset_insert _ _
    · exact subset_rfl

/-- The bind rule. The second computation runs from each end of the first, with the allowed keys of
that end. -/
theorem WorldFlow.bind {β γ : Type} {p : OracleComp (WorldSpec C) β} {f : β → OracleComp (WorldSpec C) γ} {m : ℕ} :
    ∀ {n : ℕ} {keys : Finset HashOutput}, WorldFlow p n keys →
      (∀ a keys', keys ⊆ keys' → WorldFlow (f a) m keys') → WorldFlow (p >>= f) (n + m) keys := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    intro n keys _ hf
    rw [pure_bind]
    exact (hf a keys subset_rfl).mono (Nat.le_add_left _ _) subset_rfl
  | query_bind t k ih =>
    intro n keys hp hf
    rw [bind_assoc, worldFlow_query_bind]
    rw [worldFlow_query_bind] at hp
    refine ⟨?_, fun u => ?_⟩
    · rcases t with _ | t
      · trivial
      · exact ⟨fun hc => (hp.1.1 hc).trans_le (Nat.le_add_right _ _), hp.1.2⟩
    · refine (ih u (hp.2 u) fun a keys' hsub => hf a keys' ((subset_worldKeys t u keys).trans hsub)).mono ?_ subset_rfl
      rcases t with _ | t
      · exact le_rfl
      · simp only [worldBudget]
        have := hp.1.1
        split_ifs with hc
        · have := this hc
          omega
        · exact le_rfl

/-- A computation with no honest call in class `challenge` makes no honest coin call and no honest
expansion call. The monitor, the signing answers and the counted calls of the adversary are such
computations. -/
theorem worldFlow_of_noHonestChallenge {β : Type} (oa : OracleComp (WorldSpec C) β)
    (h : IsQueryBoundP oa (HonestIn (C := C) .challenge) 0) : ∀ n keys, WorldFlow oa n keys := by
  induction oa using OracleComp.inductionOn with
  | pure a => intro _ _; trivial
  | query_bind t k ih =>
    intro n keys
    rw [isQueryBoundP_query_bind_iff] at h
    rw [worldFlow_query_bind]
    have ht : ¬ HonestIn (C := C) .challenge t := by
      rcases h.1 with h1 | h1
      · exact h1
      · omega
    have hk : ∀ u, IsQueryBoundP (k u) (HonestIn (C := C) .challenge) 0 := fun u => by
      simpa only [ht, ↓reduceIte] using h.2 u
    rcases t with _ | t
    · exact ⟨trivial, fun u => ih u (hk u) n keys⟩
    · have hcoin : ¬ IsCoin t := by
        rcases t with _ | q | _
        · exact id
        · cases q <;> simp_all [IsCoin, HonestIn, InClass, queryClass]
        · exact id
      have hexp : expandKeyOf t = none := by
        rcases t with _ | q | _
        · rfl
        · cases q <;> simp_all [expandKeyOf, HonestIn, InClass, queryClass]
        · rfl
      refine ⟨⟨fun hc => absurd hc hcoin, fun key hkey => by rw [hexp] at hkey; cases hkey⟩, fun u => ?_⟩
      simpa only [worldBudget, worldKeys, hcoin, ↓reduceIte] using ih u (hk u) n keys

end World

/-! ## The flow of the honest calls on the network -/

section Network

variable {C : Committee} {E : Type}

/-- The keys of a last coin answer are allowed. -/
def LastIn (last : Option HashOutput) (keys : Finset HashOutput) : Prop := ∀ key, last = some key → key ∈ keys

theorem lastIn_none (keys : Finset HashOutput) : LastIn none keys := fun _ h => nomatch h

theorem LastIn.mono {last : Option HashOutput} {keys keys' : Finset HashOutput} (h : LastIn last keys)
    (hk : keys ⊆ keys') : LastIn last keys' := fun key hkey => hk (h key hkey)

/-- A program of one operator makes at most `n` coin calls from each last coin answer. -/
def Flows {α : Type} (p : PartyM C E RealSpec α) (n : ℕ) : Prop := ∀ last, ProgramFlow (fun _ _ => True) p.run n last

/-- The flow of the continuation of a stopped program, from an allowed last coin answer. -/
def StepFlow {α : Type} (st : Step C E RealSpec α) (n : ℕ) (keys : Finset HashOutput) : Prop :=
  match st with
  | .done _ => True
  | .wait _ k => ∃ last, LastIn last keys ∧ ∀ inbox, ProgramFlow (fun _ _ => True) (k inbox) n last
  | .call _ k => ∃ last, LastIn last keys ∧ ∀ out, ProgramFlow (fun _ _ => True) (k out) n last

theorem StepFlow.mono {α : Type} {st : Step C E RealSpec α} {n : ℕ} {keys keys' : Finset HashOutput}
    (h : StepFlow st n keys) (hk : keys ⊆ keys') : StepFlow st n keys' := by
  rcases st with _ | ⟨_, k⟩ | ⟨_, k⟩
  · trivial
  · obtain ⟨last, hl, hf⟩ := h
    exact ⟨last, hl.mono hk, hf⟩
  · obtain ⟨last, hl, hf⟩ := h
    exact ⟨last, hl.mono hk, hf⟩

/-- The adversary role makes no honest call. -/
theorem worldFlow_adversary_bind {β γ : Type} (oa : OracleComp (LocalSpec C) β) :
    ∀ (k : β → OracleComp (WorldSpec C) γ) (n : ℕ) (keys : Finset HashOutput), (∀ b, WorldFlow (k b) n keys) →
      WorldFlow (worldRoles.adversary oa >>= k) n keys := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro k n keys hk
    have e : worldRoles.adversary (pure a : OracleComp (LocalSpec C) β) = pure a := by
      simp only [worldRoles, counted, liftComp_pure, simulateQ_pure]
    rw [e, pure_bind]
    exact hk a
  | query_bind t f ih =>
    intro k n keys hk
    have e : worldRoles.adversary (liftM (OracleSpec.query t) >>= f) =
        worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun u => worldRoles.adversary (f u) := by
      simp only [worldRoles, counted, liftComp_bind]
      exact simulateQ_bind _ _ _
    rw [e, ThresholdLeanXmssSecurity.adversary_query, bind_assoc, worldFlow_query_bind]
    exact ⟨trivial, fun u => ih u k n keys hk⟩

/-- Advancing an honest operator on the free copy spends its budget of coin calls, allows the answers
of its coin calls, and leaves the rest for its continuation. -/
theorem worldFlow_free_advance_bind {α β : Type} (oa : OracleComp (PartySpec C E RealSpec) (Option α))
    (k : Step C E RealSpec α → OracleComp (WorldSpec C) β) (extra : ℕ) :
    ∀ n last (keys : Finset HashOutput), LastIn last keys → ProgramFlow (fun _ _ => True) oa n last →
      (∀ st b keys', keys ⊆ keys' → b ≤ n → StepFlow st b keys' → WorldFlow (k st) (extra + b) keys') →
      WorldFlow (free (advance oa) >>= k) (extra + n) keys := by
  induction oa using OracleComp.inductionOn with
  | pure out =>
    intro n last keys _ _ hk
    rw [advance_pure, free_pure, pure_bind]
    exact hk _ n keys subset_rfl le_rfl trivial
  | query_bind t f ih =>
    intro n last keys hlast hp hk
    rw [programFlow_query_bind] at hp
    rcases t with (q | outbox) | input
    · have e : free (advance (liftM (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) >>= f)) =
          (liftM ((WorldSpec C).query (.inr q)) : OracleComp (WorldSpec C) _) >>= fun u => free (advance (f u)) := by
        change free (advance (OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec)
          (Sum.inl (Sum.inl q))) >>= f)) = _
        rw [advance_query_bind, free_bind]
        rfl
      rw [e, bind_assoc, worldFlow_query_bind]
      refine ⟨⟨fun hc => (hp.1.1 hc).trans_le (Nat.le_add_left _ _), fun key hkey => hlast key (hp.1.2 key hkey)⟩,
        fun u => ?_⟩
      have hu := hp.2 u
      by_cases hc : IsCoin q
      · have hn := hp.1.1 hc
        simp only [programBudget, programLast, hc, ↓reduceIte] at hu
        simp only [worldBudget, worldKeys, hc, ↓reduceIte]
        have he : extra + n - 1 = extra + (n - 1) := by omega
        rw [he]
        exact ih u (n - 1) _ (insert (answerKey q u) keys)
          (fun key hkey => by simp only [Option.some.injEq] at hkey; exact hkey ▸ Finset.mem_insert_self _ _) hu
          fun st b keys' hsub hb hs => hk st b keys' ((Finset.subset_insert _ _).trans hsub) (by omega) hs
      · simp only [programBudget, programLast, hc, ↓reduceIte] at hu
        simp only [worldBudget, worldKeys, hc, ↓reduceIte]
        exact ih u n last keys hlast hu hk
    · change WorldFlow (free (pure (Step.wait outbox f)) >>= k) (extra + n) keys
      rw [free_pure, pure_bind]
      exact hk _ n keys subset_rfl le_rfl ⟨last, hlast, fun inbox => hp.2 inbox⟩
    · exact input.elim

/-- Advancing the honest operators one after another spends the budget of each. -/
theorem worldFlow_sequenceFin_free_advance_bind {α β : Type} : ∀ {N : ℕ}
    (oa : Fin N → OracleComp (PartySpec C E RealSpec) (Option α)) (budget : Fin N → ℕ) (keys : Finset HashOutput)
    (_ : ∀ i, ∃ last, LastIn last keys ∧ ProgramFlow (fun _ _ => True) (oa i) (budget i) last)
    (k : (Fin N → Step C E RealSpec α) → OracleComp (WorldSpec C) β) (extra : ℕ),
    (∀ st (b : Fin N → ℕ) keys', keys ⊆ keys' → (∀ i, b i ≤ budget i) → (∀ i, StepFlow (st i) (b i) keys') →
      WorldFlow (k st) (extra + ∑ i, b i) keys') →
    WorldFlow ((OverPermutation.sequenceFin fun i => free (advance (oa i))) >>= k) (extra + ∑ i, budget i) keys
  | 0, _, _, keys, _, k, extra, hk => by
    simp only [OverPermutation.sequenceFin, pure_bind, Fin.sum_univ_zero, Nat.add_zero]
    simpa using hk Fin.elim0 Fin.elim0 keys subset_rfl (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  | N + 1, oa, budget, keys, h, k, extra, hk => by
    simp only [OverPermutation.sequenceFin, bind_assoc, pure_bind]
    rw [Fin.sum_univ_succ]
    have he : extra + (budget 0 + ∑ i : Fin N, budget i.succ) =
        (extra + ∑ i : Fin N, budget i.succ) + budget 0 := by omega
    rw [he]
    obtain ⟨last0, hl0, hp0⟩ := h 0
    refine worldFlow_free_advance_bind (oa 0) _ _ (budget 0) last0 keys hl0 hp0 (fun st0 b0 keys0 hsub0 hb0 hs0 => ?_)
    have he' : (extra + ∑ i : Fin N, budget i.succ) + b0 = (extra + b0) + ∑ i : Fin N, budget i.succ := by omega
    rw [he']
    refine worldFlow_sequenceFin_free_advance_bind (fun i : Fin N => oa i.succ) (fun i => budget i.succ) keys0
      (fun i => by
        obtain ⟨last, hl, hp⟩ := h i.succ
        exact ⟨last, hl.mono hsub0, hp⟩)
      (fun st => k (Fin.cases st0 st)) (extra + b0) (fun st b keys' hsub hb hs => ?_)
    have hp := hk (Fin.cases st0 st) (Fin.cases b0 b) keys' (hsub0.trans hsub)
      (fun i => Fin.cases hb0 hb i) (fun i => Fin.cases (hs0.mono hsub) hs i)
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hp

variable {Ia : Type} (D : C.Coalition) (A : Adversary C E Ia PEmpty PEmpty)

theorem roundResume_flow {α : Type} (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E RealSpec α) (j : C.Party) (b : ℕ) (keys : Finset HashOutput)
    (h : StepFlow (steps j) b keys) :
    ∃ last, LastIn last keys ∧ ProgramFlow (fun _ _ => True) (roundResume D sent steps j) b last := by
  unfold roundResume
  rcases hs : steps j with out | ⟨outbox, k⟩ | ⟨input, k⟩
  · exact ⟨none, lastIn_none keys, trivial⟩
  · rw [hs] at h
    obtain ⟨last, hl, hk⟩ := h
    dsimp only
    split_ifs
    · exact ⟨none, lastIn_none keys, trivial⟩
    · exact ⟨last, hl, hk _⟩
  · exact ⟨none, lastIn_none keys, trivial⟩

/-- One round on the real network spends the budgets of the honest operators. -/
theorem worldFlow_stepRound_bind {α β : Type} (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (budget : C.Party → ℕ) (keys : Finset HashOutput) (h : ∀ j, StepFlow (steps j) (budget j) keys)
    (k : (A.State × (C.Party → Step C E RealSpec α) × (C.Party → C.Party → Option (Msg E))) →
      OracleComp (WorldSpec C) β) (extra : ℕ)
    (hk : ∀ st (b : C.Party → ℕ) keys', keys ⊆ keys' → (∀ j, b j ≤ budget j) → (∀ j, StepFlow (st.2.1 j) (b j) keys') →
      WorldFlow (k st) (extra + ∑ j, b j) keys') :
    WorldFlow (stepRound worldRoles D A noFunctionality state steps >>= k) (extra + ∑ j, budget j) keys := by
  unfold stepRound
  split_ifs with hcall
  · exact absurd hcall (by simp [ThresholdLeanXmssSecurity.callInput_real])
  simp only [bind_assoc, pure_bind]
  refine worldFlow_adversary_bind _ _ _ _ fun result => ?_
  have he : (fun j => match steps j with
      | .done out => pure (Step.done out)
      | .wait _ resume => if j ∈ D.1 then pure (Step.done none) else
          worldRoles.honest (advance (resume fun k => if k ∈ D.1 then result.2 k j else (steps k).delivered j))
      | .call _ _ => pure (Step.done none)) = fun j => free (advance (roundResume D result.2 steps j)) := by
    funext j
    cases hs : steps j with
    | done out => simp only [roundResume, hs, advance_pure, free_pure]
    | call input k => simp only [roundResume, hs, advance_pure, free_pure]
    | wait out k =>
      simp only [roundResume, hs]
      split_ifs
      · simp only [advance_pure, free_pure]
      · rfl
  have hseq := worldFlow_sequenceFin_free_advance_bind
    (fun j => roundResume D result.2 steps j) budget keys
    (fun j => roundResume_flow D result.2 steps j (budget j) keys (h j))
    (fun st => k (result.1, st, result.2)) extra
    (fun st b keys' hsub hb hs => hk (result.1, st, result.2) b keys' hsub hb hs)
  convert (congrArg (fun f : C.Party → OracleComp (WorldSpec C) (Step C E RealSpec α) =>
    WorldFlow (OverPermutation.sequenceFin f >>= fun st => k (result.1, st, result.2))
      (extra + ∑ j, budget j) keys) he).mpr hseq using 1
  congr 2
  funext j
  cases steps j <;> rfl

/-- The rounds on the real network spend the budgets of the honest operators. -/
theorem worldFlow_executeRounds {α : Type} :
    ∀ fuel state (steps : C.Party → Step C E RealSpec α) (budget : C.Party → ℕ) (keys : Finset HashOutput),
      (∀ j, StepFlow (steps j) (budget j) keys) →
      WorldFlow (executeRounds worldRoles D A noFunctionality fuel state steps) (∑ j, budget j) keys
  | 0, state, steps, budget, keys, h => trivial
  | fuel + 1, state, steps, budget, keys, h => by
    unfold executeRounds
    split_ifs
    · trivial
    · have h' := worldFlow_stepRound_bind D A state steps budget keys h _ 0
        (fun st b keys' _ _ hs => (worldFlow_executeRounds fuel st.1 st.2.1 b keys' hs).mono (Nat.le_add_left _ _)
          subset_rfl)
      exact h'.mono (Nat.zero_add _).le subset_rfl

/-- A phase on the real network makes at most the sum of the budgets of the honest programs of honest
coin calls, and each honest expansion call has an allowed key. -/
theorem worldFlow_executePhase {α : Type} (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E RealSpec α)
    (budget : C.Party → ℕ) (hp : ∀ j, j ∉ D.1 → Flows (program j) (budget j)) (keys : Finset HashOutput) :
    WorldFlow (executePhase worldRoles D A noFunctionality fuel state program) (∑ j, budget j) keys := by
  unfold executePhase startSteps
  have he : (fun i => if i ∈ D.1 then pure (Step.done none) else worldRoles.honest (advance (program i).run)) =
      fun i => free (advance (if i ∈ D.1 then pure none else (program i).run)) := by
    funext i
    split_ifs
    · simp only [advance_pure, free_pure]
    · rfl
  change WorldFlow ((OverPermutation.sequenceFin _) >>= _) _ _
  rw [he]
  refine (worldFlow_sequenceFin_free_advance_bind _ budget keys (fun j => ?_) _ 0
    (fun st b keys' _ _ hs => (worldFlow_executeRounds D A fuel state st b keys' hs).mono (Nat.le_add_left _ _)
      subset_rfl)).mono (Nat.zero_add _).le subset_rfl
  refine ⟨none, lastIn_none keys, ?_⟩
  split_ifs with hj
  · trivial
  · exact hp j hj none

end Network

/-! ## The charge of the coin keys and of the expansions in `streamWorld` -/

section Simulation

variable {C : Committee} (prims : Primitives)

/-- A free call of `H` adds at most the cell of its input. -/
theorem streamWorld_hash_cells (D : C.Coalition) (q : Query C) (w : StreamState C)
    (y : HashOutput × StreamState C) (hy : y ∈ support ((streamWorld prims D (.inr (.inr (.inl q)))).run w)) :
    ∀ x, y.2.1 x ≠ none → w.1 x ≠ none ∨ x = q := by
  obtain ⟨r, hr, rfl⟩ := mem_support_onHash _ w y hy
  exact hashAnswer_cells prims q w.1 r hr

/-- A cache with no new cell of class `challenge` keeps `SoundCache`. -/
theorem soundCache_of_old {cache cache' : HashCache C} {seen : Finset (Query C)} {keys : Finset HashOutput}
    (hs : SoundCache 0 cache seen keys) (hold : ∀ x, CellIn .challenge x → cache' x ≠ none → cache x ≠ none) :
    SoundCache 0 cache' seen keys :=
  ⟨fun tag label bits hL h => hs.1 tag label bits hL (hold _ rfl h), fun key idx h => hs.2 key idx (hold _ rfl h)⟩

/-- A call of the world in `streamWorld` with one new cell `key` of class `challenge` at most keeps
`SoundCache` with `key` charged. -/
theorem soundCache_insert {cache cache' : HashCache C} {seen : Finset (Query C)} {keys : Finset HashOutput}
    (hs : SoundCache 0 cache seen keys) (key : Query C)
    (hnew : ∀ x, CellIn .challenge x → cache' x ≠ none → cache x ≠ none ∨ x = key) :
    SoundCache 0 cache' (insert key seen) keys := by
  refine ⟨fun tag label bits hL h => ?_, fun k idx h => ?_⟩
  · rcases hnew (.coinKey tag label bits) rfl h with h | h
    · exact Finset.mem_insert_of_mem (hs.1 tag label bits hL h)
    · exact h ▸ Finset.mem_insert_self _ _
  · rcases hnew (.expand k idx) rfl h with h | h
    · exact (hs.2 k idx h).imp_right Finset.mem_insert_of_mem
    · exact Or.inr (h ▸ Finset.mem_insert_self _ _)

/-- The charge of a computation of the world. From a cache with `SoundCache 0 seen keys`, a computation
with at most `a` counted coin or expansion calls, at most `n` honest coin calls and honest expansion
calls on allowed keys ends with `SoundCache 0 seen' keys'`, with at most `a + n` more charged inputs
and `n` more expansion keys. -/
theorem simulateQ_soundCache (D : C.Coalition) {β : Type} (oa : OracleComp (WorldSpec C) β) :
    ∀ (a n : ℕ) (allowed : Finset HashOutput) (w : StreamState C) (seen : Finset (Query C))
      (keys : Finset HashOutput), IsQueryBoundP oa (OwnAdds .challenge) a → WorldFlow oa n allowed →
      allowed ⊆ keys → SoundCache 0 w.1 seen keys →
      ∀ z ∈ support ((simulateQ (streamWorld prims D) oa).run w),
        ∃ (seen' : Finset (Query C)) (keys' : Finset HashOutput), SoundCache 0 z.2.1 seen' keys' ∧
          seen'.card ≤ seen.card + a + n ∧ keys'.card ≤ keys.card + n := by
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro a n allowed w seen keys _ _ _ hs z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨seen, keys, hs, by omega, by omega⟩
  | query_bind t k ih =>
    intro a n allowed w seen keys ha hf hsub hs z hz
    rw [isQueryBoundP_query_bind_iff] at ha
    rw [worldFlow_query_bind] at hf
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query, id_map,
      StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    obtain ⟨cell, hcell⟩ := streamWorld_cells prims .challenge D t w y hy
    rcases t with t | lt
    · by_cases hown : OwnAdds (C := C) .challenge (.inl t)
      · have hpos := ha.1.resolve_left (not_not.2 hown)
        have hk := ha.2 y.1
        simp only [hown, ↓reduceIte] at hk
        have hs₁ := soundCache_insert hs cell fun x hx h => (hcell x hx h).imp_right And.right
        obtain ⟨seen', keys', h', hc', hk'⟩ := ih y.1 (a - 1) n allowed y.2 _ keys hk (hf.2 y.1) hsub hs₁ z hz
        exact ⟨seen', keys', h', hc'.trans (by have := Finset.card_insert_le cell seen; omega), hk'⟩
      · have hk := ha.2 y.1
        simp only [hown, ↓reduceIte] at hk
        have hs₁ : SoundCache 0 y.2.1 seen keys := soundCache_of_old hs fun x hx h =>
          (hcell x hx h).resolve_right fun h' => hown (by rcases t with t | t <;> exact h'.1)
        exact ih y.1 a n allowed y.2 seen keys hk (hf.2 y.1) hsub hs₁ z hz
    · have hk := ha.2 y.1
      have hnot : ¬ OwnAdds (C := C) .challenge (.inr lt) := id
      simp only [hnot, ↓reduceIte] at hk
      have hfk := hf.2 y.1
      rcases lt with r | q | x
      · have hcoin : ¬ IsCoin (C := C) (.inl r) := id
        simp only [worldBudget, worldKeys, hcoin, ↓reduceIte] at hfk
        have hs₁ : SoundCache 0 y.2.1 seen keys := soundCache_of_old hs fun x hx h =>
          (hcell x hx h).resolve_right fun h' => h'.1
        exact ih y.1 a n allowed y.2 seen keys hk hfk hsub hs₁ z hz
      · have hq := streamWorld_hash_cells prims D q w y hy
        by_cases hc : ∃ tag label bits, q = .coinKey tag label bits
        · obtain ⟨tag, label, bits, rfl⟩ := hc
          have hcoin : IsCoin (C := C) (.inr (.inl (.coinKey tag label bits))) := trivial
          have hpos := hf.1.1 hcoin
          simp only [worldBudget, worldKeys, hcoin, ↓reduceIte, answerKey] at hfk
          have hs₁ : SoundCache 0 y.2.1 (insert (.coinKey tag label bits) seen) (insert y.1 keys) := by
            have h₀ := soundCache_insert hs (.coinKey tag label bits) fun x _ h => hq x h
            exact ⟨h₀.1, fun key idx h => (h₀.2 key idx h).imp_left (Finset.mem_insert_of_mem)⟩
          obtain ⟨seen', keys', h', hc', hk'⟩ := ih y.1 a (n - 1) _ y.2 _ _ hk hfk
            (Finset.insert_subset_insert _ hsub) hs₁ z hz
          refine ⟨seen', keys', h', hc'.trans ?_, hk'.trans ?_⟩
          · have := Finset.card_insert_le (Query.coinKey tag label bits) seen
            omega
          · have := Finset.card_insert_le y.1 keys
            omega
        · by_cases he : ∃ key idx, q = .expand key idx
          · obtain ⟨key, idx, rfl⟩ := he
            have hkey : key ∈ keys := hsub (hf.1.2 key rfl)
            have hcoin : ¬ IsCoin (C := C) (.inr (.inl (.expand key idx))) := id
            simp only [worldBudget, worldKeys, hcoin, ↓reduceIte] at hfk
            have hs₁ : SoundCache 0 y.2.1 seen keys := by
              refine ⟨fun tag label bits hL h => ?_, fun k' idx' h => ?_⟩
              · rcases hq _ h with h | h
                · exact hs.1 tag label bits hL h
                · cases h
              · rcases hq _ h with h | h
                · exact hs.2 k' idx' h
                · simp only [Query.expand.injEq] at h
                  exact Or.inl (h.1 ▸ hkey)
            exact ih y.1 a n allowed y.2 seen keys hk hfk hsub hs₁ z hz
          · have hcoin : ¬ IsCoin (C := C) (.inr (.inl q)) := by
              intro h
              cases q <;> simp_all [IsCoin]
            simp only [worldBudget, worldKeys, hcoin, ↓reduceIte] at hfk
            have hs₁ : SoundCache 0 y.2.1 seen keys := by
              refine ⟨fun tag label bits hL h => ?_, fun k' idx' h => ?_⟩
              · rcases hq _ h with h | h
                · exact hs.1 tag label bits hL h
                · exact absurd ⟨tag, label, bits, h.symm⟩ hc
              · rcases hq _ h with h | h
                · exact hs.2 k' idx' h
                · exact absurd ⟨k', idx', h.symm⟩ he
            exact ih y.1 a n allowed y.2 seen keys hk hfk hsub hs₁ z hz
      · have hcoin : ¬ IsCoin (C := C) (.inr (.inr x)) := id
        simp only [worldBudget, worldKeys, hcoin, ↓reduceIte] at hfk
        have hs₁ : SoundCache 0 y.2.1 seen keys := soundCache_of_old hs fun x' hx h =>
          (hcell x' hx h).resolve_right fun h' => by
            have h₁ := h'.1
            simp [Adds, InClass] at h₁
        exact ih y.1 a n allowed y.2 seen keys hk hfk hsub hs₁ z hz

end Simulation

/-! ## The flows of the blocks of a check -/

section Blocks

variable {C : Committee} {E : Type}

theorem oracleStep_run_pure {α : Type} (a : α) :
    (oracleStep (pure a) : PartyM C E RealSpec α).run = pure (some a) := by
  simp [oracleStep, localStep]

theorem oracleStep_run_query_bind {α : Type} (t : (RoSpec C).Domain)
    (k : (RoSpec C).Range t → OracleComp (RoSpec C) α) :
    (oracleStep (liftM (OracleSpec.query t) >>= k) : PartyM C E RealSpec α).run =
      (liftM (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl (.inr t)))) :
        OracleComp (PartySpec C E RealSpec) _) >>= fun u => (oracleStep (k u) : PartyM C E RealSpec α).run := by
  simp only [oracleStep, localStep, OptionT.run_lift, liftComp_bind, bind_assoc]
  rcases t with _ | _ <;> rfl

theorem oracleStep_hashQuery_bind_run {β : Type} (q : Query C) (f : HashOutput → PartyM C E RealSpec β) :
    (oracleStep (hashQuery q) >>= f : PartyM C E RealSpec β).run =
      (liftM (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl (.inr (.inl q))))) :
        OracleComp (PartySpec C E RealSpec) _) >>= fun u => (f u).run := by
  simp only [oracleStep, localStep, hashQuery, OptionT.run_bind, OptionT.run_lift]
  rfl

/-- A call of `RoSpec` that a run of the expansions of the coin key `key` does not make. -/
def BadFor (key : HashOutput) : (RoSpec C).Domain → Prop
  | .inl (.coinKey ..) => True
  | .inl (.expand k _) => k ≠ key
  | _ => False

/-- A computation of `H` and `PRG` with no coin call and only the expansions of `key` keeps the last
coin answer `key`. -/
theorem programFlow_oracleStep_key {α : Type} (key : HashOutput) (oa : OracleComp (RoSpec C) α)
    (h : NoCall (BadFor key) oa) :
    ∀ n, ProgramFlow (fun _ last => last = some key) (oracleStep oa : PartyM C E RealSpec α).run n (some key) := by
  rw [noCall_iff] at h
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n
    rw [oracleStep_run_pure]
    rfl
  | query_bind t k ih =>
    intro n
    rw [isQueryBoundP_query_bind_iff] at h
    have ht : ¬ BadFor key t := by
      rcases h.1 with h1 | h1
      · exact h1
      · omega
    rw [oracleStep_run_query_bind, programFlow_query_bind]
    have hk : ∀ u, IsQueryBoundP (k u) (BadFor key) 0 := fun u => by
      have := h.2 u
      simpa only [ht, ↓reduceIte] using this
    have hcoin : ¬ IsCoin (C := C) (.inr t) := by
      intro hc
      rcases t with q | x
      · cases q <;> simp_all [IsCoin, BadFor]
      · exact hc
    refine ⟨⟨fun hc => absurd hc hcoin, fun k' hk' => ?_⟩, fun u => ?_⟩
    · rcases t with q | x
      · cases q <;> simp_all [expandKeyOf, BadFor]
      · cases hk'
    · simpa only [programBudget, programLast, hcoin, ↓reduceIte] using ih u (hk u) n

/-- The flows of a program on a state, from each state. -/
def SFlows {σ α : Type} (p : StateT σ (PartyM C E RealSpec) α) (n : ℕ) : Prop := ∀ s, Flows (p.run s) n

theorem Flows.mono {α : Type} {p : PartyM C E RealSpec α} {n m : ℕ} (h : Flows p n) (hnm : n ≤ m) : Flows p m :=
  fun last => (h last).mono hnm

theorem Flows.of_classBound {α : Type} {p : PartyM C E RealSpec α} (h : ClassBound .challenge p 0) : Flows p 0 :=
  fun last => (programFlow_of_noChallenge p.run h 0 last).post fun _ _ _ => trivial

theorem Flows.bind {α β : Type} {p : PartyM C E RealSpec α} {f : α → PartyM C E RealSpec β} {n m : ℕ}
    (hp : Flows p n) (hf : ∀ a, some a ∈ support p.run → Flows (f a) m) : Flows (p >>= f) (n + m) := by
  intro last
  rw [OptionT.run_bind, Option.elimM]
  refine ProgramFlow.bind (hp last) fun o last' ho _ => ?_
  rcases o with _ | a
  · trivial
  · exact hf a ho last'

theorem SFlows.mono {σ α : Type} {p : StateT σ (PartyM C E RealSpec) α} {n m : ℕ} (h : SFlows p n) (hnm : n ≤ m) :
    SFlows p m := fun s => (h s).mono hnm

theorem SFlows.of_stateBound {σ α : Type} {p : StateT σ (PartyM C E RealSpec) α} (h : StateBound .challenge p 0) :
    SFlows p 0 := fun s => Flows.of_classBound (h s)

theorem SFlows.pure {σ α : Type} (a : α) : SFlows (pure a : StateT σ (PartyM C E RealSpec) α) 0 :=
  SFlows.of_stateBound (StateBound.pure a)

theorem SFlows.bind {σ α β : Type} {p : StateT σ (PartyM C E RealSpec) α} {f : α → StateT σ (PartyM C E RealSpec) β}
    {n m : ℕ} (hp : SFlows p n) (hf : ∀ a, SFlows (f a) m) : SFlows (p >>= f) (n + m) := fun s => by
  rw [StateT.run_bind]
  exact Flows.bind (hp s) fun a _ => hf a.1 a.2

theorem SFlows.zero_bind {σ α β : Type} {p : StateT σ (PartyM C E RealSpec) α}
    {f : α → StateT σ (PartyM C E RealSpec) β} {n : ℕ} (hp : SFlows p 0) (hf : ∀ a, SFlows (f a) n) :
    SFlows (p >>= f) n :=
  (SFlows.bind hp hf).mono (Nat.zero_add _).le

theorem SFlows.lift {σ α : Type} {p : PartyM C E RealSpec α} {n : ℕ} (h : Flows p n) :
    SFlows (StateT.lift p : StateT σ (PartyM C E RealSpec) α) n := fun s => by
  rw [StateT.run_lift]
  exact (Flows.bind (m := 0) h fun a _ => Flows.of_classBound (ClassBound.pure (a, s))).mono (Nat.add_zero _).le

theorem SFlows.foldlM {σ α γ : Type} (f : α → γ → StateT σ (PartyM C E RealSpec) α) (n : ℕ)
    (hf : ∀ a g, SFlows (f a g) n) : ∀ (xs : List γ) (a : α), SFlows (xs.foldlM f a) (xs.length * n)
  | [], a => by simpa using SFlows.pure (σ := σ) a
  | g :: xs, a => by
    rw [List.foldlM_cons]
    simpa [Nat.succ_mul, Nat.add_comm] using (hf a g).bind fun a' => SFlows.foldlM f n hf xs a'

theorem SFlows.mapM {σ α β : Type} (f : α → StateT σ (PartyM C E RealSpec) β) (n : ℕ) :
    ∀ xs : List α, (∀ a ∈ xs, SFlows (f a) n) → SFlows (xs.mapM f) (xs.length * n)
  | [], _ => by simpa using SFlows.pure (σ := σ) ([] : List β)
  | a :: xs, hf => by
    rw [List.mapM_cons]
    simpa [Nat.succ_mul, Nat.add_comm] using
      (hf a (List.mem_cons_self ..)).bind fun b => (SFlows.mapM f n xs fun a' ha' =>
        hf a' (List.mem_cons_of_mem _ ha')).bind fun bs => SFlows.pure (σ := σ) (b :: bs)

variable [Field E] [Algebra Bit E] (K : Constants C E) (ctx : Context C)

/-- A coin key and then a computation of its expansions make one coin call. -/
theorem sflows_coinKey_then {γ β : Type} (oa : HashOutput → OracleComp (RoSpec C) γ)
    (hoa : ∀ key, NoCall (BadFor key) (oa key)) (g : γ → RunM C E RealSpec β) (m : ℕ) (hg : ∀ c, SFlows (g c) m) :
    SFlows (coinKey K (realCheckBuildingBlocks K ctx) >>= fun key => StateT.lift (oracleStep (oa key)) >>= g)
      (1 + m) := by
  unfold coinKey
  simp only [bind_assoc]
  refine SFlows.zero_bind (SFlows.of_stateBound StateBound.get) fun state => ?_
  refine SFlows.zero_bind (SFlows.of_stateBound (coin_bound (c := .challenge) K ctx nofun 2)) fun values => ?_
  intro s last
  simp only [StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  rw [oracleStep_hashQuery_bind_run, programFlow_query_bind]
  refine ⟨⟨fun _ => by omega, fun key h => nomatch h⟩, fun u => ?_⟩
  have hcoin : IsCoin (C := C) (.inr (.inl (.coinKey state.tag state.label
      (values.flatMap fun v => List.ofFn (K.encode v))))) := trivial
  simp only [programBudget, programLast, hcoin, ↓reduceIte, answerKey]
  rw [OptionT.run_bind, Option.elimM, show 1 + m - 1 = 0 + m by omega]
  refine ProgramFlow.bind (programFlow_oracleStep_key u (oa u) (hoa u) 0) fun o last' _ _ => ?_
  rcases o with _ | c
  · trivial
  · exact hg c s last'

/-- The search of a challenge calls `H` only on the expansions of its key. -/
theorem noCall_findChallenge_key (key : HashOutput) :
    ∀ tries index, NoCall (BadFor key) (findChallenge K key tries index) := by
  intro tries
  induction tries with
  | zero => intro index; exact noCall_pure _ _
  | succ tries ih =>
    intro index
    unfold findChallenge
    refine noCall_bind _ (noCall_query _ _ fun h => h rfl) fun r => ?_
    dsimp only
    generalize Classical.propDecidable (elementOfHash K r ≠ 0 ∧ elementOfHash K r ≠ 1) = d
    rcases d with ⟨_ | _, _⟩
    · exact ih _
    · exact noCall_pure _ _

/-- A challenge makes one coin call. -/
theorem sflows_challenge : SFlows (challenge K (realCheckBuildingBlocks K ctx)) 1 := by
  unfold challenge
  refine (sflows_coinKey_then K ctx (fun key => findChallenge K key challengeTries 0)
    (fun key => noCall_findChallenge_key K key _ _) _ 0 fun o => ?_).mono (by omega)
  rcases o with _ | r
  · exact SFlows.of_stateBound (StateBound.lift_zero ClassBound.failure)
  · exact SFlows.pure _

/-- The check of tuples of the count `count` makes at most `halvings count + 2` coin calls. -/
theorem sflows_check (tuples : List (Tuple C)) :
    SFlows (check K ctx (realCheckBuildingBlocks K ctx) tuples) (halvings (tuples.map (·.count)).sum + 2) := by
  unfold check
  dsimp only
  split_ifs with hz
  · exact (SFlows.pure _).mono (Nat.zero_le _)
  have hs : sliceBits ≤ halvings (tuples.map (·.count)).sum := by unfold halvings; omega
  refine (sflows_coinKey_then K ctx (fun key => (List.range (coins (tuples.map (·.count)).sum)).mapM fun k =>
    elementOfHash K <$> hashQuery (.expand key k)) (fun key => noCall_mapM _ _ _ fun k => noCall_map _ _
    (noCall_query _ _ fun h => h rfl)) _
    ((List.range sliceBits).length * 1 + ((List.range (halvings (tuples.map (·.count)).sum - sliceBits)).length * 1 +
      (1 + 0))) fun τ => ?_).mono (by simp; omega)
  refine SFlows.zero_bind (SFlows.of_stateBound (StateBound.lift_zero (ClassBound.require _))) fun _ => ?_
  refine SFlows.bind (SFlows.foldlM _ 1 (fun v j => ?_) _ _) fun v => ?_
  · rcases v with ⟨xs, ys, D⟩
    refine SFlows.zero_bind (SFlows.of_stateBound (extendMult_bound (c := .challenge) K ctx nofun _)) fun _ => ?_
    exact (SFlows.bind (sflows_challenge K ctx) fun _ => SFlows.pure _).mono (by omega)
  rcases v with ⟨xs, ys, D⟩
  refine SFlows.bind (SFlows.foldlM _ 1 (fun v j => ?_) _ _) fun v => ?_
  · rcases v with ⟨A, B, D⟩
    refine SFlows.zero_bind (SFlows.of_stateBound (extendMult_bound (c := .challenge) K ctx nofun _)) fun _ => ?_
    exact (SFlows.bind (sflows_challenge K ctx) fun _ => SFlows.pure _).mono (by omega)
  rcases v with ⟨A, B, D⟩
  refine SFlows.zero_bind (SFlows.of_stateBound
    (prssRandomness_bound (c := .challenge) ctx _ (noCall_elementCodec K nofun) _ _)) fun w => ?_
  refine SFlows.zero_bind (SFlows.of_stateBound (extendMult_bound (c := .challenge) K ctx nofun _)) fun q => ?_
  refine SFlows.zero_bind (SFlows.of_stateBound
    (prssRandomness_bound (c := .challenge) ctx _ (noCall_bitCodec nofun) _ _)) fun salts => ?_
  refine SFlows.zero_bind (SFlows.of_stateBound ((compareDigests_bound (c := .challenge) ctx _).mono
    (by simp [digestCost]))) fun _ => ?_
  refine SFlows.bind (sflows_challenge K ctx) fun _ => ?_
  exact SFlows.zero_bind (SFlows.of_stateBound (StateBound.lift_zero (openSh_bound K ctx _ _))) fun _ =>
    SFlows.of_stateBound (StateBound.lift_zero (ClassBound.require _))

/-- `runJobs` is its head, then `verify` and `output`. -/
theorem runJobs_head {ι : Type} {G : OracleSpec ι} (bb : RunBuildingBlocks C E G) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    runJobs K bb jobs inputs = runJobsHead K bb jobs inputs >>= fun h => bb.verify h.1 >>= fun _ =>
      bb.output h.2.1 h.2.2.1 >>= fun opened =>
        pure (h.2.2.2.zipIdx.map fun (width, k) => vector width fun g => opened ((h.2.2.2.take k).sum + g)) := by
  simp only [runJobs, runJobsHead, bind_assoc, pure_bind]
  rfl

/-- The head of a batch makes no call outside the class `stream`. -/
theorem runJobsHead_bound {c : HashClass} (hc : c ≠ .stream) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    StateBound c (runJobsHead K (realRunBuildingBlocks K ctx mode) jobs inputs : RunM C E RealSpec _) 0 := by
  unfold runJobsHead
  refine StateBound.zero_bind (StateBound.foldlM _ 0 (fun v layer => ?_) _ _ |>.mono (by simp)) fun v => ?_
  · rcases v with ⟨wires, tuples⟩
    exact StateBound.bind_zero (mult_bound K ctx hc mode _ _ _) fun _ => StateBound.pure _
  rcases v with ⟨wires, tuples⟩
  refine StateBound.zero_bind (?_ : StateBound c ((realRunBuildingBlocks K ctx mode).rerand _ _) 0) fun v' =>
    StateBound.pure _
  unfold realRunBuildingBlocks
  exact StateBound.zero_bind (prssRandomness_bound ctx _ (noCall_bitCodec hc) _ _) fun _ =>
    reshare_bound K ctx _ _ _ _

/-- The counts of the tuples of the head of a batch sum to the tuple count of its circuits. -/
theorem sum_headCounts (jobs : List Circuit) : (headCounts jobs).sum = tupleCount jobs := by
  rw [headCounts, List.sum_append, List.sum_singleton, tupleCount_eq]

/-- A run of a batch of circuits with at most `M` halving steps in its check makes at most `M + 2`
coin calls. -/
theorem flows_runJobs (mode : ReshareMode) (jobs : List Circuit) (inputs : List (C.Term → List Bit)) (L tg M : ℕ)
    (hM : halvings (tupleCount jobs) ≤ M) :
    Flows ((runJobs K (realRunBuildingBlocks K ctx mode) jobs inputs).run ⟨fun _ => [], L, tg⟩) (M + 2) := by
  rw [runJobs_head, StateT.run_bind]
  refine (Flows.bind (n := 0) (m := M + 2) (Flows.of_classBound (runJobsHead_bound K ctx (c := .challenge) nofun mode jobs inputs _))
    fun h hh => ?_).mono (by omega)
  obtain ⟨-, hcount⟩ := runJobsHead_support K ctx mode jobs inputs L tg h hh
  have hsum : (h.1.1.map (·.count)).sum = tupleCount jobs := by rw [hcount, sum_headCounts]
  refine ((SFlows.bind (sflows_check K ctx h.1.1) fun _ => SFlows.zero_bind
    (SFlows.of_stateBound (StateBound.lift (openRep_bound (c := .challenge) K ctx _ _) |>.mono
      (by simp [copyCost]))) fun _ => SFlows.pure _) h.2).mono ?_
  rw [hsum]
  omega

end Blocks

/-! ## The coin calls of one ceremony and the ledger -/

section Ceremony

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
  (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

attribute [local instance] inhabitedField

/-- The coin keys of one batch at one operator, `R + 2` for the most halving steps `R` of a batch. -/
def batchCoins (circuits : Circuits) (settings : Settings) : ℕ :=
  maxBatch circuits settings (fun jobs => halvings (tupleCount jobs)) + 2

omit [Fintype E] [DecidableEq E] in
/-- A call in a class is a counted call. -/
theorem counted_of_inClass {c : HashClass} {t : (LocalSpec C).Domain} (h : InClass c t) :
    ThresholdLeanXmss.Counted t := by
  rcases t with _ | q | _
  · exact h.elim
  · cases q
    · exact h.1
    all_goals trivial
  · trivial

omit [Fintype E] [DecidableEq E] in
/-- A full real batch with at most `M` halving steps in its check makes at most `M + 2` coin calls. -/
theorem sflows_realBatch (ctx : Context C) (parameter : PublicParameter) (js : List Job) (M : ℕ)
    (hM : halvings (tupleCount (js.map (circuits parameter ·.kind))) ≤ M) :
    SFlows (realBatch K circuits settings.mode ctx parameter js) (M + 2) := by
  unfold realBatch
  refine SFlows.zero_bind (SFlows.of_stateBound StateBound.get) fun lk => ?_
  rcases lk with ⟨label, k⟩
  refine SFlows.zero_bind (SFlows.of_stateBound (StateBound.lift_zero ((ClassBound.mapM _ 0
    (fun job => inputShares_bound (c := .challenge) _ nofun job) _).mono (by simp)))) fun inputs => ?_
  refine (SFlows.bind (m := 0) (SFlows.lift (flows_runJobs K ctx settings.mode _ inputs label k M hM)) fun r => ?_).mono
    (by omega)
  rcases r with ⟨outputs, state⟩
  exact SFlows.zero_bind (SFlows.of_stateBound (StateBound.set _)) fun _ => SFlows.pure _

omit [Fintype E] [DecidableEq E] in
/-- The coin calls of one honest operator in one ceremony of admissible jobs. From each counter pair and
each last coin answer, the program `ceremonyRun` makes at most `batchCoins` coin calls for each batch,
and each of its expansion calls has the key of its last coin call, on every path, an abort included.
The job list is any admissible list. So a signature ceremony is covered for each encoding whose job
list is admissible. -/
theorem flows_ceremonyRun (i : C.Party) (keys : Keys C) (jobs : List Job) (hadm : AdmissibleJobs circuits settings jobs)
    (st : ℕ × ℕ) :
    Flows ((ceremonyRun K circuits settings (fun ctx _ _ => realRunBuildingBlocks K ctx settings.mode) i keys jobs :
        StateT (ℕ × ℕ) (PartyM C E RealSpec) _).run st)
      ((chunks settings.batchSize jobs).length * batchCoins circuits settings) := by
  rw [CheckTiming.ceremonyRun_run_keys]
  refine (Flows.bind (n := 0) (m := (chunks settings.batchSize jobs).length * batchCoins circuits settings)
    (Flows.of_classBound (prssSetup_bound (c := .challenge) nofun i)) fun prss _ => ?_).mono (by omega)
  exact (Flows.bind (m := 0) (SFlows.mapM _ _ _ (fun js hjs => sflows_realBatch K circuits settings _ _ js _
    (hadm keys.parameter js hjs).2) st) fun p _ => Flows.of_classBound (ClassBound.pure _)).mono
    (by unfold batchCoins; omega)

omit [Fintype E] [DecidableEq E] in
/-- The coin calls of the program of one honest operator in one ceremony of admissible jobs. -/
theorem flows_ceremonyProgram (i : C.Party) {σ : Type} (s : CeremonyStart C σ)
    (hadm : AdmissibleJobs circuits settings s.jobs) :
    Flows (ceremonyProgram K circuits settings i s) ((chunks settings.batchSize s.jobs).length * batchCoins circuits settings) := by
  unfold ceremonyProgram
  rcases s.keys i with _ | keys
  · exact (Flows.of_classBound ClassBound.failure).mono (Nat.zero_le _)
  · refine (Flows.bind (m := 0) (flows_ceremonyRun K circuits settings i keys s.jobs hadm s.counters) fun p _ => ?_).mono
      (by omega)
    rcases p with ⟨_ | outputs, st⟩
    · exact Flows.of_classBound ClassBound.failure
    · exact Flows.of_classBound (ClassBound.pure _)

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
/-- The ledger of the coin keys and of the expansion keys for one phase. An adversary with `step`
counted calls in a round and honest programs with the coin budgets `budget` add at most
`fuel * step + ∑ j, budget j` charged inputs and `∑ j, budget j` expansion keys. -/
theorem phase_soundCache (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (step fuel : ℕ)
    (hround : ∀ st sent, IsQueryBoundP (net.round st sent) ThresholdLeanXmss.Counted step) (st : net.State)
    {α : Type} (program : C.Party → PartyM C E RealSpec α) (budget : C.Party → ℕ)
    (hp : ∀ j, j ∉ D.1 → Flows (program j) (budget j)) (w : StreamState C) (seen : Finset (Query C))
    (keys : Finset HashOutput) (hs : SoundCache 0 w.1 seen keys) :
    ∀ r ∈ support ((simulateQ (streamWorld prims D)
        (executePhase worldRoles D net noFunctionality fuel st program)).run w),
      ∃ (seen' : Finset (Query C)) (keys' : Finset HashOutput), SoundCache 0 r.2.1 seen' keys' ∧
        seen'.card ≤ seen.card + fuel * step + ∑ j, budget j ∧ keys'.card ≤ keys.card + ∑ j, budget j :=
  simulateQ_soundCache prims D _ _ _ ∅ w seen keys
    (ownAdds_executePhase .challenge D net step (fun s m => (hround s m).of_imp fun _ h => counted_of_inClass h)
      fuel st program)
    (worldFlow_executePhase D net fuel st program budget hp ∅) (Finset.empty_subset _) hs

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] in
theorem sum_batchCoins (batches : ℕ) :
    ∑ _j : C.Party, batches * batchCoins circuits settings = coinKeysOf circuits settings C batches := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  unfold coinKeysOf batchCoins
  ring

omit [Fintype E] [DecidableEq E] in
/-- `LedgerSound`. -/
theorem ledgerSound : LedgerSound prims K circuits settings := by
  intro D net step rounds hround coins keys c world hadm ⟨seen, ekeys, hs, hseen, hkeys⟩ r hr
  obtain ⟨seen', keys', h', hc', hk'⟩ := phase_soundCache prims D net step rounds hround c.adversary _ _
    (fun j _ => flows_ceremonyProgram K circuits settings j c hadm) world seen ekeys hs r hr
  rw [sum_batchCoins] at hc' hk'
  exact ⟨seen', keys', h', by omega, by omega⟩

end Ceremony

end ThresholdLeanXmssSecurity.DkgCorrectnessProof

end

end

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.ledgerSound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.ledgerSound

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.flows_ceremonyRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.flows_ceremonyRun

/-- info: 'ThresholdLeanXmssSecurity.DkgCorrectnessProof.phase_soundCache' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgCorrectnessProof.phase_soundCache
