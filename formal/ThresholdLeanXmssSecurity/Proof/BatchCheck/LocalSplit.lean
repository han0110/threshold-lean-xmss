import ThresholdLeanXmssSecurity.Proof.BatchCheck.Streams
import ThresholdLeanXmssSecurity.Proof.CheckSound
import ThresholdLeanXmssSecurity.Proof.CheckSplit

/-!
# The frame of the stream calls, and the local split of the check

The lift of the covers through a coin and a whole check, and the check of batch `k` from the cache of
a ceremony, come first. The split of the check on the local oracles follows. The known rows of a
check keep the covers, and each stream call of the wrapper of a batch keeps the frame.
-/

section

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss Finset ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace C3

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

section Covers

variable {C : Committee} {α : Type}

/-- The four domains of `H` that only a check fills, and a counted call. -/
def CheckDomain : Query C → Prop
  | .coinKey _ _ _ => True
  | .expand _ _ => True
  | .history _ => True
  | .digest _ _ => True
  | _ => False

/-- A call that can fill a cell of the domain `P`. -/
def Fills (P : Query C → Prop) (t : (LocalSpec C).Domain) : Prop :=
  ∃ q, soundQueryProjection t = some q ∧ P q

lemma splitRegion_fills (t : (LocalSpec C).Domain) (h : SplitRegionCounted SplitHashDomain t) :
    Fills CheckDomain t := by
  obtain ⟨q, hq, hP⟩ := h
  rcases t with n | r | x
  · simp [splitLocalHashInput] at hq
  · refine ⟨q, ?_, ?_⟩
    · simpa [splitLocalHashInput, soundQueryProjection] using hq
    · cases q <;> simp_all [SplitHashDomain, CheckDomain]
  · simp only [splitLocalHashInput, Option.some.injEq] at hq
    subst hq
    exact absurd hP (by simp [SplitHashDomain])

end Covers

end C3

end ThresholdLeanXmssSecurity

end

end

section

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss Finset ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

namespace S9a

attribute [local instance] Classical.propDecidable

attribute [local irreducible] MonadAttach.support

/-! ## The covers of a cache -/

section Covers

variable {C : Committee} {α : Type}

/-- The four domains of `H` that only a check fills, and a counted call. -/
def CheckDomain : Query C → Prop
  | .coinKey _ _ _ => True
  | .expand _ _ => True
  | .history _ => True
  | .digest _ _ => True
  | _ => False

/-- A call that can fill a cell of the domain `P`. -/
def Fills (P : Query C → Prop) (t : (LocalSpec C).Domain) : Prop :=
  ∃ q, soundQueryProjection t = some q ∧ P q

/-- A local computation with at most `n` calls in the four domains adds at most `n` cells to the
part of `SoundCache` that a call fills. The other calls add nothing. -/
theorem soundCache_local (prims : Primitives) (oa : OracleComp (LocalSpec C) α) :
    ∀ n, IsQueryBoundP oa (Fills CheckDomain) n → ∀ (L : ℕ) (cache : HashCache C) (seen : Finset (Query C))
      (keys : Finset HashOutput), SoundCache L cache seen keys →
    ∀ p ∈ support ((simulateQ (localAnswer prims) oa).run cache),
      ∃ seen' : Finset (Query C), SoundCache L p.2 seen' keys ∧ seen'.card ≤ seen.card + n := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro n _ L cache seen keys hc p hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst p
    exact ⟨seen, hc, Nat.le_add_right _ _⟩
  | query_bind t f ih =>
    intro n hn L cache seen keys hc p hp
    rw [isQueryBoundP_query_bind_iff] at hn
    change p ∈ support ((localAnswer prims t >>= fun u => simulateQ (localAnswer prims) (f u)).run cache) at hp
    rw [StateT.run_bind, mem_support_bind_iff] at hp
    obtain ⟨⟨u, s⟩, hu, hp⟩ := hp
    have he := localAnswer_sound_entries prims cache t (u, s) hu
    by_cases ht : Fills CheckDomain t
    · have hnpos := hn.1.resolve_left (not_not.mpr ht)
      obtain ⟨q, hq, _⟩ := id ht
      have hs : SoundCache L s (insert q seen) keys := by
        constructor
        · intro tag label bits hL hk
          rcases he _ hk with h | h
          · exact Finset.mem_insert_of_mem (hc.1 _ _ _ hL h)
          · rw [hq] at h
            simp only [Option.toList_some, List.mem_singleton] at h
            exact h ▸ Finset.mem_insert_self _ _
        · intro key idx hk
          rcases he _ hk with h | h
          · exact (hc.2 _ _ h).imp_right Finset.mem_insert_of_mem
          · rw [hq] at h
            simp only [Option.toList_some, List.mem_singleton] at h
            exact Or.inr (h ▸ Finset.mem_insert_self _ _)
      have hu' := hn.2 u
      simp only [ht, ↓reduceIte] at hu'
      obtain ⟨seen', hs', hcard⟩ := ih u (n - 1) hu' L s _ keys hs p hp
      exact ⟨seen', hs', hcard.trans (by have := Finset.card_insert_le q seen; omega)⟩
    · have hs : SoundCache L s seen keys := by
        constructor
        · intro tag label bits hL hk
          rcases he _ hk with h | h
          · exact hc.1 _ _ _ hL h
          · exact absurd ⟨Query.coinKey tag label bits, by simpa using h, trivial⟩ ht
        · intro key idx hk
          rcases he _ hk with h | h
          · exact hc.2 _ _ h
          · exact absurd ⟨Query.expand key idx, by simpa using h, trivial⟩ ht
      have hu' := hn.2 u
      simp only [ht, ↓reduceIte] at hu'
      exact ih u n hu' L s seen keys hs p hp

end Covers

/-! ## The bound of one check against section 5.3 of the plan -/

section Bound

variable {C : Committee} {E : Type} [Fintype E]

end Bound

end S9a

end ThresholdLeanXmssSecurity

end

end

section
set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.RealNetworkCLp
open RealNetworkALP RealNetworkV3 RealNetworkE1s
attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP
variable {C : Committee} {E : Type} {ι α β : Type} {G : OracleSpec ι}

variable [Field E] [Algebra Bit E]

omit [Field E] [Algebra Bit E] in
lemma prgBits_frame (name : KeyName C) (key : HashOutput) (label idx count : ℕ) :
    IsQueryBoundP (prgBits name key label idx count)
      (fun t => C3.Fills C3.CheckDomain (.inr t)) 0 := by
  unfold prgBits
  refine isQueryBoundP_bind_zero _ _ ?_ (fun _ => isQueryBoundP_pure _ _ _)
  apply isQueryBoundP_mapM_zero
  intro position _
  exact (isQueryBoundP_query_iff ..).2
    (by simp [C3.Fills, soundQueryProjection, C3.CheckDomain])

end ThresholdLeanXmssSecurity.RealNetworkCLp

end

end

section
set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.RealNetworkCLp
open RealNetworkALP RealNetworkV3
attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP
variable {C : Committee} {E : Type}
variable {ι α β : Type} {G : OracleSpec ι}

/-- The existing party query bound restricted to history and digest calls. -/
abbrev SplitPartyBound (p : PartyM C E G α) (n : ℕ) : Prop :=
  IsQueryBoundP p.run (PartyCalls (G := G) (SplitRegionCounted SplitHashDomain)) n

abbrev SplitRunBound (p : RunM C E G α) (n : ℕ) : Prop :=
  ∀ hs, SplitPartyBound (p.run hs) n

lemma SplitPartyBound.of_counted {p : PartyM C E G α} {n : ℕ} (h : PartyBound p n) :
    SplitPartyBound p n := by
  apply IsQueryBoundP.of_imp _ h
  intro t ht
  rcases t with (t | t) | t
  · have hh := splitRegionCounted_counted _ _ ht
    cases t with
    | inl n => exact hh.elim
    | inr q => trivial
  · exact ht.elim
  · exact ht.elim

lemma SplitRunBound.of_counted {p : RunM C E G α} {n : ℕ} (h : RunBound p n) :
    SplitRunBound p n := fun hs => SplitPartyBound.of_counted (h hs)

lemma SplitPartyBound.bind {p : PartyM C E G α} {f : α → PartyM C E G β} {n m : ℕ}
    (h : SplitPartyBound p n) (hf : ∀ a, SplitPartyBound (f a) m) :
    SplitPartyBound (p >>= f) (n + m) := by
  simp only [SplitPartyBound, OptionT.run_bind]
  refine isQueryBoundP_bind h fun a _ => ?_
  cases a with
  | none => exact isQueryBoundP_pure _ _ _
  | some a => exact hf a

lemma SplitRunBound.bind {p : RunM C E G α} {f : α → RunM C E G β} {n m : ℕ}
    (h : SplitRunBound p n) (hf : ∀ a, SplitRunBound (f a) m) :
    SplitRunBound (p >>= f) (n + m) := fun hs =>
  SplitPartyBound.bind (h hs) fun a => hf a.1 a.2

lemma SplitRunBound.mono {p : RunM C E G α} {n m : ℕ} (h : SplitRunBound p n) (hnm : n ≤ m) :
    SplitRunBound p m := fun hs => (h hs).mono hnm

lemma SplitRunBound.lift {p : PartyM C E G α} {n : ℕ} (h : SplitPartyBound p n) :
    SplitRunBound (StateT.lift p : RunM C E G α) n := by
  intro hs
  change SplitPartyBound (p >>= fun a => pure (a, hs)) n
  simpa using SplitPartyBound.bind h (f := fun a => pure (a, hs)) (m := 0)
    (fun a => isQueryBoundP_pure _ _ _)

lemma SplitRunBound.foldlM {γ : Type} (f : α → γ → RunM C E G α)
    (hf : ∀ a g, SplitRunBound (f a g) 0) :
    ∀ (xs : List γ) (a : α), SplitRunBound (xs.foldlM f a) 0
  | [], a => fun hs => isQueryBoundP_pure _ _ _
  | g :: xs, a => by
    rw [List.foldlM_cons]
    exact (hf a g).bind fun a' => SplitRunBound.foldlM f hf xs a'

lemma split_oracleStep_zero (oa : OracleComp (RoSpec C) α)
    (h : IsQueryBoundP oa (fun t => SplitRegionCounted SplitHashDomain (.inr t)) 0) :
    SplitPartyBound (oracleStep oa : PartyM C E G α) 0 := by
  exact isQueryBoundP_localStep _ _ (isQueryBoundP_liftComp_ro _ oa h)

lemma split_hash_zero (q : Query C) (hq : ¬ SplitHashDomain q) :
    IsQueryBoundP (hashQuery q) (fun t => SplitRegionCounted SplitHashDomain (.inr t)) 0 := by
  change IsQueryBoundP (liftM (OracleSpec.query (spec := RoSpec C) (.inl q)) : OracleComp (RoSpec C) _ ) _ 0
  rw [isQueryBoundP_query_iff]
  intro h
  simp only [SplitRegionCounted, splitLocalHashInput] at h
  split_ifs at h with hf
  · simp at h
  · obtain ⟨q', he, hp⟩ := h
    cases Option.some.inj he
    exact (hq hp).elim

variable [Field E] [Algebra Bit E]

lemma split_findChallenge (K : Constants C E) (key : HashOutput) : ∀ tries index,
    IsQueryBoundP (findChallenge K key tries index)
      (fun t => SplitRegionCounted SplitHashDomain (.inr t)) 0
  | 0, _ => isQueryBoundP_pure _ _ _
  | tries + 1, index => by
    rw [findChallenge]
    refine isQueryBoundP_bind_zero _ _ (split_hash_zero _ (by simp [SplitHashDomain])) fun _ => ?_
    dsimp only
    split
    · exact isQueryBoundP_pure _ _ _
    · exact split_findChallenge K key tries (index + 1)

lemma split_expand (K : Constants C E) (key : HashOutput) (count : ℕ) :
    SplitRunBound (expand K key count : RunM C E G (List E)) 0 := by
  unfold expand
  apply SplitRunBound.lift
  apply split_oracleStep_zero
  apply isQueryBoundP_mapM_zero
  intro k _
  exact (isQueryBoundP_map_iff ..).2 (split_hash_zero _ (by simp [SplitHashDomain]))

lemma split_coinKey_local (K : Constants C E) (B : CheckBuildingBlocks C E G)
    (hb : ∀ n, SplitRunBound (B.coin n) 0) : SplitRunBound (coinKey K B) 0 := by
  unfold coinKey
  refine (SplitRunBound.of_counted RunBound.get).bind (m := 0) fun hs =>
    (hb 2).bind (m := 0) fun values => ?_
  exact SplitRunBound.lift (split_oracleStep_zero _ (split_hash_zero _ (by simp [SplitHashDomain])))

lemma split_challenge_local (K : Constants C E) (B : CheckBuildingBlocks C E G)
    (hb : ∀ n, SplitRunBound (B.coin n) 0) : SplitRunBound (challenge K B) 0 := by
  unfold challenge
  refine (split_coinKey_local K B hb).bind (m := 0) fun key =>
    (SplitRunBound.lift (split_oracleStep_zero _ (split_findChallenge K key _ _))).bind (m := 0) fun res => ?_
  split
  · exact SplitRunBound.of_counted (RunBound.pure _)
  · exact SplitRunBound.of_counted (RunBound.lift PartyBound.failure)

lemma check_split_local (K : Constants C E) (ctx : Context C) (B : CheckBuildingBlocks C E G)
    (hc : ∀ n, SplitRunBound (B.coin n) 0) (he : ∀ ps, SplitRunBound (B.extendMult ps) 0)
    (hE : ∀ n, SplitRunBound (B.randElements n) 0) (hB : ∀ n, SplitRunBound (B.randBits n) 0)
    (tuples : List (Tuple C)) :
    SplitRunBound (check K ctx B tuples) (2 * C.terms.length) := by
  have hs : ∀ τ count v j, SplitRunBound (sliceStep K ctx B τ count v j) 0 := by
    intro τ count ⟨xs, ys, d⟩ j
    unfold sliceStep
    exact (he _).bind fun _ =>
      (split_challenge_local K B hc).bind fun _ => SplitRunBound.of_counted (RunBound.pure _)
  have hh : ∀ width v j, SplitRunBound (halvingStep K ctx B width v j) 0 := by
    intro width ⟨a, b, d⟩ j
    unfold halvingStep
    exact (he _).bind fun _ =>
      (split_challenge_local K B hc).bind fun _ => SplitRunBound.of_counted (RunBound.pure _)
  have hf : ∀ v, SplitRunBound (finalStep K ctx B v) (2 * C.terms.length) := by
    intro ⟨a, b, d⟩
    unfold finalStep
    refine ((hE 2).bind fun _ =>
      (he _).bind fun _ =>
      (hB 256).bind fun salts =>
      (SplitRunBound.of_counted (compareDigests_queryBound ctx.self salts.1)).bind fun _ =>
      (split_challenge_local K B hc).bind fun _ =>
      (SplitRunBound.of_counted (RunBound.lift (RunBound.openSh K _ _ _))).bind fun _ =>
      SplitRunBound.of_counted (RunBound.lift (PartyBound.require _))).mono ?_
    omega
  by_cases hz : (tuples.map (·.count)).sum = 0
  · simp only [check, hz, ↓reduceIte]
    exact (SplitRunBound.of_counted (RunBound.pure ())).mono (Nat.zero_le _)
  · rw [check_eq K ctx B tuples hz]
    refine ((split_coinKey_local K B hc).bind fun key =>
      (split_expand K key _).bind fun _ =>
      (SplitRunBound.of_counted (RunBound.lift (PartyBound.require _))).bind fun _ =>
      (SplitRunBound.foldlM _ (hs _ _) _ _).bind fun _ =>
      (SplitRunBound.foldlM _ (hh _) _ _).bind fun v => hf v).mono ?_
    omega
end ThresholdLeanXmssSecurity.RealNetworkCLp

end

end

section
set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.RealNetworkCLp
open RealNetworkALP RealNetworkV3 RealNetworkE1s
attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP
variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}
variable [Field E] [Algebra Bit E]

lemma split_prgBits (name : KeyName C) (key : HashOutput) (L idx count : ℕ) :
    IsQueryBoundP (prgBits name key L idx count)
      (fun t => SplitRegionCounted SplitHashDomain (.inr t)) 0 := by
  exact IsQueryBoundP.of_imp (fun t h => C3.splitRegion_fills _ h)
    (prgBits_frame name key L idx count)

lemma split_prss {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R)
    (hd : ∀ name key L idx count, IsQueryBoundP (codec.draw name key L idx count)
      (fun t => SplitRegionCounted SplitHashDomain (.inr t)) 0) (idx count : ℕ) :
    SplitRunBound (prssRandomness (G := G) ctx codec idx count) 0 := by
  unfold prssRandomness
  refine (SplitRunBound.of_counted RunBound.freshLabel).bind (m := 0) fun L => ?_
  refine (SplitRunBound.lift (split_oracleStep_zero _ ?_)).bind (m := 0) fun r => ?_
  · apply isQueryBoundP_mapM_zero
    intro T _
    split_ifs
    · exact hd _ _ _ _ _
    · exact isQueryBoundP_pure _ _ _
  refine (SplitRunBound.lift (split_oracleStep_zero _ ?_)).bind (m := 0) fun Z =>
    SplitRunBound.of_counted (RunBound.pure _)
  apply isQueryBoundP_mapM_zero
  intro j _
  split_ifs
  · exact isQueryBoundP_pure _ _ _
  · exact hd _ _ _ _ _

lemma split_prss_bits (ctx : Context C) (idx count : ℕ) :
    SplitRunBound (prssRandomness (E := E) (G := G) ctx bitCodec idx count) 0 := by
  exact split_prss ctx bitCodec split_prgBits idx count

lemma split_prss_elements (K : Constants C E) (ctx : Context C) (idx count : ℕ) :
    SplitRunBound (prssRandomness (G := G) ctx (elementCodec K) idx count) 0 := by
  apply split_prss ctx (elementCodec K) _ idx count
  intro name key L idx count
  exact isQueryBoundP_bind_zero _ _ (split_prgBits _ _ _ _ _) (fun _ => isQueryBoundP_pure _ _ _)

lemma split_reshare {R : Type} [Field R] (K : Constants C E) (ctx : Context C)
    (codec : Codec C E R) (randomness : PrssOutput C R) (v : ℕ → R) (count : ℕ) :
    SplitRunBound (reshare (G := G) K ctx codec randomness v count) 0 := by
  unfold reshare
  exact (SplitRunBound.of_counted (RunBound.lift (PartyBound.exchange _))).bind fun _ =>
    (SplitRunBound.of_counted (RunBound.record K ctx codec _ _ _)).bind fun _ =>
    SplitRunBound.of_counted (RunBound.pure _)

end ThresholdLeanXmssSecurity.RealNetworkCLp

end

end

section
set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss
noncomputable section
namespace ThresholdLeanXmssSecurity.RealNetworkCLp
open RealNetworkALP RealNetworkV3 RealNetworkE1s
attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP
variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι}
variable [Field E] [Algebra Bit E]

lemma realCheck_split (K : Constants C E) (ctx : Context C) (tuples : List (Tuple C)) :
    SplitRunBound (check K ctx (realCheckBuildingBlocks (G := G) K ctx) tuples)
      (2 * C.terms.length) := by
  apply check_split_local K ctx
  · intro n
    dsimp only [realCheckBuildingBlocks]
    refine (split_prss_elements K ctx 1 n).bind (m := 0) fun r => ?_
    unfold coinWith
    exact (SplitRunBound.of_counted (RunBound.lift (RunBound.openSh K ctx _ _))).bind fun _ =>
      SplitRunBound.of_counted (RunBound.pure _)
  · intro ps
    exact (split_prss_elements K ctx 0 ps.length).bind fun r => split_reshare K ctx _ r _ _
  · exact fun n => split_prss_elements K ctx 1 n
  · exact fun n => split_prss_bits ctx 2 n

end ThresholdLeanXmssSecurity.RealNetworkCLp

end

end

section
set_option autoImplicit false
open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss Finset
noncomputable section
namespace ThresholdLeanXmssSecurity.RealNetworkCLp
open RealNetworkALP
attribute [local instance] Classical.propDecidable
attribute [local irreducible] MonadAttach.support OracleComp.IsQueryBoundP
variable {C : Committee} {E : Type} {ι : Type} {G : OracleSpec ι} {α β : Type}
variable {P : (LocalSpec C).Domain → Prop}

/-- The local budget remaining after the next round or hybrid call. -/
def LocalStepBound (P : (LocalSpec C).Domain → Prop) (st : Step C E G α) (n : ℕ) : Prop :=
  match st with
  | .done _ => True
  | .wait _ k => ∀ inbox, IsQueryBoundP (k inbox) (PartyCalls P (E := E) (G := G)) n
  | .call _ k => ∀ out, IsQueryBoundP (k out) (PartyCalls P (E := E) (G := G)) n

section NetworkBound
variable {I O Ia L R : Type} (D : C.Coalition) (A : Adversary C E Ia L R)
    (F : Functionality C I O L R)

lemma roundResume_localBound (sent : C.Party → C.Party → Option (Msg E))
    (steps : C.Party → Step C E (CallSpec I O) α) (budget : C.Party → ℕ)
    (h : ∀ j, LocalStepBound P (steps j) (budget j)) (j : C.Party) :
    IsQueryBoundP (roundResume D sent steps j) (PartyCalls P (E := E) (G := CallSpec I O)) (budget j) := by
  have hj := h j
  unfold roundResume
  cases hs : steps j with
  | done out => exact isQueryBoundP_pure _ _ _
  | call input k => exact isQueryBoundP_pure _ _ _
  | wait out k =>
    split_ifs
    · exact isQueryBoundP_pure _ _ _
    · simp only [LocalStepBound, hs] at hj
      exact hj _

end NetworkBound
variable [Field E] [Algebra Bit E] [SampleableType E]

end ThresholdLeanXmssSecurity.RealNetworkCLp

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkE1b

open RealNetworkE1s RealNetworkE1r RealNetworkE1g

attribute [local instance] Classical.propDecidable inhabitedField
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type}

/-! ## A call of `PRG` -/

/-- A call of the local oracles that is not a call of `PRG`. -/
def OtherCall : (LocalSpec C).Domain → Prop
  | .inr (.inr _) => False
  | _ => True

/-- A program with only calls of `PRG`. -/
def OnlyStreams {α : Type} (oa : OracleComp (LocalSpec C) α) : Prop :=
  IsQueryBoundP oa OtherCall 0

/-- Each call is a call of `PRG` or a call of `OtherCall`. -/
theorem stream_of_not_other (t : (LocalSpec C).Domain) (h : ¬ OtherCall t) : ∃ x : PrgInput C, t = .inr (.inr x) := by
  rcases t with n | q | x
  · exact (h trivial).elim
  · exact (h trivial).elim
  · exact ⟨x, rfl⟩

/-- A call that fills a cell of the four covered domains is not a call of `PRG`. -/
theorem other_of_fills (t : (LocalSpec C).Domain) (h : S9a.Fills S9a.CheckDomain t) : OtherCall t := by
  by_contra hn
  obtain ⟨x, rfl⟩ := stream_of_not_other t hn
  obtain ⟨q, hq, hd⟩ := h
  cases hq
  exact hd

/-- A digest call is not a call of `PRG`. -/
theorem other_of_digest (t : (LocalSpec C).Domain) (h : DigestQuery t) : OtherCall t := by
  by_contra hn
  obtain ⟨x, rfl⟩ := stream_of_not_other t hn
  simp [DigestQuery, digestSaltProjection] at h

namespace OnlyStreams

variable {α : Type} {oa : OracleComp (LocalSpec C) α}

/-- A program with only calls of `PRG` fills no cell of the four covered domains. -/
theorem fills (h : OnlyStreams oa) : IsQueryBoundP oa (S9a.Fills S9a.CheckDomain) 0 :=
  IsQueryBoundP.of_imp other_of_fills h

/-- A program with only calls of `PRG` makes no digest call. -/
theorem digest (h : OnlyStreams oa) : IsQueryBoundP oa DigestQuery 0 :=
  IsQueryBoundP.of_imp other_of_digest h

end OnlyStreams

/-! ## The known streams -/

section Streams

variable [Field E] [Algebra Bit E]

omit [Field E] [Algebra Bit E] in
/-- The known streams make no call of `P`, when a stream of the codec makes none. -/
theorem knownStreams_zero {R : Type} [Zero R] (P : (RoSpec C).Domain → Prop) (D : C.Coalition)
    (receivers : Finset C.Party) (codec : Codec C E R) (term : C.Term → HashOutput) (pair : C.Pair → HashOutput)
    (ρ idx count : ℕ) (hdraw : ∀ name key, IsQueryBoundP (codec.draw name key ρ idx count) P 0) :
    IsQueryBoundP (knownStreams D receivers codec term pair ρ idx count) P 0 := by
  have hterm := queryBound_mapM P (fun T => if KnownTo D.1 T ∧ ∃ i ∈ receivers, i ∉ D.1 ∧ i ∈ C.holders T then
    codec.draw (.term T) (term T) ρ idx count else pure fun _ => 0) 0 C.terms fun T _ => by
      split_ifs
      · exact hdraw _ _
      · exact isQueryBoundP_pure _ _ 0
  have hpair := queryBound_mapM P (fun j => C.parties.mapM fun i =>
    if h : j ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then
      codec.draw (.pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1))))
        (pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1)))) ρ idx count
    else pure fun _ => 0) 0 C.parties fun j _ => by
      simpa using queryBound_mapM P (fun i =>
        if h : j ∈ D.1 ∧ i ∉ D.1 ∧ i ∈ receivers then
          codec.draw (.pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1))))
            (pair (C.pairOf i j (fun e => h.2.1 (e ▸ h.1)))) ρ idx count
        else pure fun _ => 0) 0 C.parties fun i _ => by
          split_ifs
          · exact hdraw _ _
          · exact isQueryBoundP_pure _ _ 0
  rw [Nat.mul_zero] at hterm hpair
  unfold knownStreams
  exact isQueryBoundP_bind (m := 0) hterm fun _ _ =>
    isQueryBoundP_bind (m := 0) hpair fun _ _ => isQueryBoundP_pure _ _ 0

omit [Field E] [Algebra Bit E] in
/-- The known streams of bits have only calls of `PRG`. -/
theorem knownStreams_bits_only (D : C.Coalition) (receivers : Finset C.Party) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (ρ idx count : ℕ) :
    OnlyStreams (liftComp (knownStreams D receivers (bitCodec (E := E)) term pair ρ idx count) (LocalSpec C)) :=
  isQueryBoundP_liftComp_ro OtherCall _ (knownStreams_zero (fun t => OtherCall (.inr t)) D receivers bitCodec
    term pair ρ idx count fun name key =>
      isQueryBoundP_prgBits_zero (fun t => OtherCall (.inr t)) name key ρ idx count fun _ => id)

/-- The known streams of elements have only calls of `PRG`. -/
theorem knownStreams_elements_only (K : Constants C E) (D : C.Coalition) (receivers : Finset C.Party)
    (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (ρ idx count : ℕ) :
    OnlyStreams (liftComp (knownStreams D receivers (elementCodec K) term pair ρ idx count) (LocalSpec C)) :=
  isQueryBoundP_liftComp_ro OtherCall _ (knownStreams_zero (fun t => OtherCall (.inr t)) D receivers
    (elementCodec K) term pair ρ idx count fun name key => isQueryBoundP_bind (m := 0)
      (isQueryBoundP_prgBits_zero (fun t => OtherCall (.inr t)) name key ρ idx (elementBits * count) fun _ => id)
      fun _ _ => isQueryBoundP_pure _ _ 0)

end Streams

end ThresholdLeanXmssSecurity.RealNetworkE1b

end

end

section

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ThresholdLeanXmss

noncomputable section

namespace ThresholdLeanXmssSecurity.RealNetworkE1e

open RealNetworkE1s RealNetworkE1r RealNetworkE1g RealNetworkE1b RealNetworkE1o

attribute [local instance] Classical.propDecidable inhabitedField
attribute [local irreducible] MonadAttach.support

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E]

omit [Fintype E] [DecidableEq E] [SampleableType E] in
/-- The known rows over `E` of a check have only calls of `PRG`. -/
theorem knownRowsE_only (K : Constants C E) (D : C.Coalition) (live : Finset C.Party)
    (term : C.Term → HashOutput) (pair : C.Pair → HashOutput) (Lc count : ℕ) :
    OnlyStreams (knownRowsE K D live term pair Lc count) := by
  unfold knownRowsE OnlyStreams
  rw [isQueryBoundP_map_iff]
  simpa using queryBound_mapM (OtherCall (C := C)) (fun n =>
    liftComp (knownStreams D live (elementCodec K) term pair (Lc + n) (checkStream (halvings count) n) 2)
      (LocalSpec C))
    0 (List.range (RealNetworkV3.checkLabels count)) fun n _ =>
      knownStreams_elements_only K D live term pair (Lc + n) _ 2

omit [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] [SampleableType E] in
/-- The known row of the salts of a check has only calls of `PRG`. -/
theorem knownRowsB_only (D : C.Coalition) (live : Finset C.Party) (term : C.Term → HashOutput)
    (pair : C.Pair → HashOutput) (Lc count : ℕ) :
    OnlyStreams (knownRowsB (E := E) D live term pair Lc count) :=
  knownStreams_bits_only D live term pair _ 2 256

end ThresholdLeanXmssSecurity.RealNetworkE1e

end

end

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkCLp.prgBits_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkCLp.prgBits_frame

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkCLp.split_coinKey_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkCLp.split_coinKey_local

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkCLp.split_challenge_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkCLp.split_challenge_local

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkCLp.check_split_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkCLp.check_split_local

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkCLp.split_prgBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkCLp.split_prgBits

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkCLp.split_prss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkCLp.split_prss

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkCLp.split_prss_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkCLp.split_prss_bits

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkCLp.split_prss_elements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkCLp.split_prss_elements

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkCLp.split_reshare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkCLp.split_reshare

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkCLp.realCheck_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkCLp.realCheck_split

/-- info: 'ThresholdLeanXmssSecurity.RealNetworkE1b.OnlyStreams.fills' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.RealNetworkE1b.OnlyStreams.fills
