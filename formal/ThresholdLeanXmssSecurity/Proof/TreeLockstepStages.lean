import ThresholdLeanXmssSecurity.Proof.TreeEvents3
import ThresholdLeanXmssSecurity.Proof.TreeLockstep

/-!
# The salt draws of the honest digests

`compareDigests` hashes the salts that `randBits 256` draws just before it, with no exchange
between them. So each honest digest call of a round has the 256 draws of its salt in the same
round log.

* `DigestSafe seg p` states that each digest query of the program `p` before its next exchange
  has the draws of its salt in the segment `seg`, or in the queries of `p` before it.
* `digestSafeS_saltDigests` proves it for `randBits 256` and `compareDigests` together.
  `RoNoDigest` and `DigestSafeS` carry it through every other part of the ceremony.
* `digestSafe_ceremonyAfterSetup` proves it for the honest program after the PRSS setup.
* `worldDigestSafe_round` carries it to the log of one logged real round, and
  `digestSafe_reach` to every reachable configuration.
* `treeTwinDigestDrawsGoal` proves `TreeTwinDigestDrawsGoal`. It needs no collision guard.
* `treeTwinDigestGoal3_of_lockstepStages` gives `TreeTwinDigestGoal3` from
  `TreeLockstepStagesGoal` alone.

`TreeLockstepStagesGoal` stays open. It is not a fact of one operator. It needs the agreement of
the honest operators on the term keys of the PRSS setup (`TreeAgreementSetupKeys`) and on the
encoding of the second run (`TreeLockstepOpenedGoal`), and the label schedule of one operator on
partial runs, indexed by the round (`TreeLockstepRecordsRunGoal` gives it only on complete runs).
These three Props are stated on `treeSaltSetup` and on the audited logged run, so a bridge to
`TreeStagesReach` is also open. The budget domain holds `.sharedKeys`, `.copy`, `.history` and
`.digest`, so the guard excludes the collisions that break these agreements.
-/

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open scoped ENNReal

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-- The log `seg` holds the 256 draws of `salt` at one address. -/
def DigestDrawsIn (seg : TreeSimLog C) (salt : List Bit) : Prop :=
  ∃ (T : C.Term) (key : HashOutput) (label : ℕ), ∀ g : Fin 256,
    (⟨.inr (.inr (.inr (.term T, key, label, 2, g.val))), salt.getD g.val 0⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ seg

theorem DigestDrawsIn.mono {seg seg' : TreeSimLog C} {salt : List Bit} (h : DigestDrawsIn seg salt)
    (hs : ∀ x ∈ seg, x ∈ seg') : DigestDrawsIn seg' salt := by
  obtain ⟨T, key, label, hg⟩ := h
  exact ⟨T, key, label, fun g => hs _ (hg g)⟩

/-- Each digest query before the next exchange has the draws of its salt in the segment. The
segment holds the local queries since the last exchange, as entries of the free copy. -/
inductive DigestSafe {α : Type} :
    TreeSimLog C → OracleComp (PartySpec C E RealSpec) (Option α) → Prop
  | pure (seg : TreeSimLog C) (out : Option α) : DigestSafe seg (pure out)
  | queryLocal (seg : TreeSimLog C) (q : (LocalSpec C).Domain)
      (k : (LocalSpec C).Range q → OracleComp (PartySpec C E RealSpec) (Option α))
      (hq : ∀ salt hist, q = .inr (.inl (.digest salt hist)) → DigestDrawsIn seg salt)
      (h : ∀ r, DigestSafe (seg ++ [⟨.inr q, r⟩]) (k r)) :
      DigestSafe seg (.roll (.inl (.inl q)) k)
  | round (seg : TreeSimLog C) (out : Mail C E)
      (k : Mail C E → OracleComp (PartySpec C E RealSpec) (Option α))
      (h : ∀ r, DigestSafe [] (k r)) :
      DigestSafe seg (.roll (.inl (.inr out)) k)

theorem DigestSafe.mono {α : Type} {seg seg' : TreeSimLog C}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : DigestSafe seg p)
    (hs : ∀ x ∈ seg, x ∈ seg') : DigestSafe seg' p := by
  induction h generalizing seg' with
  | pure seg out => exact .pure seg' out
  | queryLocal seg q k hq h ih =>
    refine .queryLocal seg' q k (fun salt hist he => (hq salt hist he).mono hs) fun r => ih r ?_
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (hs x hx)
    · exact List.mem_append_right _ hx
  | round seg out k h ih => exact .round seg' out k h

theorem DigestSafe.of_nil {α : Type} {seg : TreeSimLog C}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : DigestSafe [] p) : DigestSafe seg p :=
  h.mono (by simp)

theorem DigestSafe.bind {α β : Type} {seg : TreeSimLog C}
    {p : PartyM C E RealSpec α} {k : α → PartyM C E RealSpec β}
    (hp : DigestSafe seg p.run) (hk : ∀ a, DigestSafe [] (k a).run) :
    DigestSafe seg (p >>= k).run := by
  simp only [OptionT.run_bind, Option.elimM]
  change DigestSafe seg (p.run >>= fun a => a.elim (Pure.pure none) (fun a => (k a).run))
  generalize p.run = oa at hp ⊢
  induction hp with
  | pure seg out =>
    cases out with
    | none => simpa only [pure_bind, Option.elim_none] using DigestSafe.pure seg (none : Option β)
    | some a => simpa only [pure_bind, Option.elim_some] using (hk a).of_nil
  | queryLocal seg q f hq hf ih =>
    change DigestSafe seg (.roll (.inl (.inl q)) _)
    exact DigestSafe.queryLocal seg q _ hq fun r => by
      simpa only [OracleComp.bind_def] using ih r
  | round seg out f hf ih =>
    change DigestSafe seg (.roll (.inl (.inr out)) _)
    exact DigestSafe.round seg out _ ih

/-- A local query. A digest query has the draws of its salt in the segment. -/
theorem DigestSafe.localQuery_bind {α : Type} {seg : TreeSimLog C} (q : (LocalSpec C).Domain)
    (k : (LocalSpec C).Range q → PartyM C E RealSpec α)
    (hq : ∀ salt hist, q = .inr (.inl (.digest salt hist)) → DigestDrawsIn seg salt)
    (hk : ∀ r, DigestSafe (seg ++ [⟨.inr q, r⟩]) (k r).run) :
    DigestSafe seg (localStep (OracleComp.lift (OracleSpec.query q)) >>= k).run := by
  simp only [localStep, OptionT.run_bind, OptionT.run_lift, Option.elimM,
    bind_assoc, pure_bind, Option.elim_some]
  change DigestSafe seg (liftComp (OracleComp.lift (OracleSpec.query q)) (PartySpec C E RealSpec) >>=
    fun a => (k a).run)
  simp only [liftComp_query]
  have hq' : ((OracleSpec.query q).cont <$> liftM (OracleSpec.query (OracleSpec.query q).input) :
      OracleComp (PartySpec C E RealSpec) _) =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inl q))) := by
    rw [← liftM_query_local]
    rfl
  rw [hq']
  exact DigestSafe.queryLocal seg q _ hq hk

/-- A local computation with no digest query keeps every safe continuation safe. -/
def LocalNoDigest {α : Type} (oa : OracleComp (LocalSpec C) α) : Prop :=
  ∀ (E β : Type) (seg : TreeSimLog C) (k : α → PartyM C E RealSpec β),
    (∀ a, DigestSafe seg (k a).run) → DigestSafe seg (localStep oa >>= k).run

theorem localStep_bind_bind {α β γ : Type} (oa : OracleComp (LocalSpec C) α)
    (f : α → OracleComp (LocalSpec C) β) (k : β → PartyM C E RealSpec γ) :
    localStep (oa >>= f) >>= k = localStep oa >>= fun a => localStep (f a) >>= k := by
  apply OptionT.ext
  simp [localStep, OptionT.run_bind, OptionT.run_lift, liftComp_bind]

theorem LocalNoDigest.pure {α : Type} (a : α) : LocalNoDigest (C := C) (Pure.pure a) := by
  intro E β seg k hk
  have : (localStep (Pure.pure a : OracleComp (LocalSpec C) α) >>= k : PartyM C E RealSpec β) = k a := by
    apply OptionT.ext
    simp [localStep]
  rw [this]
  exact hk a

theorem LocalNoDigest.bind {α β : Type} {oa : OracleComp (LocalSpec C) α}
    {f : α → OracleComp (LocalSpec C) β} (ha : LocalNoDigest oa) (hf : ∀ a, LocalNoDigest (f a)) :
    LocalNoDigest (oa >>= f) := by
  intro E γ seg k hk
  rw [localStep_bind_bind]
  exact ha E γ seg _ fun a => hf a E γ seg k hk

theorem LocalNoDigest.query (q : (LocalSpec C).Domain)
    (hq : ∀ salt hist, q ≠ .inr (.inl (.digest salt hist))) :
    LocalNoDigest (OracleComp.lift (OracleSpec.query q)) := by
  intro E β seg k hk
  exact DigestSafe.localQuery_bind q k (fun salt hist he => (hq salt hist he).elim)
    fun r => (hk r).mono fun x hx => List.mem_append_left _ hx

/-- A computation of `H` and `PRG` with no digest query. -/
def RoNoDigest {α : Type} (oa : OracleComp (RoSpec C) α) : Prop :=
  LocalNoDigest (liftComp oa (LocalSpec C))

theorem RoNoDigest.pure {α : Type} (a : α) : RoNoDigest (C := C) (Pure.pure a) := by
  unfold RoNoDigest
  rw [liftComp_pure]
  exact LocalNoDigest.pure a

theorem RoNoDigest.bind {α β : Type} {oa : OracleComp (RoSpec C) α}
    {f : α → OracleComp (RoSpec C) β} (ha : RoNoDigest oa) (hf : ∀ a, RoNoDigest (f a)) :
    RoNoDigest (oa >>= f) := by
  unfold RoNoDigest
  rw [liftComp_bind]
  exact LocalNoDigest.bind ha hf

theorem RoNoDigest.query (q : (RoSpec C).Domain)
    (hq : ∀ salt hist, q ≠ .inl (.digest salt hist)) :
    RoNoDigest (OracleComp.lift (OracleSpec.query q)) := by
  unfold RoNoDigest
  rw [liftComp_query]
  have : ((OracleSpec.query q).cont <$> liftM (OracleSpec.query (OracleSpec.query q).input) :
      OracleComp (LocalSpec C) _) = OracleComp.lift (OracleSpec.query (spec := LocalSpec C) (.inr q)) := rfl
  rw [this]
  exact LocalNoDigest.query (.inr q) fun salt hist he => hq salt hist (by cases he; rfl)

theorem RoNoDigest.map {α β : Type} {oa : OracleComp (RoSpec C) α} (f : α → β)
    (ha : RoNoDigest oa) : RoNoDigest (f <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact ha.bind fun _ => RoNoDigest.pure _

theorem RoNoDigest.mapM {α β : Type} (f : α → OracleComp (RoSpec C) β) (hf : ∀ a, RoNoDigest (f a)) :
    ∀ xs : List α, RoNoDigest (xs.mapM f)
  | [] => by simpa only [List.mapM_nil] using RoNoDigest.pure []
  | x :: xs => by
    simp only [List.mapM_cons]
    exact (hf x).bind fun _ => (RoNoDigest.mapM f hf xs).bind fun _ => RoNoDigest.pure _

theorem RoNoDigest.hashQuery (q : Query C) (hq : ∀ salt hist, q ≠ .digest salt hist) :
    RoNoDigest (hashQuery q) :=
  RoNoDigest.query (.inl q) fun salt hist he => hq salt hist (by cases he; rfl)

theorem RoNoDigest.prg (x : PrgInput C) :
    RoNoDigest (OracleComp.lift (OracleSpec.query (spec := RoSpec C) (.inr x))) :=
  RoNoDigest.query (.inr x) fun salt hist he => by cases he

theorem DigestSafe.oracle_bind {α β : Type} {seg : TreeSimLog C} {oa : OracleComp (RoSpec C) α}
    (ha : RoNoDigest oa) (k : α → PartyM C E RealSpec β) (hk : ∀ a, DigestSafe seg (k a).run) :
    DigestSafe seg (oracleStep oa >>= k).run :=
  ha E β seg k hk

theorem DigestSafe.require_bind {α : Type} {seg : TreeSimLog C} (P : Prop)
    (k : Unit → PartyM C E RealSpec α) (hk : DigestSafe seg (k ()).run) :
    DigestSafe seg (require P >>= k).run := by
  by_cases hP : P
  · simpa only [require, if_pos hP, pure_bind] using hk
  · simp only [require, if_neg hP, failure_bind]
    exact DigestSafe.pure seg none

set_option backward.isDefEq.respectTransparency false in
theorem DigestSafe.exchange_bind {α : Type} {seg : TreeSimLog C} (out : Mail C E)
    (k : Mail C E → PartyM C E RealSpec α) (hk : ∀ inbox, DigestSafe [] (k inbox).run) :
    DigestSafe seg (exchange out >>= k).run := by
  have he : (exchange out >>= k).run =
      OracleComp.lift (OracleSpec.query (spec := PartySpec C E RealSpec) (.inl (.inr out))) >>=
        exchangeResume k := by
    simp only [exchange, OptionT.run_bind, OptionT.lift, bind_assoc, OptionT.run_mk,
      pure_bind, Option.elimM]
    apply bind_congr
    intro inbox
    simp only [Option.elim]
    unfold exchangeResume
    split <;> simp_all
  rw [he]
  apply DigestSafe.round
  intro inbox
  change DigestSafe [] (exchangeResume k inbox)
  unfold exchangeResume
  split_ifs
  · exact DigestSafe.pure [] none
  · simpa only [OptionT.run_pure, pure_bind, Option.elim_some] using hk inbox

/-- A program of a state monad is safe from every state, after an exchange. -/
def DigestSafeS {σ α : Type} (p : StateT σ (PartyM C E RealSpec) α) : Prop :=
  ∀ s, DigestSafe [] (p.run s).run

theorem DigestSafeS.pure {σ α : Type} (a : α) :
    DigestSafeS (C := C) (E := E) (Pure.pure a : StateT σ (PartyM C E RealSpec) α) := by
  intro s
  simp only [StateT.run_pure, OptionT.run_pure]
  exact DigestSafe.pure [] _

theorem DigestSafeS.bind {σ α β : Type} {p : StateT σ (PartyM C E RealSpec) α}
    {k : α → StateT σ (PartyM C E RealSpec) β} (hp : DigestSafeS p) (hk : ∀ a, DigestSafeS (k a)) :
    DigestSafeS (p >>= k) := by
  intro s
  rw [StateT.run_bind]
  exact (hp s).bind fun a => hk a.1 a.2

theorem DigestSafeS.lift {σ α : Type} {p : PartyM C E RealSpec α} (hp : DigestSafe [] p.run) :
    DigestSafeS (StateT.lift p : StateT σ (PartyM C E RealSpec) α) := by
  intro s
  rw [StateT.run_lift]
  exact hp.bind fun _ => DigestSafe.pure [] _

theorem DigestSafeS.oracle {σ α : Type} {oa : OracleComp (RoSpec C) α} (ha : RoNoDigest oa) :
    DigestSafeS (StateT.lift (oracleStep oa) : StateT σ (PartyM C E RealSpec) α) := by
  apply DigestSafeS.lift
  rw [← bind_pure (oracleStep oa)]
  exact DigestSafe.oracle_bind ha _ fun _ => DigestSafe.pure [] _

theorem DigestSafeS.get {σ : Type} :
    DigestSafeS (C := C) (E := E) (MonadState.get : StateT σ (PartyM C E RealSpec) σ) := by
  intro s
  exact DigestSafe.pure [] _

theorem DigestSafeS.set {σ : Type} (t : σ) :
    DigestSafeS (C := C) (E := E) (MonadStateOf.set t : StateT σ (PartyM C E RealSpec) PUnit) := by
  intro s
  exact DigestSafe.pure [] _

theorem DigestSafeS.foldlM {σ α β : Type} (f : α → β → StateT σ (PartyM C E RealSpec) α)
    (hf : ∀ a b, DigestSafeS (f a b)) (xs : List β) (a : α) : DigestSafeS (xs.foldlM f a) := by
  induction xs generalizing a with
  | nil => simpa only [List.foldlM_nil] using DigestSafeS.pure a
  | cons b xs ih =>
    simp only [List.foldlM_cons]
    exact (hf a b).bind fun a' => ih a'

theorem DigestSafeS.mapM {σ β γ : Type} (f : β → StateT σ (PartyM C E RealSpec) γ)
    (hf : ∀ b, DigestSafeS (f b)) : ∀ xs : List β, DigestSafeS (xs.mapM f)
  | [] => by simpa only [List.mapM_nil] using DigestSafeS.pure []
  | x :: xs => by
    simp only [List.mapM_cons]
    exact (hf x).bind fun _ => (DigestSafeS.mapM f hf xs).bind fun _ => DigestSafeS.pure _

theorem digestSafe_mapM {β γ : Type} (f : β → PartyM C E RealSpec γ)
    (hf : ∀ b, DigestSafe [] (f b).run) : ∀ xs : List β, DigestSafe [] (xs.mapM f).run
  | [] => by simpa only [List.mapM_nil, OptionT.run_pure] using DigestSafe.pure [] (some [])
  | x :: xs => by
    simp only [List.mapM_cons]
    exact (hf x).bind fun _ => (digestSafe_mapM f hf xs).bind fun _ => by
      simpa only [OptionT.run_pure] using DigestSafe.pure [] _

section Programs

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (K : Constants C E)

theorem roNoDigest_prgBits (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    RoNoDigest (prgBits name key ρ idx count) := by
  unfold prgBits
  refine (RoNoDigest.mapM _ (fun position => ?_) _).bind fun _ => RoNoDigest.pure _
  exact RoNoDigest.prg (name, key, ρ, idx, position)

theorem roNoDigest_draw_bit (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    RoNoDigest ((bitCodec (C := C) (E := E)).draw name key ρ idx count) := by
  simp only [bitCodec]
  exact roNoDigest_prgBits name key ρ idx count

theorem roNoDigest_draw_element (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    RoNoDigest ((elementCodec K).draw name key ρ idx count) :=
  (roNoDigest_prgBits name key ρ idx _).bind fun _ => RoNoDigest.pure _

theorem roNoDigest_prssDraw {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R)
    (hcodec : ∀ name key ρ idx count, RoNoDigest (codec.draw name key ρ idx count)) (ρ idx count : ℕ) :
    RoNoDigest (prssDraw ctx codec ρ idx count) := by
  unfold prssDraw termDraws pairDraws
  refine (RoNoDigest.mapM _ (fun T => ?_) _).bind fun _ =>
    (RoNoDigest.mapM _ (fun j => ?_) _).bind fun _ => RoNoDigest.pure _
  · split_ifs
    · exact hcodec _ _ _ _ _
    · exact RoNoDigest.pure _
  · split_ifs
    · exact RoNoDigest.pure _
    · exact hcodec _ _ _ _ _

theorem roNoDigest_tweakable {α : Type} (oa : OracleComp HashSpec α) :
    RoNoDigest (C := C) (tweakable oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa only [tweakable, simulateQ_pure] using RoNoDigest.pure a
  | query_bind q f ih =>
    simp only [tweakable, simulateQ_bind, simulateQ_spec_query] at ih ⊢
    exact (RoNoDigest.hashQuery _ fun _ _ h => by cases h).bind ih

theorem roNoDigest_findChallenge (key : HashOutput) :
    ∀ tries index, RoNoDigest (findChallenge K key tries index)
  | 0, _ => RoNoDigest.pure _
  | tries + 1, index => by
    unfold findChallenge
    refine (RoNoDigest.hashQuery _ fun _ _ h => by cases h).bind fun r => ?_
    dsimp only
    split
    · exact RoNoDigest.pure _
    · exact roNoDigest_findChallenge key tries (index + 1)

theorem digestSafe_exchange (out : Mail C E) : DigestSafe [] (exchange (G := RealSpec) out).run := by
  rw [← bind_pure (exchange out)]
  exact DigestSafe.exchange_bind out _ fun _ => DigestSafe.pure [] _

theorem digestSafeS_prssRandomness {R : Type} [Zero R] (ctx : Context C) (codec : Codec C E R)
    (hcodec : ∀ name key ρ idx count, RoNoDigest (codec.draw name key ρ idx count)) (idx count : ℕ) :
    DigestSafeS (prssRandomness (G := RealSpec) ctx codec idx count) := by
  intro st
  have h := prssRandomness_run (G := RealSpec) ctx codec idx count pure st
  rw [bind_pure] at h
  rw [h]
  exact DigestSafe.oracle_bind (roNoDigest_prssDraw ctx codec hcodec _ _ _) _ fun _ =>
    DigestSafe.pure [] _

theorem digestSafeS_record {R : Type} (ctx : Context C) (codec : Codec C E R) (mode : ReshareMode)
    (z : Shares C R) (count : ℕ) : DigestSafeS (record (G := RealSpec) K ctx codec mode z count) := by
  intro st
  exact DigestSafe.pure [] _

theorem digestSafeS_reshare {R : Type} [Field R] (ctx : Context C) (codec : Codec C E R)
    (randomness : PrssOutput C R) (v : ℕ → R) (count : ℕ) :
    DigestSafeS (reshare (G := RealSpec) K ctx codec randomness v count) := by
  unfold reshare
  exact (DigestSafeS.lift (digestSafe_exchange _)).bind fun _ =>
    (digestSafeS_record K ctx codec _ _ _).bind fun _ => DigestSafeS.pure _

theorem digestSafeS_reshareCollector (ctx : Context C) (randomness : PrssOutput C Bit)
    (v : ℕ → Bit) (count : ℕ) :
    DigestSafeS (reshareCollector (G := RealSpec) K ctx randomness v count) := by
  unfold reshareCollector
  exact (DigestSafeS.lift (digestSafe_exchange _)).bind fun _ =>
    (DigestSafeS.lift (digestSafe_exchange _)).bind fun _ =>
      (digestSafeS_record K ctx bitCodec _ _ _).bind fun _ => DigestSafeS.pure _

theorem digestSafe_openSh (ctx : Context C) (v : ℕ → E) (count : ℕ) :
    DigestSafe [] (openSh (G := RealSpec) K ctx v count).run := by
  unfold openSh
  exact DigestSafe.exchange_bind _ _ fun _ => DigestSafe.require_bind _ _ (DigestSafe.pure [] _)

theorem digestSafe_openRep (ctx : Context C) (v : Shares C Bit) (count : ℕ) :
    DigestSafe [] (openRep (G := RealSpec) K ctx v count).run := by
  unfold openRep
  exact DigestSafe.oracle_bind
    (RoNoDigest.mapM _ (fun _ => RoNoDigest.hashQuery _ fun _ _ h => by cases h) _) _ fun _ =>
    DigestSafe.exchange_bind _ _ fun _ => DigestSafe.oracle_bind
      (RoNoDigest.mapM _ (fun _ => RoNoDigest.hashQuery _ fun _ _ h => by cases h) _) _ fun _ =>
      DigestSafe.require_bind _ _ (DigestSafe.pure [] _)

theorem digestSafeS_coin (ctx : Context C) (count : ℕ) :
    DigestSafeS ((realCheckGadgets (G := RealSpec) K ctx).coin count) := by
  change DigestSafeS (prssRandomness ctx (elementCodec K) 1 count >>= fun o => coinWith K ctx o count)
  refine (digestSafeS_prssRandomness ctx _ (roNoDigest_draw_element K) _ _).bind fun o => ?_
  unfold coinWith
  exact (DigestSafeS.lift (digestSafe_openSh K ctx _ _)).bind fun _ => DigestSafeS.pure _

theorem digestSafeS_coinKey (ctx : Context C) :
    DigestSafeS (coinKey K (realCheckGadgets (G := RealSpec) K ctx)) := by
  unfold coinKey
  exact DigestSafeS.get.bind fun _ => (digestSafeS_coin K ctx 1).bind fun _ =>
    DigestSafeS.oracle (RoNoDigest.hashQuery _ fun _ _ h => by cases h)

theorem digestSafeS_challenge (ctx : Context C) :
    DigestSafeS (challenge K (realCheckGadgets (G := RealSpec) K ctx)) := by
  unfold challenge
  refine (digestSafeS_coinKey K ctx).bind fun key => ?_
  refine (DigestSafeS.oracle (roNoDigest_findChallenge K key _ _)).bind fun r => ?_
  intro s
  cases r with
  | none =>
    simp only [StateT.run_lift, failure_bind]
    exact DigestSafe.pure [] none
  | some r =>
    simp only [StateT.run_pure, OptionT.run_pure]
    exact DigestSafe.pure [] _

theorem digestSafeS_expand (key : HashOutput) (count : ℕ) :
    DigestSafeS (expand (G := RealSpec) K key count) := by
  unfold expand
  exact DigestSafeS.oracle (RoNoDigest.mapM _ (fun _ =>
    (RoNoDigest.hashQuery _ fun _ _ h => by cases h).map _) _)

theorem digestSafeS_extendMult (ctx : Context C) (products : List (Product C E)) :
    DigestSafeS ((realCheckGadgets (G := RealSpec) K ctx).extendMult products) := by
  change DigestSafeS (prssRandomness ctx (elementCodec K) 0 products.length >>= fun rnd =>
    reshare K ctx (elementCodec K) rnd _ products.length)
  exact (digestSafeS_prssRandomness ctx _ (roNoDigest_draw_element K) _ _).bind fun _ =>
    digestSafeS_reshare K ctx _ _ _ _

theorem DigestSafe.prg_bind {α : Type} {seg : TreeSimLog C} (x : PrgInput C)
    (k : Bit → PartyM C E RealSpec α)
    (hk : ∀ b, DigestSafe (seg ++ [⟨.inr (.inr (.inr x)), b⟩]) (k b).run) :
    DigestSafe seg (oracleStep (query (spec := RoSpec C) (.inr x) : OracleComp (RoSpec C) Bit) >>= k).run := by
  change DigestSafe seg (localStep (OracleComp.lift
    (OracleSpec.query (spec := LocalSpec C) (.inr (.inr x)))) >>= k).run
  exact DigestSafe.localQuery_bind (.inr (.inr x)) k (fun _ _ h => by cases h) hk

/-- The draws of the bits at the positions `xs` are in the log, with their answers. -/
theorem DigestSafe.prgBits_bind {α : Type} (name : KeyName C) (key : HashOutput) (ρ idx : ℕ) :
    ∀ (xs : List ℕ) (seg : TreeSimLog C) (k : List Bit → PartyM C E RealSpec α),
    (∀ bits seg', (∀ x ∈ seg, x ∈ seg') → bits.length = xs.length →
      (∀ j (hj : j < xs.length), (⟨.inr (.inr (.inr (name, key, ρ, idx, xs[j]))), bits.getD j 0⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ seg') →
      DigestSafe seg' (k bits).run) →
    DigestSafe seg (oracleStep (xs.mapM fun position =>
      (query (spec := RoSpec C) (.inr (name, key, ρ, idx, position)) : OracleComp (RoSpec C) Bit)) >>= k).run
  | [], seg, k, hk => by
    simp only [List.mapM_nil, oracleStep_pure, pure_bind]
    exact hk [] seg (fun _ h => h) rfl fun j hj => (Nat.not_lt_zero j hj).elim
  | x :: xs, seg, k, hk => by
    simp only [List.mapM_cons, oracleStep_bind, bind_assoc, oracleStep_pure, pure_bind]
    refine DigestSafe.prg_bind _ _ fun b => ?_
    refine DigestSafe.prgBits_bind name key ρ idx xs _ _ fun bits seg' hseg hlen hdraw => ?_
    refine hk (b :: bits) seg' (fun y hy => hseg y (List.mem_append_left _ hy))
      (by simp [hlen]) fun j hj => ?_
    cases j with
    | zero => exact hseg _ (List.mem_append_right _ (List.mem_singleton_self _))
    | succ j =>
      simpa using hdraw j (by simpa using hj)

/-- The salt draws of the held terms are in the log, with their answers. -/
theorem DigestSafe.termDraws_bind {α : Type} (ctx : Context C) (ρ : ℕ) :
    ∀ (ts : List C.Term) (seg : TreeSimLog C) (k : List (ℕ → Bit) → PartyM C E RealSpec α),
    (∀ r seg', (∀ x ∈ seg, x ∈ seg') →
      (∀ i (hi : i < ts.length), ctx.self ∈ C.holders ts[i] → ∀ g < 256,
        (⟨.inr (.inr (.inr (.term ts[i], ctx.prss.term ts[i], ρ, 2, g))), (r.getD i fun _ => 0) g⟩ :
          (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ seg') →
      DigestSafe seg' (k r).run) →
    DigestSafe seg (oracleStep (ts.mapM fun T => if ctx.self ∈ C.holders T then
      (bitCodec (C := C) (E := E)).draw (.term T) (ctx.prss.term T) ρ 2 256
      else (Pure.pure fun _ => 0 : OracleComp (RoSpec C) (ℕ → Bit))) >>= k).run
  | [], seg, k, hk => by
    simp only [List.mapM_nil, oracleStep_pure, pure_bind]
    exact hk [] seg (fun _ h => h) fun i hi => (Nat.not_lt_zero i hi).elim
  | T :: ts, seg, k, hk => by
    simp only [List.mapM_cons, oracleStep_bind, bind_assoc, oracleStep_pure, pure_bind]
    by_cases hT : ctx.self ∈ C.holders T
    · simp only [if_pos hT, bitCodec, prgBits, oracleStep_bind, bind_assoc, oracleStep_pure, pure_bind]
      refine DigestSafe.prgBits_bind _ _ _ _ _ _ _ fun bits seg₁ hseg₁ hlen hdraw => ?_
      refine DigestSafe.termDraws_bind ctx ρ ts _ _ fun r seg' hseg hr => ?_
      refine hk _ seg' (fun y hy => hseg y (hseg₁ y hy)) fun i hi hheld g hg => ?_
      cases i with
      | zero =>
        have hg' : g < (List.range 256).length := by simpa using hg
        have h := hseg _ (hdraw g hg')
        have move : ∀ m, m = g →
            (⟨.inr (.inr (.inr (.term T, ctx.prss.term T, ρ, 2, m))), bits.getD g 0⟩ :
              (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ seg' →
            (⟨.inr (.inr (.inr (.term T, ctx.prss.term T, ρ, 2, g))), bits.getD g 0⟩ :
              (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ seg' := by
          rintro m rfl hm
          exact hm
        exact move _ (List.getElem_range hg') h
      | succ i => simpa using hr i (by simpa using hi) (by simpa using hheld) g hg
    · simp only [if_neg hT, oracleStep_pure, pure_bind]
      refine DigestSafe.termDraws_bind ctx ρ ts _ _ fun r seg' hseg hr => ?_
      refine hk _ seg' hseg fun i hi hheld g hg => ?_
      cases i with
      | zero => exact (hT (by simpa using hheld)).elim
      | succ i => simpa using hr i (by simpa using hi) (by simpa using hheld) g hg

theorem DigestSafe.hash_bind {α : Type} {seg : TreeSimLog C} (q : Query C)
    (k : HashOutput → PartyM C E RealSpec α)
    (hq : ∀ salt hist, q = .digest salt hist → DigestDrawsIn seg salt)
    (hk : ∀ h, DigestSafe (seg ++ [⟨.inr (.inr (.inl q)), h⟩]) (k h).run) :
    DigestSafe seg (oracleStep (hashQuery q) >>= k).run := by
  change DigestSafe seg (localStep (OracleComp.lift
    (OracleSpec.query (spec := LocalSpec C) (.inr (.inl q)))) >>= k).run
  exact DigestSafe.localQuery_bind (.inr (.inl q)) k
    (fun salt hist he => hq salt hist (by cases he; rfl)) hk

/-- The digest queries of the held terms, whose salts have their draws in the log. -/
theorem DigestSafe.digests_bind {α : Type} (i : C.Party) (salts : Shares C Bit)
    (h : C.Term → List Bit) :
    ∀ (ts : List C.Term) (seg : TreeSimLog C) (k : List HashOutput → PartyM C E RealSpec α),
    (∀ T ∈ ts, i ∈ C.holders T → DigestDrawsIn seg (vector 256 (salts T))) →
    (∀ ds, DigestSafe seg (k ds).run) →
    DigestSafe seg (oracleStep (ts.mapM fun T => if i ∈ C.holders T then do
      hashQuery (.digest (vector 256 (salts T)) (← hashQuery (.history (h T)))) else Pure.pure 0) >>= k).run
  | [], seg, k, _, hk => by
    simp only [List.mapM_nil, oracleStep_pure, pure_bind]
    exact hk []
  | T :: ts, seg, k, hd, hk => by
    simp only [List.mapM_cons, oracleStep_bind, bind_assoc, oracleStep_pure, pure_bind]
    have hrest : ∀ d, DigestSafe seg (oracleStep (ts.mapM fun T => if i ∈ C.holders T then do
        hashQuery (.digest (vector 256 (salts T)) (← hashQuery (.history (h T)))) else Pure.pure 0) >>=
          fun ds => k (d :: ds)).run := fun d =>
      DigestSafe.digests_bind i salts h ts seg _ (fun T' hT' => hd T' (List.mem_cons_of_mem _ hT'))
        fun ds => hk _
    by_cases hT : i ∈ C.holders T
    · simp only [if_pos hT, oracleStep_bind, bind_assoc]
      refine DigestSafe.hash_bind _ _ (fun _ _ he => by cases he) fun hist => ?_
      refine DigestSafe.hash_bind _ _ (fun salt hist' he => ?_) fun d => ?_
      · cases he
        exact (hd T List.mem_cons_self hT).mono fun x hx => List.mem_append_left _ hx
      · exact (hrest d).mono fun x hx => List.mem_append_left _ (List.mem_append_left _ hx)
    · simp only [if_neg hT, oracleStep_pure, pure_bind]
      exact hrest 0

theorem DigestSafe.digestQuery_bind {α : Type} {seg : TreeSimLog C} (i : C.Party)
    (salts : Shares C Bit) (h : C.Term → List Bit) (k : List HashOutput → PartyM C E RealSpec α)
    (hd : ∀ T, i ∈ C.holders T → DigestDrawsIn seg (vector 256 (salts T)))
    (hk : ∀ ds, DigestSafe seg (k ds).run) :
    DigestSafe seg (oracleStep (digestQuery i salts h) >>= k).run :=
  DigestSafe.digests_bind i salts h C.terms seg k (fun T _ => hd T) hk

theorem digestDrawsIn_vector {seg : TreeSimLog C} (T : C.Term) (key : HashOutput) (ρ : ℕ)
    (f : ℕ → Bit)
    (h : ∀ g < 256, (⟨.inr (.inr (.inr (.term T, key, ρ, 2, g))), f g⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ seg) :
    DigestDrawsIn seg (vector 256 f) := by
  refine ⟨T, key, ρ, fun g => ?_⟩
  have hv : (vector 256 f).getD g.val 0 = f g.val := by
    simp [vector, List.getD_eq_getElem?_getD, g.isLt]
  rw [hv]
  exact h g.val g.isLt

/-- `randBits 256` and `compareDigests` run in one local step. Each digest query hashes the salt
of a held term, and the draws of that salt are in the same segment. -/
theorem digestSafeS_saltDigests (ctx : Context C) {β : Type} (k : Unit → RunM C E RealSpec β)
    (hk : ∀ u, DigestSafeS (k u)) :
    DigestSafeS ((realCheckGadgets (G := RealSpec) K ctx).randBits 256 >>= fun salts =>
      compareDigests ctx salts.1 >>= k) := by
  intro st
  change DigestSafe [] ((prssRandomness ctx bitCodec 2 256 >>= fun salts =>
    compareDigests ctx salts.1 >>= k).run st).run
  rw [prssRandomness_run]
  unfold prssDraw termDraws
  simp only [oracleStep_bind, bind_assoc, oracleStep_pure, pure_bind]
  refine DigestSafe.termDraws_bind ctx st.label C.terms [] _ fun r seg' _ hr => ?_
  have hpair : RoNoDigest (pairDraws ctx (bitCodec (C := C) (E := E)) st.label 2 256) := by
    unfold pairDraws
    refine RoNoDigest.mapM _ (fun j => ?_) _
    split_ifs
    · exact RoNoDigest.pure _
    · exact roNoDigest_draw_bit _ _ _ _ _
  refine DigestSafe.oracle_bind hpair _ fun Z => ?_
  rw [StateT.run_bind, compareDigests_run]
  simp only [bind_assoc]
  refine DigestSafe.digestQuery_bind _ _ _ _ (fun T hT => ?_) fun ds => ?_
  · have hi : C.terms.idxOf T < C.terms.length := List.idxOf_lt_length_of_mem (mem_terms T)
    have hget : C.terms[C.terms.idxOf T] = T := List.getElem_idxOf hi
    have h := hr _ hi (by rw [hget]; exact hT)
    rw [hget] at h
    exact digestDrawsIn_vector T _ _ _ h
  · refine DigestSafe.exchange_bind _ _ fun inbox => ?_
    refine DigestSafe.require_bind _ _ ?_
    simpa only [pure_bind] using hk () (nextLabel st)

theorem digestSafeS_check (ctx : Context C) (tuples : List (Tuple C)) :
    DigestSafeS (check K ctx (realCheckGadgets (G := RealSpec) K ctx) tuples) := by
  unfold check
  dsimp only
  split_ifs with hzero
  · exact DigestSafeS.pure _
  refine (DigestSafeS.pure _).bind fun _ => ?_
  refine (digestSafeS_coinKey K ctx).bind fun key => ?_
  refine (digestSafeS_expand K key _).bind fun τ => ?_
  refine (DigestSafeS.lift (by
    rw [← bind_pure (require _)]
    exact DigestSafe.require_bind _ _ (DigestSafe.pure [] _))).bind fun _ => ?_
  refine (DigestSafeS.foldlM _ (fun x j => (digestSafeS_extendMult K ctx _).bind fun t =>
    (digestSafeS_challenge K ctx).bind fun r => DigestSafeS.pure _) _ _).bind fun x => ?_
  refine (DigestSafeS.foldlM _ (fun x j => (digestSafeS_extendMult K ctx _).bind fun t =>
    (digestSafeS_challenge K ctx).bind fun r => DigestSafeS.pure _) _ _).bind fun y => ?_
  refine (digestSafeS_prssRandomness ctx _ (roNoDigest_draw_element K) _ _).bind fun w => ?_
  refine (digestSafeS_extendMult K ctx _).bind fun q => ?_
  refine digestSafeS_saltDigests K ctx _ fun _ => ?_
  refine (digestSafeS_challenge K ctx).bind fun r => ?_
  refine (DigestSafeS.lift (digestSafe_openSh K ctx _ _)).bind fun opened => ?_
  exact DigestSafeS.lift (by
    rw [← bind_pure (require _)]
    exact DigestSafe.require_bind _ _ (DigestSafe.pure [] _))

theorem roNoDigest_flatMapM {α β : Type} (f : α → OracleComp (RoSpec C) (List β))
    (hf : ∀ a, RoNoDigest (f a)) : ∀ xs : List α, RoNoDigest (xs.flatMapM f)
  | xs => by
    have loop : ∀ (ys : List α) (acc : List (List β)), RoNoDigest (List.flatMapM.loop f ys acc) := by
      intro ys
      induction ys with
      | nil => intro acc; exact RoNoDigest.pure _
      | cons y ys ih => intro acc; exact (hf y).bind fun _ => ih _
    exact loop xs []

theorem digestSafe_inputShares (ctx : Context C) (job : Job) :
    DigestSafe [] (inputShares (E := E) (G := RealSpec) ctx job).run := by
  unfold inputShares
  refine DigestSafe.oracle_bind (RoNoDigest.mapM _ (fun T => ?_) _) _ fun _ => DigestSafe.pure [] _
  split_ifs
  · exact roNoDigest_flatMapM _ (fun x =>
      ((RoNoDigest.hashQuery _ fun _ _ h => by cases h).map _).map _) _
  · exact RoNoDigest.pure _

theorem digestSafeS_runJobs (ctx : Context C) (mode : ReshareMode) (jobs : List Circuit)
    (inputs : List (C.Term → List Bit)) :
    DigestSafeS (runJobs K (realRunGadgets (G := RealSpec) K ctx mode) jobs inputs) := by
  unfold runJobs
  refine (DigestSafeS.foldlM _ (fun x layer => ?_) _ _).bind fun x => ?_
  · refine ((digestSafeS_prssRandomness ctx _ (roNoDigest_draw_bit) _ _).bind fun rnd => ?_).bind
      fun z => DigestSafeS.pure _
    cases mode with
    | peer => exact digestSafeS_reshare K ctx _ _ _ _
    | collector => exact digestSafeS_reshareCollector K ctx _ _ _
  · refine ((digestSafeS_prssRandomness ctx _ (roNoDigest_draw_bit) _ _).bind fun rnd =>
      digestSafeS_reshare K ctx _ _ _ _).bind fun v' => ?_
    refine (digestSafeS_check K ctx _).bind fun _ => ?_
    exact (DigestSafeS.lift (digestSafe_openRep K ctx _ _)).bind fun _ => DigestSafeS.pure _

variable (circuits : Circuits) (settings : Settings)

theorem digestSafeS_ceremonyBatch (ctx : Context C) (jobs : List Job) :
    DigestSafeS (ceremonyBatch (G := RealSpec) K circuits settings ctx jobs) := by
  unfold ceremonyBatch
  refine DigestSafeS.get.bind fun x => ?_
  obtain ⟨label, k⟩ := x
  refine (DigestSafeS.lift (digestSafe_mapM _ (digestSafe_inputShares ctx) jobs)).bind
    fun inputs => ?_
  refine (DigestSafeS.lift (digestSafeS_runJobs K ctx _ _ inputs _)).bind fun y => ?_
  obtain ⟨outputs, state⟩ := y
  exact (DigestSafeS.set _).bind fun _ => DigestSafeS.pure _

theorem digestSafeS_batched (ctx : Context C) (js : List Job) :
    DigestSafeS (batched settings.batchSize (ceremonyBatch K circuits settings ctx) js :
      StateT (ℕ × ℕ) (PartyM C E RealSpec) _) := by
  unfold batched
  exact (DigestSafeS.mapM _ (digestSafeS_ceremonyBatch K circuits settings ctx) _).bind fun _ =>
    DigestSafeS.pure _

theorem digestSafeS_ceremonyOutput (ctx : Context C) (top : TopTree) (tree : Tree) :
    DigestSafeS (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
      (fun oa => StateT.lift (oracleStep (tweakable oa))) ctx.keys.parameter
      (batched settings.batchSize (ceremonyBatch K circuits settings ctx)) top tree) := by
  have hlift : ∀ {α : Type} (oa : OracleComp HashSpec α),
      DigestSafeS (StateT.lift (oracleStep (tweakable oa)) :
        StateT (ℕ × ℕ) (PartyM C E RealSpec) α) :=
    fun oa => DigestSafeS.oracle (roNoDigest_tweakable oa)
  cases tree with
  | top =>
    simp only [ceremonyOutput]
    refine (digestSafeS_batched K circuits settings ctx _).bind fun r => ?_
    cases r with
    | none => exact DigestSafeS.pure _
    | some outputs => exact (hlift _).bind fun _ => DigestSafeS.pure _
  | bottom b =>
    simp only [ceremonyOutput]
    refine (digestSafeS_batched K circuits settings ctx _).bind fun r => ?_
    cases r with
    | none => exact DigestSafeS.pure _
    | some outputs =>
      refine (hlift _).bind fun root => (hlift _).bind fun base => (hlift _).bind fun g => ?_
      rcases g with _ | ⟨randomness, encoding⟩
      · exact DigestSafeS.pure _
      refine (digestSafeS_batched K circuits settings ctx _).bind fun v => ?_
      rcases v with _ | values
      · exact DigestSafeS.pure _
      refine (hlift _).bind fun path => (hlift _).bind fun root' => ?_
      split_ifs
      · exact DigestSafeS.pure _
      · exact DigestSafeS.pure _

/-- The honest program after the PRSS setup is safe. -/
theorem digestSafe_ceremonyAfterSetup (ctx : Context C) (top : TopTree) (tree : Tree) :
    DigestSafe [] (ceremonyAfterSetup K circuits settings ctx top tree :
      PartyM C E RealSpec TreeOutput).run := by
  unfold ceremonyAfterSetup
  refine DigestSafe.bind ?_ fun o => ?_
  · rw [StateT.run'_eq, map_eq_bind_pure_comp]
    exact (digestSafeS_ceremonyOutput K circuits settings ctx top tree (0, 0)).bind fun _ =>
      DigestSafe.pure [] _
  · cases o with
    | none => exact DigestSafe.pure [] none
    | some output => exact DigestSafe.pure [] _

end Programs

section World

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E] (prims : Primitives) (D : C.Coalition)

/-- A suspended honest step whose resumption is safe after the exchange. -/
def DigestSafeStep {α : Type} : Step C E RealSpec α → Prop
  | .done _ => True
  | .wait _ resume => ∀ inbox, DigestSafe [] (resume inbox)
  | .call input _ => input.elim

theorem DigestSafe.advance_mem {α : Type} {seg : TreeSimLog C}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : DigestSafe seg p) :
    ∀ step ∈ support (advance p), DigestSafeStep step := by
  induction h with
  | pure seg out =>
    intro step hs
    change step ∈ support (Pure.pure (.done out) : OracleComp (LocalSpec C) (Step C E RealSpec α)) at hs
    have he : step = .done out := by simpa using hs
    subst step
    trivial
  | queryLocal seg q k hq h ih =>
    intro step hs
    obtain ⟨r, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hs
    exact ih r step hr
  | round seg out k h ih =>
    intro step hs
    have he : step = .wait out k := by simpa [advance] using hs
    subst step
    exact h

/-- Each honest digest entry that a run of `p` appends to the log has the draws of its salt in
`seg` or in the appended log. -/
def WorldDigestSafe {β : Type} (seg : TreeSimLog C) (p : OracleComp (WorldSpec C) β) : Prop :=
  ∀ (s : TreeSimState C) r, r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s) →
    ∃ l, r.2.2 = s.2 ++ l ∧ ∀ salt hist answer,
      (⟨.inr (.inr (.inl (.digest salt hist))), answer⟩ :
        (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ l → DigestDrawsIn (seg ++ l) salt

theorem WorldDigestSafe.pure {β : Type} (seg : TreeSimLog C) (b : β) :
    WorldDigestSafe prims D seg (Pure.pure b) := by
  intro s r hr
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
  subst r
  exact ⟨[], by simp, fun _ _ _ h => by simp at h⟩

theorem WorldDigestSafe.bind {β γ : Type} {seg : TreeSimLog C} {p : OracleComp (WorldSpec C) β}
    {k : β → OracleComp (WorldSpec C) γ} (hp : WorldDigestSafe prims D seg p)
    (hk : ∀ b, WorldDigestSafe prims D [] (k b)) : WorldDigestSafe prims D seg (p >>= k) := by
  intro s r hr
  rw [simulateQ_bind, StateT.run_bind] at hr
  obtain ⟨x, hx, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  obtain ⟨l₁, hl₁, h₁⟩ := hp s x hx
  obtain ⟨l₂, hl₂, h₂⟩ := hk x.1 x.2 r hr
  refine ⟨l₁ ++ l₂, by rw [hl₂, hl₁, List.append_assoc], fun salt hist answer hmem => ?_⟩
  rcases List.mem_append.mp hmem with hm | hm
  · exact (h₁ salt hist answer hm).mono fun y hy => by
      rcases List.mem_append.mp hy with hy | hy
      · exact List.mem_append_left _ hy
      · exact List.mem_append_right _ (List.mem_append_left _ hy)
  · exact (h₂ salt hist answer hm).mono fun y hy => by
      rcases List.mem_append.mp hy with hy | hy
      · simp at hy
      · exact List.mem_append_right _ (List.mem_append_right _ hy)

theorem WorldDigestSafe.query_bind {β : Type} {seg : TreeSimLog C} (t : (WorldSpec C).Domain)
    (k : (WorldSpec C).Range t → OracleComp (WorldSpec C) β)
    (ht : ∀ salt hist, t = .inr (.inr (.inl (.digest salt hist))) → DigestDrawsIn seg salt)
    (hk : ∀ u, WorldDigestSafe prims D (seg ++ [⟨t, u⟩]) (k u)) :
    WorldDigestSafe prims D seg (OracleComp.lift (OracleSpec.query t) >>= k) := by
  intro s r hr
  rw [simulateQ_bind, StateT.run_bind] at hr
  obtain ⟨x, hx, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  have hx' : x ∈ support ((treeSimLoggedWorld prims D t).run s) := by simpa using hx
  simp only [treeSimLoggedWorld, StateT.run_mk, support_map, Set.mem_image] at hx'
  obtain ⟨y, _, rfl⟩ := hx'
  obtain ⟨l, hl, h⟩ := hk y.1 _ r hr
  refine ⟨⟨t, y.1⟩ :: l, by rw [hl]; simp, fun salt hist answer hmem => ?_⟩
  rcases List.mem_cons.mp hmem with he | hm
  · have ht' : t = .inr (.inr (.inl (.digest salt hist))) := (congrArg Sigma.fst he).symm
    exact (ht salt hist ht').mono fun z hz => List.mem_append_left _ hz
  · exact (h salt hist answer hm).mono fun z hz => by simpa using hz

theorem worldDigestSafe_counted {β : Type} (seg : TreeSimLog C) (oa : OracleComp (SimulatorSpec C) β) :
    WorldDigestSafe prims D seg (counted oa) := by
  induction oa using OracleComp.inductionOn generalizing seg with
  | pure b =>
    have : counted (Pure.pure b : OracleComp (SimulatorSpec C) β) = Pure.pure b := simulateQ_pure _ _
    rw [this]
    exact WorldDigestSafe.pure prims D seg b
  | query_bind q f ih =>
    simp only [counted] at ih ⊢
    exact WorldDigestSafe.query_bind prims D _ _ (fun _ _ h => by cases h) fun u => ih u _

theorem worldDigestSafe_free_advance {α : Type} {seg : TreeSimLog C}
    {p : OracleComp (PartySpec C E RealSpec) (Option α)} (h : DigestSafe seg p) :
    WorldDigestSafe prims D seg (free (advance p)) := by
  induction h with
  | pure seg out =>
    change WorldDigestSafe prims D seg (free (Pure.pure (Step.done out)))
    rw [free_pure]
    exact WorldDigestSafe.pure prims D seg _
  | queryLocal seg q k hq h ih =>
    change WorldDigestSafe prims D seg
      (free (OracleComp.lift (OracleSpec.query (spec := LocalSpec C) q) >>= fun r => advance (k r)))
    rw [free_bind]
    simp only [free]
    exact WorldDigestSafe.query_bind prims D _ _
      (fun salt hist he => hq salt hist (by cases he; rfl)) ih
  | round seg out k h ih =>
    simpa only [advance, free_pure] using WorldDigestSafe.pure prims D seg _

theorem worldDigestSafe_sequenceFin {γ : Type} :
    ∀ {n : ℕ} (f : Fin n → OracleComp (WorldSpec C) γ), (∀ i, WorldDigestSafe prims D [] (f i)) →
      WorldDigestSafe prims D [] (Concrete.sequenceFin f)
  | 0, f, _ => by
    simp only [Concrete.sequenceFin]
    exact WorldDigestSafe.pure prims D [] _
  | n + 1, f, hf => by
    simp only [Concrete.sequenceFin]
    exact WorldDigestSafe.bind prims D (hf 0) fun _ => WorldDigestSafe.bind prims D
      (worldDigestSafe_sequenceFin (fun i : Fin n => f i.succ) fun i => hf i.succ) fun _ =>
        WorldDigestSafe.pure prims D [] _

/-- A real round of honest steps that are safe appends a log whose honest digests have their
draws in it. -/
theorem worldDigestSafe_round {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (hs : ∀ i, i ∉ D.1 → DigestSafeStep (steps i)) :
    WorldDigestSafe prims D [] (stepRound worldRoles D A noFunctionality state steps) := by
  rw [stepRound_real]
  refine WorldDigestSafe.bind prims D (worldDigestSafe_counted prims D [] _) fun x => ?_
  obtain ⟨state', sent⟩ := x
  refine WorldDigestSafe.bind prims D ?_ fun _ => WorldDigestSafe.pure prims D [] _
  rw [free_sequenceFin]
  refine worldDigestSafe_sequenceFin prims D _ fun i => ?_
  unfold roundLocal
  cases he : steps i with
  | done out =>
    simp only [free_pure]
    exact WorldDigestSafe.pure prims D [] _
  | call input _ => exact input.elim
  | wait out resume =>
    simp only
    split_ifs with hi
    · simp only [free_pure]
      exact WorldDigestSafe.pure prims D [] _
    · have h := hs i hi
      rw [he] at h
      exact worldDigestSafe_free_advance prims D (h _)

theorem digestSafe_round_steps {α : Type} (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (steps : C.Party → Step C E RealSpec α)
    (hs : ∀ i, i ∉ D.1 → DigestSafeStep (steps i)) :
    ∀ r ∈ support (stepRound worldRoles D A noFunctionality state steps),
      ∀ i, i ∉ D.1 → DigestSafeStep (r.2.1 i) := by
  rw [stepRound_real]
  intro r hr
  obtain ⟨sent, _, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  obtain ⟨next, hn, hr⟩ := (mem_support_bind_iff _ _ _).mp hr
  have he : r = (sent.1, next, sent.2) := by simpa using hr
  subst r
  have hl := treeSimCheck_support_free _ hn
  intro i hi
  have hni := mem_support_sequenceFin_oc _ _ hl i
  have h := hs i hi
  revert hni h
  unfold roundLocal
  cases steps i with
  | done out =>
    intro hni _
    have : next i = .done out := by simpa using hni
    simp only [this]
    trivial
  | call input _ => exact input.elim
  | wait out resume =>
    intro hni h
    simp only [if_neg hi] at hni
    exact (h _).advance_mem _ hni

variable (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-- Every honest step of a reachable configuration is safe. -/
theorem digestSafe_reach (top : TopTree) (tree : Tree) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (state : A.State) (s : TreeSimState C) :
    ∀ n a, TreeStagesReach prims K circuits settings top tree D A x state s n a →
      ∀ i, i ∉ D.1 → DigestSafeStep (a.1.2 i) := by
  intro n
  induction n with
  | zero =>
    intro a ha i hi
    simp only [TreeStagesReach, treeStagesTrace, executeSteps, StateT.run_bind, StateT.run_pure,
      support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at ha
    obtain ⟨p, _, next, hnext, rfl⟩ := ha
    have hn : next.1 ∈ support (treeSimContinue (treeSimRealCont K circuits settings top tree x) p.1.2) := by
      apply OracleComp.support_simulateQ_run'_subset (treeSimLoggedWorld prims D)
      rw [StateT.run'_eq, support_map]
      exact ⟨next, hnext, rfl⟩
    have hi' := mem_support_sequenceFin_oc _ _ (treeSimCheck_support_free _ hn) i
    cases hk : p.1.2 i with
    | none =>
      simp only [hk, continueStep, support_pure, Set.mem_singleton_iff] at hi'
      show DigestSafeStep (next.1 i)
      rw [hi']
      trivial
    | some prss =>
      simp only [hk, continueStep] at hi'
      exact (digestSafe_ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree).advance_mem _ hi'
  | succ n ih =>
    intro a ha i hi
    unfold TreeStagesReach at ha
    rw [treeStages_trace_add] at ha
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion] at ha
    obtain ⟨b, hb', ha⟩ := ha
    have hw := ih b hb'
    simp only [executeSteps] at ha
    split_ifs at ha with hdone
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at ha
      subst a
      exact hw i hi
    · simp only [StateT.run_bind, support_bind, Set.mem_iUnion, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at ha
      obtain ⟨u, hu, rfl⟩ := ha
      exact digestSafe_round_steps D A b.1.1 b.1.2 hw u.1
        (treeTwin_real_round_mem prims D A b.1.1 b.1.2 b.2 u hu) i hi

end World

section Goal

variable [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (circuits : Circuits) (prims : Primitives) (K : Constants C E) (settings : Settings)

/-- Each honest digest entry of a reachable round has the 256 draws of its salt in the same round
log. It needs no collision guard. -/
theorem treeTwinDigestDrawsGoal : TreeTwinDigestDrawsGoal circuits prims K settings := by
  intro _ top tree D A parameter seeds pairs z p _ padding r _ n a reach u hu l hl
  have hs := digestSafe_reach prims D K circuits settings top tree A _ _ _ n a reach
  have hround : (stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2) =
      simulateQ (treeSimLoggedWorld prims D) (stepRound worldRoles D A noFunctionality a.1.1 a.1.2) := by
    rw [simulateQ_stepRound]
    rfl
  rw [hround] at hu
  obtain ⟨l', hl', h⟩ := worldDigestSafe_round prims D A a.1.1 a.1.2 hs a.2 u hu
  have hll : l = l' := List.append_cancel_left (hl.symm.trans hl')
  subst hll
  intro salt hist answer mem
  have hd := h salt hist answer mem
  rw [List.nil_append] at hd
  exact hd

/-- `TreeTwinDigestGoal3` from the lockstep alone. The other half is `treeTwinDigestDrawsGoal`. -/
theorem treeTwinDigestGoal3_of_lockstepStages
    (lockstep : TreeLockstepStagesGoal circuits prims K settings) :
    TreeTwinDigestGoal3 prims K circuits settings :=
  treeTwinDigestGoal3_of_lockstep prims K circuits settings lockstep
    (treeTwinDigestDrawsGoal circuits prims K settings)

end Goal

/-- info: 'ThresholdLeanXmssSecurity.treeTwinDigestDrawsGoal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinDigestDrawsGoal

/-- info: 'ThresholdLeanXmssSecurity.treeTwinDigestGoal3_of_lockstepStages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeTwinDigestGoal3_of_lockstepStages

end ThresholdLeanXmssSecurity
