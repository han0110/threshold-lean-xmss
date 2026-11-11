import ThresholdLeanXmssSecurity.Proof.TreeSecurity
import ThresholdLeanXmssSecurity.Proof.Coupling
import ThresholdLeanXmssSecurity.Proof.CheckSplit

set_option pp.deepTerms false
set_option pp.maxSteps 2000
set_option linter.unusedSectionVars false

open OracleComp OracleSpec LeanXmss ThresholdLeanXmss
open OracleComp.ProgramLogic.Relational

noncomputable section

namespace ThresholdLeanXmssSecurity

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]
variable (prims : Primitives) (K : Constants C E) (circuits : Circuits) (settings : Settings)

/-!
The simulator is normalized to its actual dummy-seed ceremony and T₀ output
shift. The dealer and the full three-round PRSS setup are common prefixes.
Optional ghost hash-cache padding preserves both experiments and the real log.
Fresh stream-table translations retain the exact caches and query log; local
peer, collector and coin interactions also have proved relational couplings.
Actual gadget entries retain their oracle draws and abort-aware continuations.
Bit PRSS also couples mixed fresh/cached reads and visible AES keys. A complete
peer gadget preserves the actual outputs, histories, aborts, shared caches and
real log; unread blocks permit adaptive extensions of earlier mask translations.
With `w = 0`, the peer output difference is confined to `T₀`, and its history
translation is recorded exactly. The frozen peer multiplication and `Rerand`
gadgets preserve these relations, including selective aborts. The real collector
reshare and multiplication now preserve the same invariants through both rushing
exchanges, including propagated aborts and the all-abort early return. The
collector proof uses arbitrary base masks and needs no ideal randomness call.
Its mask translation adapts the GS20 method to the note's collector mode.
The collector case of the ceremony round induction is now derived from exact
per-round transitions with general continuations; only reachable boundary
identification and continuation closure remain contextual obligations. Collector
exits also expose their absolute next labels. Partially active entries propagate
an existing honest abort through the actual rushing round. The rushing calls
preserve both hidden caches exactly, retaining entry freshness facts. Per-party
collector multiplication entries thread the current shared cache inside earlier
continuations. Actual vector resumption now constructs the next collector's
mask equations and boundary, including selectively aborted parties. One global
translation is chosen after the common reply and before any local resume. The
concrete `TreeSimCollectorNext` certificate contains program equations and
freshness facts, with its coupling proved here. Invariant closure retains the
exact activity pattern, boundary parameters and both actual marginal supports.
The named `reshareCollectorNext` case consumes this concrete certificate in the
main round induction; other collector successors retain their contextual rule.
Actual bit PRSS and selectively aborted vector entries preserve every private
cache entry outside their current label. The concrete next-collector certificate
uses future-cache emptiness and future-zero translations to derive its freshness
conditions; the coupling exports both invariants at the following label.
Field PRSS now couples mixed fresh/cached reads with identical decoded outputs
when the accumulated translation is zero at its label, and preserves every
other label. Actual Coin entries produce common masks through the shared cache.
The Coin round case is derived from its real opening, agreement test and ordered
continuations. Partial Coin entries propagate earlier honest aborts through the
actual rushing round. Coin boundary identification and post-Coin continuations
remain contextual obligations. The entire Coin round is no longer a hypothesis.
Optional vector resumption constructs field masks common to both worlds,
including prior aborts, and derives the zero translation at Coin's label from
the preceding translated bit block. Coin entry frames also preserve future
cache emptiness. Rerand's real peer exchange feeds this resumption in the main
induction, following the `Rerand`-then-check order of `runJobs`. The empty-check
branch instead enters the actual empty opening, retaining its copy hashes,
exchange and abort checks. Empty-opening entries couple over any shared hash cache,
including the dealer's earlier queries, and preserve both hidden caches.
Partial Rerand entries propagate earlier aborts through the real rushing round.
The empty opening's exchange, cached copy checks and abort decisions now form
their own proved round stage. Each operator's checks precede its continuation
in the actual driver order. The checks need agreement only at `.copy []` and
preserve all other cache entries, allowing continuations to create different
PRF entries. Entry populates this copy address without a freshness assumption.
Rerand's successor coupling exports this fact whenever another honest round
is possible. Public-cache growth then preserves the same value through the
rushing call and all continuations, independently of the chosen local invariant.
The full public caches still agree at the round boundary and rushing call.
Mask balance, reachable programs, successful post-opening continuations and
invariant closure remain contextual certificates. Nonempty opening now has a
proved round transition. Its canonical waiting boundary, including T₀ alignment
and all prefix hash-cache effects, remains a contextual obligation, as do its
post-opening continuations and invariant closure.
The peer case now uses its actual round, including partial prior aborts. Its
GS20 block equation proves message balance; optional returns preserve the T₀
sharing and history shifts and absolute label increments. Only continuations
at these actual outputs are coupled, in driver order. Reachable peer boundaries,
local continuation couplings and invariant closure remain explicit obligations.
The event choice is now fixed in `treeSimEvents`: one collision/salt-guess
union and accepted incorrect outputs outside that union. `TreeSimStagesGoal`,
`TreeSimHashBoundGoal` and `TreeSimCheckBoundGoal` are independent proof tasks,
assembled by `treeSimulationHopClosed`. For the stages task, sticky-event
bookkeeping and final observation follow from replay, cache alignment and
matching success bits. Digest comparison and the final checked Shamir opening
now have proved round transitions, including partial prior aborts. Their
entry alignment and local continuations remain boundary obligations. The
post-setup invariant, ceremony transitions and the two probability bounds are
still open. `treeSimulationHopClosed` has three Prop premises, not a closed proof.
-/

/-- The output translation used verbatim by `treeSimulator`. -/
def treeSimShift {R : Type} [Add R] (D : C.Coalition) (v : Shares C R)
    (shift : ℕ → R) : Shares C R :=
  fun T g => if lackedTerm D.1 = some T then v T g + shift g else v T g

/-- The pivot is invisible to every corrupt operator. -/
theorem treeSimShift_known {R : Type} [Add R] (D : C.Coalition) (v : Shares C R) (shift : ℕ → R)
    (T : C.Term) (hT : KnownTo D.1 T) : treeSimShift D v shift T = v T := by
  funext g
  exact if_neg (fun h => main_lacked_unknown D T h hT)

/-- The shifted opening is exactly the sharing rebuilt with the desired value. -/
theorem treeSimShift_rebuild (D : C.Coalition) (v : Shares C Bit) (target : ℕ → Bit) :
    treeSimShift D v (fun g => target g + shareValue v g) = mainMultSharing D v target := by
  funext T g
  unfold treeSimShift mainMultSharing
  split_ifs with hT
  · have hs := Finset.sum_erase_add Finset.univ (fun T => v T g) (Finset.mem_univ T)
    unfold shareValue
    dsimp only
    rw [← hs]
    have hz := bit_add_self (v T g)
    have hn := CharTwo.neg_eq (∑ T' ∈ Finset.univ.erase T, v T' g)
    rw [sub_eq_add_neg, hn]
    linear_combination hz
  · rfl

/-- On a correct dummy computation, the simulator opens the functionality's output. -/
theorem treeSimShift_value (D : C.Coalition) (v : Shares C Bit) (target clear : ℕ → Bit)
    (hclear : shareValue v = clear) :
    shareValue (treeSimShift D v (fun g => target g + clear g)) = target := by
  rw [← hclear, treeSimShift_rebuild]
  obtain ⟨T, hT⟩ := main_lacked_exists D
  funext g
  exact mainMultSharing_sum D v target T hT g

/-- The two independent mask families can be translated together. -/
theorem treeSim_masks {M N α β : Type} [AddGroup M] [SampleableType M]
    [AddGroup N] [SampleableType N] (δ : M) (ε : N)
    (f : M → N → ProbComp α) (g : M → N → ProbComp β) (R : α → β → Prop)
    (h : ∀ r p, RelTriple (f r p) (g (r + δ) (p + ε)) R) :
    RelTriple (do let r ← $ᵗ M; let p ← $ᵗ N; f r p)
      (do let r ← $ᵗ M; let p ← $ᵗ N; g r p) R := by
  apply relTriple_uniform_shift δ
  intro r
  exact relTriple_uniform_shift ε (h r)

/-- A rushing adversary uses the same reply and cache on equal views.
`answer` may itself be an entire stateful oracle computation. -/
theorem treeSim_rushing {α β V σ : Type} {oa : ProbComp α} {ob : ProbComp β}
    {R : α → β → Prop} (h : RelTriple oa ob R) (leftView : α → V) (rightView : β → V)
    (hview : ∀ a b, R a b → leftView a = rightView b) (answer : V → ProbComp σ) :
    RelTriple (do let a ← oa; let st ← answer (leftView a); pure (a, st))
      (do let b ← ob; let st ← answer (rightView b); pure (b, st))
      (fun a b => R a.1 b.1 ∧ a.2 = b.2) := by
  apply relTriple_bind h
  intro a b hab
  rw [hview a b hab]
  apply relTriple_bind (relTriple_refl (answer (rightView b)))
  intro st st' hst
  exact relTriple_pure_pure ⟨hab, hst⟩

/-- Setup is unchanged by a hidden stream-key rename. From the same incoming
hash cache it couples exactly, including the cache left by its first message.
This does not commute setup past the dealer's queries. -/
theorem treeSim_prssSetup (D : C.Coalition) (a b : HashOutput) (i : C.Party)
    (s : HashCache C) :
    RelTriple
      ((simulateQ (localAnswer prims) (advance
        (renameParty D a b (prssSetup i : PartyM C E RealSpec (PrssKeys C))).run)).run s)
      ((simulateQ (localAnswer prims) (advance
        (prssSetup i : PartyM C E RealSpec (PrssKeys C)).run)).run s) Eq := by
  rw [renameParty_prssSetup]
  exact relTriple_refl _

/-- Peer reshare: the translated masks give exactly the same corrupt view.
The masks remain available for the output/history invariant. -/
theorem treeSim_reshare (D : C.Coalition) {R : Type} [Field R] [SampleableType R]
    (codec : Codec C E R) {c : ℕ}
    (known : Shares C R) (pairs : C.Party → C.Party → ℕ → R)
    {T₀ : C.Term} {p : C.Party} (hp : Pivot K D T₀ p)
    (v : C.Party → ℕ → R) (w : C.Term → Fin c → R) :
    RelTriple
      (do let r ← $ᵗ (C.Term → Fin c → R)
          let z ← $ᵗ (C.Pair → Fin c → R)
          pure (r, z))
      (do let r ← $ᵗ (C.Term → Fin c → R)
          let z ← $ᵗ (C.Pair → Fin c → R)
          pure (r, z))
      (fun a b => b.1 = a.1 + termShift K D T₀ p v w ∧
        b.2 = a.2 + pairShift p (pairDelta K D T₀ p v w) ∧
        realMsgs K D codec known pairs b.1 b.2 v =
          realMsgs K D codec known pairs a.1 a.2 (fun _ _ => 0)) := by
  apply treeSim_masks (termShift K D T₀ p v w)
    (pairShift p (pairDelta K D T₀ p v w))
  intro r z
  exact relTriple_pure_pure ⟨rfl, rfl, realMsgs_shift K D codec known pairs r z hp v w⟩

/-- Collector reshare: both rushing rounds have the same corrupt view,
for every reply to the first round. -/
theorem treeSim_reshareCollector (D : C.Coalition) {c : ℕ}
    (known : Shares C Bit) (pairs : C.Party → C.Party → ℕ → Bit)
    (T₀ : C.Term) (hT : ¬ KnownTo D.1 T₀) (hp : K.owner T₀ ∉ D.1)
    (v : C.Party → ℕ → Bit) (w : C.Term → Fin c → Bit) :
    RelTriple
      (do let r ← $ᵗ (C.Term → Fin c → Bit)
          let z ← $ᵗ (C.Pair → Fin c → Bit)
          pure (r, z))
      (do let r ← $ᵗ (C.Term → Fin c → Bit)
          let z ← $ᵗ (C.Pair → Fin c → Bit)
          pure (r, z))
      (fun a b => b.1 = a.1 + ΔC K D T₀ v w ∧
        b.2 = a.2 + pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) v w) ∧
        colMsgs1 K D c (frandShare D c known pairs b.1 b.2) v =
          colMsgs1 K D c (frandShare D c known pairs a.1 a.2) (fun _ _ => 0) ∧
        ∀ sent, colMsgs2 K D c (frandShare D c known pairs b.1 b.2) v sent =
          colMsgs2 K D c (frandShare D c known pairs a.1 a.2) (fun _ _ => 0) sent) := by
  apply treeSim_masks (ΔC K D T₀ v w)
    (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) v w))
  intro r z
  exact relTriple_pure_pure ⟨rfl, rfl,
    colMsgs1_shift K D known pairs r z T₀ hT hp v w,
    fun sent => colMsgs2_shift K D known pairs r z T₀ hT hp v w sent⟩

/-- Peer output preservation under the same mask coupling, for every
adversarial inbox, including aborts. This is the output part of the invariant
needed in addition to equality of corrupt views. -/
theorem treeSim_reshare_outputs (D : C.Coalition) {c : ℕ}
    (known : Shares C Bit) (pairs : C.Party → C.Party → ℕ → Bit)
    {T₀ : C.Term} {p : C.Party} (hp : Pivot K D T₀ p)
    (v : C.Party → ℕ → Bit) (w : C.Term → Fin c → Bit) :
    RelTriple
      (do let r ← $ᵗ (C.Term → Fin c → Bit)
          let z ← $ᵗ (C.Pair → Fin c → Bit)
          pure (r, z))
      (do let r ← $ᵗ (C.Term → Fin c → Bit)
          let z ← $ᵗ (C.Pair → Fin c → Bit)
          pure (r, z))
      (fun a b => realMsgs K D bitCodec known pairs b.1 b.2 v =
          realMsgs K D bitCodec known pairs a.1 a.2 (fun _ _ => 0) ∧
        ∀ sent, realOut K D bitCodec known pairs b.1 b.2 v sent =
          idealOut D (filler K .peer) (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g)
            (peerReply K D bitCodec known pairs a.1 a.2 sent)
            (w + fun T g => termVal K D bitCodec known pairs a.1 a.2 (fun _ _ => 0)
              (fun _ _ => none) (refHolder D T) T g.val)) := by
  apply relTriple_post_mono (treeSim_reshare K D bitCodec known pairs hp v w)
  intro a b h
  refine ⟨h.2.2, fun sent => ?_⟩
  rw [h.1, h.2.1]
  exact realOut_shift K D bitCodec bitCodec_roundTrip known pairs a.1 a.2 hp v w
    (filler K .peer) (fun T g => filler_peer_corrupt K D T g) _ (fun _ => rfl) sent

/-- Collector outputs preserve the ideal sharing, including the reply-dependent
translation `cbC` fixed after the first rushing round. -/
theorem treeSim_collector_outputs (D : C.Coalition) {c : ℕ}
    (known : Shares C Bit) (pairs : C.Party → C.Party → ℕ → Bit)
    (T₀ : C.Term) (hT : lackedTerm D.1 = some T₀)
    (v : C.Party → ℕ → Bit) (w : C.Term → Fin c → Bit) :
    RelTriple
      (do let r ← $ᵗ (C.Term → Fin c → Bit)
          let z ← $ᵗ (C.Pair → Fin c → Bit)
          pure (r, z))
      (do let r ← $ᵗ (C.Term → Fin c → Bit)
          let z ← $ᵗ (C.Pair → Fin c → Bit)
          pure (r, z))
      (fun a b => colMsgs1 K D c (frandShare D c known pairs b.1 b.2) v =
          colMsgs1 K D c (frandShare D c known pairs a.1 a.2) (fun _ _ => 0) ∧
        (∀ sent, colMsgs2 K D c (frandShare D c known pairs b.1 b.2) v sent =
          colMsgs2 K D c (frandShare D c known pairs a.1 a.2) (fun _ _ => 0) sent) ∧
        ∀ sent sent', colOuts K D c (frandShare D c known pairs b.1 b.2) v sent sent' =
          idealOut D (filler K .collector) (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g)
            (colReply K D c (frandShare D c known pairs a.1 a.2)
              (colInbox K D c (frandShare D c known pairs a.1 a.2) (fun _ _ => 0) sent) sent')
            (w + (fun T g => termValC K D known pairs a.1 a.2 (fun _ _ => 0)
              (fun _ _ => none) (fun _ _ => none) (refHolder D T) T g.val) + cbC K D sent)) := by
  have hidden := main_lacked_unknown D T₀ hT
  have honest : K.owner T₀ ∉ D.1 := fun hi => hidden ⟨_, hi, K.owner_held T₀⟩
  apply relTriple_post_mono (treeSim_reshareCollector K D known pairs T₀ hidden honest v w)
  intro a b h
  refine ⟨h.2.2.1, h.2.2.2, fun sent sent' => ?_⟩
  rw [h.1, h.2.1]
  exact colOuts_shift K D known pairs a.1 a.2 T₀ hT hidden honest v w _ (fun _ => rfl) sent sent'

/-- The full peer interaction, with arbitrary stateful rushing traffic. The
returned state may contain the public hash cache and transcript. Its joint law with
all honest outputs agrees with an independent ideal sharing. -/
theorem treeSim_peer_round {R σ : Type} [Field R] [CharP R 2] [SampleableType R]
    (D : C.Coalition) (codec : Codec C E R) (hcodec : CodecRoundTrip codec) {c : ℕ}
    (known : Shares C R) (pairs : C.Party → C.Party → ℕ → R)
    (v : C.Party → ℕ → R) (filled : C.Term → ℕ → Option C.Party)
    (hfilled : ∀ T g, (∃ j ∈ D.1, filled T g = some j) ↔ ∃ j ∈ D.1, K.filled j = T)
    (answer : (C.Party → C.Party → Option (Msg E)) →
      ProbComp (σ × (C.Party → C.Party → Option (Msg E)))) :
    RelTriple
      (do let r ← $ᵗ (C.Term → Fin c → R)
          let p ← $ᵗ (C.Pair → Fin c → R)
          let b ← answer (realMsgs K D codec known pairs r p v)
          pure (b.1, realOut K D codec known pairs r p v b.2))
      (do let r ← $ᵗ (C.Term → Fin c → R)
          let p ← $ᵗ (C.Pair → Fin c → R)
          let w ← $ᵗ (C.Term → Fin c → R)
          let b ← answer (realMsgs K D codec known pairs r p (fun _ _ => 0))
          pure (b.1, idealOut D filled
            (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g)
            (peerReply K D codec known pairs r p b.2) w)) Eq := by
  obtain ⟨T₀, j, hp⟩ := exists_pivot K D
  apply relTriple_eqRel_of_evalDist_eq
  refine evalDist_shift _ _ (fun w =>
    (termShift K D T₀ j v w, pairShift j (pairDelta K D T₀ j v w)))
    (fun r p T g => termVal K D codec known pairs r p (fun _ _ => 0)
      (fun _ _ => none) (refHolder D T) T g.val) ?_
  intro w r p
  dsimp only
  rw [realMsgs_shift K D codec known pairs r p hp v w]
  apply bind_congr'
  intro b
  rw [realOut_shift K D codec hcodec known pairs r p hp v w filled hfilled
    _ (fun _ => rfl)]

/-- A hidden uniform value can be translated after the first adversarial
reply, without changing the reply or its state. -/
theorem treeSim_shift_after {α β G : Type} [AddGroup G] [SampleableType G]
    (first : ProbComp α) (rest : α → G → ProbComp β) (shift : α → G) :
    𝒟[do let w ← $ᵗ G; let a ← first; rest a (w + shift a)] =
      𝒟[do let w ← $ᵗ G; let a ← first; rest a w] := by
  rw [evalDist_bind_bind_swap ($ᵗ G) first]
  rw [evalDist_bind_bind_swap ($ᵗ G) first]
  exact evalDist_bind_congr_all first fun a => evalDist_bind_add_uniform (shift a) (rest a)

/-- Both collector rounds, including the branch where every honest operator
aborts after the first reply. The adversary carries the same state and cache
through both rounds; the ideal sharing is independent of both replies. -/
theorem treeSim_collector_rounds {σ : Type} (D : C.Coalition) {c : ℕ}
    (known : Shares C Bit) (pairs : C.Party → C.Party → ℕ → Bit)
    (v : C.Party → ℕ → Bit) (state : σ)
    (answer : σ → (C.Party → C.Party → Option (Msg E)) →
      ProbComp (σ × (C.Party → C.Party → Option (Msg E)))) :
    RelTriple
      (do let r ← $ᵗ (C.Term → Fin c → Bit)
          let p ← $ᵗ (C.Pair → Fin c → Bit)
          let rnd := frandShare D c known pairs r p
          let b ← answer state (colMsgs1 K D c rnd v)
          if ∀ i, i ∉ D.1 → anyAbort (colInbox K D c rnd v b.2 i) = true then
            pure (b.1, fun _ => none)
          else do
            let b' ← answer b.1 (colMsgs2 K D c rnd v b.2)
            pure (b'.1, colOuts K D c rnd v b.2 b'.2))
      (do let r ← $ᵗ (C.Term → Fin c → Bit)
          let p ← $ᵗ (C.Pair → Fin c → Bit)
          let w ← $ᵗ (C.Term → Fin c → Bit)
          let rnd := frandShare D c known pairs r p
          let b ← answer state (colMsgs1 K D c rnd (fun _ _ => 0))
          if ∀ i, i ∉ D.1 → anyAbort (colInbox K D c rnd (fun _ _ => 0) b.2 i) = true then
            pure (b.1, fun _ => none)
          else do
            let b' ← answer b.1 (colMsgs2 K D c rnd (fun _ _ => 0) b.2)
            pure (b'.1, idealOut D (filler K .collector)
              (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g)
              (colReply K D c rnd (colInbox K D c rnd (fun _ _ => 0) b.2) b'.2) w)) Eq := by
  obtain ⟨T₀, hT, hidden⟩ := lackedTerm_spec D
  have honest : K.owner T₀ ∉ D.1 := fun hi => hidden ⟨_, hi, K.owner_held T₀⟩
  apply relTriple_eqRel_of_evalDist_eq
  refine evalDist_shift2 _ _ (fun r p w => do
    let rnd := frandShare D c known pairs r p
    let b ← answer state (colMsgs1 K D c rnd (fun _ _ => 0))
    if ∀ i, i ∉ D.1 → anyAbort (colInbox K D c rnd (fun _ _ => 0) b.2 i) = true then
      pure (b.1, fun _ => none)
    else do
      let b' ← answer b.1 (colMsgs2 K D c rnd (fun _ _ => 0) b.2)
      pure (b'.1, idealOut D (filler K .collector)
        (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g)
        (colReply K D c rnd (colInbox K D c rnd (fun _ _ => 0) b.2) b'.2)
        (w + colShiftF K D known pairs r p b.2)))
    (fun w => (ΔC K D T₀ v w, pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) v w))) ?_ ?_
  · intro w r p
    dsimp only
    rw [colMsgs1_shift K D known pairs r p T₀ hidden honest v w]
    apply bind_congr'
    intro b
    simp only [anyAbort_colInbox]
    split_ifs
    · rfl
    · rw [colMsgs2_shift K D known pairs r p T₀ hidden honest v w]
      apply bind_congr'
      intro b'
      rw [colOuts_shift K D known pairs r p T₀ hT hidden honest v w _ (fun _ => rfl)]
      simp only [colShiftF, add_assoc]
  · intro r p
    exact treeSim_shift_after (answer state (colMsgs1 K D c (frandShare D c known pairs r p) (fun _ _ => 0)))
      (fun b w =>
        if ∀ i, i ∉ D.1 → anyAbort (colInbox K D c (frandShare D c known pairs r p) (fun _ _ => 0) b.2 i) = true then
          pure (b.1, fun _ => none)
        else do
          let b' ← answer b.1 (colMsgs2 K D c (frandShare D c known pairs r p) (fun _ _ => 0) b.2)
          pure (b'.1, idealOut D (filler K .collector)
            (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g)
            (colReply K D c (frandShare D c known pairs r p)
              (colInbox K D c (frandShare D c known pairs r p) (fun _ _ => 0) b.2) b'.2) w))
      (fun b => colShiftF K D known pairs r p b.2)

/-- The field-mask coupling used by `ExtendMult` is the same peer coupling.
The inputs are the actual additive `productValues` of its replicated/Shamir entries. -/
theorem treeSim_extendMult [SampleableType E] (D : C.Coalition) {c : ℕ}
    (known : Shares C E) (pairs : C.Party → C.Party → ℕ → E)
    {T₀ : C.Term} {p : C.Party} (hp : Pivot K D T₀ p)
    (x : C.Party → List (Product C E)) (w : C.Term → Fin c → E) :
    let v := fun i => productValues K i (x i)
    RelTriple
      (do let r ← $ᵗ (C.Term → Fin c → E)
          let z ← $ᵗ (C.Pair → Fin c → E)
          pure (r, z))
      (do let r ← $ᵗ (C.Term → Fin c → E)
          let z ← $ᵗ (C.Pair → Fin c → E)
          pure (r, z))
      (fun a b => b.1 = a.1 + termShift K D T₀ p v w ∧
        b.2 = a.2 + pairShift p (pairDelta K D T₀ p v w) ∧
        realMsgs K D (elementCodec K) known pairs b.1 b.2 v =
          realMsgs K D (elementCodec K) known pairs a.1 a.2 (fun _ _ => 0)) := by
  exact treeSim_reshare K D (elementCodec K) known pairs hp (fun i => productValues K i (x i)) w

/-- Coin reconstruction preserves the uniform distribution for every
continuation, including a continuation returning its final hash cache. -/
theorem treeSim_coin [SampleableType E] (D : C.Coalition) (known : Shares C E)
    {n : ℕ} {α : Type} (k : (C.Term → Fin n → E) → ProbComp α) :
    RelTriple
      (do let v ← $ᵗ (Fin n → E)
          let r ← $ᵗ (C.Term → Fin n → E)
          k (adjust D known r v))
      ($ᵗ (C.Term → Fin n → E) >>= k) Eq := by
  exact relTriple_eqRel_of_evalDist_eq (dist_adjust D known k)

def treeSimCoinView (D : C.Coalition) (c : ℕ) (rnd : C.Party → PrssOutput C E) :
    C.Party → C.Party → Option (Msg E) :=
  fun j i => if j ∈ D.1 ∧ i ∉ D.1 then coinOut K i c (rnd i) j else none

def treeSimCoinOutput (D : C.Coalition) (c : ℕ) (rnd : C.Party → PrssOutput C E)
    (sent : C.Party → C.Party → Option (Msg E)) : C.Party → Option (List E) :=
  fun i => if i ∈ D.1 then none else coinRes K i c (rnd i)
    (fun j => if j ∈ D.1 then sent j i else coinOut K j c (rnd j) i)

/-- Opening the adjusted Shamir sharing produces the chosen coin at every
honest operator that does not abort, even for inconsistent adversarial replies. -/
theorem treeSim_coin_outputs (D : C.Coalition) {c : ℕ} (known : Shares C E)
    (pairs : C.Party → C.Party → ℕ → E) (r : C.Term → Fin c → E) (p : C.Pair → Fin c → E)
    (vals : Fin c → E) (sent : C.Party → C.Party → Option (Msg E)) :
    let out := treeSimCoinOutput K D c (frandShare D c known pairs (adjust D known r vals) p) sent
    out = fun i => (out i).map (fun _ => List.ofFn vals) := by
  funext i
  by_cases hi : i ∈ D.1
  · simp [treeSimCoinOutput, hi]
  · rcases coinRes_robust K D c known pairs (adjust D known r vals) p sent i hi with h | h
    · simp [treeSimCoinOutput, hi, h]
    · simp only [sum_frandAt_adjust] at h
      simp [treeSimCoinOutput, hi, h]

/-- The entire coin round is coupled to a uniform coin with selective abort,
retaining the adversary's state and public hash cache with all honest outputs. -/
theorem treeSim_coin_round [SampleableType E] {σ : Type} (D : C.Coalition) {c : ℕ}
    (known : Shares C E) (pairs : C.Party → C.Party → ℕ → E)
    (answer : (C.Party → C.Party → Option (Msg E)) →
      ProbComp (σ × (C.Party → C.Party → Option (Msg E)))) :
    RelTriple
      (do let r ← $ᵗ (C.Term → Fin c → E)
          let p ← $ᵗ (C.Pair → Fin c → E)
          let rnd := frandShare D c known pairs r p
          let b ← answer (treeSimCoinView K D c rnd)
          pure (b.1, treeSimCoinOutput K D c rnd b.2))
      (do let vals ← $ᵗ (Fin c → E)
          let r ← $ᵗ (C.Term → Fin c → E)
          let p ← $ᵗ (C.Pair → Fin c → E)
          let rnd := frandShare D c known pairs (adjust D known r vals) p
          let b ← answer (treeSimCoinView K D c rnd)
          pure (b.1, fun i => (treeSimCoinOutput K D c rnd b.2 i).map (fun _ => List.ofFn vals))) Eq := by
  apply relTriple_eqRel_of_evalDist_eq
  symm
  have h := dist_adjust D known (fun r => do
    let p ← $ᵗ (C.Pair → Fin c → E)
    let rnd := frandShare D c known pairs r p
    let b ← answer (treeSimCoinView K D c rnd)
    pure (b.1, treeSimCoinOutput K D c rnd b.2))
  rw [← h]
  apply evalDist_bind_congr_all
  intro vals
  apply evalDist_bind_congr_all
  intro r
  apply evalDist_bind_congr_all
  intro p
  apply evalDist_bind_congr_all
  intro b
  rw [← treeSim_coin_outputs K D known pairs r p vals b.2]

/-- `Rerand` uses peer reshare on the additive owner sums, so its message
coupling is the peer coupling with those actual inputs. -/
theorem treeSim_rerand (D : C.Coalition) {c : ℕ}
    (known : Shares C Bit) (pairs : C.Party → C.Party → ℕ → Bit)
    {T₀ : C.Term} {p : C.Party} (hp : Pivot K D T₀ p)
    (v : C.Party → Shares C Bit) (w : C.Term → Fin c → Bit) :
    let inputs := fun i => ownerSum K (localContext i) (v i)
    RelTriple
      (do let r ← $ᵗ (C.Term → Fin c → Bit)
          let z ← $ᵗ (C.Pair → Fin c → Bit)
          pure (r, z))
      (do let r ← $ᵗ (C.Term → Fin c → Bit)
          let z ← $ᵗ (C.Pair → Fin c → Bit)
          pure (r, z))
      (fun a b => b.1 = a.1 + termShift K D T₀ p inputs w ∧
        b.2 = a.2 + pairShift p (pairDelta K D T₀ p inputs w) ∧
        realMsgs K D bitCodec known pairs b.1 b.2 inputs =
          realMsgs K D bitCodec known pairs a.1 a.2 (fun _ _ => 0)) := by
  exact treeSim_reshare K D bitCodec known pairs hp (fun i => ownerSum K (localContext i) (v i)) w

/-- Common translations of the hidden pivot preserve the check's split-slice
relation, even when the known copies are inconsistent across honest operators. -/
theorem treeSim_checkSlice [SampleableType E] (D : C.Coalition)
    {xsR ysR xsD ysD : C.Party → Shares C E}
    (h : SplitSliceRel D xsR ysR xsD ysD) (δx δy : ℕ → E) :
    SplitSliceRel D (fun i => treeSimShift D (xsR i) δx)
      (fun i => treeSimShift D (ysR i) δy) xsD ysD := by
  constructor
  · intro i hi T hT hiT
    simpa only [treeSimShift_known D _ δx T hT, treeSimShift_known D _ δy T hT]
      using h.1 i hi T hT hiT
  · intro T hT i j hi hj hiT hjT
    obtain ⟨hx, hy, hxd, hyd⟩ := h.2 T hT i j hi hj hiT hjT
    refine ⟨?_, ?_, hxd, hyd⟩
    · funext g
      simp only [treeSimShift, hx]
    · funext g
      simp only [treeSimShift, hy]

/-- The pointwise reconstruction identity applies to the real `openRep`,
including its copy hashes and abort conditions. Correctness of `clear` must
come from the checked batch invariant. -/
theorem treeSim_openRep (D : C.Coalition) (ctx : Context C) (v : Shares C Bit)
    (target clear : ℕ → Bit) (hclear : shareValue v = clear) (count : ℕ) :
    (openRep K ctx (treeSimShift D v (fun g => target g + clear g)) count :
      PartyM C E RealSpec (ℕ → Bit)) =
      openRep K ctx (mainMultSharing D v target) count := by
  rw [← hclear, treeSimShift_rebuild]

/-! The round induction below separates the still-open contextual obligations.
A concrete invariant must retain PRSS labels, translated caches, tuple histories,
corrupt state, and the sticky union of bad events. In particular, the local view
couplings above do not themselves prove the `check` or initialization stages. -/

/-- The protocol stage responsible for the next synchronous round. -/
inductive TreeSimStage where
  | prssSetup | reshare | reshareCollector | reshareCollectorNext | rerand | coin | extendMult | check | openRep | openRepEmpty | ceremony

section Rounds

variable {σ₁ σ₂ : Type}
variable (Ro₁ : Roles C (StateT σ₁ ProbComp)) (Ro₂ : Roles C (StateT σ₂ ProbComp))
variable (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)

/-- A configuration at a boundary between synchronous rounds. -/
abbrev TreeSimConfig (σ : Type) :=
  (A.State × (C.Party → Step C E RealSpec TreeOutput)) × σ

variable (Bad : σ₁ → Prop)
variable (Inv : TreeSimConfig A σ₁ → TreeSimConfig A σ₂ → Prop)
variable (stage : TreeSimConfig A σ₁ → TreeSimStage)

/-- One named contextual preservation obligation, with actual `stepRound`
semantics. Honest aborts and the rushing adversary are part of the step. -/
def TreeSimPreserves (gadget : TreeSimStage) : Prop :=
  ∀ c₁ c₂, stage c₁ = gadget → Inv c₁ c₂ → ¬ Bad c₁.2 → ¬ AllDone D c₁.1.2 →
    RelTriple ((stepRound Ro₁ D A noFunctionality c₁.1.1 c₁.1.2).run c₁.2)
      ((stepRound Ro₂ D A noFunctionality c₂.1.1 c₂.1.2).run c₂.2)
      (fun x y => Bad x.2 ∨ Inv ((x.1.1, x.1.2.1), x.2) ((y.1.1, y.1.2.1), y.2))

/-- The stage partition assembles a whole-ceremony round coupling. The main
application factors out the complete PRSS prefix and uses the remaining cases
to carry the post-setup invariant. -/
theorem treeSim_executeRounds
    (setup : TreeSimPreserves Ro₁ Ro₂ D A Bad Inv stage .prssSetup)
    (peer : TreeSimPreserves Ro₁ Ro₂ D A Bad Inv stage .reshare)
    (collector : TreeSimPreserves Ro₁ Ro₂ D A Bad Inv stage .reshareCollector)
    (collectorNext : TreeSimPreserves Ro₁ Ro₂ D A Bad Inv stage .reshareCollectorNext)
    (rerand : TreeSimPreserves Ro₁ Ro₂ D A Bad Inv stage .rerand)
    (coin : TreeSimPreserves Ro₁ Ro₂ D A Bad Inv stage .coin)
    (extendMult : TreeSimPreserves Ro₁ Ro₂ D A Bad Inv stage .extendMult)
    (check : TreeSimPreserves Ro₁ Ro₂ D A Bad Inv stage .check)
    (opening : TreeSimPreserves Ro₁ Ro₂ D A Bad Inv stage .openRep)
    (openingEmpty : TreeSimPreserves Ro₁ Ro₂ D A Bad Inv stage .openRepEmpty)
    (ceremony : TreeSimPreserves Ro₁ Ro₂ D A Bad Inv stage .ceremony)
    (Q : (A.State × (C.Party → Option TreeOutput)) × σ₁ →
      (A.State × (C.Party → Option TreeOutput)) × σ₂ → Prop)
    (sticky : ∀ st (steps : C.Party → Step C E RealSpec TreeOutput) s, Bad s →
      ∀ x ∈ support ((stepRound Ro₁ D A noFunctionality st steps).run s), Bad x.2)
    (done : ∀ c₁ c₂, Inv c₁ c₂ → ¬ Bad c₁.2 → (AllDone D c₁.1.2 ↔ AllDone D c₂.1.2))
    (output : ∀ c₁ c₂, Inv c₁ c₂ → ¬ Bad c₁.2 →
      Q ((c₁.1.1, fun i => (c₁.1.2 i).output), c₁.2)
        ((c₂.1.1, fun i => (c₂.1.2 i).output), c₂.2))
    (fuel : ℕ) (c₁ : TreeSimConfig A σ₁) (c₂ : TreeSimConfig A σ₂)
    (initial : Bad c₁.2 ∨ Inv c₁ c₂) :
    RelTriple ((executeRounds Ro₁ D A noFunctionality fuel c₁.1.1 c₁.1.2).run c₁.2)
      ((executeRounds Ro₂ D A noFunctionality fuel c₂.1.1 c₂.1.2).run c₂.2)
      (fun x y => Bad x.2 ∨ Q x y) := by
  apply relTriple_executeRounds Ro₁ Ro₂ D D A A noFunctionality noFunctionality
    Bad Inv Q sticky done output _ fuel c₁ c₂ initial
  intro a b hab hbad hdone
  cases hs : stage a with
  | prssSetup => exact setup a b hs hab hbad hdone
  | reshare => exact peer a b hs hab hbad hdone
  | reshareCollector => exact collector a b hs hab hbad hdone
  | reshareCollectorNext => exact collectorNext a b hs hab hbad hdone
  | rerand => exact rerand a b hs hab hbad hdone
  | coin => exact coin a b hs hab hbad hdone
  | extendMult => exact extendMult a b hs hab hbad hdone
  | check => exact check a b hs hab hbad hdone
  | openRep => exact opening a b hs hab hbad hdone
  | openRepEmpty => exact openingEmpty a b hs hab hbad hdone
  | ceremony => exact ceremony a b hs hab hbad hdone

end Rounds

/-! Exact transport of the actual emulation through log erasure. -/

section ExecutionHom
variable {m n : Type → Type} [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
variable (φ : ∀ {α : Type}, m α → n α)
variable (hpure : ∀ {α : Type} (a : α), φ (pure a) = pure a)
variable (hbind : ∀ {α β : Type} (p : m α) (k : α → m β), φ (p >>= k) = φ p >>= fun a => φ (k a))

include hpure hbind in
private theorem treeSim_hom_sequence {α : Type} : ∀ {k : ℕ} (p : Fin k → m α),
    φ (Concrete.sequenceFin p) = Concrete.sequenceFin (fun i => φ (p i))
  | 0, p => by simp [Concrete.sequenceFin, hpure]
  | k + 1, p => by
    simp only [Concrete.sequenceFin, hbind, hpure, treeSim_hom_sequence]

include hpure hbind in
private theorem treeSim_hom_simulate {ι α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec m) (p : OracleComp spec α) :
    φ (simulateQ impl p) = simulateQ (fun t => φ (impl t)) p := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [hpure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, hbind, ih]

variable (Ro : Roles C m) (Ro' : Roles C n)
variable (hadv : ∀ {α : Type} (p : OracleComp (LocalSpec C) α), φ (Ro.adversary p) = Ro'.adversary p)
variable (hhonest : ∀ {α : Type} (p : OracleComp (LocalSpec C) α), φ (Ro.honest p) = Ro'.honest p)
variable {I α : Type} (D : C.Coalition) (A : Adversary C E I PEmpty PEmpty)

include hpure hbind hadv hhonest in
private theorem treeSim_hom_round (state : A.State) (steps : C.Party → Step C E RealSpec α) :
    φ (stepRound Ro D A noFunctionality state steps) =
      stepRound Ro' D A noFunctionality state steps := by
  unfold stepRound
  rw [if_neg (by simp [callInput_real]), if_neg (by simp [callInput_real])]
  simp only [hbind, hpure, hadv, treeSim_hom_sequence φ hpure hbind]
  apply bind_congr
  intro r
  congr 1
  congr 1
  funext j
  cases hs : steps j with
  | done out => exact hpure _
  | wait outbox resume =>
    by_cases hj : j ∈ D.1
    · simp [hj, hpure]
    · simp [hj, hhonest]
  | call input resume => exact input.elim

include hpure hbind hadv hhonest in
private theorem treeSim_hom_rounds : ∀ fuel state (steps : C.Party → Step C E RealSpec α),
    φ (executeRounds Ro D A noFunctionality fuel state steps) =
      executeRounds Ro' D A noFunctionality fuel state steps
  | 0, state, steps => by simp [executeRounds, hpure]
  | fuel + 1, state, steps => by
    simp only [executeRounds]
    split_ifs
    · exact hpure _
    · rw [hbind, treeSim_hom_round φ hpure hbind Ro Ro' hadv hhonest D A]
      exact bind_congr fun r => treeSim_hom_rounds fuel r.1 r.2.1

include hpure hbind hadv hhonest in
/-- A monad morphism transports a whole real phase, preserving the rushing
adversary, all stopping decisions, and every honest output. -/
theorem treeSim_hom_phase (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) :
    φ (executePhase Ro D A noFunctionality fuel state program) =
      executePhase Ro' D A noFunctionality fuel state program := by
  unfold executePhase
  rw [hbind]
  have hs : φ (startSteps Ro D program) = startSteps Ro' D program := by
    unfold startSteps
    rw [treeSim_hom_sequence φ hpure hbind]
    congr 1
    funext i
    by_cases hi : i ∈ D.1 <;> simp [hi, hpure, hhonest]
  rw [hs]
  exact bind_congr fun steps => treeSim_hom_rounds φ hpure hbind Ro Ro' hadv hhonest D A fuel state steps
end ExecutionHom

/-- Erase only the simulator's call log, retaining its hidden-stream cache. -/
def treeSimErase {α : Type} (p : EmulationM C α) :
    StateT (StreamCache C) (OracleComp (WorldSpec C)) α :=
  StateT.mk fun cache => keygenEraseLog (p.run cache)

theorem treeSimErase_pure {α : Type} (a : α) : treeSimErase (C := C) (pure a) = pure a := by
  funext cache
  exact keygenEraseLog_pure _

theorem treeSimErase_bind {α β : Type} (p : EmulationM C α) (k : α → EmulationM C β) :
    treeSimErase (p >>= k) = treeSimErase p >>= fun a => treeSimErase (k a) := by
  funext cache
  simp only [treeSimErase, StateT.run_bind, keygenEraseLog_bind]
  rfl

/-- The actual emulated roles after erasing their unused call log. -/
def treeSimErasedRoles (D : C.Coalition) :
    Roles C (StateT (StreamCache C) (OracleComp (WorldSpec C))) where
  adversary p := treeSimErase ((emulatedRoles D).adversary p)
  honest p := treeSimErase ((emulatedRoles D).honest p)

/-- The complete emulation, not just an individual query, has exactly this
log-free semantics. The hidden stream cache is still returned. -/
theorem treeSimErase_phase {I α : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) :
    treeSimErase (executePhase (emulatedRoles D) D A noFunctionality fuel state program) =
      executePhase (treeSimErasedRoles D) D A noFunctionality fuel state program := by
  exact treeSim_hom_phase (fun p => treeSimErase p) (fun a => treeSimErase_pure a)
    (fun p k => treeSimErase_bind p k) (emulatedRoles D) (treeSimErasedRoles D)
    (fun _ => rfl) (fun _ => rfl) D A fuel state program

/-- The emulator and the stream world use the same address, parenthesized
differently. This conversion preserves every cached bit. -/
def treeSimCache (cache : StreamCache C) : HiddenCache C :=
  fun x => cache (x.1.1, x.1.2, x.2)

def treeSimCacheInv (cache : HiddenCache C) : StreamCache C :=
  fun x => cache ((x.1, x.2.1), x.2.2)

@[simp] theorem treeSimCache_inverse (cache : HiddenCache C) :
    treeSimCache (treeSimCacheInv cache) = cache := rfl

@[simp] theorem treeSimCacheInv_inverse (cache : StreamCache C) :
    treeSimCacheInv (treeSimCache cache) = cache := rfl

private theorem treeSimCache_update (cache : StreamCache C) (x : PrgInput C) (b : Bit) :
    treeSimCache (cache.cacheQuery x b) =
      (treeSimCache cache).cacheQuery ((x.1, x.2.1), x.2.2) b := by
  funext y
  have he : y = ((x.1, x.2.1), x.2.2) ↔ (y.1.1, y.1.2, y.2) = x := by
    rcases x with ⟨a, b, c⟩
    rcases y with ⟨⟨a', b'⟩, c'⟩
    simp only [Prod.mk.injEq, and_assoc]
  by_cases hy : y = ((x.1, x.2.1), x.2.2)
  · subst y
    simp [treeSimCache, QueryCache.cacheQuery]
  · have hx := mt he.mpr hy
    simp [treeSimCache, QueryCache.cacheQuery, Function.update_of_ne hy, Function.update_of_ne hx]

/-- Exact lazy-cache conversion, including both fresh and repeated draws. -/
theorem treeSimCache_query (cache : StreamCache C) (x : PrgInput C) :
    (fun r => (r.1, treeSimCache r.2)) <$> (((PrgInput C →ₒ Bit).randomOracle x).run cache) =
      (((((KeyName C × HashOutput) × ℕ × ℕ × ℕ) →ₒ Bit).randomOracle
        ((x.1, x.2.1), x.2.2)).run (treeSimCache cache)) := by
  simp only [randomOracle.apply_eq, StateT.run_bind, StateT.run_get, pure_bind]
  cases hc : cache x <;> simp [treeSimCache, hc, StateT.run_modifyGet,
    StateT.run_pure, bind_pure_comp, treeSimCache_update]

/-- Evaluate the actual log-free emulator in the world while preserving both
caches, in the layout used by `streamWorld`. -/
def treeSimEvaluate {α : Type}
    (p : StateT (StreamCache C) (OracleComp (WorldSpec C)) α) :
    StateT (HashCache C × HiddenCache C) ProbComp α :=
  StateT.mk fun s => (fun r => (r.1.1, r.2, treeSimCache r.1.2)) <$>
    (simulateQ (worldAnswer prims) (p.run (treeSimCacheInv s.2))).run s.1

theorem treeSimEvaluate_pure {α : Type} (a : α) :
    treeSimEvaluate prims (C := C) (pure a) = pure a := by
  apply StateT.ext
  intro s
  simp [treeSimEvaluate]

theorem treeSimEvaluate_bind {α β : Type}
    (p : StateT (StreamCache C) (OracleComp (WorldSpec C)) α)
    (k : α → StateT (StreamCache C) (OracleComp (WorldSpec C)) β) :
    treeSimEvaluate prims (p >>= k) = treeSimEvaluate prims p >>= fun a => treeSimEvaluate prims (k a) := by
  apply StateT.ext
  intro s
  simp [treeSimEvaluate, StateT.run_bind, simulateQ_bind, bind_map_left, map_bind]

theorem treeSimErase_lift {α : Type} (p : OracleComp (WorldSpec C) α) :
    treeSimErase (StateT.lift (liftM p)) = StateT.lift p := by
  apply StateT.ext
  intro cache
  simp [treeSimErase, StateT.run_lift, keygenEraseLog, WriterT.run_liftM, Functor.map_map]

theorem treeSimErase_adversary {α : Type} (D : C.Coalition) (p : OracleComp (LocalSpec C) α) :
    (treeSimErasedRoles D).adversary p = StateT.lift (worldRoles.adversary p) := by
  apply StateT.ext
  intro cache
  simp only [treeSimErasedRoles, treeSimErase, emulatedRoles, StateT.run_mk,
    StateT.run_lift, keygenEraseLog]
  rw [← fst_observe]
  simp [bind_pure_comp, Functor.map_map]

theorem treeSimEvaluate_lift {α : Type} (p : OracleComp (WorldSpec C) α) :
    treeSimEvaluate prims (StateT.lift p) = onHash (simulateQ (worldAnswer prims) p) := by
  apply StateT.ext
  intro s
  simp [treeSimEvaluate, onHash, StateT.run_lift, simulateQ_map, Functor.map_map]

/-- A free probabilistic draw does not modify the shared hash cache. -/
theorem treeSim_world_sample {α : Type} (p : ProbComp α) :
    simulateQ (worldAnswer (C := C) prims) (free (liftComp p (LocalSpec C))) = StateT.lift p := by
  rw [simulateQ_free]
  induction p using OracleComp.inductionOn with
  | pure a =>
    apply StateT.ext
    intro s
    simp [StateT.run_lift]
  | query_bind t k ih =>
    simp only [liftComp_bind, simulateQ_bind, ih]
    apply StateT.ext
    intro s
    simp [StateT.run_bind, StateT.run_lift]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem treeSimEvaluate_hidden (D : C.Coalition) (x : PrgInput C) (hx : Hidden D x.1) :
    treeSimEvaluate prims (StateT.mk fun cache =>
      free (liftComp (((PrgInput C →ₒ Bit).randomOracle x).run cache) (LocalSpec C))) =
      streamWorld prims D (.inr (.inr (.inr x))) := by
  apply StateT.ext
  intro s
  have h := congrArg (Functor.map (fun r => (r.1, s.1, r.2)))
    (treeSimCache_query (treeSimCacheInv s.2) x)
  simp only [treeSimEvaluate, StateT.run_mk, treeSim_world_sample, StateT.run_lift,
    bind_pure_comp]
  simpa only [streamWorld, if_pos hx, StateT.run_mk, treeSimCache_inverse, Functor.map_map] using h

private theorem treeSim_stream_free {α : Type} (D : C.Coalition)
    (p : OracleComp (LocalSpec C) α) :
    simulateQ (streamWorld prims D) (free p) =
      simulateQ (fun t => streamWorld prims D (.inr t)) p := by
  have he : streamWorld prims D = (fun t => streamWorld prims D (.inl t)) +
      (fun t => streamWorld prims D (.inr t)) := by
    funext t
    cases t <;> rfl
  conv_lhs => rw [he]
  exact simulateQ_free _ _ p

set_option backward.isDefEq.respectTransparency false in
/-- The emulator's honest role is exactly the stream-world honest role once
its log is erased and its stream-cache addresses are converted. -/
theorem treeSimEvaluate_honest {α : Type} (D : C.Coalition) (p : OracleComp (LocalSpec C) α) :
    treeSimEvaluate prims ((treeSimErasedRoles D).honest p) =
      simulateQ (streamWorld prims D) (free p) := by
  dsimp only [treeSimErasedRoles, emulatedRoles]
  rw [treeSim_hom_simulate (fun p => treeSimErase p) (fun a => treeSimErase_pure a)
    (fun p k => treeSimErase_bind p k)]
  rw [treeSim_hom_simulate (fun p => treeSimEvaluate prims p) (fun a => treeSimEvaluate_pure prims a)
    (fun p k => treeSimEvaluate_bind prims p k), treeSim_stream_free]
  congr 1
  funext t
  rcases t with n | q | x
  · rw [treeSimErase_lift, treeSimEvaluate_lift]
    simp only [worldAnswer, simulateQ_free, simulateQ_spec_query]
    rfl
  · rw [treeSimErase_lift, treeSimEvaluate_lift]
    simp only [worldAnswer, simulateQ_free, simulateQ_spec_query]
    rfl
  · by_cases hx : Hidden D x.1
    · simp only [if_pos hx]
      have he : treeSimErase (StateT.mk fun cache =>
          (liftM (free (liftComp (((PrgInput C →ₒ Bit).randomOracle x).run cache) (LocalSpec C))) :
            WriterT (CallLog C) (OracleComp (WorldSpec C)) (Bit × StreamCache C))) =
          StateT.mk fun cache => free (liftComp (((PrgInput C →ₒ Bit).randomOracle x).run cache) (LocalSpec C)) := by
        apply StateT.ext
        intro cache
        exact keygenEraseLog_lift _
      rw [he]
      exact treeSimEvaluate_hidden prims D x hx
    · simp only [if_neg hx]
      rw [treeSimErase_lift, treeSimEvaluate_lift]
      simp [streamWorld, hx, worldAnswer, simulateQ_free]

private theorem treeSim_onHash_pure {α : Type} (a : α) :
    onHash (C := C) (pure a) = pure a := by
  apply StateT.ext
  intro s
  simp [onHash]

private theorem treeSim_onHash_bind {α β : Type} (p : StateT (HashCache C) ProbComp α)
    (k : α → StateT (HashCache C) ProbComp β) :
    onHash (p >>= k) = onHash p >>= fun a => onHash (k a) := by
  apply StateT.ext
  intro s
  simp [onHash, StateT.run_bind, map_bind, bind_map_left]

set_option backward.isDefEq.respectTransparency false in
/-- Counted local calls keep exactly the ordinary shared hash-cache semantics. -/
theorem treeSim_stream_adversary {α : Type} (D : C.Coalition) (p : OracleComp (LocalSpec C) α) :
    simulateQ (streamWorld prims D) (worldRoles.adversary p) =
      onHash (simulateQ (localAnswer prims) p) := by
  induction p using OracleComp.inductionOn with
  | pure a => simp [treeSim_onHash_pure]
  | query_bind t k ih =>
    change simulateQ (streamWorld prims D) (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
      fun x => worldRoles.adversary (k x)) = _
    rw [simulateQ_bind, adversary_query, simulateQ_spec_query]
    simp only [simulateQ_bind, simulateQ_spec_query, treeSim_onHash_bind, ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem treeSimEvaluate_adversary {α : Type} (D : C.Coalition) (p : OracleComp (LocalSpec C) α) :
    treeSimEvaluate prims ((treeSimErasedRoles D).adversary p) =
      simulateQ (streamWorld prims D) (worldRoles.adversary p) := by
  rw [treeSimErase_adversary, treeSimEvaluate_lift, treeSim_stream_adversary]
  congr 1
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change simulateQ (worldAnswer prims) (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
      fun x => worldRoles.adversary (k x)) = _
    rw [simulateQ_bind, adversary_query, simulateQ_spec_query]
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    rfl

/-- The whole log-free emulator is the stream-world execution of its actual
honest program, from the same hash cache and the converted stream cache. -/
theorem treeSimEvaluate_phase {I α : Type} (D : C.Coalition)
    (A : Adversary C E I PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (program : C.Party → PartyM C E RealSpec α) :
    treeSimEvaluate prims (executePhase (treeSimErasedRoles D) D A noFunctionality fuel state program) =
      simulateQ (streamWorld prims D) (executePhase worldRoles D A noFunctionality fuel state program) := by
  rw [simulateQ_executePhase]
  exact treeSim_hom_phase (fun p => treeSimEvaluate prims p) (fun a => treeSimEvaluate_pure prims a)
    (fun p k => treeSimEvaluate_bind prims p k) (treeSimErasedRoles D)
    (simRoles (streamWorld prims D) worldRoles)
    (fun p => treeSimEvaluate_adversary prims D p) (fun p => treeSimEvaluate_honest prims D p)
    D A fuel state program

/-! The exact functionality boundary, before any statistical argument. -/

/-- Seed selection in `Ftree` and in `treeSimulator`. -/
def treeSimSeeds (inputs : C.Party → Option (Keys C)) : C.Term → HashOutput :=
  fun T => (C.parties.findSome? fun i =>
    if i ∈ C.holders T then (inputs i).map (·.seed T) else none).getD 0

/-- A selected holder of dealt keys supplies the dealt seed. -/
theorem treeSimSeeds_dealt (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (pairs : C.Pair → HashOutput) (active : C.Party → Prop) [DecidablePred active]
    (T : C.Term) (h : ∃ i, active i ∧ i ∈ C.holders T) :
    treeSimSeeds (fun i => if active i then some (dealtKeys parameter seeds pairs i) else none) T = seeds T := by
  obtain ⟨i, hi, hiT⟩ := h
  have hsome : (C.parties.findSome? fun j => if j ∈ C.holders T then
      ((if active j then some (dealtKeys parameter seeds pairs j) else none) : Option (Keys C)).map
        (·.seed T) else none).isSome := by
    rw [List.findSome?_isSome_iff]
    exact ⟨i, by simp [Committee.parties], by simp [hi, hiT]⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨j, _, hj⟩ := List.exists_of_findSome?_eq_some hv
  unfold treeSimSeeds
  rw [hv]
  split_ifs at hj with hjT hactive
  all_goals simp_all [dealtKeys]

/-- The dummy seeds coincide with the real seeds on every known term and
are exactly zero on every hidden term. -/
theorem treeSimSeeds_corrupt (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (T : C.Term) :
    treeSimSeeds (corruptInputs D (dealtKeys parameter seeds pairs)) T =
      if KnownTo D.1 T then seeds T else 0 := by
  by_cases h : KnownTo D.1 T
  · rw [if_pos h]
    exact treeSimSeeds_dealt parameter seeds pairs (fun i => i ∈ D.1) T h
  · rw [if_neg h]
    have hn : ∀ i, (if i ∈ C.holders T then
        (corruptInputs D (dealtKeys parameter seeds pairs) i).map (·.seed T) else none) = none := by
      intro i
      by_cases hi : i ∈ D.1
      · have hiT : i ∉ C.holders T := fun hiT => h ⟨i, hi, hiT⟩
        simp [hiT]
      · simp [corruptInputs, hi]
    simp only [treeSimSeeds, hn]
    have hh : C.parties.findSome? (fun _ => (none : Option HashOutput)) = none := by
      induction C.parties <;> simp_all
    rw [hh]
    rfl

/-- Every term has an honest holder, so the functionality uses the original
dealt seeds even for terms also held by the coalition. -/
theorem treeSimSeeds_honest (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) :
    treeSimSeeds (fun i => if i ∈ D.1 then none else some (dealtKeys parameter seeds pairs i)) = seeds := by
  funext T
  have h := treeSimSeeds_dealt parameter seeds pairs (fun i => i ∉ D.1) T
    (by obtain ⟨i, hiT, hi⟩ := exists_honest_holder (C := C) D T; exact ⟨i, hi, hiT⟩)
  simpa only [ite_not] using h

/-- The exact functionality on valid dealt keys, with its dealer call before
the simulator leak and with its actual selective-abort output. -/
theorem treeSim_Ftree (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (top : TopTree) (tree : Tree) :
    (Ftree circuits settings top tree).run D
      (fun i => if i ∈ D.1 then none else some (dealtKeys parameter seeds pairs i)) = (do
        let (output, openings) ← liftComp (dealerCeremony circuits settings parameter seeds top tree) _
        let receivers ← leak (parameter, openings)
        pure fun i => if i ∉ D.1 ∧ i ∈ receivers then output else none) := by
  have hp : (firstInput (fun i => if i ∈ D.1 then none else
      some (dealtKeys parameter seeds pairs i))).parameter = parameter := by
    obtain ⟨i, _, hi⟩ := firstInput_honest D (dealtKeys parameter seeds pairs)
    rw [hi]
    rfl
  change (do
    let (output, openings) ← liftComp (dealerCeremony circuits settings _
      (treeSimSeeds _) top tree) _
    let receivers ← leak (_, openings)
    pure fun i => if i ∉ D.1 ∧ i ∈ receivers then output else none) = _
  rw [hp, treeSimSeeds_honest]

/-- The real gadgets with exactly the simulator's output override. -/
def treeSimGadgets (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (openings : List (List (List Bit)))
    (ctx : Context C) (k : ℕ) (jobs : List Job) : RunGadgets C E RealSpec :=
  { realRunGadgets K ctx settings.mode with
    output := fun v count => do
      let clear ← StateT.lift (oracleStep (jobs.mapM (evalJob circuits parameter seeds)))
      let shift := fun g => (openings.getD k []).flatten.getD g 0 + clear.flatten.getD g 0
      StateT.lift (openRep K ctx (treeSimShift D v shift) count) }

/-- The exact honest program executed by `treeSimulator`, with its leak made
explicit. This uses the real gadgets and the simulator's real output override. -/
def treeSimProgram (D : C.Coalition) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (openings : List (List (List Bit)))
    (top : TopTree) (tree : Tree) (i : C.Party) : PartyM C E RealSpec TreeOutput :=
  ceremonyWith K circuits settings (treeSimGadgets K circuits settings D parameter seeds openings)
    i ⟨parameter, seeds, fun _ => 0⟩ top tree

/-- The actual emulator answer with only the unused log removed. -/
def treeSimPhase (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) : OracleComp (WorldSpec C) (A.State × Finset C.Party) := do
  let (state, outputs) ← (executePhase (treeSimErasedRoles D) D A noFunctionality
    (ceremonyFuel circuits settings) state
    (treeSimProgram K circuits settings D parameter seeds openings top tree)).run' ∅
  pure (state, Finset.univ.filter fun i => (outputs i).isSome)

/-- Exact projection of the frozen simulator's answer to the data used by the
ideal game. No hash cache is discarded or reset by this identity. -/
theorem treeSim_answer (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (st : SimulatorState C (Keys C) A.State)
    (parameter : PublicParameter) (openings : List (List (List Bit))) :
    (fun r => (r.1.adversary, r.2)) <$>
      (treeSimulator K circuits settings top tree D A).answer st (parameter, openings) =
      treeSimPhase K circuits settings top tree D A st.adversary parameter
        (treeSimSeeds st.corrupt) openings := by
  simp only [treeSimulator, bind_pure_comp, Functor.map_map]
  unfold treeSimPhase
  rw [← treeSimErase_phase]
  simp only [treeSimErase, StateT.run'_eq, StateT.run_mk, keygenEraseLog,
    Functor.map_map, bind_pure_comp]
  rfl

/-- The dealer's local calls use the same free world as the simulator;
its outer simulator-state layer is untouched. -/
theorem treeSim_dealer_lift {σ L R α : Type}
    (reply : QueryImpl (L →ₒ R) (StateT σ (OracleComp (WorldSpec C))))
    (oa : OracleComp (RoSpec C) α) :
    simulateQ ((fun t : (LocalSpec C).Domain =>
        (StateT.lift (free (OracleComp.lift (OracleSpec.query t))) :
          StateT σ (OracleComp (WorldSpec C)) _)) + reply)
      (liftComp oa (LocalSpec C + (L →ₒ R))) =
      StateT.lift (free (liftComp oa (LocalSpec C))) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    apply StateT.ext
    intro st
    simp [StateT.run_lift]
  | query_bind t k ih =>
    simp only [liftComp_bind, simulateQ_bind, ih, free_bind]
    apply StateT.ext
    intro st
    rcases t with q | x <;> simp [StateT.run_bind, StateT.run_lift] <;> rfl

/-- An explicit ideal game: adversary start, dealer, the actual emulation,
and the distinguisher, in their actual shared world. -/
def treeSimIdealRun (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) : OracleComp (WorldSpec C) Bool := do
  let state ← worldRoles.adversary (A.start (corruptInputs D (dealtKeys parameter seeds pairs)) z)
  let (output, openings) ← free (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))
  let (state, receivers) ← treeSimPhase K circuits settings top tree D A state parameter
    (fun T => if KnownTo D.1 T then seeds T else 0) openings
  worldRoles.adversary (Z (state, fun i => if i ∉ D.1 ∧ i ∈ receivers then output else none))

set_option backward.isDefEq.respectTransparency false in
/-- Normalize the frozen ideal experiment exactly. The shared dealer cache
remains explicit, so subsequent couplings cannot silently replace it by `∅`. -/
theorem treeSim_idealGame (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    treeIdealGame K circuits settings top tree D A (dealtKeys parameter seeds pairs) z Z =
      treeSimIdealRun K circuits settings top tree D A parameter seeds pairs z Z := by
  unfold treeIdealGame distinguish idealExecution
  rw [treeSim_Ftree circuits settings D parameter seeds pairs top tree]
  simp only [simulateQ_bind, treeSim_dealer_lift, simulateQ_leak_add, simulateQ_pure,
    StateT.run_bind, StateT.run_lift, StateT.run_pure, StateT.run_mk,
    bind_assoc, pure_bind]
  have hs : (treeSimulator K circuits settings top tree D A).start
      (corruptInputs D (dealtKeys parameter seeds pairs)) z =
      (fun r => (⟨r.1, r.2, corruptInputs D (dealtKeys parameter seeds pairs)⟩ :
        SimulatorState C (Keys C) A.State)) <$>
        observe (A.start (corruptInputs D (dealtKeys parameter seeds pairs)) z) := rfl
  have ho : ∀ st, (treeSimulator K circuits settings top tree D A).output st = pure st.adversary :=
    fun _ => rfl
  rw [hs]
  simp only [ho, pure_bind, bind_map_left]
  unfold treeSimIdealRun
  rw [← fst_observe, bind_map_left]
  dsimp only
  apply bind_congr
  intro r
  apply bind_congr
  intro out
  have hseeds : treeSimSeeds (corruptInputs D (dealtKeys parameter seeds pairs)) =
      (fun T => if KnownTo D.1 T then seeds T else 0) :=
    funext (treeSimSeeds_corrupt D parameter seeds pairs)
  rw [← hseeds, ← treeSim_answer K circuits settings top tree D A
    ⟨r.1, r.2, corruptInputs D (dealtKeys parameter seeds pairs)⟩ parameter out.2]
  simp only [bind_map_left]


/-- Evaluating an emulation and forgetting its private stream cache preserves
its returned value and the shared hash cache, from every initial cache. -/
theorem treeSimEvaluate_run {α : Type}
    (p : StateT (StreamCache C) (OracleComp (WorldSpec C)) α)
    (h : HashCache C) (cache : StreamCache C) :
    (simulateQ (worldAnswer prims) (p.run' cache)).run h =
      (fun r => (r.1, r.2.1)) <$> (treeSimEvaluate prims p).run (h, treeSimCache cache) := by
  simp [treeSimEvaluate, StateT.run'_eq, simulateQ_map, Functor.map_map]

/-- The actual simulator phase, now executed by the ideal-stream handler. -/
def treeSimStreamPhase (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) :
    StateT (HashCache C × HiddenCache C) ProbComp (A.State × Finset C.Party) := do
  let (state, outputs) ← simulateQ (streamWorld prims D)
    (executePhase worldRoles D A noFunctionality (ceremonyFuel circuits settings) state
      (treeSimProgram K circuits settings D parameter seeds openings top tree))
  pure (state, Finset.univ.filter fun i => (outputs i).isSome)

/-- The simulator phase starts with an empty private stream cache and the
hash cache left by the dealer. -/
theorem treeSimPhase_run (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (openings : List (List (List Bit))) (h : HashCache C) :
    (simulateQ (worldAnswer prims)
      (treeSimPhase K circuits settings top tree D A state parameter seeds openings)).run h =
      (fun r => (r.1, r.2.1)) <$>
        (treeSimStreamPhase prims K circuits settings top tree D A state parameter seeds openings).run (h, ∅) := by
  unfold treeSimPhase treeSimStreamPhase
  simp only [bind_pure_comp, simulateQ_map, StateT.run_map]
  rw [treeSimEvaluate_run, treeSimEvaluate_phase]
  simp only [Functor.map_map]
  rfl

/-- Both actual phases can now be compared in the same cache monad. The
honest dealer still runs before the simulator and shares its hash cache. -/
def treeSimStreamIdealRun (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) : ProbComp Bool := do
  let (state, h) ← (simulateQ (localAnswer prims)
    (A.start (corruptInputs D (dealtKeys parameter seeds pairs)) z)).run ∅
  let ((output, openings), h) ← (simulateQ (localAnswer prims)
    (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))).run h
  let ((state, receivers), caches) ←
    (treeSimStreamPhase prims K circuits settings top tree D A state parameter
      (fun T => if KnownTo D.1 T then seeds T else 0) openings).run (h, ∅)
  (simulateQ (localAnswer prims)
    (Z (state, fun i => if i ∉ D.1 ∧ i ∈ receivers then output else none))).run' caches.1

set_option backward.isDefEq.respectTransparency false in
private theorem treeSim_world_adversary {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ (worldAnswer prims) (worldRoles.adversary p) = simulateQ (localAnswer prims) p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    change simulateQ (worldAnswer prims) (worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>=
      fun x => worldRoles.adversary (k x)) = _
    rw [simulateQ_bind, adversary_query, simulateQ_spec_query]
    simp only [simulateQ_bind, simulateQ_spec_query, ih]
    rfl

/-- Exact acceptance normalization, including the dealer's shared-cache
prefix and the final adversarial distinguisher. -/
theorem treeSim_streamIdeal_eq (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    Prod.fst <$> worldRun prims
      (treeIdealGame K circuits settings top tree D A (dealtKeys parameter seeds pairs) z Z) =
      treeSimStreamIdealRun prims K circuits settings top tree D A parameter seeds pairs z Z := by
  rw [treeSim_idealGame]
  unfold treeSimIdealRun worldRun treeSimStreamIdealRun
  simp only [simulateQ_bind, treeSim_world_adversary, simulateQ_free, StateT.run_bind,
    treeSimPhase_run, bind_map_left, map_bind, StateT.run'_eq]

/-- The ideal phase and distinguisher after the dealer and adversary start,
from the hash cache produced by those two prefix computations. -/
def treeSimIdealFinish (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (Z : Distinguisher C A.State TreeOutput)
    (state : A.State) (dealt : Option TreeOutput × List (List (List Bit))) :
    StateT (HashCache C) ProbComp Bool := StateT.mk fun h => do
  let ((state, receivers), caches) ←
    (treeSimStreamPhase prims K circuits settings top tree D A state parameter
      (fun T => if KnownTo D.1 T then seeds T else 0) dealt.2).run (h, ∅)
  (simulateQ (localAnswer prims)
    (Z (state, fun i => if i ∉ D.1 ∧ i ∈ receivers then dealt.1 else none))).run caches.1

/-- The normalized ideal run with exactly the same dealer-first prefix as
the ghost real experiment. The dealer's output is retained for the T0 shift. -/
def treeSimDealerFirstIdeal (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) : ProbComp Bool :=
  (do
    let dealt ← simulateQ (localAnswer prims)
      (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))
    let state ← simulateQ (localAnswer prims)
      (A.start (corruptInputs D (dealtKeys parameter seeds pairs)) z)
    treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z state dealt).run' ∅

/-- Initialization commutes jointly: dealer output, adversary state, and
shared cache all feed the same continuation. No independence assumption is
made about the values returned by the shared hash oracle. -/
theorem treeSim_ideal_prefix_swap (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    𝒟[treeSimStreamIdealRun prims K circuits settings top tree D A parameter seeds pairs z Z] =
      𝒟[treeSimDealerFirstIdeal prims K circuits settings top tree D A parameter seeds pairs z Z] := by
  have h := (commutes_simulateQ (localAnswer prims)
    (fun t u => commutes_of_isAtom (isAtom_localAnswer prims t) (isAtom_localAnswer prims u))
    (A.start (corruptInputs D (dealtKeys parameter seeds pairs)) z)
    (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))).bind
      (treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z) ∅
  have e := congrArg (fun d => Prod.fst <$> d) h
  simpa only [treeSimStreamIdealRun, treeSimDealerFirstIdeal, treeSimIdealFinish,
    ← evalDist_map, StateT.run'_eq, StateT.run_bind, StateT.run_mk, map_bind] using e

/-! The dealer's queries may be moved across a computation which cannot
program the hash oracle. This is equality of joint distributions, including
both caches; it does not assert independence of the dealer and the ceremony. -/

private theorem treeSim_onHash_commutes {α β : Type}
    {p : StateT (HashCache C) ProbComp α} {q : StateT (HashCache C) ProbComp β}
    (h : Commutes p q) : Commutes (onHash p) (onHash q) := by
  intro s
  have e := congrArg (fun d => (fun r => (r.1, r.2, s.2)) <$> d) (h s.1)
  simpa only [onHash, StateT.run_bind, StateT.run_mk, StateT.run_pure,
    map_bind, bind_map_left, Functor.map_map, evalDist_map, evalDist_bind, evalDist_pure, map_pure, Function.comp_def] using e

private theorem treeSim_hash_hidden_commutes {α β : Type}
    (p : StateT (HashCache C) ProbComp α) (q : StateT (HiddenCache C) ProbComp β) :
    Commutes (onHash p) (StateT.mk fun s => (fun r => (r.1, s.1, r.2)) <$> q.run s.2) := by
  intro s
  simp only [onHash, StateT.run_bind, StateT.run_mk, StateT.run_pure,
    bind_map_left]
  exact DeferredSampling.evalDist_bind_comm _ _ _

/-- The two local interfaces used by the real protocol. Unlike the simulator
interface, neither side has a programming query. -/
def treeSimLocalWorld : QueryImpl (LocalSpec C + LocalSpec C) (OracleComp (WorldSpec C)) :=
  ((fun t => OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inl (.inl t)))) :
    QueryImpl (LocalSpec C) (OracleComp (WorldSpec C))) +
  ((fun t => OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr t))) :
    QueryImpl (LocalSpec C) (OracleComp (WorldSpec C)))

set_option backward.isDefEq.respectTransparency false in
private theorem treeSim_local_query_commutes (D : C.Coalition)
    (t : (LocalSpec C).Domain) (u : (LocalSpec C + LocalSpec C).Domain) :
    Commutes (onHash (localAnswer prims t))
      (simulateQ (streamWorld prims D) (treeSimLocalWorld u)) := by
  rcases u with u | (u | u | x)
  · change Commutes (onHash (localAnswer prims t))
      (simulateQ (streamWorld prims D)
        (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inl (.inl u)))))
    rw [simulateQ_spec_query]
    exact treeSim_onHash_commutes
      (commutes_of_isAtom (isAtom_localAnswer prims t) (isAtom_localAnswer prims u))
  · simpa only [treeSimLocalWorld, QueryImpl.add_apply_inr, simulateQ_spec_query, streamWorld] using
      treeSim_onHash_commutes (commutes_of_isAtom (isAtom_localAnswer prims t)
        (isAtom_localAnswer prims (.inl u)))
  · simpa only [treeSimLocalWorld, QueryImpl.add_apply_inr, simulateQ_spec_query, streamWorld] using
      treeSim_onHash_commutes (commutes_of_isAtom (isAtom_localAnswer prims t)
        (isAtom_localAnswer prims (.inr (.inl u))))
  · simp only [treeSimLocalWorld, QueryImpl.add_apply_inr, simulateQ_spec_query, streamWorld]
    split_ifs
    · exact treeSim_hash_hidden_commutes _ _
    · exact treeSim_onHash_commutes (commutes_of_isAtom (isAtom_localAnswer prims t)
        (isAtom_localAnswer prims (.inr (.inr x))))

/-- Every dealer/local computation commutes with every nonprogramming
stream-world computation, including adaptive queries and repeated cache hits. -/
theorem treeSim_dealer_commutes (D : C.Coalition) {α β : Type}
    (dealer : OracleComp (LocalSpec C) α) (p : OracleComp (LocalSpec C + LocalSpec C) β) :
    Commutes (onHash (simulateQ (localAnswer prims) dealer))
      (simulateQ (streamWorld prims D) (simulateQ treeSimLocalWorld p)) := by
  rw [← QueryImpl.simulateQ_compose]
  have hquery : ∀ t, Commutes (onHash (localAnswer prims t))
      (simulateQ ((streamWorld prims D).compose treeSimLocalWorld) p) := by
    intro t
    induction p using OracleComp.inductionOn with
    | pure a => simpa using commutes_pure (onHash (localAnswer prims t)) a
    | query_bind u k ih =>
      rw [simulateQ_bind, simulateQ_spec_query]
      exact (treeSim_local_query_commutes prims D t u).bind_right ih
  induction dealer using OracleComp.inductionOn with
  | pure a =>
    rw [simulateQ_pure, treeSim_onHash_pure]
    exact (commutes_pure _ a).symm
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, treeSim_onHash_bind]
    exact (hquery t).bind_left ih

/-- The real protocol uses two copies of the local interface. -/
def treeSimLocalRoles : Roles C (OracleComp (LocalSpec C + LocalSpec C)) where
  adversary p := simulateQ (fun t => OracleComp.lift
    (OracleSpec.query (spec := LocalSpec C + LocalSpec C) (.inl t))) p
  honest p := simulateQ (fun t => OracleComp.lift
    (OracleSpec.query (spec := LocalSpec C + LocalSpec C) (.inr t))) p

set_option backward.isDefEq.respectTransparency false in
private theorem treeSimLocalWorld_adversary {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ treeSimLocalWorld (treeSimLocalRoles.adversary p) = worldRoles.adversary p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [treeSimLocalRoles, simulateQ_bind, simulateQ_spec_query]
    change (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inl (.inl t))) >>=
      fun a => simulateQ treeSimLocalWorld (treeSimLocalRoles.adversary (k a))) = _
    rw [show worldRoles.adversary (OracleComp.lift (OracleSpec.query t) >>= k) =
      worldRoles.adversary (OracleComp.lift (OracleSpec.query t)) >>= fun a => worldRoles.adversary (k a) from rfl,
      adversary_query]
    simp only [ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem treeSimLocalWorld_honest {α : Type} (p : OracleComp (LocalSpec C) α) :
    simulateQ treeSimLocalWorld (treeSimLocalRoles.honest p) = free p := by
  induction p using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind t k ih =>
    simp only [treeSimLocalRoles, simulateQ_bind, simulateQ_spec_query, free_bind]
    change (OracleComp.lift (OracleSpec.query (spec := WorldSpec C) (.inr t)) >>=
      fun a => simulateQ treeSimLocalWorld (treeSimLocalRoles.honest (k a))) = _
    simp only [ih]
    rfl

/-- The real experiment represented without a programming interface. -/
def treeSimLocalRealGame (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) : OracleComp (LocalSpec C + LocalSpec C) Bool := do
  let state ← treeSimLocalRoles.adversary (A.start (corruptInputs D x) z)
  let outputs ← executePhase treeSimLocalRoles D A noFunctionality (ceremonyFuel circuits settings)
    state (fun i => ceremony K circuits settings i (x i) top tree)
  treeSimLocalRoles.adversary (Z outputs)

/-- Inserting the nonprogramming representation recovers the frozen real game. -/
theorem treeSim_localReal_eq (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    simulateQ treeSimLocalWorld (treeSimLocalRealGame K circuits settings top tree D A x z Z) =
      treeRealGame K circuits settings top tree D A x z Z := by
  unfold treeSimLocalRealGame treeRealGame distinguish realExecution
  simp only [simulateQ_bind, treeSimLocalWorld_adversary, bind_assoc]
  apply bind_congr
  intro state
  rw [treeSim_hom_phase (fun p => simulateQ treeSimLocalWorld p)
    (fun a => simulateQ_pure _ a) (fun p k => simulateQ_bind _ p k)
    treeSimLocalRoles worldRoles (fun p => treeSimLocalWorld_adversary p)
    (fun p => treeSimLocalWorld_honest p)]

/-- A value-irrelevant dealer prefix may be dropped for any nonprogramming
computation, including one that returns its complete query history. -/
theorem treeSim_dealer_prefix {α β : Type} (D : C.Coalition)
    (dealer : OracleComp (LocalSpec C) α) (p : OracleComp (LocalSpec C + LocalSpec C) β)
    (cache : HashCache C × HiddenCache C) :
    𝒟[(do
      let _ ← onHash (simulateQ (localAnswer prims) dealer)
      simulateQ (streamWorld prims D) (simulateQ treeSimLocalWorld p)).run' cache] =
      𝒟[(simulateQ (streamWorld prims D) (simulateQ treeSimLocalWorld p)).run' cache] := by
  have h := treeSim_dealer_commutes prims D dealer p
  have e := congrArg (fun d => Prod.fst <$> d) (h.bind (fun _ b => pure b) cache)
  simp only [bind_pure, ← evalDist_map, ← StateT.run'_eq] at e
  rw [e]
  simp only [StateT.run'_eq, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
  apply DeferredSampling.evalDist_bind_congr_left
  intro r
  exact DeferredSampling.evalDist_bind_const_neverFails _ (by simp) _

/-- A shared-cache dealer prefix can be inserted without changing the real
acceptance distribution. Its value may then be retained as a ghost for the
simulation coupling. The cache itself is never reset. -/
theorem treeSim_real_dealer_prefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) {α : Type}
    (dealer : OracleComp (LocalSpec C) α) (cache : HashCache C × HiddenCache C) :
    𝒟[(do
      let _ ← onHash (simulateQ (localAnswer prims) dealer)
      simulateQ (streamWorld prims D)
        (treeRealGame K circuits settings top tree D A x z Z)).run' cache] =
      𝒟[(simulateQ (streamWorld prims D)
        (treeRealGame K circuits settings top tree D A x z Z)).run' cache] := by
  simpa only [treeSim_localReal_eq] using treeSim_dealer_prefix prims D dealer
    (treeSimLocalRealGame K circuits settings top tree D A x z Z) cache

/-- An instrumented stream run. The first component is acceptance; the two
flags are the union of all hash failures and all undetected check failures. -/
abbrev TreeSimTrace (C : Committee) (E : Type) :=
  ∀ (_ : TopTree) (_ : Tree) (_ : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty),
    (C.Party → Keys C) → Aux → Distinguisher C A.State TreeOutput →
    ProbComp (Bool × Bool × Bool)

/-- Complete query/answer history of the concrete stream-world execution. -/
abbrev TreeSimLog (C : Committee) := List ((t : (WorldSpec C).Domain) × (WorldSpec C).Range t)

/-- Embed a local query/answer into its actual counted/free world address. -/
def treeSimLocalLog : (t : (LocalSpec C + LocalSpec C).Domain) →
    (LocalSpec C + LocalSpec C).Range t → TreeSimLog C
  | .inl t, u => [⟨.inl (.inl t), u⟩]
  | .inr t, u => [⟨.inr t, u⟩]

/-- Tracing the nonprogramming presentation can itself be expressed as a
nonprogramming computation, so dealer commutation also preserves the trace. -/
def treeSimLocalLogged {α : Type} (p : OracleComp (LocalSpec C + LocalSpec C) α) :
    OracleComp (LocalSpec C + LocalSpec C) (α × TreeSimLog C) :=
  (simulateQ (QueryImpl.withTraceAppend (spec := LocalSpec C + LocalSpec C)
    (fun t => OracleComp.lift (OracleSpec.query t)) treeSimLocalLog) p).run

set_option backward.isDefEq.respectTransparency false in
private theorem treeSimLocalLogged_run {α : Type} (D : C.Coalition)
    (p : OracleComp (LocalSpec C + LocalSpec C) α) :
    (simulateQ ((streamWorld prims D).withTraceAppend (fun t u => ([⟨t, u⟩] : TreeSimLog C)))
      (simulateQ treeSimLocalWorld p)).run =
      simulateQ (streamWorld prims D) (simulateQ treeSimLocalWorld (treeSimLocalLogged p)) := by
  induction p using OracleComp.inductionOn with
  | pure a =>
    simp [treeSimLocalLogged, WriterT.run_pure]
  | query_bind t k ih =>
    rcases t with t | t
    all_goals
      simp only [treeSimLocalLogged, simulateQ_bind, simulateQ_spec_query,
        treeSimLocalWorld, QueryImpl.add_apply_inl, QueryImpl.add_apply_inr,
        QueryImpl.withTraceAppend_apply, WriterT.run_bind,
        WriterT.run_liftM, WriterT.run_tell, pure_bind, bind_assoc,
        simulateQ_map, bind_map_left, Functor.map_map]
      apply bind_congr
      intro u
      congr 1
      exact ih u

/-- The two bad flags must classify a concrete run. They are kept abstract
until the contextual hash and check arguments identify their events. -/
abbrev TreeSimEvents (C : Committee) (E : Type) :=
  ∀ (_ : TopTree) (_ : Tree) (_ : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty),
    (C.Party → Keys C) → Aux → Distinguisher C A.State TreeOutput →
    TreeSimLog C → Bool × Bool

/-- Record every real-world query and response, without modifying either cache. -/
def treeSimLoggedRun {α : Type} (D : C.Coalition) (p : OracleComp (WorldSpec C) α) :
    ProbComp (α × TreeSimLog C) :=
  (simulateQ ((streamWorld prims D).withTraceAppend (fun t u => [⟨t, u⟩])) p).run.run' (∅, ∅)

/-- Retain the dealer's output as private ghost data. Its calls share the
hash cache but are excluded from the real adversary/honest query log. -/
def treeSimGhostRun {α β : Type} (D : C.Coalition) (dealer : OracleComp (LocalSpec C) α)
    (p : OracleComp (WorldSpec C) β) : ProbComp (α × (β × TreeSimLog C)) :=
  (do
    let d ← onHash (simulateQ (localAnswer prims) dealer)
    let r ← (simulateQ ((streamWorld prims D).withTraceAppend
      (fun t u => ([⟨t, u⟩] : TreeSimLog C))) p).run
    pure (d, r)).run' (∅, ∅)

/-- Dealer insertion preserves the entire real transcript, not just its
acceptance bit. Both caches are shared throughout this ghost execution. -/
theorem treeSim_ghost_log (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) {α : Type}
    (dealer : OracleComp (LocalSpec C) α) :
    𝒟[Prod.snd <$> treeSimGhostRun prims D dealer
      (treeRealGame K circuits settings top tree D A x z Z)] =
      𝒟[treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)] := by
  have h := treeSim_dealer_prefix prims D dealer
    (treeSimLocalLogged (treeSimLocalRealGame K circuits settings top tree D A x z Z)) (∅, ∅)
  rw [← treeSimLocalLogged_run, treeSim_localReal_eq] at h
  simpa only [treeSimGhostRun, treeSimLoggedRun, StateT.run'_eq, StateT.run_bind,
    StateT.run_pure, StateT.run_map, map_bind, map_pure, Functor.map_map, bind_pure_comp] using h

/-- Erasing the query log is an exact program equality. -/
theorem treeSim_log_erase {α : Type} (D : C.Coalition) (p : OracleComp (WorldSpec C) α) :
    Prod.fst <$> treeSimLoggedRun prims D p = (simulateQ (streamWorld prims D) p).run' (∅, ∅) := by
  have h := congrArg (fun m => m.run' (∅, ∅))
    (QueryImpl.fst_map_run_withTraceAppend (streamWorld prims D)
      (fun t u => ([⟨t, u⟩] : TreeSimLog C)) p)
  simpa only [treeSimLoggedRun, StateT.run'_eq, StateT.run_map, Functor.map_map] using h

/-- The simulation's collision region. The two points per PRSS key belong to
`keySplit`, and are deliberately absent. Deterministic `Th` calls are absent too. -/
def TreeSimHashDomain : Query C → Prop
  | .history _ | .digest _ _ | .copy _ | .coinKey _ _ _ => True
  | _ => False

/-- A hash answer in either the honest or the counted part of the real log. -/
def TreeSimHashAnswer (log : TreeSimLog C) (q : Query C) (h : HashOutput) : Prop :=
  (⟨.inr (.inr (.inl q)), h⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log ∨
  (⟨.inl (.inl (.inr (.inl q))), h⟩ : (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log

/-- One collision union over the whole ceremony, including the distinguisher. -/
def TreeSimHashCollision (log : TreeSimLog C) : Prop :=
  ∃ q r h, TreeSimHashDomain q ∧ TreeSimHashDomain r ∧ q ≠ r ∧
    TreeSimHashAnswer log q h ∧ TreeSimHashAnswer log r h

/-- The 256 bits of an actually queried hidden digest salt (`Rand(_,2)`).
The same label/key may be read by several holders; these are the same salt. -/
def TreeSimHiddenSalt (D : C.Coalition) (log : TreeSimLog C) (salt : List Bit) : Prop :=
  salt.length = 256 ∧ ∃ T key label, ¬ KnownTo D.1 T ∧ ∀ g : Fin 256,
    (⟨.inr (.inr (.inr (.term T, key, label, 2, g.val))), salt.getD g.val 0⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log

/-- Guessing a hidden salt in a counted digest query. This includes queries
before the salt was drawn and queries after its digest was revealed. -/
def TreeSimSaltGuess (D : C.Coalition) (log : TreeSimLog C) : Prop :=
  ∃ salt hist h, TreeSimHiddenSalt D log salt ∧
    (⟨.inl (.inl (.inr (.inl (.digest salt hist)))), h⟩ :
      (t : (WorldSpec C).Domain) × (WorldSpec C).Range t) ∈ log

/-- All simulation hash failures form one event, not one budget per batch. -/
def TreeSimHashBad (D : C.Coalition) (log : TreeSimLog C) : Prop :=
  TreeSimHashCollision log ∨ TreeSimSaltGuess D log

/-- A bounded prefix of the actual ceremony with the shared-cache dealer.
Keeping the fuel is essential: an honest party can finish before its peers.
The log includes all draws, so this is a semantic replay certificate, not a
fresh independent execution used in a probability estimate. -/
def TreeSimOutputWitness (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (dealt : Option TreeOutput × List (List (List Bit)))
    (out : A.State × (C.Party → Option TreeOutput)) (log : TreeSimLog C) : Prop :=
  ∃ fuel pref, fuel ≤ ceremonyFuel circuits settings ∧ pref <+: log ∧
    (dealt, (out, pref)) ∈ support (treeSimGhostRun prims D
      (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))
      (realExecution D A noFunctionality fuel
        (fun i keys => (ceremony K circuits settings i keys top tree : PartyM C E RealSpec TreeOutput))
        (dealtKeys parameter seeds pairs) z))

/-- A semantic certificate of an accepted incorrect result. Later queries
cannot erase it. Bounding this event requires identifying the first incorrect
batch in the logged execution and applying contextual check soundness. -/
def TreeSimWrongOutput (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (log : TreeSimLog C) : Prop :=
  ∃ parameter seeds pairs dealt out,
    x = dealtKeys parameter seeds pairs ∧
    TreeSimOutputWitness prims K circuits settings top tree D A parameter seeds pairs z dealt out log ∧
    ∃ i, i ∉ D.1 ∧ (out.2 i).isSome ∧ out.2 i ≠ dealt.1

/-- Fixed classifiers for the three independent proof tasks below. Hash
failures take precedence, so the check bound pays only the algebraic error.
There are no oracle programs or classifiers left as parameters of this choice. -/
def treeSimEvents : TreeSimEvents C E := fun top tree D A x z _ log =>
  (decide (TreeSimHashBad D log),
    decide (¬ TreeSimHashBad D log ∧ TreeSimWrongOutput prims K circuits settings top tree D A x z log))

/-- The sticky predicate used in the concrete stage invariant. -/
def TreeSimBad (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (log : TreeSimLog C) : Prop :=
  TreeSimHashBad D log ∨ TreeSimWrongOutput prims K circuits settings top tree D A x z log

theorem treeSimHashBad_mono (D : C.Coalition) {a b : TreeSimLog C}
    (hab : a <+: b) : TreeSimHashBad D a → TreeSimHashBad D b := by
  have mem : ∀ {v}, v ∈ a → v ∈ b := fun hv => hab.sublist.subset hv
  have answer : ∀ q h, TreeSimHashAnswer a q h → TreeSimHashAnswer b q h := by
    intro q h hq
    exact hq.imp mem mem
  rintro (⟨q, r, h, hq, hr, hne, ha, hb⟩ | ⟨salt, hist, h, hsalt, hh⟩)
  · exact Or.inl ⟨q, r, h, hq, hr, hne, answer q h ha, answer r h hb⟩
  · obtain ⟨hlen, T, key, label, hT, hbits⟩ := hsalt
    exact Or.inr ⟨salt, hist, h, ⟨hlen, T, key, label, hT, fun g => mem (hbits g)⟩, mem hh⟩

theorem treeSimBad_mono (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    {a b : TreeSimLog C} (hab : a <+: b) :
    TreeSimBad prims K circuits settings top tree D A x z a →
      TreeSimBad prims K circuits settings top tree D A x z b := by
  rintro (h | ⟨parameter, seeds, pairs, dealt, out, hx, ⟨fuel, pref, hf, hp, hr⟩, hw⟩)
  · exact Or.inl (treeSimHashBad_mono D hab h)
  · exact Or.inr ⟨parameter, seeds, pairs, dealt, out, hx, ⟨fuel, pref, hf, hp.trans hab, hr⟩, hw⟩

/-- The two recorded flags are exactly the sticky stage predicate. The check
flag itself need not be sticky: a later hash failure takes precedence. -/
theorem treeSimEvents_bad (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (log : TreeSimLog C) :
    ((treeSimEvents prims K circuits settings top tree D A x z Z log).1 = true ∨
      (treeSimEvents prims K circuits settings top tree D A x z Z log).2 = true) ↔
      TreeSimBad prims K circuits settings top tree D A x z log := by
  simp only [treeSimEvents, decide_eq_true_eq, TreeSimBad]
  tauto

/-- Instrument the fixed real execution with a supplied classifier.
The three parallel proof tasks below use the concrete choice `treeSimEvents`. -/
def treeSimTrace (events : TreeSimEvents C E) : TreeSimTrace C E :=
  fun top tree D A x z Z =>
    (fun r => (r.1, events top tree D A x z Z r.2)) <$>
      treeSimLoggedRun prims D (treeRealGame K circuits settings top tree D A x z Z)

/-- Inserting the ghost dealer also preserves both classified bad flags.
The classifiers see exactly the original real transcript. -/
theorem treeSim_ghost_trace (events : TreeSimEvents C E) (top : TopTree) (tree : Tree)
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (x : C.Party → Keys C) (z : Aux) (Z : Distinguisher C A.State TreeOutput)
    {α : Type} (dealer : OracleComp (LocalSpec C) α) :
    𝒟[(fun r => (r.2.1, events top tree D A x z Z r.2.2)) <$>
      treeSimGhostRun prims D dealer (treeRealGame K circuits settings top tree D A x z Z)] =
      𝒟[treeSimTrace prims K circuits settings events top tree D A x z Z] := by
  have h := congrArg (fun d => (fun r => (r.1, events top tree D A x z Z r.2)) <$> d)
    (treeSim_ghost_log prims K circuits settings top tree D A x z Z dealer)
  simpa only [treeSimTrace, evalDist_map, Functor.map_map, Function.comp_def] using h

/-- Instrumentation must preserve the actual stream-world acceptance marginal. -/
def TreeSimMarginal (trace : TreeSimTrace C E) : Prop :=
  ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput),
    𝒟[Prod.fst <$> trace top tree D A x z Z] =
      𝒟[(simulateQ (streamWorld prims D)
        (treeRealGame K circuits settings top tree D A x z Z)).run' (∅, ∅)]

/-- No instrumentation hypothesis is needed for the concrete trace. -/
theorem treeSim_trace_marginal (events : TreeSimEvents C E) :
    TreeSimMarginal prims K circuits settings (treeSimTrace prims K circuits settings events) := by
  intro top tree D A x z Z
  unfold treeSimTrace
  simp only [Functor.map_map]
  rw [treeSim_log_erase]

/-- The remaining whole-ceremony relation, with the real instrumentation and
the simulator's actual program fixed. The right experiment explicitly contains
the shared-cache dealer prefix, dummy seeds, the T0 shift, and the distinguisher.
The round obligations in `treeSim_executeRounds` are intended to discharge it. -/
def TreeSimStreamCoupling (events : TreeSimEvents C E) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    RelTriple (treeSimTrace prims K circuits settings events top tree D A
      (dealtKeys parameter seeds pairs) z Z)
      (treeSimStreamIdealRun prims K circuits settings top tree D A parameter seeds pairs z Z)
      (fun a b => (a.2.1 = true ∨ a.2.2 = true) ∨ (a.1 = true ↔ b = true))

/-! The concrete round handler, retaining the actual real transcript. -/

abbrev TreeSimState (C : Committee) := (HashCache C × HiddenCache C) × TreeSimLog C

/-- Logging as state makes the actual transcript available to the round
invariant and to a sticky union of bad events. -/
def treeSimLoggedWorld (D : C.Coalition) : QueryImpl (WorldSpec C) (StateT (TreeSimState C) ProbComp) :=
  fun t => StateT.mk fun s =>
    (fun r => (r.1, r.2, s.2 ++ [⟨t, r.1⟩])) <$> (streamWorld prims D t).run s.1

/-- The stateful log and the writer log are exactly the same instrumentation,
including an existing prefix and both final caches. -/
theorem treeSimLoggedWorld_run {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (cache : HashCache C × HiddenCache C) (log : TreeSimLog C) :
    (simulateQ (treeSimLoggedWorld prims D) p).run (cache, log) =
      (fun r => (r.1.1, r.2, log ++ r.1.2)) <$>
        (simulateQ ((streamWorld prims D).withTraceAppend (fun t u => ([⟨t, u⟩] : TreeSimLog C))) p).run.run cache := by
  induction p using OracleComp.inductionOn generalizing cache log with
  | pure a => simp [StateT.run_pure, WriterT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, treeSimLoggedWorld, StateT.run_bind,
      StateT.run_mk, QueryImpl.withTraceAppend_apply, WriterT.run_bind, WriterT.run_liftM,
      WriterT.run_tell, StateT.run_map, map_bind, bind_map_left,
      pure_bind, bind_assoc, Functor.map_map, ih]
    simp [List.append_assoc]

/-- Every supported execution extends the actual transcript, including adaptive queries. -/
theorem treeSimLoggedWorld_prefix {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (s : TreeSimState C)
    (r : α × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) :
    s.2 <+: r.2.2 := by
  rw [treeSimLoggedWorld_run] at hr
  simp only [support_map, Set.mem_image] at hr
  obtain ⟨a, _, rfl⟩ := hr
  exact ⟨a.1.2, rfl⟩

/-- The exact query log of a finite hidden-stream table. -/
def treeSimHiddenLog {n : ℕ} (addr : Fin n → HiddenAddress C) (vals : Fin n → Bit) : TreeSimLog C :=
  List.ofFn fun i => ⟨.inr (.inr (.inr ((addr i).1.1, (addr i).1.2, (addr i).2))), vals i⟩

/-- Drawing a table retains its precise answers in the real transcript as
well as the resulting hidden cache. This also allows repeated cached reads. -/
theorem treeSim_hiddenDraws_log (D : C.Coalition) {n : ℕ} (addr : Fin n → HiddenAddress C)
    (cache : HashCache C × HiddenCache C) (log : TreeSimLog C) :
    (simulateQ (treeSimLoggedWorld prims D) (hiddenDraws addr)).run (cache, log) =
      (fun r => (r.1, r.2, log ++ treeSimHiddenLog addr r.1)) <$>
        (simulateQ (streamWorld prims D) (hiddenDraws addr)).run cache := by
  have query (x : HiddenAddress C) (cache : HashCache C × HiddenCache C) (log : TreeSimLog C) :
      (simulateQ (treeSimLoggedWorld prims D) (hiddenQuery x)).run (cache, log) =
        (fun r => (r.1, r.2, log ++ [⟨.inr (.inr (.inr (x.1.1, x.1.2, x.2))), r.1⟩])) <$>
          (simulateQ (streamWorld prims D) (hiddenQuery x)).run cache := by
    unfold hiddenQuery
    erw [simulateQ_spec_query, simulateQ_spec_query]
    rfl
  induction n generalizing cache log with
  | zero => simp [hiddenDraws, Concrete.sequenceFin, StateT.run_pure, treeSimHiddenLog]
  | succ n ih =>
    simp only [hiddenDraws] at ih ⊢
    simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind,
      StateT.run_pure, query, bind_map_left, map_bind, ih]
    simp [treeSimHiddenLog, List.ofFn_succ, List.append_assoc]

/-- Related private caches have the same populated addresses and translated answers.
The shift is fixed before the coupled run; it may be zero on earlier labels. -/
def TreeSimHiddenRel (δ : HiddenAddress C → Bit) (c₁ c₂ : HiddenCache C) : Prop :=
  ∀ x, c₂ x = (fun b => b + δ x) <$> c₁ x

/-- Empty caches satisfy every fixed translation. -/
theorem treeSim_hiddenRel_empty (δ : HiddenAddress C → Bit) : TreeSimHiddenRel δ ∅ ∅ := by
  intro x
  rfl

/-- A translation may be extended adaptively on unread addresses. Previously
cached answers keep their existing translation; no resampling is needed. -/
theorem treeSim_hiddenRel_extend (δ ε : HiddenAddress C → Bit) {c₁ c₂ : HiddenCache C}
    (hc : TreeSimHiddenRel δ c₁ c₂) (fresh : ∀ x, (c₁ x).isSome → ε x = 0) :
    TreeSimHiddenRel (δ + ε) c₁ c₂ := by
  intro x
  rw [hc x]
  cases hx : c₁ x with
  | none => rfl
  | some b =>
    have hε := fresh x (by simp [hx])
    simp [Pi.add_apply, hε]

/-- Caching a related answer preserves the relation at every other address. -/
theorem treeSim_hiddenRel_update (δ : HiddenAddress C → Bit) {c₁ c₂ : HiddenCache C}
    (hc : TreeSimHiddenRel δ c₁ c₂) (x : HiddenAddress C) (b : Bit) :
    TreeSimHiddenRel δ (c₁.cacheQuery x b) (c₂.cacheQuery x (b + δ x)) := by
  intro y
  by_cases hy : y = x
  · subst y
    simp
  · simpa only [QueryCache.cacheQuery_of_ne _ _ hy] using hc y

/-- One lazy hidden-stream read couples under translation whether it is fresh
or cached. Both runs update the same address, and keep their public caches. -/
theorem treeSim_hiddenQuery_mixed (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (x : HiddenAddress C) (hidden : Hidden D x.1.1)
    (h₁ h₂ : HashCache C) (c₁ c₂ : HiddenCache C) (hc : TreeSimHiddenRel δ c₁ c₂) :
    RelTriple
      ((simulateQ (streamWorld prims D) (hiddenQuery x)).run (h₁, c₁))
      ((simulateQ (streamWorld prims D) (hiddenQuery x)).run (h₂, c₂))
      (fun a b => b.1 = a.1 + δ x ∧ a.2.1 = h₁ ∧ b.2.1 = h₂ ∧
        TreeSimHiddenRel δ a.2.2 b.2.2) := by
  have hc' := hc x
  unfold hiddenQuery
  erw [simulateQ_spec_query]
  simp only [streamWorld, hidden, if_true, StateT.run_mk]
  change RelTriple
    ((fun r : Bit × HiddenCache C => (r.1, h₁, r.2)) <$>
      ((HiddenAddress C →ₒ Bit).randomOracle x).run c₁)
    ((fun r : Bit × HiddenCache C => (r.1, h₂, r.2)) <$>
      ((HiddenAddress C →ₒ Bit).randomOracle x).run c₂) _
  cases hx : c₁ x with
  | some v =>
    rw [hx] at hc'
    change c₂ x = some (v + δ x) at hc'
    erw [QueryImpl.withCaching_run_some _ hx, QueryImpl.withCaching_run_some _ hc']
    simp only [map_pure]
    exact relTriple_pure_pure ⟨rfl, rfl, rfl, hc⟩
  | none =>
    rw [hx] at hc'
    change c₂ x = none at hc'
    erw [QueryImpl.withCaching_run_none _ hx, QueryImpl.withCaching_run_none _ hc']
    simp only [Functor.map_map]
    apply relTriple_map
    exact relTriple_uniformSample_bij (AddGroup.addRight_bijective (δ x)) _
      (fun v => ⟨rfl, rfl, rfl, treeSim_hiddenRel_update δ hc x v⟩)

/-- Lift the uniform table shift to the actual handlers, retaining both
updated caches and the complete real query log. -/
theorem treeSim_hiddenTable_shift (D : C.Coalition) {n : ℕ} (addr : Fin n → HiddenAddress C)
    (ha : Function.Injective addr) (hh : ∀ i, Hidden D (addr i).1.1)
    (h₁ h₂ : HashCache C) (c₁ c₂ : HiddenCache C) (log : TreeSimLog C)
    (hc₁ : ∀ i, c₁ (addr i) = none) (hc₂ : ∀ i, c₂ (addr i) = none) (δ : Fin n → Bit) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (hiddenDraws addr)).run ((h₁, c₁), log))
      ((simulateQ (streamWorld prims D) (hiddenDraws addr)).run (h₂, c₂))
      (fun a b => b.1 = a.1 + δ ∧
        a.2.1 = (h₁, cacheFin addr a.1 c₁) ∧ b.2 = (h₂, cacheFin addr b.1 c₂) ∧
        a.2.2 = log ++ treeSimHiddenLog addr a.1) := by
  rw [treeSim_hiddenDraws_log]
  have h : RelTriple
      ((fun r => (r.1, r.2, log ++ treeSimHiddenLog addr r.1)) <$>
        (simulateQ (streamWorld prims D) (hiddenDraws addr)).run (h₁, c₁))
      (id <$> (simulateQ (streamWorld prims D) (hiddenDraws addr)).run (h₂, c₂))
      (fun a b => b.1 = a.1 + δ ∧
        a.2.1 = (h₁, cacheFin addr a.1 c₁) ∧ b.2 = (h₂, cacheFin addr b.1 c₂) ∧
        a.2.2 = log ++ treeSimHiddenLog addr a.1) := by
    apply relTriple_map
    apply relTriple_post_mono (streamWorld_fresh_rel prims D addr ha hh h₁ h₂ c₁ c₂ hc₁ hc₂ δ)
    intro a b hab
    exact ⟨hab.1, hab.2.1, hab.2.2, rfl⟩
  simpa only [id_map] using h

/-- The actual positions used for a term's bits at label ρ and stream index idx. -/
def treeSimPivotAddress (T : C.Term) (seed : HashOutput) (ρ idx : ℕ) {n : ℕ} (g : Fin n) : HiddenAddress C :=
  ((.term T, seed), ρ, idx, g.val)

/-- The T₀ translation on real stream queries. Both caches and the real log
are retained, so later repeated reads see the coupled values. -/
theorem treeSim_pivot_stream (D : C.Coalition) (T₀ : C.Term) (hT : lackedTerm D.1 = some T₀)
    (seed : HashOutput) (ρ idx : ℕ) {n : ℕ}
    (h₁ h₂ : HashCache C) (c₁ c₂ : HiddenCache C) (log : TreeSimLog C)
    (hc₁ : ∀ g : Fin n, c₁ (treeSimPivotAddress T₀ seed ρ idx g) = none)
    (hc₂ : ∀ g : Fin n, c₂ (treeSimPivotAddress T₀ seed ρ idx g) = none) (δ : Fin n → Bit) :
    let addr := treeSimPivotAddress T₀ seed ρ idx (n := n)
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (hiddenDraws addr)).run ((h₁, c₁), log))
      ((simulateQ (streamWorld prims D) (hiddenDraws addr)).run (h₂, c₂))
      (fun a b => b.1 = a.1 + δ ∧
        a.2.1 = (h₁, cacheFin addr a.1 c₁) ∧ b.2 = (h₂, cacheFin addr b.1 c₂) ∧
        a.2.2 = log ++ treeSimHiddenLog addr a.1) := by
  apply treeSim_hiddenTable_shift prims D _ _ _ h₁ h₂ c₁ c₂ log hc₁ hc₂ δ
  · intro i j hij
    exact Fin.ext (congrArg (fun a : HiddenAddress C => a.2.2.2) hij)
  · intro g
    exact main_lacked_unknown D T₀ hT

/-- Erase the log but retain both caches, from every initial transcript. -/
theorem treeSimLoggedWorld_erase {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (cache : HashCache C × HiddenCache C) (log : TreeSimLog C) :
    (fun r => (r.1, r.2.1)) <$> (simulateQ (treeSimLoggedWorld prims D) p).run (cache, log) =
      (simulateQ (streamWorld prims D) p).run cache := by
  have h := congrArg (fun m => m.run cache)
    (QueryImpl.fst_map_run_withTraceAppend (streamWorld prims D)
      (fun t u => ([⟨t, u⟩] : TreeSimLog C)) p)
  rw [treeSimLoggedWorld_run]
  simpa only [StateT.run_map, Functor.map_map] using h

/-- Adversary initialization has exactly the same joint state and hash-cache
marginal as its ordinary local execution. -/
theorem treeSimLoggedWorld_start {α : Type} (D : C.Coalition)
    (p : OracleComp (LocalSpec C) α) (h : HashCache C) (log : TreeSimLog C) :
    (fun r => (r.1, r.2.1.1)) <$>
      (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run ((h, ∅), log) =
      (simulateQ (localAnswer prims) p).run h := by
  have e := congrArg (fun p => (fun r => (r.1, r.2.1)) <$> p)
    (treeSimLoggedWorld_erase prims D (worldRoles.adversary p) (h, ∅) log)
  simpa [treeSim_stream_adversary, onHash, StateT.run_mk, Functor.map_map] using e

/-- The actual real phase and distinguisher, carrying the existing transcript. -/
def treeSimRealFinish (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (state : A.State) (s : TreeSimState C) :
    ProbComp (Bool × TreeSimLog C) :=
  (fun r => (r.1, r.2.2)) <$>
    (simulateQ (treeSimLoggedWorld prims D) (do
      let out ← executePhase worldRoles D A noFunctionality (ceremonyFuel circuits settings) state
        (fun i => ceremony K circuits settings i (x i) top tree)
      worldRoles.adversary (Z out))).run s

/-- The prefix is shared literally: dealer, then the actual adversary start,
with its real transcript and the hash cache left by both computations. -/
def treeSimCommonPrefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux) :
    ProbComp ((Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C)) := do
  let (dealt, h) ← (simulateQ (localAnswer prims)
    (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))).run ∅
  let start ← (simulateQ (treeSimLoggedWorld prims D)
    (worldRoles.adversary (A.start (corruptInputs D (dealtKeys parameter seeds pairs)) z))).run ((h, ∅), [])
  pure (dealt, start)

/-- Factor the ghost real execution at the end of the common prefix. -/
theorem treeSimGhostRun_prefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    treeSimGhostRun prims D
      (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))
      (treeRealGame K circuits settings top tree D A (dealtKeys parameter seeds pairs) z Z) =
    (do
      let p ← treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z
      (fun r => (p.1, r)) <$> treeSimRealFinish prims K circuits settings top tree D A
        (dealtKeys parameter seeds pairs) Z p.2.1 p.2.2) := by
  unfold treeSimCommonPrefix treeSimRealFinish treeSimGhostRun
  simp only [StateT.run'_eq, StateT.run_bind, onHash, StateT.run_mk, bind_map_left,
    StateT.run_pure, map_bind, map_pure, bind_assoc, pure_bind, Functor.map_map]
  apply bind_congr
  intro d
  have h := congrArg (fun p => (fun r => (d.1, r.1, r.2.2)) <$> p)
    (treeSimLoggedWorld_run prims D
      (treeRealGame K circuits settings top tree D A (dealtKeys parameter seeds pairs) z Z) (d.2, ∅) [])
  simpa only [treeRealGame, distinguish, realExecution, simulateQ_bind, StateT.run_bind,
    bind_assoc, map_bind, Functor.map_map, List.nil_append, bind_pure_comp] using h.symm

/-- The ideal execution has the same concrete prefix after erasing only
its auxiliary real log. In particular, initialization has no simulation error. -/
theorem treeSimDealerFirstIdeal_prefix (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) :
    treeSimDealerFirstIdeal prims K circuits settings top tree D A parameter seeds pairs z Z =
    (do
      let p ← treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z
      (treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z p.2.1 p.1).run' p.2.2.1.1) := by
  unfold treeSimDealerFirstIdeal treeSimCommonPrefix
  simp only [StateT.run'_eq, StateT.run_bind, bind_assoc, pure_bind, map_bind]
  apply bind_congr
  intro d
  rw [← treeSimLoggedWorld_start prims D _ d.2 []]
  simp only [bind_map_left]

/-- Equality coupling retaining reachability of the shared prefix. -/
private theorem treeSim_refl_support {α : Type} (p : ProbComp α) :
    RelTriple p p (fun a b => a ∈ support p ∧ a = b) := by
  refine relTriple_iff_relWP.2 ⟨_root_.SPMF.Coupling.refl (𝒟[p]), fun z hz => ?_⟩
  obtain ⟨a, ha, rfl⟩ : ∃ a ∈ support (𝒟[p]), (a, a) = z := by
    simpa [_root_.SPMF.Coupling.refl, support_pure] using hz
  exact ⟨(mem_support_evalDist_iff _ _).1 ha, rfl⟩

/-- A local adversarial computation cannot change the private stream cache,
even when its sampling and hash calls are recorded in the real log. -/
theorem treeSim_local_private {α : Type} (D : C.Coalition) (p : OracleComp (LocalSpec C) α)
    (h : HashCache C) (c : HiddenCache C) (log : TreeSimLog C)
    (r : α × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run ((h, c), log))) :
    r.2.1.2 = c := by
  have hm : (r.1, r.2.1) ∈ support
      ((fun r => (r.1, r.2.1)) <$>
        (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run ((h, c), log)) := by
    rw [support_map]
    exact ⟨r, hr, rfl⟩
  rw [treeSimLoggedWorld_erase, treeSim_stream_adversary] at hm
  simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hm
  obtain ⟨out, _, heq⟩ := hm
  exact (congrArg (fun x => x.2.2) heq).symm

/-- Equal views and a common hash cache couple the full local adversarial
computation, while preserving two possibly different private stream caches. -/
theorem treeSim_local_coupling {α : Type} (D : C.Coalition) (p : OracleComp (LocalSpec C) α)
    (h : HashCache C) (c₁ c₂ : HiddenCache C) (log : TreeSimLog C) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run ((h, c₁), log))
      ((simulateQ (streamWorld prims D) (worldRoles.adversary p)).run (h, c₂))
      (fun a b => a.1 = b.1 ∧ a.2.1.1 = b.2.1 ∧ a.2.1.2 = c₁ ∧ b.2.2 = c₂) := by
  have e := congrArg (fun p => (fun r => (r.1, r.2.1, c₂)) <$> p)
    (treeSimLoggedWorld_erase prims D (worldRoles.adversary p) (h, c₁) log)
  simp only [treeSim_stream_adversary, onHash, StateT.run_mk, Functor.map_map] at e
  have hmap : (simulateQ (streamWorld prims D) (worldRoles.adversary p)).run (h, c₂) =
      (fun a => (a.1, a.2.1.1, c₂)) <$>
        (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run ((h, c₁), log) := by
    simpa only [treeSim_stream_adversary, onHash, StateT.run_mk] using e.symm
  rw [hmap]
  have hr : RelTriple
      (id <$> (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run ((h, c₁), log))
      ((fun a => (a.1, a.2.1.1, c₂)) <$>
        (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run ((h, c₁), log))
      (fun a b => a.1 = b.1 ∧ a.2.1.1 = b.2.1 ∧ a.2.1.2 = c₁ ∧ b.2.2 = c₂) := by
    apply relTriple_map
    apply relTriple_post_mono (treeSim_refl_support _)
    rintro a _ ⟨ha, rfl⟩
    exact ⟨rfl, rfl, treeSim_local_private prims D p h c₁ log a ha, rfl⟩
  simpa only [id_map] using hr

/-- The public hash cache agrees; the private caches are translated. The real
log remains the actual log maintained by its handler. -/
def TreeSimStreamRel (δ : HiddenAddress C → Bit) (a : TreeSimState C)
    (b : HashCache C × HiddenCache C) : Prop :=
  a.1.1 = b.1 ∧ TreeSimHiddenRel δ a.1.2 b.2

/-- A visible read may itself sample the stream key. Coupling the actual
`prgAnswer` handles this first read as well as subsequent cached reads. -/
theorem treeSim_visibleQuery_mixed (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (x : HiddenAddress C) (visible : ¬ Hidden D x.1.1)
    (h : HashCache C) (c₁ c₂ : HiddenCache C) (log : TreeSimLog C)
    (hc : TreeSimHiddenRel δ c₁ c₂) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (hiddenQuery x)).run ((h, c₁), log))
      ((simulateQ (streamWorld prims D) (hiddenQuery x)).run (h, c₂))
      (fun a b => a.1 = b.1 ∧ TreeSimStreamRel δ a.2 b.2) := by
  unfold hiddenQuery
  erw [simulateQ_spec_query, simulateQ_spec_query]
  simp only [treeSimLoggedWorld, streamWorld, visible, if_false, onHash, localAnswer,
    QueryImpl.add_apply_inr]
  simp only [StateT.run_mk, Functor.map_map]
  change RelTriple
    ((fun r : Bit × HashCache C => (r.1, (r.2, c₁),
      log ++ [⟨.inr (.inr (.inr (x.1.1, x.1.2, x.2))), r.1⟩])) <$>
      (prgAnswer prims (x.1.1, x.1.2, x.2)).run h)
    ((fun r : Bit × HashCache C => (r.1, r.2, c₂)) <$>
      (prgAnswer prims (x.1.1, x.1.2, x.2)).run h) _
  apply relTriple_map
  apply relTriple_post_mono (relTriple_refl _)
  rintro a b rfl
  exact ⟨rfl, rfl, hc⟩

/-- Every PRG query preserves the mixed-cache relation. Hidden answers are
translated, visible answers agree, and the real query is logged exactly once. -/
theorem treeSim_prgQuery_mixed (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (x : HiddenAddress C) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (hiddenQuery x)).run a)
      ((simulateQ (streamWorld prims D) (hiddenQuery x)).run b)
      (fun u v => v.1 = u.1 + δ x ∧ TreeSimStreamRel δ u.2 v.2) := by
  rcases a with ⟨⟨h₁, c₁⟩, log⟩
  rcases b with ⟨h₂, c₂⟩
  rcases hs with ⟨rfl, hc⟩
  by_cases hidden : Hidden D x.1.1
  · have logged : (simulateQ (treeSimLoggedWorld prims D) (hiddenQuery x)).run ((h₁, c₁), log) =
        (fun r => (r.1, r.2, log ++ [⟨.inr (.inr (.inr (x.1.1, x.1.2, x.2))), r.1⟩])) <$>
          (simulateQ (streamWorld prims D) (hiddenQuery x)).run (h₁, c₁) := by
      unfold hiddenQuery
      erw [simulateQ_spec_query, simulateQ_spec_query]
      rfl
    rw [logged]
    rw [← id_map ((simulateQ (streamWorld prims D) (hiddenQuery x)).run (h₁, c₂))]
    apply relTriple_map
    apply relTriple_post_mono (treeSim_hiddenQuery_mixed prims D δ x hidden h₁ h₁ c₁ c₂ hc)
    intro u v huv
    exact ⟨huv.1, huv.2.1.trans huv.2.2.1.symm, huv.2.2.2⟩
  · apply relTriple_post_mono (treeSim_visibleQuery_mixed prims D δ x hidden h₁ c₁ c₂ log hc)
    intro u v huv
    exact ⟨by rw [hδ x hidden, add_zero]; exact huv.1.symm, huv.2⟩

/-- An entire block may mix fresh, repeated, hidden and visible addresses.
The relation is threaded through the real query order, without ghost reads. -/
theorem treeSim_draws_mixed (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) {n : ℕ} (addr : Fin n → HiddenAddress C)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (hiddenDraws addr)).run a)
      ((simulateQ (streamWorld prims D) (hiddenDraws addr)).run b)
      (fun u v => v.1 = u.1 + (fun i => δ (addr i)) ∧ TreeSimStreamRel δ u.2 v.2) := by
  induction n generalizing a b with
  | zero =>
    simp only [hiddenDraws, Concrete.sequenceFin, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨Subsingleton.elim _ _, hs⟩
  | succ n ih =>
    simp only [hiddenDraws] at ih ⊢
    simp only [Concrete.sequenceFin, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
    apply relTriple_bind (treeSim_prgQuery_mixed prims D δ hδ (addr 0) a b hs)
    intro u v huv
    apply relTriple_bind (ih (fun i => addr i.succ) u.2 v.2 huv.2)
    intro us vs hus
    apply relTriple_pure_pure
    refine ⟨?_, hus.2⟩
    funext i
    cases i using Fin.cases with
    | zero => exact huv.1
    | succ i => exact congrFun hus.1 i

/-- A translated table followed by a rushing local response. The real result
still contains its actual transcript; the postcondition relates the replies
and translated caches needed by the next round. -/
theorem treeSim_hiddenTable_rushing {V α : Type} (D : C.Coalition) {n : ℕ}
    (addr : Fin n → HiddenAddress C) (ha : Function.Injective addr) (hh : ∀ i, Hidden D (addr i).1.1)
    (h : HashCache C) (c₁ c₂ : HiddenCache C) (log : TreeSimLog C)
    (hc₁ : ∀ i, c₁ (addr i) = none) (hc₂ : ∀ i, c₂ (addr i) = none) (δ : Fin n → Bit)
    (view₁ view₂ : (Fin n → Bit) → V) (hview : ∀ vals, view₁ vals = view₂ (vals + δ))
    (answer : V → OracleComp (LocalSpec C) α) :
    RelTriple
      (do let r ← (simulateQ (treeSimLoggedWorld prims D) (hiddenDraws addr)).run ((h, c₁), log)
          (fun a => (r.1, a)) <$>
            (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary (answer (view₁ r.1)))).run r.2)
      (do let r ← (simulateQ (streamWorld prims D) (hiddenDraws addr)).run (h, c₂)
          (fun b => (r.1, b)) <$>
            (simulateQ (streamWorld prims D) (worldRoles.adversary (answer (view₂ r.1)))).run r.2)
      (fun a b => b.1 = a.1 + δ ∧ a.2.1 = b.2.1 ∧ a.2.2.1.1 = b.2.2.1 ∧
        a.2.2.1.2 = cacheFin addr a.1 c₁ ∧ b.2.2.2 = cacheFin addr b.1 c₂) := by
  apply relTriple_bind (treeSim_hiddenTable_shift prims D addr ha hh h h c₁ c₂ log hc₁ hc₂ δ)
  intro a b hab
  have hstate : a.2 = ((h, cacheFin addr a.1 c₁), log ++ treeSimHiddenLog addr a.1) :=
    Prod.ext hab.2.1 hab.2.2.2
  rw [hstate, hab.2.2.1, hab.1, hview]
  apply relTriple_map
  apply relTriple_post_mono (treeSim_local_coupling prims D (answer (view₂ (a.1 + δ))) h
    (cacheFin addr a.1 c₁) (cacheFin addr (a.1 + δ) c₂) (log ++ treeSimHiddenLog addr a.1))
  intro x y hxy
  exact ⟨rfl, hxy⟩

/-- `sequenceFin` and the protocol's list traversal use the same draw order. -/
theorem treeSim_sequenceFin_mapM {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    {n : ℕ} (f : Fin n → m α) :
    List.ofFn <$> Concrete.sequenceFin f = (List.finRange n).mapM f := by
  induction n with
  | zero => simp [Concrete.sequenceFin, List.finRange]
  | succ n ih =>
    simp only [Concrete.sequenceFin, List.finRange_succ, List.mapM_cons, List.mapM_map,
      map_bind, map_pure, List.ofFn_succ]
    rw [← ih]
    simp only [bind_map_left, pure_bind]
    rfl

/-- The actual `List.range` traversal of a PRG block is the same finite table. -/
theorem treeSim_range_mapM {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    (n : ℕ) (f : ℕ → m α) :
    (List.range n).mapM f = List.ofFn <$> Concrete.sequenceFin (fun g : Fin n => f g.val) := by
  rw [treeSim_sequenceFin_mapM]
  have hr : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem
    · simp [List.finRange]
    · intro i h₁ h₂
      simp [List.finRange]
  rw [← hr, List.mapM_map]
  rfl

/-- Run a finite list of already-cached computations in its actual order. -/
private theorem treeSim_mapM_cached {α β σ : Type} (f : α → StateT σ ProbComp β)
    (values : α → β) (xs : List α) (state : σ)
    (h : ∀ x ∈ xs, (f x).run state = pure (values x, state)) :
    (xs.mapM f).run state = pure (xs.map values, state) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, h x (by simp), pure_bind]
    rw [ih (fun y hy => h y (by simp [hy]))]
    simp

/-- A real `prgBits` query uses exactly the hidden-stream address of the
corresponding finite-table entry. -/
theorem treeSim_prgBit_query (name : KeyName C) (key : HashOutput) (ρ idx g : ℕ) :
    free (liftComp (query (spec := RoSpec C) (.inr (name, key, ρ, idx, g)) :
      OracleComp (RoSpec C) Bit) (LocalSpec C)) = hiddenQuery ((name, key), ρ, idx, g) := by
  simp [free, liftComp, hiddenQuery]
  erw [simulateQ_spec_query]
  rfl

/-- The protocol's actual bit block is a finite family of the same stream queries. -/
theorem treeSim_prgBits_table (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ) :
    free (liftComp (prgBits name key ρ idx count) (LocalSpec C)) =
      (fun vals g => (List.ofFn vals).getD g 0) <$>
        hiddenDraws (fun g : Fin count => ((name, key), ρ, idx, g.val)) := by
  unfold prgBits
  simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, keygen_liftComp_mapM]
  have hm : free ((List.range count).mapM fun g =>
      liftComp (query (spec := RoSpec C) (.inr (name, key, ρ, idx, g)) :
        OracleComp (RoSpec C) Bit) (LocalSpec C)) =
      (List.range count).mapM (fun g => hiddenQuery ((name, key), ρ, idx, g)) := by
    unfold free
    erw [simulateQ_list_mapM]
    congr 1
  erw [hm]
  rw [treeSim_range_mapM]
  erw [bind_map_left]
  rfl

/-- The mask on a real bit block is zero beyond its requested length. -/
def treeSimBitShift (δ : HiddenAddress C → Bit) (name : KeyName C) (key : HashOutput)
    (ρ idx count : ℕ) : ℕ → Bit := fun g => if g < count then δ ((name, key), ρ, idx, g) else 0

/-- The actual `prgBits` block couples with no populated-cache assumption.
Fresh and cached reads, visible stream-key sampling and the real log are retained. -/
theorem treeSim_prgBits_mixed (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (prgBits name key ρ idx count) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (prgBits name key ρ idx count) (LocalSpec C)))).run b)
      (fun u v => v.1 = u.1 + treeSimBitShift δ name key ρ idx count ∧ TreeSimStreamRel δ u.2 v.2) := by
  rw [treeSim_prgBits_table]
  simp only [simulateQ_map, StateT.run_map]
  apply relTriple_map
  apply relTriple_post_mono (treeSim_draws_mixed prims D δ hδ
    (fun g : Fin count => ((name, key), ρ, idx, g.val)) a b hs)
  intro u v huv
  refine ⟨?_, huv.2⟩
  funext g
  rw [huv.1]
  by_cases hg : g < count
  · simp [treeSimBitShift, List.getD_eq_getElem?_getD, hg]
  · simp [treeSimBitShift, List.getD_eq_getElem?_getD, hg]

/-- Thread a state relation through the actual list traversal, retaining each
input-dependent output translation and the complete final state. -/
private theorem treeSim_mapM_shift {ι α σ₁ σ₂ : Type}
    (f₁ : ι → StateT σ₁ ProbComp α) (f₂ : ι → StateT σ₂ ProbComp α)
    (shift : ι → α → α) (I : σ₁ → σ₂ → Prop) (xs : List ι)
    (step : ∀ i ∈ xs, ∀ s₁ s₂, I s₁ s₂ →
      RelTriple ((f₁ i).run s₁) ((f₂ i).run s₂)
        (fun u v => v.1 = shift i u.1 ∧ I u.2 v.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : I s₁ s₂) :
    RelTriple ((xs.mapM f₁).run s₁) ((xs.mapM f₂).run s₂)
      (fun u v => u.1.length = xs.length ∧ v.1 = List.zipWith shift xs u.1 ∧ I u.2 v.2) := by
  induction xs generalizing s₁ s₂ with
  | nil =>
    simp only [List.mapM_nil, StateT.run_pure]
    exact relTriple_pure_pure ⟨rfl, rfl, hs⟩
  | cons i xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure]
    apply relTriple_bind (step i (by simp) s₁ s₂ hs)
    intro u v huv
    apply relTriple_bind (ih (fun j hj => step j (by simp [hj])) u.2 v.2 huv.2)
    intro us vs hus
    apply relTriple_pure_pure
    exact ⟨by simp [hus.1], by simp [List.zipWith, huv.1, hus.2.1], hus.2.2⟩

/-- Reading a translated list at a valid index retains the pointwise relation. -/
private theorem treeSim_getD_zipWith {ι α : Type} (shift : ι → α → α)
    (xs : List ι) (ys : List α) (hlen : ys.length = xs.length)
    (i : ℕ) (hi : i < xs.length) (default : α) :
    (List.zipWith shift xs ys).getD i default = shift xs[i] (ys.getD i default) := by
  have hy : i < ys.length := by omega
  have hz : i < (List.zipWith shift xs ys).length := by simp [hlen, hi]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hz,
    List.getElem?_eq_getElem hy, Option.getD_some, List.getElem_zipWith]

/-- Interpret a list of protocol oracle computations in its original order. -/
private theorem treeSim_mapM_ro {m : Type → Type} [Monad m] [LawfulMonad m] {α β : Type}
    (impl : QueryImpl (WorldSpec C) m) (xs : List α) (f : α → OracleComp (RoSpec C) β) :
    simulateQ impl (free (liftComp (xs.mapM f) (LocalSpec C))) =
      xs.mapM (fun x => simulateQ impl (free (liftComp (f x) (LocalSpec C)))) := by
  rw [keygen_liftComp_mapM]
  unfold free
  erw [simulateQ_list_mapM, simulateQ_list_mapM]

/-- The translation on the PRSS output respects unheld terms and the diagonal pair. -/
def treeSimPrssShift (δ : HiddenAddress C → Bit) (ctx : Context C) (ρ idx count : ℕ) : PrssOutput C Bit :=
  (fun T => if ctx.self ∈ C.holders T then treeSimBitShift δ (.term T) (ctx.prss.term T) ρ idx count else 0,
    fun j => if hj : j = ctx.self then 0 else
      treeSimBitShift δ (.pair (C.pairOf ctx.self j (Ne.symm hj))) (ctx.prss.pair j) ρ idx count)

/-- Per-address translations add at the actual PRSS boundary. -/
theorem treeSim_prssShift_add (δ ε : HiddenAddress C → Bit) (ctx : Context C) (ρ idx count : ℕ) :
    treeSimPrssShift (δ + ε) ctx ρ idx count =
      treeSimPrssShift δ ctx ρ idx count + treeSimPrssShift ε ctx ρ idx count := by
  apply Prod.ext
  · funext T g
    by_cases ht : ctx.self ∈ C.holders T <;> by_cases hg : g < count <;>
      simp [treeSimPrssShift, treeSimBitShift, ht, hg]
  · funext j g
    by_cases hj : j = ctx.self <;> by_cases hg : g < count <;>
      simp [treeSimPrssShift, treeSimBitShift, hj, hg]

/-- Earlier translations have no effect on a new labelled block. -/
theorem treeSim_prssShift_zero (δ : HiddenAddress C → Bit) (ctx : Context C) (ρ idx count : ℕ)
    (hz : ∀ name key g, g < count → δ ((name, key), ρ, idx, g) = 0) :
    treeSimPrssShift δ ctx ρ idx count = 0 := by
  apply Prod.ext
  · funext T g
    by_cases ht : ctx.self ∈ C.holders T <;> by_cases hg : g < count <;>
      simp [treeSimPrssShift, treeSimBitShift, ht, hg, hz]
  · funext j g
    by_cases hj : j = ctx.self <;> by_cases hg : g < count <;>
      simp [treeSimPrssShift, treeSimBitShift, hj, hg, hz]

/-- A GS20 mask translation on one labelled block, zero on visible streams. -/
def treeSimBlockShift (D : C.Coalition) (ρ idx count : ℕ)
    (dt : C.Term → Fin count → Bit) (dp : C.Pair → Fin count → Bit)
    (x : HiddenAddress C) : Bit :=
  if Hidden D x.1.1 ∧ x.2.1 = ρ ∧ x.2.2.1 = idx then
    if hg : x.2.2.2 < count then
      match x.1.1 with
      | .parameter => 0
      | .term T => dt T ⟨x.2.2.2, hg⟩
      | .pair p => dp p ⟨x.2.2.2, hg⟩
    else 0
  else 0

theorem treeSim_blockShift_visible (D : C.Coalition) (ρ idx count : ℕ)
    (dt : C.Term → Fin count → Bit) (dp : C.Pair → Fin count → Bit)
    (x : HiddenAddress C) (hx : ¬ Hidden D x.1.1) :
    treeSimBlockShift D ρ idx count dt dp x = 0 := by
  simp [treeSimBlockShift, hx]

private theorem treeSim_hidden_pair (D : C.Coalition) (i j : C.Party) (h : i ≠ j) :
    Hidden D (.pair (C.pairOf i j h)) ↔ i ∉ D.1 ∧ j ∉ D.1 := by
  unfold Committee.pairOf
  split_ifs <;> simp [Hidden, and_comm]

/-- The handler-level translation is exactly the GS20 per-party mask translation. -/
theorem treeSim_prssShift_block (D : C.Coalition) (ctx : Context C) (hi : ctx.self ∉ D.1)
    (ρ idx count : ℕ) (dt : C.Term → Fin count → Bit) (dp : C.Pair → Fin count → Bit) :
    treeSimPrssShift (treeSimBlockShift D ρ idx count dt dp) ctx ρ idx count =
      frandShare D count 0 0 dt dp ctx.self := by
  apply Prod.ext
  · funext T g
    by_cases held : ctx.self ∈ C.holders T
    · by_cases known : KnownTo D.1 T <;> by_cases hg : g < count <;>
        simp [treeSimPrssShift, treeSimBitShift, treeSimBlockShift, frandShare,
          held, Hidden, known, hg]
    · simp [treeSimPrssShift, frandShare, held]
  · funext j g
    by_cases hj : j = ctx.self
    · subst j
      simp [treeSimPrssShift, frandShare]
    · by_cases hc : j ∈ D.1 <;> by_cases hg : g < count <;>
        simp [treeSimPrssShift, treeSimBitShift, treeSimBlockShift, frandShare,
          hj, Ne.symm hj, treeSim_hidden_pair, hi, hc, hg]

/-- The GS20 peer translation at an actual stream address. -/
def treeSimPeerShift (D : C.Coalition) (T₀ : C.Term) (p : C.Party)
    (ρ idx count : ℕ) (v : C.Party → ℕ → Bit) (w : C.Term → Fin count → Bit) :
    HiddenAddress C → Bit :=
  treeSimBlockShift D ρ idx count (termShift K D T₀ p v w)
    (pairShift p (pairDelta K D T₀ p v w))

/-- The concrete GS20 masks cancel the honest input on every corrupt-visible
filled term. Thus the actual peer prefix needs no abstract balance assumption. -/
theorem treeSim_peerShift_balance (D : C.Coalition) {T₀ : C.Term} {p : C.Party}
    (hp : Pivot K D T₀ p) (ctx : Context C) (hi : ctx.self ∉ D.1)
    (hk : KnownTo D.1 (K.filled ctx.self)) (ρ idx count : ℕ)
    (v : C.Party → ℕ → Bit) (w : C.Term → Fin count → Bit) (g : ℕ) (hg : g < count) :
    reshareU K ctx
      (treeSimPrssShift (treeSimPeerShift K D T₀ p ρ idx count v w) ctx ρ idx count).1
      (treeSimPrssShift (treeSimPeerShift K D T₀ p ρ idx count v w) ctx ρ idx count).2
      (fun _ => 0) g = v ctx.self g := by
  unfold treeSimPeerShift
  rw [treeSim_prssShift_block D ctx hi]
  change reshareU K (localContext ctx.self)
    (frandShare D count 0 0 (termShift K D T₀ p v w)
      (pairShift p (pairDelta K D T₀ p v w)) ctx.self).1
    (frandShare D count 0 0 (termShift K D T₀ p v w)
      (pairShift p (pairDelta K D T₀ p v w)) ctx.self).2 (fun _ => 0) g = _
  rw [reshareU_frandShare K D 0 0 _ _ (fun _ _ => 0)]
  have he := uVal_termShift K D (R := Bit) 0 0 0 0 T₀ hp.hidden p hp.honest
    hp.filled hp.owner v w ctx.self hi (fun h => hp.hidden (h ▸ hk)) g hg
  simp only [zero_add, targetShift, if_pos hk, Pi.zero_apply, add_zero] at he
  have hz : uVal K D (c := count) (0 : Shares C Bit) 0 0 0 (fun _ _ => 0) ctx.self g = 0 := by
    simp [uVal, pairVal, randVal]
  rw [hz] at he
  simp only [uVal] at he ⊢
  have htwo := bit_add_self (v ctx.self g)
  linear_combination he - htwo

/-- The same GS20 translation handles arbitrary related peer inputs, including
the simulator's nonzero local shares inherited from earlier gadgets. -/
theorem treeSim_peerShift_balance_inputs (D : C.Coalition) {T₀ : C.Term} {p : C.Party}
    (hp : Pivot K D T₀ p) (ctx : Context C) (hi : ctx.self ∉ D.1)
    (hk : KnownTo D.1 (K.filled ctx.self)) (ρ idx count : ℕ)
    (v₁ v₂ : C.Party → ℕ → Bit) (w : C.Term → Fin count → Bit) (g : ℕ) (hg : g < count) :
    reshareU K ctx
      (treeSimPrssShift (treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) w) ctx ρ idx count).1
      (treeSimPrssShift (treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) w) ctx ρ idx count).2
      (v₂ ctx.self) g = v₁ ctx.self g := by
  have h := treeSim_peerShift_balance K D hp ctx hi hk ρ idx count (v₁ - v₂) w g hg
  simp only [reshareU, Pi.sub_apply] at h ⊢
  linear_combination h

/-- With `w = 0`, the GS20 translated masks put the entire honest input sum
at the lacked term. This is the translation needed by the ceremony simulator. -/
theorem treeSim_termVal_pivot (D : C.Coalition) {T₀ : C.Term} {p : C.Party}
    (hp : Pivot K D T₀ p) (count : ℕ) (v : C.Party → ℕ → Bit)
    (i : C.Party) (T : C.Term) (g : ℕ) (hg : g < count) :
    termVal K D (bitCodec (E := E)) 0 0
      (termShift K D T₀ p v (0 : C.Term → Fin count → Bit))
      (pairShift p (pairDelta K D T₀ p v (0 : C.Term → Fin count → Bit)))
      v (fun _ _ => none) i T g =
      if T = T₀ then ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g else 0 := by
  have hzero : ∀ i T, termVal K D (bitCodec (E := E)) (c := count) 0 0 0 0
      (fun _ _ => 0) (fun _ _ => none) i T g = 0 := by
    intro i T
    simp [termVal, uVal, randVal, pairVal, bitCodec, Msg.bitAt]
  have hother : ∀ T, T ≠ T₀ → termVal K D (bitCodec (E := E)) 0 0
      (termShift K D T₀ p v (0 : C.Term → Fin count → Bit))
      (pairShift p (pairDelta K D T₀ p v (0 : C.Term → Fin count → Bit)))
      v (fun _ _ => none) i T g = 0 := by
    intro T hT
    have h := termVal_shift K D (bitCodec (E := E)) 0 0 0 0 hp v
      (0 : C.Term → Fin count → Bit) (fun _ _ => none) i T hT g hg
    simpa only [zero_add, hzero, Pi.zero_apply, ite_self, add_zero] using h
  by_cases hT : T = T₀
  · subst T
    rw [if_pos rfl]
    have hsum := sum_termVal K D (bitCodec (E := E)) 0 0
      (termShift K D T₀ p v (0 : C.Term → Fin count → Bit))
      (pairShift p (pairDelta K D T₀ p v (0 : C.Term → Fin count → Bit)))
      v (fun _ _ => none) (fun _ => i) g
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T₀)] at hsum
    simp only [Finset.sum_eq_zero (fun T hT => hother T (Finset.ne_of_mem_erase hT)), add_zero] at hsum
    simpa [advVal, bitCodec, Msg.bitAt] using hsum
  · rw [if_neg hT]
    exact hother T hT

/-- The value of a peer term before restricting it to its honest holders. The
base masks may be arbitrary; no independence or consistency assumption is used. -/
def treeSimPeerValue (D : C.Coalition) (ctx : C.Party → Context C)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (sent : C.Party → Mail C E) (i : C.Party) (T : C.Term) (g : ℕ) : Bit :=
  if T ∈ filledTerms K then
    ∑ j ∈ Finset.univ.filter (K.filled · = T),
      if j ∈ D.1 then Msg.bitAt (sent j i) g else reshareU K (ctx j) (rnd j).1 (rnd j).2 (v j) g
  else (rnd i).1 T g

/-- Normalize the actual peer inbox, with arbitrary honest masks and arbitrary
malicious messages, to its per-term value. -/
theorem treeSim_reshareZ_value (D : C.Coalition) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit) (count : ℕ)
    (sent : C.Party → Mail C E) (i : C.Party) (hi : i ∉ D.1) (T : C.Term) (g : ℕ) :
    reshareZ K (ctx i) (bitCodec (E := E)) (rnd i).1 (rnd i).2 (v i) count
      (fun j => if j ∈ D.1 then sent j i else
        reshareOut K (ctx j) bitCodec (rnd j).1 (rnd j).2 (v j) count i) T g =
      if i ∉ C.holders T ∨ count ≤ g then 0 else treeSimPeerValue K D ctx rnd v sent i T g := by
  unfold reshareZ treeSimPeerValue
  rw [self i hi]
  split_ifs with hbound hfilled
  · rfl
  · push Not at hbound
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjT := (Finset.mem_filter.mp hj).2
    by_cases hji : j = i
    · subst j
      simp [hi]
    · simp only [if_neg hji]
      by_cases hjD : j ∈ D.1
      · simp [hjD, bitCodec]
      · simp only [if_neg hjD, reshareOut, self j hjD]
        rw [if_pos ⟨Ne.symm hji, hjT ▸ hbound.1⟩]
        exact vector_getD count _ g hbound.2
  · rfl

/-- Translating the masks changes a peer term by the corresponding zero-base
execution. Characteristic two fixes the sign of the input difference. Corrupt
messages are unchanged, including malformed and recipient-specific ones. -/
theorem treeSim_peer_value_shift (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (count : ℕ) (dt : C.Term → Fin count → Bit) (dp : C.Pair → Fin count → Bit)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit)
    (masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0 dt dp i)
    (v₁ v₂ : C.Party → ℕ → Bit) (sent : C.Party → Mail C E)
    (i : C.Party) (hi : i ∉ D.1) (T : C.Term) (held : i ∈ C.holders T)
    (g : ℕ) (hg : g < count) :
    treeSimPeerValue K D ctx₂ rnd₂ v₂ sent i T g = treeSimPeerValue K D ctx₁ rnd₁ v₁ sent i T g +
      termVal K D (bitCodec (E := E)) 0 0 dt dp (v₁ - v₂) (fun _ _ => none) i T g := by
  have hu : ∀ j, j ∉ D.1 → reshareU K (ctx₂ j) (rnd₂ j).1 (rnd₂ j).2 (v₂ j) g =
      reshareU K (ctx₁ j) (rnd₁ j).1 (rnd₁ j).2 (v₁ j) g +
        uVal K D 0 0 dt dp (v₁ - v₂) j g := by
    intro j hj
    have he := reshareU_frandShare K D (R := Bit) 0 0 dt dp (v₁ - v₂) j g
    rw [masks j hj]
    simp only [reshareU, self₁ j hj, self₂ j hj, localContext, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib] at he ⊢
    have htwo := bit_add_self (v₁ j g - v₂ j g)
    linear_combination he - htwo
  unfold treeSimPeerValue termVal
  by_cases hf : T ∈ filledTerms K
  · simp only [if_pos hf, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hc : j ∈ D.1
    · simp [hc, bitCodec, Msg.bitAt]
    · simp only [if_neg hc]
      exact hu j hc
  · simp only [if_neg hf, masks i hi, Prod.fst_add, Pi.add_apply]
    rw [frandShare_fst D (0 : Shares C Bit) 0 dt dp i T g held]

/-- The `T₀` shift on an operator's stored sharing, respecting held terms and
the gadget length. Unlike an opening, an internal sharing stores zero elsewhere. -/
def treeSimHeldShift (D : C.Coalition) (i : C.Party) (count : ℕ)
    (difference : ℕ → Bit) (v : Shares C Bit) : Shares C Bit := fun T g =>
  v T g + if i ∈ C.holders T ∧ g < count ∧ lackedTerm D.1 = some T then difference g else 0

/-- The actual peer outputs differ only at `T₀`, for arbitrary base masks and
arbitrary common malicious messages. This holds before inspecting the abort bit. -/
theorem treeSim_reshareZ_pivot (D : C.Coalition) {T₀ : C.Term} {p : C.Party}
    (hp : Pivot K D T₀ p) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit)
    (masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0
      (termShift K D T₀ p (v₁ - v₂) (0 : C.Term → Fin count → Bit))
      (pairShift p (pairDelta K D T₀ p (v₁ - v₂) (0 : C.Term → Fin count → Bit))) i)
    (sent : C.Party → Mail C E) (i : C.Party) (hi : i ∉ D.1) :
    reshareZ K (ctx₂ i) bitCodec (rnd₂ i).1 (rnd₂ i).2 (v₂ i) count
      (fun j => if j ∈ D.1 then sent j i else
        reshareOut K (ctx₂ j) bitCodec (rnd₂ j).1 (rnd₂ j).2 (v₂ j) count i) =
    treeSimHeldShift D i count (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g)
      (reshareZ K (ctx₁ i) bitCodec (rnd₁ i).1 (rnd₁ i).2 (v₁ i) count
        (fun j => if j ∈ D.1 then sent j i else
          reshareOut K (ctx₁ j) bitCodec (rnd₁ j).1 (rnd₁ j).2 (v₁ j) count i)) := by
  funext T g
  rw [treeSimHeldShift, treeSim_reshareZ_value K D ctx₁ self₁ (hi := hi),
    treeSim_reshareZ_value K D ctx₂ self₂ (hi := hi)]
  by_cases hb : i ∉ C.holders T ∨ count ≤ g
  · simp only [if_pos hb]
    have hn : ¬ (i ∈ C.holders T ∧ g < count ∧ lackedTerm D.1 = some T) := by
      intro h
      rcases hb with hb | hb
      · exact hb h.1
      · omega
    simp [hn]
  · have held : i ∈ C.holders T := by tauto
    have hg : g < count := by omega
    simp only [if_neg hb]
    rw [treeSim_peer_value_shift K D ctx₁ ctx₂ self₁ self₂ count _ _ rnd₁ rnd₂ masks
      v₁ v₂ sent i hi T held g hg, treeSim_termVal_pivot K D hp count (v₁ - v₂) i T g hg]
    simp [held, hg, hp.lacked, eq_comm]

/-- Histories agree outside `T₀`; at a held `T₀` they differ by one common
bit vector of the exact recorded length. This records the shift needed by the check. -/
def TreeSimHistoryRel (D : C.Coalition) (i : C.Party) (difference : List Bit)
    (h₁ h₂ : C.Term → List Bit) : Prop :=
  ∀ T, if i ∈ C.holders T ∧ lackedTerm D.1 = some T then
    (h₁ T).length = difference.length ∧ h₂ T = List.zipWith (· + ·) (h₁ T) difference
  else h₂ T = h₁ T

/-- The history relation starts from the actual empty transcript. -/
theorem treeSimHistoryRel_empty (D : C.Coalition) (i : C.Party) :
    TreeSimHistoryRel D i [] (fun _ => []) (fun _ => []) := by
  intro T
  split_ifs <;> simp

/-- Every corrupt-visible term has identical recorded histories. -/
theorem treeSimHistoryRel_known (D : C.Coalition) (i : C.Party) (difference : List Bit)
    (h₁ h₂ : C.Term → List Bit) (h : TreeSimHistoryRel D i difference h₁ h₂)
    (T : C.Term) (known : KnownTo D.1 T) : h₂ T = h₁ T := by
  have hn : lackedTerm D.1 ≠ some T := fun hp => main_lacked_unknown D T hp known
  simpa only [TreeSimHistoryRel, hn, and_false, if_false] using h T

/-- The new history difference records precisely the positions recorded by
`recordPeer` at `T₀`, rather than every requested position unconditionally. -/
def treeSimHistoryAppend (T₀ : C.Term) (count : ℕ) (past : List Bit) (difference : ℕ → Bit) : List Bit :=
  past ++ ((List.range count).filter fun g => (filler K .peer T₀ g).isSome).map difference

/-- Recording the translated peer output preserves the exact history shift. -/
theorem treeSim_recordPeer_shift (D : C.Coalition) (T₀ : C.Term) (hT₀ : lackedTerm D.1 = some T₀)
    (i : C.Party) (count : ℕ) (past : List Bit) (difference : ℕ → Bit)
    (h₁ h₂ : C.Term → List Bit) (hh : TreeSimHistoryRel D i past h₁ h₂)
    (z₁ z₂ : Shares C Bit) (hz : z₂ = treeSimHeldShift D i count difference z₁) :
    TreeSimHistoryRel D i (treeSimHistoryAppend K T₀ count past difference)
      (recordPeer K bitCodec i h₁ z₁ count) (recordPeer K bitCodec i h₂ z₂ count) := by
  intro T
  have h := hh T
  by_cases ht : i ∈ C.holders T ∧ lackedTerm D.1 = some T
  · have hEq : T = T₀ := Option.some.inj (ht.2.symm.trans hT₀)
    subst T
    rw [if_pos ht] at h ⊢
    simp only [recordPeer, if_pos ht.1, bitCodec, Function.comp_def, ← List.map_eq_flatMap]
    constructor
    · simp [treeSimHistoryAppend, h.1]
    · rw [treeSimHistoryAppend, List.zipWith_append h.1, h.2, List.zipWith_map, List.zipWith_self]
      congr 1
      apply List.map_congr_left
      intro g hg
      have hg' := List.mem_range.mp (List.mem_filter.mp hg).1
      simp [hz, treeSimHeldShift, ht.1, hT₀, hg']
  · rw [if_neg ht] at h ⊢
    by_cases held : i ∈ C.holders T
    · have hn : lackedTerm D.1 ≠ some T := fun hp => ht ⟨held, hp⟩
      have he : z₂ T = z₁ T := by
        funext g
        simp [hz, treeSimHeldShift, hn]
      simp [recordPeer, held, h, he]
    · simp [recordPeer, held, h]

/-- The local run state carries the same label and tag, and a precise common
translation of the hidden history, rather than just equal history lengths. -/
def TreeSimRunStateRel (D : C.Coalition) (i : C.Party) (difference : List Bit)
    (s₁ s₂ : RunState C) : Prop :=
  s₁.label = s₂.label ∧ s₁.tag = s₂.tag ∧ TreeSimHistoryRel D i difference s₁.history s₂.history

/-- `Rerand` routes the difference of replicated sharings through the honest
owner of `T₀`; its honest additive input difference is the incoming shift. -/
theorem treeSim_rerand_difference (D : C.Coalition) {T₀ : C.Term} {p : C.Party}
    (hp : Pivot K D T₀ p) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (count : ℕ) (difference : ℕ → Bit) (x₁ x₂ : C.Party → Shares C Bit)
    (hx : ∀ i, i ∉ D.1 → x₂ i = treeSimHeldShift D i count difference (x₁ i)) (g : ℕ) :
    ∑ i ∈ Finset.univ.filter (· ∉ D.1),
      (ownerSum K (ctx₁ i) (x₁ i) g - ownerSum K (ctx₂ i) (x₂ i) g) =
      if g < count then difference g else 0 := by
  have howner : K.owner T₀ ∉ D.1 := fun h => hp.hidden ⟨_, h, K.owner_held T₀⟩
  have he : ∀ i, i ∉ D.1 → ownerSum K (ctx₂ i) (x₂ i) g = ownerSum K (ctx₁ i) (x₁ i) g +
      if K.owner T₀ = i then (if g < count then difference g else 0) else 0 := by
    intro i hi
    simp only [ownerSum, self₁ i hi, self₂ i hi]
    have hh : ∀ T ∈ Finset.univ.filter (K.owner · = i), x₂ i T g = x₁ i T g +
        if T = T₀ then (if g < count then difference g else 0) else 0 := by
      intro T hT
      have held : i ∈ C.holders T := (Finset.mem_filter.mp hT).2 ▸ K.owner_held T
      by_cases ht : T = T₀
      · subst T
        simp [hx i hi, treeSimHeldShift, hp.lacked, held]
      · simp [hx i hi, treeSimHeldShift, hp.lacked, held, ht, Ne.symm ht]
    rw [Finset.sum_congr rfl hh, Finset.sum_add_distrib]
    simp
  have hd : ∀ i, i ∉ D.1 → ownerSum K (ctx₁ i) (x₁ i) g - ownerSum K (ctx₂ i) (x₂ i) g =
      if K.owner T₀ = i then (if g < count then difference g else 0) else 0 := by
    intro i hi
    rw [he i hi]
    simp [CharTwo.neg_eq]
  rw [Finset.sum_congr rfl (fun i hi => hd i (Finset.mem_filter.mp hi).2)]
  simp [howner]

/-- Internal share shifts only use positions inside the gadget. -/
theorem treeSimHeldShift_truncate (D : C.Coalition) (i : C.Party) (count : ℕ)
    (difference : ℕ → Bit) (v : Shares C Bit) :
    treeSimHeldShift D i count (fun g => if g < count then difference g else 0) v =
      treeSimHeldShift D i count difference v := by
  funext T g
  by_cases hg : g < count <;> simp [treeSimHeldShift, hg]

/-- The recorded difference likewise ignores positions beyond the gadget. -/
theorem treeSimHistoryAppend_truncate (T₀ : C.Term) (count : ℕ) (past : List Bit) (difference : ℕ → Bit) :
    treeSimHistoryAppend K T₀ count past (fun g => if g < count then difference g else 0) =
      treeSimHistoryAppend K T₀ count past difference := by
  unfold treeSimHistoryAppend
  congr 1
  exact List.map_congr_left fun g hg => if_pos (List.mem_range.mp (List.mem_filter.mp hg).1)

/-- All term reads in one actual PRSS invocation, including mixed cache states. -/
theorem treeSim_termDraws_mixed (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx : Context C) (ρ idx count : ℕ)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (termDraws ctx (bitCodec (E := E)) ρ idx count) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (termDraws ctx (bitCodec (E := E)) ρ idx count) (LocalSpec C)))).run b)
      (fun u v => u.1.length = C.terms.length ∧
        v.1 = List.zipWith (fun T r => r + (treeSimPrssShift δ ctx ρ idx count).1 T) C.terms u.1 ∧
        TreeSimStreamRel δ u.2 v.2) := by
  unfold termDraws
  rw [treeSim_mapM_ro, treeSim_mapM_ro]
  apply treeSim_mapM_shift
  · intro T _ s₁ s₂ hstate
    by_cases held : ctx.self ∈ C.holders T
    · simp only [if_pos held, treeSimPrssShift]
      simpa only [treeSimPrssShift, if_pos held, bitCodec] using
        treeSim_prgBits_mixed prims D δ hδ (.term T) (ctx.prss.term T) ρ idx count s₁ s₂ hstate
    · simp only [if_neg held, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      exact ⟨by simp [treeSimPrssShift, held], hstate⟩
  · exact hs

/-- All pair reads use the same mixed-cache invariant, including a first visible stream key. -/
theorem treeSim_pairDraws_mixed (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx : Context C) (ρ idx count : ℕ)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (pairDraws ctx (bitCodec (E := E)) ρ idx count) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (pairDraws ctx (bitCodec (E := E)) ρ idx count) (LocalSpec C)))).run b)
      (fun u v => u.1.length = C.parties.length ∧
        v.1 = List.zipWith (fun j r => r + (treeSimPrssShift δ ctx ρ idx count).2 j) C.parties u.1 ∧
        TreeSimStreamRel δ u.2 v.2) := by
  unfold pairDraws
  rw [treeSim_mapM_ro, treeSim_mapM_ro]
  apply treeSim_mapM_shift
  · intro j _ s₁ s₂ hstate
    by_cases hj : j = ctx.self
    · simp only [dif_pos hj, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      exact ⟨by simp [treeSimPrssShift, hj], hstate⟩
    · simp only [dif_neg hj]
      simpa only [treeSimPrssShift, dif_neg hj, bitCodec] using
        treeSim_prgBits_mixed prims D δ hδ (.pair (C.pairOf ctx.self j (Ne.symm hj)))
          (ctx.prss.pair j) ρ idx count s₁ s₂ hstate
  · exact hs

/-- The full actual bit PRSS invocation couples in mixed cache states. This
includes fresh first holders, repeated holders, visible keys and the real transcript. -/
theorem treeSim_prssBits_mixed (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx : Context C) (ρ idx count : ℕ)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (prssDraw ctx (bitCodec (E := E)) ρ idx count) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (prssDraw ctx (bitCodec (E := E)) ρ idx count) (LocalSpec C)))).run b)
      (fun u v => v.1.1 = u.1.1 + (treeSimPrssShift δ ctx ρ idx count).1 ∧
        v.1.2 = u.1.2 + (treeSimPrssShift δ ctx ρ idx count).2 ∧ TreeSimStreamRel δ u.2 v.2) := by
  unfold prssDraw
  simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  apply relTriple_bind (treeSim_termDraws_mixed prims D δ hδ ctx ρ idx count a b hs)
  intro r₁ r₂ hr
  apply relTriple_bind (treeSim_pairDraws_mixed prims D δ hδ ctx ρ idx count r₁.2 r₂.2 hr.2.2)
  intro z₁ z₂ hz
  apply relTriple_pure_pure
  refine ⟨?_, ?_, hz.2.2⟩
  · funext T
    dsimp only [Prod.fst, Pi.add_apply]
    rw [hr.2.1, treeSim_getD_zipWith _ _ _ hr.1 _ (List.idxOf_lt_length_of_mem (mem_terms T))]
    simp only [List.getElem_idxOf]
  · funext j
    dsimp only [Prod.fst, Prod.snd, Pi.add_apply]
    rw [hz.2.1, treeSim_getD_zipWith _ _ _ hz.1 j.val (by simpa [Committee.parties] using j.isLt)]
    simp [Committee.parties]

/-- A PRSS invocation writes only its own label in the private stream cache. -/
def TreeSimCacheFrame (ρ : ℕ) (before after : HiddenCache C) : Prop :=
  ∀ x, x.2.1 ≠ ρ → after x = before x

/-- No hidden draw has populated this or a later label. -/
def TreeSimFutureEmpty (ρ : ℕ) (cache : HiddenCache C) : Prop :=
  ∀ x, ρ ≤ x.2.1 → cache x = none

/-- Earlier translations are zero at this and every later label. -/
def TreeSimFutureZero (ρ : ℕ) (δ : HiddenAddress C → Bit) : Prop :=
  ∀ x, ρ ≤ x.2.1 → δ x = 0

theorem treeSim_futureEmpty_after {ρ : ℕ} {a b : HiddenCache C}
    (h : TreeSimFutureEmpty ρ a) (frame : TreeSimCacheFrame ρ a b) :
    TreeSimFutureEmpty (ρ + 1) b := by
  intro x hx
  rw [frame x (by omega)]
  exact h x (by omega)

theorem treeSim_futureEmpty_related {ρ : ℕ} {δ : HiddenAddress C → Bit} {a b : HiddenCache C}
    (h : TreeSimFutureEmpty ρ a) (related : TreeSimHiddenRel δ a b) : TreeSimFutureEmpty ρ b := by
  intro x hx
  rw [related x, h x hx]
  rfl

/-- Unread future labels justify any adapted block translation at the next label. -/
theorem treeSim_futureEmpty_block (D : C.Coalition) (ρ idx count : ℕ)
    (dt : C.Term → Fin count → Bit) (dp : C.Pair → Fin count → Bit)
    (cache : HiddenCache C) (h : TreeSimFutureEmpty ρ cache)
    (x : HiddenAddress C) (hx : (cache x).isSome) :
    treeSimBlockShift D ρ idx count dt dp x = 0 := by
  by_cases hl : x.2.1 = ρ
  · have he := h x (by omega)
    simp [he] at hx
  · simp [treeSimBlockShift, hl]

theorem treeSim_futureZero_extend (D : C.Coalition) (ρ idx count : ℕ)
    (dt : C.Term → Fin count → Bit) (dp : C.Pair → Fin count → Bit)
    (past : HiddenAddress C → Bit) (h : TreeSimFutureZero ρ past) :
    TreeSimFutureZero (ρ + 1) (past + treeSimBlockShift D ρ idx count dt dp) := by
  intro x hx
  have hn : x.2.1 ≠ ρ := by omega
  simp [Pi.add_apply, h x (by omega), treeSimBlockShift, hn]

private theorem treeSim_state_mapM_preserves {ι α σ β : Type}
    (q : σ → β) (f : ι → StateT σ ProbComp α) (xs : List ι)
    (step : ∀ i ∈ xs, ∀ s r, r ∈ support ((f i).run s) → q r.2 = q s)
    (s : σ) (r : List α × σ) (hr : r ∈ support ((xs.mapM f).run s)) : q r.2 = q s := by
  induction xs generalizing s r with
  | nil =>
    have heq : r = ([], s) := by simpa using hr
    subst r
    rfl
  | cons i xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr
    exact (ih (fun j hj => step j (by simp [hj])) u.2 v hv).trans (step i (by simp) s u hu)

private theorem treeSim_state_sequenceFin_preserves {α σ β : Type} {n : ℕ}
    (q : σ → β) (f : Fin n → StateT σ ProbComp α)
    (step : ∀ i s r, r ∈ support ((f i).run s) → q r.2 = q s)
    (s : σ) (r : (Fin n → α) × σ)
    (hr : r ∈ support ((Concrete.sequenceFin f).run s)) : q r.2 = q s := by
  induction n generalizing s with
  | zero =>
    have heq : r = (Fin.elim0, s) := by simpa [Concrete.sequenceFin] using hr
    subst r
    rfl
  | succ n ih =>
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr
    exact (ih (fun i => f i.succ) (fun i => step i.succ) u.2 v hv).trans (step 0 s u hu)

/-- A single stream read leaves every other address untouched, including
visible-key reads, which only access the hash cache. -/
theorem treeSim_hiddenQuery_frame (D : C.Coalition) (x y : HiddenAddress C) (hne : y ≠ x)
    (s : HashCache C × HiddenCache C) (r : Bit × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (hiddenQuery x)).run s)) :
    r.2.2 y = s.2 y := by
  unfold hiddenQuery at hr
  erw [simulateQ_spec_query] at hr
  by_cases hh : Hidden D x.1.1
  · simp only [streamWorld, hh, if_true] at hr
    change r ∈ support ((fun u : Bit × HiddenCache C => (u.1, s.1, u.2)) <$>
      ((HiddenAddress C →ₒ Bit).randomOracle x).run s.2) at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨u, hu, rfl⟩ := hr
    change u ∈ support (((HiddenAddress C →ₒ Bit).randomOracle x).run s.2) at hu
    cases hx : s.2 x with
    | some v =>
      erw [QueryImpl.withCaching_run_some _ hx] at hu
      have heq : u = (v, s.2) := by simpa using hu
      subst u
      rfl
    | none =>
      erw [QueryImpl.withCaching_run_none _ hx] at hu
      simp only [support_map, Set.mem_image] at hu
      obtain ⟨v, _, rfl⟩ := hu
      exact QueryCache.cacheQuery_of_ne s.2 v hne
  · simp only [streamWorld, hh, if_false, onHash] at hr
    change r ∈ support ((fun u : Bit × HashCache C => (u.1, u.2, s.2)) <$>
      (localAnswer prims (.inr (.inr (x.1.1, x.1.2, x.2)))).run s.1) at hr
    simp only [support_map, Set.mem_image] at hr
    obtain ⟨u, _, rfl⟩ := hr
    rfl

/-- The actual finite bit block cannot populate a future (or older) label. -/
theorem treeSim_prgBits_frame (D : C.Coalition) (name : KeyName C) (key : HashOutput)
    (ρ idx count : ℕ) (s : HashCache C × HiddenCache C)
    (r : (ℕ → Bit) × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prgBits name key ρ idx count) (LocalSpec C)))).run s)) :
    TreeSimCacheFrame ρ s.2 r.2.2 := by
  rw [treeSim_prgBits_table] at hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  intro y hy
  simp only [hiddenDraws, simulateQ_sequenceFin] at hu
  apply treeSim_state_sequenceFin_preserves (fun t : HashCache C × HiddenCache C => t.2 y) _ _ s u hu
  intro i t v hv
  exact treeSim_hiddenQuery_frame prims D _ y (fun h => hy (congrArg (fun z => z.2.1) h)) t v hv

/-- All term and pair reads of a PRSS invocation preserve
private-cache entries outside the invocation's label. -/
theorem treeSim_prssDraw_frame {R : Type} [Zero R] (D : C.Coalition)
    (codec : Codec C E R) (ctx : Context C) (ρ idx count : ℕ)
    (draw : ∀ name key a b, b ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (codec.draw name key ρ idx count) (LocalSpec C)))).run a) →
      TreeSimCacheFrame ρ a.2 b.2.2)
    (s : HashCache C × HiddenCache C) (r : PrssOutput C R × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx codec ρ idx count) (LocalSpec C)))).run s)) :
    TreeSimCacheFrame ρ s.2 r.2.2 := by
  have term : ∀ t u, u ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (termDraws ctx codec ρ idx count) (LocalSpec C)))).run t) →
      TreeSimCacheFrame ρ t.2 u.2.2 := by
    intro t u hu y hy
    unfold termDraws at hu
    rw [treeSim_mapM_ro] at hu
    apply treeSim_state_mapM_preserves (fun s : HashCache C × HiddenCache C => s.2 y) _ _ _ t u hu
    intro T _ a b hb
    by_cases held : ctx.self ∈ C.holders T
    · simp only [if_pos held] at hb
      exact draw _ _ a b hb y hy
    · simp [held, liftComp_pure, free_pure] at hb
      subst b
      rfl
  have pair : ∀ t u, u ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (pairDraws ctx codec ρ idx count) (LocalSpec C)))).run t) →
      TreeSimCacheFrame ρ t.2 u.2.2 := by
    intro t u hu y hy
    unfold pairDraws at hu
    rw [treeSim_mapM_ro] at hu
    apply treeSim_state_mapM_preserves (fun s : HashCache C × HiddenCache C => s.2 y) _ _ _ t u hu
    intro j _ a b hb
    by_cases hj : j = ctx.self
    · simp [hj, liftComp_pure, free_pure] at hb
      subst b
      rfl
    · simp only [dif_neg hj] at hb
      exact draw _ _ a b hb y hy
  unfold prssDraw at hr
  simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, support_bind, Set.mem_iUnion,
    support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨u, hu, v, hv, rfl⟩ := hr
  intro y hy
  exact (pair u.2 v hv y hy).trans (term s u hu y hy)

/-- Bit PRSS has no private-cache writes outside its current label. -/
theorem treeSim_prssBits_frame (D : C.Coalition) (ctx : Context C) (ρ idx count : ℕ)
    (s : HashCache C × HiddenCache C) (r : PrssOutput C Bit × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (bitCodec (E := E)) ρ idx count) (LocalSpec C)))).run s)) :
    TreeSimCacheFrame ρ s.2 r.2.2 :=
  treeSim_prssDraw_frame prims D bitCodec ctx ρ idx count
    (fun name key a b hb => treeSim_prgBits_frame prims D name key ρ idx count a b hb) s r hr

/-- Decoding a field block does not add any oracle queries. -/
theorem treeSim_elementDraw_frame (D : C.Coalition) (name : KeyName C) (key : HashOutput)
    (ρ idx count : ℕ) (s : HashCache C × HiddenCache C)
    (r : (ℕ → E) × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp ((elementCodec K).draw name key ρ idx count) (LocalSpec C)))).run s)) :
    TreeSimCacheFrame ρ s.2 r.2.2 := by
  simp only [elementCodec, liftComp_bind, liftComp_pure, free_bind, free_pure,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  exact treeSim_prgBits_frame prims D name key ρ idx _ s u hu

/-- Field PRSS preserves all future labels, including its unused pair draws. -/
theorem treeSim_prssElements_frame (D : C.Coalition) (ctx : Context C) (ρ idx count : ℕ)
    (s : HashCache C × HiddenCache C) (r : PrssOutput C E × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) ρ idx count) (LocalSpec C)))).run s)) :
    TreeSimCacheFrame ρ s.2 r.2.2 :=
  treeSim_prssDraw_frame prims D (elementCodec K) ctx ρ idx count
    (treeSim_elementDraw_frame prims K D · · ρ idx count) s r hr

/-- Equality of draw results lifts through a stateful list traversal. -/
private theorem treeSim_mapM_same {ι α σ₁ σ₂ : Type}
    (f₁ : ι → StateT σ₁ ProbComp α) (f₂ : ι → StateT σ₂ ProbComp α)
    (I : σ₁ → σ₂ → Prop) (xs : List ι)
    (step : ∀ i ∈ xs, ∀ a b, I a b → RelTriple ((f₁ i).run a) ((f₂ i).run b)
      (fun u z => u.1 = z.1 ∧ I u.2 z.2))
    (a : σ₁) (b : σ₂) (h : I a b) :
    RelTriple ((xs.mapM f₁).run a) ((xs.mapM f₂).run b)
      (fun u z => u.1 = z.1 ∧ I u.2 z.2) := by
  induction xs generalizing a b with
  | nil => exact relTriple_pure_pure ⟨rfl, h⟩
  | cons i xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure]
    apply relTriple_bind (step i (by simp) a b h)
    intro u z hu
    apply relTriple_bind (ih (fun j hj => step j (by simp [hj])) u.2 z.2 hu.2)
    intro v w hv
    exact relTriple_pure_pure ⟨by simp [hu.1, hv.1], hv.2⟩

/-- Field decoding preserves equality of current blocks even when earlier
labels carry a nonzero translation. No additive property of `encode` is used. -/
theorem treeSim_elementDraw_mixed (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (name : KeyName C) (key : HashOutput) (ρ idx count : ℕ)
    (block : ∀ g, δ ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp ((elementCodec K).draw name key ρ idx count) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp ((elementCodec K).draw name key ρ idx count) (LocalSpec C)))).run b)
      (fun u z => u.1 = z.1 ∧ TreeSimStreamRel δ u.2 z.2) := by
  simp only [elementCodec, liftComp_bind, liftComp_pure, free_bind, free_pure,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  apply relTriple_bind (treeSim_prgBits_mixed prims D δ visible name key ρ idx _ a b h)
  intro u z hu
  have hz : treeSimBitShift δ name key ρ idx (elementBits * count) = 0 := by
    funext g
    simp [treeSimBitShift, block]
  have he : z.1 = u.1 := by simpa only [hz, add_zero] using hu.1
  exact relTriple_pure_pure ⟨by rw [he], hu.2⟩

/-- Untranslated codec draws give identical PRSS output while retaining the
translation on older cache entries and every visible-key oracle query. -/
theorem treeSim_prssDraw_same {R : Type} [Zero R] (D : C.Coalition)
    (codec : Codec C E R) (δ : HiddenAddress C → Bit) (ctx : Context C) (ρ idx count : ℕ)
    (draw : ∀ name key a b, TreeSimStreamRel δ a b →
      RelTriple ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (codec.draw name key ρ idx count) (LocalSpec C)))).run a)
        ((simulateQ (streamWorld prims D)
        (free (liftComp (codec.draw name key ρ idx count) (LocalSpec C)))).run b)
        (fun u z => u.1 = z.1 ∧ TreeSimStreamRel δ u.2 z.2))
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : TreeSimStreamRel δ a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (prssDraw ctx codec ρ idx count) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (prssDraw ctx codec ρ idx count) (LocalSpec C)))).run b)
      (fun u z => u.1 = z.1 ∧ TreeSimStreamRel δ u.2 z.2) := by
  have term : ∀ a b, TreeSimStreamRel δ a b →
      RelTriple ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (termDraws ctx codec ρ idx count) (LocalSpec C)))).run a)
        ((simulateQ (streamWorld prims D)
        (free (liftComp (termDraws ctx codec ρ idx count) (LocalSpec C)))).run b)
        (fun u z => u.1 = z.1 ∧ TreeSimStreamRel δ u.2 z.2) := by
    intro a b hab
    unfold termDraws
    rw [treeSim_mapM_ro, treeSim_mapM_ro]
    apply treeSim_mapM_same _ _ _ _ (fun T _ s t hst => ?_) a b hab
    by_cases held : ctx.self ∈ C.holders T
    · simp only [if_pos held]
      exact draw _ _ s t hst
    · simp only [if_neg held, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨rfl, hst⟩
  have pair : ∀ a b, TreeSimStreamRel δ a b →
      RelTriple ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (pairDraws ctx codec ρ idx count) (LocalSpec C)))).run a)
        ((simulateQ (streamWorld prims D)
        (free (liftComp (pairDraws ctx codec ρ idx count) (LocalSpec C)))).run b)
        (fun u z => u.1 = z.1 ∧ TreeSimStreamRel δ u.2 z.2) := by
    intro a b hab
    unfold pairDraws
    rw [treeSim_mapM_ro, treeSim_mapM_ro]
    apply treeSim_mapM_same _ _ _ _ (fun j _ s t hst => ?_) a b hab
    by_cases hj : j = ctx.self
    · simp only [dif_pos hj, liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨rfl, hst⟩
    · simp only [dif_neg hj]
      exact draw _ _ s t hst
  unfold prssDraw
  simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  apply relTriple_bind (term a b h)
  intro r₁ r₂ hr
  apply relTriple_bind (pair r₁.2 r₂.2 hr.2)
  intro z₁ z₂ hz
  exact relTriple_pure_pure ⟨by rw [hr.1, hz.1], hz.2⟩

/-- Field PRSS at the next label needs no new shift. Earlier T₀ translations
remain in the two caches, while both worlds obtain exactly the same masks. -/
theorem treeSim_prssElements_mixed (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx : Context C) (ρ idx count : ℕ)
    (future : TreeSimFutureZero ρ δ)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : TreeSimStreamRel δ a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (prssDraw ctx (elementCodec K) ρ idx count) (LocalSpec C)))).run a)
      ((simulateQ (streamWorld prims D)
        (free (liftComp (prssDraw ctx (elementCodec K) ρ idx count) (LocalSpec C)))).run b)
      (fun u z => u.1 = z.1 ∧ TreeSimStreamRel δ u.2 z.2) :=
  treeSim_prssDraw_same prims D (elementCodec K) δ ctx ρ idx count
    (fun name key a b hab => treeSim_elementDraw_mixed prims K D δ visible name key ρ idx count
      (fun g => future ((name, key), ρ, idx, g) le_rfl) a b hab) a b h

/-- Logging does not change the private-cache footprint of actual PRSS. -/
theorem treeSim_prssBits_logged_frame (D : C.Coalition) (ctx : Context C) (ρ idx count : ℕ)
    (s : TreeSimState C) (r : PrssOutput C Bit × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prssDraw ctx (bitCodec (E := E)) ρ idx count) (LocalSpec C)))).run s)) :
    TreeSimCacheFrame ρ s.1.2 r.2.1.2 := by
  apply treeSim_prssBits_frame (E := E) prims D ctx ρ idx count s.1 (r.1, r.2.1)
  rw [← treeSimLoggedWorld_erase prims D _ s.1 s.2, support_map]
  exact ⟨r, hr, rfl⟩

/-- A finite table may be reread by every honest holder without resampling. -/
theorem treeSim_hiddenDraws_cached (D : C.Coalition) {n : ℕ}
    (addr : Fin n → HiddenAddress C) (hidden : ∀ i, Hidden D (addr i).1.1)
    (vals : Fin n → Bit) (h : HashCache C) (cache : HiddenCache C)
    (hc : ∀ i, cache (addr i) = some (vals i)) :
    (simulateQ (streamWorld prims D) (hiddenDraws addr)).run (h, cache) = pure (vals, (h, cache)) := by
  induction n with
  | zero =>
    simp only [hiddenDraws, Concrete.sequenceFin, simulateQ_pure, StateT.run_pure]
    congr 2
    exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [hiddenDraws, Concrete.sequenceFin, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure]
    rw [streamWorld_hidden_cached prims D (addr 0) (hidden 0) h cache (vals 0) (hc 0), pure_bind]
    simp only [hiddenDraws] at ih
    rw [ih (fun i => addr i.succ) (fun i => hidden i.succ) (fun i => vals i.succ) (fun i => hc i.succ), pure_bind]
    congr 2
    funext i
    cases i using Fin.cases <;> rfl

/-- Cached reads still appear in the real log. In particular this covers the
second and subsequent honest holders of a hidden PRSS term. -/
theorem treeSim_prgBits_cached_logged (D : C.Coalition) (name : KeyName C)
    (hidden : Hidden D name) (key : HashOutput) (ρ idx count : ℕ)
    (vals : Fin count → Bit) (h : HashCache C) (cache : HiddenCache C) (log : TreeSimLog C)
    (hc : ∀ g : Fin count, cache ((name, key), ρ, idx, g.val) = some (vals g)) :
    (simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (prgBits name key ρ idx count) (LocalSpec C)))).run ((h, cache), log) =
      pure ((fun g => (List.ofFn vals).getD g 0), (h, cache),
        log ++ treeSimHiddenLog (fun g : Fin count => ((name, key), ρ, idx, g.val)) vals) := by
  rw [treeSim_prgBits_table, simulateQ_map, StateT.run_map, treeSim_hiddenDraws_log,
    treeSim_hiddenDraws_cached prims D _ (fun _ => hidden) vals h cache hc]
  simp only [map_pure]

/-- A fresh actual PRG block can be translated while retaining its real transcript
and both exact final caches. The finite witnesses also specify the zero tail. -/
theorem treeSim_prgBits_shift (D : C.Coalition) (name : KeyName C)
    (hidden : Hidden D name) (key : HashOutput) (ρ idx count : ℕ)
    (h₁ h₂ : HashCache C) (c₁ c₂ : HiddenCache C) (log : TreeSimLog C)
    (hc₁ : ∀ g < count, c₁ ((name, key), ρ, idx, g) = none)
    (hc₂ : ∀ g < count, c₂ ((name, key), ρ, idx, g) = none)
    (δ : Fin count → Bit) :
    let addr := fun g : Fin count => ((name, key), ρ, idx, g.val)
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (free (liftComp (prgBits name key ρ idx count) (LocalSpec C)))).run ((h₁, c₁), log))
      ((simulateQ (streamWorld prims D)
        (free (liftComp (prgBits name key ρ idx count) (LocalSpec C)))).run (h₂, c₂))
      (fun a b => ∃ vals : Fin count → Bit,
        a.1 = (fun g => (List.ofFn vals).getD g 0) ∧
        b.1 = (fun g => (List.ofFn (vals + δ)).getD g 0) ∧
        a.2.1 = (h₁, cacheFin addr vals c₁) ∧
        b.2 = (h₂, cacheFin addr (vals + δ) c₂) ∧
        a.2.2 = log ++ treeSimHiddenLog addr vals) := by
  dsimp only
  rw [treeSim_prgBits_table]
  simp only [simulateQ_map, StateT.run_map]
  apply relTriple_map
  apply relTriple_post_mono (treeSim_hiddenTable_shift prims D
    (fun g : Fin count => ((name, key), ρ, idx, g.val))
    (fun i j hij => Fin.ext (congrArg (fun x => x.2.2.2) hij))
    (fun _ => hidden) h₁ h₂ c₁ c₂ log
    (fun g => hc₁ g.val g.isLt) (fun g => hc₂ g.val g.isLt) δ)
  intro a b hab
  exact ⟨a.1, rfl, by rw [hab.1], hab.2.1, by rw [← hab.1]; exact hab.2.2.1, hab.2.2.2⟩

/-- A visible stream reads its real cached AES key, leaving the private cache intact. -/
theorem treeSim_visibleBit_cached (D : C.Coalition) (name : KeyName C)
    (visible : ¬ Hidden D name) (key derived : HashOutput) (ρ idx g : ℕ)
    (h : HashCache C) (cache : HiddenCache C) (hk : h (.streamKey key) = some derived) :
    (simulateQ (streamWorld prims D) (hiddenQuery ((name, key), ρ, idx, g))).run (h, cache) =
      pure (prims.aes.eval (truncateHash derived) (ρ, idx, g), (h, cache)) := by
  unfold hiddenQuery
  erw [simulateQ_spec_query]
  simp only [streamWorld, visible, if_false, onHash, localAnswer, QueryImpl.add_apply_inr,
    prgAnswer, StateT.run_mk, StateT.run_bind, StateT.run_pure]
  erw [StateT.run_mk, StateT.run_bind,
    hashAnswer_run_cached prims (by rintro ⟨_, heq, _⟩; cases heq) hk]
  simp

/-- The actual PRG traversal replays any already-determined stream block. -/
private theorem treeSim_prgBits_replay (D : C.Coalition) (name : KeyName C)
    (key : HashOutput) (ρ idx count : ℕ) (values : ℕ → Bit)
    (h : HashCache C) (cache : HiddenCache C)
    (hq : ∀ g < count,
      (simulateQ (streamWorld prims D) (hiddenQuery ((name, key), ρ, idx, g))).run (h, cache) =
        pure (values g, (h, cache))) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (prgBits name key ρ idx count) (LocalSpec C)))).run (h, cache) =
      pure ((fun g => ((List.range count).map values).getD g 0), (h, cache)) := by
  unfold prgBits
  simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, keygen_liftComp_mapM]
  have hm : (simulateQ (streamWorld prims D)
      (free ((List.range count).mapM fun g =>
        liftComp (query (spec := RoSpec C) (.inr (name, key, ρ, idx, g)) :
          OracleComp (RoSpec C) Bit) (LocalSpec C)))).run (h, cache) =
        pure ((List.range count).map values, (h, cache)) := by
    unfold free
    erw [simulateQ_list_mapM, simulateQ_list_mapM]
    apply treeSim_mapM_cached
    intro g hg
    have e := hq g (List.mem_range.mp hg)
    rw [← treeSim_prgBit_query] at e
    exact e
  erw [hm, pure_bind]
  rfl

/-- Replay a hidden block without changing either cache, including unrelated entries. -/
theorem treeSim_prgBits_cached (D : C.Coalition) (name : KeyName C) (hidden : Hidden D name)
    (key : HashOutput) (ρ idx count : ℕ) (values : ℕ → Bit)
    (h : HashCache C) (cache : HiddenCache C)
    (hc : ∀ g < count, cache ((name, key), ρ, idx, g) = some (values g)) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (prgBits name key ρ idx count) (LocalSpec C)))).run (h, cache) =
      pure ((fun g => ((List.range count).map values).getD g 0), (h, cache)) :=
  treeSim_prgBits_replay prims D name key ρ idx count values h cache
    (fun g hg => streamWorld_hidden_cached prims D _ hidden h cache _ (hc g hg))

/-- A populated stream block uses the hidden table or the actual visible AES key. -/
def TreeSimStreamReady (D : C.Coalition) (name : KeyName C) (key : HashOutput)
    (ρ idx count : ℕ) (values : ℕ → Bit) (h : HashCache C) (cache : HiddenCache C) : Prop :=
  if Hidden D name then ∀ g < count, cache ((name, key), ρ, idx, g) = some (values g)
  else ∃ derived, h (.streamKey key) = some derived ∧
    ∀ g < count, values g = prims.aes.eval (truncateHash derived) (ρ, idx, g)

/-- Both visible and hidden blocks replay in the real stream world. -/
theorem treeSim_prgBits_ready (D : C.Coalition) (name : KeyName C) (key : HashOutput)
    (ρ idx count : ℕ) (values : ℕ → Bit) (h : HashCache C) (cache : HiddenCache C)
    (ready : TreeSimStreamReady prims D name key ρ idx count values h cache) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (prgBits name key ρ idx count) (LocalSpec C)))).run (h, cache) =
      pure ((fun g => ((List.range count).map values).getD g 0), (h, cache)) := by
  apply treeSim_prgBits_replay prims D name key ρ idx count values h cache
  intro g hg
  unfold TreeSimStreamReady at ready
  split_ifs at ready with hidden
  · exact streamWorld_hidden_cached prims D _ hidden h cache _ (ready g hg)
  · obtain ⟨derived, hk, hv⟩ := ready
    rw [hv g hg]
    exact treeSim_visibleBit_cached prims D name hidden key derived ρ idx g h cache hk

/-- Replaying populated term and pair blocks gives the actual PRSS output at
an honest operator, including the protocol's zero entries and indexing. -/
theorem treeSim_prssDraw_replay {R : Type} [Zero R] (D : C.Coalition)
    (ctx : Context C) (codec : Codec C E R) (ρ idx count : ℕ)
    (r : Shares C R) (Z : C.Party → ℕ → R) (cache : HashCache C × HiddenCache C)
    (ht : ∀ T, ctx.self ∈ C.holders T →
      (simulateQ (streamWorld prims D) (free (liftComp
        (codec.draw (.term T) (ctx.prss.term T) ρ idx count) (LocalSpec C)))).run cache =
        pure (r T, cache))
    (hp : ∀ j (hj : j ≠ ctx.self),
      (simulateQ (streamWorld prims D) (free (liftComp
        (codec.draw (.pair (C.pairOf ctx.self j (Ne.symm hj))) (ctx.prss.pair j) ρ idx count)
        (LocalSpec C)))).run cache = pure (Z j, cache)) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx codec ρ idx count) (LocalSpec C)))).run cache =
      pure ((fun T => if ctx.self ∈ C.holders T then r T else fun _ => 0,
        fun j => if j = ctx.self then fun _ => 0 else Z j), cache) := by
  have term : (simulateQ (streamWorld prims D)
      (free (liftComp (termDraws ctx codec ρ idx count) (LocalSpec C)))).run cache =
      pure (C.terms.map (fun T => if ctx.self ∈ C.holders T then r T else fun _ => 0), cache) := by
    unfold termDraws
    rw [keygen_liftComp_mapM]
    unfold free
    erw [simulateQ_list_mapM, simulateQ_list_mapM]
    apply treeSim_mapM_cached
    intro T _
    split_ifs with hT
    · exact ht T hT
    · simp only [liftComp_pure]
      erw [simulateQ_pure]
      rfl
  have pair : (simulateQ (streamWorld prims D)
      (free (liftComp (pairDraws ctx codec ρ idx count) (LocalSpec C)))).run cache =
      pure (C.parties.map (fun j => if j = ctx.self then fun _ => 0 else Z j), cache) := by
    unfold pairDraws
    rw [keygen_liftComp_mapM]
    unfold free
    erw [simulateQ_list_mapM, simulateQ_list_mapM]
    apply treeSim_mapM_cached
    intro j _
    split_ifs with hj
    · simp only [liftComp_pure]
      erw [simulateQ_pure]
      rfl
    · exact hp j hj
  unfold prssDraw
  simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure, term, pure_bind, pair]
  congr 2
  apply Prod.ext
  · funext T
    exact getD_terms_idxOf _ _ T
  · funext j
    exact getD_parties _ _ j

/-- The finite blocks seen by one operator, with the implementation's zero entries. -/
def treeSimPrssBits (ctx : Context C) (count : ℕ) (r : Shares C Bit)
    (Z : C.Party → ℕ → Bit) : PrssOutput C Bit :=
  (fun T => if ctx.self ∈ C.holders T then fun g => ((List.range count).map (r T)).getD g 0
      else fun _ => 0,
    fun j => if j = ctx.self then fun _ => 0 else fun g => ((List.range count).map (Z j)).getD g 0)

/-- The real bit PRSS draw follows from concrete populated-cache conditions;
no abstract distribution assumption on a whole PRSS draw remains. -/
theorem treeSim_prssBits_ready (D : C.Coalition) (ctx : Context C) (ρ idx count : ℕ)
    (r : Shares C Bit) (Z : C.Party → ℕ → Bit) (h : HashCache C) (cache : HiddenCache C)
    (ht : ∀ T, ctx.self ∈ C.holders T →
      TreeSimStreamReady prims D (.term T) (ctx.prss.term T) ρ idx count (r T) h cache)
    (hp : ∀ j (hj : j ≠ ctx.self),
      TreeSimStreamReady prims D (.pair (C.pairOf ctx.self j (Ne.symm hj)))
        (ctx.prss.pair j) ρ idx count (Z j) h cache) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (bitCodec (E := E)) ρ idx count) (LocalSpec C)))).run (h, cache) =
      pure (treeSimPrssBits ctx count r Z, (h, cache)) := by
  apply treeSim_prssDraw_replay prims D ctx (bitCodec (E := E)) ρ idx count
  · intro T hT
    exact treeSim_prgBits_ready prims D _ _ _ _ _ _ h cache (ht T hT)
  · intro j hj
    exact treeSim_prgBits_ready prims D _ _ _ _ _ _ h cache (hp j hj)

/-- Decode exactly the bit block read by `elementCodec`, including its padded tail. -/
def treeSimElementBlock (count : ℕ) (bits : ℕ → Bit) : ℕ → E := fun g =>
  K.encode.symm fun b => ((List.range (elementBits * count)).map bits).getD (elementBits * g + b) 0

/-- The field codec replays the actual contiguous bit positions. No zero-preserving
assumption on the encoding equivalence is needed. -/
theorem treeSim_elementDraw_ready (D : C.Coalition) (name : KeyName C) (key : HashOutput)
    (ρ idx count : ℕ) (bits : ℕ → Bit) (h : HashCache C) (cache : HiddenCache C)
    (ready : TreeSimStreamReady prims D name key ρ idx (elementBits * count) bits h cache) :
    (simulateQ (streamWorld prims D) (free (liftComp
      ((elementCodec K).draw name key ρ idx count) (LocalSpec C)))).run (h, cache) =
      pure (treeSimElementBlock K count bits, (h, cache)) := by
  simp only [elementCodec, liftComp_bind, liftComp_pure, free_bind, free_pure,
    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [treeSim_prgBits_ready prims D name key ρ idx (elementBits * count) bits h cache ready, pure_bind]
  rfl

/-- The field PRSS output restricts the decoded blocks to the operator's held terms. -/
def treeSimPrssElements (ctx : Context C) (count : ℕ) (r : Shares C Bit)
    (Z : C.Party → ℕ → Bit) : PrssOutput C E :=
  (fun T => if ctx.self ∈ C.holders T then treeSimElementBlock K count (r T) else fun _ => 0,
    fun j => if j = ctx.self then fun _ => 0 else treeSimElementBlock K count (Z j))

/-- Concrete bit-cache conditions also discharge the complete check-field PRSS draw. -/
theorem treeSim_prssElements_ready (D : C.Coalition) (ctx : Context C) (ρ idx count : ℕ)
    (r : Shares C Bit) (Z : C.Party → ℕ → Bit) (h : HashCache C) (cache : HiddenCache C)
    (ht : ∀ T, ctx.self ∈ C.holders T →
      TreeSimStreamReady prims D (.term T) (ctx.prss.term T) ρ idx (elementBits * count) (r T) h cache)
    (hp : ∀ j (hj : j ≠ ctx.self),
      TreeSimStreamReady prims D (.pair (C.pairOf ctx.self j (Ne.symm hj)))
        (ctx.prss.pair j) ρ idx (elementBits * count) (Z j) h cache) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) ρ idx count) (LocalSpec C)))).run (h, cache) =
      pure (treeSimPrssElements K ctx count r Z, (h, cache)) := by
  apply treeSim_prssDraw_replay prims D ctx (elementCodec K) ρ idx count
  · intro T hT
    exact treeSim_elementDraw_ready prims K D _ _ _ _ _ _ h cache (ht T hT)
  · intro j hj
    exact treeSim_elementDraw_ready prims K D _ _ _ _ _ _ h cache (hp j hj)

/-- The actual suspended peer exchange, retaining the abort-aware continuation
and the history and label updates of `reshare`. -/
def treeSimPeerStep {R α : Type} [Field R] (ctx : Context C) (codec : Codec C E R)
    (rnd : PrssOutput C R) (v : ℕ → R) (count : ℕ) (st : RunState C)
    (k : Shares C R × RunState C → PartyM C E RealSpec α) : Step C E RealSpec α :=
  .wait (reshareOut K ctx codec rnd.1 rnd.2 v count) (exchangeResume fun inbox =>
    let out := reshareZ K ctx codec rnd.1 rnd.2 v count inbox
    k (out, ⟨recordPeer K codec ctx.self st.history out count, st.label + 1, st.tag⟩))

/-- The peer entry is an equality of oracle programs, before either handler
is chosen. Fresh draws, repeated cached reads and their logs are all retained. -/
theorem treeSim_peer_entry {R α : Type} [Field R] (ctx : Context C) (codec : Codec C E R)
    (idx count : ℕ) (v : ℕ → R) (st : RunState C)
    (k : Shares C R × RunState C → PartyM C E RealSpec α) :
    worldRoles.honest (advance
      ((((prssRandomness ctx codec idx count >>= fun o => reshare K ctx codec o v count).run st) >>= k).run)) =
      (fun rnd => treeSimPeerStep K ctx codec rnd v count st k) <$>
        free (liftComp (prssDraw ctx codec st.label idx count) (LocalSpec C)) := by
  rw [prssRandomness_run, bind_assoc]
  simp only [worldRoles, advance_oracleStep_bind, free_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro rnd
  rw [show rnd = (rnd.1, rnd.2) from rfl, reshare_run]
  simp only [bind_assoc, pure_bind, advance_exchange_bind, free_pure]
  rfl

/-- Populated PRSS blocks expose the real peer gadget's first round, with its
entire continuation, rather than merely its message marginal. -/
theorem treeSim_peer_start {R α : Type} [Field R] (D : C.Coalition)
    (ctx : Context C) (codec : Codec C E R) (idx count : ℕ) (v : ℕ → R)
    (st : RunState C) (k : Shares C R × RunState C → PartyM C E RealSpec α)
    (rnd : PrssOutput C R) (cache : HashCache C × HiddenCache C)
    (hdraw : (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx codec st.label idx count) (LocalSpec C)))).run cache =
      pure (rnd, cache)) :
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance ((((prssRandomness ctx codec idx count >>= fun o => reshare K ctx codec o v count).run st) >>= k).run)))).run cache =
      pure (treeSimPeerStep K ctx codec rnd v count st k, cache) := by
  rw [treeSim_peer_entry, simulateQ_map, StateT.run_map, hdraw, map_pure]

/-- The real Rerand has exactly this suspended peer round. -/
theorem treeSim_rerand_start {α : Type} (D : C.Coalition) (ctx : Context C)
    (mode : ReshareMode) (v : Shares C Bit) (count : ℕ) (st : RunState C)
    (k : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (rnd : PrssOutput C Bit) (cache : HashCache C × HiddenCache C)
    (hdraw : (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (bitCodec (E := E)) st.label 0 count) (LocalSpec C)))).run cache =
      pure (rnd, cache)) :
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance ((((realRunGadgets K ctx mode).rerand v count).run st >>= k).run)))).run cache =
      pure (treeSimPeerStep K ctx (bitCodec (E := E)) rnd (ownerSum K ctx v) count st k, cache) := by
  exact treeSim_peer_start prims K D ctx (bitCodec (E := E)) 0 count (ownerSum K ctx v) st k rnd cache hdraw

/-- The real extended multiplication uses the same peer step over the check field. -/
theorem treeSim_extendMult_start {α : Type} (D : C.Coalition) (ctx : Context C)
    (products : List (Product C E)) (st : RunState C)
    (k : Shares C E × RunState C → PartyM C E RealSpec α)
    (rnd : PrssOutput C E) (cache : HashCache C × HiddenCache C)
    (hdraw : (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) st.label 0 products.length) (LocalSpec C)))).run cache =
      pure (rnd, cache)) :
    (simulateQ (streamWorld prims D) (worldRoles.honest
      (advance ((((realCheckGadgets K ctx).extendMult products).run st >>= k).run)))).run cache =
      pure (treeSimPeerStep K ctx (elementCodec K) rnd (contextProductValues K ctx products)
        products.length st k, cache) := by
  exact treeSim_peer_start prims K D ctx (elementCodec K) 0 products.length
    (contextProductValues K ctx products) st k rnd cache hdraw

/-- Both actual collector rounds, suspended before the first exchange. -/
def treeSimCollectorStep {α : Type} (ctx : Context C) (rnd : PrssOutput C Bit)
    (v : ℕ → Bit) (count : ℕ) (st : RunState C)
    (k : Shares C Bit × RunState C → PartyM C E RealSpec α) : Step C E RealSpec α :=
  .wait (colOut1 K ctx.self rnd.1 rnd.2 v count) (exchangeResume fun inbox =>
    exchange (colOut2 K ctx.self rnd.1 rnd.2 v count inbox) >>= fun forward =>
      let out := colZ K ctx.self rnd.1 rnd.2 v count inbox forward
      k (out, ⟨recordMode K .collector ctx.self st.history out count, st.label + 1, st.tag⟩))

/-- The collector entry retains its actual PRSS queries under either handler. -/
theorem treeSim_collector_entry {α : Type} (ctx : Context C) (idx count : ℕ)
    (v : ℕ → Bit) (st : RunState C)
    (k : Shares C Bit × RunState C → PartyM C E RealSpec α) :
    worldRoles.honest (advance
      ((((prssRandomness ctx (bitCodec (E := E)) idx count >>= fun o =>
        reshareCollector K ctx o v count).run st) >>= k).run)) =
      (fun rnd => treeSimCollectorStep K ctx rnd v count st k) <$>
        free (liftComp (prssDraw ctx (bitCodec (E := E)) st.label idx count) (LocalSpec C)) := by
  rw [prssRandomness_run, bind_assoc]
  simp only [worldRoles, advance_oracleStep_bind, free_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro rnd
  rw [show rnd = (rnd.1, rnd.2) from rfl, reshareCollector_run]
  simp only [bind_assoc, pure_bind, advance_exchange_bind, free_pure]
  rfl

/-- The real collector gadget, with both abort-aware exchanges and the exact
history update, follows its populated PRSS draw. -/
theorem treeSim_collector_start {α : Type} (D : C.Coalition) (ctx : Context C)
    (idx count : ℕ) (v : ℕ → Bit) (st : RunState C)
    (k : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (rnd : PrssOutput C Bit) (cache : HashCache C × HiddenCache C)
    (hdraw : (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (bitCodec (E := E)) st.label idx count) (LocalSpec C)))).run cache =
      pure (rnd, cache)) :
    (simulateQ (streamWorld prims D) (worldRoles.honest (advance
      ((((prssRandomness ctx (bitCodec (E := E)) idx count >>= fun o =>
        reshareCollector K ctx o v count).run st) >>= k).run)))).run cache =
      pure (treeSimCollectorStep K ctx rnd v count st k, cache) := by
  rw [treeSim_collector_entry, simulateQ_map, StateT.run_map, hdraw, map_pure]

/-- Multiplication selects precisely the peer or collector continuation from
the frozen implementation. -/
theorem treeSim_mult_start {α : Type} (D : C.Coalition) (ctx : Context C)
    (mode : ReshareMode) (x y : Shares C Bit) (count : ℕ) (st : RunState C)
    (k : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (rnd : PrssOutput C Bit) (cache : HashCache C × HiddenCache C)
    (hdraw : (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (bitCodec (E := E)) st.label 0 count) (LocalSpec C)))).run cache =
      pure (rnd, cache)) :
    (simulateQ (streamWorld prims D) (worldRoles.honest (advance
      ((((realRunGadgets K ctx mode).mult x y count).run st >>= k).run)))).run cache =
      pure ((match mode with
        | .peer => treeSimPeerStep K ctx (bitCodec (E := E)) rnd (mulRep K ctx x y) count st k
        | .collector => treeSimCollectorStep K ctx rnd (mulRep K ctx x y) count st k), cache) := by
  cases mode with
  | peer =>
    exact treeSim_peer_start prims K D ctx (bitCodec (E := E)) 0 count
      (mulRep K ctx x y) st k rnd cache hdraw
  | collector =>
    exact treeSim_collector_start prims K D ctx 0 count
      (mulRep K ctx x y) st k rnd cache hdraw

/-- A concrete cache certificate suffices for the actual multiplication entry,
in both modes, with its precise suspended continuation. -/
theorem treeSim_mult_start_ready {α : Type} (D : C.Coalition) (ctx : Context C)
    (mode : ReshareMode) (x y : Shares C Bit) (count : ℕ) (st : RunState C)
    (k : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (r : Shares C Bit) (Z : C.Party → ℕ → Bit) (h : HashCache C) (cache : HiddenCache C)
    (ht : ∀ T, ctx.self ∈ C.holders T →
      TreeSimStreamReady prims D (.term T) (ctx.prss.term T) st.label 0 count (r T) h cache)
    (hp : ∀ j (hj : j ≠ ctx.self),
      TreeSimStreamReady prims D (.pair (C.pairOf ctx.self j (Ne.symm hj)))
        (ctx.prss.pair j) st.label 0 count (Z j) h cache) :
    (simulateQ (streamWorld prims D) (worldRoles.honest (advance
      ((((realRunGadgets K ctx mode).mult x y count).run st >>= k).run)))).run (h, cache) =
      pure ((match mode with
        | .peer => treeSimPeerStep K ctx (bitCodec (E := E)) (treeSimPrssBits ctx count r Z)
            (mulRep K ctx x y) count st k
        | .collector => treeSimCollectorStep K ctx (treeSimPrssBits ctx count r Z)
            (mulRep K ctx x y) count st k), (h, cache)) := by
  apply treeSim_mult_start prims K D ctx mode x y count st k
  exact treeSim_prssBits_ready prims D ctx st.label 0 count r Z h cache ht hp

/-- The actual coin opening keeps both transport abort and Shamir agreement checks. -/
def treeSimCoinStep {α : Type} (ctx : Context C) (rnd : PrssOutput C E)
    (count : ℕ) (st : RunState C)
    (k : List E × RunState C → PartyM C E RealSpec α) : Step C E RealSpec α :=
  let v := conv K ctx rnd.1
  .wait (openOut ctx.self v count) (exchangeResume fun inbox =>
    require (OpenAgreesN K ctx.self v count inbox) >>= fun _ =>
      k (vector count (openValueN K ctx.self v inbox), nextLabel st))

/-- The Coin entry retains its complete field draw before exposing the checked opening. -/
theorem treeSim_coin_entry {α : Type} (ctx : Context C) (count : ℕ) (st : RunState C)
    (k : List E × RunState C → PartyM C E RealSpec α) :
    worldRoles.honest (advance ((((realCheckGadgets K ctx).coin count).run st >>= k).run)) =
      (fun rnd => treeSimCoinStep K ctx rnd count st k) <$>
        free (liftComp (prssDraw ctx (elementCodec K) st.label 1 count) (LocalSpec C)) := by
  rw [realCoin_run, bind_assoc]
  simp only [worldRoles, advance_oracleStep_bind, free_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro rnd
  simp only [pure_bind, openSh_eqN, bind_assoc, advance_exchange_bind, free_pure]
  rfl

/-- The real Coin is the checked opening of its actual PRSS draw. -/
theorem treeSim_coin_start {α : Type} (D : C.Coalition) (ctx : Context C)
    (count : ℕ) (st : RunState C) (k : List E × RunState C → PartyM C E RealSpec α)
    (rnd : PrssOutput C E) (cache : HashCache C × HiddenCache C)
    (hdraw : (simulateQ (streamWorld prims D)
      (free (liftComp (prssDraw ctx (elementCodec K) st.label 1 count) (LocalSpec C)))).run cache =
      pure (rnd, cache)) :
    (simulateQ (streamWorld prims D) (worldRoles.honest (advance
      ((((realCheckGadgets K ctx).coin count).run st >>= k).run)))).run cache =
      pure (treeSimCoinStep K ctx rnd count st k, cache) := by
  rw [treeSim_coin_entry, simulateQ_map, StateT.run_map, hdraw, map_pure]

/-- PRSS queries depend on the shared setup keys, not on the ceremony's input seeds. -/
theorem treeSim_prssDraw_context {R : Type} [Zero R] (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (codec : Codec C E R) (ρ idx count : ℕ) :
    prssDraw ctx₁ codec ρ idx count = prssDraw ctx₂ codec ρ idx count := by
  cases ctx₁
  cases ctx₂
  cases self
  cases keys
  rfl

/-- The suspended peer steps retain the paired masks, including their translation. -/
def TreeSimPeerRel {α : Type} (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : Context C) (idx count : ℕ) (v₁ v₂ : ℕ → Bit)
    (st₁ st₂ : RunState C) (k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (s₁ s₂ : Step C E RealSpec α) : Prop :=
  ∃ r₁ r₂ : PrssOutput C Bit,
    r₂.1 = r₁.1 + (treeSimPrssShift δ ctx₁ st₁.label idx count).1 ∧
    r₂.2 = r₁.2 + (treeSimPrssShift δ ctx₁ st₁.label idx count).2 ∧
    s₁ = treeSimPeerStep K ctx₁ (bitCodec (E := E)) r₁ v₁ count st₁ k₁ ∧
    s₂ = treeSimPeerStep K ctx₂ (bitCodec (E := E)) r₂ v₂ count st₂ k₂

/-- Peer relations for the honest operators; corrupt operators have no suspended program. -/
def TreeSimPeerStepsRel {α : Type} (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : C.Party → Context C) (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (s₁ s₂ : C.Party → Step C E RealSpec α) : Prop :=
  ∀ i, if i ∈ D.1 then s₁ i = .done none ∧ s₂ i = .done none else
    TreeSimPeerRel K δ (ctx₁ i) (ctx₂ i) idx count (v₁ i) (v₂ i) (st₁ i) (st₂ i) (k₁ i) (k₂ i) (s₁ i) (s₂ i)

/-- Actual peer entry with arbitrary fresh/cached PRSS reads, different input
seeds and histories, and complete suspended continuations on both sides. -/
theorem treeSim_peer_start_mixed {α : Type} (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (idx count : ℕ) (v₁ v₂ : ℕ → Bit) (st₁ st₂ : RunState C) (lab : st₁.label = st₂.label)
    (k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance
        ((((prssRandomness ctx₁ (bitCodec (E := E)) idx count >>= fun o =>
          reshare K ctx₁ (bitCodec (E := E)) o v₁ count).run st₁) >>= k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
        ((((prssRandomness ctx₂ (bitCodec (E := E)) idx count >>= fun o =>
          reshare K ctx₂ (bitCodec (E := E)) o v₂ count).run st₂) >>= k₂).run)))).run b)
      (fun u v => TreeSimPeerRel K δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ u.1 v.1 ∧
        TreeSimStreamRel δ u.2 v.2) := by
  rw [treeSim_peer_entry, treeSim_peer_entry]
  rw [← lab, ← treeSim_prssDraw_context ctx₁ ctx₂ self keys]
  simp only [simulateQ_map, StateT.run_map]
  apply relTriple_map
  apply relTriple_post_mono (treeSim_prssBits_mixed prims D δ hδ ctx₁ st₁.label idx count a b hs)
  intro u v huv
  exact ⟨⟨u.1, v.1, huv.1, huv.2.1, rfl, rfl⟩, huv.2.2⟩

/-- Sequential honest operators share the same caches. This threads their
state invariant instead of assuming independent per-operator draws. -/
private theorem treeSim_sequenceFin_rel {α β σ₁ σ₂ : Type} {n : ℕ}
    (f₁ : Fin n → StateT σ₁ ProbComp α) (f₂ : Fin n → StateT σ₂ ProbComp β)
    (I : σ₁ → σ₂ → Prop) (R : Fin n → α → β → Prop)
    (step : ∀ i s₁ s₂, I s₁ s₂ →
      RelTriple ((f₁ i).run s₁) ((f₂ i).run s₂) (fun u v => R i u.1 v.1 ∧ I u.2 v.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : I s₁ s₂) :
    RelTriple ((Concrete.sequenceFin f₁).run s₁) ((Concrete.sequenceFin f₂).run s₂)
      (fun u v => (∀ i, R i (u.1 i) (v.1 i)) ∧ I u.2 v.2) := by
  induction n generalizing s₁ s₂ with
  | zero =>
    simp only [Concrete.sequenceFin, StateT.run_pure]
    exact relTriple_pure_pure ⟨fun i => Fin.elim0 i, hs⟩
  | succ n ih =>
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure]
    apply relTriple_bind (step 0 s₁ s₂ hs)
    intro u v huv
    apply relTriple_bind (ih (fun i => f₁ i.succ) (fun i => f₂ i.succ)
      (fun i => R i.succ) (fun i => step i.succ) u.2 v.2 huv.2)
    intro us vs hus
    apply relTriple_pure_pure
    refine ⟨?_, hus.2⟩
    intro i
    cases i using Fin.cases with
    | zero => exact huv.1
    | succ i => exact hus.1 i

/-- A peer gadget with its actual random draw and continuation. -/
def treeSimPeerProgram {α : Type} (ctx : Context C) (idx count : ℕ) (v : ℕ → Bit)
    (st : RunState C) (k : Shares C Bit × RunState C → PartyM C E RealSpec α) : PartyM C E RealSpec α :=
  (prssRandomness ctx (bitCodec (E := E)) idx count >>= fun o =>
    reshare K ctx (bitCodec (E := E)) o v count).run st >>= k

/-- All honest peer entries share a single lazy cache on each side. Corrupt
operators draw nothing; honest first and repeated holders use the mixed coupling. -/
theorem treeSim_peer_all_start {α : Type} (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx₁ ctx₂ : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx₁ i).self = (ctx₂ i).self)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab : ∀ i, i ∉ D.1 → (st₁ i).label = (st₂ i).label)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D
        (fun i => treeSimPeerProgram K (ctx₁ i) idx count (v₁ i) (st₁ i) (k₁ i)))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D
        (fun i => treeSimPeerProgram K (ctx₂ i) idx count (v₂ i) (st₂ i) (k₂ i)))).run b)
      (fun u v => TreeSimPeerStepsRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ u.1 v.1 ∧
        TreeSimStreamRel δ u.2 v.2) := by
  unfold startSteps TreeSimPeerStepsRel
  rw [simulateQ_sequenceFin, simulateQ_sequenceFin]
  apply treeSim_sequenceFin_rel _ _ (TreeSimStreamRel δ)
    (fun i x y => if i ∈ D.1 then x = .done none ∧ y = .done none else
      TreeSimPeerRel K δ (ctx₁ i) (ctx₂ i) idx count (v₁ i) (v₂ i) (st₁ i) (st₂ i) (k₁ i) (k₂ i) x y)
  · intro i s₁ s₂ hstate
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨rfl, rfl⟩, hstate⟩
    · simp only [if_neg hi]
      exact treeSim_peer_start_mixed prims K D δ hδ (ctx₁ i) (ctx₂ i) (self i hi) (keys i hi)
        idx count (v₁ i) (v₂ i) (st₁ i) (st₂ i) (lab i hi) (k₁ i) (k₂ i) s₁ s₂ hstate
  · exact hs

/-- The peer message balance is a pointwise equation, independent of the sampled masks. -/
theorem treeSim_reshareOut_balance {R : Type} [Field R] (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (codec : Codec C E R)
    (r dr : Shares C R) (z dz : C.Party → ℕ → R) (v₁ v₂ : ℕ → R) (count : ℕ)
    (balance : ∀ g < count, reshareU K ctx₁ dr dz v₂ g = v₁ g) :
    reshareOut K ctx₂ codec (r + dr) (z + dz) v₂ count = reshareOut K ctx₁ codec r z v₁ count := by
  have hu : ∀ g < count, reshareU K ctx₂ (r + dr) (z + dz) v₂ g = reshareU K ctx₁ r z v₁ g := by
    intro g hg
    have hb := balance g hg
    simp only [reshareU, ← self, Pi.add_apply, Finset.sum_add_distrib] at hb ⊢
    linear_combination hb
  funext j
  simp only [reshareOut, ← self]
  split_ifs
  · congr 2
    exact List.map_congr_left (fun g hg => hu g (List.mem_range.mp hg))
  · rfl

/-- The precise view passed to the rushing adversary in `stepRound`. -/
def treeSimRoundView {α : Type} (D : C.Coalition) (steps : C.Party → Step C E RealSpec α) :
    C.Party → C.Party → Option (Msg E) :=
  fun c i => if c ∈ D.1 ∧ i ∉ D.1 then (steps i).outbox c else none

/-- The concrete peer steps have equal corrupt views when their mask shifts
balance the input difference on every filled term known to the coalition. -/
theorem treeSim_peer_steps_view {α : Type} (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx₁ i).self = (ctx₂ i).self)
    (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (balance : ∀ i, i ∉ D.1 → KnownTo D.1 (K.filled (ctx₁ i).self) → ∀ g < count,
      reshareU K (ctx₁ i) (treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count).1
        (treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count).2 (v₂ i) g = v₁ i g)
    (s₁ s₂ : C.Party → Step C E RealSpec α)
    (hs : TreeSimPeerStepsRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂) :
    treeSimRoundView D s₁ = treeSimRoundView D s₂ := by
  funext c i
  unfold treeSimRoundView
  by_cases hci : c ∈ D.1 ∧ i ∉ D.1
  · simp only [if_pos hci]
    have hi := hs i
    rw [if_neg hci.2] at hi
    obtain ⟨r₁, r₂, ht, hp, hs₁, hs₂⟩ := hi
    rw [hs₁, hs₂]
    change reshareOut K (ctx₁ i) (bitCodec (E := E)) r₁.1 r₁.2 (v₁ i) count c =
      reshareOut K (ctx₂ i) (bitCodec (E := E)) r₂.1 r₂.2 (v₂ i) count c
    by_cases hc : c ≠ (ctx₁ i).self ∧ c ∈ C.holders (K.filled (ctx₁ i).self)
    · rw [ht, hp, treeSim_reshareOut_balance K (ctx₁ i) (ctx₂ i) (self i hci.2)
        (bitCodec (E := E)) r₁.1 _ r₁.2 _ (v₁ i) (v₂ i) count (balance i hci.2 ⟨c, hci.1, hc.2⟩)]
    · simp [reshareOut, ← self i hci.2, hc]
  · simp only [if_neg hci]

/-- Local adversarial computation preserves the translated-cache relation. -/
theorem treeSim_local_streamRel {α : Type} (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (p : OracleComp (LocalSpec C) α) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.adversary p)).run b)
      (fun u v => u.1 = v.1 ∧ TreeSimStreamRel δ u.2 v.2) := by
  rcases a with ⟨⟨h₁, c₁⟩, log⟩
  rcases b with ⟨h₂, c₂⟩
  rcases hs with ⟨rfl, hc⟩
  apply relTriple_post_mono (treeSim_local_coupling prims D p h₁ c₁ c₂ log)
  intro u v huv
  refine ⟨huv.1, huv.2.1, ?_⟩
  rw [huv.2.2.1, huv.2.2.2]
  exact hc

/-- The actual peer entries followed by the rushing adversary's actual round call. -/
def treeSimPeerRushing {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx : C.Party → Context C) (idx count : ℕ) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C) (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    OracleComp (WorldSpec C)
      ((C.Party → Step C E RealSpec α) × A.State × (C.Party → C.Party → Option (Msg E))) := do
  let steps ← startSteps worldRoles D (fun i => treeSimPeerProgram K (ctx i) idx count (v i) (st i) (k i))
  let reply ← worldRoles.adversary (A.round state (treeSimRoundView D steps))
  pure (steps, reply)

/-- A whole peer communication prefix: all honest random draws, the corrupt
view, and the rushing response are coupled in the actual two handlers. -/
theorem treeSim_peer_rushing_mixed {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (δ : HiddenAddress C → Bit) (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx₁ i).self = (ctx₂ i).self)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab : ∀ i, i ∉ D.1 → (st₁ i).label = (st₂ i).label)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (balance : ∀ i, i ∉ D.1 → KnownTo D.1 (K.filled (ctx₁ i).self) → ∀ g < count,
      reshareU K (ctx₁ i) (treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count).1
        (treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count).2 (v₂ i) g = v₁ i g)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeSimPeerRushing K D A state ctx₁ idx count v₁ st₁ k₁)).run a)
      ((simulateQ (streamWorld prims D)
        (treeSimPeerRushing K D A state ctx₂ idx count v₂ st₂ k₂)).run b)
      (fun u v => TreeSimPeerStepsRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ u.1.1 v.1.1 ∧
        u.1.2 = v.1.2 ∧ TreeSimStreamRel δ u.2 v.2) := by
  unfold treeSimPeerRushing
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  apply relTriple_bind (treeSim_peer_all_start prims K D δ hδ ctx₁ ctx₂ self keys
    idx count v₁ v₂ st₁ st₂ lab k₁ k₂ a b hs)
  intro u v huv
  rw [treeSim_peer_steps_view K D δ ctx₁ ctx₂ self idx count v₁ v₂ st₁ st₂ k₁ k₂ balance u.1 v.1 huv.1]
  apply relTriple_bind (treeSim_local_streamRel prims D δ _ u.2 v.2 huv.2)
  intro r₁ r₂ hr
  exact relTriple_pure_pure ⟨huv.1, hr.1, hr.2⟩

/-- GS20's peer simulation in the actual stream worlds: arbitrary real and
simulator inputs, with the identical corrupt view and rushing response.
The shared caches may contain any mixture of fresh and previously read addresses
provided they satisfy the stated translation relation. -/
theorem treeSim_peer_rushing {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    {T₀ : C.Term} {p : C.Party} (hp : Pivot K D T₀ p)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (w : C.Term → Fin count → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hs : TreeSimStreamRel (treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) w) a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeSimPeerRushing K D A state ctx₁ idx count v₁ st₁ k₁)).run a)
      ((simulateQ (streamWorld prims D)
        (treeSimPeerRushing K D A state ctx₂ idx count v₂ st₂ k₂)).run b)
      (fun u z => TreeSimPeerStepsRel K D (treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) w)
          ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ u.1.1 z.1.1 ∧
        u.1.2 = z.1.2 ∧ TreeSimStreamRel (treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) w) u.2 z.2) := by
  apply treeSim_peer_rushing_mixed prims K D A state _
    (treeSim_blockShift_visible D ρ idx count _ _) ctx₁ ctx₂
    (fun i hi => (self₁ i hi).trans (self₂ i hi).symm) keys idx count v₁ v₂
    st₁ st₂ (fun i hi => (lab₁ i hi).trans (lab₂ i hi).symm) k₁ k₂ _ a b hs
  intro i hi hk g hg
  rw [lab₁ i hi]
  have h := treeSim_peerShift_balance_inputs K D hp (ctx₁ i) (by simpa [self₁ i hi] using hi)
    hk ρ idx count v₁ v₂ w g hg
  simpa only [treeSimPeerShift, self₁ i hi] using h

/-- The next peer exchange extends earlier cache translations only on its
unread block. Its shift may depend on the inputs already reached in the ceremony. -/
theorem treeSim_peer_rushing_next {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    {T₀ : C.Term} {p : C.Party} (hp : Pivot K D T₀ p)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (w : C.Term → Fin count → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) w x = 0) :
    let δ := past + treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) w
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeSimPeerRushing K D A state ctx₁ idx count v₁ st₁ k₁)).run a)
      ((simulateQ (streamWorld prims D)
        (treeSimPeerRushing K D A state ctx₂ idx count v₂ st₂ k₂)).run b)
      (fun u z => TreeSimPeerStepsRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ u.1.1 z.1.1 ∧
        u.1.2 = z.1.2 ∧ TreeSimStreamRel δ u.2 z.2) := by
  intro δ
  have hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0 := by
    intro x hx
    simp only [δ, Pi.add_apply, visible x hx, treeSimPeerShift,
      treeSim_blockShift_visible D ρ idx count _ _ x hx, add_zero]
  have hstate : TreeSimStreamRel δ a b :=
    ⟨hs.1, treeSim_hiddenRel_extend past _ hs.2 fresh⟩
  apply treeSim_peer_rushing_mixed prims K D A state δ hδ ctx₁ ctx₂
    (fun i hi => (self₁ i hi).trans (self₂ i hi).symm) keys idx count v₁ v₂
    st₁ st₂ (fun i hi => (lab₁ i hi).trans (lab₂ i hi).symm) k₁ k₂ _ a b hstate
  intro i hi hk g hg
  rw [lab₁ i hi]
  have hshift : treeSimPrssShift δ (ctx₁ i) ρ idx count =
      treeSimPrssShift (treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) w) (ctx₁ i) ρ idx count := by
    dsimp only [δ]
    rw [treeSim_prssShift_add, treeSim_prssShift_zero past (ctx₁ i) ρ idx count block, zero_add]
  rw [hshift]
  simpa only [self₁ i hi] using treeSim_peerShift_balance_inputs K D hp (ctx₁ i)
    (by simpa [self₁ i hi] using hi) hk ρ idx count v₁ v₂ w g hg

/-- The exact terminating peer result, including abort and history updates. -/
def treeSimPeerReturn (ctx : Context C) (rnd : PrssOutput C Bit) (v : ℕ → Bit)
    (count : ℕ) (st : RunState C) (inbox : Mail C E) : Option (Shares C Bit × RunState C) :=
  if anyAbort inbox then none else
    let out := reshareZ K ctx (bitCodec (E := E)) rnd.1 rnd.2 v count inbox
    some (out, ⟨recordPeer K (bitCodec (E := E)) ctx.self st.history out count, st.label + 1, st.tag⟩)

theorem treeSim_peer_return (ctx : Context C) (rnd : PrssOutput C Bit) (v : ℕ → Bit)
    (count : ℕ) (st : RunState C) (inbox : Mail C E) :
    advance (exchangeResume (G := RealSpec) (fun inbox =>
      let out := reshareZ K ctx (bitCodec (E := E)) rnd.1 rnd.2 v count inbox
      pure (out, ⟨recordPeer K (bitCodec (E := E)) ctx.self st.history out count, st.label + 1, st.tag⟩)) inbox) =
      pure (.done (treeSimPeerReturn K ctx rnd v count st inbox)) := by
  unfold exchangeResume treeSimPeerReturn anyAbort
  split_ifs <;> rfl

/-- The resolved peer outputs retain both sampled masks and their concrete
history updates; inboxes include the common malicious replies verbatim. -/
def TreeSimPeerAfterAt (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : C.Party → Context C) (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (s₁ s₂ : C.Party → Step C E RealSpec (Shares C Bit × RunState C))
    (sent : C.Party → Mail C E)
    (i : C.Party) (next₁ next₂ : Step C E RealSpec (Shares C Bit × RunState C)) : Prop :=
  if i ∈ D.1 then next₁ = .done none ∧ next₂ = .done none else
    ∃ r₁ r₂ : PrssOutput C Bit,
      r₂.1 = r₁.1 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count).1 ∧
      r₂.2 = r₁.2 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count).2 ∧
      s₁ i = treeSimPeerStep K (ctx₁ i) bitCodec r₁ (v₁ i) count (st₁ i) pure ∧
      s₂ i = treeSimPeerStep K (ctx₂ i) bitCodec r₂ (v₂ i) count (st₂ i) pure ∧
      next₁ = .done (treeSimPeerReturn K (ctx₁ i) r₁ (v₁ i) count (st₁ i)
        (fun j => if j ∈ D.1 then sent j i else (s₁ j).delivered i)) ∧
      next₂ = .done (treeSimPeerReturn K (ctx₂ i) r₂ (v₂ i) count (st₂ i)
        (fun j => if j ∈ D.1 then sent j i else (s₂ j).delivered i))

def TreeSimPeerAfterRel (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : C.Party → Context C) (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (s₁ s₂ : C.Party → Step C E RealSpec (Shares C Bit × RunState C))
    (sent : C.Party → Mail C E)
    (next₁ next₂ : C.Party → Step C E RealSpec (Shares C Bit × RunState C)) : Prop :=
  ∀ i, TreeSimPeerAfterAt K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ s₁ s₂ sent i (next₁ i) (next₂ i)

/-- Resolve every honest peer's actual continuation, retaining its output and
history. No further randomness or hash query occurs in this terminating phase. -/
theorem treeSim_peer_finish (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : C.Party → Context C) (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (s₁ s₂ : C.Party → Step C E RealSpec (Shares C Bit × RunState C))
    (hsteps : TreeSimPeerStepsRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂
      (fun _ => pure) (fun _ => pure) s₁ s₂)
    (sent : C.Party → Mail C E) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (free (Concrete.sequenceFin (roundLocal D s₁ sent)))).run a)
      ((simulateQ (streamWorld prims D) (free (Concrete.sequenceFin (roundLocal D s₂ sent)))).run b)
      (fun u z => TreeSimPeerAfterRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ s₁ s₂ sent u.1 z.1 ∧
        TreeSimStreamRel δ u.2 z.2) := by
  rw [free_sequenceFin, free_sequenceFin, simulateQ_sequenceFin, simulateQ_sequenceFin]
  apply treeSim_sequenceFin_rel (I := TreeSimStreamRel δ)
    (R := TreeSimPeerAfterAt K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ s₁ s₂ sent) _ _ ?_ a b hs
  intro i a' b' hab
  unfold TreeSimPeerAfterAt
  have hi := hsteps i
  by_cases hc : i ∈ D.1
  · rw [if_pos hc] at hi
    simp only [roundLocal, hi.1, hi.2, free_pure, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨by simp [hc], hab⟩
  · rw [if_neg hc] at hi
    obtain ⟨r₁, r₂, ht, hp, he₁, he₂⟩ := hi
    have hl₁ : roundLocal D s₁ sent i = pure (.done (treeSimPeerReturn K (ctx₁ i) r₁ (v₁ i) count (st₁ i)
        (fun j => if j ∈ D.1 then sent j i else (s₁ j).delivered i))) := by
      simp only [roundLocal, he₁, treeSimPeerStep, if_neg hc]
      exact treeSim_peer_return K _ _ _ _ _ _
    have hl₂ : roundLocal D s₂ sent i = pure (.done (treeSimPeerReturn K (ctx₂ i) r₂ (v₂ i) count (st₂ i)
        (fun j => if j ∈ D.1 then sent j i else (s₂ j).delivered i))) := by
      simp only [roundLocal, he₂, treeSimPeerStep, if_neg hc]
      exact treeSim_peer_return K _ _ _ _ _ _
    rw [hl₁, hl₂]
    simp only [free_pure, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨by simpa only [if_neg hc] using
      ⟨r₁, r₂, ht, hp, he₁, he₂, rfl, rfl⟩, hab⟩

/-- Honest peer messages cannot introduce an abort frame. The two inboxes
therefore abort on exactly the same malicious replies. -/
theorem treeSim_peer_inbox_abort {α : Type} (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : C.Party → Context C) (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (s₁ s₂ : C.Party → Step C E RealSpec α)
    (hs : TreeSimPeerStepsRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ s₁ s₂)
    (sent : C.Party → Mail C E) (i : C.Party) :
    anyAbort (fun j => if j ∈ D.1 then sent j i else (s₁ j).delivered i) =
      anyAbort (fun j => if j ∈ D.1 then sent j i else (s₂ j).delivered i) := by
  unfold anyAbort
  congr 1
  funext j
  by_cases hj : j ∈ D.1
  · simp only [if_pos hj]
  · have h := hs j
    rw [if_neg hj] at h
    obtain ⟨r₁, r₂, _, _, h₁, h₂⟩ := h
    simp only [if_neg hj, h₁, h₂, treeSimPeerStep, Step.delivered, reshareOut]
    split_ifs <;> rfl

/-- The complete gadget leaves only terminal steps and agrees on every honest
abort, even if malicious parties send different replies to different recipients. -/
theorem treeSim_peer_after_terminal (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : C.Party → Context C) (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (s₁ s₂ n₁ n₂ : C.Party → Step C E RealSpec (Shares C Bit × RunState C))
    (hs : TreeSimPeerStepsRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂
      (fun _ => pure) (fun _ => pure) s₁ s₂)
    (sent : C.Party → Mail C E)
    (hn : TreeSimPeerAfterRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ s₁ s₂ sent n₁ n₂) :
    ∀ i, (n₁ i).isDone ∧ (n₂ i).isDone ∧ (n₁ i).output.isSome = (n₂ i).output.isSome := by
  intro i
  have hi := hn i
  unfold TreeSimPeerAfterAt at hi
  by_cases hc : i ∈ D.1
  · rw [if_pos hc] at hi
    simp [hi.1, hi.2, Step.isDone]
  · rw [if_neg hc] at hi
    obtain ⟨r₁, r₂, _, _, _, _, h₁, h₂⟩ := hi
    rw [h₁, h₂]
    have hab := treeSim_peer_inbox_abort K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂
      (fun _ => pure) (fun _ => pure) s₁ s₂ hs sent i
    simp only [Step.isDone, Step.output, true_and, treeSimPeerReturn, hab]
    split_ifs <;> rfl

/-- Successful honest results have the same sharing except for the stored
`T₀` shift. Aborts must match as well. -/
def TreeSimPeerOutputShift (D : C.Coalition) (count : ℕ) (difference : ℕ → Bit)
    (n₁ n₂ : C.Party → Step C E RealSpec (Shares C Bit × RunState C)) : Prop :=
  ∀ i, Option.Rel (fun x y => y.1 = treeSimHeldShift D i count difference x.1)
    (n₁ i).output (n₂ i).output

/-- The mask witnesses of the actual peer round imply the `T₀` sharing relation,
including every selective abort. -/
theorem treeSim_peer_after_shares (D : C.Coalition) {T₀ : C.Term} {p : C.Party}
    (hp : Pivot K D T₀ p) (δ : HiddenAddress C → Bit) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (block : ∀ i, i ∉ D.1 → treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count =
      frandShare D count 0 0 (termShift K D T₀ p (v₁ - v₂) (0 : C.Term → Fin count → Bit))
        (pairShift p (pairDelta K D T₀ p (v₁ - v₂) (0 : C.Term → Fin count → Bit))) i)
    (s₁ s₂ n₁ n₂ : C.Party → Step C E RealSpec (Shares C Bit × RunState C))
    (hs : TreeSimPeerStepsRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂
      (fun _ => pure) (fun _ => pure) s₁ s₂)
    (sent : C.Party → Mail C E)
    (hn : TreeSimPeerAfterRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ s₁ s₂ sent n₁ n₂) :
    TreeSimPeerOutputShift D count (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g) n₁ n₂ := by
  have witnesses : ∀ i, ∃ r₁ r₂ : PrssOutput C Bit, i ∉ D.1 →
      r₂.1 = r₁.1 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count).1 ∧
      r₂.2 = r₁.2 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count).2 ∧
      s₁ i = treeSimPeerStep K (ctx₁ i) bitCodec r₁ (v₁ i) count (st₁ i) pure ∧
      s₂ i = treeSimPeerStep K (ctx₂ i) bitCodec r₂ (v₂ i) count (st₂ i) pure ∧
      n₁ i = .done (treeSimPeerReturn K (ctx₁ i) r₁ (v₁ i) count (st₁ i)
        (fun j => if j ∈ D.1 then sent j i else (s₁ j).delivered i)) ∧
      n₂ i = .done (treeSimPeerReturn K (ctx₂ i) r₂ (v₂ i) count (st₂ i)
        (fun j => if j ∈ D.1 then sent j i else (s₂ j).delivered i)) := by
    intro i
    by_cases hi : i ∈ D.1
    · exact ⟨0, 0, fun h => (h hi).elim⟩
    · have h := hn i
      rw [TreeSimPeerAfterAt, if_neg hi] at h
      obtain ⟨r₁, r₂, h⟩ := h
      exact ⟨r₁, r₂, fun _ => h⟩
  choose r₁ r₂ hr using witnesses
  have masks : ∀ i, i ∉ D.1 → r₂ i = r₁ i + frandShare D count 0 0
      (termShift K D T₀ p (v₁ - v₂) (0 : C.Term → Fin count → Bit))
      (pairShift p (pairDelta K D T₀ p (v₁ - v₂) (0 : C.Term → Fin count → Bit))) i := by
    intro i hi
    exact Prod.ext (by simpa only [block i hi, Prod.fst_add] using (hr i hi).1)
      (by simpa only [block i hi, Prod.snd_add] using (hr i hi).2.1)
  intro i
  by_cases hi : i ∈ D.1
  · have h := hn i
    rw [TreeSimPeerAfterAt, if_pos hi] at h
    rw [h.1, h.2]
    exact Option.Rel.none
  · rcases hr i hi with ⟨_, _, _, _, h₁, h₂⟩
    rw [h₁, h₂]
    have hab := treeSim_peer_inbox_abort K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂
      (fun _ => pure) (fun _ => pure) s₁ s₂ hs sent i
    simp only [Step.output, treeSimPeerReturn, hab]
    split_ifs
    · exact Option.Rel.none
    · apply Option.Rel.some
      have hin₁ : (fun j => if j ∈ D.1 then sent j i else (s₁ j).delivered i) =
          (fun j => if j ∈ D.1 then sent j i else
            reshareOut K (ctx₁ j) bitCodec (r₁ j).1 (r₁ j).2 (v₁ j) count i) := by
        funext j
        by_cases hj : j ∈ D.1
        · simp [hj]
        · simp only [if_neg hj, (hr j hj).2.2.1, treeSimPeerStep, Step.delivered]
      have hin₂ : (fun j => if j ∈ D.1 then sent j i else (s₂ j).delivered i) =
          (fun j => if j ∈ D.1 then sent j i else
            reshareOut K (ctx₂ j) bitCodec (r₂ j).1 (r₂ j).2 (v₂ j) count i) := by
        funext j
        by_cases hj : j ∈ D.1
        · simp [hj]
        · simp only [if_neg hj, (hr j hj).2.2.2.1, treeSimPeerStep, Step.delivered]
      dsimp only
      rw [hin₁, hin₂]
      exact treeSim_reshareZ_pivot K D hp ctx₁ ctx₂ self₁ self₂ count v₁ v₂ r₁ r₂ masks sent i hi

/-- The actual return values also preserve the history, label and tag
relation, with the precise new `T₀` history difference. -/
theorem treeSim_peer_after_states (D : C.Coalition) (T₀ : C.Term) (hT₀ : lackedTerm D.1 = some T₀)
    (δ : HiddenAddress C → Bit) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (past : List Bit) (difference : ℕ → Bit)
    (hstate : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i past (st₁ i) (st₂ i))
    (s₁ s₂ n₁ n₂ : C.Party → Step C E RealSpec (Shares C Bit × RunState C))
    (hs : TreeSimPeerStepsRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂
      (fun _ => pure) (fun _ => pure) s₁ s₂)
    (sent : C.Party → Mail C E)
    (hn : TreeSimPeerAfterRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ s₁ s₂ sent n₁ n₂)
    (hout : TreeSimPeerOutputShift D count difference n₁ n₂) :
    ∀ i, Option.Rel (fun x y => TreeSimRunStateRel D i (treeSimHistoryAppend K T₀ count past difference) x.2 y.2)
      (n₁ i).output (n₂ i).output := by
  intro i
  have h := hn i
  by_cases hi : i ∈ D.1
  · rw [TreeSimPeerAfterAt, if_pos hi] at h
    rw [h.1, h.2]
    exact Option.Rel.none
  · rw [TreeSimPeerAfterAt, if_neg hi] at h
    obtain ⟨r₁, r₂, _, _, _, _, h₁, h₂⟩ := h
    have ho := hout i
    rw [h₁, h₂] at ho ⊢
    have hab := treeSim_peer_inbox_abort K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂
      (fun _ => pure) (fun _ => pure) s₁ s₂ hs sent i
    simp only [Step.output, treeSimPeerReturn, hab] at ho ⊢
    split_ifs at ho ⊢
    · exact Option.Rel.none
    · cases ho with
      | some hz =>
        apply Option.Rel.some
        refine ⟨congrArg (· + 1) (hstate i hi).1, (hstate i hi).2.1, ?_⟩
        dsimp only
        rw [self₁ i hi, self₂ i hi]
        exact treeSim_recordPeer_shift K D T₀ hT₀ i count past difference _ _ (hstate i hi).2.2 _ _ hz

/-- One complete peer gadget in the real network, ending after its exchange. -/
def treeSimPeerRound (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (ctx : C.Party → Context C) (idx count : ℕ)
    (v : C.Party → ℕ → Bit) (st : C.Party → RunState C) :
    OracleComp (WorldSpec C) (A.State ×
      (C.Party → Step C E RealSpec (Shares C Bit × RunState C)) × (C.Party → Mail C E)) := do
  let steps ← startSteps worldRoles D (fun i => treeSimPeerProgram K (ctx i) idx count (v i) (st i) pure)
  stepRound worldRoles D A noFunctionality state steps

private theorem treeSim_peer_round_factor (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx : C.Party → Context C) (idx count : ℕ) (v : C.Party → ℕ → Bit) (st : C.Party → RunState C) :
    treeSimPeerRound K D A state ctx idx count v st = (do
      let r ← treeSimPeerRushing K D A state ctx idx count v st (fun _ => pure)
      let next ← free (Concrete.sequenceFin (roundLocal D r.1 r.2.2))
      pure (r.2.1, next, r.2.2)) := by
  unfold treeSimPeerRound treeSimPeerRushing
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro steps
  exact stepRound_real D A state steps

/-- The complete peer-stage relation: the adversary agrees, the sampled-mask
witnesses explain the outputs and histories, and terminal/abort status agrees. -/
def TreeSimPeerRoundRel (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (δ : HiddenAddress C → Bit) (ctx₁ ctx₂ : C.Party → Context C)
    (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C) :
    (A.State × (C.Party → Step C E RealSpec (Shares C Bit × RunState C)) × (C.Party → Mail C E)) ×
      TreeSimState C →
    (A.State × (C.Party → Step C E RealSpec (Shares C Bit × RunState C)) × (C.Party → Mail C E)) ×
      (HashCache C × HiddenCache C) → Prop :=
  fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        (∃ s₁ s₂, TreeSimPeerStepsRel K D δ
            ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ (fun _ => pure) (fun _ => pure) s₁ s₂ ∧
          TreeSimPeerAfterRel K D δ
            ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ s₁ s₂ u.1.2.2 u.1.2.1 z.1.2.1) ∧
        (∀ i, (u.1.2.1 i).isDone ∧ (z.1.2.1 i).isDone ∧
          (u.1.2.1 i).output.isSome = (z.1.2.1 i).output.isSome) ∧
        TreeSimStreamRel δ u.2 z.2

private theorem treeSim_peer_round_of_rushing (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (δ : HiddenAddress C → Bit) (ctx₁ ctx₂ : C.Party → Context C)
    (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (coupled : RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeSimPeerRushing K D A state ctx₁ idx count v₁ st₁ (fun _ => pure))).run a)
      ((simulateQ (streamWorld prims D)
        (treeSimPeerRushing K D A state ctx₂ idx count v₂ st₂ (fun _ => pure))).run b)
      (fun u z => TreeSimPeerStepsRel K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂
          (fun _ => pure) (fun _ => pure) u.1.1 z.1.1 ∧
        u.1.2 = z.1.2 ∧ TreeSimStreamRel δ u.2 z.2)) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimPeerRound K D A state ctx₁ idx count v₁ st₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimPeerRound K D A state ctx₂ idx count v₂ st₂)).run b)
      (TreeSimPeerRoundRel K D A δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂) := by
  rw [treeSim_peer_round_factor, treeSim_peer_round_factor]
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  apply relTriple_bind coupled
  intro r₁ r₂ hr
  have hsent := congrArg Prod.snd hr.2.1
  rw [← hsent]
  apply relTriple_bind (treeSim_peer_finish prims K D δ ctx₁ ctx₂ idx count v₁ v₂
    st₁ st₂ r₁.1.1 r₂.1.1 hr.1 r₁.1.2.2 r₁.2 r₂.2 hr.2.2)
  intro n₁ n₂ hn
  have hstate : r₁.1.2.1 = r₂.1.2.1 := congrArg Prod.fst hr.2.1
  exact relTriple_pure_pure ⟨hstate, rfl, ⟨r₁.1.1, r₂.1.1, hr.1, hn.1⟩,
    treeSim_peer_after_terminal K D δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂
      r₁.1.1 r₂.1.1 n₁.1 n₂.1 hr.1 r₁.1.2.2 hn.1, hn.2⟩

/-- A complete peer gadget coupling with the GS20 masks, actual shared caches,
malicious replies, aborts and updated honest histories. The postcondition keeps
both suspended exchanges so subsequent invariants can inspect every sampled mask. -/
theorem treeSim_peer_round_actual (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    {T₀ : C.Term} {p : C.Party} (hp : Pivot K D T₀ p)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (w : C.Term → Fin count → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hs : TreeSimStreamRel (treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) w) a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimPeerRound K D A state ctx₁ idx count v₁ st₁)).run a)
      ((simulateQ (streamWorld prims D)
        (treeSimPeerRound K D A state ctx₂ idx count v₂ st₂)).run b)
      (TreeSimPeerRoundRel K D A (treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) w)
        ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂) := by
  exact treeSim_peer_round_of_rushing prims K D A state _ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ a b
    (treeSim_peer_rushing prims K D A state hp ctx₁ ctx₂ self₁ self₂ keys
      ρ idx count v₁ v₂ w st₁ st₂ lab₁ lab₂ (fun _ => pure) (fun _ => pure) a b hs)

/-- Complete the next actual peer gadget while preserving every earlier cache
translation. Freshness is needed only where the new shift is nonzero. -/
theorem treeSim_peer_round_next (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    {T₀ : C.Term} {p : C.Party} (hp : Pivot K D T₀ p)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (w : C.Term → Fin count → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hs : TreeSimStreamRel past a b)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) w x = 0) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimPeerRound K D A state ctx₁ idx count v₁ st₁)).run a)
      ((simulateQ (streamWorld prims D)
        (treeSimPeerRound K D A state ctx₂ idx count v₂ st₂)).run b)
      (TreeSimPeerRoundRel K D A (past + treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) w)
        ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂) := by
  exact treeSim_peer_round_of_rushing prims K D A state _ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ a b
    (treeSim_peer_rushing_next prims K D A state hp ctx₁ ctx₂ self₁ self₂ keys
      ρ idx count v₁ v₂ w st₁ st₂ lab₁ lab₂ (fun _ => pure) (fun _ => pure)
      past visible block a b hs fresh)

/-- The actual complete peer round preserves a `T₀`-shifted sharing, with
accumulated stream translations, exact history updates and matching selective abort. -/
theorem treeSim_peer_round_pivot (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    {T₀ : C.Term} {p : C.Party} (hp : Pivot K D T₀ p)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) 0 x = 0) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimPeerRound K D A state ctx₁ idx count v₁ st₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimPeerRound K D A state ctx₂ idx count v₂ st₂)).run b)
      (fun u z => TreeSimPeerRoundRel K D A
          (past + treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) 0)
          ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ u z ∧
        TreeSimPeerOutputShift D count
          (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g) u.1.2.1 z.1.2.1) := by
  apply relTriple_post_mono (treeSim_peer_round_next prims K D A state hp ctx₁ ctx₂ self₁ self₂ keys
    ρ idx count v₁ v₂ 0 st₁ st₂ lab₁ lab₂ past visible block a b hs fresh)
  intro u z h
  refine ⟨h, ?_⟩
  obtain ⟨s₁, s₂, hsteps, hafter⟩ := h.2.2.1
  apply treeSim_peer_after_shares K D hp _ ctx₁ ctx₂ self₁ self₂ idx count v₁ v₂ st₁ st₂
    _ s₁ s₂ u.1.2.1 z.1.2.1 hsteps u.1.2.2 hafter
  intro i hi
  rw [lab₁ i hi, treeSim_prssShift_add, treeSim_prssShift_zero past (ctx₁ i) ρ idx count block, zero_add]
  unfold treeSimPeerShift
  rw [treeSim_prssShift_block D (ctx₁ i) (by simpa [self₁ i hi] using hi), self₁ i hi]

/-- Peer-stage preservation for both the sharing and the recorded run state.
The history difference is common to all honest holders of `T₀`, as required for
the later check; actual corrupt messages and cache translations are retained. -/
theorem treeSim_peer_round_state (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    {T₀ : C.Term} {p : C.Party} (hp : Pivot K D T₀ p)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (history : List Bit) (hstate : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) 0 x = 0) :
    let difference := fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimPeerRound K D A state ctx₁ idx count v₁ st₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimPeerRound K D A state ctx₂ idx count v₂ st₂)).run b)
      (fun u z => TreeSimPeerRoundRel K D A
          (past + treeSimPeerShift K D T₀ p ρ idx count (v₁ - v₂) 0)
          ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ u z ∧
        TreeSimPeerOutputShift D count difference u.1.2.1 z.1.2.1 ∧
        ∀ i, Option.Rel (fun x y => TreeSimRunStateRel D i
          (treeSimHistoryAppend K T₀ count history difference) x.2 y.2)
          (u.1.2.1 i).output (z.1.2.1 i).output) := by
  intro difference
  apply relTriple_post_mono (treeSim_peer_round_pivot prims K D A state hp ctx₁ ctx₂ self₁ self₂ keys
    ρ idx count v₁ v₂ st₁ st₂ lab (fun i hi => (hstate i hi).1.symm.trans (lab i hi))
    past visible block a b hs fresh)
  intro u z h
  refine ⟨h.1, h.2, ?_⟩
  obtain ⟨s₁, s₂, hsteps, hafter⟩ := h.1.2.2.1
  exact treeSim_peer_after_states K D T₀ hp.lacked _ ctx₁ ctx₂ self₁ self₂ idx count v₁ v₂ st₁ st₂
    history difference hstate s₁ s₂ u.1.2.1 z.1.2.1 hsteps u.1.2.2 hafter h.2

/-- One complete invocation of the frozen `Rerand` gadget in the real network. -/
def treeSimRerandRound (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (mode : ReshareMode) (ctx : C.Party → Context C) (count : ℕ)
    (x : C.Party → Shares C Bit) (st : C.Party → RunState C) :
    OracleComp (WorldSpec C) (A.State ×
      (C.Party → Step C E RealSpec (Shares C Bit × RunState C)) × (C.Party → Mail C E)) := do
  let steps ← startSteps worldRoles D (fun i => ((realRunGadgets K (ctx i) mode).rerand (x i) count).run (st i))
  stepRound worldRoles D A noFunctionality state steps

theorem treeSim_rerand_round_eq (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (mode : ReshareMode) (ctx : C.Party → Context C) (count : ℕ)
    (x : C.Party → Shares C Bit) (st : C.Party → RunState C) :
    treeSimRerandRound K D A state mode ctx count x st =
      treeSimPeerRound K D A state ctx 0 count (fun i => ownerSum K (ctx i) (x i)) st := by
  simp only [treeSimRerandRound, treeSimPeerRound, treeSimPeerProgram, realRunGadgets, bind_pure]

/-- `Rerand` preserves the incoming sharing shift and appends that same shift
to the recorded pivot history, in either configured multiplication mode. -/
theorem treeSim_rerand_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (mode : ReshareMode)
    {T₀ : C.Term} {p : C.Party} (hp : Pivot K D T₀ p)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ count : ℕ) (difference : ℕ → Bit) (x₁ x₂ : C.Party → Shares C Bit)
    (hx : ∀ i, i ∉ D.1 → x₂ i = treeSimHeldShift D i count difference (x₁ i))
    (st₁ st₂ : C.Party → RunState C) (lab : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (history : List Bit) (hstate : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, 0, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b) :
    let v₁ := fun i => ownerSum K (ctx₁ i) (x₁ i)
    let v₂ := fun i => ownerSum K (ctx₂ i) (x₂ i)
    (∀ x, (a.1.2 x).isSome → treeSimPeerShift K D T₀ p ρ 0 count (v₁ - v₂) 0 x = 0) →
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimRerandRound K D A state mode ctx₁ count x₁ st₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimRerandRound K D A state mode ctx₂ count x₂ st₂)).run b)
      (fun u z => TreeSimPeerRoundRel K D A
          (past + treeSimPeerShift K D T₀ p ρ 0 count (v₁ - v₂) 0)
          ctx₁ ctx₂ 0 count v₁ v₂ st₁ st₂ u z ∧
        TreeSimPeerOutputShift D count difference u.1.2.1 z.1.2.1 ∧
        ∀ i, Option.Rel (fun x y => TreeSimRunStateRel D i
          (treeSimHistoryAppend K T₀ count history difference) x.2 y.2)
          (u.1.2.1 i).output (z.1.2.1 i).output) := by
  intro v₁ v₂ fresh
  rw [treeSim_rerand_round_eq, treeSim_rerand_round_eq]
  have hd : (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g) =
      fun g => if g < count then difference g else 0 := by
    funext g
    exact treeSim_rerand_difference K D hp ctx₁ ctx₂ self₁ self₂ count difference x₁ x₂ hx g
  apply relTriple_post_mono (treeSim_peer_round_state prims K D A state hp ctx₁ ctx₂ self₁ self₂ keys
    ρ 0 count v₁ v₂ st₁ st₂ lab history hstate past visible block a b hs fresh)
  intro u z h
  rw [hd] at h
  exact ⟨h.1, by simpa only [TreeSimPeerOutputShift, treeSimHeldShift_truncate] using h.2.1,
    by simpa only [treeSimHistoryAppend_truncate] using h.2.2⟩

/-- One complete multiplication in peer mode, using the frozen real gadget. -/
def treeSimMultPeerRound (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (ctx : C.Party → Context C) (count : ℕ)
    (x y : C.Party → Shares C Bit) (st : C.Party → RunState C) :
    OracleComp (WorldSpec C) (A.State ×
      (C.Party → Step C E RealSpec (Shares C Bit × RunState C)) × (C.Party → Mail C E)) := do
  let steps ← startSteps worldRoles D (fun i => ((realRunGadgets K (ctx i) .peer).mult (x i) (y i) count).run (st i))
  stepRound worldRoles D A noFunctionality state steps

theorem treeSim_multPeer_round_eq (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (ctx : C.Party → Context C) (count : ℕ)
    (x y : C.Party → Shares C Bit) (st : C.Party → RunState C) :
    treeSimMultPeerRound K D A state ctx count x y st =
      treeSimPeerRound K D A state ctx 0 count (fun i => mulRep K (ctx i) (x i) (y i)) st := by
  simp only [treeSimMultPeerRound, treeSimPeerRound, treeSimPeerProgram, realRunGadgets, reshareWith, bind_pure]

/-- Multiplication in peer mode preserves the sharing/history relation with
shift equal to the difference of the honest additive `MulRep` values. -/
theorem treeSim_multPeer_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    {T₀ : C.Term} {p : C.Party} (hp : Pivot K D T₀ p)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ count : ℕ) (x₁ y₁ x₂ y₂ : C.Party → Shares C Bit) (st₁ st₂ : C.Party → RunState C)
    (lab : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (history : List Bit) (hstate : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, 0, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b) :
    let v₁ := fun i => mulRep K (ctx₁ i) (x₁ i) (y₁ i)
    let v₂ := fun i => mulRep K (ctx₂ i) (x₂ i) (y₂ i)
    let difference := fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g
    (∀ x, (a.1.2 x).isSome → treeSimPeerShift K D T₀ p ρ 0 count (v₁ - v₂) 0 x = 0) →
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimMultPeerRound K D A state ctx₁ count x₁ y₁ st₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimMultPeerRound K D A state ctx₂ count x₂ y₂ st₂)).run b)
      (fun u z => TreeSimPeerRoundRel K D A
          (past + treeSimPeerShift K D T₀ p ρ 0 count (v₁ - v₂) 0)
          ctx₁ ctx₂ 0 count v₁ v₂ st₁ st₂ u z ∧
        TreeSimPeerOutputShift D count difference u.1.2.1 z.1.2.1 ∧
        ∀ i, Option.Rel (fun x y => TreeSimRunStateRel D i
          (treeSimHistoryAppend K T₀ count history difference) x.2 y.2)
          (u.1.2.1 i).output (z.1.2.1 i).output) := by
  intro v₁ v₂ difference fresh
  rw [treeSim_multPeer_round_eq, treeSim_multPeer_round_eq]
  exact treeSim_peer_round_state prims K D A state hp ctx₁ ctx₂ self₁ self₂ keys
    ρ 0 count v₁ v₂ st₁ st₂ lab history hstate past visible block a b hs fresh

/-- The two concrete roles at a ceremony round boundary. -/
def treeSimRealRoles (D : C.Coalition) : Roles C (StateT (TreeSimState C) ProbComp) :=
  simRoles (treeSimLoggedWorld prims D) worldRoles

def treeSimIdealRoles (D : C.Coalition) : Roles C (StateT (HashCache C × HiddenCache C) ProbComp) :=
  simRoles (streamWorld prims D) worldRoles

abbrev TreeSimRoundOutput (A : Adversary C E (Keys C) PEmpty PEmpty) (σ : Type) :=
  (A.State × (C.Party → Option TreeOutput)) × σ

/-- Bad events recorded in a transcript persist through each actual round. -/
theorem treeSim_round_bad (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Bad : TreeSimState C → Prop)
    (persistent : ∀ s s' : TreeSimState C, s.2 <+: s'.2 → Bad s → Bad s')
    (st : A.State) (steps : C.Party → Step C E RealSpec TreeOutput)
    (s : TreeSimState C) (hs : Bad s)
    (r : (A.State × (C.Party → Step C E RealSpec TreeOutput) ×
      (C.Party → C.Party → Option (Msg E))) × TreeSimState C)
    (hr : r ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality st steps).run s)) :
    Bad r.2 := by
  apply persistent s r.2 _ hs
  apply treeSimLoggedWorld_prefix prims D (stepRound worldRoles D A noFunctionality st steps) s r
  simpa only [simulateQ_stepRound, treeSimRealRoles] using hr

/-- The collector's two rushing exchanges, retaining the actual recorded state. -/
def treeSimCollectorExchange (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (count : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C) :
    OracleComp (WorldSpec C) (A.State × (C.Party → Option (Shares C Bit × RunState C))) := do
  let b ← worldRoles.adversary (A.round state (colMsgs1 K D count rnd v))
  if ∀ i, i ∉ D.1 → anyAbort (colInbox K D count rnd v b.2 i) = true then
    pure (b.1, fun _ => none)
  else do
    let b' ← worldRoles.adversary (A.round b.1 (colMsgs2 K D count rnd v b.2))
    pure (b'.1, fun i => (colOuts K D count rnd v b.2 b'.2 i).map fun out =>
      (out, ⟨recordMode K .collector i (st i).history out count, (st i).label + 1, (st i).tag⟩))

/-- Exact normalization of the real collector continuations. In particular,
all-abort after the first reply makes no second adversary call. -/
theorem treeSim_collector_exchange_eq (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (count : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C) :
    executeRounds worldRoles D A noFunctionality 2 state
      (fun i => if i ∈ D.1 then .done none else
        treeSimCollectorStep K (ctx i) (rnd i) (v i) count (st i) pure) =
      treeSimCollectorExchange K D A state count rnd v st := by
  have hsteps : (fun i => if i ∈ D.1 then Step.done none else
      treeSimCollectorStep K (ctx i) (rnd i) (v i) count (st i) pure) =
      fun i => if i ∈ D.1 then Step.done none else
        Step.wait (colOut1 K i (rnd i).1 (rnd i).2 (v i) count)
          (exchangeResume (G := RealSpec) fun inbox =>
            exchange (colOut2 K i (rnd i).1 (rnd i).2 (v i) count inbox) >>= fun forward =>
              let out := colZ K i (rnd i).1 (rnd i).2 (v i) count inbox forward
              pure (out, ⟨recordMode K .collector i (st i).history out count,
                (st i).label + 1, (st i).tag⟩)) := by
    funext i
    by_cases hi : i ∈ D.1
    · simp [hi]
    · simp only [if_neg hi, treeSimCollectorStep, self i hi]
  rw [hsteps, executeRounds_wait]
  unfold treeSimCollectorExchange
  apply bind_congr
  intro b
  let inbox := colInbox K D count rnd v b.2
  let ab := fun i => anyAbort (inbox i)
  let out2 := fun i => colOut2 K i (rnd i).1 (rnd i).2 (v i) count (inbox i)
  let k2 : C.Party → Mail C E → OracleComp (PartySpec C E RealSpec)
      (Option (Shares C Bit × RunState C)) := fun i => exchangeResume (G := RealSpec) fun forward =>
    let out := colZ K i (rnd i).1 (rnd i).2 (v i) count (inbox i) forward
    pure (out, ⟨recordMode K .collector i (st i).history out count,
      (st i).label + 1, (st i).tag⟩)
  rw [sequenceFin_congr_pure _ (fun i => if i ∈ D.1 ∨ ab i then Step.done none else
      Step.wait (out2 i) (k2 i)) (fun i => by
    by_cases hi : i ∈ D.1
    · simp only [hi, if_true, true_or]
    · simp only [hi, if_false, false_or]
      change free (advance (exchangeResume _ (inbox i))) = _
      dsimp only [ab]
      unfold exchangeResume anyAbort
      split_ifs with hab
      · rfl
      · rw [advance_exchange_bind]
        rfl)]
  simp only [pure_bind]
  by_cases hall : ∀ i, i ∉ D.1 → ab i = true
  · rw [if_pos hall, executeRounds, if_pos (fun i hi => by simp [hall i hi])]
    congr 2
    funext i
    by_cases hi : i ∈ D.1 <;> simp [hi, hall i, Step.output]
  · rw [if_neg hall]
    push Not at hall
    rw [executeRounds_round D A noFunctionality 0 b.1 ab out2 k2 hall]
    apply bind_congr
    intro b'
    rw [sequenceFin_congr_pure _ (fun i => Step.done
        ((colOuts K D count rnd v b.2 b'.2 i).map fun out =>
          (out, ⟨recordMode K .collector i (st i).history out count,
            (st i).label + 1, (st i).tag⟩))) (fun i => by
      by_cases hi : i ∈ D.1 ∨ ab i = true
      · simp only [if_pos hi, colOuts, show (i ∈ D.1 ∨
            anyAbort (colInbox K D count rnd v b.2 i) = true) from hi, if_true, Option.map_none]
      · simp only [if_neg hi, colOuts, show ¬ (i ∈ D.1 ∨
            anyAbort (colInbox K D count rnd v b.2 i) = true) from hi, if_false]
        dsimp only [k2, ab, out2, inbox]
        unfold exchangeResume anyAbort
        split_ifs <;> first | rfl | contradiction)]
    simp only [pure_bind, executeRounds]
    rfl

/-- The pointwise collector obligations, separated from scheduling, randomness,
and adversarial oracle queries. The output relation includes the recorded state. -/
def TreeSimCollectorTranscriptRel (D : C.Coalition) (count : ℕ)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (R : C.Party → (Shares C Bit × RunState C) → (Shares C Bit × RunState C) → Prop) : Prop :=
  colMsgs1 K D count rnd₁ v₁ = colMsgs1 K D count rnd₂ v₂ ∧
  (∀ sent, colMsgs2 K D count rnd₁ v₁ sent = colMsgs2 K D count rnd₂ v₂ sent) ∧
  ∀ sent sent' i, Option.Rel (R i)
    ((colOuts K D count rnd₁ v₁ sent sent' i).map fun out =>
      (out, ⟨recordMode K .collector i (st₁ i).history out count, (st₁ i).label + 1, (st₁ i).tag⟩))
    ((colOuts K D count rnd₂ v₂ sent sent' i).map fun out =>
      (out, ⟨recordMode K .collector i (st₂ i).history out count, (st₂ i).label + 1, (st₂ i).tag⟩))

/-- Both live rushing calls preserve the shared-cache relation, including
selective abort and early termination. No randomness is resampled between calls. -/
theorem treeSim_collector_exchange_mixed (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (δ : HiddenAddress C → Bit) (count : ℕ)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (R : C.Party → (Shares C Bit × RunState C) → (Shares C Bit × RunState C) → Prop)
    (hm : TreeSimCollectorTranscriptRel K D count rnd₁ rnd₂ v₁ v₂ st₁ st₂ R)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeSimCollectorExchange K D A state count rnd₁ v₁ st₁)).run a)
      ((simulateQ (streamWorld prims D)
        (treeSimCollectorExchange K D A state count rnd₂ v₂ st₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ (∀ i, Option.Rel (R i) (u.1.2 i) (z.1.2 i)) ∧
        TreeSimStreamRel δ u.2 z.2) := by
  unfold treeSimCollectorExchange
  simp only [simulateQ_bind, StateT.run_bind]
  rw [hm.1]
  apply relTriple_bind (treeSim_local_streamRel prims D δ _ a b hs)
  intro r₁ r₂ hr
  rcases r₁ with ⟨r₁, a'⟩
  rcases r₂ with ⟨r₂, b'⟩
  dsimp only at hr ⊢
  rcases hr with ⟨rfl, hs'⟩
  simp only [anyAbort_colInbox]
  split_ifs with hall
  · simp only [simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨rfl, fun _ => Option.Rel.none, hs'⟩
  · simp only [simulateQ_bind, StateT.run_bind]
    rw [hm.2.1]
    apply relTriple_bind (treeSim_local_streamRel prims D δ _ a' b' hs')
    intro t₁ t₂ ht
    simp only [simulateQ_pure, StateT.run_pure]
    apply relTriple_pure_pure
    rw [ht.1]
    exact ⟨rfl, hm.2.2 _ t₂.1.2, ht.2⟩

/-- All honest collector masks, queried in the actual operator order. -/
def treeSimCollectorDraws (D : C.Coalition) (ctx : C.Party → Context C)
    (idx count : ℕ) (st : C.Party → RunState C) :
    OracleComp (WorldSpec C) (C.Party → PrssOutput C Bit) :=
  Concrete.sequenceFin fun i => if i ∈ D.1 then pure 0 else
    free (liftComp (prssDraw (ctx i) (bitCodec (E := E)) (st i).label idx count) (LocalSpec C))

/-- Actual collector program before its PRSS draw. -/
def treeSimCollectorProgram (ctx : Context C) (idx count : ℕ) (v : ℕ → Bit)
    (st : RunState C) : PartyM C E RealSpec (Shares C Bit × RunState C) :=
  (prssRandomness ctx (bitCodec (E := E)) idx count >>= fun o =>
    reshareCollector K ctx o v count).run st

/-- One complete actual collector gadget, including both network rounds. -/
def treeSimCollectorRound (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (ctx : C.Party → Context C) (idx count : ℕ)
    (v : C.Party → ℕ → Bit) (st : C.Party → RunState C) :
    OracleComp (WorldSpec C) (A.State × (C.Party → Option (Shares C Bit × RunState C))) := do
  let steps ← startSteps worldRoles D (fun i => treeSimCollectorProgram K (ctx i) idx count (v i) (st i))
  executeRounds worldRoles D A noFunctionality 2 state steps

/-- The whole real collector gadget factors through its actual masks and the
abort-aware exchanges, without introducing a fresh randomness functionality. -/
theorem treeSim_collector_round_factor (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (idx count : ℕ) (v : C.Party → ℕ → Bit) (st : C.Party → RunState C) :
    treeSimCollectorRound K D A state ctx idx count v st = (do
      let rnd ← treeSimCollectorDraws (E := E) D ctx idx count st
      treeSimCollectorExchange K D A state count rnd v st) := by
  have hstart : startSteps worldRoles D
      (fun i => treeSimCollectorProgram K (ctx i) idx count (v i) (st i)) =
      (do let rnd ← treeSimCollectorDraws (E := E) D ctx idx count st
          pure (fun i => if i ∈ D.1 then .done none else
            treeSimCollectorStep K (ctx i) (rnd i) (v i) count (st i) pure)) := by
    unfold startSteps treeSimCollectorDraws
    rw [← sequenceFin_bind_pure _ (fun i (rnd : PrssOutput C Bit) =>
      if i ∈ D.1 then Step.done none else treeSimCollectorStep K (ctx i) rnd (v i) count (st i) pure)]
    congr 1
    funext i
    by_cases hi : i ∈ D.1
    · simp [hi]
    · simp only [if_neg hi]
      simpa only [treeSimCollectorProgram, bind_pure, map_eq_bind_pure_comp, Function.comp_def] using
        treeSim_collector_entry K (ctx i) idx count (v i) (st i) pure
  unfold treeSimCollectorRound
  rw [hstart]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro rnd
  exact treeSim_collector_exchange_eq K D A state ctx self count rnd v st

/-- The concrete translation of all masks returned by the collector's PRSS reads. -/
def TreeSimCollectorMasksRel (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (ctx : C.Party → Context C) (idx count : ℕ) (st : C.Party → RunState C)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) : Prop :=
  ∀ i, i ∉ D.1 →
    (rnd₂ i).1 = (rnd₁ i).1 + (treeSimPrssShift δ (ctx i) (st i).label idx count).1 ∧
    (rnd₂ i).2 = (rnd₁ i).2 + (treeSimPrssShift δ (ctx i) (st i).label idx count).2

/-- Collector draws use one shared cache, including repeated holders and keys
visible to the adversary. This is the real PRSS operation, not `F_rand`. -/
theorem treeSim_collector_draws_mixed (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx₁ ctx₂ : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx₁ i).self = (ctx₂ i).self)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (idx count : ℕ) (st₁ st₂ : C.Party → RunState C)
    (lab : ∀ i, i ∉ D.1 → (st₁ i).label = (st₂ i).label)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeSimCollectorDraws (E := E) D ctx₁ idx count st₁)).run a)
      ((simulateQ (streamWorld prims D)
        (treeSimCollectorDraws (E := E) D ctx₂ idx count st₂)).run b)
      (fun u z => TreeSimCollectorMasksRel D δ ctx₁ idx count st₁ u.1 z.1 ∧
        TreeSimStreamRel δ u.2 z.2) := by
  unfold treeSimCollectorDraws TreeSimCollectorMasksRel
  rw [simulateQ_sequenceFin, simulateQ_sequenceFin]
  apply treeSim_sequenceFin_rel _ _ (TreeSimStreamRel δ)
    (fun i (x y : PrssOutput C Bit) => i ∉ D.1 →
      y.1 = x.1 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count).1 ∧
      y.2 = x.2 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count).2)
  · intro i s₁ s₂ hstate
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨fun h => (h hi).elim, hstate⟩
    · simp only [if_neg hi]
      rw [← treeSim_prssDraw_context (ctx₁ i) (ctx₂ i) (self i hi) (keys i hi), ← lab i hi]
      apply relTriple_post_mono (treeSim_prssBits_mixed prims D δ hδ (ctx₁ i)
        (st₁ i).label idx count s₁ s₂ hstate)
      intro u z h
      exact ⟨fun _ => ⟨h.1, h.2.1⟩, h.2.2⟩
  · exact hs

/-- The remaining collector algebra is a named, pointwise obligation. Its
arguments are the actual translated masks; it has no probabilistic premise. -/
def TreeSimCollectorAlgebra (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (ctx : C.Party → Context C) (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (R : C.Party → (Shares C Bit × RunState C) → (Shares C Bit × RunState C) → Prop) : Prop :=
  ∀ rnd₁ rnd₂, TreeSimCollectorMasksRel D δ ctx idx count st₁ rnd₁ rnd₂ →
    TreeSimCollectorTranscriptRel K D count rnd₁ rnd₂ v₁ v₂ st₁ st₂ R

/-- The complete collector stage with the real PRSS gadget and both actual
network rounds. Only the pointwise algebra is assumed; cache handling,
stateful rushing calls, early termination and output scheduling are proved. -/
theorem treeSim_collector_round_mixed (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (δ : HiddenAddress C → Bit) (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab : ∀ i, i ∉ D.1 → (st₁ i).label = (st₂ i).label)
    (R : C.Party → (Shares C Bit × RunState C) → (Shares C Bit × RunState C) → Prop)
    (algebra : TreeSimCollectorAlgebra K D δ ctx₁ idx count v₁ v₂ st₁ st₂ R)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeSimCollectorRound K D A state ctx₁ idx count v₁ st₁)).run a)
      ((simulateQ (streamWorld prims D)
        (treeSimCollectorRound K D A state ctx₂ idx count v₂ st₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧ (∀ i, Option.Rel (R i) (u.1.2 i) (z.1.2 i)) ∧
        TreeSimStreamRel δ u.2 z.2) := by
  rw [treeSim_collector_round_factor K D A state ctx₁ self₁,
    treeSim_collector_round_factor K D A state ctx₂ self₂]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_collector_draws_mixed prims D δ hδ ctx₁ ctx₂
    (fun i hi => (self₁ i hi).trans (self₂ i hi).symm) keys idx count st₁ st₂ lab a b hs)
  intro u z h
  exact treeSim_collector_exchange_mixed prims K D A state δ count u.1 z.1 v₁ v₂ st₁ st₂ R
    (algebra u.1 z.1 h.1) u.2 z.2 h.2

/-- The GS20 mask translation adapted to the note's collector mode,
restricted to this PRSS block. -/
def treeSimCollectorShift (D : C.Coalition) (T₀ : C.Term) (ρ idx count : ℕ)
    (difference : C.Party → ℕ → Bit) : HiddenAddress C → Bit :=
  treeSimBlockShift D ρ idx count (ΔC K D T₀ difference 0)
    (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) difference 0))

/-- Collector contributions are affine in arbitrary local masks. The base
masks need not be independent or consistent across operators. -/
theorem treeSim_colU_add (D : C.Coalition) (count : ℕ)
    (dt : C.Term → Fin count → Bit) (dp : C.Pair → Fin count → Bit)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit)
    (masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0 dt dp i)
    (v₁ v₂ : C.Party → ℕ → Bit) (i : C.Party) (hi : i ∉ D.1) (g : ℕ) :
    colU K i (rnd₂ i).1 (rnd₂ i).2 (v₂ i) g =
      colU K i (rnd₁ i).1 (rnd₁ i).2 (v₁ i) g +
        colUVal K D 0 0 dt dp (v₁ - v₂) i g := by
  have he := colU_frandShare K D (0 : Shares C Bit) 0 dt dp (v₁ - v₂) i g
  rw [masks i hi]
  simp only [colU, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.sub_apply,
    Finset.sum_add_distrib] at he ⊢
  have htwo := bit_add_self (v₁ i g - v₂ i g)
  linear_combination he - htwo

/-- Normalize an honest collector's sum for arbitrary base masks. -/
theorem treeSim_colSum_value (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (sent : C.Party → Mail C E) (g : ℕ) (hg : g < count)
    (honest : (K.collector g).2 ∉ D.1) :
    let κ := (K.collector g).2
    colSum K κ (rnd κ).1 (rnd κ).2 (v κ) count (colInbox K D count rnd v sent κ) g =
      (∑ j ∈ Finset.univ.filter (· ∉ D.1), colU K j (rnd j).1 (rnd j).2 (v j) g) +
      ∑ j ∈ D.1, Msg.bitAt (sent j κ) ((collectedBy K count κ).idxOf g) := by
  intro κ
  let F : C.Party → Bit := fun j => if j ∈ D.1 then
    Msg.bitAt (sent j κ) ((collectedBy K count κ).idxOf g) else
      colU K j (rnd j).1 (rnd j).2 (v j) g
  have hF : ∀ j ∈ Finset.univ.erase κ,
      Msg.bitAt (colInbox K D count rnd v sent κ j) ((collectedBy K count κ).idxOf g) = F j := by
    intro j hj
    have hjκ := Finset.ne_of_mem_erase hj
    by_cases hjD : j ∈ D.1
    · simp [colInbox, F, hjD]
    · simp only [colInbox, F, if_neg hjD, colOut1, if_pos (Ne.symm hjκ), Msg.bitAt]
      exact getD_map_idxOf (mem_collectedBy K hg) _
  unfold colSum
  rw [Finset.sum_congr rfl hF]
  have hκF : colU K κ (rnd κ).1 (rnd κ).2 (v κ) g = F κ := by
    simp only [F, κ, if_neg honest]
  rw [hκF, Finset.add_sum_erase _ _ (Finset.mem_univ κ)]
  simp only [F, Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter]
  ring

/-- A mask translation changes an honest collector's sum by the zero-base
execution, even for recipient-dependent malicious messages. -/
theorem treeSim_colSum_add (D : C.Coalition) (count : ℕ)
    (dt : C.Term → Fin count → Bit) (dp : C.Pair → Fin count → Bit)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit)
    (masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0 dt dp i)
    (v₁ v₂ : C.Party → ℕ → Bit) (sent : C.Party → Mail C E)
    (g : ℕ) (hg : g < count) (honest : (K.collector g).2 ∉ D.1) :
    let κ := (K.collector g).2
    colSum K κ (rnd₂ κ).1 (rnd₂ κ).2 (v₂ κ) count (colInbox K D count rnd₂ v₂ sent κ) g =
      colSum K κ (rnd₁ κ).1 (rnd₁ κ).2 (v₁ κ) count (colInbox K D count rnd₁ v₁ sent κ) g +
        colSumVal K D 0 0 dt dp (v₁ - v₂) (fun _ _ => none) κ g := by
  dsimp only
  rw [treeSim_colSum_value K D count rnd₂ v₂ sent g hg honest,
    treeSim_colSum_value K D count rnd₁ v₁ sent g hg honest]
  have hu := Finset.sum_congr (s₁ := Finset.univ.filter (· ∉ D.1)) rfl
    (fun j hj => treeSim_colU_add K D count dt dp rnd₁ rnd₂ masks v₁ v₂ j (Finset.mem_filter.mp hj).2 g)
  rw [hu]
  simp only [Finset.sum_add_distrib, colSumVal, Msg.bitAt, Finset.sum_const_zero, add_zero]
  ring

/-- The zero-base collector translation hides every first-round message to
a corrupt collector, and moves only the sum whose collected term is `T₀`. -/
theorem treeSim_collector_virtual (D : C.Coalition) (count : ℕ) (T₀ : C.Term)
    (hidden : ¬ KnownTo D.1 T₀) (honest : K.owner T₀ ∉ D.1)
    (d : C.Party → ℕ → Bit) (g : ℕ) (hg : g < count) :
    let dt := ΔC K D T₀ d (0 : C.Term → Fin count → Bit)
    let dp := pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) d (0 : C.Term → Fin count → Bit))
    ((K.collector g).2 ∈ D.1 → ∀ i, i ∉ D.1 → colUVal K D 0 0 dt dp d i g = 0) ∧
    ((K.collector g).2 ∉ D.1 →
      colSumVal K D 0 0 dt dp d (fun _ _ => none) (K.collector g).2 g =
        if (K.collector g).1 = T₀ then ∑ j ∈ Finset.univ.filter (· ∉ D.1), d j g else 0) := by
  dsimp only
  constructor
  · intro hc i hi
    have h := colUVal_corrupt K D (0 : Shares C Bit) 0 (0 : C.Term → Fin count → Bit) 0
      T₀ hidden honest d 0 i hi g hg hc
    simpa [colUVal, randVal, pairVal] using h
  · intro hc
    have h := colSumVal_honest K D (0 : Shares C Bit) 0 (0 : C.Term → Fin count → Bit) 0
      T₀ hidden honest d 0 (fun _ _ => none) g hg hc
    simp only [zero_add] at h
    rw [h]
    simp only [colSumVal, colUVal, randVal, pairVal, Pi.zero_apply, ite_self, add_zero,
      Finset.sum_const_zero, Msg.bitAt, zero_add, γC]
    by_cases he : (K.collector g).1 = T₀
    · simp [he]
    · simp [he, Ne.symm he, bit_add_self]

/-- The adapted GS20 translation preserves both corrupt views for arbitrary
base masks, and places the honest sum difference at the first lacked term. -/
theorem treeSim_collector_balance (D : C.Coalition) (count : ℕ) (T₀ : C.Term)
    (hidden : ¬ KnownTo D.1 T₀) (honest : K.owner T₀ ∉ D.1)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (v₁ v₂ : C.Party → ℕ → Bit)
    (masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0
      (ΔC K D T₀ (v₁ - v₂) 0) (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i) :
    colMsgs1 K D count rnd₁ v₁ = colMsgs1 K D count rnd₂ v₂ ∧
    (∀ sent, colMsgs2 K D count rnd₁ v₁ sent = colMsgs2 K D count rnd₂ v₂ sent) ∧
    ∀ sent g, g < count → (K.collector g).2 ∉ D.1 →
      let κ := (K.collector g).2
      colSum K κ (rnd₂ κ).1 (rnd₂ κ).2 (v₂ κ) count (colInbox K D count rnd₂ v₂ sent κ) g =
        colSum K κ (rnd₁ κ).1 (rnd₁ κ).2 (v₁ κ) count (colInbox K D count rnd₁ v₁ sent κ) g +
          if (K.collector g).1 = T₀ then ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g else 0 := by
  have hs : ∀ sent g, g < count → (K.collector g).2 ∉ D.1 →
      let κ := (K.collector g).2
      colSum K κ (rnd₂ κ).1 (rnd₂ κ).2 (v₂ κ) count (colInbox K D count rnd₂ v₂ sent κ) g =
        colSum K κ (rnd₁ κ).1 (rnd₁ κ).2 (v₁ κ) count (colInbox K D count rnd₁ v₁ sent κ) g +
          if (K.collector g).1 = T₀ then ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g else 0 := by
    intro sent g hg hc
    dsimp only
    rw [treeSim_colSum_add K D count _ _ rnd₁ rnd₂ masks v₁ v₂ sent g hg hc,
      (treeSim_collector_virtual K D count T₀ hidden honest (v₁ - v₂) g hg).2 hc]
  refine ⟨?_, ?_, hs⟩
  · funext c i
    unfold colMsgs1
    split_ifs with h
    · unfold colOut1
      split_ifs
      · congr 2
        apply List.map_congr_left
        intro g hg
        simp only [collectedBy, List.mem_filter, List.mem_range, decide_eq_true_eq] at hg
        rw [treeSim_colU_add K D count _ _ rnd₁ rnd₂ masks v₁ v₂ i h.2,
          (treeSim_collector_virtual K D count T₀ hidden honest (v₁ - v₂) g hg.1).1
            (hg.2 ▸ h.1) i h.2, add_zero]
      · rfl
    · rfl
  · intro sent
    funext c i
    unfold colMsgs2
    simp only [anyAbort_colInbox]
    split_ifs with h
    · unfold colOut2
      split_ifs
      · congr 2
        apply List.map_congr_left
        intro g hg
        simp only [forwardedTo, collectedBy, List.mem_filter, List.mem_range, decide_eq_true_eq] at hg
        obtain ⟨⟨hgc, hκ⟩, hc⟩ := hg
        subst i
        have hn : (K.collector g).1 ≠ T₀ := fun he => hidden (he ▸ ⟨c, h.1, hc⟩)
        rw [hs sent g hgc h.2.1, if_neg hn, add_zero]
      · rfl
    · rfl

/-- Read a forwarded collector value without assuming consistent base masks. -/
theorem treeSim_colZ_value (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (sent sent' : C.Party → Mail C E) (ab : C.Party → Bool)
    (hab : ∀ k, k ∉ D.1 → ab k = false)
    (i : C.Party) (hi : i ∉ D.1) (T : C.Term) (held : i ∈ C.holders T)
    (g : ℕ) (hg : g < count) :
    colZ K i (rnd i).1 (rnd i).2 (v i) count (colInbox K D count rnd v sent i)
      (fun k => if k ∈ D.1 then sent' k i else if ab k then some .abort else
        colOut2 K k (rnd k).1 (rnd k).2 (v k) count (colInbox K D count rnd v sent k) i) T g =
      if T = (K.collector g).1 then
        if (K.collector g).2 ∈ D.1 then
          Msg.bitAt (sent' (K.collector g).2 i) ((forwardedTo K count (K.collector g).2 i).idxOf g)
        else colSum K (K.collector g).2 (rnd (K.collector g).2).1 (rnd (K.collector g).2).2
          (v (K.collector g).2) count (colInbox K D count rnd v sent (K.collector g).2) g
      else (rnd i).1 T g := by
  unfold colZ
  rw [if_neg (by simp [held, Nat.not_le.mpr hg])]
  by_cases ht : T = (K.collector g).1
  · rw [if_pos ht, if_pos ht]
    by_cases hc : (K.collector g).2 = i
    · subst i
      simp only [if_pos rfl, if_neg hi, ite_true]
    · rw [if_neg hc]
      by_cases hd : (K.collector g).2 ∈ D.1
      · simp only [if_pos hd]
      · simp only [if_neg hd, hab _ hd, Bool.false_eq_true, if_false, colOut2,
          if_pos (Ne.symm hc), Msg.bitAt]
        apply getD_map_idxOf
        simp only [forwardedTo, List.mem_filter, decide_eq_true_eq]
        exact ⟨mem_collectedBy K hg, ht ▸ held⟩
  · simp only [if_neg ht]

/-- Collector outputs differ only at `T₀`, after arbitrary common malicious
messages. This statement also retains every abort, including propagated aborts. -/
theorem treeSim_collector_outputs_pivot (D : C.Coalition) (count : ℕ) (T₀ : C.Term)
    (hT₀ : lackedTerm D.1 = some T₀)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (v₁ v₂ : C.Party → ℕ → Bit)
    (masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0
      (ΔC K D T₀ (v₁ - v₂) 0) (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i)
    (sent sent' : C.Party → Mail C E) (i : C.Party) :
    Option.Rel (fun x y => y = treeSimHeldShift D i count
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g) x)
      (colOuts K D count rnd₁ v₁ sent sent' i) (colOuts K D count rnd₂ v₂ sent sent' i) := by
  have hidden := main_lacked_unknown D T₀ hT₀
  have honest : K.owner T₀ ∉ D.1 := fun hi => hidden ⟨_, hi, K.owner_held T₀⟩
  have hs := (treeSim_collector_balance K D count T₀ hidden honest rnd₁ rnd₂ v₁ v₂ masks).2.2
  unfold colOuts
  dsimp only
  simp only [anyAbort_colForward]
  simp only [anyAbort_colInbox]
  by_cases hi : i ∈ D.1
  · simp only [hi, true_or, if_true]
    exact Option.Rel.none
  by_cases h1 : anyAbort (fun k => if k ∈ D.1 then sent k i else (none : Option (Msg E))) = true
  · simp only [h1, or_true, if_true]
    exact Option.Rel.none
  by_cases h2 : anyAbort (fun k => if k ∈ D.1 then sent' k i else
      if anyAbort (fun k' => if k' ∈ D.1 then sent k' k else (none : Option (Msg E))) = true
        then some .abort else none) = true
  · simp only [hi, h1, Bool.false_eq_true, or_self, if_false, h2, if_true]
    exact Option.Rel.none
  have hall : ∀ k, k ∉ D.1 →
      anyAbort (fun k' => if k' ∈ D.1 then sent k' k else (none : Option (Msg E))) = false := by
    intro k hk
    by_contra hc
    apply h2
    unfold anyAbort
    rw [List.any_eq_true]
    refine ⟨k, by simp [Committee.parties], ?_⟩
    have hc' := Bool.eq_true_of_not_eq_false hc
    unfold anyAbort at hc'
    simp only [hk, if_false, hc', if_true]
    rfl
  simp only [hi, h1, h2, Bool.false_eq_true, or_self, if_false]
  apply Option.Rel.some
  funext T g
  by_cases hb : i ∈ C.holders T ∧ g < count
  · rw [treeSim_colZ_value K D count rnd₂ v₂ sent sent' _ hall i hi T hb.1 g hb.2]
    unfold treeSimHeldShift
    rw [treeSim_colZ_value K D count rnd₁ v₁ sent sent' _ hall i hi T hb.1 g hb.2]
    by_cases ht : T = (K.collector g).1
    · rw [if_pos ht, if_pos ht]
      by_cases hc : (K.collector g).2 ∈ D.1
      · have hn : lackedTerm D.1 ≠ some T := by
          intro he
          have heq : T = T₀ := Option.some.inj (he.symm.trans hT₀)
          exact hidden (heq ▸ ⟨_, hc, ht ▸ K.collector_held g⟩)
        simp only [if_pos hc, hn, and_false, if_false, add_zero]
      · rw [if_neg hc, if_neg hc, hs sent g hb.2 hc]
        by_cases he : (K.collector g).1 = T₀
        · have held0 : i ∈ C.holders T₀ := (ht.trans he) ▸ hb.1
          simp [he, ht, hb.2, held0, hT₀]
        · have hn : lackedTerm D.1 ≠ some T := by
            intro h
            exact he (ht.symm.trans (Option.some.inj (h.symm.trans hT₀)))
          simp [he, hn]
    · rw [if_neg ht, if_neg ht, masks i hi]
      simp only [Prod.fst_add, Pi.add_apply]
      rw [frandShare_fst D (0 : Shares C Bit) 0 _ _ i T g hb.1]
      by_cases he : T = T₀
      · subst T
        simp [randVal, hb, hidden, hT₀, ΔC, Δ0C, γC, ht]
      · have hn : lackedTerm D.1 ≠ some T := by
          intro h
          exact he (Option.some.inj (h.symm.trans hT₀))
        simp [randVal, hb, hn, ΔC, Δ0C, he]
  · have hout : i ∉ C.holders T ∨ count ≤ g := by
      by_cases hh : i ∈ C.holders T
      · exact Or.inr (Nat.le_of_not_gt (fun hg => hb ⟨hh, hg⟩))
      · exact Or.inl hh
    have hn : ¬ (i ∈ C.holders T ∧ g < count ∧ lackedTerm D.1 = some T) :=
      fun h => hb ⟨h.1, h.2.1⟩
    simp only [colZ, treeSimHeldShift, if_pos hout, if_neg hn, add_zero]

/-- The history shift records exactly the positions selected by this mode. -/
def treeSimHistoryAppendMode (mode : ReshareMode) (T₀ : C.Term) (count : ℕ)
    (past : List Bit) (difference : ℕ → Bit) : List Bit :=
  past ++ ((List.range count).filter fun g => (filler K mode T₀ g).isSome).map difference

/-- Recording a translated sharing preserves the common, exact history shift
in either reshare mode. -/
theorem treeSim_recordMode_shift (D : C.Coalition) (mode : ReshareMode)
    (T₀ : C.Term) (hT₀ : lackedTerm D.1 = some T₀)
    (i : C.Party) (count : ℕ) (past : List Bit) (difference : ℕ → Bit)
    (h₁ h₂ : C.Term → List Bit) (hh : TreeSimHistoryRel D i past h₁ h₂)
    (z₁ z₂ : Shares C Bit) (hz : z₂ = treeSimHeldShift D i count difference z₁) :
    TreeSimHistoryRel D i (treeSimHistoryAppendMode K mode T₀ count past difference)
      (recordMode K mode i h₁ z₁ count) (recordMode K mode i h₂ z₂ count) := by
  intro T
  have h := hh T
  by_cases ht : i ∈ C.holders T ∧ lackedTerm D.1 = some T
  · have hEq : T = T₀ := Option.some.inj (ht.2.symm.trans hT₀)
    subst T
    rw [if_pos ht] at h ⊢
    simp only [recordMode, if_pos ht.1, bitCodec, Function.comp_def, ← List.map_eq_flatMap]
    constructor
    · simp [treeSimHistoryAppendMode, h.1]
    · rw [treeSimHistoryAppendMode, List.zipWith_append h.1, h.2, List.zipWith_map, List.zipWith_self]
      congr 1
      apply List.map_congr_left
      intro g hg
      have hg' := List.mem_range.mp (List.mem_filter.mp hg).1
      simp [hz, treeSimHeldShift, ht.1, hT₀, hg']
  · rw [if_neg ht] at h ⊢
    by_cases held : i ∈ C.holders T
    · have hn : lackedTerm D.1 ≠ some T := fun hp => ht ⟨held, hp⟩
      have he : z₂ T = z₁ T := by
        funext g
        simp [hz, treeSimHeldShift, hn]
      simp [recordMode, held, h, he]
    · simp [recordMode, held, h]

/-- The successful collector result carries the translated sharing and its
actual history, with the same label and tag. -/
def TreeSimCollectorResultRel (D : C.Coalition) (T₀ : C.Term) (count : ℕ)
    (history : List Bit) (difference : ℕ → Bit) (i : C.Party)
    (x y : Shares C Bit × RunState C) : Prop :=
  y.1 = treeSimHeldShift D i count difference x.1 ∧
    TreeSimRunStateRel D i (treeSimHistoryAppendMode K .collector T₀ count history difference) x.2 y.2

/-- Discharge the pointwise collector obligations, including the exact
history update, from the adapted GS20 mask translation. -/
theorem treeSim_collector_transcript_pivot (D : C.Coalition) (count : ℕ) (T₀ : C.Term)
    (hT₀ : lackedTerm D.1 = some T₀)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (v₁ v₂ : C.Party → ℕ → Bit)
    (masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0
      (ΔC K D T₀ (v₁ - v₂) 0) (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i)
    (history : List Bit) (st₁ st₂ : C.Party → RunState C)
    (hstate : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i)) :
    TreeSimCollectorTranscriptRel K D count rnd₁ rnd₂ v₁ v₂ st₁ st₂
      (TreeSimCollectorResultRel K D T₀ count history
        (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g)) := by
  have hidden := main_lacked_unknown D T₀ hT₀
  have honest : K.owner T₀ ∉ D.1 := fun hi => hidden ⟨_, hi, K.owner_held T₀⟩
  have hb := treeSim_collector_balance K D count T₀ hidden honest rnd₁ rnd₂ v₁ v₂ masks
  refine ⟨hb.1, hb.2.1, ?_⟩
  intro sent sent' i
  by_cases hi : i ∈ D.1
  · simp only [colOuts, hi, true_or, if_true, Option.map_none]
    exact Option.Rel.none
  · have ho := treeSim_collector_outputs_pivot K D count T₀ hT₀ rnd₁ rnd₂ v₁ v₂ masks sent sent' i
    generalize colOuts K D count rnd₁ v₁ sent sent' i = left at ho ⊢
    generalize colOuts K D count rnd₂ v₂ sent sent' i = right at ho ⊢
    cases ho with
    | none => exact Option.Rel.none
    | some hz =>
      apply Option.Rel.some
      refine ⟨hz, congrArg (· + 1) (hstate i hi).1, (hstate i hi).2.1, ?_⟩
      exact treeSim_recordMode_shift K D .collector T₀ hT₀ i count history _ _ _
        (hstate i hi).2.2 _ _ hz

/-- Complete collector simulation by the adapted GS20 translation. Earlier
mask translations remain in the shared cache; this fresh block adds its own
translation. No collector algebra or exchange obligation remains assumed. -/
theorem treeSim_collector_round_state (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (T₀ : C.Term) (hT₀ : lackedTerm D.1 = some T₀)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ)
    (history : List Bit) (hstate : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂) x = 0) :
    let δ := past + treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂)
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeSimCollectorRound K D A state ctx₁ idx count v₁ st₁)).run a)
      ((simulateQ (streamWorld prims D)
        (treeSimCollectorRound K D A state ctx₂ idx count v₂ st₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧
        (∀ i, Option.Rel (TreeSimCollectorResultRel K D T₀ count history
          (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g) i)
          (u.1.2 i) (z.1.2 i)) ∧ TreeSimStreamRel δ u.2 z.2) := by
  intro δ
  have hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0 := by
    intro x hx
    simp only [δ, Pi.add_apply, visible x hx, treeSimCollectorShift,
      treeSim_blockShift_visible D ρ idx count _ _ x hx, add_zero]
  apply treeSim_collector_round_mixed prims K D A state δ hδ ctx₁ ctx₂ self₁ self₂ keys
    idx count v₁ v₂ st₁ st₂ (fun i hi => (lab₁ i hi).trans (lab₂ i hi).symm) _ _ a b
    ⟨hs.1, treeSim_hiddenRel_extend past _ hs.2 fresh⟩
  intro rnd₁ rnd₂ hm
  apply treeSim_collector_transcript_pivot K D count T₀ hT₀ rnd₁ rnd₂ v₁ v₂ _ history st₁ st₂ hstate
  intro i hi
  have hshift : treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count =
      frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
        (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i := by
    rw [lab₁ i hi]
    dsimp only [δ]
    rw [treeSim_prssShift_add, treeSim_prssShift_zero past (ctx₁ i) ρ idx count block, zero_add]
    unfold treeSimCollectorShift
    rw [treeSim_prssShift_block D (ctx₁ i) (by simpa [self₁ i hi] using hi), self₁ i hi]
  have hm' := hm i hi
  rw [hshift] at hm'
  exact Prod.ext hm'.1 hm'.2

/-- One complete multiplication in collector mode, using the frozen real gadget. -/
def treeSimMultCollectorRound (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (ctx : C.Party → Context C) (count : ℕ)
    (x y : C.Party → Shares C Bit) (st : C.Party → RunState C) :
    OracleComp (WorldSpec C) (A.State × (C.Party → Option (Shares C Bit × RunState C))) := do
  let steps ← startSteps worldRoles D
    (fun i => ((realRunGadgets K (ctx i) .collector).mult (x i) (y i) count).run (st i))
  executeRounds worldRoles D A noFunctionality 2 state steps

theorem treeSim_multCollector_round_eq (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (state : A.State) (ctx : C.Party → Context C) (count : ℕ)
    (x y : C.Party → Shares C Bit) (st : C.Party → RunState C) :
    treeSimMultCollectorRound K D A state ctx count x y st =
      treeSimCollectorRound K D A state ctx 0 count (fun i => mulRep K (ctx i) (x i) (y i)) st := by
  simp only [treeSimMultCollectorRound, treeSimCollectorRound, treeSimCollectorProgram,
    realRunGadgets, reshareWith]

/-- The frozen collector multiplication preserves the exact sharing/history
translation, with difference given by the honest additive `MulRep` values. -/
theorem treeSim_multCollector_round (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (T₀ : C.Term) (hT₀ : lackedTerm D.1 = some T₀)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ count : ℕ) (x₁ y₁ x₂ y₂ : C.Party → Shares C Bit) (st₁ st₂ : C.Party → RunState C)
    (lab : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (history : List Bit) (hstate : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, 0, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b) :
    let v₁ := fun i => mulRep K (ctx₁ i) (x₁ i) (y₁ i)
    let v₂ := fun i => mulRep K (ctx₂ i) (x₂ i) (y₂ i)
    let difference := fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g
    (∀ x, (a.1.2 x).isSome → treeSimCollectorShift K D T₀ ρ 0 count (v₁ - v₂) x = 0) →
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeSimMultCollectorRound K D A state ctx₁ count x₁ y₁ st₁)).run a)
      ((simulateQ (streamWorld prims D)
        (treeSimMultCollectorRound K D A state ctx₂ count x₂ y₂ st₂)).run b)
      (fun u z => u.1.1 = z.1.1 ∧
        (∀ i, Option.Rel (TreeSimCollectorResultRel K D T₀ count history difference i)
          (u.1.2 i) (z.1.2 i)) ∧
        TreeSimStreamRel (past + treeSimCollectorShift K D T₀ ρ 0 count (v₁ - v₂)) u.2 z.2) := by
  intro v₁ v₂ difference fresh
  rw [treeSim_multCollector_round_eq, treeSim_multCollector_round_eq]
  exact treeSim_collector_round_state prims K D A state T₀ hT₀ ctx₁ ctx₂ self₁ self₂ keys
    ρ 0 count v₁ v₂ st₁ st₂ lab (fun i hi => (hstate i hi).1.symm.trans (lab i hi))
    history hstate past visible block a b hs fresh

/-- The collector's first communication boundary, with arbitrary ceremony
continuations. The context has already supplied its real PRSS masks. -/
def treeSimCollectorWaiting {α : Type} (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    C.Party → Step C E RealSpec α := fun i =>
  if i ∈ D.1 then .done none else
    treeSimCollectorStep K (localContext i) (rnd i) (v i) count (st i) (k i)

/-- The intermediate collector boundary retains the first rushing reply and
any operators that have already aborted. -/
def treeSimCollectorAfterFirst {α : Type} (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) : C.Party → Step C E RealSpec α := fun i =>
  let inbox := colInbox K D count rnd v sent i
  if i ∈ D.1 ∨ anyAbort inbox then .done none else
    .wait (colOut2 K i (rnd i).1 (rnd i).2 (v i) count inbox)
      (exchangeResume fun forward =>
        let out := colZ K i (rnd i).1 (rnd i).2 (v i) count inbox forward
        k i (out, ⟨recordMode K .collector i (st i).history out count, (st i).label + 1, (st i).tag⟩))

/-- The initial collector boundary exposes exactly the first corrupt view. -/
theorem treeSim_collector_waiting_view {α : Type} (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    treeSimRoundView D (treeSimCollectorWaiting K D count rnd v st k) = colMsgs1 K D count rnd v := by
  funext c i
  by_cases hi : i ∈ D.1
  · simp [treeSimRoundView, colMsgs1, hi]
  · simp [treeSimRoundView, treeSimCollectorWaiting, treeSimCollectorStep, localContext,
      Step.outbox, colMsgs1, hi]

/-- Resolve just the first exchange; the continuation is still suspended. -/
theorem treeSim_collector_first_local {α : Type} (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (treeSimCollectorWaiting K D count rnd v st k) sent i =
      pure (treeSimCollectorAfterFirst K D count rnd v st k sent i) := by
  by_cases hi : i ∈ D.1
  · simp only [roundLocal, treeSimCollectorWaiting, if_pos hi, treeSimCollectorAfterFirst, hi, true_or, if_true]
  · have hin : (fun j => if j ∈ D.1 then sent j i else
        (treeSimCollectorWaiting K D count rnd v st k j).delivered i) =
        colInbox K D count rnd v sent i := by
      funext j
      by_cases hj : j ∈ D.1 <;>
        simp [colInbox, treeSimCollectorWaiting, treeSimCollectorStep, localContext, Step.delivered, hj]
    simp only [roundLocal, treeSimCollectorWaiting, if_neg hi, treeSimCollectorStep, localContext]
    simp only [treeSimCollectorWaiting, treeSimCollectorStep, localContext] at hin
    rw [hin]
    unfold treeSimCollectorAfterFirst exchangeResume anyAbort
    simp only [hi, false_or]
    split_ifs
    · rfl
    · rw [advance_exchange_bind]
      rfl

/-- The exact first `stepRound`, with a general continuation and a retained
intermediate state suitable for the ceremony's round induction. -/
theorem treeSim_collector_first_factor {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state (treeSimCollectorWaiting K D count rnd v st k) = (do
      let b ← worldRoles.adversary (A.round state (colMsgs1 K D count rnd v))
      pure (b.1, treeSimCollectorAfterFirst K D count rnd v st k b.2, b.2)) := by
  rw [stepRound_real]
  change (do
    let b ← worldRoles.adversary (A.round state
      (treeSimRoundView D (treeSimCollectorWaiting K D count rnd v st k)))
    let next ← free (Concrete.sequenceFin (roundLocal D (treeSimCollectorWaiting K D count rnd v st k) b.2))
    pure (b.1, next, b.2)) = _
  rw [treeSim_collector_waiting_view]
  apply bind_congr
  intro b
  rw [sequenceFin_congr_pure _ _ (treeSim_collector_first_local K D count rnd v st k b.2)]
  simp only [free_pure, pure_bind]

/-- After the first reply, both worlds terminate at exactly the same parties.
Thus the round driver also makes the same all-abort early-return decision. -/
theorem treeSim_collector_afterFirst_done {α β : Type} (D : C.Coalition) (count : ℕ)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec β)
    (sent : C.Party → Mail C E) (i : C.Party) :
    (treeSimCollectorAfterFirst K D count rnd₁ v₁ st₁ k₁ sent i).isDone =
      (treeSimCollectorAfterFirst K D count rnd₂ v₂ st₂ k₂ sent i).isDone := by
  simp only [treeSimCollectorAfterFirst, anyAbort_colInbox]
  split_ifs <;> rfl

/-- The intermediate collector boundary exposes the second corrupt view,
including parties that aborted after the first reply. -/
theorem treeSim_collector_afterFirst_view {α : Type} (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) :
    treeSimRoundView D (treeSimCollectorAfterFirst K D count rnd v st k sent) =
      colMsgs2 K D count rnd v sent := by
  funext c i
  unfold treeSimRoundView treeSimCollectorAfterFirst colMsgs2
  split_ifs <;> simp_all [Step.outbox]

/-- Resume the ceremony after a successful gadget, or retain its abort. -/
def treeSimResume {α β : Type} (k : β → PartyM C E RealSpec α)
    (out : Option β) : OracleComp (LocalSpec C) (Step C E RealSpec α) :=
  match out with
  | none => pure (.done none)
  | some x => advance (k x).run

/-- Resume a fixed vector of recorded outputs in the driver's operator order. -/
def treeSimResumeAll {α β : Type}
    (k : C.Party → β → PartyM C E RealSpec α)
    (out : C.Party → Option β) :
    OracleComp (WorldSpec C) (C.Party → Step C E RealSpec α) :=
  free (Concrete.sequenceFin fun i => treeSimResume (k i) (out i))

/-- A successful vector resumes exactly the actual programs, without an
extra adversarial call or a reset of either cache. -/
theorem treeSim_resumeAll_start {α : Type} (D : C.Coalition)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (out : C.Party → Option (Shares C Bit × RunState C))
    (x : C.Party → Shares C Bit × RunState C)
    (corrupt : ∀ i, i ∈ D.1 → out i = none)
    (honest : ∀ i, i ∉ D.1 → out i = some (x i)) :
    treeSimResumeAll k out = startSteps worldRoles D (fun i => k i (x i)) := by
  unfold treeSimResumeAll startSteps
  rw [free_sequenceFin]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi, corrupt i hi, treeSimResume, free_pure]
  · simp [hi, honest i hi, treeSimResume, worldRoles]

/-- Fixed optional outputs need only be coupled at their actual values. The
shared relation may be chosen after the common rushing response. -/
theorem treeSim_resumeAll_rel {α β : Type} (D : C.Coalition)
    (k₁ k₂ : C.Party → β → PartyM C E RealSpec α)
    (out₁ out₂ : C.Party → Option β)
    (J : TreeSimState C → (HashCache C × HiddenCache C) → Prop)
    (Q : C.Party → Step C E RealSpec α → Step C E RealSpec α → Prop)
    (step : ∀ i a b, J a b →
      RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (treeSimResume (k₁ i) (out₁ i)))).run a)
        ((simulateQ (streamWorld prims D) (free (treeSimResume (k₂ i) (out₂ i)))).run b)
        (fun u z => Q i u.1 z.1 ∧ J u.2 z.2))
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : J a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => (∀ i, Q i (u.1 i) (z.1 i)) ∧ J u.2 z.2) := by
  unfold treeSimResumeAll
  rw [free_sequenceFin, free_sequenceFin, simulateQ_sequenceFin, simulateQ_sequenceFin]
  exact treeSim_sequenceFin_rel _ _ J Q step a b h

/-- The actual collector output, including the exact recorded state. -/
def treeSimCollectorRecorded (count : ℕ) (st : C.Party → RunState C) (i : C.Party)
    (out : Option (Shares C Bit)) : Option (Shares C Bit × RunState C) :=
  out.map fun z => (z, ⟨recordMode K .collector i (st i).history z count, (st i).label + 1, (st i).tag⟩)

/-- Resolve the second exchange into the actual ceremony continuation. That
continuation may draw randomness, query hashes, or reach the next gadget. -/
theorem treeSim_collector_second_local {α : Type} (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent sent' : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (treeSimCollectorAfterFirst K D count rnd v st k sent) sent' i =
      treeSimResume (k i) (treeSimCollectorRecorded K count st i (colOuts K D count rnd v sent sent' i)) := by
  have hin : (fun j => if j ∈ D.1 then sent' j i else
      (treeSimCollectorAfterFirst K D count rnd v st k sent j).delivered i) =
      fun j => if j ∈ D.1 then sent' j i else
        if anyAbort (colInbox K D count rnd v sent j) then some .abort else
          colOut2 K j (rnd j).1 (rnd j).2 (v j) count (colInbox K D count rnd v sent j) i := by
    funext j
    by_cases hj : j ∈ D.1
    · simp [hj]
    · simp only [if_neg hj, treeSimCollectorAfterFirst, hj, false_or]
      split_ifs <;> rfl
  by_cases hi : i ∈ D.1 ∨ anyAbort (colInbox K D count rnd v sent i) = true
  · simp only [roundLocal, treeSimCollectorAfterFirst, if_pos hi, treeSimCollectorRecorded,
      colOuts, if_pos hi, Option.map_none, treeSimResume]
  · have hc : i ∉ D.1 := fun h => hi (Or.inl h)
    simp only [roundLocal, treeSimCollectorAfterFirst, if_neg hi, if_neg hc]
    simp only [treeSimCollectorAfterFirst] at hin
    rw [hin]
    unfold treeSimCollectorRecorded colOuts
    rw [if_neg hi]
    dsimp only
    unfold exchangeResume anyAbort
    split_ifs <;> first | rfl | contradiction

/-- The exact second `stepRound` sequences the actual continuations in the
network's operator order, after the common rushing response. -/
theorem treeSim_collector_second_factor {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) :
    stepRound worldRoles D A noFunctionality state (treeSimCollectorAfterFirst K D count rnd v st k sent) = (do
      let b ← worldRoles.adversary (A.round state (colMsgs2 K D count rnd v sent))
      let next ← free (Concrete.sequenceFin fun i => treeSimResume (k i)
        (treeSimCollectorRecorded K count st i (colOuts K D count rnd v sent b.2 i)))
      pure (b.1, next, b.2)) := by
  rw [stepRound_real]
  change (do
    let b ← worldRoles.adversary (A.round state
      (treeSimRoundView D (treeSimCollectorAfterFirst K D count rnd v st k sent)))
    let next ← free (Concrete.sequenceFin (roundLocal D (treeSimCollectorAfterFirst K D count rnd v st k sent) b.2))
    pure (b.1, next, b.2)) = _
  rw [treeSim_collector_afterFirst_view]
  apply bind_congr
  intro b
  congr 1
  congr 1
  congr 1
  funext i
  exact treeSim_collector_second_local K D count rnd v st k sent b.2 i

/-- Adversarial local queries leave both hidden caches unchanged. Keeping
these equalities transports freshness of later blocks through a rushing call. -/
theorem treeSim_local_streamRel_fixed {α : Type} (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (p : OracleComp (LocalSpec C) α) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary p)).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.adversary p)).run b)
      (fun u z => u.1 = z.1 ∧ TreeSimStreamRel δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  rcases a with ⟨⟨h₁, c₁⟩, log⟩
  rcases b with ⟨h₂, c₂⟩
  rcases hs with ⟨rfl, hc⟩
  apply relTriple_post_mono (treeSim_local_coupling prims D p h₁ c₁ c₂ log)
  intro u z h
  refine ⟨h.1, ⟨h.2.1, ?_⟩, h.2.2.1, h.2.2.2⟩
  rw [h.2.2.1, h.2.2.2]
  exact hc

/-- Collector entrants may share a boundary with parties that aborted in
the preceding gadget. Their common activity mask retains those terminal steps. -/
def treeSimCollectorPartial {α : Type} (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    C.Party → Step C E RealSpec α := fun i =>
  if live i then treeSimCollectorWaiting K D count rnd v st k i else .done none

theorem treeSim_collector_partial_view {α : Type} (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    treeSimRoundView D (treeSimCollectorPartial K D live count rnd v st k) =
      fun c i => if live i then colMsgs1 K D count rnd v c i else none := by
  have hv := treeSim_collector_waiting_view K D count rnd v st k
  funext c i
  by_cases hl : live i = true
  · simpa only [treeSimRoundView, treeSimCollectorPartial, if_pos hl] using congrFun (congrFun hv c) i
  · simp [treeSimRoundView, treeSimCollectorPartial, hl, Step.outbox]

/-- A previously aborted honest operator sends an abort frame to every
remaining entrant. No collector continuation or second exchange is reached. -/
theorem treeSim_collector_partial_local {α : Type} (D : C.Coalition) (live : C.Party → Bool)
    (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (treeSimCollectorPartial K D live count rnd v st k) sent i = pure (.done none) := by
  by_cases hl : live i = true
  · by_cases hi : i ∈ D.1
    · simp only [roundLocal, treeSimCollectorPartial, if_pos hl, treeSimCollectorWaiting, if_pos hi]
    · have hab : anyAbort (fun j => if j ∈ D.1 then sent j i else
          (treeSimCollectorPartial K D live count rnd v st k j).delivered i) = true := by
        obtain ⟨j, hj, hjl⟩ := stopped
        unfold anyAbort
        rw [List.any_eq_true]
        refine ⟨j, by simp [Committee.parties], ?_⟩
        simp [hj, treeSimCollectorPartial, hjl, Step.delivered, Msg.isAbort]
      simp only [roundLocal, treeSimCollectorPartial, if_pos hl, treeSimCollectorWaiting,
        if_neg hi, treeSimCollectorStep, localContext]
      change advance (exchangeResume (G := RealSpec) _ (fun j => if j ∈ D.1 then sent j i else
        (treeSimCollectorPartial K D live count rnd v st k j).delivered i)) = _
      unfold exchangeResume
      unfold anyAbort at hab
      rw [if_pos hab]
      rfl
  · simp only [roundLocal, treeSimCollectorPartial, if_neg hl]

/-- Exact abort propagation at a partially active collector entry. This is
one actual network round, so the rushing adversary still receives its view. -/
theorem treeSim_collector_partial_factor {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (live : C.Party → Bool)
    (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state (treeSimCollectorPartial K D live count rnd v st k) = (do
      let b ← worldRoles.adversary (A.round state fun c i => if live i then colMsgs1 K D count rnd v c i else none)
      pure (b.1, (fun _ => Step.done none), b.2)) := by
  rw [stepRound_real]
  change (do
    let b ← worldRoles.adversary (A.round state
      (treeSimRoundView D (treeSimCollectorPartial K D live count rnd v st k)))
    let next ← free (Concrete.sequenceFin (roundLocal D (treeSimCollectorPartial K D live count rnd v st k) b.2))
    pure (b.1, next, b.2)) = _
  rw [treeSim_collector_partial_view]
  apply bind_congr
  intro b
  rw [sequenceFin_congr_pure _ (fun _ => Step.done none)
    (treeSim_collector_partial_local K D live stopped count rnd v st k b.2)]
  simp only [free_pure, pure_bind]

/-- Couple the real abort-propagation round for parties stopped before this
collector. The shared hidden caches remain fixed through the rushing call. -/
theorem treeSim_collector_partial_mixed {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (live : C.Party → Bool) (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true)
    (δ : HiddenAddress C → Bit) (count : ℕ)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (view : colMsgs1 K D count rnd₁ v₁ = colMsgs1 K D count rnd₂ v₂)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (stepRound worldRoles D A noFunctionality state
        (treeSimCollectorPartial K D live count rnd₁ v₁ st₁ k₁))).run a)
      ((simulateQ (streamWorld prims D) (stepRound worldRoles D A noFunctionality state
        (treeSimCollectorPartial K D live count rnd₂ v₂ st₂ k₂))).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        u.1.2.1 = (fun _ => .done none) ∧ z.1.2.1 = (fun _ => .done none) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  rw [treeSim_collector_partial_factor K D A state live stopped,
    treeSim_collector_partial_factor K D A state live stopped]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [view]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D δ _ a b hs)
  intro u z h
  simp only [simulateQ_pure, StateT.run_pure]
  apply relTriple_pure_pure
  rw [h.1]
  exact ⟨rfl, rfl, rfl, rfl, h.2⟩

/-- Couple the first collector `stepRound`, retaining the common rushing
reply and the exact intermediate continuations. -/
theorem treeSim_collector_first_mixed {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (δ : HiddenAddress C → Bit) (count : ℕ)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (view : colMsgs1 K D count rnd₁ v₁ = colMsgs1 K D count rnd₂ v₂)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (stepRound worldRoles D A noFunctionality state
        (treeSimCollectorWaiting K D count rnd₁ v₁ st₁ k₁))).run a)
      ((simulateQ (streamWorld prims D) (stepRound worldRoles D A noFunctionality state
        (treeSimCollectorWaiting K D count rnd₂ v₂ st₂ k₂))).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        u.1.2.1 = treeSimCollectorAfterFirst K D count rnd₁ v₁ st₁ k₁ u.1.2.2 ∧
        z.1.2.1 = treeSimCollectorAfterFirst K D count rnd₂ v₂ st₂ k₂ u.1.2.2 ∧
        TreeSimStreamRel δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  rw [treeSim_collector_first_factor, treeSim_collector_first_factor]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [view]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D δ _ a b hs)
  intro u z h
  simp only [simulateQ_pure, StateT.run_pure]
  apply relTriple_pure_pure
  rw [h.1]
  exact ⟨rfl, rfl, rfl, rfl, h.2⟩

/-- The only contextual obligation at a collector exit is coupling the actual
successful continuations. The cache invariant may include subsequent stages. -/
def TreeSimCollectorContinues {α : Type} (D : C.Coalition)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (R : C.Party → (Shares C Bit × RunState C) → (Shares C Bit × RunState C) → Prop)
    (J : TreeSimState C → (HashCache C × HiddenCache C) → Prop)
    (Q : C.Party → Step C E RealSpec α → Step C E RealSpec α → Prop) : Prop :=
  ∀ i x y, R i x y → ∀ a b, J a b →
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance ((k₁ i) x).run))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance ((k₂ i) y).run))).run b)
      (fun u z => Q i u.1 z.1 ∧ J u.2 z.2)

/-- Resume related optional results. Aborted parties perform no continuation. -/
theorem treeSim_resume_mixed {α : Type} (D : C.Coalition)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (R : C.Party → (Shares C Bit × RunState C) → (Shares C Bit × RunState C) → Prop)
    (J : TreeSimState C → (HashCache C × HiddenCache C) → Prop)
    (Q : C.Party → Step C E RealSpec α → Step C E RealSpec α → Prop)
    (abort : ∀ i, Q i (.done none) (.done none))
    (cont : TreeSimCollectorContinues prims D k₁ k₂ R J Q)
    (i : C.Party) (out₁ out₂ : Option (Shares C Bit × RunState C)) (hout : Option.Rel (R i) out₁ out₂)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : J a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (free (treeSimResume (k₁ i) out₁))).run a)
      ((simulateQ (streamWorld prims D) (free (treeSimResume (k₂ i) out₂))).run b)
      (fun u z => Q i u.1 z.1 ∧ J u.2 z.2) := by
  cases hout with
  | none =>
    simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨abort i, hs⟩
  | some h => exact cont i _ _ h a b hs

/-- Couple the second actual `stepRound`. All local continuations share and
update the same caches in operator order; none is treated as a pure output. -/
theorem treeSim_collector_second_mixed {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (δ : HiddenAddress C → Bit) (count : ℕ)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (v₁ v₂ : C.Party → ℕ → Bit)
    (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (R : C.Party → (Shares C Bit × RunState C) → (Shares C Bit × RunState C) → Prop)
    (hm : TreeSimCollectorTranscriptRel K D count rnd₁ rnd₂ v₁ v₂ st₁ st₂ R)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b)
    (J : TreeSimState C → (HashCache C × HiddenCache C) → Prop)
    (Q : C.Party → Step C E RealSpec α → Step C E RealSpec α → Prop)
    (entry : ∀ a' b', TreeSimStreamRel δ a' b' → a'.1.2 = a.1.2 → b'.2 = b.2 → J a' b')
    (abort : ∀ i, Q i (.done none) (.done none))
    (cont : TreeSimCollectorContinues prims D k₁ k₂ R J Q)
    (sent : C.Party → Mail C E) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (stepRound worldRoles D A noFunctionality state
        (treeSimCollectorAfterFirst K D count rnd₁ v₁ st₁ k₁ sent))).run a)
      ((simulateQ (streamWorld prims D) (stepRound worldRoles D A noFunctionality state
        (treeSimCollectorAfterFirst K D count rnd₂ v₂ st₂ k₂ sent))).run b)
      (fun u z => u.1.1 = z.1.1 ∧ u.1.2.2 = z.1.2.2 ∧
        (∀ i, Q i (u.1.2.1 i) (z.1.2.1 i)) ∧ J u.2 z.2) := by
  rw [treeSim_collector_second_factor, treeSim_collector_second_factor]
  simp only [simulateQ_bind, StateT.run_bind]
  rw [hm.2.1]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D δ _ a b hs)
  intro r₁ r₂ hr
  rw [hr.1]
  rw [free_sequenceFin, free_sequenceFin, simulateQ_sequenceFin, simulateQ_sequenceFin]
  apply relTriple_bind (treeSim_sequenceFin_rel _ _ J Q
    (fun i a' b' h => treeSim_resume_mixed prims D k₁ k₂ R J Q abort cont i _ _
      (hm.2.2 sent r₂.1.2 i) a' b' h) r₁.2 r₂.2 (entry _ _ hr.2.1 hr.2.2.1 hr.2.2.2))
  intro u z h
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure ⟨rfl, rfl, h.1, h.2⟩

/-- One collector entry retains its actual masks and suspended continuation. -/
def TreeSimCollectorEntryRel {α : Type} (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : Context C) (idx count : ℕ) (v₁ v₂ : ℕ → Bit) (st₁ st₂ : RunState C)
    (k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (s₁ s₂ : Step C E RealSpec α) : Prop :=
  ∃ rnd₁ rnd₂ : PrssOutput C Bit,
    rnd₂.1 = rnd₁.1 + (treeSimPrssShift δ ctx₁ st₁.label idx count).1 ∧
    rnd₂.2 = rnd₁.2 + (treeSimPrssShift δ ctx₁ st₁.label idx count).2 ∧
    s₁ = treeSimCollectorStep K ctx₁ rnd₁ v₁ count st₁ k₁ ∧
    s₂ = treeSimCollectorStep K ctx₂ rnd₂ v₂ count st₂ k₂

/-- Per-party collector entry inside a preceding round's continuation. It
threads the current shared cache, so no simultaneous fresh start is assumed. -/
theorem treeSim_collector_entry_mixed {α : Type} (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (idx count : ℕ) (v₁ v₂ : ℕ → Bit) (st₁ st₂ : RunState C) (lab : st₁.label = st₂.label)
    (k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance
        ((treeSimCollectorProgram K ctx₁ idx count v₁ st₁ >>= k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
        ((treeSimCollectorProgram K ctx₂ idx count v₂ st₂ >>= k₂).run)))).run b)
      (fun u z => TreeSimCollectorEntryRel K δ ctx₁ ctx₂ idx count v₁ v₂ st₁ st₂ k₁ k₂ u.1 z.1 ∧
        TreeSimStreamRel δ u.2 z.2) := by
  unfold treeSimCollectorProgram
  rw [treeSim_collector_entry, treeSim_collector_entry]
  rw [← lab, ← treeSim_prssDraw_context ctx₁ ctx₂ self keys]
  simp only [simulateQ_map, StateT.run_map]
  apply relTriple_map
  apply relTriple_post_mono (treeSim_prssBits_mixed prims D δ hδ ctx₁ st₁.label idx count a b hs)
  intro u z h
  exact ⟨⟨u.1, z.1, h.1, h.2.1, rfl, rfl⟩, h.2.2⟩

/-- The actual collector multiplication can be entered from a ceremony
continuation one party at a time, including repeated hidden-cache reads. -/
theorem treeSim_multCollector_entry_mixed {α : Type} (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (count : ℕ) (x₁ y₁ x₂ y₂ : Shares C Bit) (st₁ st₂ : RunState C) (lab : st₁.label = st₂.label)
    (k₁ k₂ : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance
        (((((realRunGadgets K ctx₁ .collector).mult x₁ y₁ count).run st₁) >>= k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
        (((((realRunGadgets K ctx₂ .collector).mult x₂ y₂ count).run st₂) >>= k₂).run)))).run b)
      (fun u z => TreeSimCollectorEntryRel K δ ctx₁ ctx₂ 0 count
          (mulRep K ctx₁ x₁ y₁) (mulRep K ctx₂ x₂ y₂) st₁ st₂ k₁ k₂ u.1 z.1 ∧
        TreeSimStreamRel δ u.2 z.2) := by
  simpa only [realRunGadgets, reshareWith, treeSimCollectorProgram] using
    treeSim_collector_entry_mixed prims K D δ hδ ctx₁ ctx₂ self keys 0 count
      (mulRep K ctx₁ x₁ y₁) (mulRep K ctx₂ x₂ y₂) st₁ st₂ lab k₁ k₂ a b hs

/-- Suspending at a collector entry preserves every other stream label,
regardless of the suspended continuation. -/
theorem treeSim_collector_entry_frame {α : Type} (D : C.Coalition) (ctx : Context C)
    (idx count : ℕ) (v : ℕ → Bit) (st : RunState C)
    (k : Shares C Bit × RunState C → PartyM C E RealSpec α)
    (s : HashCache C × HiddenCache C) (r : Step C E RealSpec α × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
      ((treeSimCollectorProgram K ctx idx count v st >>= k).run)))).run s)) :
    TreeSimCacheFrame st.label s.2 r.2.2 := by
  unfold treeSimCollectorProgram at hr
  rw [treeSim_collector_entry] at hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  exact treeSim_prssBits_frame (E := E) prims D ctx st.label idx count s u hu

/-- A selectively aborted vector resumes only its live programs. No local
entry can touch another label, even after earlier holders populate this one. -/
theorem treeSim_collector_resume_frame {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (ρ idx count : ℕ) (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k next : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (out : C.Party → Option (Shares C Bit × RunState C))
    (x : C.Party → Shares C Bit × RunState C) (live : C.Party → Bool)
    (lab : ∀ i, i ∉ D.1 → live i = true → (st i).label = ρ)
    (shape : ∀ i, out i = if i ∈ D.1 then none else if live i then some (x i) else none)
    (program : ∀ i, i ∉ D.1 → live i = true →
      k i (x i) = treeSimCollectorProgram K (ctx i) idx count (v i) (st i) >>= next i)
    (s : HashCache C × HiddenCache C) (r : (C.Party → Step C E RealSpec α) × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (treeSimResumeAll k out)).run s)) :
    TreeSimCacheFrame ρ s.2 r.2.2 := by
  unfold treeSimResumeAll at hr
  rw [free_sequenceFin, simulateQ_sequenceFin] at hr
  intro y hy
  apply treeSim_state_sequenceFin_preserves (fun t : HashCache C × HiddenCache C => t.2 y) _ _ s r hr
  intro i a b hb
  rw [shape i] at hb
  by_cases hi : i ∈ D.1
  · simp [hi, treeSimResume, free_pure] at hb
    subst b
    rfl
  · simp only [if_neg hi] at hb
    by_cases hl : live i = true
    · simp only [if_pos hl, treeSimResume, program i hi hl] at hb
      have h := treeSim_collector_entry_frame prims K D (ctx i) idx count (v i) (st i) (next i) a b hb
      rw [lab i hi hl] at h
      exact h y hy
    · simp [hl, treeSimResume, free_pure] at hb
      subst b
      rfl

/-- The logged resumption has exactly the same private-cache footprint. -/
theorem treeSim_collector_resume_logged_frame {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (ρ idx count : ℕ) (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k next : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (out : C.Party → Option (Shares C Bit × RunState C))
    (x : C.Party → Shares C Bit × RunState C) (live : C.Party → Bool)
    (lab : ∀ i, i ∉ D.1 → live i = true → (st i).label = ρ)
    (shape : ∀ i, out i = if i ∈ D.1 then none else if live i then some (x i) else none)
    (program : ∀ i, i ∉ D.1 → live i = true →
      k i (x i) = treeSimCollectorProgram K (ctx i) idx count (v i) (st i) >>= next i)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k out)).run s)) :
    TreeSimCacheFrame ρ s.1.2 r.2.1.2 := by
  apply treeSim_collector_resume_frame prims K D ctx ρ idx count v st k next out x live lab shape program
    s.1 (r.1, r.2.1)
  rw [← treeSimLoggedWorld_erase prims D _ s.1 s.2, support_map]
  exact ⟨r, hr, rfl⟩

/-- The actual PRSS entry with arbitrary ceremony continuations factors
through the real shared-cache draws and the first communication boundary. -/
theorem treeSim_collector_start_factor {α : Type} (D : C.Coalition)
    (ctx : C.Party → Context C) (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (idx count : ℕ) (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    startSteps worldRoles D
      (fun i => treeSimCollectorProgram K (ctx i) idx count (v i) (st i) >>= k i) = (do
      let rnd ← treeSimCollectorDraws (E := E) D ctx idx count st
      pure (treeSimCollectorWaiting K D count rnd v st k)) := by
  unfold startSteps treeSimCollectorDraws treeSimCollectorWaiting
  rw [← sequenceFin_bind_pure _ (fun i (rnd : PrssOutput C Bit) =>
    if i ∈ D.1 then Step.done none else treeSimCollectorStep K (localContext i) rnd (v i) count (st i) (k i))]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi]
  · simp only [if_neg hi]
    simpa only [treeSimCollectorProgram, map_eq_bind_pure_comp, Function.comp_def,
      treeSimCollectorStep, self i hi, localContext] using
      treeSim_collector_entry K (ctx i) idx count (v i) (st i) (k i)

/-- Coupled actual PRSS entries export their mask witnesses at the first
round boundary, without running or restricting their continuations. -/
theorem treeSim_collector_start_mixed {α : Type} (D : C.Coalition)
    (δ : HiddenAddress C → Bit) (hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0)
    (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab : ∀ i, i ∉ D.1 → (st₁ i).label = (st₂ i).label)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D
        (fun i => treeSimCollectorProgram K (ctx₁ i) idx count (v₁ i) (st₁ i) >>= k₁ i))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D
        (fun i => treeSimCollectorProgram K (ctx₂ i) idx count (v₂ i) (st₂ i) >>= k₂ i))).run b)
      (fun u z => (∃ rnd₁ rnd₂, TreeSimCollectorMasksRel D δ ctx₁ idx count st₁ rnd₁ rnd₂ ∧
        u.1 = treeSimCollectorWaiting K D count rnd₁ v₁ st₁ k₁ ∧
        z.1 = treeSimCollectorWaiting K D count rnd₂ v₂ st₂ k₂) ∧ TreeSimStreamRel δ u.2 z.2) := by
  rw [treeSim_collector_start_factor K D ctx₁ self₁, treeSim_collector_start_factor K D ctx₂ self₂]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_collector_draws_mixed prims D δ hδ ctx₁ ctx₂
    (fun i hi => (self₁ i hi).trans (self₂ i hi).symm) keys idx count st₁ st₂ lab a b hs)
  intro u z h
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure ⟨⟨u.1, z.1, h.1, rfl, rfl⟩, h.2⟩

/-- Enter the per-round collector invariant from the actual PRSS gadget.
The exported masks have precisely the adapted GS20 translation, while the
cache retains all earlier translations and the continuations stay suspended. -/
theorem treeSim_collector_start_next {α : Type} (D : C.Coalition)
    (T₀ : C.Term) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂) x = 0) :
    let δ := past + treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂)
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D
        (fun i => treeSimCollectorProgram K (ctx₁ i) idx count (v₁ i) (st₁ i) >>= k₁ i))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D
        (fun i => treeSimCollectorProgram K (ctx₂ i) idx count (v₂ i) (st₂ i) >>= k₂ i))).run b)
      (fun u z => (∃ rnd₁ rnd₂,
        (∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0
          (ΔC K D T₀ (v₁ - v₂) 0) (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i) ∧
        u.1 = treeSimCollectorWaiting K D count rnd₁ v₁ st₁ k₁ ∧
        z.1 = treeSimCollectorWaiting K D count rnd₂ v₂ st₂ k₂) ∧ TreeSimStreamRel δ u.2 z.2) := by
  intro δ
  have hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0 := by
    intro x hx
    simp only [δ, Pi.add_apply, visible x hx, treeSimCollectorShift,
      treeSim_blockShift_visible D ρ idx count _ _ x hx, add_zero]
  apply relTriple_post_mono (treeSim_collector_start_mixed prims K D δ hδ ctx₁ ctx₂ self₁ self₂ keys
    idx count v₁ v₂ st₁ st₂ (fun i hi => (lab₁ i hi).trans (lab₂ i hi).symm) k₁ k₂ a b
    ⟨hs.1, treeSim_hiddenRel_extend past _ hs.2 fresh⟩)
  intro u z h
  obtain ⟨rnd₁, rnd₂, hm, hu, hz⟩ := h.1
  refine ⟨⟨rnd₁, rnd₂, ?_, hu, hz⟩, h.2⟩
  intro i hi
  have hshift : treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count =
      frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
        (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i := by
    rw [lab₁ i hi]
    dsimp only [δ]
    rw [treeSim_prssShift_add, treeSim_prssShift_zero past (ctx₁ i) ρ idx count block, zero_add]
    unfold treeSimCollectorShift
    rw [treeSim_prssShift_block D (ctx₁ i) (by simpa [self₁ i hi] using hi), self₁ i hi]
  have hm' := hm i hi
  rw [hshift] at hm'
  exact Prod.ext hm'.1 hm'.2

/-- Collector exits export the absolute next labels as well as the sharing
and history translation, so continuations can identify their next PRSS block. -/
def TreeSimCollectorExitRel (D : C.Coalition) (T₀ : C.Term) (count : ℕ)
    (history : List Bit) (difference : ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (i : C.Party) (x y : Shares C Bit × RunState C) : Prop :=
  TreeSimCollectorResultRel K D T₀ count history difference i x y ∧
    x.2.label = (st₁ i).label + 1 ∧ y.2.label = (st₂ i).label + 1

/-- The actual record operation supplies the absolute labels at successful
collector exits; aborts are unchanged. -/
theorem treeSim_collector_transcript_exit (D : C.Coalition) (count : ℕ) (T₀ : C.Term)
    (hT₀ : lackedTerm D.1 = some T₀)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (v₁ v₂ : C.Party → ℕ → Bit)
    (masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0
      (ΔC K D T₀ (v₁ - v₂) 0) (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i)
    (history : List Bit) (st₁ st₂ : C.Party → RunState C)
    (hstate : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i)) :
    TreeSimCollectorTranscriptRel K D count rnd₁ rnd₂ v₁ v₂ st₁ st₂
      (TreeSimCollectorExitRel K D T₀ count history
        (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g) st₁ st₂) := by
  have hm := treeSim_collector_transcript_pivot K D count T₀ hT₀ rnd₁ rnd₂ v₁ v₂ masks history st₁ st₂ hstate
  refine ⟨hm.1, hm.2.1, ?_⟩
  intro sent sent' i
  have ho := hm.2.2 sent sent' i
  generalize colOuts K D count rnd₁ v₁ sent sent' i = left at ho ⊢
  generalize colOuts K D count rnd₂ v₂ sent sent' i = right at ho ⊢
  cases left <;> cases right <;> simp only [Option.map_none, Option.map_some] at ho ⊢ <;> cases ho
  · exact Option.Rel.none
  · exact Option.Rel.some ⟨by assumption, rfl, rfl⟩

/-- Concrete data at either collector communication boundary. The masks and
history obey the proved translation; continuations return ceremony outputs. -/
structure TreeSimCollectorData (D : C.Coalition) where
  count : ℕ
  T₀ : C.Term
  lacked : lackedTerm D.1 = some T₀
  δ : HiddenAddress C → Bit
  rnd₁ : C.Party → PrssOutput C Bit
  rnd₂ : C.Party → PrssOutput C Bit
  v₁ : C.Party → ℕ → Bit
  v₂ : C.Party → ℕ → Bit
  st₁ : C.Party → RunState C
  st₂ : C.Party → RunState C
  k₁ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput
  k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput
  history : List Bit
  masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0
    (ΔC K D T₀ (v₁ - v₂) 0) (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i
  states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i)

/-- Collector boundaries: initial exchange, forwarding, or a partially active entry. -/
def TreeSimCollectorBoundary (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (d : TreeSimCollectorData K D)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  a.1.1 = b.1.1 ∧ TreeSimStreamRel d.δ a.2 b.2 ∧
  ((a.1.2 = treeSimCollectorWaiting K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
    b.1.2 = treeSimCollectorWaiting K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂) ∨
    (∃ sent, a.1.2 = treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent ∧
      b.1.2 = treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent) ∨
    ∃ live, (∃ j, j ∉ D.1 ∧ live j ≠ true) ∧
      a.1.2 = treeSimCollectorPartial K D live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
      b.1.2 = treeSimCollectorPartial K D live d.count d.rnd₂ d.v₂ d.st₂ d.k₂)

/-- Actual PRSS entry constructs the collector boundary data, including the
GS20 mask equations. No boundary or mask certificate is assumed. -/
theorem treeSim_collector_start_boundary (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (T₀ : C.Term) (lacked : lackedTerm D.1 = some T₀) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (history : List Bit) (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂) x = 0) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D
        (fun i => treeSimCollectorProgram K (ctx₁ i) idx count (v₁ i) (st₁ i) >>= k₁ i))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D
        (fun i => treeSimCollectorProgram K (ctx₂ i) idx count (v₂ i) (st₂ i) >>= k₂ i))).run b)
      (fun u z => ∃ rnd₁ rnd₂, ∃ masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i +
        frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
          (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i,
        TreeSimCollectorBoundary K D A
          ⟨count, T₀, lacked, past + treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂),
            rnd₁, rnd₂, v₁, v₂, st₁, st₂, k₁, k₂, history, masks, states⟩
          ((state, u.1), u.2) ((state, z.1), z.2)) := by
  apply relTriple_post_mono (treeSim_collector_start_next prims K D T₀ ctx₁ ctx₂ self₁ self₂ keys
    ρ idx count v₁ v₂ st₁ st₂ lab₁ lab₂ k₁ k₂ past visible block a b hs fresh)
  intro u z h
  obtain ⟨⟨rnd₁, rnd₂, masks, hu, hz⟩, hc⟩ := h
  exact ⟨rnd₁, rnd₂, masks, rfl, hc, Or.inl ⟨hu, hz⟩⟩

/-- Resume an actual vector into the next collector, including selective
aborts. The next mask translation is chosen once for the entire vector before
any party draws; inactive parties perform no oracle query. -/
theorem treeSim_collector_resume_boundary (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (T₀ : C.Term) (lacked : lackedTerm D.1 = some T₀) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (ρ idx count : ℕ) (v₁ v₂ : C.Party → ℕ → Bit) (st₁ st₂ : C.Party → RunState C)
    (lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ)
    (lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ)
    (next₁ next₂ k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C))
    (x₁ x₂ : C.Party → Shares C Bit × RunState C) (live : C.Party → Bool)
    (shape₁ : ∀ i, out₁ i = if i ∈ D.1 then none else if live i then some (x₁ i) else none)
    (shape₂ : ∀ i, out₂ i = if i ∈ D.1 then none else if live i then some (x₂ i) else none)
    (program₁ : ∀ i, i ∉ D.1 → live i = true →
      k₁ i (x₁ i) = treeSimCollectorProgram K (ctx₁ i) idx count (v₁ i) (st₁ i) >>= next₁ i)
    (program₂ : ∀ i, i ∉ D.1 → live i = true →
      k₂ i (x₂ i) = treeSimCollectorProgram K (ctx₂ i) idx count (v₂ i) (st₂ i) >>= next₂ i)
    (history : List Bit) (states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i))
    (past : HiddenAddress C → Bit) (visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0)
    (block : ∀ name key g, g < count → past ((name, key), ρ, idx, g) = 0)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b)
    (fresh : ∀ x, (a.1.2 x).isSome → treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂) x = 0) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => ∃ rnd₁ rnd₂, ∃ masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i +
        frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
          (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0)) i,
        u.1 = treeSimCollectorPartial K D live count rnd₁ v₁ st₁ next₁ ∧
        z.1 = treeSimCollectorPartial K D live count rnd₂ v₂ st₂ next₂ ∧
        TreeSimCollectorBoundary K D A
          ⟨count, T₀, lacked, past + treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂),
            rnd₁, rnd₂, v₁, v₂, st₁, st₂, next₁, next₂, history, masks, states⟩
          ((state, u.1), u.2) ((state, z.1), z.2)) := by
  let δ := past + treeSimCollectorShift K D T₀ ρ idx count (v₁ - v₂)
  let dt := frandShare D count 0 0 (ΔC K D T₀ (v₁ - v₂) 0)
    (pairShift (K.owner T₀) (δC K D T₀ (K.owner T₀) (v₁ - v₂) 0))
  have hδ : ∀ x, ¬ Hidden D x.1.1 → δ x = 0 := by
    intro x hx
    simp only [δ, Pi.add_apply, visible x hx, treeSimCollectorShift,
      treeSim_blockShift_visible D ρ idx count _ _ x hx, add_zero]
  have hshift : ∀ i, i ∉ D.1 → treeSimPrssShift δ (ctx₁ i) (st₁ i).label idx count = dt i := by
    intro i hi
    rw [lab₁ i hi]
    dsimp only [δ]
    rw [treeSim_prssShift_add, treeSim_prssShift_zero past (ctx₁ i) ρ idx count block, zero_add]
    unfold treeSimCollectorShift
    rw [treeSim_prssShift_block D (ctx₁ i) (by simpa [self₁ i hi] using hi), self₁ i hi]
  let Q := fun i (s₁ s₂ : Step C E RealSpec TreeOutput) => ∃ r₁ r₂ : PrssOutput C Bit,
    (i ∉ D.1 → r₂ = r₁ + dt i) ∧
    s₁ = treeSimCollectorPartial K D live count (fun _ => r₁) v₁ st₁ next₁ i ∧
    s₂ = treeSimCollectorPartial K D live count (fun _ => r₂) v₂ st₂ next₂ i
  have step : ∀ i a' b', TreeSimStreamRel δ a' b' →
      RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (treeSimResume (k₁ i) (out₁ i)))).run a')
        ((simulateQ (streamWorld prims D) (free (treeSimResume (k₂ i) (out₂ i)))).run b')
        (fun u z => Q i u.1 z.1 ∧ TreeSimStreamRel δ u.2 z.2) := by
    intro i a' b' hc
    rw [shape₁ i, shape₂ i]
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      apply relTriple_pure_pure
      refine ⟨⟨0, 0, fun h => (h hi).elim, ?_, ?_⟩, hc⟩ <;>
        simp [treeSimCollectorPartial, treeSimCollectorWaiting, hi]
    · simp only [if_neg hi]
      by_cases hl : live i = true
      · simp only [if_pos hl, treeSimResume, program₁ i hi hl, program₂ i hi hl]
        apply relTriple_post_mono (treeSim_collector_entry_mixed prims K D δ hδ (ctx₁ i) (ctx₂ i)
          ((self₁ i hi).trans (self₂ i hi).symm) (keys i hi) idx count (v₁ i) (v₂ i)
          (st₁ i) (st₂ i) ((lab₁ i hi).trans (lab₂ i hi).symm) (next₁ i) (next₂ i) a' b' hc)
        intro u z h
        obtain ⟨⟨r₁, r₂, ht, hp, hu, hz⟩, hc'⟩ := h
        rw [hshift i hi] at ht hp
        refine ⟨⟨r₁, r₂, fun _ => Prod.ext ht hp, ?_, ?_⟩, hc'⟩
        · simpa only [treeSimCollectorPartial, hl, if_true, treeSimCollectorWaiting, if_neg hi,
            treeSimCollectorStep, self₁ i hi, localContext] using hu
        · simpa only [treeSimCollectorPartial, hl, if_true, treeSimCollectorWaiting, if_neg hi,
            treeSimCollectorStep, self₂ i hi, localContext] using hz
      · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
        apply relTriple_pure_pure
        exact ⟨⟨0, 0 + dt i, fun _ => rfl, by simp [treeSimCollectorPartial, hl],
          by simp [treeSimCollectorPartial, hl]⟩, hc⟩
  apply relTriple_post_mono (treeSim_resumeAll_rel prims D k₁ k₂ out₁ out₂ (TreeSimStreamRel δ) Q
    step a b ⟨hs.1, treeSim_hiddenRel_extend past _ hs.2 fresh⟩)
  intro u z h
  choose rnd₁ rnd₂ masks hu hz using h.1
  have hu' : u.1 = treeSimCollectorPartial K D live count rnd₁ v₁ st₁ next₁ := funext hu
  have hz' : z.1 = treeSimCollectorPartial K D live count rnd₂ v₂ st₂ next₂ := funext hz
  refine ⟨rnd₁, rnd₂, masks, hu', hz', rfl, h.2, ?_⟩
  by_cases stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true
  · exact Or.inr (Or.inr ⟨live, stopped, hu', hz'⟩)
  · left
    have allLive : ∀ i, i ∉ D.1 → live i = true := by
      intro i hi
      by_contra hl
      exact stopped ⟨i, hi, hl⟩
    constructor
    · rw [hu']
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimCollectorPartial, treeSimCollectorWaiting, hi]
      · simp [treeSimCollectorPartial, allLive i hi]
    · rw [hz']
      funext i
      by_cases hi : i ∈ D.1
      · simp [treeSimCollectorPartial, treeSimCollectorWaiting, hi]
      · simp [treeSimCollectorPartial, allLive i hi]

/-- A coupling may retain the actual marginal supports. This lets a caller
use unary execution facts rather than quantify over arbitrary final caches. -/
theorem treeSim_relTriple_support {α β : Type} {oa : ProbComp α} {ob : ProbComp β}
    {R : α → β → Prop} (h : RelTriple oa ob R) :
    RelTriple oa ob (fun x y => R x y ∧ x ∈ support oa ∧ y ∈ support ob) := by
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  refine relTriple_iff_relWP.2 ⟨c, fun z hz => ⟨hc z hz, ?_, ?_⟩⟩
  · have hp : z.1 ∈ support (Prod.fst <$> c.1) := by
      rw [support_map]
      exact ⟨z, hz, rfl⟩
    rw [c.2.map_fst] at hp
    exact (mem_support_evalDist_iff _ _).1 hp
  · have hp : z.2 ∈ support (Prod.snd <$> c.1) := by
      rw [support_map]
      exact ⟨z, hz, rfl⟩
    rw [c.2.map_snd] at hp
    exact (mem_support_evalDist_iff _ _).1 hp

/-- Concrete next-collector parameters for fixed optional outputs. These
are program equations, state relations and freshness facts, not a coupling. -/
structure TreeSimCollectorNext (D : C.Coalition) (past : HiddenAddress C → Bit)
    (initial : HiddenCache C)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C)) where
  T₀ : C.Term
  lacked : lackedTerm D.1 = some T₀
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss
  ρ : ℕ
  idx : ℕ
  count : ℕ
  v₁ : C.Party → ℕ → Bit
  v₂ : C.Party → ℕ → Bit
  st₁ : C.Party → RunState C
  st₂ : C.Party → RunState C
  lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ
  lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ
  next₁ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput
  next₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput
  x₁ : C.Party → Shares C Bit × RunState C
  x₂ : C.Party → Shares C Bit × RunState C
  live : C.Party → Bool
  shape₁ : ∀ i, out₁ i = if i ∈ D.1 then none else if live i then some (x₁ i) else none
  shape₂ : ∀ i, out₂ i = if i ∈ D.1 then none else if live i then some (x₂ i) else none
  program₁ : ∀ i, i ∉ D.1 → live i = true →
    k₁ i (x₁ i) = treeSimCollectorProgram K (ctx₁ i) idx count (v₁ i) (st₁ i) >>= next₁ i
  program₂ : ∀ i, i ∉ D.1 → live i = true →
    k₂ i (x₂ i) = treeSimCollectorProgram K (ctx₂ i) idx count (v₂ i) (st₂ i) >>= next₂ i
  history : List Bit
  states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i)
  visible : ∀ x, ¬ Hidden D x.1.1 → past x = 0
  futureZero : TreeSimFutureZero ρ past
  futureEmpty : TreeSimFutureEmpty ρ initial

/-- The current block is zero because all earlier translations use smaller labels. -/
theorem TreeSimCollectorNext.block {D : C.Coalition} {past : HiddenAddress C → Bit}
    {initial : HiddenCache C} {k₁ k₂} {out₁ out₂}
    (n : TreeSimCollectorNext K D past initial k₁ k₂ out₁ out₂) :
    ∀ name key g, g < n.count → past ((name, key), n.ρ, n.idx, g) = 0 := by
  intro name key g _
  exact n.futureZero _ (by rfl)

/-- Freshness of the adapted GS20 shift follows from the retained future-label invariant. -/
theorem TreeSimCollectorNext.fresh {D : C.Coalition} {past : HiddenAddress C → Bit}
    {initial : HiddenCache C} {k₁ k₂} {out₁ out₂}
    (n : TreeSimCollectorNext K D past initial k₁ k₂ out₁ out₂) :
    ∀ x, (initial x).isSome → treeSimCollectorShift K D n.T₀ n.ρ n.idx n.count (n.v₁ - n.v₂) x = 0 := by
  exact treeSim_futureEmpty_block D n.ρ n.idx n.count _ _ initial n.futureEmpty

/-- The exact mask equation exported by this next collector. -/
def TreeSimCollectorNext.Masks {D : C.Coalition} {past : HiddenAddress C → Bit}
    {initial : HiddenCache C} {k₁ k₂} {out₁ out₂}
    (n : TreeSimCollectorNext K D past initial k₁ k₂ out₁ out₂)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) : Prop :=
  ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D n.count 0 0 (ΔC K D n.T₀ (n.v₁ - n.v₂) 0)
    (pairShift (K.owner n.T₀) (δC K D n.T₀ (K.owner n.T₀) (n.v₁ - n.v₂) 0)) i

/-- Rebuild boundary data without forgetting its exact input vector or history. -/
def TreeSimCollectorNext.data {D : C.Coalition} {past : HiddenAddress C → Bit}
    {initial : HiddenCache C} {k₁ k₂} {out₁ out₂}
    (n : TreeSimCollectorNext K D past initial k₁ k₂ out₁ out₂)
    (rnd₁ rnd₂ : C.Party → PrssOutput C Bit) (masks : n.Masks K rnd₁ rnd₂) : TreeSimCollectorData K D :=
  ⟨n.count, n.T₀, n.lacked, past + treeSimCollectorShift K D n.T₀ n.ρ n.idx n.count (n.v₁ - n.v₂),
    rnd₁, rnd₂, n.v₁, n.v₂, n.st₁, n.st₂, n.next₁, n.next₂, n.history, masks, n.states⟩

/-- Discharge the next-collector continuation from its concrete program and
freshness certificate. The only cache equality needed is the retained entry one. -/
theorem TreeSimCollectorNext.coupling (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State)
    (past : HiddenAddress C → Bit) (initial : HiddenCache C) (k₁ k₂) (out₁ out₂)
    (n : TreeSimCollectorNext K D past initial k₁ k₂ out₁ out₂)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hs : TreeSimStreamRel past a b)
    (ha : a.1.2 = initial) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => TreeSimCacheFrame n.ρ a.1.2 u.2.1.2 ∧ TreeSimCacheFrame n.ρ b.2 z.2.2 ∧
        TreeSimFutureEmpty (n.ρ + 1) u.2.1.2 ∧ TreeSimFutureEmpty (n.ρ + 1) z.2.2 ∧
        TreeSimFutureZero (n.ρ + 1)
          (past + treeSimCollectorShift K D n.T₀ n.ρ n.idx n.count (n.v₁ - n.v₂)) ∧
        ∃ rnd₁ rnd₂, ∃ masks : n.Masks K rnd₁ rnd₂,
        u.1 = treeSimCollectorPartial K D n.live n.count rnd₁ n.v₁ n.st₁ n.next₁ ∧
        z.1 = treeSimCollectorPartial K D n.live n.count rnd₂ n.v₂ n.st₂ n.next₂ ∧
        TreeSimCollectorBoundary K D A (n.data K rnd₁ rnd₂ masks)
          ((state, u.1), u.2) ((state, z.1), z.2)) := by
  apply relTriple_post_mono (treeSim_relTriple_support (treeSim_collector_resume_boundary prims K D A state n.T₀ n.lacked n.ctx₁ n.ctx₂
    n.self₁ n.self₂ n.keys n.ρ n.idx n.count n.v₁ n.v₂ n.st₁ n.st₂ n.lab₁ n.lab₂
    n.next₁ n.next₂ k₁ k₂ out₁ out₂ n.x₁ n.x₂ n.live n.shape₁ n.shape₂ n.program₁ n.program₂
    n.history n.states past n.visible (n.block K) a b hs (by simpa only [ha] using n.fresh K)))
  intro u z h
  have f₁ := treeSim_collector_resume_logged_frame prims K D n.ctx₁ n.ρ n.idx n.count n.v₁ n.st₁
    k₁ n.next₁ out₁ n.x₁ n.live (fun i hi _ => n.lab₁ i hi) n.shape₁ n.program₁ a u h.2.1
  have f₂ := treeSim_collector_resume_frame prims K D n.ctx₂ n.ρ n.idx n.count n.v₂ n.st₂
    k₂ n.next₂ out₂ n.x₂ n.live (fun i hi _ => n.lab₂ i hi) n.shape₂ n.program₂ b z h.2.2
  have he : TreeSimFutureEmpty n.ρ a.1.2 := by simpa only [ha] using n.futureEmpty
  refine ⟨f₁, f₂, treeSim_futureEmpty_after he f₁,
    treeSim_futureEmpty_after (treeSim_futureEmpty_related he hs.2) f₂, ?_, h.1⟩
  exact treeSim_futureZero_extend D n.ρ n.idx n.count _ _ past n.futureZero

/-- The concrete collector boundary preserves the driver's termination test,
including its partially aborted intermediate configurations. -/
theorem treeSim_collector_boundary_done (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (d : TreeSimCollectorData K D)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C))
    (h : TreeSimCollectorBoundary K D A d a b) : AllDone D a.1.2 ↔ AllDone D b.1.2 := by
  rcases h.2.2 with h | ⟨sent, h⟩ | ⟨live, _, h⟩
  · rw [h.1, h.2]
    have hn : ∀ rnd v st k, ¬ AllDone D (treeSimCollectorWaiting (α := TreeOutput) K D d.count rnd v st k) := by
      intro rnd v st k hall
      obtain ⟨i, hi⟩ := exists_honest D
      have hh := hall i hi
      simp [treeSimCollectorWaiting, treeSimCollectorStep, hi] at hh
    exact iff_of_false (hn _ _ _ _) (hn _ _ _ _)
  · rw [h.1, h.2]
    unfold AllDone
    simp only [treeSim_collector_afterFirst_done K D d.count d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ sent]

  · rw [h.1, h.2]
    unfold AllDone
    apply forall_congr'
    intro i
    apply forall_congr'
    intro hi
    by_cases hl : live i = true <;>
      simp [treeSimCollectorPartial, treeSimCollectorWaiting, treeSimCollectorStep, hl, hi]

/-- Collector-specific closure facts for a proposed ceremony invariant.
There is no exchange or algebra premise: those are proved below. -/
structure TreeSimCollectorLocalClosure (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (d : TreeSimCollectorData K D) (initial₁ initial₂ : HiddenCache C) where
  J : TreeSimState C → (HashCache C × HiddenCache C) → Prop
  Q : C.Party → Step C E RealSpec TreeOutput → Step C E RealSpec TreeOutput → Prop
  entry : ∀ a b, TreeSimStreamRel d.δ a b → a.1.2 = initial₁ → b.2 = initial₂ → J a b
  abort : ∀ i, Q i (.done none) (.done none)
  continues : TreeSimCollectorContinues prims D d.k₁ d.k₂
    (TreeSimCollectorExitRel K D d.T₀ d.count d.history
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g) d.st₁ d.st₂) J Q
  first : ∀ state sent a b, TreeSimStreamRel d.δ a b → a.1.2 = initial₁ → b.2 = initial₂ →
    Bad a ∨ Inv ((state, treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent), a)
      ((state, treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent), b)
  exit : ∀ state s₁ s₂ a b, (∀ i, Q i (s₁ i) (s₂ i)) → J a b →
    Bad a ∨ Inv ((state, s₁), a) ((state, s₂), b)

/-- Contextual collector closure at the exact outputs of a common reply.
The continuation proof may choose its next global translation after seeing
that reply, before the driver resumes any honest party. -/
structure TreeSimCollectorClosure (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (d : TreeSimCollectorData K D) (initial₁ initial₂ : HiddenCache C) where
  first : ∀ state sent a b, TreeSimStreamRel d.δ a b → a.1.2 = initial₁ → b.2 = initial₂ →
    Bad a ∨ Inv ((state, treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent), a)
      ((state, treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent), b)
  abort : ∀ state a b, TreeSimStreamRel d.δ a b → a.1.2 = initial₁ → b.2 = initial₂ →
    Bad a ∨ Inv ((state, fun _ => .done none), a) ((state, fun _ => .done none), b)
  resume : ∀ state sent sent' a b, TreeSimStreamRel d.δ a b → a.1.2 = initial₁ → b.2 = initial₂ →
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll d.k₁
        (fun i => treeSimCollectorRecorded K d.count d.st₁ i (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i)))).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll d.k₂
        (fun i => treeSimCollectorRecorded K d.count d.st₂ i (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i)))).run b)
      (fun u z => Bad u.2 ∨ Inv ((state, u.1), u.2) ((state, z.1), z.2))

/-- The previous scalar continuation rule remains sufficient. The new vector
rule additionally permits a reply-dependent translation shared by all parties. -/
theorem TreeSimCollectorLocalClosure.toClosure (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (d : TreeSimCollectorData K D) (initial₁ initial₂ : HiddenCache C)
    (h : TreeSimCollectorLocalClosure prims K D A Bad Inv d initial₁ initial₂) :
    TreeSimCollectorClosure prims K D A Bad Inv d initial₁ initial₂ := by
  refine ⟨h.first, ?_, ?_⟩
  · intro state a b hc hl hr
    exact h.exit state _ _ a b h.abort (h.entry a b hc hl hr)
  · intro state sent sent' a b hc hl hr
    have hm := treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
      d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states
    apply relTriple_post_mono (treeSim_resumeAll_rel prims D d.k₁ d.k₂ _ _ h.J h.Q
      (fun i a' b' hab => treeSim_resume_mixed prims D d.k₁ d.k₂ _ h.J h.Q h.abort h.continues
        i _ _ (hm.2.2 sent sent' i) a' b' hab) a b (h.entry a b hc hl hr))
    intro u z hz
    exact h.exit state u.1 z.1 u.2 z.2 hz.1 hz.2

/-- Concrete collector-to-collector closure. Each common reply may select a
new next-block certificate; there is no assumed probabilistic continuation. -/
structure TreeSimCollectorNextClosure (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (d : TreeSimCollectorData K D) (initial₁ initial₂ : HiddenCache C) where
  first : ∀ state sent a b, TreeSimStreamRel d.δ a b → a.1.2 = initial₁ → b.2 = initial₂ →
      Bad a ∨ Inv ((state, treeSimCollectorAfterFirst K D d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent), a)
        ((state, treeSimCollectorAfterFirst K D d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent), b)
  abort : ∀ state a b, TreeSimStreamRel d.δ a b → a.1.2 = initial₁ → b.2 = initial₂ →
      Bad a ∨ Inv ((state, fun _ => .done none), a) ((state, fun _ => .done none), b)
  next : ∀ state sent sent' a b, TreeSimStreamRel d.δ a b → a.1.2 = initial₁ → b.2 = initial₂ →
      let out₁ := fun i => treeSimCollectorRecorded K d.count d.st₁ i (colOuts K D d.count d.rnd₁ d.v₁ sent sent' i)
      let out₂ := fun i => treeSimCollectorRecorded K d.count d.st₂ i (colOuts K D d.count d.rnd₂ d.v₂ sent sent' i)
      ∃ n : TreeSimCollectorNext K D d.δ initial₁ d.k₁ d.k₂ out₁ out₂,
      ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll d.k₁ out₁)).run a),
      ∀ z ∈ support ((simulateQ (streamWorld prims D) (treeSimResumeAll d.k₂ out₂)).run b),
      ∀ rnd₁ rnd₂ (masks : n.Masks K rnd₁ rnd₂),
        TreeSimCacheFrame n.ρ a.1.2 u.2.1.2 → TreeSimCacheFrame n.ρ b.2 z.2.2 →
        TreeSimFutureEmpty (n.ρ + 1) u.2.1.2 → TreeSimFutureEmpty (n.ρ + 1) z.2.2 →
        TreeSimFutureZero (n.ρ + 1) (n.data K rnd₁ rnd₂ masks).δ →
        u.1 = treeSimCollectorPartial K D n.live n.count rnd₁ n.v₁ n.st₁ n.next₁ →
        z.1 = treeSimCollectorPartial K D n.live n.count rnd₂ n.v₂ n.st₂ n.next₂ →
        TreeSimCollectorBoundary K D A (n.data K rnd₁ rnd₂ masks) ((state, u.1), u.2) ((state, z.1), z.2) →
        Bad u.2 ∨ Inv ((state, u.1), u.2) ((state, z.1), z.2)

/-- The concrete next-collector certificate discharges vector resumption. -/
theorem TreeSimCollectorClosure.ofNext (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (d : TreeSimCollectorData K D) (initial₁ initial₂ : HiddenCache C)
    (concrete : TreeSimCollectorNextClosure prims K D A Bad Inv d initial₁ initial₂) :
    TreeSimCollectorClosure prims K D A Bad Inv d initial₁ initial₂ := by
  refine ⟨concrete.first, concrete.abort, ?_⟩
  intro state sent sent' a b hc hl hr
  obtain ⟨n, accepts⟩ := concrete.next state sent sent' a b hc hl hr
  apply relTriple_post_mono (treeSim_relTriple_support
    (n.coupling prims K D A state d.δ initial₁ d.k₁ d.k₂ _ _ a b hc hl))
  intro u z h
  obtain ⟨⟨f₁, f₂, e₁, e₂, zero, rnd₁, rnd₂, masks, hu, hz, hb⟩, hsu, hsz⟩ := h
  exact accepts u hsu z hsz rnd₁ rnd₂ masks f₁ f₂ e₁ e₂ zero hu hz hb

/-- Discharge the collector case of the ceremony's actual one-round induction.
The remaining premises identify reachable collector boundaries and relate
successful ceremony continuations; both network rounds are proved here. -/
theorem treeSim_collector_preserves (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (stage : TreeSimConfig A (TreeSimState C) → TreeSimStage) {gadget : TreeSimStage}
    (identify : ∀ a b, stage a = gadget → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
      ∃ d : TreeSimCollectorData K D, TreeSimCollectorBoundary K D A d a b ∧
        Nonempty (TreeSimCollectorClosure prims K D A Bad Inv d a.2.1.2 b.2.2)) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A Bad Inv stage gadget := by
  intro a b hg hinv hbad hdone
  obtain ⟨d, hd, ⟨close⟩⟩ := identify a b hg hinv hbad hdone
  have hm := treeSim_collector_transcript_exit K D d.count d.T₀ d.lacked
    d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.masks d.history d.st₁ d.st₂ d.states
  change RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2) _
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rcases hd with ⟨had, hcache, hsteps | ⟨sent, hsteps⟩ | ⟨live, stopped, hsteps⟩⟩
  · rw [hsteps.1, hsteps.2, ← had]
    apply relTriple_post_mono (treeSim_collector_first_mixed prims K D A a.1.1 d.δ d.count
      d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ hm.1 a.2 b.2 hcache)
    intro u z h
    rcases h with ⟨had, _, hu, hz, hc, hl, hr⟩
    rw [hu, hz, ← had]
    exact close.first u.1.1 u.1.2.2 u.2 z.2 hc hl hr
  · rw [hsteps.1, hsteps.2, ← had]
    rw [treeSim_collector_second_factor, treeSim_collector_second_factor]
    simp only [simulateQ_bind, StateT.run_bind]
    rw [hm.2.1]
    apply relTriple_bind (treeSim_local_streamRel_fixed prims D d.δ _ a.2 b.2 hcache)
    intro r₁ r₂ hr
    rw [hr.1]
    apply relTriple_bind (close.resume r₂.1.1 sent r₂.1.2 r₁.2 r₂.2 hr.2.1 hr.2.2.1 hr.2.2.2)
    intro u z hz
    simp only [simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure hz

  · rw [hsteps.1, hsteps.2, ← had]
    apply relTriple_post_mono (treeSim_collector_partial_mixed prims K D A a.1.1 live stopped d.δ d.count
      d.rnd₁ d.rnd₂ d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ hm.1 a.2 b.2 hcache)
    intro u z h
    rcases h with ⟨had, _, hu, hz, hc, hl, hr⟩
    rw [hu, hz, ← had]
    exact close.abort u.1.1 u.2 z.2 hc hl hr

/-- The actual Coin opening, with arbitrary subsequent ceremony programs. -/
def treeSimCoinWaiting {α : Type} (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C E) (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α) :
    C.Party → Step C E RealSpec α :=
  fun i => if i ∈ D.1 then .done none else
    treeSimCoinStep K (localContext i) (rnd i) count (st i) (k i)

/-- Actual Coin entries share their complete field PRSS output. The input
contexts may have different dummy seeds; only their PRSS keys must agree. -/
theorem treeSim_coin_entry_mixed {α : Type} (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (keys : ctx₁.prss = ctx₂.prss)
    (count : ℕ) (st₁ st₂ : RunState C) (lab : st₁.label = st₂.label)
    (future : TreeSimFutureZero st₁.label δ)
    (k₁ k₂ : List E × RunState C → PartyM C E RealSpec α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (worldRoles.honest (advance
        ((((realCheckGadgets K ctx₁).coin count).run st₁ >>= k₁).run)))).run a)
      ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
        ((((realCheckGadgets K ctx₂).coin count).run st₂ >>= k₂).run)))).run b)
      (fun u z => (∃ rnd, u.1 = treeSimCoinStep K ctx₁ rnd count st₁ k₁ ∧
        z.1 = treeSimCoinStep K ctx₂ rnd count st₂ k₂) ∧ TreeSimStreamRel δ u.2 z.2) := by
  rw [treeSim_coin_entry, treeSim_coin_entry, ← lab,
    ← treeSim_prssDraw_context ctx₁ ctx₂ self keys]
  simp only [simulateQ_map, StateT.run_map]
  apply relTriple_map
  apply relTriple_post_mono (treeSim_prssElements_mixed prims K D δ visible ctx₁ st₁.label 1 count future a b h)
  intro u z hu
  exact ⟨⟨u.1, rfl, by rw [hu.1]⟩, hu.2⟩

/-- Coin stops immediately after its field draw, so saved continuations cannot
write another stream label before this opening is exposed. -/
theorem treeSim_coin_entry_frame {α : Type} (D : C.Coalition) (ctx : Context C)
    (count : ℕ) (st : RunState C) (k : List E × RunState C → PartyM C E RealSpec α)
    (s : HashCache C × HiddenCache C) (r : Step C E RealSpec α × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (worldRoles.honest (advance
      ((((realCheckGadgets K ctx).coin count).run st >>= k).run)))).run s)) :
    TreeSimCacheFrame st.label s.2 r.2.2 := by
  rw [treeSim_coin_entry] at hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  exact treeSim_prssElements_frame prims K D ctx st.label 1 count s u hu

/-- After sampling, Coin uses only the operator identity from its context. -/
theorem treeSim_coinStep_context {α : Type} (ctx₁ ctx₂ : Context C)
    (self : ctx₁.self = ctx₂.self) (rnd : PrssOutput C E) (count : ℕ) (st : RunState C)
    (k : List E × RunState C → PartyM C E RealSpec α) :
    treeSimCoinStep K ctx₁ rnd count st k = treeSimCoinStep K ctx₂ rnd count st k := by
  cases ctx₁
  cases ctx₂
  cases self
  rfl

/-- All honest Coin entries use the same lazy cache, including repeated
holders. The result constructs a mask vector common to both worlds at full entry. -/
theorem treeSim_coin_all_start {α : Type} (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss)
    (count : ℕ) (st₁ st₂ : C.Party → RunState C)
    (lab : ∀ i, i ∉ D.1 → (st₁ i).label = (st₂ i).label)
    (future : ∀ i, i ∉ D.1 → TreeSimFutureZero (st₁ i).label δ)
    (k₁ k₂ : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D) (startSteps worldRoles D
        (fun i => ((realCheckGadgets K (ctx₁ i)).coin count).run (st₁ i) >>= k₁ i))).run a)
      ((simulateQ (streamWorld prims D) (startSteps worldRoles D
        (fun i => ((realCheckGadgets K (ctx₂ i)).coin count).run (st₂ i) >>= k₂ i))).run b)
      (fun u z => (∃ rnd, u.1 = treeSimCoinWaiting K D count rnd st₁ k₁ ∧
        z.1 = treeSimCoinWaiting K D count rnd st₂ k₂) ∧ TreeSimStreamRel δ u.2 z.2) := by
  unfold startSteps
  rw [simulateQ_sequenceFin, simulateQ_sequenceFin]
  have step : ∀ i s t, TreeSimStreamRel δ s t →
      RelTriple
        ((simulateQ (treeSimLoggedWorld prims D)
          (if i ∈ D.1 then pure (.done none) else worldRoles.honest (advance
            ((((realCheckGadgets K (ctx₁ i)).coin count).run (st₁ i) >>= k₁ i).run)))).run s)
        ((simulateQ (streamWorld prims D)
          (if i ∈ D.1 then pure (.done none) else worldRoles.honest (advance
            ((((realCheckGadgets K (ctx₂ i)).coin count).run (st₂ i) >>= k₂ i).run)))).run t)
        (fun u z => (∃ rnd, u.1 = treeSimCoinWaiting K D count (fun _ => rnd) st₁ k₁ i ∧
          z.1 = treeSimCoinWaiting K D count (fun _ => rnd) st₂ k₂ i) ∧ TreeSimStreamRel δ u.2 z.2) := by
    intro i s t hst
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨0, by simp [treeSimCoinWaiting, hi], by simp [treeSimCoinWaiting, hi]⟩, hst⟩
    · simp only [if_neg hi]
      apply relTriple_post_mono (treeSim_coin_entry_mixed prims K D δ visible (ctx₁ i) (ctx₂ i)
        ((self₁ i hi).trans (self₂ i hi).symm) (keys i hi) count (st₁ i) (st₂ i) (lab i hi)
        (future i hi) (k₁ i) (k₂ i) s t hst)
      intro u z hu
      obtain ⟨⟨rnd, hu, hz⟩, hc⟩ := hu
      refine ⟨⟨rnd, ?_, ?_⟩, hc⟩
      · rw [hu]
        simp only [treeSimCoinWaiting, if_neg hi]
        exact treeSim_coinStep_context K _ _ (self₁ i hi) rnd count (st₁ i) (k₁ i)
      · rw [hz]
        simp only [treeSimCoinWaiting, if_neg hi]
        exact treeSim_coinStep_context K _ _ (self₂ i hi) rnd count (st₂ i) (k₂ i)
  apply relTriple_post_mono (treeSim_sequenceFin_rel _ _ (TreeSimStreamRel δ)
    (fun i x y => ∃ rnd, x = treeSimCoinWaiting K D count (fun _ => rnd) st₁ k₁ i ∧
      y = treeSimCoinWaiting K D count (fun _ => rnd) st₂ k₂ i) step a b h)
  intro u z hu
  choose rnd h₁ h₂ using hu.1
  exact ⟨⟨rnd, funext h₁, funext h₂⟩, hu.2⟩

/-- The Coin view is independent of the saved histories and continuations. -/
theorem treeSim_coin_waiting_view {α : Type} (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C E) (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α) :
    treeSimRoundView D (treeSimCoinWaiting K D count rnd st k) = treeSimCoinView K D count rnd := by
  funext j i
  by_cases hi : i ∈ D.1 <;>
    simp [treeSimRoundView, treeSimCoinWaiting, treeSimCoinView, treeSimCoinStep, coinOut, hi, Step.outbox]

/-- Resolve both transport abort and the actual Shamir agreement test before
resuming Coin's continuation. -/
theorem treeSim_coin_local {α : Type} (D : C.Coalition) (count : ℕ)
    (rnd : C.Party → PrssOutput C E) (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (treeSimCoinWaiting K D count rnd st k) sent i =
      treeSimResume (k i) ((treeSimCoinOutput K D count rnd sent i).map
        (fun vals => (vals, nextLabel (st i)))) := by
  have hin : (fun j => if j ∈ D.1 then sent j i else
      (treeSimCoinWaiting K D count rnd st k j).delivered i) =
      fun j => if j ∈ D.1 then sent j i else coinOut K j count (rnd j) i := by
    funext j
    by_cases hj : j ∈ D.1 <;>
      simp [hj, treeSimCoinWaiting, treeSimCoinStep, Step.delivered, coinOut]
  by_cases hi : i ∈ D.1
  · simp [roundLocal, treeSimCoinWaiting, treeSimCoinOutput, hi, treeSimResume]
  · simp only [roundLocal, treeSimCoinWaiting, if_neg hi, treeSimCoinStep]
    simp only [treeSimCoinWaiting, treeSimCoinStep] at hin
    rw [hin]
    unfold treeSimCoinOutput
    rw [if_neg hi]
    unfold coinRes openRes exchangeResume anyAbort require OpenAgreesN openValueN
    dsimp only
    simp only [openShareN, openShare]
    split_ifs <;> simp [treeSimResume] <;> rfl

/-- The real Coin round makes one common rushing call and resumes the exact
optional outputs in the driver's order, retaining the shared oracle state. -/
theorem treeSim_coin_round_factor {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (count : ℕ)
    (rnd : C.Party → PrssOutput C E) (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state (treeSimCoinWaiting K D count rnd st k) = (do
      let b ← worldRoles.adversary (A.round state (treeSimCoinView K D count rnd))
      let next ← treeSimResumeAll k (fun i => (treeSimCoinOutput K D count rnd b.2 i).map
        (fun vals => (vals, nextLabel (st i))))
      pure (b.1, next, b.2)) := by
  rw [stepRound_real]
  change (do
    let b ← worldRoles.adversary (A.round state
      (treeSimRoundView D (treeSimCoinWaiting K D count rnd st k)))
    let next ← free (Concrete.sequenceFin (roundLocal D (treeSimCoinWaiting K D count rnd st k) b.2))
    pure (b.1, next, b.2)) = _
  rw [treeSim_coin_waiting_view]
  apply bind_congr
  intro b
  congr 1
  congr 1
  congr 1
  funext i
  exact treeSim_coin_local K D count rnd st k b.2 i

/-- Coin entries that retain previously aborted honest parties. -/
def treeSimCoinPartial {α : Type} (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (rnd : C.Party → PrssOutput C E)
    (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α) :
    C.Party → Step C E RealSpec α := fun i =>
  if live i then treeSimCoinWaiting K D count rnd st k i else .done none

theorem treeSim_coin_partial_view {α : Type} (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (rnd : C.Party → PrssOutput C E)
    (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α) :
    treeSimRoundView D (treeSimCoinPartial K D live count rnd st k) =
      fun c i => if live i then treeSimCoinView K D count rnd c i else none := by
  have hv := treeSim_coin_waiting_view K D count rnd st k
  funext c i
  by_cases hl : live i = true
  · simpa only [treeSimRoundView, treeSimCoinPartial, if_pos hl] using congrFun (congrFun hv c) i
  · simp [treeSimRoundView, treeSimCoinPartial, hl, Step.outbox]

/-- A previously aborted honest operator sends an abort frame to every
remaining entrant. No Coin continuation is reached. -/
theorem treeSim_coin_partial_local {α : Type} (D : C.Coalition) (live : C.Party → Bool)
    (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true) (count : ℕ)
    (rnd : C.Party → PrssOutput C E)
    (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (treeSimCoinPartial K D live count rnd st k) sent i = pure (.done none) := by
  by_cases hl : live i = true
  · by_cases hi : i ∈ D.1
    · simp only [roundLocal, treeSimCoinPartial, if_pos hl, treeSimCoinWaiting, if_pos hi]
    · have hab : anyAbort (fun j => if j ∈ D.1 then sent j i else
          (treeSimCoinPartial K D live count rnd st k j).delivered i) = true := by
        obtain ⟨j, hj, hjl⟩ := stopped
        unfold anyAbort
        rw [List.any_eq_true]
        refine ⟨j, by simp [Committee.parties], ?_⟩
        simp [hj, treeSimCoinPartial, hjl, Step.delivered, Msg.isAbort]
      simp only [roundLocal, treeSimCoinPartial, if_pos hl, treeSimCoinWaiting,
        if_neg hi, treeSimCoinStep, localContext]
      change advance (exchangeResume (G := RealSpec) _ (fun j => if j ∈ D.1 then sent j i else
        (treeSimCoinPartial K D live count rnd st k j).delivered i)) = _
      unfold exchangeResume
      unfold anyAbort at hab
      rw [if_pos hab]
      rfl
  · simp only [roundLocal, treeSimCoinPartial, if_neg hl]

/-- Exact abort propagation at a partially active Coin entry. This is
one actual network round, so the rushing adversary still receives its view. -/
theorem treeSim_coin_partial_factor {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (live : C.Party → Bool)
    (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true) (count : ℕ)
    (rnd : C.Party → PrssOutput C E)
    (st : C.Party → RunState C)
    (k : C.Party → List E × RunState C → PartyM C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state (treeSimCoinPartial K D live count rnd st k) = (do
      let b ← worldRoles.adversary (A.round state fun c i => if live i then treeSimCoinView K D count rnd c i else none)
      pure (b.1, (fun _ => Step.done none), b.2)) := by
  rw [stepRound_real]
  change (do
    let b ← worldRoles.adversary (A.round state
      (treeSimRoundView D (treeSimCoinPartial K D live count rnd st k)))
    let next ← free (Concrete.sequenceFin (roundLocal D (treeSimCoinPartial K D live count rnd st k) b.2))
    pure (b.1, next, b.2)) = _
  rw [treeSim_coin_partial_view]
  apply bind_congr
  intro b
  rw [sequenceFin_congr_pure _ (fun _ => Step.done none)
    (treeSim_coin_partial_local K D live stopped count rnd st k b.2)]
  simp only [free_pure, pure_bind]

/-- Remaining obligations concern the programs after Coin and their invariant;
Coin's adversarial call, opening, agreement test and abort are proved below. -/
structure TreeSimCoinClosure (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (δ : HiddenAddress C → Bit) (st₁ st₂ : C.Party → RunState C)
    (k₁ k₂ : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput)
    (initial₁ initial₂ : HiddenCache C) where
  J : TreeSimState C → (HashCache C × HiddenCache C) → Prop
  Q : C.Party → Step C E RealSpec TreeOutput → Step C E RealSpec TreeOutput → Prop
  entry : ∀ a b, TreeSimStreamRel δ a b → a.1.2 = initial₁ → b.2 = initial₂ → J a b
  abort : ∀ i, Q i (.done none) (.done none)
  continues : ∀ i vals a b, J a b →
    RelTriple ((simulateQ (treeSimLoggedWorld prims D)
      (free (advance (k₁ i (vals, nextLabel (st₁ i))).run))).run a)
      ((simulateQ (streamWorld prims D)
      (free (advance (k₂ i (vals, nextLabel (st₂ i))).run))).run b)
      (fun u z => Q i u.1 z.1 ∧ J u.2 z.2)
  exit : ∀ state s₁ s₂ a b, (∀ i, Q i (s₁ i) (s₂ i)) → J a b →
    Bad a ∨ Inv ((state, s₁), a) ((state, s₂), b)

/-- Identify either a complete Coin opening or its forced-abort partial
entry. These are program shapes and continuation obligations, not a round coupling. -/
def TreeSimCoinBoundary (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ count rnd st₁ st₂ k₁ k₂ δ,
    a.1.1 = b.1.1 ∧ TreeSimStreamRel δ a.2 b.2 ∧
    ((a.1.2 = treeSimCoinWaiting K D count rnd st₁ k₁ ∧
      b.1.2 = treeSimCoinWaiting K D count rnd st₂ k₂ ∧
      Nonempty (TreeSimCoinClosure prims D A Bad Inv δ st₁ st₂ k₁ k₂ a.2.1.2 b.2.2)) ∨
    ∃ live, (∃ j, j ∉ D.1 ∧ live j ≠ true) ∧
      a.1.2 = treeSimCoinPartial K D live count rnd st₁ k₁ ∧
      b.1.2 = treeSimCoinPartial K D live count rnd st₂ k₂ ∧
      (∀ state u z, TreeSimStreamRel δ u z → u.1.2 = a.2.1.2 → z.2 = b.2.2 →
        Bad u ∨ Inv ((state, fun _ => .done none), u) ((state, fun _ => .done none), z)))

/-- The actual Coin stage is reduced to local post-Coin continuation proofs.
Its shared rushing response is coupled with the two hidden caches untouched. -/
theorem treeSim_coin_preserves (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (stage : TreeSimConfig A (TreeSimState C) → TreeSimStage)
    (identify : ∀ a b, stage a = .coin → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
      TreeSimCoinBoundary prims K D A Bad Inv a b) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A Bad Inv stage .coin := by
  intro a b hg hinv hbad hdone
  obtain ⟨count, rnd, st₁, st₂, k₁, k₂, δ, had, hc, boundary⟩ :=
    identify a b hg hinv hbad hdone
  change RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2) _
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rcases boundary with ⟨ha, hb, ⟨close⟩⟩ | ⟨live, stopped, ha, hb, close⟩
  · rw [ha, hb, ← had, treeSim_coin_round_factor, treeSim_coin_round_factor]
    simp only [simulateQ_bind, StateT.run_bind]
    apply relTriple_bind (treeSim_local_streamRel_fixed prims D δ _ a.2 b.2 hc)
    intro r₁ r₂ hr
    rw [hr.1]
    have hJ := close.entry r₁.2 r₂.2 hr.2.1 hr.2.2.1 hr.2.2.2
    refine relTriple_bind (treeSim_resumeAll_rel prims D k₁ k₂ _ _ close.J close.Q
      (fun i u z hu => ?_) r₁.2 r₂.2 hJ) ?_
    · cases ho : treeSimCoinOutput K D count rnd r₂.1.2 i with
      | none =>
        simp only [Option.map_none, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨close.abort i, hu⟩
      | some vals =>
        simp only [Option.map_some, treeSimResume]
        exact close.continues i vals u z hu
    · intro u z hz
      simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (close.exit r₂.1.1 u.1 z.1 u.2 z.2 hz.1 hz.2)
  · rw [ha, hb, ← had, treeSim_coin_partial_factor K D A _ live stopped,
      treeSim_coin_partial_factor K D A _ live stopped]
    simp only [simulateQ_bind, StateT.run_bind]
    apply relTriple_bind (treeSim_local_streamRel_fixed prims D δ _ a.2 b.2 hc)
    intro r₁ r₂ hr
    simp only [simulateQ_pure, StateT.run_pure]
    apply relTriple_pure_pure
    rw [hr.1]
    exact close r₂.1.1 r₁.2 r₂.2 hr.2.1 hr.2.2.1 hr.2.2.2

/-- Concrete resumption into Coin. The Coin-label zero translation
is derived from the preceding translated bit block, not supplied as a new premise. -/
structure TreeSimCoinNext (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C)) where
  ρ : ℕ
  idx : ℕ
  blockCount : ℕ
  dt : C.Term → Fin blockCount → Bit
  dp : C.Pair → Fin blockCount → Bit
  past : HiddenAddress C → Bit
  pastZero : TreeSimFutureZero ρ past
  visiblePast : ∀ x, ¬ Hidden D x.1.1 → past x = 0
  translation : δ = past + treeSimBlockShift D ρ idx blockCount dt dp
  count : ℕ
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  keys : ∀ i, i ∉ D.1 → (ctx₁ i).prss = (ctx₂ i).prss
  st₁ : C.Party → RunState C
  st₂ : C.Party → RunState C
  lab₁ : ∀ i, i ∉ D.1 → (st₁ i).label = ρ + 1
  lab₂ : ∀ i, i ∉ D.1 → (st₂ i).label = ρ + 1
  live : C.Party → Bool
  x₁ : C.Party → Shares C Bit × RunState C
  x₂ : C.Party → Shares C Bit × RunState C
  shape₁ : ∀ i, out₁ i = if i ∈ D.1 then none else if live i then some (x₁ i) else none
  shape₂ : ∀ i, out₂ i = if i ∈ D.1 then none else if live i then some (x₂ i) else none
  next₁ : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput
  next₂ : C.Party → List E × RunState C → PartyM C E RealSpec TreeOutput
  program₁ : ∀ i, i ∉ D.1 → live i = true →
    k₁ i (x₁ i) = ((realCheckGadgets K (ctx₁ i)).coin count).run (st₁ i) >>= next₁ i
  program₂ : ∀ i, i ∉ D.1 → live i = true →
    k₂ i (x₂ i) = ((realCheckGadgets K (ctx₂ i)).coin count).run (st₂ i) >>= next₂ i

/-- The previous mask translation is zero at Coin's next label. -/
theorem TreeSimCoinNext.futureZero (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C))
    (n : TreeSimCoinNext K D δ k₁ k₂ out₁ out₂) : TreeSimFutureZero (n.ρ + 1) δ := by
  intro x hx
  rw [n.translation]
  exact treeSim_futureZero_extend D n.ρ n.idx n.blockCount n.dt n.dp n.past n.pastZero x hx

/-- Resume the actual optional gadget outputs into Coin, preserving the
shared caches and constructing field masks common to both worlds. No assumption
of equal Coin masks or of a probabilistic resumption appears in the certificate. -/
theorem TreeSimCoinNext.coupling (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C))
    (n : TreeSimCoinNext K D δ k₁ k₂ out₁ out₂)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hc : TreeSimStreamRel δ a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => (∃ rnd,
        u.1 = treeSimCoinPartial K D n.live n.count rnd n.st₁ n.next₁ ∧
        z.1 = treeSimCoinPartial K D n.live n.count rnd n.st₂ n.next₂) ∧ TreeSimStreamRel δ u.2 z.2) := by
  have visible : ∀ x, ¬ Hidden D x.1.1 → δ x = 0 := by
    intro x hx
    rw [n.translation]
    simp only [Pi.add_apply, n.visiblePast x hx,
      treeSim_blockShift_visible D n.ρ n.idx n.blockCount n.dt n.dp x hx, zero_add]
  let Q := fun i (u z : Step C E RealSpec TreeOutput) => ∃ rnd,
    u = treeSimCoinPartial K D n.live n.count (fun _ => rnd) n.st₁ n.next₁ i ∧
    z = treeSimCoinPartial K D n.live n.count (fun _ => rnd) n.st₂ n.next₂ i
  have step : ∀ i s t, TreeSimStreamRel δ s t →
      RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (treeSimResume (k₁ i) (out₁ i)))).run s)
        ((simulateQ (streamWorld prims D) (free (treeSimResume (k₂ i) (out₂ i)))).run t)
        (fun u z => Q i u.1 z.1 ∧ TreeSimStreamRel δ u.2 z.2) := by
    intro i s t hst
    rw [n.shape₁ i, n.shape₂ i]
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨0, by simp [treeSimCoinPartial, treeSimCoinWaiting, hi],
        by simp [treeSimCoinPartial, treeSimCoinWaiting, hi]⟩, hst⟩
    · simp only [if_neg hi]
      by_cases hl : n.live i = true
      · simp only [if_pos hl, treeSimResume, n.program₁ i hi hl, n.program₂ i hi hl]
        apply relTriple_post_mono (treeSim_coin_entry_mixed prims K D δ visible (n.ctx₁ i) (n.ctx₂ i)
          ((n.self₁ i hi).trans (n.self₂ i hi).symm) (n.keys i hi) n.count (n.st₁ i) (n.st₂ i)
          ((n.lab₁ i hi).trans (n.lab₂ i hi).symm)
          (by rw [n.lab₁ i hi]; exact n.futureZero K D δ k₁ k₂ out₁ out₂)
          (n.next₁ i) (n.next₂ i) s t hst)
        intro u z hu
        obtain ⟨⟨rnd, hu, hz⟩, hc⟩ := hu
        refine ⟨⟨rnd, ?_, ?_⟩, hc⟩
        · rw [hu]
          simp only [treeSimCoinPartial, treeSimCoinWaiting, if_pos hl, if_neg hi]
          exact treeSim_coinStep_context K _ _ (n.self₁ i hi) rnd n.count (n.st₁ i) (n.next₁ i)
        · rw [hz]
          simp only [treeSimCoinPartial, treeSimCoinWaiting, if_pos hl, if_neg hi]
          exact treeSim_coinStep_context K _ _ (n.self₂ i hi) rnd n.count (n.st₂ i) (n.next₂ i)
      · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨⟨0, by simp [treeSimCoinPartial, hl],
          by simp [treeSimCoinPartial, hl]⟩, hst⟩
  apply relTriple_post_mono (treeSim_resumeAll_rel prims D k₁ k₂ out₁ out₂ (TreeSimStreamRel δ) Q step a b hc)
  intro u z hu
  choose rnd h₁ h₂ using hu.1
  exact ⟨⟨rnd, funext h₁, funext h₂⟩, hu.2⟩

/-- A selectively aborted vector resumes only its live programs. No local
entry can touch another label, even after earlier holders populate this one. -/
theorem treeSim_coin_resume_frame {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (ρ count : ℕ) (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (next : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (out : C.Party → Option (Shares C Bit × RunState C))
    (x : C.Party → Shares C Bit × RunState C) (live : C.Party → Bool)
    (lab : ∀ i, i ∉ D.1 → live i = true → (st i).label = ρ)
    (shape : ∀ i, out i = if i ∈ D.1 then none else if live i then some (x i) else none)
    (program : ∀ i, i ∉ D.1 → live i = true →
      k i (x i) = ((realCheckGadgets K (ctx i)).coin count).run (st i) >>= next i)
    (s : HashCache C × HiddenCache C) (r : (C.Party → Step C E RealSpec α) × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (treeSimResumeAll k out)).run s)) :
    TreeSimCacheFrame ρ s.2 r.2.2 := by
  unfold treeSimResumeAll at hr
  rw [free_sequenceFin, simulateQ_sequenceFin] at hr
  intro y hy
  apply treeSim_state_sequenceFin_preserves (fun t : HashCache C × HiddenCache C => t.2 y) _ _ s r hr
  intro i a b hb
  rw [shape i] at hb
  by_cases hi : i ∈ D.1
  · simp [hi, treeSimResume, free_pure] at hb
    subst b
    rfl
  · simp only [if_neg hi] at hb
    by_cases hl : live i = true
    · simp only [if_pos hl, treeSimResume, program i hi hl] at hb
      have h := treeSim_coin_entry_frame prims K D (ctx i) count (st i) (next i) a b hb
      rw [lab i hi hl] at h
      exact h y hy
    · simp [hl, treeSimResume, free_pure] at hb
      subst b
      rfl

/-- The logged resumption has exactly the same private-cache footprint. -/
theorem treeSim_coin_resume_logged_frame {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (ρ count : ℕ) (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (next : C.Party → List E × RunState C → PartyM C E RealSpec α)
    (out : C.Party → Option (Shares C Bit × RunState C))
    (x : C.Party → Shares C Bit × RunState C) (live : C.Party → Bool)
    (lab : ∀ i, i ∉ D.1 → live i = true → (st i).label = ρ)
    (shape : ∀ i, out i = if i ∈ D.1 then none else if live i then some (x i) else none)
    (program : ∀ i, i ∉ D.1 → live i = true →
      k i (x i) = ((realCheckGadgets K (ctx i)).coin count).run (st i) >>= next i)
    (s : TreeSimState C) (r : (C.Party → Step C E RealSpec α) × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k out)).run s)) :
    TreeSimCacheFrame ρ s.1.2 r.2.1.2 := by
  apply treeSim_coin_resume_frame prims K D ctx ρ count st k next out x live lab shape program
    s.1 (r.1, r.2.1)
  rw [← treeSimLoggedWorld_erase prims D _ s.1 s.2, support_map]
  exact ⟨r, hr, rfl⟩

/-- The actual Coin resume preserves future cache freshness on both sides.
The input freshness is transported through every sequential holder read. -/
theorem TreeSimCoinNext.coupling_fresh (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C))
    (n : TreeSimCoinNext K D δ k₁ k₂ out₁ out₂)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hc : TreeSimStreamRel δ a b)
    (fresh : TreeSimFutureEmpty (n.ρ + 1) a.1.2) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => TreeSimCacheFrame (n.ρ + 1) a.1.2 u.2.1.2 ∧
        TreeSimCacheFrame (n.ρ + 1) b.2 z.2.2 ∧
        TreeSimFutureEmpty (n.ρ + 2) u.2.1.2 ∧ TreeSimFutureEmpty (n.ρ + 2) z.2.2 ∧
        TreeSimFutureZero (n.ρ + 2) δ ∧ (∃ rnd,
          u.1 = treeSimCoinPartial K D n.live n.count rnd n.st₁ n.next₁ ∧
          z.1 = treeSimCoinPartial K D n.live n.count rnd n.st₂ n.next₂) ∧
        TreeSimStreamRel δ u.2 z.2) := by
  apply relTriple_post_mono (treeSim_relTriple_support (n.coupling prims K D δ k₁ k₂ out₁ out₂ a b hc))
  intro u z h
  have f₁ := treeSim_coin_resume_logged_frame prims K D n.ctx₁ (n.ρ + 1) n.count n.st₁ k₁ n.next₁
    out₁ n.x₁ n.live (fun i hi _ => n.lab₁ i hi) n.shape₁ n.program₁ a u h.2.1
  have f₂ := treeSim_coin_resume_frame prims K D n.ctx₂ (n.ρ + 1) n.count n.st₂ k₂ n.next₂
    out₂ n.x₂ n.live (fun i hi _ => n.lab₂ i hi) n.shape₂ n.program₂ b z h.2.2
  refine ⟨f₁, f₂, treeSim_futureEmpty_after fresh f₁,
    treeSim_futureEmpty_after (treeSim_futureEmpty_related fresh hc.2) f₂, ?_, h.1⟩
  intro x hx
  exact n.futureZero K D δ k₁ k₂ out₁ out₂ x (by omega)

/-- Peer-mode Rerand retains its real PRSS draw and its ceremony continuation. -/
theorem treeSim_rerand_entry {α : Type} (ctx : Context C) (mode : ReshareMode)
    (x : Shares C Bit) (count : ℕ) (st : RunState C)
    (k : Shares C Bit × RunState C → PartyM C E RealSpec α) :
    worldRoles.honest (advance ((((realRunGadgets K ctx mode).rerand x count).run st >>= k).run)) =
      (fun rnd => treeSimPeerStep K ctx bitCodec rnd (ownerSum K ctx x) count st k) <$>
        free (liftComp (prssDraw ctx (bitCodec (E := E)) st.label 0 count) (LocalSpec C)) := by
  exact treeSim_peer_entry K ctx bitCodec 0 count (ownerSum K ctx x) st k

/-- Suspended peer exchanges, including the peer-mode exchange used by Rerand. -/
def treeSimPeerWaiting {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (count : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C) (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    C.Party → Step C E RealSpec α := fun i =>
  if i ∈ D.1 then .done none else treeSimPeerStep K (ctx i) bitCodec (rnd i) (v i) count (st i) (k i)

/-- Actual optional peer outputs, with the history and label recorded before
entering the next check gadget. -/
def treeSimPeerOutputs {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (count : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C) (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) : C.Party → Option (Shares C Bit × RunState C) := fun i =>
  if i ∈ D.1 then none else treeSimPeerReturn K (ctx i) (rnd i) (v i) count (st i)
    (fun j => if j ∈ D.1 then sent j i else (treeSimPeerWaiting K D ctx count rnd v st k j).delivered i)

theorem treeSim_peer_resume_local {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (count : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C) (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (treeSimPeerWaiting K D ctx count rnd v st k) sent i =
      treeSimResume (k i) (treeSimPeerOutputs K D ctx count rnd v st k sent i) := by
  by_cases hi : i ∈ D.1
  · simp [roundLocal, treeSimPeerWaiting, treeSimPeerOutputs, hi, treeSimResume]
  · simp only [roundLocal, treeSimPeerWaiting, if_neg hi, treeSimPeerStep, treeSimPeerOutputs]
    unfold treeSimPeerReturn exchangeResume anyAbort
    dsimp only
    split_ifs <;> rfl

/-- One real peer round, followed by its actual optional continuations. -/
theorem treeSim_peer_resume_factor {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (ctx : C.Party → Context C)
    (count : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C) (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state (treeSimPeerWaiting K D ctx count rnd v st k) = (do
      let b ← worldRoles.adversary (A.round state (treeSimRoundView D (treeSimPeerWaiting K D ctx count rnd v st k)))
      let next ← treeSimResumeAll k (treeSimPeerOutputs K D ctx count rnd v st k b.2)
      pure (b.1, next, b.2)) := by
  rw [stepRound_real]
  change (do
    let b ← worldRoles.adversary (A.round state (treeSimRoundView D (treeSimPeerWaiting K D ctx count rnd v st k)))
    let next ← free (Concrete.sequenceFin (roundLocal D (treeSimPeerWaiting K D ctx count rnd v st k) b.2))
    pure (b.1, next, b.2)) = _
  apply bind_congr
  intro b
  congr 1
  congr 1
  congr 1
  funext i
  exact treeSim_peer_resume_local K D ctx count rnd v st k b.2 i

/-- Any honest computation confined to the hash cache couples without
modifying either hidden-stream cache. Its actual logged query origins remain. -/
theorem treeSim_onHash_coupling {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (m : StateT (HashCache C) ProbComp α)
    (hp : simulateQ (streamWorld prims D) p = onHash m)
    (δ : HiddenAddress C → Bit) (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hc : TreeSimStreamRel δ a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) p).run a)
      ((simulateQ (streamWorld prims D) p).run b)
      (fun u z => u.1 = z.1 ∧ TreeSimStreamRel δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  rcases a with ⟨⟨h, c₁⟩, log⟩
  rcases b with ⟨h', c₂⟩
  rcases hc with ⟨rfl, hc⟩
  have keepsHidden : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run ((h, c₁), log)),
      u.2.1.2 = c₁ := by
    intro u hu
    have hm : (u.1, u.2.1) ∈ support ((fun r => (r.1, r.2.1)) <$>
        (simulateQ (treeSimLoggedWorld prims D) p).run ((h, c₁), log)) := by
      rw [support_map]
      exact ⟨u, hu, rfl⟩
    rw [treeSimLoggedWorld_erase, hp] at hm
    simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hm
    obtain ⟨r, _, heq⟩ := hm
    exact (congrArg (fun x => x.2.2) heq).symm
  have e := congrArg (fun q => (fun r => (r.1, r.2.1, c₂)) <$> q)
    (treeSimLoggedWorld_erase prims D p (h, c₁) log)
  simp only [hp, onHash, StateT.run_mk, Functor.map_map] at e
  have he : (simulateQ (streamWorld prims D) p).run (h, c₂) =
      (fun u => (u.1, u.2.1.1, c₂)) <$>
        (simulateQ (treeSimLoggedWorld prims D) p).run ((h, c₁), log) := by
    simpa only [hp, onHash, StateT.run_mk] using e.symm
  rw [he]
  have hr : RelTriple
      (id <$> (simulateQ (treeSimLoggedWorld prims D) p).run ((h, c₁), log))
      ((fun u => (u.1, u.2.1.1, c₂)) <$> (simulateQ (treeSimLoggedWorld prims D) p).run ((h, c₁), log))
      (fun u z => u.1 = z.1 ∧ TreeSimStreamRel δ u.2 z.2 ∧ u.2.1.2 = c₁ ∧ z.2.2 = c₂) := by
    apply relTriple_map
    apply relTriple_post_mono (treeSim_refl_support _)
    rintro u _ ⟨hu, rfl⟩
    have hprivate := keepsHidden u hu
    exact ⟨rfl, ⟨rfl, by simpa only [id_eq, hprivate] using hc⟩, hprivate, rfl⟩
  simpa only [id_map] using hr

/-- A list of honest copy-hash calls uses only the common hash cache. -/
theorem treeSim_hashes_onHash (D : C.Coalition) (qs : List (Query C)) :
    simulateQ (streamWorld prims D) (free (liftComp (qs.mapM hashQuery) (LocalSpec C))) =
      onHash (qs.mapM (hashAnswer prims)) := by
  have single : ∀ q : Query C, simulateQ (streamWorld prims D)
      (free (liftComp (hashQuery q) (LocalSpec C))) = onHash (hashAnswer prims q) := by
    intro q
    unfold hashQuery
    erw [simulateQ_spec_query]
    rfl
  induction qs with
  | nil => simp [liftComp_pure, free_pure, treeSim_onHash_pure]
  | cons q qs ih =>
    simp only [List.mapM_cons, liftComp_bind, liftComp_pure, free_bind, free_pure,
      simulateQ_bind, simulateQ_pure, treeSim_onHash_bind, treeSim_onHash_pure, single, ih]

/-- Every actual stream-world query only extends the public cache. Hidden
stream sampling changes its separate table, and programming respects prior entries. -/
theorem treeSim_streamWorld_grows (D : C.Coalition) (t : (WorldSpec C).Domain)
    (s : HashCache C × HiddenCache C) (r : (WorldSpec C).Range t × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((streamWorld prims D t).run s)) : s.1 ≤ r.2.1 := by
  have onhash {α : Type} (m : StateT (HashCache C) ProbComp α)
      (hm : ∀ z ∈ support (m.run s.1), s.1 ≤ z.2)
      (z : α × (HashCache C × HiddenCache C)) (hz : z ∈ support ((onHash m).run s)) : s.1 ≤ z.2.1 := by
    simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    exact hm u hu
  rcases t with ((u | q | x) | p) | (u | q | x)
  · exact onhash _ (grows_localAnswer prims (.inl u) s.1) r hr
  · exact onhash _ (grows_localAnswer prims (.inr (.inl q)) s.1) r hr
  · exact onhash _ (grows_localAnswer prims (.inr (.inr x)) s.1) r hr
  · exact onhash _ (grows_programAnswer p s.1) r hr
  · exact onhash _ (grows_localAnswer prims (.inl u) s.1) r hr
  · exact onhash _ (grows_localAnswer prims (.inr (.inl q)) s.1) r hr
  · by_cases hx : Hidden D x.1
    · simp only [streamWorld, if_pos hx, StateT.run_mk, support_map, Set.mem_image] at hr
      obtain ⟨z, hz, rfl⟩ := hr
      exact le_rfl
    · simp only [streamWorld, if_neg hx] at hr
      exact onhash _ (grows_localAnswer prims (.inr (.inr x)) s.1) r hr

/-- Public entries survive arbitrary adaptive stream-world computations,
including honest continuations and simulator programming calls. -/
theorem treeSim_stream_grows {α : Type} (D : C.Coalition) (p : OracleComp (WorldSpec C) α)
    (s : HashCache C × HiddenCache C) (r : α × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) p).run s)) : s.1 ≤ r.2.1 := by
  induction p using OracleComp.inductionOn generalizing s r with
  | pure a =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hr
    subst r
    exact le_rfl
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      StateT.run_bind, support_bind, Set.mem_iUnion] at hr
    obtain ⟨u, hu, hr⟩ := hr
    exact (treeSim_streamWorld_grows prims D t s u hu).trans (ih u.1 u.2 r hr)

/-- Logging preserves the same monotone public cache. -/
theorem treeSim_logged_grows {α : Type} (D : C.Coalition) (p : OracleComp (WorldSpec C) α)
    (s : TreeSimState C) (r : α × TreeSimState C)
    (hr : r ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run s)) : s.1.1 ≤ r.2.1.1 := by
  have hm : (r.1, r.2.1) ∈ support ((fun z => (z.1, z.2.1)) <$>
      (simulateQ (treeSimLoggedWorld prims D) p).run s) := by
    rw [support_map]
    exact ⟨r, hr, rfl⟩
  rw [treeSimLoggedWorld_erase] at hm
  exact treeSim_stream_grows prims D p s.1 _ hm

/-- Empty replicated openings still hash every copy, including repeated
queries to the same `.copy []` address. -/
def treeSimEmptyCopyHashes : OracleComp (RoSpec C) (List HashOutput) :=
  C.terms.mapM fun _ => hashQuery (.copy [])

def treeSimEmptyOpenOut (i : C.Party) (digests : List HashOutput) : Mail C E :=
  fun j => if j = i then none else some (.bundle [
    .bits [], .hashes ((C.terms.zip digests).filterMap fun (T, d) =>
      if j ∉ C.holders T ∧ i ∈ C.holders T ∧ K.owner T ≠ i then some d else none)])

def TreeSimOpenValid (i : C.Party) (inbox : Mail C E) (copyDigests : List HashOutput) : Prop :=
  ∀ T : C.Term, i ∉ C.holders T → ∀ h ∈ C.holders T, h ≠ K.owner T →
    let sent := C.terms.filter fun T' => i ∉ C.holders T' ∧ h ∈ C.holders T' ∧ K.owner T' ≠ h
    (Msg.hashesOf (Msg.part (inbox h) 1))[sent.idxOf T]? = (C.terms.zip copyDigests).lookup T

/-- The suspended empty opening keeps the real received-hash checks. -/
def treeSimEmptyOpenStep {α : Type} (i : C.Party) (digests : List HashOutput)
    (k : PartyM C E RealSpec α) : Step C E RealSpec α :=
  .wait (treeSimEmptyOpenOut K i digests)
    (exchangeResume fun inbox => do
      let copyDigests ← oracleStep (treeSimEmptyCopyHashes (C := C))
      require (TreeSimOpenValid K i inbox copyDigests)
      k)

/-- Only the empty vector is consumed by the ceremony. Its opening still
retains all oracle calls, the exchange, and the malicious hash-check abort. -/
theorem treeSim_emptyOpen_entry {α : Type} (ctx : Context C) (v : Shares C Bit)
    (k : PartyM C E RealSpec α) :
    worldRoles.honest (advance ((openRep K ctx v 0 >>= fun _ => k).run)) =
      (fun digests => treeSimEmptyOpenStep K ctx.self digests k) <$>
        free (liftComp (treeSimEmptyCopyHashes (C := C)) (LocalSpec C)) := by
  unfold openRep
  simp only [vector, List.range_zero, List.map_nil, bind_assoc, pure_bind]
  simp only [worldRoles, advance_oracleStep_bind, free_bind, map_eq_bind_pure_comp]
  apply bind_congr
  intro digests
  have empty (xs : List C.Term) : xs.flatMap (fun _ => ([] : List Bit)) = [] :=
    List.flatMap_eq_nil_iff.mpr (by simp)
  simp only [empty, pure_bind, advance_exchange_bind, free_pure]
  rfl

/-- The zero-count branch of the real check skips directly to the real output
gadget. The actual `runJobs` output slicing is independent of the opened sharing
because every output width is zero. -/
theorem treeSim_emptyCheck_finish (ctx : Context C) (mode : ReshareMode)
    (tuples : List (Tuple C)) (v v' : Shares C Bit) (widths : List ℕ) (st : RunState C)
    (zero : ((tuples ++ [(⟨v, one K, v', widths.sum, .peer⟩ : Tuple C)]).map (·.count)).sum = 0) :
    ((do
      (realRunGadgets K ctx mode).verify (tuples ++ [⟨v, one K, v', widths.sum, .peer⟩])
      let opened ← (realRunGadgets K ctx mode).output v' widths.sum
      pure (widths.zipIdx.map fun (width, k) => vector width fun g => opened ((widths.take k).sum + g))
      : RunM C E RealSpec (List (List Bit))).run st) =
      (openRep K ctx v' 0 >>= fun _ => pure (widths.map (fun _ => []), st)) := by
  have wz : widths.sum = 0 := by
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero] at zero
    omega
  have each : ∀ w ∈ widths, w = 0 := List.sum_eq_zero_iff_forall_eq_nat.mp wz
  have sliced (opened : ℕ → Bit) :
      widths.zipIdx.map (fun (width, k) => vector width fun g => opened ((widths.take k).sum + g)) =
        widths.map (fun _ => ([] : List Bit)) := by
    have hmap : widths.zipIdx.map (fun (width, k) => vector width fun g => opened ((widths.take k).sum + g)) =
        widths.zipIdx.map (fun _ => ([] : List Bit)) := by
      apply List.map_congr_left
      intro p hp
      have hw := each p.1 (by
        rw [← List.zipIdx_map_fst 0 widths]
        exact List.mem_map.mpr ⟨p, hp, rfl⟩)
      simp only [hw, vector, List.range_zero, List.map_nil]
    rw [hmap]
    simpa only [List.map_map, Function.comp_def] using
      congrArg (List.map (fun _ : ℕ => ([] : List Bit))) (List.zipIdx_map_fst 0 widths)
  have chk : (realRunGadgets (G := RealSpec) K ctx mode).verify
      (tuples ++ [⟨v, one K, v', widths.sum, .peer⟩]) = pure PUnit.unit := by
    simp only [realRunGadgets, check, zero, if_pos]
  rw [chk]
  simp only [pure_bind, realRunGadgets, StateT.run_bind, StateT.run_lift,
    StateT.run_pure, wz, sliced, bind_assoc, pure_bind]

/-- The flat output count used by `runJobs` equals the sum of its slice widths. -/
theorem treeSim_output_count (jobs : List Circuit) :
    (jobs.zipIdx.flatMap fun (job, k) => job.outputs.map fun a => (k, a)).length =
      (jobs.map (·.outputs.length)).sum := by
  simp only [List.length_flatMap, List.length_map]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (fun js : List Circuit => (js.map (·.outputs.length)).sum) (List.zipIdx_map_fst 0 jobs)

/-- The actual output-count expression in `runJobs` satisfies the empty-check
normalization. This is the program equation needed by the empty successor. -/
theorem treeSim_emptyCheck_jobs_finish (ctx : Context C) (mode : ReshareMode)
    (tuples : List (Tuple C)) (v v' : Shares C Bit) (jobs : List Circuit) (st : RunState C)
    (zero : ((tuples ++ [(⟨v, one K, v',
      (jobs.zipIdx.flatMap fun (job, k) => job.outputs.map fun a => (k, a)).length, .peer⟩ : Tuple C)]).map
        (·.count)).sum = 0) :
    ((do
      let count := (jobs.zipIdx.flatMap fun (job, k) => job.outputs.map fun a => (k, a)).length
      (realRunGadgets K ctx mode).verify (tuples ++ [⟨v, one K, v', count, .peer⟩])
      let opened ← (realRunGadgets K ctx mode).output v' count
      let widths := jobs.map (·.outputs.length)
      pure (widths.zipIdx.map fun (width, k) => vector width fun g => opened ((widths.take k).sum + g))
      : RunM C E RealSpec (List (List Bit))).run st) =
      (openRep K ctx v' 0 >>= fun _ => pure ((jobs.map (·.outputs.length)).map (fun _ => []), st)) := by
  rw [treeSim_output_count] at zero ⊢
  exact treeSim_emptyCheck_finish K ctx mode tuples v v' _ st zero

/-- Empty openings enter with common copy digests and leave both hidden
caches unchanged, even when the shared hash cache was populated by the dealer. -/
theorem treeSim_emptyOpen_entry_coupling (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (ctx₁ ctx₂ : Context C) (self : ctx₁.self = ctx₂.self)
    (v₁ v₂ : Shares C Bit) (k₁ k₂ : PartyM C E RealSpec TreeOutput)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hc : TreeSimStreamRel δ a b) :
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.honest (advance ((openRep K ctx₁ v₁ 0 >>= fun _ => k₁).run)))).run a)
      ((simulateQ (streamWorld prims D)
        (worldRoles.honest (advance ((openRep K ctx₂ v₂ 0 >>= fun _ => k₂).run)))).run b)
      (fun u z => (∃ ds, u.1 = treeSimEmptyOpenStep K ctx₁.self ds k₁ ∧
        z.1 = treeSimEmptyOpenStep K ctx₁.self ds k₂) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  rw [treeSim_emptyOpen_entry, treeSim_emptyOpen_entry]
  simp only [simulateQ_map, StateT.run_map]
  apply relTriple_map
  have hp := treeSim_hashes_onHash prims D (C.terms.map fun _ => Query.copy [])
  simp only [List.mapM_map, Function.comp_def] at hp
  apply relTriple_post_mono (treeSim_onHash_coupling prims D _ _ hp δ a b hc)
  intro u z h
  exact ⟨⟨u.1, rfl, by rw [h.1, self]⟩, h.2⟩

/-- Repeated copy queries replay the value already installed by opening
entry. Unrelated public cache entries need not agree between executions. -/
theorem treeSim_copyHashes_cached (xs : List C.Term) (h : HashCache C) (digest : HashOutput)
    (cached : h (.copy []) = some digest) :
    (xs.mapM (fun _ => hashAnswer prims (.copy []))).run h =
      pure (List.replicate xs.length digest, h) := by
  induction xs with
  | nil => rfl
  | cons T xs ih =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure,
      hashAnswer_run_cached prims (by rintro ⟨_, heq, _⟩; cases heq) cached,
      pure_bind, ih, List.length_cons, List.replicate_succ]

/-- A nonempty sequence of empty-copy hashes installs one value and repeats
it on every copy. This includes an initially populated dealer cache. -/
theorem treeSim_copyHashes_populated (xs : List C.Term) (nonempty : xs ≠ [])
    (h : HashCache C) (r : List HashOutput × HashCache C)
    (hr : r ∈ support ((xs.mapM fun _ => hashAnswer prims (.copy [])).run h)) :
    ∃ digest, r.2 (.copy []) = some digest ∧ r.1 = List.replicate xs.length digest := by
  cases xs with
  | nil => exact False.elim (nonempty rfl)
  | cons T xs =>
    simp only [List.mapM_cons, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, hu, z, hz, rfl⟩ := hr
    have cached := hashAnswer_cached prims (q := Query.copy [])
      (by rintro ⟨_, heq, _⟩; cases heq) h u hu
    rw [treeSim_copyHashes_cached prims xs u.2 u.1 cached,
      support_pure, Set.mem_singleton_iff] at hz
    subst z
    exact ⟨u.1, cached, rfl⟩

/-- The honest entry really populates the copy address required by the later
checks. This is a property of its actual execution, with no freshness premise. -/
theorem treeSim_emptyOpen_entry_populated (D : C.Coalition) (ctx : Context C)
    (v : Shares C Bit) (k : PartyM C E RealSpec TreeOutput)
    (s : HashCache C × HiddenCache C) (r : Step C E RealSpec TreeOutput × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D)
      (worldRoles.honest (advance ((openRep K ctx v 0 >>= fun _ => k).run)))).run s)) :
    ∃ digest, r.2.1 (.copy []) = some digest ∧
      r.1 = treeSimEmptyOpenStep K ctx.self (List.replicate C.terms.length digest) k := by
  rw [treeSim_emptyOpen_entry] at hr
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at hr
  obtain ⟨u, hu, rfl⟩ := hr
  have hp := treeSim_hashes_onHash prims D (C.terms.map fun _ => Query.copy [])
  simp only [List.mapM_map, Function.comp_def] at hp
  change u ∈ support ((simulateQ (streamWorld prims D)
    (free (liftComp (C.terms.mapM fun _ => hashQuery (.copy [])) (LocalSpec C)))).run s) at hu
  rw [hp] at hu
  simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hu
  obtain ⟨z, hz, rfl⟩ := hu
  have nonempty : C.terms ≠ [] := by
    intro he
    have hm := mem_terms K.publicTerm
    rw [he] at hm
    exact List.not_mem_nil hm
  obtain ⟨digest, cached, vals⟩ := treeSim_copyHashes_populated prims C.terms nonempty s.1 z hz
  exact ⟨digest, cached, by rw [vals]⟩

/-- Optional Rerand results that skip an empty check still execute the real
empty opening. Its continuation is not assumed to have succeeded. -/
structure TreeSimEmptyOpenNext (D : C.Coalition)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C)) where
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  v₁ : C.Party → Shares C Bit
  v₂ : C.Party → Shares C Bit
  live : C.Party → Bool
  x₁ : C.Party → Shares C Bit × RunState C
  x₂ : C.Party → Shares C Bit × RunState C
  shape₁ : ∀ i, out₁ i = if i ∈ D.1 then none else if live i then some (x₁ i) else none
  shape₂ : ∀ i, out₂ i = if i ∈ D.1 then none else if live i then some (x₂ i) else none
  next₁ : C.Party → PartyM C E RealSpec TreeOutput
  next₂ : C.Party → PartyM C E RealSpec TreeOutput
  program₁ : ∀ i, i ∉ D.1 → live i = true →
    k₁ i (x₁ i) = (openRep K (ctx₁ i) (v₁ i) 0 >>= fun _ => next₁ i)
  program₂ : ∀ i, i ∉ D.1 → live i = true →
    k₂ i (x₂ i) = (openRep K (ctx₂ i) (v₂ i) 0 >>= fun _ => next₂ i)

def treeSimEmptyOpenPartial (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (next : C.Party → PartyM C E RealSpec TreeOutput) :
    C.Party → Step C E RealSpec TreeOutput := fun i =>
  if i ∈ D.1 then .done none else if live i then treeSimEmptyOpenStep K i (ds i) (next i) else .done none

/-- A suspended empty opening can take another round only if an honest
operator is live. Otherwise every honest step is already `.done none`. -/
theorem treeSim_emptyOpenPartial_active (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (next : C.Party → PartyM C E RealSpec TreeOutput)
    (h : ¬ AllDone D (treeSimEmptyOpenPartial K D live ds next)) :
    ∃ i, i ∉ D.1 ∧ live i = true := by
  by_contra hn
  apply h
  intro i hi
  have hl : live i ≠ true := fun hl => hn ⟨i, hi, hl⟩
  simp [treeSimEmptyOpenPartial, hi, hl, Step.isDone]

/-- Sequence the actual empty-opening entries in operator order. In particular,
later operators use the hash cache left by earlier ones. -/
theorem TreeSimEmptyOpenNext.coupling (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C))
    (n : TreeSimEmptyOpenNext K D k₁ k₂ out₁ out₂)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hc : TreeSimStreamRel δ a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => (∃ ds, u.1 = treeSimEmptyOpenPartial K D n.live ds n.next₁ ∧
        z.1 = treeSimEmptyOpenPartial K D n.live ds n.next₂) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  let J := fun s t => TreeSimStreamRel δ s t ∧ s.1.2 = a.1.2 ∧ t.2 = b.2
  let Q := fun i (u z : Step C E RealSpec TreeOutput) => ∃ ds,
    u = treeSimEmptyOpenPartial K D n.live (fun _ => ds) n.next₁ i ∧
    z = treeSimEmptyOpenPartial K D n.live (fun _ => ds) n.next₂ i
  have step : ∀ i s t, J s t →
      RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (treeSimResume (k₁ i) (out₁ i)))).run s)
        ((simulateQ (streamWorld prims D) (free (treeSimResume (k₂ i) (out₂ i)))).run t)
        (fun u z => Q i u.1 z.1 ∧ J u.2 z.2) := by
    intro i s t hst
    rw [n.shape₁ i, n.shape₂ i]
    by_cases hi : i ∈ D.1
    · simp only [if_pos hi, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨⟨[], by simp [treeSimEmptyOpenPartial, hi],
        by simp [treeSimEmptyOpenPartial, hi]⟩, hst⟩
    · simp only [if_neg hi]
      by_cases hl : n.live i = true
      · simp only [if_pos hl, treeSimResume, n.program₁ i hi hl, n.program₂ i hi hl]
        apply relTriple_post_mono (treeSim_emptyOpen_entry_coupling prims K D δ (n.ctx₁ i) (n.ctx₂ i)
          ((n.self₁ i hi).trans (n.self₂ i hi).symm) (n.v₁ i) (n.v₂ i) (n.next₁ i) (n.next₂ i) s t hst.1)
        intro u z hu
        obtain ⟨⟨ds, hu, hz⟩, hc, h₁, h₂⟩ := hu
        refine ⟨⟨ds, ?_, ?_⟩, hc, h₁.trans hst.2.1, h₂.trans hst.2.2⟩
        · simpa only [treeSimEmptyOpenPartial, if_neg hi, if_pos hl, n.self₁ i hi] using hu
        · simpa only [treeSimEmptyOpenPartial, if_neg hi, if_pos hl, n.self₁ i hi] using hz
      · simp only [if_neg hl, treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
        exact relTriple_pure_pure ⟨⟨[], by simp [treeSimEmptyOpenPartial, hi, hl],
          by simp [treeSimEmptyOpenPartial, hi, hl]⟩, hst⟩
  apply relTriple_post_mono (treeSim_resumeAll_rel prims D k₁ k₂ out₁ out₂ J Q step a b ⟨hc, rfl, rfl⟩)
  intro u z hu
  choose ds h₁ h₂ using hu.1
  exact ⟨⟨ds, funext h₁, funext h₂⟩, hu.2⟩

private theorem treeSim_sequenceFin_preserves_prop {α σ : Type} {n : ℕ}
    (P : σ → Prop) (f : Fin n → StateT σ ProbComp α)
    (preserve : ∀ i s r, P s → r ∈ support ((f i).run s) → P r.2)
    (s : σ) (hs : P s) (r : (Fin n → α) × σ)
    (hr : r ∈ support ((Concrete.sequenceFin f).run s)) : P r.2 := by
  induction n generalizing s with
  | zero =>
    have heq : r = (Fin.elim0, s) := by simpa [Concrete.sequenceFin] using hr
    subst r
    exact hs
  | succ n ih =>
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr
    exact ih (fun i => f i.succ) (fun i => preserve i.succ) u.2 (preserve 0 s u hs hu) v hv

/-- A property established by one operator and preserved by all later
operators holds after the actual sequential traversal. -/
private theorem treeSim_sequenceFin_establishes {α σ : Type} {n : ℕ}
    (P : σ → Prop) (f : Fin n → StateT σ ProbComp α)
    (preserve : ∀ i s r, P s → r ∈ support ((f i).run s) → P r.2)
    (i : Fin n) (establish : ∀ s r, r ∈ support ((f i).run s) → P r.2)
    (s : σ) (r : (Fin n → α) × σ)
    (hr : r ∈ support ((Concrete.sequenceFin f).run s)) : P r.2 := by
  induction n generalizing s with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    simp only [Concrete.sequenceFin, StateT.run_bind, StateT.run_pure, support_bind,
      Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hr
    obtain ⟨u, hu, v, hv, rfl⟩ := hr
    cases i using Fin.cases with
    | zero =>
      exact treeSim_sequenceFin_preserves_prop P (fun i => f i.succ) (fun i => preserve i.succ)
        u.2 (establish s u hu) v hv
    | succ i =>
      exact ih (fun i => f i.succ) (fun i => preserve i.succ) i establish u.2 v hv

/-- One live honest empty-opening entry installs the copy digest. All later
entries retain it, even when corrupt or inactive operators occur between them. -/
theorem TreeSimEmptyOpenNext.populated (D : C.Coalition)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C))
    (n : TreeSimEmptyOpenNext K D k₁ k₂ out₁ out₂)
    (active : ∃ i, i ∉ D.1 ∧ n.live i = true)
    (s : HashCache C × HiddenCache C)
    (r : (C.Party → Step C E RealSpec TreeOutput) × (HashCache C × HiddenCache C))
    (hr : r ∈ support ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run s)) :
    ∃ digest, r.2.1 (.copy []) = some digest := by
  unfold treeSimResumeAll at hr
  rw [free_sequenceFin, simulateQ_sequenceFin] at hr
  obtain ⟨i, hi, hl⟩ := active
  apply treeSim_sequenceFin_establishes (fun t => ∃ digest, t.1 (.copy []) = some digest)
    _ (fun j a b ha hb => ?_) i (fun a b hb => ?_) s r hr
  · obtain ⟨digest, cached⟩ := ha
    exact ⟨digest, (treeSim_stream_grows prims D _ a b hb) cached⟩
  · simp only [n.shape₂ i, if_neg hi, if_pos hl, treeSimResume, n.program₂ i hi hl] at hb
    obtain ⟨digest, cached, _⟩ := treeSim_emptyOpen_entry_populated prims K D
      (n.ctx₂ i) (n.v₂ i) (n.next₂ i) a b hb
    exact ⟨digest, cached⟩

/-- The entry coupling exports the common populated address whenever any
honest party is live. The all-stopped branch needs no hash-cache premise. -/
theorem TreeSimEmptyOpenNext.coupling_populated (D : C.Coalition) (δ : HiddenAddress C → Bit)
    (k₁ k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput)
    (out₁ out₂ : C.Party → Option (Shares C Bit × RunState C))
    (n : TreeSimEmptyOpenNext K D k₁ k₂ out₁ out₂)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (hc : TreeSimStreamRel δ a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll k₁ out₁)).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll k₂ out₂)).run b)
      (fun u z => (∃ ds, u.1 = treeSimEmptyOpenPartial K D n.live ds n.next₁ ∧
        z.1 = treeSimEmptyOpenPartial K D n.live ds n.next₂) ∧
        TreeSimStreamRel δ u.2 z.2 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2 ∧
        ((∃ i, i ∉ D.1 ∧ n.live i = true) →
          ∃ digest, u.2.1.1 (.copy []) = some digest ∧ z.2.1 (.copy []) = some digest)) := by
  apply relTriple_post_mono (treeSim_relTriple_support (n.coupling prims K D δ k₁ k₂ out₁ out₂ a b hc))
  intro u z hz
  obtain ⟨⟨shapes, hs, h₁, h₂⟩, _, hsz⟩ := hz
  refine ⟨shapes, hs, h₁, h₂, ?_⟩
  intro active
  obtain ⟨digest, cached⟩ := n.populated prims K D k₁ k₂ out₁ out₂ active b z hsz
  exact ⟨digest, by rw [hs.1]; exact cached, cached⟩

/-- Rerand entrants retain the aborts of previously stopped honest parties. -/
def treeSimPeerPartial {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (live : C.Party → Bool) (count : ℕ) (rnd : C.Party → PrssOutput C Bit)
    (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    C.Party → Step C E RealSpec α := fun i =>
  if live i then treeSimPeerWaiting K D ctx count rnd v st k i else .done none

theorem treeSim_peer_partial_view {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (live : C.Party → Bool) (count : ℕ) (rnd : C.Party → PrssOutput C Bit)
    (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    treeSimRoundView D (treeSimPeerPartial K D ctx live count rnd v st k) =
      fun c i => if live i then treeSimRoundView D (treeSimPeerWaiting K D ctx count rnd v st k) c i else none := by
  funext c i
  by_cases hl : live i = true
  · simp only [treeSimRoundView, treeSimPeerPartial, if_pos hl]
  · simp [treeSimRoundView, treeSimPeerPartial, hl, Step.outbox]

/-- The real peer exchange propagates a prior honest abort before running
any continuation, including when all remaining parties were ready for Rerand. -/
theorem treeSim_peer_partial_local {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (live : C.Party → Bool) (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (treeSimPeerPartial K D ctx live count rnd v st k) sent i = pure (.done none) := by
  by_cases hl : live i = true
  · by_cases hi : i ∈ D.1
    · simp only [roundLocal, treeSimPeerPartial, if_pos hl, treeSimPeerWaiting, if_pos hi]
    · have hab : anyAbort (fun j => if j ∈ D.1 then sent j i else
          (treeSimPeerPartial K D ctx live count rnd v st k j).delivered i) = true := by
        obtain ⟨j, hj, hjl⟩ := stopped
        unfold anyAbort
        rw [List.any_eq_true]
        refine ⟨j, by simp [Committee.parties], ?_⟩
        simp [hj, treeSimPeerPartial, hjl, Step.delivered, Msg.isAbort]
      simp only [roundLocal, treeSimPeerPartial, if_pos hl, treeSimPeerWaiting, if_neg hi, treeSimPeerStep]
      change advance (exchangeResume (G := RealSpec) _ (fun j => if j ∈ D.1 then sent j i else
        (treeSimPeerPartial K D ctx live count rnd v st k j).delivered i)) = _
      unfold exchangeResume
      unfold anyAbort at hab
      rw [if_pos hab]
      rfl
  · simp only [roundLocal, treeSimPeerPartial, if_neg hl]

/-- Prior aborts still expose the exact Rerand view to the rushing adversary. -/
theorem treeSim_peer_partial_factor {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (ctx : C.Party → Context C)
    (live : C.Party → Bool) (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true) (count : ℕ)
    (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit) (st : C.Party → RunState C)
    (k : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state (treeSimPeerPartial K D ctx live count rnd v st k) = (do
      let b ← worldRoles.adversary (A.round state
        (treeSimRoundView D (treeSimPeerPartial K D ctx live count rnd v st k)))
      pure (b.1, (fun _ => Step.done none), b.2)) := by
  rw [stepRound_real]
  change (do
    let b ← worldRoles.adversary (A.round state
      (treeSimRoundView D (treeSimPeerPartial K D ctx live count rnd v st k)))
    let next ← free (Concrete.sequenceFin (roundLocal D (treeSimPeerPartial K D ctx live count rnd v st k) b.2))
    pure (b.1, next, b.2)) = _
  apply bind_congr
  intro b
  rw [sequenceFin_congr_pure _ (fun _ => Step.done none)
    (treeSim_peer_partial_local K D ctx live stopped count rnd v st k b.2)]
  simp only [free_pure, pure_bind]

/-- Concrete Rerand boundary data. Mask balance proves equality of the
rushing views, while the actual peer outputs retain both saved histories. -/
structure TreeSimRerandData (D : C.Coalition) where
  δ : HiddenAddress C → Bit
  count : ℕ
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  self : ∀ i, i ∉ D.1 → (ctx₁ i).self = (ctx₂ i).self
  rnd₁ : C.Party → PrssOutput C Bit
  rnd₂ : C.Party → PrssOutput C Bit
  v₁ : C.Party → ℕ → Bit
  v₂ : C.Party → ℕ → Bit
  st₁ : C.Party → RunState C
  st₂ : C.Party → RunState C
  k₁ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput
  k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput
  masks : ∀ i, i ∉ D.1 →
    (rnd₂ i).1 = (rnd₁ i).1 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).1 ∧
    (rnd₂ i).2 = (rnd₁ i).2 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).2
  balance : ∀ i, i ∉ D.1 → KnownTo D.1 (K.filled (ctx₁ i).self) → ∀ g < count,
    reshareU K (ctx₁ i) (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).1
      (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).2 (v₂ i) g = v₁ i g

theorem TreeSimRerandData.view (D : C.Coalition) (d : TreeSimRerandData K D) :
    treeSimRoundView D (treeSimPeerWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁) =
      treeSimRoundView D (treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂) := by
  apply treeSim_peer_steps_view K D d.δ d.ctx₁ d.ctx₂ d.self 0 d.count d.v₁ d.v₂ d.st₁ d.st₂ d.k₁ d.k₂ d.balance
  intro i
  by_cases hi : i ∈ D.1
  · simp [treeSimPeerWaiting, hi]
  · simp only [if_neg hi]
    exact ⟨d.rnd₁ i, d.rnd₂ i, (d.masks i hi).1, (d.masks i hi).2,
      by simp [treeSimPeerWaiting, hi], by simp [treeSimPeerWaiting, hi]⟩

/-- Reachability after the actual common rushing call. These support facts
retain the relationship between the adversary state, cache and query log. -/
def TreeSimReplyReachable (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state₀ : A.State)
    (steps : C.Party → Step C E RealSpec TreeOutput)
    (initial₁ : TreeSimState C) (initial₂ : HashCache C × HiddenCache C)
    (state : A.State) (sent : C.Party → Mail C E)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) : Prop :=
  ((state, sent), a) ∈ support ((simulateQ (treeSimLoggedWorld prims D)
    (worldRoles.adversary (A.round state₀ (treeSimRoundView D steps)))).run initial₁) ∧
  ((state, sent), b) ∈ support ((simulateQ (streamWorld prims D)
    (worldRoles.adversary (A.round state₀ (treeSimRoundView D steps)))).run initial₂)

/-- At the actual Rerand-to-Coin boundary, only concrete resumed programs and
closure of the ceremony invariant remain obligations. -/
structure TreeSimRerandCoinClosure (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (d : TreeSimRerandData K D) (state₀ : A.State)
    (initial₁ : TreeSimState C) (initial₂ : HashCache C × HiddenCache C) where
  next : ∀ state sent a b,
      TreeSimReplyReachable prims D A state₀
        (treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂) initial₁ initial₂ state sent a b →
      TreeSimStreamRel d.δ a b → a.1.2 = initial₁.1.2 → b.2 = initial₂.2 →
      let out₁ := treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent
      let out₂ := treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent
      ∃ n : TreeSimCoinNext K D d.δ d.k₁ d.k₂ out₁ out₂,
      TreeSimFutureEmpty (n.ρ + 1) a.1.2 ∧
      ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll d.k₁ out₁)).run a),
      ∀ z ∈ support ((simulateQ (streamWorld prims D) (treeSimResumeAll d.k₂ out₂)).run b),
      ∀ rnd, TreeSimCacheFrame (n.ρ + 1) a.1.2 u.2.1.2 →
        TreeSimCacheFrame (n.ρ + 1) b.2 z.2.2 →
        TreeSimFutureEmpty (n.ρ + 2) u.2.1.2 → TreeSimFutureEmpty (n.ρ + 2) z.2.2 →
        TreeSimFutureZero (n.ρ + 2) d.δ →
        u.1 = treeSimCoinPartial K D n.live n.count rnd n.st₁ n.next₁ →
        z.1 = treeSimCoinPartial K D n.live n.count rnd n.st₂ n.next₂ → TreeSimStreamRel d.δ u.2 z.2 →
        Bad u.2 ∨ Inv ((state, u.1), u.2) ((state, z.1), z.2)

/-- If the check has no terms, Rerand resumes into the real empty opening.
The remaining obligation is deterministic closure of the ceremony invariant. -/
structure TreeSimRerandEmptyClosure (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (d : TreeSimRerandData K D) (state₀ : A.State)
    (initial₁ : TreeSimState C) (initial₂ : HashCache C × HiddenCache C) where
  next : ∀ state sent a b,
      TreeSimReplyReachable prims D A state₀
        (treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂) initial₁ initial₂ state sent a b →
      TreeSimStreamRel d.δ a b → a.1.2 = initial₁.1.2 → b.2 = initial₂.2 →
      let out₁ := treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent
      let out₂ := treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent
      ∃ n : TreeSimEmptyOpenNext K D d.k₁ d.k₂ out₁ out₂,
      ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll d.k₁ out₁)).run a),
      ∀ z ∈ support ((simulateQ (streamWorld prims D) (treeSimResumeAll d.k₂ out₂)).run b),
      ∀ ds, u.1 = treeSimEmptyOpenPartial K D n.live ds n.next₁ →
        z.1 = treeSimEmptyOpenPartial K D n.live ds n.next₂ → TreeSimStreamRel d.δ u.2 z.2 →
        u.2.1.2 = a.1.2 → z.2.2 = b.2 →
        (¬ AllDone D u.1 → ∃ digest, u.2.1.1 (.copy []) = some digest ∧ z.2.1 (.copy []) = some digest) →
        Bad u.2 ∨ Inv ((state, u.1), u.2) ((state, z.1), z.2)

/-- Partial Rerand retains equal corrupt views for any common live set. -/
theorem TreeSimRerandData.partial_view (D : C.Coalition) (d : TreeSimRerandData K D)
    (live : C.Party → Bool) :
    treeSimRoundView D (treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁) =
      treeSimRoundView D (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) := by
  rw [treeSim_peer_partial_view, treeSim_peer_partial_view, d.view K D]

/-- Rerand resumes into Coin or an empty opening, or propagates a prior abort. -/
def TreeSimRerandBoundary (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ d : TreeSimRerandData K D, a.1.1 = b.1.1 ∧ TreeSimStreamRel d.δ a.2 b.2 ∧
    ((a.1.2 = treeSimPeerWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
      b.1.2 = treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ ∧
      (Nonempty (TreeSimRerandCoinClosure prims K D A Bad Inv d a.1.1 a.2 b.2) ∨
       Nonempty (TreeSimRerandEmptyClosure prims K D A Bad Inv d a.1.1 a.2 b.2))) ∨
    ∃ live, (∃ j, j ∉ D.1 ∧ live j ≠ true) ∧
      a.1.2 = treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
      b.1.2 = treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ ∧
      (∀ state sent u z, TreeSimReplyReachable prims D A a.1.1
          (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) a.2 b.2 state sent u z →
        TreeSimStreamRel d.δ u z → u.1.2 = a.2.1.2 → z.2 = b.2.2 →
        Bad u ∨ Inv ((state, fun _ => .done none), u) ((state, fun _ => .done none), z)))

/-- Rerand's peer exchange and its actual successor are coupled in a single
real round, in the order used by `runJobs`. The certificates contain no coupling. -/
theorem treeSim_rerand_preserves (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (stage : TreeSimConfig A (TreeSimState C) → TreeSimStage)
    (identify : ∀ a b, stage a = .rerand → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
      TreeSimRerandBoundary prims K D A Bad Inv a b) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A Bad Inv stage .rerand := by
  intro a b hg hinv hbad hdone
  obtain ⟨d, had, hc, boundary⟩ := identify a b hg hinv hbad hdone
  change RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2) _
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rcases boundary with ⟨ha, hb, close⟩ | ⟨live, stopped, ha, hb, close⟩
  · rw [ha, hb, ← had, treeSim_peer_resume_factor, treeSim_peer_resume_factor, d.view K D]
    simp only [simulateQ_bind, StateT.run_bind]
    apply relTriple_bind (treeSim_relTriple_support
      (treeSim_local_streamRel_fixed prims D d.δ _ a.2 b.2 hc))
    intro r₁ r₂ hr
    obtain ⟨hr, hs₁, hs₂⟩ := hr
    have reach : TreeSimReplyReachable prims D A a.1.1
        (treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂) a.2 b.2 r₂.1.1 r₂.1.2 r₁.2 r₂.2 := by
      refine ⟨?_, hs₂⟩
      change (r₂.1, r₁.2) ∈ _
      rw [← hr.1]
      exact hs₁
    rw [hr.1]
    rcases close with close | close
    · obtain ⟨close⟩ := close
      obtain ⟨n, fresh, accepts⟩ := close.next r₂.1.1 r₂.1.2 r₁.2 r₂.2 reach hr.2.1 hr.2.2.1 hr.2.2.2
      apply relTriple_bind (treeSim_relTriple_support
        (n.coupling_fresh prims K D d.δ d.k₁ d.k₂ _ _ r₁.2 r₂.2 hr.2.1 fresh))
      intro u z hz
      obtain ⟨⟨f₁, f₂, e₁, e₂, zero, ⟨rnd, hu, hz⟩, hc⟩, hsu, hsz⟩ := hz
      simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (accepts u hsu z hsz rnd f₁ f₂ e₁ e₂ zero hu hz hc)
    · obtain ⟨close⟩ := close
      obtain ⟨n, accepts⟩ := close.next r₂.1.1 r₂.1.2 r₁.2 r₂.2 reach hr.2.1 hr.2.2.1 hr.2.2.2
      apply relTriple_bind (treeSim_relTriple_support
        (n.coupling_populated prims K D d.δ d.k₁ d.k₂ _ _ r₁.2 r₂.2 hr.2.1))
      intro u z hz
      obtain ⟨⟨⟨ds, hu, hz⟩, hc, h₁, h₂, populated⟩, hsu, hsz⟩ := hz
      have cached : ¬ AllDone D u.1 →
          ∃ digest, u.2.1.1 (.copy []) = some digest ∧ z.2.1 (.copy []) = some digest := by
        intro hdone
        apply populated
        apply treeSim_emptyOpenPartial_active K D n.live ds n.next₁
        simpa only [← hu] using hdone
      simp only [simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure (accepts u hsu z hsz ds hu hz hc h₁ h₂ cached)
  · rw [ha, hb, ← had, treeSim_peer_partial_factor K D A _ _ live stopped,
      treeSim_peer_partial_factor K D A _ _ live stopped, d.partial_view K D live]
    simp only [simulateQ_bind, StateT.run_bind]
    apply relTriple_bind (treeSim_relTriple_support
      (treeSim_local_streamRel_fixed prims D d.δ _ a.2 b.2 hc))
    intro r₁ r₂ hr
    obtain ⟨hr, hs₁, hs₂⟩ := hr
    have reach : TreeSimReplyReachable prims D A a.1.1
        (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) a.2 b.2 r₂.1.1 r₂.1.2 r₁.2 r₂.2 := by
      refine ⟨?_, hs₂⟩
      change (r₂.1, r₁.2) ∈ _
      rw [← hr.1]
      exact hs₁
    simp only [simulateQ_pure, StateT.run_pure]
    apply relTriple_pure_pure
    rw [hr.1]
    exact close r₂.1.1 r₂.1.2 r₁.2 r₂.2 reach hr.2.1 hr.2.2.1 hr.2.2.2

/-- Saved continuations do not affect the messages already exposed by a
peer exchange, including the delivered abort frames of corrupt placeholders. -/
theorem treeSim_peer_delivered_cont {α β : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (count : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k₁ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec β) (i : C.Party) :
    (treeSimPeerWaiting K D ctx count rnd v st k₁ i).delivered =
      (treeSimPeerWaiting K D ctx count rnd v st k₂ i).delivered := by
  by_cases hi : i ∈ D.1 <;> simp [treeSimPeerWaiting, treeSimPeerStep, Step.delivered, hi]

/-- The actual optional peer return, including its recorded history, is
independent of the continuation which consumes it. -/
theorem treeSim_peer_outputs_cont {α β : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (count : ℕ) (rnd : C.Party → PrssOutput C Bit) (v : C.Party → ℕ → Bit)
    (st : C.Party → RunState C)
    (k₁ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec α)
    (k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec β) (sent : C.Party → Mail C E) :
    treeSimPeerOutputs K D ctx count rnd v st k₁ sent = treeSimPeerOutputs K D ctx count rnd v st k₂ sent := by
  funext i
  simp only [treeSimPeerOutputs, treeSim_peer_delivered_cont K D ctx count rnd v st k₁ k₂]

/-- Peer boundary witnesses with the GS20 zero-w translation and the incoming
history relation. Corrupt-visible message balance follows from this block. -/
structure TreeSimPeerData (D : C.Coalition) where
  δ : HiddenAddress C → Bit
  count : ℕ
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  rnd₁ : C.Party → PrssOutput C Bit
  rnd₂ : C.Party → PrssOutput C Bit
  v₁ : C.Party → ℕ → Bit
  v₂ : C.Party → ℕ → Bit
  st₁ : C.Party → RunState C
  st₂ : C.Party → RunState C
  k₁ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput
  k₂ : C.Party → Shares C Bit × RunState C → PartyM C E RealSpec TreeOutput
  masks : ∀ i, i ∉ D.1 →
    (rnd₂ i).1 = (rnd₁ i).1 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).1 ∧
    (rnd₂ i).2 = (rnd₁ i).2 + (treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count).2
  T₀ : C.Term
  pivotParty : C.Party
  pivot : Pivot K D T₀ pivotParty
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  history : List Bit
  states : ∀ i, i ∉ D.1 → TreeSimRunStateRel D i history (st₁ i) (st₂ i)
  block : ∀ i, i ∉ D.1 → treeSimPrssShift δ (ctx₁ i) (st₁ i).label 0 count =
    frandShare D count 0 0 (termShift K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin count → Bit))
      (pairShift pivotParty (pairDelta K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin count → Bit))) i

/-- The restricted GS20 block equation already proves message balance;
the reachable peer boundary need not assume that algebra separately. -/
def TreeSimPeerData.toTreeSimRerandData (D : C.Coalition) (d : TreeSimPeerData K D) :
    TreeSimRerandData K D where
  δ := d.δ
  count := d.count
  ctx₁ := d.ctx₁
  ctx₂ := d.ctx₂
  self i hi := (d.self₁ i hi).trans (d.self₂ i hi).symm
  rnd₁ := d.rnd₁
  rnd₂ := d.rnd₂
  v₁ := d.v₁
  v₂ := d.v₂
  st₁ := d.st₁
  st₂ := d.st₂
  k₁ := d.k₁
  k₂ := d.k₂
  masks := d.masks
  balance := by
    intro i hi hk g hg
    have hself : (d.ctx₁ i).self ∉ D.1 := by simpa only [d.self₁ i hi] using hi
    have h := treeSim_peerShift_balance_inputs K D d.pivot (d.ctx₁ i) hself hk
      (d.st₁ i).label 0 d.count d.v₁ d.v₂ 0 g hg
    unfold treeSimPeerShift at h
    rw [treeSim_prssShift_block D (d.ctx₁ i) hself, d.self₁ i hi] at h
    rw [d.block i hi]
    exact h

theorem TreeSimPeerData.view (D : C.Coalition) (d : TreeSimPeerData K D) :
    treeSimRoundView D (treeSimPeerWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁) =
      treeSimRoundView D (treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂) :=
  (d.toTreeSimRerandData K D).view K D

theorem TreeSimPeerData.partial_view (D : C.Coalition) (d : TreeSimPeerData K D)
    (live : C.Party → Bool) :
    treeSimRoundView D (treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁) =
      treeSimRoundView D (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) :=
  (d.toTreeSimRerandData K D).partial_view K D live

/-- Successful peer outputs retain the T₀ sharing shift, exact history shift,
label increments and cross-world tag equality. Aborts use `Option.Rel`. -/
def TreeSimPeerExitRel (D : C.Coalition) (d : TreeSimPeerData K D)
    (i : C.Party) (x y : Shares C Bit × RunState C) : Prop :=
  let difference := fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g
  y.1 = treeSimHeldShift D i d.count difference x.1 ∧
    TreeSimRunStateRel D i (treeSimHistoryAppend K d.T₀ d.count d.history difference) x.2 y.2 ∧
    x.2.label = (d.st₁ i).label + 1 ∧ y.2.label = (d.st₂ i).label + 1

/-- The real optional outputs satisfy the peer exit relation for every
common malicious response, before either ceremony continuation executes. -/
theorem TreeSimPeerData.outputs (D : C.Coalition) (d : TreeSimPeerData K D)
    (sent : C.Party → Mail C E) (i : C.Party) :
    Option.Rel (TreeSimPeerExitRel K D d i)
      (treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent i)
      (treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent i) := by
  let s₁ : C.Party → Step C E RealSpec (Shares C Bit × RunState C) := treeSimPeerWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ (fun _ => pure)
  let s₂ : C.Party → Step C E RealSpec (Shares C Bit × RunState C) := treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ (fun _ => pure)
  let n₁ : C.Party → Step C E RealSpec (Shares C Bit × RunState C) := fun j => Step.done (treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ (fun _ => pure) sent j)
  let n₂ : C.Party → Step C E RealSpec (Shares C Bit × RunState C) := fun j => Step.done (treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ (fun _ => pure) sent j)
  have hs : TreeSimPeerStepsRel K D d.δ d.ctx₁ d.ctx₂ 0 d.count d.v₁ d.v₂ d.st₁ d.st₂
      (fun _ => pure) (fun _ => pure) s₁ s₂ := by
    intro j
    by_cases hj : j ∈ D.1
    · simp [TreeSimPeerStepsRel, s₁, s₂, treeSimPeerWaiting, hj]
    · simp only [TreeSimPeerStepsRel, if_neg hj]
      exact ⟨d.rnd₁ j, d.rnd₂ j, (d.masks j hj).1, (d.masks j hj).2,
        by simp [s₁, treeSimPeerWaiting, hj], by simp [s₂, treeSimPeerWaiting, hj]⟩
  have hn : TreeSimPeerAfterRel K D d.δ d.ctx₁ d.ctx₂ 0 d.count d.v₁ d.v₂ d.st₁ d.st₂ s₁ s₂ sent n₁ n₂ := by
    intro j
    by_cases hj : j ∈ D.1
    · simp [TreeSimPeerAfterAt, n₁, n₂, treeSimPeerOutputs, hj]
    · simp only [TreeSimPeerAfterAt, if_neg hj]
      exact ⟨d.rnd₁ j, d.rnd₂ j, (d.masks j hj).1, (d.masks j hj).2,
        by simp [s₁, treeSimPeerWaiting, hj], by simp [s₂, treeSimPeerWaiting, hj],
        by simp [n₁, treeSimPeerOutputs, hj, s₁], by simp [n₂, treeSimPeerOutputs, hj, s₂]⟩
  have shares := treeSim_peer_after_shares K D d.pivot d.δ d.ctx₁ d.ctx₂ d.self₁ d.self₂
    0 d.count d.v₁ d.v₂ d.st₁ d.st₂ d.block s₁ s₂ n₁ n₂ hs sent hn
  have states := treeSim_peer_after_states K D d.T₀ d.pivot.lacked d.δ d.ctx₁ d.ctx₂ d.self₁ d.self₂
    0 d.count d.v₁ d.v₂ d.st₁ d.st₂ d.history _ d.states s₁ s₂ n₁ n₂ hs sent hn shares i
  have ho := shares i
  simp only [TreeSimPeerOutputShift, n₁, n₂, Step.output] at ho states
  rw [treeSim_peer_outputs_cont K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ (fun _ => pure),
    treeSim_peer_outputs_cont K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ (fun _ => pure)]
  have labels : ∀ ctx rnd v st (j : C.Party) x,
      treeSimPeerOutputs K D ctx d.count rnd v st (fun _ => pure) sent j = some x → x.2.label = (st j).label + 1 := by
    intro ctx rnd v st j x hx
    unfold treeSimPeerOutputs at hx
    split_ifs at hx with hj
    unfold treeSimPeerReturn at hx
    split_ifs at hx with hab
    cases hx
    rfl
  generalize h₁ : treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ (fun _ => pure) sent i = left at ho states ⊢
  generalize h₂ : treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ (fun _ => pure) sent i = right at ho states ⊢
  cases ho with
  | none => exact Option.Rel.none
  | some hshift =>
    cases states with
    | some hstate =>
      exact Option.Rel.some ⟨hshift, hstate, labels _ _ _ _ i _ h₁, labels _ _ _ _ i _ h₂⟩

/-- Only the actual successful peer outputs require continuation couplings.
The relation is chosen after the whole output vector and the rushing reply. -/
structure TreeSimPeerLocalClosure (D : C.Coalition) (d : TreeSimPeerData K D)
    (sent : C.Party → Mail C E) where
  J : TreeSimState C → (HashCache C × HiddenCache C) → Prop
  Q : C.Party → Step C E RealSpec TreeOutput → Step C E RealSpec TreeOutput → Prop
  abort : ∀ i, Q i (.done none) (.done none)
  continues : ∀ i x y,
    treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent i = some x →
    treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent i = some y →
    TreeSimPeerExitRel K D d i x y → ∀ a b, J a b →
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (advance (d.k₁ i x).run))).run a)
      ((simulateQ (streamWorld prims D) (free (advance (d.k₂ i y).run))).run b)
      (fun u z => Q i u.1 z.1 ∧ J u.2 z.2)

/-- Resume the real peer continuations in the driver's operator order. -/
theorem TreeSimPeerLocalClosure.resume (D : C.Coalition) (d : TreeSimPeerData K D)
    (sent : C.Party → Mail C E) (close : TreeSimPeerLocalClosure prims K D d sent)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : close.J a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll d.k₁
        (treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent))).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll d.k₂
        (treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent))).run b)
      (fun u z => (∀ i, close.Q i (u.1 i) (z.1 i)) ∧ close.J u.2 z.2) := by
  apply treeSim_resumeAll_rel prims D d.k₁ d.k₂ _ _ close.J close.Q _ a b h
  intro i u z hj
  have ho := d.outputs K D sent i
  generalize h₁ : treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent i = left at ho ⊢
  generalize h₂ : treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent i = right at ho ⊢
  cases ho with
  | none =>
    simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨close.abort i, hj⟩
  | some hexit => exact close.continues i _ _ h₁ h₂ hexit u z hj

/-- The remaining peer obligations concern local saved continuations and
closure of the ceremony invariant, at supported replies and resumes. -/
structure TreeSimPeerClosure (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (d : TreeSimPeerData K D) (state₀ : A.State)
    (initial₁ : TreeSimState C) (initial₂ : HashCache C × HiddenCache C) where
  next : ∀ state sent a b,
    TreeSimReplyReachable prims D A state₀
      (treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂) initial₁ initial₂ state sent a b →
    TreeSimStreamRel d.δ a b → a.1.2 = initial₁.1.2 → b.2 = initial₂.2 →
    ∃ close : TreeSimPeerLocalClosure prims K D d sent, close.J a b ∧
      ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll d.k₁
          (treeSimPeerOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent))).run a),
      ∀ z ∈ support ((simulateQ (streamWorld prims D) (treeSimResumeAll d.k₂
          (treeSimPeerOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent))).run b),
      (∀ i, close.Q i (u.1 i) (z.1 i)) → close.J u.2 z.2 →
      Bad u.2 ∨ Inv ((state, u.1), u.2) ((state, z.1), z.2)

/-- Actual peer waiting states, local continuation certificates and prior aborts. -/
def TreeSimPeerBoundary (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  (∃ d : TreeSimPeerData K D, a.1.1 = b.1.1 ∧ TreeSimStreamRel d.δ a.2 b.2 ∧
      a.1.2 = treeSimPeerWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
      b.1.2 = treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ ∧
      Nonempty (TreeSimPeerClosure prims K D A Bad Inv d a.1.1 a.2 b.2)) ∨
  ∃ d : TreeSimRerandData K D, a.1.1 = b.1.1 ∧ TreeSimStreamRel d.δ a.2 b.2 ∧
    ∃ live, (∃ j, j ∉ D.1 ∧ live j ≠ true) ∧
      a.1.2 = treeSimPeerPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
      b.1.2 = treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ ∧
      (∀ state sent u z, TreeSimReplyReachable prims D A a.1.1
          (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) a.2 b.2 state sent u z →
        TreeSimStreamRel d.δ u z → u.1.2 = a.2.1.2 → z.2 = b.2.2 →
        Bad u ∨ Inv ((state, fun _ => .done none), u) ((state, fun _ => .done none), z))

/-- The real peer exchange couples messages, aborts, T₀ output shifts and
ordered continuation execution, conditional on reachable boundaries, local
continuation couplings and invariant closure. -/
theorem treeSim_peer_preserves (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (stage : TreeSimConfig A (TreeSimState C) → TreeSimStage)
    (identify : ∀ a b, stage a = .reshare → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
      TreeSimPeerBoundary prims K D A Bad Inv a b) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A Bad Inv stage .reshare := by
  intro a b hg hinv hbad hdone
  have boundary := identify a b hg hinv hbad hdone
  change RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2) _
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rcases boundary with ⟨d, had, hc, ha, hb, close⟩ | ⟨d, had, hc, live, stopped, ha, hb, close⟩
  · rw [ha, hb, ← had, treeSim_peer_resume_factor, treeSim_peer_resume_factor, d.view K D]
    simp only [simulateQ_bind, StateT.run_bind]
    apply relTriple_bind (treeSim_relTriple_support
      (treeSim_local_streamRel_fixed prims D d.δ _ a.2 b.2 hc))
    intro r₁ r₂ hr
    obtain ⟨hr, hs₁, hs₂⟩ := hr
    have reach : TreeSimReplyReachable prims D A a.1.1
        (treeSimPeerWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂) a.2 b.2 r₂.1.1 r₂.1.2 r₁.2 r₂.2 := by
      refine ⟨?_, hs₂⟩
      change (r₂.1, r₁.2) ∈ _
      rw [← hr.1]
      exact hs₁
    rw [hr.1]
    obtain ⟨close⟩ := close
    obtain ⟨localClose, hj, accepts⟩ := close.next r₂.1.1 r₂.1.2 r₁.2 r₂.2 reach hr.2.1 hr.2.2.1 hr.2.2.2
    apply relTriple_bind (treeSim_relTriple_support
      (localClose.resume prims K D d r₂.1.2 r₁.2 r₂.2 hj))
    intro u z hz
    obtain ⟨⟨hq, hj⟩, hsu, hsz⟩ := hz
    simp only [simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure (accepts u hsu z hsz hq hj)
  · rw [ha, hb, ← had, treeSim_peer_partial_factor K D A _ _ live stopped,
      treeSim_peer_partial_factor K D A _ _ live stopped, d.partial_view K D live]
    simp only [simulateQ_bind, StateT.run_bind]
    apply relTriple_bind (treeSim_relTriple_support
      (treeSim_local_streamRel_fixed prims D d.δ _ a.2 b.2 hc))
    intro r₁ r₂ hr
    obtain ⟨hr, hs₁, hs₂⟩ := hr
    have reach : TreeSimReplyReachable prims D A a.1.1
        (treeSimPeerPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) a.2 b.2 r₂.1.1 r₂.1.2 r₁.2 r₂.2 := by
      refine ⟨?_, hs₂⟩
      change (r₂.1, r₁.2) ∈ _
      rw [← hr.1]
      exact hs₁
    simp only [simulateQ_pure, StateT.run_pure]
    apply relTriple_pure_pure
    rw [hr.1]
    exact close r₂.1.1 r₂.1.2 r₁.2 r₂.2 reach hr.2.1 hr.2.2.1 hr.2.2.2

/-! The actual field peer exchange used by ExtendMult. Its encoded history
is retained exactly; no linearity of `Constants.encode` is assumed. The round
induction below derives this stage from concrete boundaries and local saved
continuations. Realizing the additive field masks from the actual PRSS draws,
identifying reachable programs and closing the ceremony invariant remain open.
The existing equal-output field PRSS coupling does not establish the required
shifted masks. -/

theorem treeSim_fieldTermVal_pivot (D : C.Coalition) {T₀ : C.Term} {p : C.Party}
    (hp : Pivot K D T₀ p) (count : ℕ) (v : C.Party → ℕ → E)
    (i : C.Party) (T : C.Term) (g : ℕ) (hg : g < count) :
    termVal K D (elementCodec K) 0 0
      (termShift K D T₀ p v (0 : C.Term → Fin count → E))
      (pairShift p (pairDelta K D T₀ p v (0 : C.Term → Fin count → E)))
      v (fun _ _ => none) i T g =
      if T = T₀ then ∑ j ∈ Finset.univ.filter (· ∉ D.1), v j g else 0 := by
  haveI : CharP E 2 := charTwo
  have hzero : ∀ i T, termVal K D (elementCodec K) (c := count) 0 0 0 0
      (fun _ _ => 0) (fun _ _ => none) i T g = 0 := by
    intro i T
    simp [termVal, uVal, randVal, pairVal, elementCodec, Msg.elementAt]
  have hother : ∀ T, T ≠ T₀ → termVal K D (elementCodec K) 0 0
      (termShift K D T₀ p v (0 : C.Term → Fin count → E))
      (pairShift p (pairDelta K D T₀ p v (0 : C.Term → Fin count → E)))
      v (fun _ _ => none) i T g = 0 := by
    intro T hT
    have h := termVal_shift K D (elementCodec K) 0 0 0 0 hp v
      (0 : C.Term → Fin count → E) (fun _ _ => none) i T hT g hg
    simpa only [zero_add, hzero, Pi.zero_apply, ite_self, add_zero] using h
  by_cases hT : T = T₀
  · subst T
    rw [if_pos rfl]
    have hsum := sum_termVal K D (elementCodec K) 0 0
      (termShift K D T₀ p v (0 : C.Term → Fin count → E))
      (pairShift p (pairDelta K D T₀ p v (0 : C.Term → Fin count → E)))
      v (fun _ _ => none) (fun _ => i) g
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ T₀)] at hsum
    simp only [Finset.sum_eq_zero (fun T hT => hother T (Finset.ne_of_mem_erase hT)), add_zero] at hsum
    simpa [advVal, elementCodec, Msg.elementAt] using hsum
  · rw [if_neg hT]
    exact hother T hT

/-- The value of a peer term before restricting it to its honest holders. The
base masks may be arbitrary; no independence or consistency assumption is used. -/
def treeSimFieldPeerValue (D : C.Coalition) (ctx : C.Party → Context C)
    (rnd : C.Party → PrssOutput C E) (v : C.Party → ℕ → E)
    (sent : C.Party → Mail C E) (i : C.Party) (T : C.Term) (g : ℕ) : E :=
  if T ∈ filledTerms K then
    ∑ j ∈ Finset.univ.filter (K.filled · = T),
      if j ∈ D.1 then Msg.elementAt (sent j i) g else reshareU K (ctx j) (rnd j).1 (rnd j).2 (v j) g
  else (rnd i).1 T g

/-- Normalize the actual peer inbox, with arbitrary honest masks and arbitrary
malicious messages, to its per-term value. -/
theorem treeSim_fieldReshareZ_value (D : C.Coalition) (ctx : C.Party → Context C)
    (self : ∀ i, i ∉ D.1 → (ctx i).self = i)
    (rnd : C.Party → PrssOutput C E) (v : C.Party → ℕ → E) (count : ℕ)
    (sent : C.Party → Mail C E) (i : C.Party) (hi : i ∉ D.1) (T : C.Term) (g : ℕ) :
    reshareZ K (ctx i) (elementCodec K) (rnd i).1 (rnd i).2 (v i) count
      (fun j => if j ∈ D.1 then sent j i else
        reshareOut K (ctx j) (elementCodec K) (rnd j).1 (rnd j).2 (v j) count i) T g =
      if i ∉ C.holders T ∨ count ≤ g then 0 else treeSimFieldPeerValue K D ctx rnd v sent i T g := by
  haveI : CharP E 2 := charTwo
  unfold reshareZ treeSimFieldPeerValue
  rw [self i hi]
  split_ifs with hbound hfilled
  · rfl
  · push Not at hbound
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjT := (Finset.mem_filter.mp hj).2
    by_cases hji : j = i
    · subst j
      simp [hi]
    · simp only [if_neg hji]
      by_cases hjD : j ∈ D.1
      · simp [hjD, elementCodec]
      · simp only [if_neg hjD, reshareOut, self j hjD]
        rw [if_pos ⟨Ne.symm hji, hjT ▸ hbound.1⟩]
        exact vector_getD count _ g hbound.2
  · rfl

/-- Translating the masks changes a peer term by the corresponding zero-base
execution. Characteristic two fixes the sign of the input difference. Corrupt
messages are unchanged, including malformed and recipient-specific ones. -/
theorem treeSim_fieldPeer_value_shift (D : C.Coalition) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (count : ℕ) (dt : C.Term → Fin count → E) (dp : C.Pair → Fin count → E)
    (rnd₁ rnd₂ : C.Party → PrssOutput C E)
    (masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0 dt dp i)
    (v₁ v₂ : C.Party → ℕ → E) (sent : C.Party → Mail C E)
    (i : C.Party) (hi : i ∉ D.1) (T : C.Term) (held : i ∈ C.holders T)
    (g : ℕ) (hg : g < count) :
    treeSimFieldPeerValue K D ctx₂ rnd₂ v₂ sent i T g = treeSimFieldPeerValue K D ctx₁ rnd₁ v₁ sent i T g +
      termVal K D (elementCodec K) 0 0 dt dp (v₁ - v₂) (fun _ _ => none) i T g := by
  haveI : CharP E 2 := charTwo
  have hu : ∀ j, j ∉ D.1 → reshareU K (ctx₂ j) (rnd₂ j).1 (rnd₂ j).2 (v₂ j) g =
      reshareU K (ctx₁ j) (rnd₁ j).1 (rnd₁ j).2 (v₁ j) g +
        uVal K D 0 0 dt dp (v₁ - v₂) j g := by
    intro j hj
    have he := reshareU_frandShare K D (R := E) 0 0 dt dp (v₁ - v₂) j g
    rw [masks j hj]
    simp only [reshareU, self₁ j hj, self₂ j hj, localContext, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib] at he ⊢
    have htwo := CharTwo.add_self_eq_zero (v₁ j g - v₂ j g)
    linear_combination he - htwo
  unfold treeSimFieldPeerValue termVal
  by_cases hf : T ∈ filledTerms K
  · simp only [if_pos hf, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    by_cases hc : j ∈ D.1
    · simp [hc, elementCodec, Msg.elementAt]
    · simp only [if_neg hc]
      exact hu j hc
  · simp only [if_neg hf, masks i hi, Prod.fst_add, Pi.add_apply]
    rw [frandShare_fst D (0 : Shares C E) 0 dt dp i T g held]

/-- The `T₀` shift on an operator's stored sharing, respecting held terms and
the gadget length. Unlike an opening, an internal sharing stores zero elsewhere. -/
def treeSimFieldHeldShift (D : C.Coalition) (i : C.Party) (count : ℕ)
    (difference : ℕ → E) (v : Shares C E) : Shares C E := fun T g =>
  v T g + if i ∈ C.holders T ∧ g < count ∧ lackedTerm D.1 = some T then difference g else 0

/-- The actual peer outputs differ only at `T₀`, for arbitrary base masks and
arbitrary common malicious messages. This holds before inspecting the abort bit. -/
theorem treeSim_fieldReshareZ_pivot (D : C.Coalition) {T₀ : C.Term} {p : C.Party}
    (hp : Pivot K D T₀ p) (ctx₁ ctx₂ : C.Party → Context C)
    (self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i)
    (self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i)
    (count : ℕ) (v₁ v₂ : C.Party → ℕ → E)
    (rnd₁ rnd₂ : C.Party → PrssOutput C E)
    (masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0
      (termShift K D T₀ p (v₁ - v₂) (0 : C.Term → Fin count → E))
      (pairShift p (pairDelta K D T₀ p (v₁ - v₂) (0 : C.Term → Fin count → E))) i)
    (sent : C.Party → Mail C E) (i : C.Party) (hi : i ∉ D.1) :
    reshareZ K (ctx₂ i) (elementCodec K) (rnd₂ i).1 (rnd₂ i).2 (v₂ i) count
      (fun j => if j ∈ D.1 then sent j i else
        reshareOut K (ctx₂ j) (elementCodec K) (rnd₂ j).1 (rnd₂ j).2 (v₂ j) count i) =
    treeSimFieldHeldShift D i count (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (v₁ - v₂) j g)
      (reshareZ K (ctx₁ i) (elementCodec K) (rnd₁ i).1 (rnd₁ i).2 (v₁ i) count
        (fun j => if j ∈ D.1 then sent j i else
          reshareOut K (ctx₁ j) (elementCodec K) (rnd₁ j).1 (rnd₁ j).2 (v₁ j) count i)) := by
  haveI : CharP E 2 := charTwo
  funext T g
  rw [treeSimFieldHeldShift, treeSim_fieldReshareZ_value K D ctx₁ self₁ (hi := hi),
    treeSim_fieldReshareZ_value K D ctx₂ self₂ (hi := hi)]
  by_cases hb : i ∉ C.holders T ∨ count ≤ g
  · simp only [if_pos hb]
    have hn : ¬ (i ∈ C.holders T ∧ g < count ∧ lackedTerm D.1 = some T) := by
      intro h
      rcases hb with hb | hb
      · exact hb h.1
      · omega
    simp [hn]
  · have held : i ∈ C.holders T := by tauto
    have hg : g < count := by omega
    simp only [if_neg hb]
    rw [treeSim_fieldPeer_value_shift K D ctx₁ ctx₂ self₁ self₂ count _ _ rnd₁ rnd₂ masks
      v₁ v₂ sent i hi T held g hg, treeSim_fieldTermVal_pivot K D hp count (v₁ - v₂) i T g hg]
    simp [held, hg, hp.lacked, eq_comm]

def treeSimExtendMultReturn (ctx : Context C) (rnd : PrssOutput C E) (v : ℕ → E)
    (count : ℕ) (st : RunState C) (inbox : Mail C E) : Option (Shares C E × RunState C) :=
  if anyAbort inbox then none else
    let out := reshareZ K ctx (elementCodec K) rnd.1 rnd.2 v count inbox
    some (out, ⟨recordPeer K (elementCodec K) ctx.self st.history out count, st.label + 1, st.tag⟩)

/-- Suspended peer exchanges, over the check field. -/
def treeSimExtendMultWaiting {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (count : ℕ) (rnd : C.Party → PrssOutput C E) (v : C.Party → ℕ → E)
    (st : C.Party → RunState C) (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α) :
    C.Party → Step C E RealSpec α := fun i =>
  if i ∈ D.1 then .done none else treeSimPeerStep K (ctx i) (elementCodec K) (rnd i) (v i) count (st i) (k i)

/-- Actual optional peer outputs, with the history and label recorded before
entering the next check gadget. -/
def treeSimExtendMultOutputs {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (count : ℕ) (rnd : C.Party → PrssOutput C E) (v : C.Party → ℕ → E)
    (st : C.Party → RunState C) (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) : C.Party → Option (Shares C E × RunState C) := fun i =>
  if i ∈ D.1 then none else treeSimExtendMultReturn K (ctx i) (rnd i) (v i) count (st i)
    (fun j => if j ∈ D.1 then sent j i else (treeSimExtendMultWaiting K D ctx count rnd v st k j).delivered i)

theorem treeSim_extendMult_resume_local {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (count : ℕ) (rnd : C.Party → PrssOutput C E) (v : C.Party → ℕ → E)
    (st : C.Party → RunState C) (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (treeSimExtendMultWaiting K D ctx count rnd v st k) sent i =
      treeSimResume (k i) (treeSimExtendMultOutputs K D ctx count rnd v st k sent i) := by
  by_cases hi : i ∈ D.1
  · simp [roundLocal, treeSimExtendMultWaiting, treeSimExtendMultOutputs, hi, treeSimResume]
  · simp only [roundLocal, treeSimExtendMultWaiting, if_neg hi, treeSimPeerStep, treeSimExtendMultOutputs]
    unfold treeSimExtendMultReturn exchangeResume anyAbort
    dsimp only
    split_ifs <;> rfl

/-- One real peer round, followed by its actual optional continuations. -/
theorem treeSim_extendMult_resume_factor {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (ctx : C.Party → Context C)
    (count : ℕ) (rnd : C.Party → PrssOutput C E) (v : C.Party → ℕ → E)
    (st : C.Party → RunState C) (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state (treeSimExtendMultWaiting K D ctx count rnd v st k) = (do
      let b ← worldRoles.adversary (A.round state (treeSimRoundView D (treeSimExtendMultWaiting K D ctx count rnd v st k)))
      let next ← treeSimResumeAll k (treeSimExtendMultOutputs K D ctx count rnd v st k b.2)
      pure (b.1, next, b.2)) := by
  rw [stepRound_real]
  change (do
    let b ← worldRoles.adversary (A.round state (treeSimRoundView D (treeSimExtendMultWaiting K D ctx count rnd v st k)))
    let next ← free (Concrete.sequenceFin (roundLocal D (treeSimExtendMultWaiting K D ctx count rnd v st k) b.2))
    pure (b.1, next, b.2)) = _
  apply bind_congr
  intro b
  congr 1
  congr 1
  congr 1
  funext i
  exact treeSim_extendMult_resume_local K D ctx count rnd v st k b.2 i

def treeSimExtendMultPartial {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (live : C.Party → Bool) (count : ℕ) (rnd : C.Party → PrssOutput C E)
    (v : C.Party → ℕ → E) (st : C.Party → RunState C)
    (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α) :
    C.Party → Step C E RealSpec α := fun i =>
  if live i then treeSimExtendMultWaiting K D ctx count rnd v st k i else .done none

theorem treeSim_extendMult_partial_view {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (live : C.Party → Bool) (count : ℕ) (rnd : C.Party → PrssOutput C E)
    (v : C.Party → ℕ → E) (st : C.Party → RunState C)
    (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α) :
    treeSimRoundView D (treeSimExtendMultPartial K D ctx live count rnd v st k) =
      fun c i => if live i then treeSimRoundView D (treeSimExtendMultWaiting K D ctx count rnd v st k) c i else none := by
  funext c i
  by_cases hl : live i = true
  · simp only [treeSimRoundView, treeSimExtendMultPartial, if_pos hl]
  · simp [treeSimRoundView, treeSimExtendMultPartial, hl, Step.outbox]

/-- The real peer exchange propagates a prior honest abort before running
any continuation, including when all remaining parties were ready for ExtendMult. -/
theorem treeSim_extendMult_partial_local {α : Type} (D : C.Coalition) (ctx : C.Party → Context C)
    (live : C.Party → Bool) (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true) (count : ℕ)
    (rnd : C.Party → PrssOutput C E) (v : C.Party → ℕ → E) (st : C.Party → RunState C)
    (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (treeSimExtendMultPartial K D ctx live count rnd v st k) sent i = pure (.done none) := by
  by_cases hl : live i = true
  · by_cases hi : i ∈ D.1
    · simp only [roundLocal, treeSimExtendMultPartial, if_pos hl, treeSimExtendMultWaiting, if_pos hi]
    · have hab : anyAbort (fun j => if j ∈ D.1 then sent j i else
          (treeSimExtendMultPartial K D ctx live count rnd v st k j).delivered i) = true := by
        obtain ⟨j, hj, hjl⟩ := stopped
        unfold anyAbort
        rw [List.any_eq_true]
        refine ⟨j, by simp [Committee.parties], ?_⟩
        simp [hj, treeSimExtendMultPartial, hjl, Step.delivered, Msg.isAbort]
      simp only [roundLocal, treeSimExtendMultPartial, if_pos hl, treeSimExtendMultWaiting, if_neg hi, treeSimPeerStep]
      change advance (exchangeResume (G := RealSpec) _ (fun j => if j ∈ D.1 then sent j i else
        (treeSimExtendMultPartial K D ctx live count rnd v st k j).delivered i)) = _
      unfold exchangeResume
      unfold anyAbort at hab
      rw [if_pos hab]
      rfl
  · simp only [roundLocal, treeSimExtendMultPartial, if_neg hl]

/-- Prior aborts still expose the exact field-peer view to the rushing adversary. -/
theorem treeSim_extendMult_partial_factor {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (ctx : C.Party → Context C)
    (live : C.Party → Bool) (stopped : ∃ j, j ∉ D.1 ∧ live j ≠ true) (count : ℕ)
    (rnd : C.Party → PrssOutput C E) (v : C.Party → ℕ → E) (st : C.Party → RunState C)
    (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state (treeSimExtendMultPartial K D ctx live count rnd v st k) = (do
      let b ← worldRoles.adversary (A.round state
        (treeSimRoundView D (treeSimExtendMultPartial K D ctx live count rnd v st k)))
      pure (b.1, (fun _ => Step.done none), b.2)) := by
  rw [stepRound_real]
  change (do
    let b ← worldRoles.adversary (A.round state
      (treeSimRoundView D (treeSimExtendMultPartial K D ctx live count rnd v st k)))
    let next ← free (Concrete.sequenceFin (roundLocal D (treeSimExtendMultPartial K D ctx live count rnd v st k) b.2))
    pure (b.1, next, b.2)) = _
  apply bind_congr
  intro b
  rw [sequenceFin_congr_pure _ (fun _ => Step.done none)
    (treeSim_extendMult_partial_local K D ctx live stopped count rnd v st k b.2)]
  simp only [free_pure, pure_bind]

/-- Concrete field peer waiting programs, also used after a prior abort. -/
structure TreeSimExtendMultWaitingData where
  δ : HiddenAddress C → Bit
  count : ℕ
  ctx₁ : C.Party → Context C
  ctx₂ : C.Party → Context C
  rnd₁ : C.Party → PrssOutput C E
  rnd₂ : C.Party → PrssOutput C E
  v₁ : C.Party → ℕ → E
  v₂ : C.Party → ℕ → E
  st₁ : C.Party → RunState C
  st₂ : C.Party → RunState C
  k₁ : C.Party → Shares C E × RunState C → PartyM C E RealSpec TreeOutput
  k₂ : C.Party → Shares C E × RunState C → PartyM C E RealSpec TreeOutput
/-- The additive field masks required at a reachable ExtendMult boundary.
Their realization by actual PRSS remains an explicit obligation. -/
structure TreeSimExtendMultData (D : C.Coalition) extends TreeSimExtendMultWaitingData (C := C) (E := E) where
  self₁ : ∀ i, i ∉ D.1 → (ctx₁ i).self = i
  self₂ : ∀ i, i ∉ D.1 → (ctx₂ i).self = i
  T₀ : C.Term
  pivotParty : C.Party
  pivot : Pivot K D T₀ pivotParty
  masks : ∀ i, i ∉ D.1 → rnd₂ i = rnd₁ i + frandShare D count 0 0
    (termShift K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin count → E))
    (pairShift pivotParty (pairDelta K D T₀ pivotParty (v₁ - v₂) (0 : C.Term → Fin count → E))) i

/-- GS20's masks cancel the change of every corrupt-visible field message. -/
theorem TreeSimExtendMultData.visible (D : C.Coalition) (d : TreeSimExtendMultData K D)
    (i : C.Party) (hi : i ∉ D.1) (hk : KnownTo D.1 (K.filled i)) (g : ℕ) (hg : g < d.count) :
    reshareU K (d.ctx₂ i) (d.rnd₂ i).1 (d.rnd₂ i).2 (d.v₂ i) g =
      reshareU K (d.ctx₁ i) (d.rnd₁ i).1 (d.rnd₁ i).2 (d.v₁ i) g := by
  haveI : CharP E 2 := charTwo
  let dt := termShift K D d.T₀ d.pivotParty (d.v₁ - d.v₂) (0 : C.Term → Fin d.count → E)
  let dp := pairShift d.pivotParty (pairDelta K D d.T₀ d.pivotParty (d.v₁ - d.v₂) (0 : C.Term → Fin d.count → E))
  have hz := uVal_termShift K D (R := E) 0 0 0 0 d.T₀ d.pivot.hidden d.pivotParty d.pivot.honest
    d.pivot.filled d.pivot.owner (d.v₁ - d.v₂) (0 : C.Term → Fin d.count → E) i hi
    (fun h => d.pivot.hidden (h ▸ hk)) g hg
  have he := reshareU_frandShare K D (R := E) 0 0 dt dp (d.v₁ - d.v₂) i g
  have hzero : uVal K D (c := d.count) (0 : Shares C E) 0 0 0 (fun _ _ => 0) i g = 0 := by
    simp [uVal, pairVal, randVal]
  simp only [zero_add, hzero, targetShift, if_pos hk, Pi.zero_apply, add_zero] at hz
  change uVal K D 0 0 dt dp (d.v₁ - d.v₂) i g = 0 at hz
  rw [hz] at he
  rw [d.masks i hi]
  simp only [reshareU, d.self₁ i hi, d.self₂ i hi, localContext, Prod.fst_add, Prod.snd_add,
    Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib] at he ⊢
  have htwo := CharTwo.add_self_eq_zero (d.v₁ i g - d.v₂ i g)
  linear_combination he - htwo

theorem TreeSimExtendMultData.view (D : C.Coalition) (d : TreeSimExtendMultData K D) :
    treeSimRoundView D (treeSimExtendMultWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁) =
      treeSimRoundView D (treeSimExtendMultWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂) := by
  funext c i
  by_cases hc : c ∈ D.1
  · by_cases hi : i ∈ D.1
    · simp [treeSimRoundView, treeSimExtendMultWaiting, hc, hi, Step.outbox]
    · simp only [treeSimRoundView, if_pos (show c ∈ D.1 ∧ i ∉ D.1 from ⟨hc, hi⟩), if_neg hi, treeSimExtendMultWaiting,
        treeSimPeerStep, Step.outbox, reshareOut, d.self₁ i hi, d.self₂ i hi]
      split_ifs with h
      · congr 2
        apply vector_congr
        intro g hg
        exact (d.visible K D i hi ⟨c, hc, h.2⟩ g hg).symm
      · rfl
  · simp [treeSimRoundView, hc]

/-- Both inboxes abort on the same malicious frames; honest messages are
field vectors or absent messages, never abort frames. -/
theorem TreeSimExtendMultData.abort (D : C.Coalition) (d : TreeSimExtendMultData K D)
    (sent : C.Party → Mail C E) (i : C.Party) :
    anyAbort (fun j => if j ∈ D.1 then sent j i else
      (treeSimExtendMultWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ j).delivered i) =
    anyAbort (fun j => if j ∈ D.1 then sent j i else
      (treeSimExtendMultWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ j).delivered i) := by
  unfold anyAbort
  congr 1
  funext j
  by_cases hj : j ∈ D.1
  · simp only [if_pos hj]
  · simp only [if_neg hj, treeSimExtendMultWaiting, treeSimPeerStep, Step.delivered, reshareOut]
    split_ifs <;> rfl

/-- Exact field records, without assuming linearity of the encoding. -/
def TreeSimExtendMultExitRel (D : C.Coalition) (d : TreeSimExtendMultData K D)
    (i : C.Party) (x y : Shares C E × RunState C) : Prop :=
  y.1 = treeSimFieldHeldShift D i d.count
      (fun g => ∑ j ∈ Finset.univ.filter (· ∉ D.1), (d.v₁ - d.v₂) j g) x.1 ∧
    x.2 = ⟨recordPeer K (elementCodec K) (d.ctx₁ i).self (d.st₁ i).history x.1 d.count,
      (d.st₁ i).label + 1, (d.st₁ i).tag⟩ ∧
    y.2 = ⟨recordPeer K (elementCodec K) (d.ctx₂ i).self (d.st₂ i).history y.1 d.count,
      (d.st₂ i).label + 1, (d.st₂ i).tag⟩

theorem TreeSimExtendMultData.outputs (D : C.Coalition) (d : TreeSimExtendMultData K D)
    (sent : C.Party → Mail C E) (i : C.Party) :
    Option.Rel (TreeSimExtendMultExitRel K D d i)
      (treeSimExtendMultOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent i)
      (treeSimExtendMultOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent i) := by
  by_cases hi : i ∈ D.1
  · simp [treeSimExtendMultOutputs, hi, Option.Rel.none]
  · simp only [treeSimExtendMultOutputs, if_neg hi, treeSimExtendMultReturn, d.abort K D sent i]
    split_ifs
    · exact Option.Rel.none
    · apply Option.Rel.some
      refine ⟨?_, rfl, rfl⟩
      have inbox : ∀ ctx rnd v st (k : C.Party → Shares C E × RunState C → PartyM C E RealSpec TreeOutput),
          (fun j => if j ∈ D.1 then sent j i else
            (treeSimExtendMultWaiting K D ctx d.count rnd v st k j).delivered i) =
          (fun j => if j ∈ D.1 then sent j i else
            reshareOut K (ctx j) (elementCodec K) (rnd j).1 (rnd j).2 (v j) d.count i) := by
        intro ctx rnd v st k
        funext j
        by_cases hj : j ∈ D.1 <;>
          simp [treeSimExtendMultWaiting, treeSimPeerStep, Step.delivered, hj]
      dsimp only
      rw [inbox, inbox]
      exact treeSim_fieldReshareZ_pivot K D d.pivot d.ctx₁ d.ctx₂ d.self₁ d.self₂ d.count
        d.v₁ d.v₂ d.rnd₁ d.rnd₂ d.masks sent i hi

/-- Only the actual successful field outputs require continuation couplings.
The relation is chosen after the whole output vector and the rushing reply. -/
structure TreeSimExtendMultLocalClosure (D : C.Coalition) (d : TreeSimExtendMultData K D)
    (sent : C.Party → Mail C E) where
  J : TreeSimState C → (HashCache C × HiddenCache C) → Prop
  Q : C.Party → Step C E RealSpec TreeOutput → Step C E RealSpec TreeOutput → Prop
  abort : ∀ i, Q i (.done none) (.done none)
  continues : ∀ i x y,
    treeSimExtendMultOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent i = some x →
    treeSimExtendMultOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent i = some y →
    TreeSimExtendMultExitRel K D d i x y → ∀ a b, J a b →
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (advance (d.k₁ i x).run))).run a)
      ((simulateQ (streamWorld prims D) (free (advance (d.k₂ i y).run))).run b)
      (fun u z => Q i u.1 z.1 ∧ J u.2 z.2)

/-- Resume the real field continuations in the driver's operator order. -/
theorem TreeSimExtendMultLocalClosure.resume (D : C.Coalition) (d : TreeSimExtendMultData K D)
    (sent : C.Party → Mail C E) (close : TreeSimExtendMultLocalClosure prims K D d sent)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : close.J a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll d.k₁
        (treeSimExtendMultOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent))).run a)
      ((simulateQ (streamWorld prims D) (treeSimResumeAll d.k₂
        (treeSimExtendMultOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent))).run b)
      (fun u z => (∀ i, close.Q i (u.1 i) (z.1 i)) ∧ close.J u.2 z.2) := by
  apply treeSim_resumeAll_rel prims D d.k₁ d.k₂ _ _ close.J close.Q _ a b h
  intro i u z hj
  have ho := d.outputs K D sent i
  generalize h₁ : treeSimExtendMultOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent i = left at ho ⊢
  generalize h₂ : treeSimExtendMultOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent i = right at ho ⊢
  cases ho with
  | none =>
    simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨close.abort i, hj⟩
  | some hexit => exact close.continues i _ _ h₁ h₂ hexit u z hj

/-- The remaining field exchange obligations concern local saved continuations and
closure of the ceremony invariant, at supported replies and resumes. -/
structure TreeSimExtendMultClosure (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (d : TreeSimExtendMultData K D) (state₀ : A.State)
    (initial₁ : TreeSimState C) (initial₂ : HashCache C × HiddenCache C) where
  next : ∀ state sent a b,
    TreeSimReplyReachable prims D A state₀
      (treeSimExtendMultWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂) initial₁ initial₂ state sent a b →
    TreeSimStreamRel d.δ a b → a.1.2 = initial₁.1.2 → b.2 = initial₂.2 →
    ∃ close : TreeSimExtendMultLocalClosure prims K D d sent, close.J a b ∧
      ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) (treeSimResumeAll d.k₁
          (treeSimExtendMultOutputs K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ sent))).run a),
      ∀ z ∈ support ((simulateQ (streamWorld prims D) (treeSimResumeAll d.k₂
          (treeSimExtendMultOutputs K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ sent))).run b),
      (∀ i, close.Q i (u.1 i) (z.1 i)) → close.J u.2 z.2 →
      Bad u.2 ∨ Inv ((state, u.1), u.2) ((state, z.1), z.2)

/-- Actual field peer waiting states and local continuation certificates.
Prior aborts require equal visible partial messages. Proving this equality
for reachable states still requires the live senders' mask cancellation. -/
def TreeSimExtendMultBoundary (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  (∃ d : TreeSimExtendMultData K D, a.1.1 = b.1.1 ∧ TreeSimStreamRel d.δ a.2 b.2 ∧
      a.1.2 = treeSimExtendMultWaiting K D d.ctx₁ d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
      b.1.2 = treeSimExtendMultWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂ ∧
      Nonempty (TreeSimExtendMultClosure prims K D A Bad Inv d a.1.1 a.2 b.2)) ∨
  ∃ d : TreeSimExtendMultWaitingData (C := C) (E := E), a.1.1 = b.1.1 ∧ TreeSimStreamRel d.δ a.2 b.2 ∧
    ∃ live, (∃ j, j ∉ D.1 ∧ live j ≠ true) ∧
      a.1.2 = treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁ ∧
      b.1.2 = treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂ ∧
      treeSimRoundView D (treeSimExtendMultPartial K D d.ctx₁ live d.count d.rnd₁ d.v₁ d.st₁ d.k₁) =
        treeSimRoundView D (treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) ∧
      (∀ state sent u z, TreeSimReplyReachable prims D A a.1.1
          (treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) a.2 b.2 state sent u z →
        TreeSimStreamRel d.δ u z → u.1.2 = a.2.1.2 → z.2 = b.2.2 →
        Bad u ∨ Inv ((state, fun _ => .done none), u) ((state, fun _ => .done none), z))

/-- The real ExtendMult exchange couples messages, aborts, field T₀ output shifts and
ordered continuation execution, conditional on reachable boundaries, local
continuation couplings and invariant closure. -/
theorem treeSim_extendMult_preserves (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (stage : TreeSimConfig A (TreeSimState C) → TreeSimStage)
    (identify : ∀ a b, stage a = .extendMult → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
      TreeSimExtendMultBoundary prims K D A Bad Inv a b) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A Bad Inv stage .extendMult := by
  intro a b hg hinv hbad hdone
  have boundary := identify a b hg hinv hbad hdone
  change RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2) _
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rcases boundary with ⟨d, had, hc, ha, hb, close⟩ | ⟨d, had, hc, live, stopped, ha, hb, views, close⟩
  · rw [ha, hb, ← had, treeSim_extendMult_resume_factor, treeSim_extendMult_resume_factor, d.view K D]
    simp only [simulateQ_bind, StateT.run_bind]
    apply relTriple_bind (treeSim_relTriple_support
      (treeSim_local_streamRel_fixed prims D d.δ _ a.2 b.2 hc))
    intro r₁ r₂ hr
    obtain ⟨hr, hs₁, hs₂⟩ := hr
    have reach : TreeSimReplyReachable prims D A a.1.1
        (treeSimExtendMultWaiting K D d.ctx₂ d.count d.rnd₂ d.v₂ d.st₂ d.k₂) a.2 b.2 r₂.1.1 r₂.1.2 r₁.2 r₂.2 := by
      refine ⟨?_, hs₂⟩
      change (r₂.1, r₁.2) ∈ _
      rw [← hr.1]
      exact hs₁
    rw [hr.1]
    obtain ⟨close⟩ := close
    obtain ⟨localClose, hj, accepts⟩ := close.next r₂.1.1 r₂.1.2 r₁.2 r₂.2 reach hr.2.1 hr.2.2.1 hr.2.2.2
    apply relTriple_bind (treeSim_relTriple_support
      (localClose.resume prims K D d r₂.1.2 r₁.2 r₂.2 hj))
    intro u z hz
    obtain ⟨⟨hq, hj⟩, hsu, hsz⟩ := hz
    simp only [simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure (accepts u hsu z hsz hq hj)
  · rw [ha, hb, ← had, treeSim_extendMult_partial_factor K D A _ _ live stopped,
      treeSim_extendMult_partial_factor K D A _ _ live stopped, views]
    simp only [simulateQ_bind, StateT.run_bind]
    apply relTriple_bind (treeSim_relTriple_support
      (treeSim_local_streamRel_fixed prims D d.δ _ a.2 b.2 hc))
    intro r₁ r₂ hr
    obtain ⟨hr, hs₁, hs₂⟩ := hr
    have reach : TreeSimReplyReachable prims D A a.1.1
        (treeSimExtendMultPartial K D d.ctx₂ live d.count d.rnd₂ d.v₂ d.st₂ d.k₂) a.2 b.2 r₂.1.1 r₂.1.2 r₁.2 r₂.2 := by
      refine ⟨?_, hs₂⟩
      change (r₂.1, r₁.2) ∈ _
      rw [← hr.1]
      exact hs₁
    simp only [simulateQ_pure, StateT.run_pure]
    apply relTriple_pure_pure
    rw [hr.1]
    exact close r₂.1.1 r₂.1.2 r₁.2 r₂.2 reach hr.2.1 hr.2.2.1 hr.2.2.2

/-- Empty-opening messages and delivered aborts do not depend on the
continuations saved by either execution. -/
theorem treeSim_emptyOpen_view (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput) :
    treeSimRoundView D (treeSimEmptyOpenPartial K D live ds k₁) =
      treeSimRoundView D (treeSimEmptyOpenPartial K D live ds k₂) := by
  funext j i
  simp only [treeSimRoundView, treeSimEmptyOpenPartial]
  split_ifs <;> rfl

def treeSimEmptyOpenInbox (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E) (i : C.Party) : Mail C E :=
  fun j => if j ∈ D.1 then sent j i else
    if live j then treeSimEmptyOpenOut K j (ds j) i else some .abort

/-- The local head performs transport-abort detection, the real copy-hash
queries and the real agreement test, before entering the saved continuation. -/
def treeSimEmptyOpenHead (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E) (i : C.Party) :
    OracleComp (RoSpec C) (Option Unit) :=
  if i ∈ D.1 then pure none else if live i then
    let inbox := treeSimEmptyOpenInbox K D live ds sent i
    if anyAbort inbox then pure none else do
      let copyDigests ← treeSimEmptyCopyHashes (C := C)
      pure (if TreeSimOpenValid K i inbox copyDigests then some () else none)
  else pure none

/-- This equation retains the hash calls at their original position in the
operator sequence. They cannot be moved ahead of other continuations. -/
theorem treeSim_emptyOpen_local (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (k : C.Party → PartyM C E RealSpec TreeOutput)
    (sent : C.Party → Mail C E) (i : C.Party) :
    free (roundLocal D (treeSimEmptyOpenPartial K D live ds k) sent i) = (do
      let out ← free (liftComp (treeSimEmptyOpenHead K D live ds sent i) (LocalSpec C))
      free (treeSimResume (fun _ : Unit => k i) out)) := by
  have inbox : (fun j => if j ∈ D.1 then sent j i else
      (treeSimEmptyOpenPartial K D live ds k j).delivered i) =
      treeSimEmptyOpenInbox K D live ds sent i := by
    funext j
    by_cases hj : j ∈ D.1 <;> by_cases hl : live j = true <;>
      simp [treeSimEmptyOpenPartial, treeSimEmptyOpenStep, treeSimEmptyOpenInbox, Step.delivered, hj, hl]
  by_cases hi : i ∈ D.1
  · simp [roundLocal, treeSimEmptyOpenHead, treeSimEmptyOpenPartial, hi, treeSimResume,
      liftComp_pure, free_pure]
  · by_cases hl : live i = true
    · simp only [roundLocal, if_neg hi, treeSimEmptyOpenPartial, if_pos hl, treeSimEmptyOpenStep]
      simp only [treeSimEmptyOpenPartial, treeSimEmptyOpenStep] at inbox
      rw [inbox]
      unfold treeSimEmptyOpenHead
      rw [if_neg hi, if_pos hl]
      unfold exchangeResume anyAbort
      dsimp only
      split_ifs with habort
      · rfl
      · simp only [advance_oracleStep_bind, free_bind, liftComp_bind, liftComp_pure, free_pure,
          bind_assoc, pure_bind]
        apply bind_congr
        intro copyDigests
        unfold require
        split_ifs <;> simp [treeSimResume, pure_bind, free_pure] <;> rfl
    · simp [roundLocal, treeSimEmptyOpenPartial, treeSimEmptyOpenHead, hi, hl,
        treeSimResume, liftComp_pure, free_pure]

/-- The local agreement decision uses only the common hash cache. -/
theorem treeSim_emptyOpen_head_onHash (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E) (i : C.Party) :
    ∃ m : StateT (HashCache C) ProbComp (Option Unit),
      simulateQ (streamWorld prims D)
        (free (liftComp (treeSimEmptyOpenHead K D live ds sent i) (LocalSpec C))) = onHash m := by
  have hp := treeSim_hashes_onHash prims D (C.terms.map fun _ => Query.copy [])
  simp only [List.mapM_map, Function.comp_def] at hp
  unfold treeSimEmptyOpenHead
  dsimp only
  split_ifs
  · exact ⟨pure none, by simp [liftComp_pure, free_pure, treeSim_onHash_pure]⟩
  · exact ⟨pure none, by simp [liftComp_pure, free_pure, treeSim_onHash_pure]⟩
  · refine ⟨(C.terms.mapM fun _ => hashAnswer prims (.copy [])) >>= fun copyDigests =>
      pure (if TreeSimOpenValid K i (treeSimEmptyOpenInbox K D live ds sent i) copyDigests
        then some () else none), ?_⟩
    simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
      simulateQ_pure, treeSimEmptyCopyHashes, hp]
    rw [treeSim_onHash_bind]
    simp only [treeSim_onHash_pure]
  · exact ⟨pure none, by simp [liftComp_pure, free_pure, treeSim_onHash_pure]⟩

def treeSimEmptyOpenDecision (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E) (i : C.Party)
    (digest : HashOutput) : Option Unit :=
  if i ∈ D.1 then none else if live i then
    let inbox := treeSimEmptyOpenInbox K D live ds sent i
    if anyAbort inbox then none else
      if TreeSimOpenValid K i inbox (List.replicate C.terms.length digest) then some () else none
  else none

/-- The actual head leaves both caches intact, while the logged execution
still records every honest hash query. -/
theorem treeSim_emptyOpen_head_cached (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E) (i : C.Party)
    (s : HashCache C × HiddenCache C) (digest : HashOutput)
    (cached : s.1 (.copy []) = some digest) :
    (simulateQ (streamWorld prims D)
      (free (liftComp (treeSimEmptyOpenHead K D live ds sent i) (LocalSpec C)))).run s =
      pure (treeSimEmptyOpenDecision K D live ds sent i digest, s) := by
  have hp := treeSim_hashes_onHash prims D (C.terms.map fun _ => Query.copy [])
  simp only [List.mapM_map, Function.comp_def] at hp
  unfold treeSimEmptyOpenHead treeSimEmptyOpenDecision
  dsimp only
  split_ifs <;> try simp only [liftComp_pure, free_pure, simulateQ_pure, StateT.run_pure]
  all_goals
    simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind, simulateQ_pure,
      treeSimEmptyCopyHashes, hp, StateT.run_bind, onHash, StateT.run_mk,
      treeSim_copyHashes_cached prims _ _ _ cached, map_pure, pure_bind, StateT.run_pure]
  all_goals simp_all only [if_pos, if_neg, if_false, if_true]

/-- A deterministic cache-preserving head couples over different public and
private caches. The actual real log is retained, rather than reconstructed. -/
theorem treeSim_readOnly_coupling {α : Type} (D : C.Coalition) (p : OracleComp (WorldSpec C) α)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (out : α)
    (ha : (simulateQ (streamWorld prims D) p).run a.1 = pure (out, a.1))
    (hb : (simulateQ (streamWorld prims D) p).run b = pure (out, b)) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) p).run a)
      ((simulateQ (streamWorld prims D) p).run b)
      (fun u z => u.1 = out ∧ z.1 = out ∧ u.2.1 = a.1 ∧ z.2 = b) := by
  have erase := treeSimLoggedWorld_erase prims D p a.1 a.2
  rw [ha] at erase
  have actual : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run a),
      u.1 = out ∧ u.2.1 = a.1 := by
    intro u hu
    have hmem : (u.1, u.2.1) ∈ support ((fun r => (r.1, r.2.1)) <$>
        (simulateQ (treeSimLoggedWorld prims D) p).run a) := by
      rw [support_map]
      exact ⟨u, hu, rfl⟩
    rw [erase] at hmem
    simpa only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] using hmem
  have mapped := congrArg (fun q => (fun _ : α × (HashCache C × HiddenCache C) => (out, b)) <$> q) erase
  simp only [Functor.map_map, map_pure, Function.comp_def] at mapped
  rw [hb, ← mapped]
  have h : RelTriple
      (id <$> (simulateQ (treeSimLoggedWorld prims D) p).run a)
      ((fun _ => (out, b)) <$> (simulateQ (treeSimLoggedWorld prims D) p).run a)
      (fun u z => u.1 = out ∧ z.1 = out ∧ u.2.1 = a.1 ∧ z.2 = b) := by
    apply relTriple_map
    apply relTriple_post_mono (treeSim_refl_support _)
    rintro u _ ⟨hu, rfl⟩
    exact ⟨(actual u hu).1, rfl, (actual u hu).2, rfl⟩
  simpa only [id_map] using h

/-- Only the post-opening continuations remain probabilistic obligations.
The head closure is deterministic, on actual supported executions that leave
both caches unchanged. No equality of unrelated public entries is required. -/
structure TreeSimEmptyOpenLocalClosure (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput) where
  J : TreeSimState C → (HashCache C × HiddenCache C) → Prop
  Q : C.Party → Step C E RealSpec TreeOutput → Step C E RealSpec TreeOutput → Prop
  head : ∀ i a b out u z, J a b →
    u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (treeSimEmptyOpenHead K D live ds sent i) (LocalSpec C)))).run a) →
    z ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (treeSimEmptyOpenHead K D live ds sent i) (LocalSpec C)))).run b) →
    u.1 = out → z.1 = out → u.2.1 = a.1 → z.2 = b → J u.2 z.2
  abort : ∀ i, Q i (.done none) (.done none)
  continues : ∀ i a b u z, J a b →
    u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (treeSimEmptyOpenHead K D live ds sent i) (LocalSpec C)))).run a) →
    z ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (treeSimEmptyOpenHead K D live ds sent i) (LocalSpec C)))).run b) →
    u.1 = some () → z.1 = some () → J u.2 z.2 →
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (advance (k₁ i).run))).run u.2)
      ((simulateQ (streamWorld prims D) (free (advance (k₂ i).run))).run z.2)
      (fun u z => Q i u.1 z.1 ∧ J u.2 z.2)

/-- The real local opening step couples its cached hash calls and abort test,
then invokes only the obligation for the continuation that actually runs. -/
theorem TreeSimEmptyOpenLocalClosure.local (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput)
    (close : TreeSimEmptyOpenLocalClosure prims K D live ds sent k₁ k₂)
    (i : C.Party) (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : close.J a b)
    (digest : HashOutput) (h₁ : a.1.1 (.copy []) = some digest) (h₂ : b.1 (.copy []) = some digest) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D)
      (free (roundLocal D (treeSimEmptyOpenPartial K D live ds k₁) sent i))).run a)
      ((simulateQ (streamWorld prims D)
      (free (roundLocal D (treeSimEmptyOpenPartial K D live ds k₂) sent i))).run b)
      (fun u z => close.Q i u.1 z.1 ∧ close.J u.2 z.2) := by
  rw [treeSim_emptyOpen_local, treeSim_emptyOpen_local]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support (treeSim_readOnly_coupling prims D _ a b
    (treeSimEmptyOpenDecision K D live ds sent i digest)
    (treeSim_emptyOpen_head_cached prims K D live ds sent i a.1 digest h₁)
    (treeSim_emptyOpen_head_cached prims K D live ds sent i b digest h₂)))
  intro u z hz
  obtain ⟨⟨hu, hz, ha, hb⟩, hsu, hsz⟩ := hz
  have hj := close.head i a b _ u z h hsu hsz hu hz ha hb
  rw [hu, hz]
  cases hd : treeSimEmptyOpenDecision K D live ds sent i digest with
  | none =>
    simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨close.abort i, hj⟩
  | some out =>
    cases out
    exact close.continues i a b u z h hsu hsz (hu.trans hd) (hz.trans hd) hj

/-- Hash checks and continuations are interleaved in the actual driver order. -/
theorem TreeSimEmptyOpenLocalClosure.all (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput)
    (close : TreeSimEmptyOpenLocalClosure prims K D live ds sent k₁ k₂)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : close.J a b)
    (digest : HashOutput) (h₁ : a.1.1 (.copy []) = some digest) (h₂ : b.1 (.copy []) = some digest) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D)
      (free (Concrete.sequenceFin (roundLocal D (treeSimEmptyOpenPartial K D live ds k₁) sent)))).run a)
      ((simulateQ (streamWorld prims D)
      (free (Concrete.sequenceFin (roundLocal D (treeSimEmptyOpenPartial K D live ds k₂) sent)))).run b)
      (fun u z => (∀ i, close.Q i (u.1 i) (z.1 i)) ∧ close.J u.2 z.2 ∧
        u.2.1.1 (.copy []) = some digest ∧ z.2.1 (.copy []) = some digest) := by
  rw [free_sequenceFin, free_sequenceFin, simulateQ_sequenceFin, simulateQ_sequenceFin]
  let J := fun u z => close.J u z ∧ u.1.1 (.copy []) = some digest ∧ z.1 (.copy []) = some digest
  apply treeSim_sequenceFin_rel _ _ J close.Q (fun i s t hst => ?_) a b ⟨h, h₁, h₂⟩
  apply relTriple_post_mono (treeSim_relTriple_support
    (close.local prims K D live ds sent k₁ k₂ i s t hst.1 digest hst.2.1 hst.2.2))
  intro u z hz
  obtain ⟨hz, hsu, hsz⟩ := hz
  exact ⟨hz.1, hz.2, (treeSim_logged_grows prims D _ s u hsu) hst.2.1,
    (treeSim_stream_grows prims D _ t z hsz) hst.2.2⟩

/-- A terminal empty opening needs no continuation coupling hypothesis.
The two successful outputs may differ, but the abort decision is common. -/
def TreeSimEmptyOpenLocalClosure.terminal (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (out₁ out₂ : C.Party → TreeOutput) :
    TreeSimEmptyOpenLocalClosure prims K D live ds sent (fun i => pure (out₁ i)) (fun i => pure (out₂ i)) where
  J := fun _ _ => True
  Q := fun i u z => (u = .done none ∧ z = .done none) ∨
    (u = .done (some (out₁ i)) ∧ z = .done (some (out₂ i)))
  head := by
    intro i a b out u z h _ _ _ _ ha hb
    simpa only [ha, hb] using h
  abort := fun _ => Or.inl ⟨rfl, rfl⟩
  continues := by
    intro i a b u z _ _ _ _ _ h
    change RelTriple (pure ((.done (some (out₁ i)) : Step C E RealSpec TreeOutput), u.2))
      (pure ((.done (some (out₂ i)) : Step C E RealSpec TreeOutput), z.2)) _
    exact relTriple_pure_pure ⟨Or.inr ⟨rfl, rfl⟩, h⟩

/-- Terminal local openings couple over caches that only agree at `.copy []`.
All malformed-message and transport-abort decisions remain in the real steps. -/
theorem treeSim_emptyOpen_terminal (D : C.Coalition) (live : C.Party → Bool)
    (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (out₁ out₂ : C.Party → TreeOutput) (digest : HashOutput)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (h₁ : a.1.1 (.copy []) = some digest) (h₂ : b.1 (.copy []) = some digest) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D)
      (free (Concrete.sequenceFin (roundLocal D
        (treeSimEmptyOpenPartial K D live ds (fun i => pure (out₁ i))) sent)))).run a)
      ((simulateQ (streamWorld prims D)
      (free (Concrete.sequenceFin (roundLocal D
        (treeSimEmptyOpenPartial K D live ds (fun i => pure (out₂ i))) sent)))).run b)
      (fun u z => (∀ i, (u.1 i = .done none ∧ z.1 i = .done none) ∨
        (u.1 i = .done (some (out₁ i)) ∧ z.1 i = .done (some (out₂ i)))) ∧
        u.2.1.1 (.copy []) = some digest ∧ z.2.1 (.copy []) = some digest) := by
  apply relTriple_post_mono ((TreeSimEmptyOpenLocalClosure.terminal prims K D live ds sent out₁ out₂).all
    prims K D live ds sent _ _ a b trivial digest h₁ h₂)
  intro u z hz
  exact ⟨hz.1, hz.2.2⟩

/-- A local invariant is selected after the actual common rushing response.
All later hashes and continuation effects are handled in their actual order. -/
structure TreeSimEmptyOpenClosure (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (δ : HiddenAddress C → Bit) (live : C.Party → Bool) (ds : C.Party → List HashOutput)
    (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput) (state₀ : A.State)
    (initial₁ : TreeSimState C) (initial₂ : HashCache C × HiddenCache C) where
  next : ∀ state sent a b digest,
    TreeSimReplyReachable prims D A state₀ (treeSimEmptyOpenPartial K D live ds k₂)
      initial₁ initial₂ state sent a b →
    TreeSimStreamRel δ a b → a.1.2 = initial₁.1.2 → b.2 = initial₂.2 →
    a.1.1 (.copy []) = some digest → b.1 (.copy []) = some digest →
    ∃ close : TreeSimEmptyOpenLocalClosure prims K D live ds sent k₁ k₂, close.J a b ∧
      ∀ (u : (C.Party → Step C E RealSpec TreeOutput) × TreeSimState C)
        (z : (C.Party → Step C E RealSpec TreeOutput) × (HashCache C × HiddenCache C)),
        u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (free (Concrete.sequenceFin (roundLocal D (treeSimEmptyOpenPartial K D live ds k₁) sent)))).run a) →
        z ∈ support ((simulateQ (streamWorld prims D)
          (free (Concrete.sequenceFin (roundLocal D (treeSimEmptyOpenPartial K D live ds k₂) sent)))).run b) →
        (∀ i, close.Q i (u.1 i) (z.1 i)) → close.J u.2 z.2 →
        Bad u.2 ∨ Inv ((state, u.1), u.2) ((state, z.1), z.2)

def TreeSimEmptyOpenBoundary (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ δ live ds k₁ k₂, a.1.1 = b.1.1 ∧ TreeSimStreamRel δ a.2 b.2 ∧
    a.1.2 = treeSimEmptyOpenPartial K D live ds k₁ ∧ b.1.2 = treeSimEmptyOpenPartial K D live ds k₂ ∧
    (∃ digest, a.2.1.1 (.copy []) = some digest ∧ b.2.1 (.copy []) = some digest) ∧
    Nonempty (TreeSimEmptyOpenClosure prims K D A Bad Inv δ live ds k₁ k₂ a.1.1 a.2 b.2)

/-- The empty-opening stage includes the real rushing call, copy checks,
selective abort and the exact per-party continuation order. -/
theorem treeSim_emptyOpen_preserves (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (stage : TreeSimConfig A (TreeSimState C) → TreeSimStage)
    (identify : ∀ a b, stage a = .openRepEmpty → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
      TreeSimEmptyOpenBoundary prims K D A Bad Inv a b) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A Bad Inv stage .openRepEmpty := by
  intro a b hg hinv hbad hdone
  obtain ⟨δ, live, ds, k₁, k₂, had, hc, ha, hb, ⟨digest, cached₁, cached₂⟩, ⟨close⟩⟩ := identify a b hg hinv hbad hdone
  change RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2) _
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [ha, hb, ← had, stepRound_real, stepRound_real]
  change RelTriple
    ((simulateQ (treeSimLoggedWorld prims D) (do
      let r ← worldRoles.adversary (A.round a.1.1 (treeSimRoundView D (treeSimEmptyOpenPartial K D live ds k₁)))
      let next ← free (Concrete.sequenceFin (roundLocal D (treeSimEmptyOpenPartial K D live ds k₁) r.2))
      pure (r.1, next, r.2))).run a.2)
    ((simulateQ (streamWorld prims D) (do
      let r ← worldRoles.adversary (A.round a.1.1 (treeSimRoundView D (treeSimEmptyOpenPartial K D live ds k₂)))
      let next ← free (Concrete.sequenceFin (roundLocal D (treeSimEmptyOpenPartial K D live ds k₂) r.2))
      pure (r.1, next, r.2))).run b.2) _
  rw [treeSim_emptyOpen_view K D live ds k₁ k₂]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support
    (treeSim_local_streamRel_fixed prims D δ _ a.2 b.2 hc))
  intro r₁ r₂ hr
  obtain ⟨hr, hs₁, hs₂⟩ := hr
  have reach : TreeSimReplyReachable prims D A a.1.1
      (treeSimEmptyOpenPartial K D live ds k₂) a.2 b.2 r₂.1.1 r₂.1.2 r₁.2 r₂.2 := by
    refine ⟨?_, hs₂⟩
    change (r₂.1, r₁.2) ∈ _
    rw [← hr.1]
    exact hs₁
  rw [hr.1]
  have cached₁' := (treeSim_logged_grows prims D _ a.2 r₁ hs₁) cached₁
  have cached₂' := (treeSim_stream_grows prims D _ b.2 r₂ hs₂) cached₂
  obtain ⟨localClose, hj, finish⟩ := close.next r₂.1.1 r₂.1.2 r₁.2 r₂.2 digest
    reach hr.2.1 hr.2.2.1 hr.2.2.2 cached₁' cached₂'
  apply relTriple_bind (treeSim_relTriple_support
    (localClose.all prims K D live ds r₂.1.2 k₁ k₂ r₁.2 r₂.2 hj digest cached₁' cached₂'))
  intro u z hz
  obtain ⟨hz, hsu, hsz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure (finish u z hsu hsz hz.1 hz.2.1)

/-! Nonempty replicated openings retain the real copy-hash calls and
agreement checks. The checked-batch invariant must still align held copies and
outgoing bundles after the simulator's T₀ correction. Unheld local copies need
not agree. Hash calls remain interleaved with continuations in driver order. -/

def treeSimOpenCopyHashes (count : ℕ) (v : Shares C Bit) : OracleComp (RoSpec C) (List HashOutput) :=
  C.terms.mapM fun T => hashQuery (.copy (vector count (v T)))

def treeSimOpenOut (i : C.Party) (count : ℕ) (v : Shares C Bit) (digests : List HashOutput) : Mail C E :=
  fun j => if j = i then none else some (.bundle [
    .bits ((C.terms.filter fun T => j ∉ C.holders T ∧ K.owner T = i).flatMap fun T => vector count (v T)),
    .hashes ((C.terms.zip digests).filterMap fun (T, d) =>
      if j ∉ C.holders T ∧ i ∈ C.holders T ∧ K.owner T ≠ i then some d else none)])

def treeSimOpenCopy (i : C.Party) (count : ℕ) (v : Shares C Bit) (inbox : Mail C E) : Shares C Bit :=
  fun T g => if i ∈ C.holders T then v T g else
    let owned := C.terms.filter fun T' => i ∉ C.holders T' ∧ K.owner T' = K.owner T
    Msg.bitAt (Msg.part (inbox (K.owner T)) 0) (count * owned.idxOf T + g)

def treeSimOpenStep {α : Type} (i : C.Party) (count : ℕ) (v : Shares C Bit)
    (digests : List HashOutput) (k : (ℕ → Bit) → PartyM C E RealSpec α) : Step C E RealSpec α :=
  .wait (treeSimOpenOut K i count v digests) (exchangeResume fun inbox => do
    let copy := treeSimOpenCopy K i count v inbox
    let copyDigests ← oracleStep (treeSimOpenCopyHashes count copy)
    require (TreeSimOpenValid K i inbox copyDigests)
    k (fun g => ∑ T, copy T g))

/-- The real opening prefix hashes every local copy before exposing its
bundle. This retains even unused hashes of terms the operator does not hold. -/
theorem treeSim_open_entry {α : Type} (ctx : Context C) (count : ℕ) (v : Shares C Bit)
    (k : (ℕ → Bit) → PartyM C E RealSpec α) :
    worldRoles.honest (advance ((openRep K ctx v count >>= k).run)) =
      (fun ds => treeSimOpenStep K ctx.self count v ds k) <$>
        free (liftComp (treeSimOpenCopyHashes count v) (LocalSpec C)) := by
  unfold openRep
  simp only [bind_assoc, pure_bind, worldRoles, advance_oracleStep_bind, free_bind,
    map_eq_bind_pure_comp]
  apply bind_congr
  intro ds
  simp only [advance_exchange_bind, free_pure]
  rfl

/-- After the prefix, unheld local copies are replaced by the received owner
copies. The prefix's hash-cache effects are not erased by this equation. -/
theorem treeSim_openCopy_congr (i : C.Party) (count : ℕ) (v w : Shares C Bit)
    (held : ∀ T, i ∈ C.holders T → v T = w T) (inbox : Mail C E) :
    treeSimOpenCopy K i count v inbox = treeSimOpenCopy K i count w inbox := by
  funext T g
  unfold treeSimOpenCopy
  split_ifs with h
  · exact congrFun (held T h) g
  · rfl

theorem treeSim_openStep_congr {α : Type} (i : C.Party) (count : ℕ) (v w : Shares C Bit)
    (ds es : List HashOutput) (k : (ℕ → Bit) → PartyM C E RealSpec α)
    (held : ∀ T, i ∈ C.holders T → v T = w T)
    (messages : treeSimOpenOut K i count v ds = treeSimOpenOut K i count w es) :
    treeSimOpenStep K i count v ds k = treeSimOpenStep K i count w es k := by
  unfold treeSimOpenStep
  rw [messages]
  congr 1
  funext inbox
  unfold exchangeResume
  simp only [treeSim_openCopy_congr K i count v w held]

/-- The simulator's correction cancels the internal T₀ shift on every held
term. The bounded shift is explicit, including the unrestricted return's tail. -/
theorem treeSim_open_shift_held (D : C.Coalition) (i : C.Party) (count : ℕ)
    (difference : ℕ → Bit) (v : Shares C Bit) (T : C.Term) (held : i ∈ C.holders T) :
    treeSimShift D (treeSimHeldShift D i count difference v)
      (fun g => if g < count then difference g else 0) T = v T := by
  funext g
  by_cases hT : lackedTerm D.1 = some T <;> by_cases hg : g < count
  · simp only [treeSimShift, if_pos hT, treeSimHeldShift, held, hg, hT, and_self, if_true]
    rw [add_assoc, bit_add_self, add_zero]
  · simp [treeSimShift, treeSimHeldShift, hT, hg]
  · simp [treeSimShift, treeSimHeldShift, hT, hg]
  · simp [treeSimShift, treeSimHeldShift, hT, hg]

/-- After the real prefix hashes, the T₀-corrected simulated opening has the
same suspended program once its transmitted bundles have been aligned. -/
theorem treeSim_open_shift_step {α : Type} (D : C.Coalition) (i : C.Party) (count : ℕ)
    (difference : ℕ → Bit) (v : Shares C Bit) (ds es : List HashOutput)
    (k : (ℕ → Bit) → PartyM C E RealSpec α)
    (messages : treeSimOpenOut K i count
      (treeSimShift D (treeSimHeldShift D i count difference v)
        (fun g => if g < count then difference g else 0)) ds = treeSimOpenOut K i count v es) :
    treeSimOpenStep K i count
      (treeSimShift D (treeSimHeldShift D i count difference v)
        (fun g => if g < count then difference g else 0)) ds k = treeSimOpenStep K i count v es k := by
  exact treeSim_openStep_congr K i count _ v ds es k
    (treeSim_open_shift_held D i count difference v) messages

/-- Canonical waiting programs use common held copies and outgoing bundles.
The saved continuations may differ. -/
def treeSimOpenPartial {α : Type} (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec α) : C.Party → Step C E RealSpec α :=
  fun i => if i ∈ D.1 then .done none else
    if live i then treeSimOpenStep K i count (v i) (ds i) (k i) else .done none

def treeSimOpenInbox (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) : Mail C E :=
  fun j => if j ∈ D.1 then sent j i else
    if live j then treeSimOpenOut K j count (v j) (ds j) i else some .abort

/-- This head includes transport abort, owner-copy reconstruction, copy hashes
and agreement checks. All malicious frames are decoded by the real protocol. -/
def treeSimOpenHead (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) : OracleComp (RoSpec C) (Option (ℕ → Bit)) :=
  if i ∈ D.1 then pure none else if live i then
    let inbox := treeSimOpenInbox K D live count v ds sent i
    if anyAbort inbox then pure none else do
      let copy := treeSimOpenCopy K i count (v i) inbox
      let copyDigests ← treeSimOpenCopyHashes count copy
      pure (if TreeSimOpenValid K i inbox copyDigests then some (fun g => ∑ T, copy T g) else none)
  else pure none

theorem treeSim_open_view (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (k₁ k₂ : C.Party → (ℕ → Bit) → PartyM C E RealSpec TreeOutput) :
    treeSimRoundView D (treeSimOpenPartial K D live count v ds k₁) =
      treeSimRoundView D (treeSimOpenPartial K D live count v ds k₂) := by
  funext j i
  simp only [treeSimRoundView, treeSimOpenPartial]
  split_ifs <;> rfl

theorem treeSim_open_local (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit)
    (ds : C.Party → List HashOutput) (k : C.Party → (ℕ → Bit) → PartyM C E RealSpec TreeOutput)
    (sent : C.Party → Mail C E) (i : C.Party) :
    free (roundLocal D (treeSimOpenPartial K D live count v ds k) sent i) = (do
      let out ← free (liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C))
      free (treeSimResume (k i) out)) := by
  have inbox : (fun j => if j ∈ D.1 then sent j i else
      (treeSimOpenPartial K D live count v ds k j).delivered i) =
      treeSimOpenInbox K D live count v ds sent i := by
    funext j
    by_cases hj : j ∈ D.1 <;> by_cases hl : live j = true <;>
      simp [treeSimOpenPartial, treeSimOpenStep, treeSimOpenInbox, Step.delivered, hj, hl]
  by_cases hi : i ∈ D.1
  · simp [roundLocal, treeSimOpenHead, treeSimOpenPartial, hi, treeSimResume,
      liftComp_pure, free_pure]
  · by_cases hl : live i = true
    · simp only [roundLocal, if_neg hi, treeSimOpenPartial, if_pos hl, treeSimOpenStep]
      simp only [treeSimOpenPartial, treeSimOpenStep] at inbox
      rw [inbox]
      unfold treeSimOpenHead
      rw [if_neg hi, if_pos hl]
      unfold exchangeResume anyAbort
      dsimp only
      split_ifs with habort
      · rfl
      · simp only [advance_oracleStep_bind, free_bind, liftComp_bind, liftComp_pure, free_pure,
          bind_assoc, pure_bind]
        apply bind_congr
        intro copyDigests
        unfold require
        split_ifs <;> simp [treeSimResume, pure_bind, free_pure] <;> rfl
    · simp [roundLocal, treeSimOpenPartial, treeSimOpenHead, hi, hl,
        treeSimResume, liftComp_pure, free_pure]

/-- Hash-only computations require equality only of the public caches.
Both private caches are retained exactly, with no relation assumed between them. -/
theorem treeSim_onHash_public_coupling {α : Type} (D : C.Coalition)
    (p : OracleComp (WorldSpec C) α) (m : StateT (HashCache C) ProbComp α)
    (hp : simulateQ (streamWorld prims D) p = onHash m)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C)
    (hc : a.1.1 = b.1) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) p).run a)
      ((simulateQ (streamWorld prims D) p).run b)
      (fun u z => u.1 = z.1 ∧ u.2.1.1 = z.2.1 ∧ u.2.1.2 = a.1.2 ∧ z.2.2 = b.2) := by
  rcases a with ⟨⟨h, c₁⟩, log⟩
  rcases b with ⟨h', c₂⟩
  cases hc
  have keepsHidden : ∀ u ∈ support ((simulateQ (treeSimLoggedWorld prims D) p).run ((h, c₁), log)),
      u.2.1.2 = c₁ := by
    intro u hu
    have hm : (u.1, u.2.1) ∈ support ((fun r => (r.1, r.2.1)) <$>
        (simulateQ (treeSimLoggedWorld prims D) p).run ((h, c₁), log)) := by
      rw [support_map]
      exact ⟨u, hu, rfl⟩
    rw [treeSimLoggedWorld_erase, hp] at hm
    simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hm
    obtain ⟨r, _, heq⟩ := hm
    exact (congrArg (fun x => x.2.2) heq).symm
  have e := congrArg (fun q => (fun r => (r.1, r.2.1, c₂)) <$> q)
    (treeSimLoggedWorld_erase prims D p (h, c₁) log)
  simp only [hp, onHash, StateT.run_mk, Functor.map_map] at e
  have he : (simulateQ (streamWorld prims D) p).run (h, c₂) =
      (fun u => (u.1, u.2.1.1, c₂)) <$>
        (simulateQ (treeSimLoggedWorld prims D) p).run ((h, c₁), log) := by
    simpa only [hp, onHash, StateT.run_mk] using e.symm
  rw [he]
  have hr : RelTriple
      (id <$> (simulateQ (treeSimLoggedWorld prims D) p).run ((h, c₁), log))
      ((fun u => (u.1, u.2.1.1, c₂)) <$> (simulateQ (treeSimLoggedWorld prims D) p).run ((h, c₁), log))
      (fun u z => u.1 = z.1 ∧ u.2.1.1 = z.2.1 ∧ u.2.1.2 = c₁ ∧ z.2.2 = c₂) := by
    apply relTriple_map
    apply relTriple_post_mono (treeSim_refl_support _)
    rintro u _ ⟨hu, rfl⟩
    have hprivate := keepsHidden u hu
    exact ⟨rfl, rfl, hprivate, rfl⟩
  simpa only [id_map] using hr

theorem treeSim_open_head_onHash (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (sent : C.Party → Mail C E) (i : C.Party) :
    ∃ m : StateT (HashCache C) ProbComp (Option (ℕ → Bit)),
      simulateQ (streamWorld prims D)
        (free (liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C))) = onHash m := by
  let copy := treeSimOpenCopy K i count (v i) (treeSimOpenInbox K D live count v ds sent i)
  have hp := treeSim_hashes_onHash prims D (C.terms.map fun T => Query.copy (vector count (copy T)))
  simp only [List.mapM_map, Function.comp_def] at hp
  unfold treeSimOpenHead
  dsimp only
  split_ifs
  · exact ⟨pure none, by simp [liftComp_pure, free_pure, treeSim_onHash_pure]⟩
  · exact ⟨pure none, by simp [liftComp_pure, free_pure, treeSim_onHash_pure]⟩
  · refine ⟨(C.terms.mapM fun T => hashAnswer prims (.copy (vector count (copy T)))) >>= fun copyDigests =>
      pure (if TreeSimOpenValid K i (treeSimOpenInbox K D live count v ds sent i) copyDigests
        then some (fun g => ∑ T, copy T g) else none), ?_⟩
    change simulateQ (streamWorld prims D) (free (liftComp (do
      let copyDigests ← treeSimOpenCopyHashes count copy
      pure (if TreeSimOpenValid K i (treeSimOpenInbox K D live count v ds sent i) copyDigests
        then some (fun g => ∑ T, copy T g) else none)) (LocalSpec C))) = _
    simp only [liftComp_bind, liftComp_pure, free_bind, free_pure, simulateQ_bind,
      simulateQ_pure, treeSimOpenCopyHashes, hp]
    rw [treeSim_onHash_bind]
    simp only [treeSim_onHash_pure]
  · exact ⟨pure none, by simp [liftComp_pure, free_pure, treeSim_onHash_pure]⟩

/-- Only supported successful reconstructions invoke a continuation coupling.
Public-cache agreement is needed before each operator's actual copy checks. -/
structure TreeSimOpenLocalClosure (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (k₁ k₂ : C.Party → (ℕ → Bit) → PartyM C E RealSpec TreeOutput) where
  J : TreeSimState C → (HashCache C × HiddenCache C) → Prop
  Q : C.Party → Step C E RealSpec TreeOutput → Step C E RealSpec TreeOutput → Prop
  cache : ∀ a b, J a b → a.1.1 = b.1
  head : ∀ i a b out u z, J a b →
    u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C)))).run a) →
    z ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C)))).run b) →
    u.1 = out → z.1 = out → u.2.1.1 = z.2.1 → u.2.1.2 = a.1.2 → z.2.2 = b.2 → J u.2 z.2
  abort : ∀ i, Q i (.done none) (.done none)
  continues : ∀ i a b out u z, J a b →
    u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
      (free (liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C)))).run a) →
    z ∈ support ((simulateQ (streamWorld prims D)
      (free (liftComp (treeSimOpenHead K D live count v ds sent i) (LocalSpec C)))).run b) →
    u.1 = some out → z.1 = some out → J u.2 z.2 →
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (advance (k₁ i out).run))).run u.2)
      ((simulateQ (streamWorld prims D) (free (advance (k₂ i out).run))).run z.2)
      (fun u z => Q i u.1 z.1 ∧ J u.2 z.2)

/-- The two heads make identical hash queries and agreement decisions, then
resume only their actual successful outputs. Malicious aborts remain synchronized. -/
theorem TreeSimOpenLocalClosure.local (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (k₁ k₂ : C.Party → (ℕ → Bit) → PartyM C E RealSpec TreeOutput)
    (close : TreeSimOpenLocalClosure prims K D live count v ds sent k₁ k₂)
    (i : C.Party) (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : close.J a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D)
      (free (roundLocal D (treeSimOpenPartial K D live count v ds k₁) sent i))).run a)
      ((simulateQ (streamWorld prims D)
      (free (roundLocal D (treeSimOpenPartial K D live count v ds k₂) sent i))).run b)
      (fun u z => close.Q i u.1 z.1 ∧ close.J u.2 z.2) := by
  rw [treeSim_open_local, treeSim_open_local]
  simp only [simulateQ_bind, StateT.run_bind]
  obtain ⟨m, hm⟩ := treeSim_open_head_onHash prims K D live count v ds sent i
  apply relTriple_bind (treeSim_relTriple_support
    (treeSim_onHash_public_coupling prims D _ m hm a b (close.cache a b h)))
  intro u z hz
  obtain ⟨⟨heq, hc, ha, hb⟩, hsu, hsz⟩ := hz
  have hj := close.head i a b z.1 u z h hsu hsz heq rfl hc ha hb
  rw [heq]
  cases hd : z.1 with
  | none =>
    simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure ⟨close.abort i, hj⟩
  | some out => exact close.continues i a b out u z h hsu hsz (heq.trans hd) hd hj

/-- Each operator's copy checks precede its continuation, preserving the
shared cache used by later operators. -/
theorem TreeSimOpenLocalClosure.all (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (k₁ k₂ : C.Party → (ℕ → Bit) → PartyM C E RealSpec TreeOutput)
    (close : TreeSimOpenLocalClosure prims K D live count v ds sent k₁ k₂)
    (a : TreeSimState C) (b : HashCache C × HiddenCache C) (h : close.J a b) :
    RelTriple ((simulateQ (treeSimLoggedWorld prims D)
      (free (Concrete.sequenceFin (roundLocal D (treeSimOpenPartial K D live count v ds k₁) sent)))).run a)
      ((simulateQ (streamWorld prims D)
      (free (Concrete.sequenceFin (roundLocal D (treeSimOpenPartial K D live count v ds k₂) sent)))).run b)
      (fun u z => (∀ i, close.Q i (u.1 i) (z.1 i)) ∧ close.J u.2 z.2) := by
  rw [free_sequenceFin, free_sequenceFin, simulateQ_sequenceFin, simulateQ_sequenceFin]
  exact treeSim_sequenceFin_rel _ _ close.J close.Q
    (fun i s t hst => close.local prims K D live count v ds sent k₁ k₂ i s t hst) a b h

/-- Terminal openings need no assumed continuation coupling. The relation
retains each party's actual common reconstruction, without asserting agreement
between different parties under malicious messages. -/
def TreeSimOpenLocalClosure.terminal (D : C.Coalition) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput) (sent : C.Party → Mail C E)
    (f₁ f₂ : C.Party → (ℕ → Bit) → TreeOutput) :
    TreeSimOpenLocalClosure prims K D live count v ds sent
      (fun i out => pure (f₁ i out)) (fun i out => pure (f₂ i out)) where
  J := fun a b => a.1.1 = b.1
  Q := fun i u z => (u = .done none ∧ z = .done none) ∨
    ∃ out, u = .done (some (f₁ i out)) ∧ z = .done (some (f₂ i out))
  cache := fun _ _ h => h
  head := by
    intro i a b out u z _ _ _ _ _ hc _ _
    exact hc
  abort := fun _ => Or.inl ⟨rfl, rfl⟩
  continues := by
    intro i a b out u z _ _ _ _ _ h
    change RelTriple (pure ((.done (some (f₁ i out)) : Step C E RealSpec TreeOutput), u.2))
      (pure ((.done (some (f₂ i out)) : Step C E RealSpec TreeOutput), z.2)) _
    exact relTriple_pure_pure ⟨Or.inr ⟨out, rfl, rfl⟩, h⟩

/-- A local invariant is selected after the actual common rushing response.
All later hashes and continuation effects are handled in their actual order. -/
structure TreeSimOpenClosure (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (δ : HiddenAddress C → Bit) (live : C.Party → Bool) (count : ℕ)
    (v : C.Party → Shares C Bit) (ds : C.Party → List HashOutput)
    (k₁ k₂ : C.Party → (ℕ → Bit) → PartyM C E RealSpec TreeOutput) (state₀ : A.State)
    (initial₁ : TreeSimState C) (initial₂ : HashCache C × HiddenCache C) where
  next : ∀ state sent a b,
    TreeSimReplyReachable prims D A state₀ (treeSimOpenPartial K D live count v ds k₂)
      initial₁ initial₂ state sent a b →
    TreeSimStreamRel δ a b → a.1.2 = initial₁.1.2 → b.2 = initial₂.2 →
    ∃ close : TreeSimOpenLocalClosure prims K D live count v ds sent k₁ k₂, close.J a b ∧
      ∀ (u : (C.Party → Step C E RealSpec TreeOutput) × TreeSimState C)
        (z : (C.Party → Step C E RealSpec TreeOutput) × (HashCache C × HiddenCache C)),
        u ∈ support ((simulateQ (treeSimLoggedWorld prims D)
          (free (Concrete.sequenceFin (roundLocal D (treeSimOpenPartial K D live count v ds k₁) sent)))).run a) →
        z ∈ support ((simulateQ (streamWorld prims D)
          (free (Concrete.sequenceFin (roundLocal D (treeSimOpenPartial K D live count v ds k₂) sent)))).run b) →
        (∀ i, close.Q i (u.1 i) (z.1 i)) → close.J u.2 z.2 →
        Bad u.2 ∨ Inv ((state, u.1), u.2) ((state, z.1), z.2)

/-- The checked-batch/T₀ alignment and entry-hash effects must establish
these actual waiting programs and shared public cache. They are not assumed
as a whole-round coupling. -/
def TreeSimOpenBoundary (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ δ live count v ds k₁ k₂, a.1.1 = b.1.1 ∧ TreeSimStreamRel δ a.2 b.2 ∧
    a.1.2 = treeSimOpenPartial K D live count v ds k₁ ∧ b.1.2 = treeSimOpenPartial K D live count v ds k₂ ∧
    Nonempty (TreeSimOpenClosure prims K D A Bad Inv δ live count v ds k₁ k₂ a.1.1 a.2 b.2)

/-- The replicated-opening stage includes the real rushing call, copy checks,
selective abort and the exact per-party continuation order. -/
theorem treeSim_open_preserves (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (stage : TreeSimConfig A (TreeSimState C) → TreeSimStage)
    (identify : ∀ a b, stage a = .openRep → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
      TreeSimOpenBoundary prims K D A Bad Inv a b) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A Bad Inv stage .openRep := by
  intro a b hg hinv hbad hdone
  obtain ⟨δ, live, count, v, ds, k₁, k₂, had, hc, ha, hb, ⟨close⟩⟩ := identify a b hg hinv hbad hdone
  change RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2) _
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [ha, hb, ← had, stepRound_real, stepRound_real]
  change RelTriple
    ((simulateQ (treeSimLoggedWorld prims D) (do
      let r ← worldRoles.adversary (A.round a.1.1 (treeSimRoundView D (treeSimOpenPartial K D live count v ds k₁)))
      let next ← free (Concrete.sequenceFin (roundLocal D (treeSimOpenPartial K D live count v ds k₁) r.2))
      pure (r.1, next, r.2))).run a.2)
    ((simulateQ (streamWorld prims D) (do
      let r ← worldRoles.adversary (A.round a.1.1 (treeSimRoundView D (treeSimOpenPartial K D live count v ds k₂)))
      let next ← free (Concrete.sequenceFin (roundLocal D (treeSimOpenPartial K D live count v ds k₂) r.2))
      pure (r.1, next, r.2))).run b.2) _
  rw [treeSim_open_view K D live count v ds k₁ k₂]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_relTriple_support
    (treeSim_local_streamRel_fixed prims D δ _ a.2 b.2 hc))
  intro r₁ r₂ hr
  obtain ⟨hr, hs₁, hs₂⟩ := hr
  have reach : TreeSimReplyReachable prims D A a.1.1
      (treeSimOpenPartial K D live count v ds k₂) a.2 b.2 r₂.1.1 r₂.1.2 r₁.2 r₂.2 := by
    refine ⟨?_, hs₂⟩
    change (r₂.1, r₁.2) ∈ _
    rw [← hr.1]
    exact hs₁
  rw [hr.1]
  obtain ⟨localClose, hj, finish⟩ := close.next r₂.1.1 r₂.1.2 r₁.2 r₂.2
    reach hr.2.1 hr.2.2.1 hr.2.2.2
  apply relTriple_bind (treeSim_relTriple_support
    (localClose.all prims K D live count v ds r₂.1.2 k₁ k₂ r₁.2 r₂.2 hj))
  intro u z hz
  obtain ⟨hz, hsu, hsz⟩ := hz
  simp only [simulateQ_pure, StateT.run_pure]
  exact relTriple_pure_pure (finish u z hsu hsz hz.1 hz.2)

/-- The real distinguisher continues from the last round's actual log and caches. -/
def treeSimRealObserve (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (out : TreeSimRoundOutput A (TreeSimState C)) :
    ProbComp (Bool × TreeSimLog C) :=
  (fun r => (r.1, r.2.2)) <$>
    (simulateQ (treeSimLoggedWorld prims D) (worldRoles.adversary (Z out.1))).run out.2

/-- Final adversarial observation extends the same real transcript. -/
theorem treeSim_observe_prefix (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (a : TreeSimRoundOutput A (TreeSimState C))
    (x : Bool × TreeSimLog C) (hx : x ∈ support (treeSimRealObserve prims D A Z a)) :
    a.2.2 <+: x.2 := by
  simp only [treeSimRealObserve, support_map, Set.mem_image] at hx
  obtain ⟨r, hr, rfl⟩ := hx
  exact treeSimLoggedWorld_prefix prims D _ a.2 r hr

/-- The ideal distinguisher receives exactly the selective-abort output of Ftree. -/
def treeSimIdealObserve (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (dealt : Option TreeOutput)
    (out : TreeSimRoundOutput A (HashCache C × HiddenCache C)) : ProbComp Bool :=
  (simulateQ (localAnswer prims) (Z (out.1.1, fun i =>
    if i ∉ D.1 ∧ (out.1.2 i).isSome then dealt else none))).run' out.2.1

/-- A sufficient terminating relation when hash caches have been synchronized.
This is not imposed on the general stage invariant: dummy-seed PRF queries
can otherwise leave different cache domains. -/
def TreeSimFinalRel (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (dealt : Option TreeOutput) (a : TreeSimRoundOutput A (TreeSimState C))
    (b : TreeSimRoundOutput A (HashCache C × HiddenCache C)) : Prop :=
  a.1.1 = b.1.1 ∧ a.2.1.1 = b.2.1 ∧
    a.1.2 = fun i => if i ∉ D.1 ∧ (b.1.2 i).isSome then dealt else none

/-- From the concrete final relation, every distinguisher has the same output
law. Its local queries use the shared hash cache, never the hidden stream cache. -/
theorem treeSim_observe_marginal (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (dealt : Option TreeOutput)
    (a : TreeSimRoundOutput A (TreeSimState C)) (b : TreeSimRoundOutput A (HashCache C × HiddenCache C))
    (h : TreeSimFinalRel D A dealt a b) :
    Prod.fst <$> treeSimRealObserve prims D A Z a = treeSimIdealObserve prims D A Z dealt b := by
  have e := congrArg (fun p => Prod.fst <$> p)
    (treeSimLoggedWorld_erase prims D (worldRoles.adversary (Z a.1)) a.2.1 a.2.2)
  simp only [Functor.map_map, treeSim_stream_adversary, onHash, StateT.run_mk] at e
  unfold treeSimRealObserve treeSimIdealObserve
  simp only [Functor.map_map, StateT.run'_eq]
  rw [e]
  rcases h with ⟨hst, hcache, hout⟩
  rw [hcache, show a.1 = (b.1.1, fun i => if i ∉ D.1 ∧ (b.1.2 i).isSome then dealt else none) from
    Prod.ext hst hout]

/-- The final adversarial interaction couples exactly under the sufficient
relation above. Other final cache relations use `observeGood` instead. -/
theorem treeSim_observe_good (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Z : Distinguisher C A.State TreeOutput) (dealt : Option TreeOutput)
    (a : TreeSimRoundOutput A (TreeSimState C)) (b : TreeSimRoundOutput A (HashCache C × HiddenCache C))
    (h : TreeSimFinalRel D A dealt a b) :
    RelTriple (treeSimRealObserve prims D A Z a) (treeSimIdealObserve prims D A Z dealt b)
      (fun x y => x.1 = y) := by
  rw [← treeSim_observe_marginal prims D A Z dealt a b h]
  have hr : RelTriple (id <$> treeSimRealObserve prims D A Z a)
      (Prod.fst <$> treeSimRealObserve prims D A Z a) (fun x y => x.1 = y) := by
    apply relTriple_map
    exact relTriple_post_mono (relTriple_refl _) (fun _ _ h => congrArg Prod.fst h)
  simpa only [id_map] using hr

theorem treeSimRealFinish_rounds (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (state : A.State) (s : TreeSimState C) :
    treeSimRealFinish prims K circuits settings top tree D A x Z state s =
      (executePhase (treeSimRealRoles prims D) D A noFunctionality (ceremonyFuel circuits settings) state
        (fun i => ceremony K circuits settings i (x i) top tree)).run s >>= treeSimRealObserve prims D A Z := by
  simp only [treeSimRealFinish, simulateQ_bind, simulateQ_executePhase,
    treeSimRealRoles, StateT.run_bind, map_bind]
  rfl

theorem treeSimIdealFinish_rounds (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (Z : Distinguisher C A.State TreeOutput)
    (state : A.State) (dealt : Option TreeOutput × List (List (List Bit))) (h : HashCache C) :
    (treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z state dealt).run' h =
      (executePhase (treeSimIdealRoles prims D) D A noFunctionality (ceremonyFuel circuits settings) state
        (treeSimProgram K circuits settings D parameter (fun T => if KnownTo D.1 T then seeds T else 0)
          dealt.2 top tree)).run (h, ∅) >>= treeSimIdealObserve prims D A Z dealt.1 := by
  simp only [treeSimIdealFinish, treeSimStreamPhase, treeSimIdealRoles,
    simulateQ_executePhase, StateT.run'_eq, StateT.run_bind, StateT.run_mk,
    StateT.run_pure, map_bind, pure_bind, bind_assoc]
  congr 1
  funext out
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- A phase followed by arbitrary local observation, without any programming interface. -/
def treeSimLocalFinish {α : Type} (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E RealSpec TreeOutput)
    (finish : (A.State × (C.Party → Option TreeOutput)) → OracleComp (LocalSpec C) α) :
    OracleComp (LocalSpec C + LocalSpec C) α := do
  let out ← executePhase treeSimLocalRoles D A noFunctionality fuel state program
  treeSimLocalRoles.adversary (finish out)

theorem treeSimLocalFinish_eq {α : Type} (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (fuel : ℕ) (state : A.State) (program : C.Party → PartyM C E RealSpec TreeOutput)
    (finish : (A.State × (C.Party → Option TreeOutput)) → OracleComp (LocalSpec C) α) :
    simulateQ treeSimLocalWorld (treeSimLocalFinish D A fuel state program finish) = (do
      let out ← executePhase worldRoles D A noFunctionality fuel state program
      worldRoles.adversary (finish out)) := by
  simp only [treeSimLocalFinish, simulateQ_bind, treeSimLocalWorld_adversary]
  rw [treeSim_hom_phase (fun p => simulateQ treeSimLocalWorld p)
    (fun a => simulateQ_pure _ a) (fun p k => simulateQ_bind _ p k)
    treeSimLocalRoles worldRoles (fun p => treeSimLocalWorld_adversary p)
    (fun p => treeSimLocalWorld_honest p)]

/-- Prequerying an ignored local computation preserves a nonprogramming run
and its real log. The padding queries themselves are ghost queries. -/
theorem treeSim_logged_padding {α β : Type} (D : C.Coalition)
    (padding : OracleComp (LocalSpec C) α) (p : OracleComp (LocalSpec C + LocalSpec C) β)
    (s : TreeSimState C) :
    𝒟[do
        let r ← (simulateQ (localAnswer prims) padding).run s.1.1
        (fun out : β × TreeSimState C => (out.1, out.2.2)) <$>
            (simulateQ (treeSimLoggedWorld prims D) (simulateQ treeSimLocalWorld p)).run ((r.2, s.1.2), s.2)] =
      𝒟[(fun out : β × TreeSimState C => (out.1, out.2.2)) <$>
        (simulateQ (treeSimLoggedWorld prims D) (simulateQ treeSimLocalWorld p)).run s] := by
  rcases s with ⟨⟨hcache, c⟩, log⟩
  have h := treeSim_dealer_prefix prims D padding (treeSimLocalLogged p) (hcache, c)
  have e := congrArg (fun d => (fun r => (r.1, log ++ r.2)) <$> d) h
  simp only [onHash, StateT.run'_eq, StateT.run_bind, StateT.run_mk, bind_map_left,
    map_bind] at e
  simp only [← evalDist_map, map_bind, Functor.map_map] at e
  simpa only [treeSimLoggedWorld_run, treeSimLocalLogged_run, Functor.map_map] using e

/-- The same ghost padding may be inserted before the actual real suffix,
with no change to acceptance or the classified query log. -/
theorem treeSimRealFinish_padding (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C)
    (Z : Distinguisher C A.State TreeOutput) (state : A.State) (s : TreeSimState C)
    (padding : OracleComp (LocalSpec C) Unit) :
    𝒟[do
        let r ← (simulateQ (localAnswer prims) padding).run s.1.1
        treeSimRealFinish prims K circuits settings top tree D A x Z state ((r.2, s.1.2), s.2)] =
      𝒟[treeSimRealFinish prims K circuits settings top tree D A x Z state s] := by
  simpa only [treeSimLocalFinish_eq, treeSimRealFinish] using treeSim_logged_padding prims D padding
    (treeSimLocalFinish D A (ceremonyFuel circuits settings) state
      (fun i => ceremony K circuits settings i (x i) top tree) Z) s

/-- Normalize the ideal suffix as a nonprogramming local phase. -/
theorem treeSimIdealFinish_local (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (Z : Distinguisher C A.State TreeOutput) (state : A.State)
    (dealt : Option TreeOutput × List (List (List Bit))) (h : HashCache C) :
    (treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z state dealt).run' h =
      (simulateQ (streamWorld prims D) (simulateQ treeSimLocalWorld
        (treeSimLocalFinish D A (ceremonyFuel circuits settings) state
          (treeSimProgram K circuits settings D parameter (fun T => if KnownTo D.1 T then seeds T else 0)
            dealt.2 top tree)
          (fun out => Z (out.1, fun i => if i ∉ D.1 ∧ (out.2 i).isSome then dealt.1 else none))))).run' (h, ∅) := by
  rw [treeSimIdealFinish_rounds, treeSimLocalFinish_eq]
  simp only [simulateQ_bind, simulateQ_executePhase, treeSimIdealRoles, StateT.run'_eq,
    StateT.run_bind, map_bind]
  apply bind_congr'
  intro out
  simp only [treeSimIdealObserve, treeSim_stream_adversary, onHash, StateT.run'_eq,
    StateT.run_mk, Functor.map_map]

/-- Padding the ideal suffix is exact as well. This permits dummy-seed PRF
queries to be sampled in a common prefix instead of requiring equal sparse caches. -/
theorem treeSimIdealFinish_padding (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
    (Z : Distinguisher C A.State TreeOutput) (state : A.State)
    (dealt : Option TreeOutput × List (List (List Bit))) (h : HashCache C)
    (padding : OracleComp (LocalSpec C) Unit) :
    𝒟[do
        let r ← (simulateQ (localAnswer prims) padding).run h
        (treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z state dealt).run' r.2] =
      𝒟[(treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z state dealt).run' h] := by
  simp only [treeSimIdealFinish_local]
  have e := treeSim_dealer_prefix prims D padding
    (treeSimLocalFinish D A (ceremonyFuel circuits settings) state
      (treeSimProgram K circuits settings D parameter (fun T => if KnownTo D.1 T then seeds T else 0) dealt.2 top tree)
      (fun out => Z (out.1, fun i => if i ∉ D.1 ∧ (out.2 i).isSome then dealt.1 else none))) (h, ∅)
  simpa only [onHash, StateT.run'_eq, StateT.run_bind, StateT.run_mk, bind_map_left, map_bind] using e

/-- The complete setup subroutine, including all rushing rounds and aborts,
couples exactly with the actual emulator. This pays no PRSS-key bad event. -/
theorem treeSim_prssSetup_allRounds (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (fuel : ℕ) (state : A.State)
    (cache : HashCache C × HiddenCache C) :
    RelTriple
      ((simulateQ (streamWorld prims D) (executePhase worldRoles D A noFunctionality fuel state
        (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C))))).run cache)
      ((treeSimEvaluate prims (treeSimErase (executePhase (emulatedRoles D) D A noFunctionality fuel state
        (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))))).run cache) Eq := by
  rw [treeSimErase_phase, treeSimEvaluate_phase]
  exact relTriple_refl _

/-- The two ceremonies both begin with exactly the fresh real PRSS setup. -/
theorem treeSim_real_setup (top : TopTree) (tree : Tree) (x : C.Party → Keys C) :
    ∃ k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput,
      ∀ i, ceremony K circuits settings i (x i) top tree = prssSetup i >>= k i := by
  unfold ceremony ceremonyWith
  exact ⟨_, fun _ => rfl⟩

theorem treeSim_ideal_setup (top : TopTree) (tree : Tree) (D : C.Coalition)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (openings : List (List (List Bit))) :
    ∃ k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput,
      ∀ i, treeSimProgram K circuits settings D parameter seeds openings top tree i = prssSetup i >>= k i := by
  unfold treeSimProgram ceremonyWith
  exact ⟨_, fun _ => rfl⟩

/-- Attach a ceremony continuation to the real setup's first suspended step. -/
def treeSimSetupStep (k : PrssKeys C → PartyM C E RealSpec TreeOutput)
    (i : C.Party) (data : Parts C × List HashOutput) : Step C E RealSpec TreeOutput :=
  .wait (commitOutbox i data.2) (fun inbox =>
    (OptionT.mk ((exchangeResume fun committed => do
      let revealed ← exchange (prssRevealOutbox data.1 i)
      prssPostReveal i data.1 committed revealed) inbox) >>= k).run)

def treeSimSetupSteps (D : C.Coalition)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (data : C.Party → Parts C × List HashOutput) : C.Party → Step C E RealSpec TreeOutput :=
  fun i => if i ∈ D.1 then .done none else treeSimSetupStep (k i) i (data i)

/-- Starting any continuation of setup performs the same real sampling and
commitment queries; only the suspended continuations differ. -/
theorem treeSim_startSetup (D : C.Coalition)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) :
    startSteps worldRoles D (fun i => prssSetup i >>= k i) =
      treeSimSetupSteps D k <$> free (prssInitialData D) := by
  unfold startSteps prssInitialData
  rw [free_sequenceFin, map_eq_bind_pure_comp]
  change _ = Concrete.sequenceFin _ >>= fun rows => pure (treeSimSetupSteps D k rows)
  unfold treeSimSetupSteps
  rw [← sequenceFin_bind_pure _ (fun i (row : Parts C × List HashOutput) =>
    if i ∈ D.1 then Step.done (E := E) (G := RealSpec) (α := TreeOutput) none
    else treeSimSetupStep (k i) i row)]
  congr 1
  funext i
  by_cases hi : i ∈ D.1
  · simp [hi]
  · simp only [if_neg hi, worldRoles, advance_bind, advance_prssSetup_run,
      bind_assoc, pure_bind, free_bind, free_pure, treeSimSetupStep,
      prssCommitStep, continueStep]

def treeSimRealCont (top : TopTree) (tree : Tree) (x : C.Party → Keys C) :
    C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput :=
  fun i prss => ceremonyAfterSetup K circuits settings ⟨i, x i, prss⟩ top tree

/-- The explicit simulator suffix, retaining its label and batch counters. -/
def treeSimIdealCont (top : TopTree) (tree : Tree) (D : C.Coalition)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (openings : List (List (List Bit)))
    (i : C.Party) (prss : PrssKeys C) : PartyM C E RealSpec TreeOutput := do
  let ctx : Context C := ⟨i, ⟨parameter, seeds, fun _ => 0⟩, prss⟩
  let some output ← (ceremonyOutput (m := StateT (ℕ × ℕ) (PartyM C E RealSpec))
    (fun oa => StateT.lift (oracleStep (tweakable oa))) parameter
    (batched settings.batchSize fun jobs => do
      let (label, k) ← get
      let inputs ← StateT.lift (jobs.mapM (inputShares ctx))
      let (outputs, state) ← StateT.lift ((runJobs K
        (treeSimGadgets K circuits settings D parameter seeds openings ctx k jobs)
        (jobs.map (circuits parameter ·.kind)) inputs).run ⟨fun _ => [], label, k⟩)
      set (state.label, k + 1)
      pure (some outputs)) top tree).run' (0, 0) | failure
  pure output

theorem treeSim_real_cont (top : TopTree) (tree : Tree) (x : C.Party → Keys C) (i : C.Party) :
    ceremony K circuits settings i (x i) top tree = prssSetup i >>= treeSimRealCont K circuits settings top tree x i := rfl

theorem treeSim_ideal_cont (top : TopTree) (tree : Tree) (D : C.Coalition)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (openings : List (List (List Bit))) (i : C.Party) :
    treeSimProgram K circuits settings D parameter seeds openings top tree i =
      prssSetup i >>= treeSimIdealCont K circuits settings top tree D parameter seeds openings i := rfl

private theorem treeSim_start_transport {σ : Type}
    (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp)) (D : C.Coalition)
    (program : C.Party → PartyM C E RealSpec TreeOutput) :
    startSteps (simRoles impl worldRoles) D program = simulateQ impl (startSteps worldRoles D program) := by
  simp only [startSteps, simulateQ_sequenceFin]
  congr 1
  funext i
  split_ifs <;> simp [simRoles]

/-- Exact coupling of the real setup draws, including the commitment hash
queries and the dealer's incoming cache. Only membership in the later
ceremony invariant remains to be checked at the resulting suspended steps. -/
theorem treeSim_startSetup_coupling (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (s : TreeSimState C)
    (ka kb : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (R : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (hR : ∀ r ∈ support ((simulateQ (treeSimLoggedWorld prims D) (free (prssInitialData D))).run s),
      R ((state, treeSimSetupSteps D ka r.1), r.2) ((state, treeSimSetupSteps D kb r.1), r.2.1)) :
    RelTriple
      ((startSteps (treeSimRealRoles prims D) D (fun i => prssSetup i >>= ka i)).run s)
      ((startSteps (treeSimIdealRoles prims D) D (fun i => prssSetup i >>= kb i)).run s.1)
      (fun a b => R ((state, a.1), a.2) ((state, b.1), b.2)) := by
  simp only [treeSimRealRoles, treeSimIdealRoles, treeSim_start_transport, treeSim_startSetup,
    simulateQ_map, StateT.run_map]
  rw [← treeSimLoggedWorld_erase prims D (free (prssInitialData D)) s.1 s.2]
  simp only [Functor.map_map]
  apply relTriple_map
  apply relTriple_post_mono (treeSim_refl_support _)
  rintro a _ ⟨ha, rfl⟩
  exact hR a ha

/-- Start the next local computation only for operators that completed setup. -/
def treeSimContinue (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (keys : C.Party → Option (PrssKeys C)) : OracleComp (WorldSpec C) (C.Party → Step C E RealSpec TreeOutput) :=
  free (Concrete.sequenceFin fun i => continueStep (k i) (.done (keys i)))

/-- The same three setup rounds precede both continuations, under any handler. -/
theorem treeSim_prssSetup_split {σ : Type} (impl : QueryImpl (WorldSpec C) (StateT σ ProbComp))
    (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (fuel : ℕ)
    (k : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput) :
    executePhase (simRoles impl worldRoles) D A noFunctionality (fuel + 3) state
      (fun i => prssSetup i >>= k i) = (do
      let p ← executePhase (simRoles impl worldRoles) D A noFunctionality 3 state
        (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))
      let next ← simulateQ impl (treeSimContinue k p.2)
      executeRounds (simRoles impl worldRoles) D A noFunctionality fuel p.1 next) := by
  rw [← simulateQ_executePhase, executePhase_prssSetup_bind]
  simp only [simulateQ_bind, simulateQ_executePhase, simulateQ_executeRounds, treeSimContinue]

/-- Exact coupling of the complete setup prefix, followed by arbitrary
related continuations. No hash bad event is spent on the shared PRSS keys. -/
theorem treeSim_prssSetup_continuations (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (fuel : ℕ) (s : TreeSimState C)
    (ka kb : C.Party → PrssKeys C → PartyM C E RealSpec TreeOutput)
    (R : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (Q : TreeSimRoundOutput A (TreeSimState C) → TreeSimRoundOutput A (HashCache C × HiddenCache C) → Prop)
    (entry : ∀ p ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 state
        (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s),
      RelTriple
        ((simulateQ (treeSimLoggedWorld prims D) (treeSimContinue ka p.1.2)).run p.2)
        ((simulateQ (streamWorld prims D) (treeSimContinue kb p.1.2)).run p.2.1)
        (fun a b => R ((p.1.1, a.1), a.2) ((p.1.1, b.1), b.2)))
    (rounds : ∀ a b, R a b → RelTriple
      ((executeRounds (treeSimRealRoles prims D) D A noFunctionality fuel a.1.1 a.1.2).run a.2)
      ((executeRounds (treeSimIdealRoles prims D) D A noFunctionality fuel b.1.1 b.1.2).run b.2) Q) :
    RelTriple
      ((executePhase (treeSimRealRoles prims D) D A noFunctionality (fuel + 3) state
        (fun i => prssSetup i >>= ka i)).run s)
      ((executePhase (treeSimIdealRoles prims D) D A noFunctionality (fuel + 3) state
        (fun i => prssSetup i >>= kb i)).run s.1) Q := by
  have erased := treeSimLoggedWorld_erase prims D
    (executePhase worldRoles D A noFunctionality 3 state
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))) s.1 s.2
  simp only [simulateQ_executePhase] at erased
  simp only [treeSimRealRoles, treeSimIdealRoles, treeSim_prssSetup_split, StateT.run_bind]
  rw [← erased, bind_map_left]
  apply relTriple_bind (treeSim_refl_support _)
  rintro p _ ⟨hp, rfl⟩
  apply relTriple_bind (entry p hp)
  intro a b hab
  exact rounds ((p.1.1, a.1), a.2) ((p.1.1, b.1), b.2) hab

/-- The shared prefix cannot write to the private honest stream cache. -/
theorem treeSimCommonPrefix_hidden (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (p : (Option TreeOutput × List (List (List Bit))) × (A.State × TreeSimState C))
    (hp : p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z)) :
    p.2.2.1.2 = ∅ := by
  simp only [treeSimCommonPrefix, support_bind, Set.mem_iUnion, support_pure, Set.mem_singleton_iff] at hp
  obtain ⟨d, hd, st, hst, rfl⟩ := hp
  have hm : (st.1, st.2.1) ∈ support
      ((fun r => (r.1, r.2.1)) <$> (simulateQ (treeSimLoggedWorld prims D)
        (worldRoles.adversary (A.start (corruptInputs D (dealtKeys parameter seeds pairs)) z))).run ((d.2, ∅), [])) := by
    rw [support_map]
    exact ⟨st, hst, rfl⟩
  rw [treeSimLoggedWorld_erase, treeSim_stream_adversary] at hm
  simp only [onHash, StateT.run_mk, support_map, Set.mem_image] at hm
  obtain ⟨r, _, heq⟩ := hm
  exact (congrArg (fun x => x.2.2) heq).symm

/-- The two synchronous rounds left inside `check` after its Coin and
ExtendMult rounds have been assigned their own stages. -/
inductive TreeSimCheckKind (C : Committee) (E : Type) where
  | digests (ds : C.Party → List HashOutput)
  | opening (v : C.Party → ℕ → E)

def treeSimCheckOut (kind : TreeSimCheckKind C E) (i : C.Party) : Mail C E :=
  match kind with
  | .digests ds => digestOutbox i (ds i)
  | .opening v => openOutbox i (v i)

def TreeSimCheckAccept (kind : TreeSimCheckKind C E) (i : C.Party) (inbox : Mail C E) : Prop :=
  match kind with
  | .digests ds => DigestsAgree i (ds i) inbox
  | .opening v => OpenAgrees K i (v i) inbox ∧
      openValue K i (v i) inbox 0 * openValue K i (v i) inbox 1 = openValue K i (v i) inbox 2

def treeSimCheckStep {α : Type} (kind : TreeSimCheckKind C E) (i : C.Party)
    (k : PartyM C E RealSpec α) : Step C E RealSpec α :=
  .wait (treeSimCheckOut kind i) (exchangeResume fun inbox =>
    require (TreeSimCheckAccept K kind i inbox) >>= fun _ => k)

/-- The real digest entry, retaining both history and salted-digest queries. -/
theorem treeSim_digest_entry {α : Type} (ctx : Context C) (salts : Shares C Bit)
    (st : RunState C) (k : Unit × RunState C → PartyM C E RealSpec α) :
    worldRoles.honest (advance (((compareDigests ctx salts).run st >>= k).run)) =
      (fun ds => treeSimCheckStep K (.digests (fun _ => ds)) ctx.self (k ((), st))) <$>
        free (liftComp (digestQuery ctx.self salts st.history) (LocalSpec C)) := by
  have run : (compareDigests ctx salts).run st >>= k =
      (oracleStep (digestQuery ctx.self salts st.history) >>= fun ds =>
        exchange (digestOutbox ctx.self ds) >>= fun inbox =>
          require (DigestsAgree ctx.self ds inbox) >>= fun _ => k ((), st)) := by
    simp only [compareDigests, StateT.run_bind, StateT.run_lift, StateT.run_get,
      bind_assoc, pure_bind, StateT.run_pure]
    rfl
  rw [run]
  simp only [worldRoles, advance_oracleStep_bind, free_bind, advance_exchange_bind,
    free_pure, map_eq_bind_pure_comp]
  rfl

/-- The final check includes both Shamir consistency and the multiplication
identity, before the subsequent ceremony program is resumed. -/
theorem treeSim_check_open_entry {α : Type} (ctx : Context C) (v : ℕ → E)
    (k : PartyM C E RealSpec α) :
    advance ((openSh K ctx v 3 >>= fun opened =>
      require (opened 0 * opened 1 = opened 2) >>= fun _ => k).run) =
      pure (treeSimCheckStep K (.opening (fun _ => v)) ctx.self k) := by
  have run : (openSh K ctx v 3 >>= fun opened =>
      require (opened 0 * opened 1 = opened 2) >>= fun _ => k) =
      (exchange (openOutbox ctx.self v) >>= fun inbox =>
        require (TreeSimCheckAccept K (.opening (fun _ => v)) ctx.self inbox) >>= fun _ => k) := by
    have merge (p q : Prop) :
        (require p >>= fun _ => require q >>= fun _ => k) =
          (require (p ∧ q) >>= fun _ => k) := by
      by_cases hp : p <;> by_cases hq : q <;> simp [require, hp, hq]
    unfold openSh
    simp only [bind_assoc, pure_bind]
    change (exchange (openOutbox ctx.self v) >>= fun inbox =>
      require (OpenAgrees K ctx.self v inbox) >>= fun _ =>
        require (openValue K ctx.self v inbox 0 * openValue K ctx.self v inbox 1 =
          openValue K ctx.self v inbox 2) >>= fun _ => k) = _
    apply congrArg (fun f => exchange (openOutbox ctx.self v) >>= f)
    funext inbox
    exact merge _ _
  rw [run, advance_exchange_bind]
  rfl

/-- `live` also records prior honest aborts; they remain `.done none`. -/
def treeSimCheckWaiting {α : Type} (D : C.Coalition) (live : C.Party → Bool)
    (kind : TreeSimCheckKind C E) (k : C.Party → PartyM C E RealSpec α) :
    C.Party → Step C E RealSpec α := fun i =>
  if i ∈ D.1 then .done none else if live i then treeSimCheckStep K kind i (k i) else .done none

def treeSimCheckView (D : C.Coalition) (live : C.Party → Bool) (kind : TreeSimCheckKind C E) :
    C.Party → C.Party → Option (Msg E) := fun c i =>
  if c ∈ D.1 ∧ i ∉ D.1 ∧ live i then treeSimCheckOut kind i c else none

def treeSimCheckInbox (D : C.Coalition) (live : C.Party → Bool) (kind : TreeSimCheckKind C E)
    (sent : C.Party → Mail C E) (i : C.Party) : Mail C E := fun j =>
  if j ∈ D.1 then sent j i else if live j then treeSimCheckOut kind j i else some .abort

def treeSimCheckResult (D : C.Coalition) (live : C.Party → Bool) (kind : TreeSimCheckKind C E)
    (sent : C.Party → Mail C E) (i : C.Party) : Option Unit :=
  if i ∈ D.1 then none else if live i then
    if anyAbort (treeSimCheckInbox D live kind sent i) then none else
      if TreeSimCheckAccept K kind i (treeSimCheckInbox D live kind sent i) then some () else none
    else none

theorem treeSim_check_waiting_view {α : Type} (D : C.Coalition) (live : C.Party → Bool)
    (kind : TreeSimCheckKind C E) (k : C.Party → PartyM C E RealSpec α) :
    treeSimRoundView D (treeSimCheckWaiting K D live kind k) = treeSimCheckView D live kind := by
  funext c i
  unfold treeSimRoundView treeSimCheckWaiting treeSimCheckView
  by_cases hi : i ∈ D.1 <;> by_cases hc : c ∈ D.1 <;> by_cases hl : live i = true <;>
    simp [hi, hc, hl, treeSimCheckStep, Step.outbox]

theorem treeSim_check_local {α : Type} (D : C.Coalition) (live : C.Party → Bool)
    (kind : TreeSimCheckKind C E) (k : C.Party → PartyM C E RealSpec α)
    (sent : C.Party → Mail C E) (i : C.Party) :
    roundLocal D (treeSimCheckWaiting K D live kind k) sent i =
      treeSimResume (fun (_ : Unit) => k i) (treeSimCheckResult K D live kind sent i) := by
  have hin : (fun j => if j ∈ D.1 then sent j i else
      (treeSimCheckWaiting K D live kind k j).delivered i) = treeSimCheckInbox D live kind sent i := by
    funext j
    by_cases hj : j ∈ D.1 <;> by_cases hl : live j = true <;>
      simp [hj, hl, treeSimCheckWaiting, treeSimCheckInbox, treeSimCheckStep, Step.delivered]
  by_cases hi : i ∈ D.1
  · simp [roundLocal, treeSimCheckWaiting, treeSimCheckResult, hi, treeSimResume]
  · by_cases hl : live i = true
    · simp only [roundLocal, treeSimCheckWaiting, if_neg hi, if_pos hl, treeSimCheckStep]
      simp only [treeSimCheckWaiting, treeSimCheckStep] at hin
      rw [hin]
      unfold treeSimCheckResult
      rw [if_neg hi, if_pos hl]
      unfold exchangeResume anyAbort require
      split_ifs <;> simp_all [treeSimResume] <;> rfl
    · simp [roundLocal, treeSimCheckWaiting, treeSimCheckResult, hi, hl, treeSimResume]

/-- One common rushing call, followed by the actual abort/test decisions and
ordered continuations. This covers both check rounds and partial entries. -/
theorem treeSim_check_round_factor {α : Type} (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (state : A.State) (live : C.Party → Bool)
    (kind : TreeSimCheckKind C E) (k : C.Party → PartyM C E RealSpec α) :
    stepRound worldRoles D A noFunctionality state (treeSimCheckWaiting K D live kind k) = (do
      let b ← worldRoles.adversary (A.round state (treeSimCheckView D live kind))
      let next ← treeSimResumeAll (fun i (_ : Unit) => k i) (treeSimCheckResult K D live kind b.2)
      pure (b.1, next, b.2)) := by
  rw [stepRound_real]
  change (do
    let b ← worldRoles.adversary (A.round state (treeSimRoundView D (treeSimCheckWaiting K D live kind k)))
    let next ← free (Concrete.sequenceFin (roundLocal D (treeSimCheckWaiting K D live kind k) b.2))
    pure (b.1, next, b.2)) = _
  rw [treeSim_check_waiting_view]
  apply bind_congr
  intro b
  congr 1
  congr 1
  congr 1
  funext i
  exact treeSim_check_local K D live kind k b.2 i

/-- Only local continuations remain after the actual common check decision.
`entry` retains both private caches through the adversarial call. -/
structure TreeSimCheckClosure (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (δ : HiddenAddress C → Bit) (k₁ k₂ : C.Party → PartyM C E RealSpec TreeOutput)
    (initial₁ initial₂ : HiddenCache C) where
  J : TreeSimState C → (HashCache C × HiddenCache C) → Prop
  Q : C.Party → Step C E RealSpec TreeOutput → Step C E RealSpec TreeOutput → Prop
  entry : ∀ a b, TreeSimStreamRel δ a b → a.1.2 = initial₁ → b.2 = initial₂ → J a b
  abort : ∀ i, Q i (.done none) (.done none)
  continues : ∀ i a b, J a b →
    RelTriple ((simulateQ (treeSimLoggedWorld prims D) (free (advance (k₁ i).run))).run a)
      ((simulateQ (streamWorld prims D) (free (advance (k₂ i).run))).run b)
      (fun u z => Q i u.1 z.1 ∧ J u.2 z.2)
  exit : ∀ state s₁ s₂ a b, (∀ i, Q i (s₁ i) (s₂ i)) → J a b →
    Bad a ∨ Inv ((state, s₁), a) ((state, s₂), b)

/-- Reachable digest entries must align their digests; final-opening entries
must align their masked three-element vectors. These are still contextual
obligations, including all entry hashes and the non-linear field encoding. -/
def TreeSimCheckBoundary (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (a : TreeSimConfig A (TreeSimState C)) (b : TreeSimConfig A (HashCache C × HiddenCache C)) : Prop :=
  ∃ live kind k₁ k₂ δ, a.1.1 = b.1.1 ∧ TreeSimStreamRel δ a.2 b.2 ∧
    a.1.2 = treeSimCheckWaiting K D live kind k₁ ∧ b.1.2 = treeSimCheckWaiting K D live kind k₂ ∧
    Nonempty (TreeSimCheckClosure prims D A Bad Inv δ k₁ k₂ a.2.1.2 b.2.2)

/-- Check preservation, with both real tests and partial-entry aborts proved.
There is no whole-check-round coupling premise. -/
theorem treeSim_check_preserves (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (Bad : TreeSimState C → Prop)
    (Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop)
    (stage : TreeSimConfig A (TreeSimState C) → TreeSimStage)
    (identify : ∀ a b, stage a = .check → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
      TreeSimCheckBoundary prims K D A Bad Inv a b) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A Bad Inv stage .check := by
  intro a b hg hinv hbad hdone
  obtain ⟨live, kind, k₁, k₂, δ, had, hc, ha, hb, ⟨close⟩⟩ := identify a b hg hinv hbad hdone
  change RelTriple
    ((stepRound (treeSimRealRoles prims D) D A noFunctionality a.1.1 a.1.2).run a.2)
    ((stepRound (treeSimIdealRoles prims D) D A noFunctionality b.1.1 b.1.2).run b.2) _
  simp only [← simulateQ_stepRound, treeSimRealRoles, treeSimIdealRoles]
  rw [ha, hb, ← had, treeSim_check_round_factor, treeSim_check_round_factor]
  simp only [simulateQ_bind, StateT.run_bind]
  apply relTriple_bind (treeSim_local_streamRel_fixed prims D δ _ a.2 b.2 hc)
  intro r₁ r₂ hr
  rw [hr.1]
  have hJ := close.entry r₁.2 r₂.2 hr.2.1 hr.2.2.1 hr.2.2.2
  refine relTriple_bind (treeSim_resumeAll_rel prims D (fun i (_ : Unit) => k₁ i)
    (fun i (_ : Unit) => k₂ i) _ _ close.J close.Q (fun i u z hu => ?_) r₁.2 r₂.2 hJ) ?_
  · cases ho : treeSimCheckResult K D live kind r₂.1.2 i with
    | none =>
      simp only [treeSimResume, free_pure, simulateQ_pure, StateT.run_pure]
      exact relTriple_pure_pure ⟨close.abort i, hu⟩
    | some vals =>
      simp only [treeSimResume]
      exact close.continues i u z hu
  · intro u z hz
    simp only [simulateQ_pure, StateT.run_pure]
    exact relTriple_pure_pure (close.exit r₂.1.1 u.1 z.1 u.2 z.2 hz.1 hz.2)

/-- Contextual obligations for the fixed actual executions. A witness supplies
the invariant and its stage partition; each labeled case must identify the
corresponding suspended program. Final observation allows different hash caches. -/
structure TreeSimRoundStages (events : TreeSimEvents C E)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput)
    (dealt : Option TreeOutput × List (List (List Bit))) (state : A.State) (s : TreeSimState C) where
  Bad : TreeSimState C → Prop
  Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop
  stage : TreeSimConfig A (TreeSimState C) → TreeSimStage
  Q : TreeSimRoundOutput A (TreeSimState C) → TreeSimRoundOutput A (HashCache C × HiddenCache C) → Prop
  entry : ∀ p ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 state
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s),
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeSimContinue (treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs)) p.1.2)).run p.2)
      ((simulateQ (streamWorld prims D)
        (treeSimContinue (treeSimIdealCont K circuits settings top tree D parameter
          (fun T => if KnownTo D.1 T then seeds T else 0) dealt.2) p.1.2)).run p.2.1)
      (fun a b => Bad a.2 ∨ Inv ((p.1.1, a.1), a.2) ((p.1.1, b.1), b.2))
  noSetup : ∀ a b, Inv a b → ¬ Bad a.2 → stage a ≠ .prssSetup
  /-- `Bad` depends only on the log and is monotone under every extension. -/
  badPersistent : ∀ s s' : TreeSimState C, s.2 <+: s'.2 → Bad s → Bad s'
  done : ∀ a b, Inv a b → ¬ Bad a.2 → (AllDone D a.1.2 ↔ AllDone D b.1.2)
  output : ∀ a b, Inv a b → ¬ Bad a.2 →
    Q ((a.1.1, fun i => (a.1.2 i).output), a.2) ((b.1.1, fun i => (b.1.2 i).output), b.2)
  peerBoundary : ∀ a b, stage a = .reshare → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimPeerBoundary prims K D A Bad Inv a b
  collectorBoundary : ∀ a b, stage a = .reshareCollector → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    ∃ d : TreeSimCollectorData K D, TreeSimCollectorBoundary K D A d a b ∧
      Nonempty (TreeSimCollectorClosure prims K D A Bad Inv d a.2.1.2 b.2.2)
  /-- Direct next-collector transitions use program equations and freshness,
  with their probabilistic resumption proved by `TreeSimCollectorNext.coupling`. -/
  collectorNextBoundary : ∀ a b, stage a = .reshareCollectorNext → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    ∃ d : TreeSimCollectorData K D, TreeSimCollectorBoundary K D A d a b ∧
      Nonempty (TreeSimCollectorNextClosure prims K D A Bad Inv d a.2.1.2 b.2.2)
  rerandBoundary : ∀ a b, stage a = .rerand → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimRerandBoundary prims K D A Bad Inv a b
  coinBoundary : ∀ a b, stage a = .coin → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimCoinBoundary prims K D A Bad Inv a b
  extendMultBoundary : ∀ a b, stage a = .extendMult → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimExtendMultBoundary prims K D A Bad Inv a b
  checkBoundary : ∀ a b, stage a = .check → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimCheckBoundary prims K D A Bad Inv a b
  openingBoundary : ∀ a b, stage a = .openRep → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimOpenBoundary prims K D A Bad Inv a b
  emptyOpeningBoundary : ∀ a b, stage a = .openRepEmpty → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimEmptyOpenBoundary prims K D A Bad Inv a b
  ceremony : TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A Bad Inv stage .ceremony
  observeGood : ∀ a b, Q a b →
    RelTriple (treeSimRealObserve prims D A Z a) (treeSimIdealObserve prims D A Z dealt.1 b)
      (fun x y =>
        let flags := events top tree D A (dealtKeys parameter seeds pairs) z Z x.2
        (flags.1 = true ∨ flags.2 = true) ∨ (x.1 = true ↔ y = true))
  badRecorded : ∀ s, Bad s →
    let flags := events top tree D A (dealtKeys parameter seeds pairs) z Z s.2
    flags.1 = true ∨ flags.2 = true

variable {prims K circuits settings} in
/-- The main induction derives both remaining check rounds from their boundaries. -/
theorem TreeSimRoundStages.check {events : TreeSimEvents C E}
    {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
    {parameter : PublicParameter} {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput}
    {z : Aux} {Z : Distinguisher C A.State TreeOutput}
    {dealt : Option TreeOutput × List (List (List Bit))} {state : A.State} {s : TreeSimState C}
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A
      stages.Bad stages.Inv stages.stage .check :=
  treeSim_check_preserves prims K D A stages.Bad stages.Inv stages.stage stages.checkBoundary

variable {prims K circuits settings} in
/-- The main induction derives the replicated opening from its boundary certificate. -/
theorem TreeSimRoundStages.opening {events : TreeSimEvents C E}
    {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
    {parameter : PublicParameter} {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput}
    {z : Aux} {Z : Distinguisher C A.State TreeOutput}
    {dealt : Option TreeOutput × List (List (List Bit))} {state : A.State} {s : TreeSimState C}
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A
      stages.Bad stages.Inv stages.stage .openRep :=
  treeSim_open_preserves prims K D A stages.Bad stages.Inv stages.stage stages.openingBoundary




variable {prims K circuits settings} in
/-- The main induction derives the field exchange from its boundary certificate. -/
theorem TreeSimRoundStages.extendMult {events : TreeSimEvents C E}
    {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
    {parameter : PublicParameter} {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput}
    {z : Aux} {Z : Distinguisher C A.State TreeOutput}
    {dealt : Option TreeOutput × List (List (List Bit))} {state : A.State} {s : TreeSimState C}
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A
      stages.Bad stages.Inv stages.stage .extendMult :=
  treeSim_extendMult_preserves prims K D A stages.Bad stages.Inv stages.stage stages.extendMultBoundary



variable {prims K circuits settings} in
/-- The main ceremony induction consumes the actual peer coupling. -/
theorem TreeSimRoundStages.peer {events : TreeSimEvents C E}
    {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
    {parameter : PublicParameter} {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput}
    {z : Aux} {Z : Distinguisher C A.State TreeOutput}
    {dealt : Option TreeOutput × List (List (List Bit))} {state : A.State} {s : TreeSimState C}
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A
      stages.Bad stages.Inv stages.stage .reshare :=
  treeSim_peer_preserves prims K D A stages.Bad stages.Inv stages.stage stages.peerBoundary


variable {prims K circuits settings} in
/-- The main ceremony induction consumes the actual Rerand-to-Coin coupling. -/
theorem TreeSimRoundStages.rerand {events : TreeSimEvents C E}
    {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
    {parameter : PublicParameter} {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput}
    {z : Aux} {Z : Distinguisher C A.State TreeOutput}
    {dealt : Option TreeOutput × List (List (List Bit))} {state : A.State} {s : TreeSimState C}
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A
      stages.Bad stages.Inv stages.stage .rerand :=
  treeSim_rerand_preserves prims K D A stages.Bad stages.Inv stages.stage stages.rerandBoundary

variable {prims K circuits settings} in
/-- Empty opening is derived from its real hash checks and local continuations. -/
theorem TreeSimRoundStages.openingEmpty {events : TreeSimEvents C E}
    {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
    {parameter : PublicParameter} {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput}
    {z : Aux} {Z : Distinguisher C A.State TreeOutput}
    {dealt : Option TreeOutput × List (List (List Bit))} {state : A.State} {s : TreeSimState C}
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A
      stages.Bad stages.Inv stages.stage .openRepEmpty :=
  treeSim_emptyOpen_preserves prims K D A stages.Bad stages.Inv stages.stage stages.emptyOpeningBoundary

variable {prims K circuits settings} in
/-- Coin's contextual stage now uses its proved real round semantics. -/
theorem TreeSimRoundStages.coin {events : TreeSimEvents C E}
    {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
    {parameter : PublicParameter} {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput}
    {z : Aux} {Z : Distinguisher C A.State TreeOutput}
    {dealt : Option TreeOutput × List (List (List Bit))} {state : A.State} {s : TreeSimState C}
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A
      stages.Bad stages.Inv stages.stage .coin :=
  treeSim_coin_preserves prims K D A stages.Bad stages.Inv stages.stage stages.coinBoundary

variable {prims K circuits settings} in
/-- The ceremony certificate uses the proved collector round transitions;
it only supplies the concrete boundary and continuation invariant. -/
theorem TreeSimRoundStages.collector {events : TreeSimEvents C E}
    {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
    {parameter : PublicParameter} {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput}
    {z : Aux} {Z : Distinguisher C A.State TreeOutput}
    {dealt : Option TreeOutput × List (List (List Bit))} {state : A.State} {s : TreeSimState C}
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A
      stages.Bad stages.Inv stages.stage .reshareCollector :=
  treeSim_collector_preserves prims K D A stages.Bad stages.Inv stages.stage stages.collectorBoundary

variable {prims K circuits settings} in
/-- The direct collector-to-collector case consumes only the concrete next
program certificate and its deterministic invariant-closure facts. -/
theorem TreeSimRoundStages.collectorNext {events : TreeSimEvents C E}
    {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
    {parameter : PublicParameter} {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput}
    {z : Aux} {Z : Distinguisher C A.State TreeOutput}
    {dealt : Option TreeOutput × List (List (List Bit))} {state : A.State} {s : TreeSimState C}
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s) :
    TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A
      stages.Bad stages.Inv stages.stage .reshareCollectorNext := by
  apply treeSim_collector_preserves prims K D A stages.Bad stages.Inv stages.stage
  intro a b hg hinv hbad hdone
  obtain ⟨d, hb, ⟨concrete⟩⟩ := stages.collectorNextBoundary a b hg hinv hbad hdone
  exact ⟨d, hb, ⟨TreeSimCollectorClosure.ofNext prims K D A stages.Bad stages.Inv d a.2.1.2 b.2.2 concrete⟩⟩

variable {prims K circuits settings} in
/-- The certificate's transcript condition discharges every round's bad branch. -/
theorem TreeSimRoundStages.sticky {events : TreeSimEvents C E}
    {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
    {parameter : PublicParameter} {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput}
    {z : Aux} {Z : Distinguisher C A.State TreeOutput}
    {dealt : Option TreeOutput × List (List (List Bit))} {state : A.State} {s : TreeSimState C}
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s)
    (st : A.State) (steps : C.Party → Step C E RealSpec TreeOutput) (r : TreeSimState C)
    (hr : stages.Bad r) :
    ∀ x ∈ support ((stepRound (treeSimRealRoles prims D) D A noFunctionality st steps).run r),
      stages.Bad x.2 :=
  fun x hx => treeSim_round_bad prims D A stages.Bad stages.badPersistent st steps r hr x hx

variable {prims K circuits settings} in
/-- No probabilistic observation obligation is needed once a bad event is logged. -/
theorem TreeSimRoundStages.badObserved {events : TreeSimEvents C E}
    {top : TopTree} {tree : Tree} {D : C.Coalition} {A : Adversary C E (Keys C) PEmpty PEmpty}
    {parameter : PublicParameter} {seeds : C.Term → HashOutput} {pairs : C.Pair → HashOutput}
    {z : Aux} {Z : Distinguisher C A.State TreeOutput}
    {dealt : Option TreeOutput × List (List (List Bit))} {state : A.State} {s : TreeSimState C}
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s)
    (a : TreeSimRoundOutput A (TreeSimState C)) (ha : stages.Bad a.2)
    (x : Bool × TreeSimLog C) (hx : x ∈ support (treeSimRealObserve prims D A Z a)) :
    let flags := events top tree D A (dealtKeys parameter seeds pairs) z Z x.2
    flags.1 = true ∨ flags.2 = true := by
  exact stages.badRecorded (a.2.1, x.2)
    (stages.badPersistent a.2 (a.2.1, x.2) (treeSim_observe_prefix prims D A Z a x hx) ha)

/-- Split final observation into persistence of already-detected bad flags
and a contextual coupling from the terminating relation. The latter allows
hash-cache padding; literal equality of the two caches is not required. -/
theorem treeSimRoundStages_observe (events : TreeSimEvents C E)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput)
    (dealt : Option TreeOutput × List (List (List Bit))) (state : A.State) (s : TreeSimState C)
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s)
    (a : TreeSimRoundOutput A (TreeSimState C)) (b : TreeSimRoundOutput A (HashCache C × HiddenCache C))
    (h : stages.Bad a.2 ∨ stages.Q a b) :
    RelTriple (treeSimRealObserve prims D A Z a) (treeSimIdealObserve prims D A Z dealt.1 b)
      (fun x y =>
        let flags := events top tree D A (dealtKeys parameter seeds pairs) z Z x.2
        (flags.1 = true ∨ flags.2 = true) ∨ (x.1 = true ↔ y = true)) := by
  rcases h with hbad | hgood
  · exact relTriple_of_support_left fun x hx _ => Or.inl (stages.badObserved a hbad x hx)
  · exact stages.observeGood a b hgood

/-- The full PRSS setup is coupled before applying the remaining round
invariant. Only the post-setup local computations need its entry proof. -/
theorem treeSimRoundStages_phase (events : TreeSimEvents C E)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput)
    (dealt : Option TreeOutput × List (List (List Bit))) (state : A.State) (s : TreeSimState C)
    (hs : s.1.2 = ∅)
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s) :
    RelTriple
      ((executePhase (treeSimRealRoles prims D) D A noFunctionality (ceremonyFuel circuits settings) state
        (fun i => ceremony K circuits settings i (dealtKeys parameter seeds pairs i) top tree)).run s)
      ((executePhase (treeSimIdealRoles prims D) D A noFunctionality (ceremonyFuel circuits settings) state
        (treeSimProgram K circuits settings D parameter (fun T => if KnownTo D.1 T then seeds T else 0)
          dealt.2 top tree)).run (s.1.1, ∅))
      (fun a b => stages.Bad a.2 ∨ stages.Q a b) := by
  have hr : (fun i => ceremony K circuits settings i (dealtKeys parameter seeds pairs i) top tree) =
      (fun i => prssSetup i >>= treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs) i) :=
    funext (treeSim_real_cont K circuits settings top tree (dealtKeys parameter seeds pairs))
  have hi : treeSimProgram K circuits settings D parameter (fun T => if KnownTo D.1 T then seeds T else 0) dealt.2 top tree =
      (fun i => prssSetup i >>= treeSimIdealCont K circuits settings top tree D parameter
        (fun T => if KnownTo D.1 T then seeds T else 0) dealt.2 i) :=
    funext (treeSim_ideal_cont K circuits settings top tree D parameter
      (fun T => if KnownTo D.1 T then seeds T else 0) dealt.2)
  have hc : (s.1.1, (∅ : HiddenCache C)) = s.1 := by rw [← hs]
  have hf : ceremonyFuel circuits settings = (ceremonyFuel circuits settings - 3) + 3 := by
    unfold ceremonyFuel setupRounds
    omega
  rw [hr, hi, hc, hf]
  apply treeSim_prssSetup_continuations prims D A state _ s _ _
    (fun a b => stages.Bad a.2 ∨ stages.Inv a b) _ (by exact stages.entry)
  intro a b hab
  exact treeSim_executeRounds (treeSimRealRoles prims D) (treeSimIdealRoles prims D)
    D A stages.Bad stages.Inv stages.stage (by
      intro a b hstage hinv hgood _
      exact (stages.noSetup a b hinv hgood hstage).elim) (by exact stages.peer)
    (by exact stages.collector) (by exact stages.collectorNext) (by exact stages.rerand) (by exact stages.coin) (by exact stages.extendMult)
    (by exact stages.check) (by exact stages.opening) (by exact stages.openingEmpty)
    (by exact stages.ceremony) stages.Q
    (by exact stages.sticky) (by exact stages.done) (by exact stages.output)
    (ceremonyFuel circuits settings - 3) a b (by exact hab)

set_option backward.isDefEq.respectTransparency false in
/-- Assemble the actual phase from the named round obligations. This theorem
accounts for initialization, all early stops, fuel exhaustion, and Z. -/
theorem treeSimRoundStages_run (events : TreeSimEvents C E)
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (z : Aux) (Z : Distinguisher C A.State TreeOutput)
    (dealt : Option TreeOutput × List (List (List Bit))) (state : A.State) (s : TreeSimState C)
    (hs : s.1.2 = ∅)
    (stages : TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z dealt state s) :
    RelTriple (treeSimRealFinish prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) Z state s)
      ((treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z state dealt).run' s.1.1)
      (fun x y =>
        let flags := events top tree D A (dealtKeys parameter seeds pairs) z Z x.2
        (flags.1 = true ∨ flags.2 = true) ∨ (x.1 = true ↔ y = true)) := by
  have hr := treeSimRealFinish_rounds prims K circuits settings top tree D A
    (dealtKeys parameter seeds pairs) Z state s
  have hi := treeSimIdealFinish_rounds prims K circuits settings top tree D A parameter seeds Z state dealt s.1.1
  rw [hr, hi]
  exact relTriple_bind (treeSimRoundStages_phase prims K circuits settings events top tree D A
    parameter seeds pairs z Z dealt state s hs stages) (by
      exact treeSimRoundStages_observe prims K circuits settings events top tree D A
        parameter seeds pairs z Z dealt state s stages)


/-- The remaining local gadget obligations after a reachable common prefix.
An optional shared ghost computation may pad the hash cache first; its exact
marginal and log erasure laws are proved, and `pure ()` gives no padding. -/
def TreeSimStages (events : TreeSimEvents C E) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    ∃ padding : OracleComp (LocalSpec C) Unit,
      ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
      Nonempty (TreeSimRoundStages prims K circuits settings events top tree D A parameter seeds pairs z Z
        p.1 p.2.1 ((r.2, p.2.2.1.2), p.2.2.2))

/-- The remaining relation starts after a proved common initialization. It
compares the actual real phase with the actual dummy-seed/shifted phase from
each reachable prefix, retaining the initial real transcript. -/
def TreeSimCeremonyCoupling (events : TreeSimEvents C E) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
    RelTriple (treeSimRealFinish prims K circuits settings top tree D A
      (dealtKeys parameter seeds pairs) Z p.2.1 p.2.2)
      ((treeSimIdealFinish prims K circuits settings top tree D A parameter seeds Z p.2.1 p.1).run' p.2.2.1.1)
      (fun a b =>
        let flags := events top tree D A (dealtKeys parameter seeds pairs) z Z a.2
        (flags.1 = true ∨ flags.2 = true) ∨ (a.1 = true ↔ b = true))

theorem treeSim_stages_coupling (events : TreeSimEvents C E)
    (h : TreeSimStages prims K circuits settings events) :
    TreeSimCeremonyCoupling prims K circuits settings events := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  obtain ⟨padding, hstages⟩ := h hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  apply relTriple_of_evalDist_eq_left
    (treeSimRealFinish_padding prims K circuits settings top tree D A
      (dealtKeys parameter seeds pairs) Z p.2.1 p.2.2 padding).symm
  apply relTriple_of_evalDist_eq_right
    (treeSimIdealFinish_padding prims K circuits settings top tree D A parameter seeds Z p.2.1 p.1 p.2.2.1.1 padding)
  apply relTriple_bind (treeSim_refl_support _)
  rintro r _ ⟨hr, rfl⟩
  obtain ⟨stages⟩ := hstages r hr
  exact treeSimRoundStages_run prims K circuits settings events top tree D A parameter seeds pairs z Z
    p.1 p.2.1 ((r.2, p.2.2.1.2), p.2.2.2)
    (treeSimCommonPrefix_hidden prims circuits settings top tree D A parameter seeds pairs z p hp) stages

/-- Contextual ceremony obligation after inserting the actual dealer as
private ghost data on the real side. The dealer and real execution share the
same hash cache. Both bad flags still refer to the original real transcript. -/
def TreeSimGhostCoupling (events : TreeSimEvents C E) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    RelTriple (treeSimGhostRun prims D
      (liftComp (dealerCeremony circuits settings parameter seeds top tree) (LocalSpec C))
      (treeRealGame K circuits settings top tree D A (dealtKeys parameter seeds pairs) z Z))
      (treeSimDealerFirstIdeal prims K circuits settings top tree D A parameter seeds pairs z Z)
      (fun a b =>
        let flags := events top tree D A (dealtKeys parameter seeds pairs) z Z a.2.2
        (flags.1 = true ∨ flags.2 = true) ∨ (a.2.1 = true ↔ b = true))

/-- Discharge the dealer and adversary-start stages by the common-prefix
coupling, with no loss and no restriction to an empty incoming phase cache. -/
theorem treeSim_ceremony_coupling (events : TreeSimEvents C E)
    (h : TreeSimCeremonyCoupling prims K circuits settings events) :
    TreeSimGhostCoupling prims K circuits settings events := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall
  rw [treeSimGhostRun_prefix, treeSimDealerFirstIdeal_prefix]
  apply relTriple_bind (treeSim_refl_support _)
  rintro p _ ⟨hp, rfl⟩
  have hc := h hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  simpa only [id_map] using (relTriple_map
    (R := fun (a : (Option TreeOutput × List (List (List Bit))) × (Bool × TreeSimLog C)) (b : Bool) =>
      let flags := events top tree D A (dealtKeys parameter seeds pairs) z Z a.2.2
      (flags.1 = true ∨ flags.2 = true) ∨ (a.2.1 = true ↔ b = true))
    (f := fun r => (p.1, r)) (g := id) hc)

/-- Project the private dealer and the real query log only after the
contextual coupling. The distribution of each bad flag is unchanged. -/
theorem treeSim_ghost_coupling (events : TreeSimEvents C E)
    (h : TreeSimGhostCoupling prims K circuits settings events) :
    TreeSimStreamCoupling prims K circuits settings events := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall
  have hc := relTriple_map
    (R := fun (a : Bool × Bool × Bool) (b : Bool) =>
      (a.2.1 = true ∨ a.2.2 = true) ∨ (a.1 = true ↔ b = true))
    (f := fun r : (Option TreeOutput × List (List (List Bit))) × (Bool × TreeSimLog C) =>
      (r.2.1, events top tree D A (dealtKeys parameter seeds pairs) z Z r.2.2))
    (g := id) (h hb top tree D A parameter seeds pairs z Z q hq hsmall)
  simp only [id_map] at hc
  apply relTriple_of_evalDist_eq_right
    (treeSim_ideal_prefix_swap prims K circuits settings top tree D A parameter seeds pairs z Z).symm
  exact relTriple_of_evalDist_eq_left
    (treeSim_ghost_trace prims K circuits settings events top tree D A
      (dealtKeys parameter seeds pairs) z Z _).symm hc

/-- Remaining relational obligation. This includes initialization with the
shared dealer cache, all real gadget rounds, and the final distinguisher.
Outside either bad flag the acceptance bits must agree. -/
def TreeSimCoupling (trace : TreeSimTrace C E) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    RelTriple (trace top tree D A x z Z)
      (worldRun prims (treeIdealGame K circuits settings top tree D A x z Z))
      (fun a b => (a.2.1 = true ∨ a.2.2 = true) ∨ (a.1 = true ↔ b.1 = true))

/-- One birthday bound for the union of hash failures. The `2 m` PRSS-key
points have already been paid by `keySplit`; no per-gadget hash budgets are added. -/
def TreeSimHashBound (trace : TreeSimTrace C E) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    Pr[fun r => r.2.1 = true | trace top tree D A x z Z].toReal ≤
      (((q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) ^ 2 : ℕ) : ℝ) / 2 ^ 256

/-- The check obligation is for the adaptively reached batches of this trace,
not an invocation of the standalone check theorem from an empty cache. -/
def TreeSimCheckBound (trace : TreeSimTrace C E) : Prop :=
  0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ), DealtInputs D x →
    IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
    Pr[fun r => r.2.2 = true | trace top tree D A x z Z].toReal ≤
      treeCheckError (E := E) circuits settings tree q

/-- The hash union fits exactly in the remaining budget of the simulation hop. -/
theorem treeSim_hashBudget (tree : Tree) (q : ℕ) :
    (((q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) ^ 2 : ℕ) : ℝ) / 2 ^ 256 ≤
      treeHashError circuits settings C tree q - keySplit C q := by
  have h := keySplit_add_rest_le circuits settings (C := C) tree q
  linarith

/-- At `q ≥ 2^128` the unused hash budget alone is at least one. -/
theorem treeSim_largeHashBudget (tree : Tree) (q : ℕ) (hq : 2 ^ 128 ≤ q) :
    1 ≤ treeHashError circuits settings C tree q - keySplit C q := by
  apply le_trans _ (treeSim_hashBudget circuits settings tree q)
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 256)).mpr
  have hq' : (2 : ℝ) ^ 128 ≤ (q : ℝ) := by exact_mod_cast hq
  have hnat : q ≤ q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C) := Nat.le_add_right _ _
  have hcast : (q : ℝ) ≤ (q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C) : ℕ) := by
    exact_mod_cast hnat
  simp only [one_mul, Nat.cast_pow]
  calc
    (2 : ℝ) ^ 256 = ((2 : ℝ) ^ 128) ^ 2 := by ring
    _ ≤ (q : ℝ) ^ 2 := by gcongr
    _ ≤ (↑(q + (treeSecrets circuits settings C tree - 2 * prssKeyCount C)) : ℝ) ^ 2 := by gcongr

/-- The large-query case of the exact requested simulation hop is unconditional. -/
theorem treeSim_large (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (x : C.Party → Keys C) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput) (q : ℕ) (hq : 2 ^ 128 ≤ q) :
    |(Pr[= true | (simulateQ (streamWorld prims D)
        (treeRealGame K circuits settings top tree D A x z Z)).run' (∅, ∅)]).toReal -
      accepts prims (treeIdealGame K circuits settings top tree D A x z Z)| ≤
      treeCheckError (E := E) circuits settings tree q +
        (treeHashError circuits settings C tree q - keySplit C q) := by
  have hc : 0 ≤ treeCheckError (E := E) circuits settings tree q := by
    letI : Inhabited E := ⟨0⟩
    letI : SampleableType E := SampleableType.ofFintype E
    unfold treeCheckError
    exact mul_nonneg (Nat.cast_nonneg _) (checkErrorOf_nonneg K _ _ _)
  have hh := treeSim_largeHashBudget (C := C) circuits settings tree q hq
  have unit : ∀ {α : Type} (oa : ProbComp α) (P : α → Prop),
      0 ≤ Pr[P | oa].toReal ∧ Pr[P | oa].toReal ≤ 1 := by
    intro α oa P
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact probEvent_le_one)⟩
  rw [accepts_eq_worldRun]
  have hl := unit ((simulateQ (streamWorld prims D)
    (treeRealGame K circuits settings top tree D A x z Z)).run' (∅, ∅)) (fun b => b = true)
  have hr := unit (worldRun prims (treeIdealGame K circuits settings top tree D A x z Z))
    (fun r => r.1 = true)
  simp only [probEvent_eq_eq_probOutput] at hl
  rw [abs_le]
  constructor <;> linarith

/-- Coupling up to the single union of hash and check failures. -/
theorem treeSim_badUnion {α β : Type} (oa : ProbComp α) (ob : ProbComp β)
    (hashBad checkBad P : α → Prop) (Q : β → Prop)
    (h : RelTriple oa ob (fun a b => (hashBad a ∨ checkBad a) ∨ (P a ↔ Q b))) :
    |Pr[P | oa].toReal - Pr[Q | ob].toReal| ≤
      Pr[hashBad | oa].toReal + Pr[checkBad | oa].toReal := by
  apply (abs_probEvent_sub_le_of_relTriple (fun a => hashBad a ∨ checkBad a) P Q h).trans
  have hu : Pr[fun a => hashBad a ∨ checkBad a | oa] ≤ Pr[hashBad | oa] + Pr[checkBad | oa] :=
    probEvent_or_le _ _ _
  exact (ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨probEvent_ne_top, probEvent_ne_top⟩) hu).trans_eq
    (ENNReal.toReal_add probEvent_ne_top probEvent_ne_top)

/-- Conditional assembly, with the actual target unchanged. The four named
hypotheses above are still open; the local mask lemmas do not discharge them. -/
theorem treeSimulationHop_of_trace (trace : TreeSimTrace C E)
    (marginal : TreeSimMarginal prims K circuits settings trace)
    (coupling : TreeSimCoupling prims K circuits settings trace)
    (hashBound : TreeSimHashBound circuits settings trace)
    (checkBound : TreeSimCheckBound circuits settings trace) :
    TreeSimulationHop prims K circuits settings (keySplit C) := by
  intro hb top tree D A x z Z q hx hq
  by_cases hsmall : q < 2 ^ 128
  · have hm := congrArg (fun d => d true) (marginal top tree D A x z Z)
    have hm' : Pr[fun r => r.1 = true | trace top tree D A x z Z] =
        Pr[= true | (simulateQ (streamWorld prims D)
          (treeRealGame K circuits settings top tree D A x z Z)).run' (∅, ∅)] := by
      simpa only [← probOutput_def, probOutput_map] using hm
    rw [← hm', accepts_eq_worldRun]
    have hc := treeSim_badUnion (trace top tree D A x z Z)
      (worldRun prims (treeIdealGame K circuits settings top tree D A x z Z))
      (fun r => r.2.1 = true) (fun r => r.2.2 = true) (fun r => r.1 = true)
      (fun r => r.1 = true) (coupling hb top tree D A x z Z q hx hq hsmall)
    have hh := (hashBound hb top tree D A x z Z q hx hq hsmall).trans
      (treeSim_hashBudget circuits settings tree q)
    have hcheck := checkBound hb top tree D A x z Z q hx hq hsmall
    linarith
  · exact treeSim_large prims K circuits settings top tree D A x z Z q (Nat.le_of_not_gt hsmall)


/-- The requested hop with exact experiment normalization, ghost padding,
complete PRSS prefix coupling and trace erasure. The post-setup stage invariant
and the two event bounds remain open; no experiment-normalization premise remains. -/
theorem treeSimulationHop (events : TreeSimEvents C E)
    (stages : TreeSimStages prims K circuits settings events)
    (hashBound : TreeSimHashBound circuits settings (treeSimTrace prims K circuits settings events))
    (checkBound : TreeSimCheckBound circuits settings (treeSimTrace prims K circuits settings events)) :
    TreeSimulationHop prims K circuits settings (keySplit C) := by
  have coupling := treeSim_ghost_coupling prims K circuits settings events
    (treeSim_ceremony_coupling prims K circuits settings events
      (treeSim_stages_coupling prims K circuits settings events stages))
  intro hb top tree D A x z Z q hx hq
  by_cases hsmall : q < 2 ^ 128
  · obtain ⟨parameter, seeds, pairs, hx⟩ := hx
    have heq : x = dealtKeys parameter seeds pairs := funext hx
    subst x
    have hm := congrArg (fun d => d true)
      (treeSim_trace_marginal prims K circuits settings events top tree D A
        (dealtKeys parameter seeds pairs) z Z)
    have hm' : Pr[fun r => r.1 = true | treeSimTrace prims K circuits settings events top tree D A
        (dealtKeys parameter seeds pairs) z Z] =
        Pr[= true | (simulateQ (streamWorld prims D)
          (treeRealGame K circuits settings top tree D A (dealtKeys parameter seeds pairs) z Z)).run' (∅, ∅)] := by
      simpa only [← probOutput_def, probOutput_map] using hm
    have hi := congrArg (fun p => Pr[= true | p])
      (treeSim_streamIdeal_eq prims K circuits settings top tree D A parameter seeds pairs z Z)
    simp only [probOutput_map] at hi
    rw [← hm', accepts_eq_worldRun, hi]
    have hc := treeSim_badUnion _ _ (fun r : Bool × Bool × Bool => r.2.1 = true) (fun r => r.2.2 = true)
      (fun r => r.1 = true) (fun b => b = true)
      (coupling hb top tree D A parameter seeds pairs z Z q hq hsmall)
    have dealt : DealtInputs D (dealtKeys parameter seeds pairs) := ⟨parameter, seeds, pairs, fun _ => rfl⟩
    have hh := (hashBound hb top tree D A _ z Z q dealt hq hsmall).trans
      (treeSim_hashBudget circuits settings tree q)
    have hcheck := checkBound hb top tree D A _ z Z q dealt hq hsmall
    simpa only [probEvent_eq_eq_probOutput, add_comm] using hc.trans (add_le_add hh hcheck)
  · exact treeSim_large prims K circuits settings top tree D A x z Z q (Nat.le_of_not_gt hsmall)


/-- Off the fixed bad event, every successful honest output in a replay
certificate equals the dealer's output. No probability bound is used here. -/
theorem treeSim_output_correct (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (dealt : Option TreeOutput × List (List (List Bit)))
    (out : A.State × (C.Party → Option TreeOutput)) (log : TreeSimLog C)
    (replay : TreeSimOutputWitness prims K circuits settings top tree D A parameter seeds pairs z dealt out log)
    (good : ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z log)
    (i : C.Party) (hi : i ∉ D.1) (hs : (out.2 i).isSome) : out.2 i = dealt.1 := by
  by_contra hne
  exact good (Or.inr ⟨parameter, seeds, pairs, dealt, out, rfl, replay, i, hi, hs, hne⟩)

/-- Terminal alignment now needs only replay, adversary/cache agreement and
matching success bits. Equality with the ideal functionality's output follows
from the concrete check event, rather than being a fresh stage assumption. -/
theorem treeSim_final_of_replay (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (dealt : Option TreeOutput × List (List (List Bit)))
    (a : TreeSimRoundOutput A (TreeSimState C)) (b : TreeSimRoundOutput A (HashCache C × HiddenCache C))
    (replay : TreeSimOutputWitness prims K circuits settings top tree D A parameter seeds pairs z dealt a.1 a.2.2)
    (good : ¬ TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z a.2.2)
    (state : a.1.1 = b.1.1) (cache : a.2.1.1 = b.2.1)
    (corrupt : ∀ i, i ∈ D.1 → a.1.2 i = none)
    (success : ∀ i, i ∉ D.1 → (a.1.2 i).isSome = (b.1.2 i).isSome) :
    TreeSimFinalRel D A dealt.1 a b := by
  refine ⟨state, cache, funext fun i => ?_⟩
  by_cases hi : i ∈ D.1
  · simp [hi, corrupt i hi]
  · by_cases hs : (a.1.2 i).isSome = true
    · have hb : (b.1.2 i).isSome = true := (success i hi).symm.trans hs
      simpa only [hi, not_false_eq_true, hb, Bool.true_eq, and_self, if_true] using
        treeSim_output_correct prims K circuits settings top tree D A parameter seeds pairs z
          dealt a.1 a.2.2 replay good i hi hs
    · have hb : (b.1.2 i).isSome ≠ true := fun h => hs ((success i hi).trans h)
      have ha : a.1.2 i = none := by
        cases he : a.1.2 i with
        | none => rfl
        | some v => exact False.elim (hs (by simp [he]))
      simp [hi, hb, ha]

/-- The remaining deterministic/relational obligations for the fixed event
choice. Sticky-event bookkeeping and final observation have been discharged.
The replay field concerns the *same* execution prefix, including dealer cache
padding; it must not be supplied from an independent run. -/
structure TreeSimRoundCore
    (top : TopTree) (tree : Tree) (D : C.Coalition) (A : Adversary C E (Keys C) PEmpty PEmpty)
    (parameter : PublicParameter) (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput)
    (z : Aux)
    (dealt : Option TreeOutput × List (List (List Bit))) (state : A.State) (s : TreeSimState C)
    (Bad : TreeSimState C → Prop) where
  Inv : TreeSimConfig A (TreeSimState C) → TreeSimConfig A (HashCache C × HiddenCache C) → Prop
  stage : TreeSimConfig A (TreeSimState C) → TreeSimStage
  entry : ∀ p ∈ support ((executePhase (treeSimRealRoles prims D) D A noFunctionality 3 state
      (fun i => (prssSetup i : PartyM C E RealSpec (PrssKeys C)))).run s),
    RelTriple
      ((simulateQ (treeSimLoggedWorld prims D)
        (treeSimContinue (treeSimRealCont K circuits settings top tree (dealtKeys parameter seeds pairs)) p.1.2)).run p.2)
      ((simulateQ (streamWorld prims D)
        (treeSimContinue (treeSimIdealCont K circuits settings top tree D parameter
          (fun T => if KnownTo D.1 T then seeds T else 0) dealt.2) p.1.2)).run p.2.1)
      (fun a b => Bad a.2 ∨ Inv ((p.1.1, a.1), a.2) ((p.1.1, b.1), b.2))
  noSetup : ∀ a b, Inv a b → ¬ Bad a.2 → stage a ≠ .prssSetup
  done : ∀ a b, Inv a b → ¬ Bad a.2 → (AllDone D a.1.2 ↔ AllDone D b.1.2)
  outputEvidence : ∀ a b, Inv a b → ¬ Bad a.2 →
    TreeSimOutputWitness prims K circuits settings top tree D A parameter seeds pairs z dealt
      (a.1.1, fun i => (a.1.2 i).output) a.2.2 ∧
    a.1.1 = b.1.1 ∧ a.2.1.1 = b.2.1 ∧
    (∀ i, i ∈ D.1 → (a.1.2 i).output = none) ∧
    (∀ i, i ∉ D.1 → (a.1.2 i).output.isSome = (b.1.2 i).output.isSome)
  peerBoundary : ∀ a b, stage a = .reshare → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimPeerBoundary prims K D A Bad Inv a b
  collectorBoundary : ∀ a b, stage a = .reshareCollector → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    ∃ d : TreeSimCollectorData K D, TreeSimCollectorBoundary K D A d a b ∧
      Nonempty (TreeSimCollectorClosure prims K D A Bad Inv d a.2.1.2 b.2.2)
  /-- Direct next-collector transitions use program equations and freshness,
  with their probabilistic resumption proved by `TreeSimCollectorNext.coupling`. -/
  collectorNextBoundary : ∀ a b, stage a = .reshareCollectorNext → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    ∃ d : TreeSimCollectorData K D, TreeSimCollectorBoundary K D A d a b ∧
      Nonempty (TreeSimCollectorNextClosure prims K D A Bad Inv d a.2.1.2 b.2.2)
  rerandBoundary : ∀ a b, stage a = .rerand → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimRerandBoundary prims K D A Bad Inv a b
  coinBoundary : ∀ a b, stage a = .coin → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimCoinBoundary prims K D A Bad Inv a b
  extendMultBoundary : ∀ a b, stage a = .extendMult → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimExtendMultBoundary prims K D A Bad Inv a b
  checkBoundary : ∀ a b, stage a = .check → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimCheckBoundary prims K D A Bad Inv a b
  openingBoundary : ∀ a b, stage a = .openRep → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimOpenBoundary prims K D A Bad Inv a b
  emptyOpeningBoundary : ∀ a b, stage a = .openRepEmpty → Inv a b → ¬ Bad a.2 → ¬ AllDone D a.1.2 →
    TreeSimEmptyOpenBoundary prims K D A Bad Inv a b
  ceremony : TreeSimPreserves (treeSimRealRoles prims D) (treeSimIdealRoles prims D) D A Bad Inv stage .ceremony

/-- Complete the fixed-event round interface from its remaining core. -/
def treeSimRoundCore_stages (top : TopTree) (tree : Tree) (D : C.Coalition)
    (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
    (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
    (Z : Distinguisher C A.State TreeOutput)
    (dealt : Option TreeOutput × List (List (List Bit))) (state : A.State) (s : TreeSimState C)
    (core : TreeSimRoundCore prims K circuits settings top tree D A parameter seeds pairs z dealt state s
      (fun t => TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2)) :
    TreeSimRoundStages prims K circuits settings (treeSimEvents prims K circuits settings)
      top tree D A parameter seeds pairs z Z dealt state s where
  Bad t := TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2
  Inv := core.Inv
  stage := core.stage
  Q := TreeSimFinalRel D A dealt.1
  entry := core.entry
  noSetup := core.noSetup
  badPersistent _ _ hp := treeSimBad_mono prims K circuits settings top tree D A _ z hp
  done := core.done
  output a b hab hgood := by
    obtain ⟨replay, state, cache, corrupt, success⟩ := core.outputEvidence a b hab hgood
    exact treeSim_final_of_replay prims K circuits settings top tree D A parameter seeds pairs z dealt
      ((a.1.1, fun i => (a.1.2 i).output), a.2) ((b.1.1, fun i => (b.1.2 i).output), b.2)
      replay hgood state cache corrupt success
  peerBoundary := core.peerBoundary
  collectorBoundary := core.collectorBoundary
  collectorNextBoundary := core.collectorNextBoundary
  rerandBoundary := core.rerandBoundary
  coinBoundary := core.coinBoundary
  extendMultBoundary := core.extendMultBoundary
  checkBoundary := core.checkBoundary
  openingBoundary := core.openingBoundary
  emptyOpeningBoundary := core.emptyOpeningBoundary
  ceremony := core.ceremony
  observeGood a b hab := relTriple_post_mono (treeSim_observe_good prims D A Z dealt.1 a b hab)
    (fun _ _ he => Or.inr (by rw [he]))
  badRecorded t ht := (treeSimEvents_bad prims K circuits settings top tree D A _ z Z t.2).mpr ht

/-- Parallel task 1: construct the actual ceremony stage invariant for the
fixed events. This task does not assume either probability bound. -/
def TreeSimStagesGoal : Prop :=
  TreeSimStages prims K circuits settings (treeSimEvents prims K circuits settings)

/-- The stages task is reduced to the core boundaries at each supported
common prefix. Event persistence, recorded flags, successful-output correctness
and the final distinguisher coupling are already proved in this reduction. -/
theorem treeSimStagesGoal_of_cores
    (cores : 0 < settings.batchSize → ∀ (top : TopTree) (tree : Tree) (D : C.Coalition)
      (A : Adversary C E (Keys C) PEmpty PEmpty) (parameter : PublicParameter)
      (seeds : C.Term → HashOutput) (pairs : C.Pair → HashOutput) (z : Aux)
      (Z : Distinguisher C A.State TreeOutput) (q : ℕ),
      IsQueryBounded A Z (ceremonyFuel circuits settings) q → q < 2 ^ 128 →
      ∀ p ∈ support (treeSimCommonPrefix prims circuits settings top tree D A parameter seeds pairs z),
      ∃ padding : OracleComp (LocalSpec C) Unit,
      ∀ r ∈ support ((simulateQ (localAnswer prims) padding).run p.2.2.1.1),
      Nonempty (TreeSimRoundCore prims K circuits settings top tree D A parameter seeds pairs z p.1 p.2.1
        ((r.2, p.2.2.1.2), p.2.2.2)
        (fun t => TreeSimBad prims K circuits settings top tree D A (dealtKeys parameter seeds pairs) z t.2))) :
    TreeSimStagesGoal prims K circuits settings := by
  intro hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  obtain ⟨padding, hpadding⟩ := cores hb top tree D A parameter seeds pairs z Z q hq hsmall p hp
  refine ⟨padding, fun r hr => ?_⟩
  obtain ⟨core⟩ := hpadding r hr
  exact ⟨treeSimRoundCore_stages prims K circuits settings top tree D A parameter seeds pairs z Z
    p.1 p.2.1 ((r.2, p.2.2.1.2), p.2.2.2) core⟩

/-- Parallel task 2: bound the fixed collision/salt-guess union. This task does
not assume the stages or the check bound. Count distinct region points, not all
PRF/Th calls, and retain the shared dealer cache. -/
def TreeSimHashBoundGoal : Prop :=
  TreeSimHashBound circuits settings
    (treeSimTrace prims K circuits settings (treeSimEvents prims K circuits settings))

/-- Parallel task 3: contextual soundness for accepted incorrect outputs,
excluding the fixed hash event. This task does not assume the stages or the
hash probability estimate. Its semantic witness must be tied to the actual
logged execution before applying the first-incorrect-batch argument. -/
def TreeSimCheckBoundGoal : Prop :=
  TreeSimCheckBound circuits settings
    (treeSimTrace prims K circuits settings (treeSimEvents prims K circuits settings))

/-- Assembly of the three fixed, independent tasks. The name denotes closure
of the interface, not a claim that its three premises have been proved. -/
theorem treeSimulationHopClosed
    (stages : TreeSimStagesGoal prims K circuits settings)
    (hashBound : TreeSimHashBoundGoal prims K circuits settings)
    (checkBound : TreeSimCheckBoundGoal prims K circuits settings) :
    TreeSimulationHop prims K circuits settings (keySplit C) := by
  exact treeSimulationHop prims K circuits settings (treeSimEvents prims K circuits settings)
    stages hashBound checkBound


/-- info: 'ThresholdLeanXmssSecurity.treeSimShift_rebuild' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimShift_rebuild

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prssSetup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_prssSetup

/-- info: 'ThresholdLeanXmssSecurity.treeSim_reshare_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_reshare_outputs

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_outputs

/-- info: 'ThresholdLeanXmssSecurity.treeSim_extendMult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_extendMult

/-- info: 'ThresholdLeanXmssSecurity.treeSim_coin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_coin

/-- info: 'ThresholdLeanXmssSecurity.treeSim_rerand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_rerand

/-- info: 'ThresholdLeanXmssSecurity.treeSim_checkSlice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_checkSlice

/-- info: 'ThresholdLeanXmssSecurity.treeSim_openRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_openRep

/-- info: 'ThresholdLeanXmssSecurity.treeSim_executeRounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_executeRounds

/-- info: 'ThresholdLeanXmssSecurity.treeSimEvaluate_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimEvaluate_phase

/-- info: 'ThresholdLeanXmssSecurity.treeSim_idealGame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_idealGame

/-- info: 'ThresholdLeanXmssSecurity.treeSim_streamIdeal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_streamIdeal_eq

/-- info: 'ThresholdLeanXmssSecurity.treeSim_ideal_prefix_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_ideal_prefix_swap

/-- info: 'ThresholdLeanXmssSecurity.treeSim_dealer_commutes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_dealer_commutes

/-- info: 'ThresholdLeanXmssSecurity.treeSim_real_dealer_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_real_dealer_prefix

/-- info: 'ThresholdLeanXmssSecurity.treeSim_ghost_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_ghost_log

/-- info: 'ThresholdLeanXmssSecurity.treeSim_ghost_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_ghost_trace

/-- info: 'ThresholdLeanXmssSecurity.treeSim_ghost_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_ghost_coupling

/-- info: 'ThresholdLeanXmssSecurity.treeSim_trace_marginal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_trace_marginal

/-- info: 'ThresholdLeanXmssSecurity.treeSim_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_large

/-- info: 'ThresholdLeanXmssSecurity.treeSim_peer_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_peer_round

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_rounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_rounds

/-- info: 'ThresholdLeanXmssSecurity.treeSim_coin_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_coin_round

/-- info: 'ThresholdLeanXmssSecurity.treeSim_hiddenDraws_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_hiddenDraws_log

/-- info: 'ThresholdLeanXmssSecurity.treeSim_hiddenTable_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_hiddenTable_shift

/-- info: 'ThresholdLeanXmssSecurity.treeSim_pivot_stream' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_pivot_stream

/-- info: 'ThresholdLeanXmssSecurity.treeSim_local_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_local_coupling

/-- info: 'ThresholdLeanXmssSecurity.treeSim_hiddenTable_rushing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_hiddenTable_rushing

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prgBits_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_prgBits_shift

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prgBits_cached_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_prgBits_cached_logged

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prssBits_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_prssBits_ready

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prssElements_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_prssElements_ready

/-- info: 'ThresholdLeanXmssSecurity.treeSim_peer_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_peer_entry

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_entry

/-- info: 'ThresholdLeanXmssSecurity.treeSim_coin_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_coin_entry

/-- info: 'ThresholdLeanXmssSecurity.treeSim_mult_start_ready' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_mult_start_ready

/-- info: 'ThresholdLeanXmssSecurity.TreeSimRoundStages.sticky' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeSimRoundStages.sticky

/-- info: 'ThresholdLeanXmssSecurity.TreeSimRoundStages.badObserved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeSimRoundStages.badObserved

/-- info: 'ThresholdLeanXmssSecurity.treeSim_observe_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_observe_good

/-- info: 'ThresholdLeanXmssSecurity.treeSimRealFinish_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimRealFinish_padding

/-- info: 'ThresholdLeanXmssSecurity.treeSimIdealFinish_padding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimIdealFinish_padding

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prssSetup_continuations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_prssSetup_continuations

/-- info: 'ThresholdLeanXmssSecurity.treeSimRoundStages_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimRoundStages_phase

/-- info: 'ThresholdLeanXmssSecurity.treeSimRoundStages_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimRoundStages_run

/-- info: 'ThresholdLeanXmssSecurity.treeSim_stages_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_stages_coupling

/-- info: 'ThresholdLeanXmssSecurity.treeSim_hiddenQuery_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_hiddenQuery_mixed

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prgBits_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_prgBits_mixed

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prssBits_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_prssBits_mixed

/-- info: 'ThresholdLeanXmssSecurity.treeSim_peerShift_balance_inputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_peerShift_balance_inputs

/-- info: 'ThresholdLeanXmssSecurity.treeSim_peer_rushing_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_peer_rushing_next

/-- info: 'ThresholdLeanXmssSecurity.treeSim_peer_round_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_peer_round_actual

/-- info: 'ThresholdLeanXmssSecurity.treeSim_peer_round_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_peer_round_next

/-- info: 'ThresholdLeanXmssSecurity.treeSim_termVal_pivot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_termVal_pivot

/-- info: 'ThresholdLeanXmssSecurity.treeSim_reshareZ_pivot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_reshareZ_pivot

/-- info: 'ThresholdLeanXmssSecurity.treeSim_recordPeer_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_recordPeer_shift

/-- info: 'ThresholdLeanXmssSecurity.treeSim_peer_round_pivot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_peer_round_pivot

/-- info: 'ThresholdLeanXmssSecurity.treeSim_peer_round_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_peer_round_state

/-- info: 'ThresholdLeanXmssSecurity.treeSim_rerand_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_rerand_round

/-- info: 'ThresholdLeanXmssSecurity.treeSim_multPeer_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_multPeer_round

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_exchange_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_exchange_eq

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_round_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_round_factor

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_draws_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_draws_mixed

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_balance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_balance

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_outputs_pivot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_outputs_pivot

/-- info: 'ThresholdLeanXmssSecurity.treeSim_recordMode_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_recordMode_shift

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_round_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_round_state

/-- info: 'ThresholdLeanXmssSecurity.treeSim_multCollector_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_multCollector_round

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_first_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_first_factor

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_second_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_second_factor

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_second_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_second_mixed

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_start_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_start_next

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_transcript_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_transcript_exit

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_boundary_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_boundary_done

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_preserves

/-- info: 'ThresholdLeanXmssSecurity.TreeSimRoundStages.collector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeSimRoundStages.collector

/-- info: 'ThresholdLeanXmssSecurity.treeSim_local_streamRel_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_local_streamRel_fixed

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_partial_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_partial_mixed

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_entry_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_entry_mixed

/-- info: 'ThresholdLeanXmssSecurity.treeSim_multCollector_entry_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_multCollector_entry_mixed

/-- info: 'ThresholdLeanXmssSecurity.treeSim_resumeAll_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_resumeAll_rel

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_start_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_start_boundary

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_resume_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_collector_resume_boundary

/-- info: 'ThresholdLeanXmssSecurity.TreeSimCollectorNext.coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeSimCollectorNext.coupling

/-- info: 'ThresholdLeanXmssSecurity.treeSim_relTriple_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_relTriple_support

/-- info: 'ThresholdLeanXmssSecurity.TreeSimCollectorLocalClosure.toClosure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms TreeSimCollectorLocalClosure.toClosure

/-- info: 'ThresholdLeanXmssSecurity.TreeSimCollectorClosure.ofNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeSimCollectorClosure.ofNext

/-- info: 'ThresholdLeanXmssSecurity.TreeSimRoundStages.collectorNext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeSimRoundStages.collectorNext

/-- info: 'ThresholdLeanXmssSecurity.treeSim_hiddenQuery_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_hiddenQuery_frame

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prgBits_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_prgBits_frame

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prssBits_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_prssBits_frame

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prssBits_logged_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_prssBits_logged_frame

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_entry_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_collector_entry_frame

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_resume_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_collector_resume_frame

/-- info: 'ThresholdLeanXmssSecurity.treeSim_collector_resume_logged_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_collector_resume_logged_frame

/-- info: 'ThresholdLeanXmssSecurity.TreeSimCollectorNext.block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimCollectorNext.block

/-- info: 'ThresholdLeanXmssSecurity.TreeSimCollectorNext.fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimCollectorNext.fresh

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prssDraw_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_prssDraw_frame

/-- info: 'ThresholdLeanXmssSecurity.treeSim_elementDraw_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_elementDraw_frame

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prssElements_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_prssElements_frame

/-- info: 'ThresholdLeanXmssSecurity.treeSim_elementDraw_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_elementDraw_mixed

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prssDraw_same' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_prssDraw_same

/-- info: 'ThresholdLeanXmssSecurity.treeSim_prssElements_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_prssElements_mixed

/-- info: 'ThresholdLeanXmssSecurity.treeSim_coin_entry_mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_coin_entry_mixed

/-- info: 'ThresholdLeanXmssSecurity.treeSim_coin_entry_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_coin_entry_frame

/-- info: 'ThresholdLeanXmssSecurity.treeSim_coin_all_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_coin_all_start

/-- info: 'ThresholdLeanXmssSecurity.treeSim_coin_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_coin_local

/-- info: 'ThresholdLeanXmssSecurity.treeSim_coin_round_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_coin_round_factor

/-- info: 'ThresholdLeanXmssSecurity.treeSim_coin_partial_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_coin_partial_factor

/-- info: 'ThresholdLeanXmssSecurity.treeSim_coin_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_coin_preserves

/-- info: 'ThresholdLeanXmssSecurity.TreeSimRoundStages.coin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimRoundStages.coin

/-- info: 'ThresholdLeanXmssSecurity.TreeSimCoinNext.futureZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimCoinNext.futureZero

/-- info: 'ThresholdLeanXmssSecurity.TreeSimCoinNext.coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimCoinNext.coupling

/-- info: 'ThresholdLeanXmssSecurity.treeSim_rerand_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_rerand_entry

/-- info: 'ThresholdLeanXmssSecurity.treeSim_peer_resume_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_peer_resume_local

/-- info: 'ThresholdLeanXmssSecurity.treeSim_peer_resume_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_peer_resume_factor

/-- info: 'ThresholdLeanXmssSecurity.TreeSimRerandData.view' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimRerandData.view

/-- info: 'ThresholdLeanXmssSecurity.TreeSimPeerData.toTreeSimRerandData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimPeerData.toTreeSimRerandData

/-- info: 'ThresholdLeanXmssSecurity.TreeSimPeerData.outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeSimPeerData.outputs

/-- info: 'ThresholdLeanXmssSecurity.TreeSimPeerLocalClosure.resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeSimPeerLocalClosure.resume

/-- info: 'ThresholdLeanXmssSecurity.treeSim_peer_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSim_peer_preserves

/-- info: 'ThresholdLeanXmssSecurity.TreeSimRoundStages.peer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms TreeSimRoundStages.peer

/-- info: 'ThresholdLeanXmssSecurity.treeSim_rerand_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_rerand_preserves

/-- info: 'ThresholdLeanXmssSecurity.TreeSimRoundStages.rerand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimRoundStages.rerand

/-- info: 'ThresholdLeanXmssSecurity.TreeSimCoinNext.coupling_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimCoinNext.coupling_fresh

/-- info: 'ThresholdLeanXmssSecurity.treeSim_peer_partial_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_peer_partial_factor

/-- info: 'ThresholdLeanXmssSecurity.treeSim_onHash_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_onHash_coupling

/-- info: 'ThresholdLeanXmssSecurity.treeSim_fieldReshareZ_pivot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_fieldReshareZ_pivot

/-- info: 'ThresholdLeanXmssSecurity.TreeSimExtendMultData.visible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimExtendMultData.visible

/-- info: 'ThresholdLeanXmssSecurity.TreeSimExtendMultData.outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimExtendMultData.outputs

/-- info: 'ThresholdLeanXmssSecurity.treeSim_extendMult_resume_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_extendMult_resume_factor

/-- info: 'ThresholdLeanXmssSecurity.treeSim_extendMult_partial_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_extendMult_partial_factor

/-- info: 'ThresholdLeanXmssSecurity.TreeSimExtendMultLocalClosure.resume' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimExtendMultLocalClosure.resume

/-- info: 'ThresholdLeanXmssSecurity.treeSim_extendMult_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_extendMult_preserves

/-- info: 'ThresholdLeanXmssSecurity.TreeSimRoundStages.extendMult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimRoundStages.extendMult

/-- info: 'ThresholdLeanXmssSecurity.treeSim_emptyOpen_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_emptyOpen_entry

/-- info: 'ThresholdLeanXmssSecurity.treeSim_emptyCheck_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_emptyCheck_finish

/-- info: 'ThresholdLeanXmssSecurity.treeSim_output_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_output_count

/-- info: 'ThresholdLeanXmssSecurity.treeSim_emptyCheck_jobs_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_emptyCheck_jobs_finish

/-- info: 'ThresholdLeanXmssSecurity.treeSim_emptyOpen_entry_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_emptyOpen_entry_coupling

/-- info: 'ThresholdLeanXmssSecurity.TreeSimEmptyOpenNext.coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimEmptyOpenNext.coupling

/-- info: 'ThresholdLeanXmssSecurity.treeSim_emptyOpen_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_emptyOpen_local

/-- info: 'ThresholdLeanXmssSecurity.treeSim_copyHashes_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_copyHashes_cached

/-- info: 'ThresholdLeanXmssSecurity.treeSim_copyHashes_populated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_copyHashes_populated

/-- info: 'ThresholdLeanXmssSecurity.treeSim_emptyOpen_entry_populated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_emptyOpen_entry_populated

/-- info: 'ThresholdLeanXmssSecurity.treeSim_emptyOpen_head_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_emptyOpen_head_cached

/-- info: 'ThresholdLeanXmssSecurity.treeSim_readOnly_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_readOnly_coupling

/-- info: 'ThresholdLeanXmssSecurity.TreeSimEmptyOpenLocalClosure.local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimEmptyOpenLocalClosure.local

/-- info: 'ThresholdLeanXmssSecurity.TreeSimEmptyOpenLocalClosure.all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimEmptyOpenLocalClosure.all

/-- info: 'ThresholdLeanXmssSecurity.treeSim_open_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_open_entry

/-- info: 'ThresholdLeanXmssSecurity.treeSim_openStep_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_openStep_congr

/-- info: 'ThresholdLeanXmssSecurity.treeSim_open_shift_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_open_shift_step

/-- info: 'ThresholdLeanXmssSecurity.treeSim_onHash_public_coupling' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_onHash_public_coupling

/-- info: 'ThresholdLeanXmssSecurity.TreeSimOpenLocalClosure.local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimOpenLocalClosure.local

/-- info: 'ThresholdLeanXmssSecurity.TreeSimOpenLocalClosure.terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimOpenLocalClosure.terminal

/-- info: 'ThresholdLeanXmssSecurity.treeSim_open_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_open_preserves

/-- info: 'ThresholdLeanXmssSecurity.TreeSimRoundStages.opening' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimRoundStages.opening

/-- info: 'ThresholdLeanXmssSecurity.treeSim_emptyOpen_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_emptyOpen_terminal

/-- info: 'ThresholdLeanXmssSecurity.treeSim_emptyOpen_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_emptyOpen_preserves

/-- info: 'ThresholdLeanXmssSecurity.TreeSimRoundStages.openingEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimRoundStages.openingEmpty

/-- info: 'ThresholdLeanXmssSecurity.treeSim_streamWorld_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_streamWorld_grows

/-- info: 'ThresholdLeanXmssSecurity.treeSim_stream_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_stream_grows

/-- info: 'ThresholdLeanXmssSecurity.treeSim_logged_grows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_logged_grows

/-- info: 'ThresholdLeanXmssSecurity.TreeSimEmptyOpenNext.populated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimEmptyOpenNext.populated

/-- info: 'ThresholdLeanXmssSecurity.TreeSimEmptyOpenNext.coupling_populated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimEmptyOpenNext.coupling_populated

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimulationHop

/-- info: 'ThresholdLeanXmssSecurity.treeSim_digest_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_digest_entry

/-- info: 'ThresholdLeanXmssSecurity.treeSim_check_open_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_check_open_entry

/-- info: 'ThresholdLeanXmssSecurity.treeSim_check_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSim_check_preserves

/-- info: 'ThresholdLeanXmssSecurity.TreeSimRoundStages.check' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TreeSimRoundStages.check

/-- info: 'ThresholdLeanXmssSecurity.treeSimRoundCore_stages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimRoundCore_stages

/-- info: 'ThresholdLeanXmssSecurity.treeSimStagesGoal_of_cores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms treeSimStagesGoal_of_cores

/-- info: 'ThresholdLeanXmssSecurity.treeSimulationHopClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeSimulationHopClosed


end ThresholdLeanXmssSecurity
