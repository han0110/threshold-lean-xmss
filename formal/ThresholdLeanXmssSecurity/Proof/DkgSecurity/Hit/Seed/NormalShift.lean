import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.NormalForm
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Vector

/-!
# The shift statement on the normal form of the seed generation

* `seedGenAt` is the normal form `seedGenNormal` with the commit addresses `commitAt` and the derive
  addresses `termAt` as parameters. The open call of an honest operator `i` for an honest sender
  `k ≠ i` asks `commitAt k i`, the cell that `k` committed to.
* `PartsShift` states that the normal form on the parts with the term part of a hidden term `T`
  shifted is `seedGenAt` on the unshifted parts with the commit addresses and the derive addresses of
  the shifted parts. So the term parts of `T` enter the program only through these addresses.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof
open ThresholdLeanXmssSecurity.DkgSecurityProof.SeedCompare (hiddenInput shiftAll)

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type}

/-! ## The parts of a hidden term -/

/-- The commit calls of the honest operators with the commit addresses `commitAt`. -/
def commitDrawsAt (D : C.Coalition) (commitAt : C.Party → C.Party → Query C) :
    OracleComp (WorldSpec C) (C.Party → List HashOutput) :=
  OverPermutation.sequenceFin fun i => if i ∈ D.1 then pure [] else
    free (liftComp (C.parties.mapM fun j => hashQuery (commitAt i j)) (LocalSpec C))

/-- The derive calls of operator `i` with the derive addresses `termAt i inbox` of the held terms. -/
def deriveAt (D : C.Coalition) (parts : C.Party → Parts C) (termAt : C.Party → Mail C E → C.Term → Query C)
    (i : C.Party) (inbox : Mail C E) :
    OracleComp (RoSpec C) (HashOutput × (C.Term → HashOutput) × (C.Party → HashOutput)) :=
  hashQuery (.derive .seedGen .parameter (C.parties.map fun k => (normView D parts i inbox k).parameter)) >>=
    fun parameter =>
  C.terms.mapM (fun T => if i ∈ C.holders T then hashQuery (termAt i inbox T) else pure 0) >>= fun term =>
  C.parties.mapM (fun j => if h : j = i then pure 0 else
    hashQuery (.derive .seedGen .pair
      [(normView D parts i inbox (C.pairOf i j (Ne.symm h)).1.1).pair (C.pairOf i j (Ne.symm h)).1.2,
        (normView D parts i inbox (C.pairOf i j (Ne.symm h)).1.2).pair (C.pairOf i j (Ne.symm h)).1.1])) >>=
    fun pair =>
  pure (parameter, fun T => term.getD (C.terms.idxOf T) 0, fun j => pair.getD j.val 0)

/-- The local step of operator `i` after round 2 with the commit addresses `commitAt` and the derive
addresses `termAt`. -/
def revealNextAt (D : C.Coalition) (parts : C.Party → Parts C) (commitAt : C.Party → C.Party → Query C)
    (termAt : C.Party → Mail C E → C.Term → Query C) (committed : C.Party → Mail C E) (i : C.Party)
    (inbox : Mail C E) : OracleComp (LocalSpec C) (Option (SeedGenEchoData C)) :=
  liftComp (C.parties.mapM fun k => hashQuery (if k ∈ D.1 ∨ k = i then openAddress D parts i inbox k else commitAt k i))
    (LocalSpec C) >>= fun opens =>
    if openCheck .seedGen i (parts i) (committed i) (normRevealed D parts i inbox) opens then
      liftComp (deriveAt D parts termAt i inbox) (LocalSpec C) >>= fun keys =>
        liftComp (C.parties.mapM fun j => hashQuery (sharedAddress i j keys.2.1)) (LocalSpec C) >>= fun shared =>
          pure (some (keys, shared))
    else pure none

/-- The normal form with the commit addresses `commitAt` and the derive addresses `termAt`. -/
def seedGenAt (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) (state : net.State)
    (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C) (parts : C.Party → Parts C)
    (commitAt : C.Party → C.Party → Query C) (termAt : C.Party → Mail C E → C.Term → Query C) :
    OracleComp (WorldSpec C) (net.State × (C.Party → Option (Keys C))) :=
  commitDrawsAt D commitAt >>= fun commitments =>
  observe (net.round state (commitMail D commitments)) >>= fun r =>
  programBlock D (early ++ r.2) r.1.2 parameter dealt parts >>= fun _ =>
  levelRound D net (setupRounds - 1) r.1.1 (revealReady (commitInbox D commitments r.1.2))
    (fun i _ => revealOutbox .seedGen i (parts i))
    (fun i _ inbox => revealNextAt D parts commitAt termAt (commitInbox D commitments r.1.2) i inbox) fun f2 s2 d2 =>
  levelRound D net f2 s2 d2 (fun i x => echoOutbox .seedGen i x.1 x.2) echoNext fun _ s3 d3 =>
  pure (s3, fun j => if j ∈ D.1 then none else d3 j)

/-- For a term `T` with no corrupt holder and each shift `c`, the normal form on the parts with the
term part of `T` of each operator `k` shifted by `c k` is the normal form on the unshifted parts in
which the commit calls and the derive calls ask the addresses of the shifted parts. -/
def PartsShift (D : C.Coalition) (net : Adversary C E Unit PEmpty PEmpty) : Prop :=
  ∀ (state : net.State) (early : CallLog C) (parameter : PublicParameter) (dealt : C.Party → Keys C)
    (parts : C.Party → Parts C) (T : C.Term) (c : C.Party → HashOutput), ¬ KnownTo D.1 T →
    seedGenNormal D net state early parameter dealt (shiftAll T c parts) =
      seedGenAt D net state early parameter dealt parts (commitAddress (shiftAll T c parts))
        (termAddress D (shiftAll T c parts))

/-! ## The seed of a hidden term -/

/-! ## The statements at the zero shift -/

section Zero

end Zero

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

