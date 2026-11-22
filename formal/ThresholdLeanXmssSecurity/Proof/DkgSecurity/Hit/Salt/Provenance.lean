import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Shift
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Cache
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Salt.Merge
import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Shared.Search

/-!
# The salt of a hidden term by the origin of each digest call

An honest operator reads the 256 bits of a salt and gives them back as the salt of one digest call. So
the hidden salt is in the hands of the program, and a statement on the world alone cannot say that it
stays hidden. This file states the program fact as an equality of two programs and puts each other
step on the world.

* `saltShift D δ` adds `δ` to the 256 cells at the stream index 2 of each place of a hidden term.
  `shiftQ_run` moves this shift from the hidden table to the answers that the program reads.
* `provShift D δ` is a rewrite of the calls of a program. It keeps a queue of the salt reads. A free
  digest call takes the first entry of the queue. If the entry is the full salt of a place of a hidden
  term and it is the salt of the call, the call goes to the salt plus `δ`.
* `SaltProv` states that the game program with the shifted answers is the game program with the
  rewritten calls. The honest program uses the bits of a salt only as the salt of its digest calls, in
  the order of its reads.
* `provWorld` is `loggedWorld` with the same queue. A free digest call with a private entry takes its
  answer from a separate table and leaves the hash cache as it is. `named D st` is the set of the
  shifts `δ` for which the hash cache holds a digest cell under a shifted salt of a full hidden place.
* `SaltProvStep` states that the rewritten program in `loggedWorld` is `provWorld` until `δ` is named,
  for each program. `SaltProvCount` bounds the named shifts at the end of the game. `SaltFullLogged`
  states that each hidden place of the end has its 256 cells.
* `hitSalt_of_prov` gives `HitSalt` from the four statements.
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open OracleComp.ProgramLogic
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof

attribute [local instance] Classical.propDecidable

variable {C : Committee}

/-! ## The shift of the salts and the rewrite of the digest calls -/

/-- The shift that adds `δ` to the 256 cells at the stream index 2 of each place of a hidden term. -/
def saltShift (D : C.Coalition) (δ : Fin 256 → Bit) : HiddenCell C → Bit := fun c =>
  match c.1.1 with
  | .term T => if h : ¬ KnownTo D.1 T ∧ c.2.2.1 = 2 ∧ c.2.2.2 < 256 then δ ⟨c.2.2.2, h.2.2⟩ else 0
  | _ => 0

/-- The salt `salt` plus `δ`, as a list of 256 bits. -/
def addSalt (δ : Fin 256 → Bit) (salt : List Bit) : List Bit := List.ofFn fun k : Fin 256 => salt.getD k.val 0 + δ k

/-- The queue of the salt reads. An entry has the place of a read, namely the name, the key and the
label, and the bits that the program read there from the position 0. -/
abbrev ProvQueue (C : Committee) := List (((KeyName C × HashOutput) × ℕ) × List Bit)

/-- The queue after a free read of a stream with the answer `b`. A read at the stream index 2 under
the name of a term starts a new entry at the position 0. At a later position it adds its bit to the
last entry, when the place is the place of that entry and the position is the next one. -/
def pushRead (x : PrgInput C) (b : Bit) (queue : ProvQueue C) : ProvQueue C :=
  match x.1 with
  | .term _ =>
      if x.2.2.2.1 = 2 then
        if x.2.2.2.2 = 0 then queue ++ [(((x.1, x.2.1), x.2.2.1), [b])]
        else match queue.getLast? with
          | some entry =>
              if entry.1 = ((x.1, x.2.1), x.2.2.1) ∧ entry.2.length = x.2.2.2.2 then
                queue.dropLast ++ [(entry.1, entry.2 ++ [b])]
              else queue
          | none => queue
      else queue
  | _ => queue

/-- The entry is the full salt of a place of a hidden term, and it is the salt `salt`. -/
def Private (D : C.Coalition) (entry : ((KeyName C × HashOutput) × ℕ) × List Bit) (salt : List Bit) : Prop :=
  Hidden D entry.1.1.1 ∧ entry.2.length = 256 ∧ entry.2 = salt

/-- The rewrite of the calls of a program. A free read of a stream goes on as it is and updates the
queue. A free digest call takes the first entry of the queue, and with a private entry it goes to the
salt plus `δ`. Each other call goes on as it is. -/
def provShift (D : C.Coalition) (δ : Fin 256 → Bit) :
    QueryImpl (WorldSpec C) (StateT (ProvQueue C) (OracleComp (WorldSpec C))) := fun t =>
  match t with
  | .inr (.inr (.inl (.digest salt history))) => StateT.mk fun queue =>
      match queue with
      | entry :: rest =>
          (fun r => (r, rest)) <$> (query (spec := WorldSpec C) (.inr (.inr (.inl
            (.digest (if Private D entry salt then addSalt δ salt else salt) history)))) :
              OracleComp (WorldSpec C) HashOutput)
      | [] => (fun r => (r, [])) <$> (query (spec := WorldSpec C) (.inr (.inr (.inl (.digest salt history)))) :
          OracleComp (WorldSpec C) HashOutput)
  | .inr (.inr (.inr x)) => StateT.mk fun queue =>
      (fun b => (b, pushRead x b queue)) <$> (query (spec := WorldSpec C) (.inr (.inr (.inr x))) :
        OracleComp (WorldSpec C) Bit)
  | t => StateT.mk fun queue => (fun r => (r, queue)) <$> query (spec := WorldSpec C) t

/-! ## The world with the queue and the separate table -/

/-- The state of `provWorld`, namely the state of `loggedWorld`, the queue of the salt reads and the
separate table of the digests. -/
abbrev ProvState (C : Committee) := LogState C × ProvQueue C × SaltTable

/-- The start of `provWorld`. -/
def provStart : ProvState C := (((∅, ∅), []), [], ∅)

variable (prims : Primitives)

/-- `loggedWorld` with the queue of the salt reads. A free digest call with a private entry takes its
answer from the separate table at its salt and its history hash, and the hash cache does not change.
No answer and no state depends on a shift. -/
def provWorld (D : C.Coalition) : QueryImpl (WorldSpec C) (StateT (ProvState C) ProbComp) := fun t =>
  match t with
  | .inr (.inr (.inl (.digest salt history))) => StateT.mk fun st =>
      match st.2.1 with
      | entry :: rest =>
          if Private D entry salt then
            (fun r => (r.1, (st.1, rest, r.2))) <$>
              ((((List Bit × HashOutput) →ₒ HashOutput).randomOracle (salt, history)).run st.2.2)
          else (fun r => (r.1, (r.2, rest, st.2.2))) <$>
            (loggedWorld prims D (.inr (.inr (.inl (.digest salt history))))).run st.1
      | [] => (fun r => (r.1, (r.2, [], st.2.2))) <$>
          (loggedWorld prims D (.inr (.inr (.inl (.digest salt history))))).run st.1
  | .inr (.inr (.inr x)) => StateT.mk fun st =>
      (fun r => (r.1, (r.2, pushRead x r.1 st.2.1, st.2.2))) <$> (loggedWorld prims D (.inr (.inr (.inr x)))).run st.1
  | t => StateT.mk fun st => (fun r => (r.1, (r.2, st.2))) <$> (loggedWorld prims D t).run st.1

/-- The shifts `δ` for which the hash cache holds a digest cell under a salt of a full hidden place
of the table shifted by `δ`. Each pair of a digest cell and a full hidden place names at most one
shift. -/
def named (D : C.Coalition) (st : ProvState C) : Finset (Fin 256 → Bit) :=
  Finset.univ.filter fun δ => ∃ (salt : List Bit) (history : HashOutput), st.1.1.1 (.digest salt history) ≠ none ∧
    salt ∈ fullHiddenSalts D (shiftCache (saltShift D δ) st.1.1.2)

/-- A counted call asks a digest cell under a salt of a full hidden place of the table shifted by
`δ`. -/
def ShiftHit (D : C.Coalition) (δ : Fin 256 → Bit) (st : LogState C) : Prop :=
  ∃ q ∈ st.2, ∃ (salt : List Bit) (history : HashOutput),
    salt ∈ fullHiddenSalts D (shiftCache (saltShift D δ) st.1.2) ∧ q = .digest salt history

/-! ## The statements -/

variable {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ)

/-- The program fact. The game program where each free read of a salt bit of a hidden term sees its
answer plus `δ` is the game program where each digest call of a holder of a hidden term goes to its
salt plus `δ`. The two sides are equal as programs, for each answer of each call. -/
def SaltProv : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (δ : Fin 256 → Bit),
    shiftQ D (saltShift D δ) (dealtRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A) =
      (simulateQ (provShift D δ) (dealtRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)).run' []

/-- The step on the world, for each program and each shift. In `loggedWorld` with the rewritten calls
a counted call under a shifted full hidden salt has at most the probability that `provWorld` names
the shift. The two runs agree until the hash cache of `provWorld` holds a digest cell under a shifted
full hidden salt. The bound is a mean over the run from the empty start. -/
def SaltProvStep : Prop :=
  ∀ (D : C.Coalition) (δ : Fin 256 → Bit) {α : Type} (oa : OracleComp (WorldSpec C) α),
    Pr{let z ← (simulateQ (loggedWorld prims D) ((simulateQ (provShift D δ) oa).run' [])).run ((∅, ∅), [])}[
        ShiftHit D δ z.2] ≤
      Pr{let y ← (simulateQ (provWorld prims D) oa).run provStart}[δ ∈ named D y.2]

/-- The count on `provWorld`. At the end of the game with the budget `q` the named shifts are at most
the product of the digest cells of the hash cache, at most `q` counted calls and
`gameBatches * n * termCount C` free calls, and of the full hidden places, at most
`gameBatches * n * termCount C`. -/
def SaltProvCount : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E) (q : ℕ), DkgTsigBounded circuits settings runLimit A q →
    ∀ y ∈ support ((simulateQ (provWorld prims D)
      (dealtRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)).run provStart),
      (named D y.2).card ≤ (q + gameBatches settings runLimit * C.n * termCount C) *
        (gameBatches settings runLimit * C.n * termCount C)

/-- At the end of the game in `loggedWorld` each salt of a hidden term is the salt of a place with all
256 cells. -/
def SaltFullLogged : Prop :=
  ∀ (D : C.Coalition) (A : DkgTsigAdversary C E),
    ∀ z ∈ support ((simulateQ (loggedWorld prims D)
      (dealtRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)).run ((∅, ∅), [])),
      hiddenSalts D z.2.1.2 ⊆ fullHiddenSalts D z.2.1.2

/-! ## The glue -/

omit [Fintype E] [DecidableEq E] in
/-- The four statements give `HitSalt`. -/
theorem hitSalt_of_prov (full : SaltFullLogged prims K circuits settings runLimit)
    (prov : SaltProv K circuits settings runLimit) (step : SaltProvStep (C := C) prims)
    (count : SaltProvCount prims K circuits settings runLimit) : HitSalt prims K circuits settings runLimit := by
  intro D A q bounded
  have e := congrArg (fun x => StateT.run x (((∅, ∅), []) : LogState C))
    (sharedDealt_erase prims D K circuits settings runLimit ⟨true, fun _ => 0⟩ A)
  simp only [StateT.run_map] at e
  have h₀ : Pr{let r ← (sharedDealt prims K circuits settings runLimit ⟨true, fun _ => 0⟩ D A).run ((∅, ∅), [])}[
      HitSaltOf D r] = Pr{let z ← (simulateQ (loggedWorld prims D)
        (dealtRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)).run ((∅, ∅), [])}[
      ∃ q ∈ z.2.2, ∃ (salt : List Bit) (history : HashOutput), salt ∈ hiddenSalts D z.2.1.2 ∧
        q = .digest salt history] := by
    rw [← e, prEvent_map]
    rfl
  have key : ∀ δ : Fin 256 → Bit, Pr{let z ← (simulateQ (loggedWorld prims D)
      (dealtRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)).run ((∅, ∅), [])}[
      ∃ q ∈ z.2.2, ∃ (salt : List Bit) (history : HashOutput), salt ∈ hiddenSalts D z.2.1.2 ∧
        q = .digest salt history] ≤
      Pr{let y ← (simulateQ (provWorld prims D)
        (dealtRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)).run provStart}[δ ∈ named D y.2] := by
    intro δ
    have hs := shiftQ_run prims D (saltShift D δ) (dealtRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)
      ((∅, ∅), [])
    have hstart : shiftState (saltShift D δ) (((∅, ∅), []) : LogState C) = ((∅, ∅), []) :=
      shiftState_eq_self _ _ fun _ _ => rfl
    rw [hstart] at hs
    refine le_trans (prEvent_mono_of_support _ _
      (fun z => ShiftHit D δ (shiftState (saltShift D δ) z.2)) fun z hz h => ?_) ?_
    · obtain ⟨q', hq', salt, history, hsalt, rfl⟩ := h
      refine ⟨_, hq', salt, history, ?_, rfl⟩
      have hback : shiftCache (saltShift D δ) (shiftCache (saltShift D δ) z.2.1.2) = z.2.1.2 :=
        congrArg (fun s : LogState C => s.1.2) (shiftState_shiftState (saltShift D δ) z.2)
      change salt ∈ fullHiddenSalts D (shiftCache (saltShift D δ) (shiftCache (saltShift D δ) z.2.1.2))
      rw [hback]
      exact full D A z hz hsalt
    · have h₁ : Pr{let z ← (simulateQ (loggedWorld prims D)
          (dealtRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A)).run ((∅, ∅), [])}[
          ShiftHit D δ (shiftState (saltShift D δ) z.2)] =
          Pr{let z ← (simulateQ (loggedWorld prims D) (shiftQ D (saltShift D δ)
            (dealtRun K circuits settings runLimit ⟨true, fun _ => 0⟩ D A))).run ((∅, ∅), [])}[ShiftHit D δ z.2] := by
        rw [hs.prEvent_eq, prEvent_map]
      rw [h₁, prov D A δ]
      exact step D δ _
  have hmean := prEvent_le_of_shiftMean _ _ (fun y : _ × ProvState C => named D y.2) _ key
    (count D A q bounded)
  unfold dealtProb hitSaltError
  rw [h₀]
  have hcard : (Fintype.card (Fin 256 → Bit) : ℝ≥0∞) = 2 ^ 256 := by
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow, Nat.cast_ofNat]
  rw [hcard] at hmean
  have hfin : ((((q + gameBatches settings runLimit * C.n * termCount C) *
      (gameBatches settings runLimit * C.n * termCount C) : ℕ) : ℝ≥0∞) / 2 ^ 256) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)
  have hreal := ENNReal.toReal_mono hfin hmean
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow] at hreal
  have htwo : (2 : ℝ≥0∞).toReal = 2 := by simp
  rw [htwo] at hreal
  exact hreal

end ThresholdLeanXmssSecurity.DkgSecurityProof

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.hitSalt_of_prov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.hitSalt_of_prov
