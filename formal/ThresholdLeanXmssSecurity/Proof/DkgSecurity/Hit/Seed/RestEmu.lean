import ThresholdLeanXmssSecurity.Proof.DkgSecurity.Hit.Seed.Rest

/-!
# The rest of the game does not read the emulated keys

With no emulated run, `secRun` always takes the real run of the tree, because `s.runs tree < 0` never
holds. The emulated keys `emu` enter `secRest` only through the emulated runs. So `secRest` on two
values of `emu` is the same program (`secRest_emu_eq`).
-/

set_option autoImplicit false

open OracleComp OracleSpec HashSig LeanXmss ENNReal ThresholdLeanXmss ThresholdLeanXmssSecurity
open ThresholdLeanXmssSecurity.DkgCorrectnessProof

noncomputable section

namespace ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

attribute [local instance] inhabitedField

variable (K : Constants C E) (circuits : Circuits) (settings : Settings) (runLimit : ℕ) (D : C.Coalition)
  (m : Mode) (hm : ∀ tree, m.emulated tree = 0) (parameter : PublicParameter) (seeds : C.Term → HashOutput)
  (dealt : C.Party → Keys C)
include hm

omit [Fintype E] [DecidableEq E] in
theorem secRun_emu (net : Adversary C E Unit PEmpty PEmpty) (emu : C.Party → Option (Keys C)) (tree : Tree) :
    secRun K circuits settings m D net parameter seeds dealt emu tree =
      secRun K circuits settings m D net parameter seeds dealt (fun _ => none) tree := by
  unfold secRun
  refine bind_congr fun s => ?_
  rw [ite_eq_right (by rw [hm]; exact Nat.not_lt_zero _), ite_eq_right (by rw [hm]; exact Nat.not_lt_zero _)]

omit [Fintype E] [DecidableEq E] in
theorem secRuns_emu (net : Adversary C E Unit PEmpty PEmpty) (emu : C.Party → Option (Keys C)) (tree : Tree) :
    ∀ count, secRuns K circuits settings runLimit m D net parameter seeds dealt emu tree count =
      secRuns K circuits settings runLimit m D net parameter seeds dealt (fun _ => none) tree count
  | 0 => rfl
  | count + 1 => by
    unfold secRuns
    refine bind_congr fun s => ?_
    rw [secRun_emu K circuits settings D m hm parameter seeds dealt net emu tree,
      secRuns_emu net emu tree count]

omit [Fintype E] [DecidableEq E] in
theorem secOracles_emu (net : Adversary C E Unit PEmpty PEmpty) (emu : C.Party → Option (Keys C)) :
    secOracles K circuits settings runLimit m D net parameter seeds dealt emu =
      secOracles K circuits settings runLimit m D net parameter seeds dealt (fun _ => none) := by
  funext dealer q
  rcases q with i | b | ⟨i, J, e, message⟩ | ⟨i, J, e, message, parts⟩
  · rfl
  · unfold secOracles secTreeRequest
    simp only [secRuns_emu K circuits settings runLimit D m hm parameter seeds dealt net emu (.bottom b) 1]
    rfl
  · rfl
  · rfl

omit [Fintype E] [DecidableEq E] in
/-- With no emulated run, `secRest` does not read the emulated keys. -/
theorem secRest_emu (A : DkgTsigAdversary C E) (emu : C.Party → Option (Keys C)) :
    secRest K circuits settings runLimit m D A parameter seeds dealt emu =
      secRest K circuits settings runLimit m D A parameter seeds dealt (fun _ => none) := by
  unfold secRest secSigning
  refine bind_congr fun s => bind_congr fun v => ?_
  obtain ⟨state, ok⟩ := v
  refine bind_congr fun _ => ?_
  rw [secRuns_emu K circuits settings runLimit D m hm parameter seeds dealt A.net (committed ok emu) .top runLimit,
    secRuns_emu K circuits settings runLimit D m hm parameter seeds dealt A.net (committed ok fun _ => none) .top
      runLimit,
    secOracles_emu K circuits settings runLimit D m hm parameter seeds dealt A.net (committed ok emu),
    secOracles_emu K circuits settings runLimit D m hm parameter seeds dealt A.net (committed ok fun _ => none)]

omit [Fintype E] [DecidableEq E] in
/-- With no emulated run, `secRest` on two values of the emulated keys is the same program. -/
theorem secRest_emu_eq (A : DkgTsigAdversary C E) (emu emu' : C.Party → Option (Keys C)) :
    secRest K circuits settings runLimit m D A parameter seeds dealt emu =
      secRest K circuits settings runLimit m D A parameter seeds dealt emu' :=
  (secRest_emu K circuits settings runLimit D m hm parameter seeds dealt A emu).trans
    (secRest_emu K circuits settings runLimit D m hm parameter seeds dealt A emu').symm

end ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal

/-- info: 'ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.secRest_emu_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ThresholdLeanXmssSecurity.DkgSecurityProof.SeedNormal.secRest_emu_eq
