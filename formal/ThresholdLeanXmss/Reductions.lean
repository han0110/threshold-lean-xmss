import ThresholdLeanXmss.Ideal

/-!
# The reduction to the AES term

`prgReduction` turns a game into an adversary of the multi-key PRF game of `hiddenStreams`. The
claims of the setup pay its advantage for the PRSS streams under the keys that the coalition lacks.
-/

set_option autoImplicit false

open OracleComp OracleSpec  HashSig LeanXmss

noncomputable section

namespace ThresholdLeanXmss

attribute [local instance] Classical.propDecidable

variable {C : Committee} {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra Bit E]

/-! ## The reduction to the AES term -/

/-- The PRF oracle of the streams under the hidden keys. -/
abbrev StreamSpec (C : Committee) := PRFScheme.PRFOracleSpec ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) Bit

/-- The reduction to `hiddenStreams`. It runs `game` on the world, and each honest stream under a key
that is hidden from `D` comes from the PRF oracle (CDI05, the PRSS of the lacked term). The counted
copy keeps the real answers, also for a hidden key. -/
def prgReduction (prims : Primitives) (D : C.Coalition) (game : OracleComp (WorldSpec C) Bool) :
    PRFScheme.PRFAdversary ((KeyName C × HashOutput) × ℕ × ℕ × ℕ) Bit :=
  let lift := fun {α : Type} (oa : StateT (HashCache C) ProbComp α) =>
    (StateT.mk fun s => liftComp (oa.run s) (StreamSpec C) : StateT (HashCache C) (OracleComp (StreamSpec C)) α)
  let real : QueryImpl (LocalSpec C) (StateT (HashCache C) (OracleComp (StreamSpec C))) :=
    fun t => lift (localAnswer prims t)
  let honest : QueryImpl (LocalSpec C) (StateT (HashCache C) (OracleComp (StreamSpec C))) := fun t =>
    match t with
    | .inr (.inr x) => if Hidden D x.1 then
        StateT.lift (query (spec := StreamSpec C) (.inr ((x.1, x.2.1), x.2.2)))
      else real (.inr (.inr x))
    | t => real t
  let programming : QueryImpl (ProgramSpec C) (StateT (HashCache C) (OracleComp (StreamSpec C))) :=
    fun x => lift (programAnswer x)
  (simulateQ ((real + programming) + honest) game).run' ∅

end ThresholdLeanXmss
