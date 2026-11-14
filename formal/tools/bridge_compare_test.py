"""The tests of bridge_compare.py.

    python3 formal/tools/bridge_compare_test.py --old <Bridge folder> --new <Bridge folder>

Each case changes a copy of the two sides in the memory and runs the comparison on the copy. A
case expects a difference or expects none. The two sides with no change have no difference line.
The script writes no file. It prints one line for each case. The exit code is 1 if a case has a
wrong result.
"""
import contextlib, io, sys

sys.dont_write_bytecode = True
import bridge_compare

# The letter of each file in the name of a text, for example `old-H` for the old Handlers.lean.
# The text `both-H` is the old Handlers.lean and the new Handlers.lean.
LETTERS = {"C": "Characterization.lean", "H": "Handlers.lean", "A": "Ambient.lean", "L": "LeanXmss.lean"}

DIGEST_BITS = "theorem digestBits_eq : digestBits = 128 := rfl"
BOTTOM_LAYER = "theorem bottomLayer_val : bottomLayer.val = 0 := rfl"
TOP_LAYER = "theorem topLayer_val : topLayer.val = 1 := rfl"
KEY_AT_OLD = "theorem keyAt_old : keyAt = LeanXmss.keyAt := rfl"
FIELD_BYTES_NEW = "theorem fieldBytes_eq (fields : TweakFields) :"
FALSE_HYPOTHESIS = "variable (h : False)\ninclude h\n"

# Each case as its name, True if it expects a difference, and its changes. A change is a text,
# a part of this text and the new part.
CASES = [
    ("no change", False, []),

    # The statements after the dictionary.
    ("C statement token", True, [("old-C", "if b = a then 1 else 0 :=\n  probOutput_pure", "if a = b then 1 else 0 :=\n  probOutput_pure")]),
    ("C extra hypothesis", True, [("old-C", "theorem failureProbability_eq_zero (mx : OracleComp spec α) :", "theorem failureProbability_eq_zero (mx : OracleComp spec α) (h : True) :")]),
    ("C abbrev body", True, [("old-C", "(fun r => r.1.2) <$> runWorld prims\n    (realExecution", "(fun r => r.1.1) <$> runWorld prims\n    (realExecution")]),
    ("C after (E := E)", True, [("old-C", "streamKeyError C +\n", "streamKeyError C + 0 +\n")]),
    ("C extra variable", True, [("old-C", "variable [Field E] [Fintype E] [Algebra Bit E]", "variable [Field E] [Fintype E] [Algebra Bit E] [DecidableEq E]")]),
    ("C removed theorem", True, [("old-C", "theorem tsum_outputProbability (mx : OracleComp spec α) : ∑' a, outputProbability mx a = 1 :=\n  tsum_probOutput_of_liftM_PMF mx\n", "")]),
    ("C doc comment", True, [("old-C", "A computation always returns an output.", "A computation returns an output.")]),
    ("C example", True, [("old-C", "example (mx : ProbComp α) (p : α → Prop) [DecidablePred p] :", "example (mx : ProbComp α) (p : α → Prop) [DecidablePred p] (h : True) :")]),
    ("C new side changed", True, [("new-C", "eventProbability (mx >>= f) p = ∑' a, outputProbability mx a * eventProbability (f a) p := by", "eventProbability (mx >>= f) p = ∑' a, eventProbability (f a) p * outputProbability mx a := by")]),
    ("C proof only", False, [("old-C", "  probFailure_of_liftM_PMF mx", "  by\n    simp\n\n    done")]),
    ("H writer log", True, [("old-H", "(fun r' => (r'.1, r.2 * r'.2)) <$> (f r.1).run", "(fun r' => (r'.1, r'.2)) <$> (f r.1).run")]),
    ("H budget equation", True, [("old-H", "(p t → 0 < n) ∧ ∀ u, IsQueryBoundP (f u) p (if p t then n - 1 else n)", "(p t → 0 < n) ∧ ∀ u, IsQueryBoundP (f u) p n")]),
    ("H abbrev without the cache lookup", True, [("old-H", "      | some u => pure (u, cache)\n      | none => ($ᵗ R) >>= fun u => pure (u, cache.cacheQuery d u)\n\n/-- The real experiment", "      | some _ => ($ᵗ R) >>= fun u => pure (u, cache.cacheQuery d u)\n      | none => ($ᵗ R) >>= fun u => pure (u, cache.cacheQuery d u)\n\n/-- The real experiment")]),
    ("H extra hypothesis", True, [("old-H", "theorem cache_empty (t : spec.Domain) :", "theorem cache_empty (t : spec.Domain) (h : True) :")]),
    ("H removed theorem", True, [("old-H", "/-- The log `1` of the counting handler is the count 0. -/\ntheorem toAdd_one : Multiplicative.toAdd (1 : Multiplicative ℕ) = 0 :=\n  rfl\n", "")]),
    ("H new side changed", True, [("new-H", "prf.keygen >>= fun k => simulateQ (prfRealAnswer prf k) adversary", "simulateQ (prfRealAnswer prf (prf.eval · · |> fun _ => default)) adversary")]),
    ("H dictionary body and proof only", False, [("old-H", "  .roll t k", "  .liftBind t k"), ("old-H", "  ⟨f, fun _ => rfl⟩", "  ⟨f, fun _ => by\n    rfl⟩")]),
    ("A constant", True, [("old-A", DIGEST_BITS, "theorem digestBits_eq : digestBits = 127 := rfl")]),
    ("A copied body", True, [("old-A", "truncateHash output = output.extractLsb' 0 digestBits", "truncateHash output = 0")]),
    ("A field order", True, [("old-A", "e.symm (root, parameter) = ⟨root, parameter⟩", "e.symm (root, parameter) = ⟨parameter, root⟩")]),
    ("A removed theorem", True, [("old-A", "theorem hashSpec_eq : HashSpec = (List UInt8 →ₒ BitVec 256) := rfl\n", "")]),
    ("A new side changed", True, [("new-A", "theorem chainStep_eq : ChainStep = Fin 3 := rfl", "theorem chainStep_eq : ChainStep = Fin 4 := rfl")]),
    ("A dictionary body and proof only", False, [("old-A", "part.randomness", "part.randomizer"), ("old-A", "theorem layer_eq : Layer = Fin 2 := rfl", "theorem layer_eq : Layer = Fin 2 := by\n  rfl")]),

    # The header, the dictionary and the commands.
    ("C added variable with include in the dictionary", True, [("old-C", "[IsUniformSpec spec] {α β : Type}\n", "[IsUniformSpec spec] {α β : Type}\n\n" + FALSE_HYPOTHESIS)]),
    ("A added variable with include before the dictionary", True, [("old-A", "namespace ThresholdLeanXmss.Ambient\n", "namespace ThresholdLeanXmss.Ambient\n\n" + FALSE_HYPOTHESIS)]),
    ("L added variable with include", True, [("new-L", "namespace ThresholdLeanXmss.OldLeanXmss\n", "namespace ThresholdLeanXmss.OldLeanXmss\n\n" + FALSE_HYPOTHESIS)]),
    ("H added hypothesis in a section header", True, [("old-H", "section Simulation\n\nvariable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} {α β : Type}", "section Simulation\n\nvariable {ι : Type} {spec : OracleSpec ι} {m : Type → Type} {α β : Type} (h : False)")]),
    ("C added hypothesis in the class of the uniform specs", True, [("new-C", "[OracleSpec.UniformAnswerMeasure spec] {α β : Type}", "[OracleSpec.UniformAnswerMeasure spec] [Subsingleton ι] {α β : Type}")]),
    ("C changed open line", True, [("old-C", "open OracleComp OracleSpec LeanXmss ENNReal", "open OracleComp OracleSpec LeanXmss ENNReal Classical")]),
    ("A changed open line on the new side", True, [("new-A", "open OracleComp OracleSpec HashSig LeanXmss", "open OracleComp OracleSpec HashSig LeanXmss XmssSecurity")]),
    ("C added import", True, [("old-C", "import ThresholdLeanXmss.Statement\n", "import ThresholdLeanXmss.Statement\nimport Mathlib\n")]),
    ("A changed import", True, [("new-A", "import ThresholdLeanXmss.Scheme", "import ThresholdLeanXmss.Ideal")]),
    ("H changed option", True, [("old-H", "set_option autoImplicit false", "set_option autoImplicit true")]),
    ("A added instance line", True, [("old-A", "namespace ThresholdLeanXmss.Ambient\n", "namespace ThresholdLeanXmss.Ambient\n\nlocal instance : Inhabited Digest := ⟨0⟩\n")]),
    ("A changed instance line", True, [("both-A", "namespace ThresholdLeanXmss.Ambient\n", "namespace ThresholdLeanXmss.Ambient\n\ninstance : Inhabited Bool := ⟨true⟩\n"), ("old-A", "Inhabited Bool := ⟨true⟩", "Inhabited Bool := ⟨false⟩")]),
    ("A same instance line on the two sides", False, [("both-A", "namespace ThresholdLeanXmss.Ambient\n", "namespace ThresholdLeanXmss.Ambient\n\ninstance : Inhabited Bool := ⟨true⟩\n")]),
    ("C added notation in the dictionary", True, [("old-C", "/-- The probability that `mx` returns `a`. -/", "local notation \"ℙ\" => failureProbability\n\n/-- The probability that `mx` returns `a`. -/")]),
    ("C changed type of a dictionary entry", True, [("old-C", "abbrev failureProbability (mx : OracleComp spec α) : ℝ≥0∞ := Pr[⊥ | mx]", "abbrev failureProbability (mx : OracleComp spec α) : ℝ := (Pr[⊥ | mx]).toReal")]),
    ("C changed module doc", False, [("old-C", "VCVio at `cbd4144` gives a computation a mass function.", "VCVio at `cbd4144` gives a computation a function.")]),
    ("C command after the module doc", True, [("old-C", "-/\n\nset_option autoImplicit false", "-/ variable (h : False)\n\nset_option autoImplicit false")]),
    ("C command in a module doc that ends early", True, [("old-C", "The part `Dictionary` gives", "-/ variable (h : False) /-! The part `Dictionary` gives")]),
    ("C command after a proof", True, [("old-C", "  probFailure_of_liftM_PMF mx\n", "  probFailure_of_liftM_PMF mx\n  variable (h : False)\n  include h\n")]),
    ("C command in a comment of a proof", False, [("old-C", "  probFailure_of_liftM_PMF mx\n", "  -- variable (h : False) include h\n  probFailure_of_liftM_PMF mx\n")]),
    ("H command in a dictionary body", True, [("old-H", "  .roll t k\n", "  .roll t k\n  open Classical\n")]),
    ("A command in the axiom checks", True, [("old-A", "#print axioms digestBits_eq\n", "#print axioms digestBits_eq\n\n" + FALSE_HYPOTHESIS)]),
    ("C added theorem on the two sides", True, [("both-C", "/-! ## The terms of the statement layer -/\n", "/-! ## The terms of the statement layer -/\n\ntheorem review : True := trivial\n")]),
    ("A added dictionary entry on the two sides", True, [("both-A", "/-! ## The numeric constants -/\n", "abbrev review : Nat := 0\n\n/-! ## The numeric constants -/\n")]),

    # The end of a statement.
    ("A comment with := before the colon of a changed theorem", True, [("both-A", DIGEST_BITS, "theorem digestBits_eq /- := -/ : digestBits = 128 := rfl"), ("old-A", "/- := -/ : digestBits = 128", "/- := -/ : digestBits = 127")]),
    ("A comment with := before the colon on the two sides", False, [("both-A", DIGEST_BITS, "theorem digestBits_eq /- := -/ : digestBits = 128 := rfl")]),
    ("A nested comment with := before a changed type", True, [("both-A", DIGEST_BITS, "theorem digestBits_eq /- a /- b -/ := -/ : digestBits = 128 := rfl"), ("old-A", "-/ : digestBits = 128", "-/ : digestBits = 127")]),
    ("A line comment with := before a changed type", True, [("both-A", "theorem truncateHash_eq (output : HashOutput) :\n", "theorem truncateHash_eq (output : HashOutput) : -- :=\n"), ("old-A", "truncateHash output = output.extractLsb' 0 digestBits", "truncateHash output = 0")]),
    ("A string with := before a changed type", True, [("both-A", DIGEST_BITS, "theorem digestBits_eq (_ : String := \") := \") : digestBits = 128 := rfl"), ("old-A", "\") : digestBits = 128", "\") : digestBits = 127")]),
    ("A character literal before a changed type", True, [("both-A", DIGEST_BITS, "theorem digestBits_eq (_ : Char := ')') : digestBits = 128 := rfl"), ("old-A", "')') : digestBits = 128", "')') : digestBits = 127")]),
    ("C changed text after the bar of an absolute value", True, [("old-C", "(outputProbability (prfIdealRun adversary) true).toReal| :=\n  rfl", "(outputProbability (prfIdealRun adversary) false).toReal| :=\n  rfl")]),
    ("H changed text after the bar of a match in a statement", True, [("old-H", "      | none => ($ᵗ spec.Range t) >>= fun u => pure (u, cache.cacheQuery t u) := by", "      | none => ($ᵗ spec.Range t) >>= fun u => pure (u, cache) := by")]),
    ("A changed statement before a where", True, [("both-A", BOTTOM_LAYER, "theorem bottomLayer_val : bottomLayer.val = 0 where\n  proof := rfl"), ("old-A", "bottomLayer.val = 0 where", "bottomLayer.val = 1 where")]),
    ("A changed proof after a where", False, [("both-A", BOTTOM_LAYER, "theorem bottomLayer_val : bottomLayer.val = 0 where\n  proof := rfl"), ("old-A", "  proof := rfl", "  proof := by rfl")]),
    ("A changed statement before a pattern", True, [("both-A", TOP_LAYER, "theorem topLayer_val : Unit → topLayer.val = 1\n  | () => rfl"), ("old-A", "Unit → topLayer.val = 1", "Unit → topLayer.val = 2")]),
    ("A changed proof after a pattern", False, [("both-A", TOP_LAYER, "theorem topLayer_val : Unit → topLayer.val = 1\n  | () => rfl"), ("old-A", "  | () => rfl", "  | _ => rfl")]),
    ("A statement with a let", True, [("both-A", DIGEST_BITS, "theorem digestBits_eq : let n := 128; digestBits = n := rfl"), ("old-A", "digestBits = n", "digestBits = n + 0")]),

    # The copies and the equations of LeanXmss.lean.
    ("L copy body", True, [("old-L", "def hashOutputBits : Nat := 256", "def hashOutputBits : Nat := 255")]),
    ("L binder rename", True, [("old-L", "(message : HashInput) (randomness : Randomness) : m Digest :=", "(message : HashInput) (randomizer : Randomness) : m Digest :=")]),
    ("L keyword", True, [("old-L", "def decode (digest : Digest)", "abbrev decode (digest : Digest)")]),
    ("L extra attribute in the copies", True, [("old-L", "end Concrete\n", "attribute [irreducible] verify\n\nend Concrete\n")]),
    ("L removed omit line", True, [("old-L", "omit [Monad m] in\n", "")]),
    ("L changed field name", True, [("old-L", "part.path layerHeight leaf", "part.randomness layerHeight leaf")]),
    ("L old equation with one binder", False, [("old-L", KEY_AT_OLD, "theorem keyAt_old (i : LeafIndex) : keyAt i = LeanXmss.keyAt i :=\n  rfl")]),
    ("L proof of an equation only", False, [("old-L", KEY_AT_OLD, "theorem keyAt_old : keyAt = LeanXmss.keyAt := by\n  rfl")]),
    ("L changed right side of an old equation", True, [("old-L", KEY_AT_OLD, "theorem keyAt_old : keyAt = LeanXmss.Concrete.keyAt := rfl")]),
    ("L changed right side of a new equation", True, [("new-L", "keyAt index lay = keyIndexOnLayer index lay", "keyAt index lay = keyIndexOnLayer index bottomLayer")]),
    ("L changed left side of a new equation", True, [("new-L", "theorem numLayers_eq : numLayers = layerCount := rfl", "theorem numLayers_eq : numChains = layerCount := rfl")]),
    ("L hypothesis in a new equation", True, [("new-L", FIELD_BYTES_NEW, "theorem fieldBytes_eq (fields : TweakFields) (h : fields.lo = 0) :")]),
    ("L instance binder in a new equation", True, [("new-L", FIELD_BYTES_NEW, "theorem fieldBytes_eq [Subsingleton TweakFields] (fields : TweakFields) :")]),
    ("L binder of another type in a new equation", True, [("new-L", "theorem chainPayload_eq (chainIdx : ChainIndex) (value : Digest) :", "theorem chainPayload_eq (chainIdx : ChainIndex) (value : Nat) :")]),
    ("L comment with := in a changed equation", True, [("new-L", "theorem numLayers_eq : numLayers = layerCount := rfl", "theorem numLayers_eq /- := -/ : numLayers = chainCount := rfl")]),
    ("L removed equation", True, [("old-L", KEY_AT_OLD + "\n", "")]),
    ("L theorem that is not an equation of a copy", True, [("new-L", "end Concrete\n", "theorem review : True := trivial\n\nend Concrete\n")]),
    ("L composed equations with no change", False, []),
    ("L changed right side of a composed equation", True, [("new-L", "theorem hashOutputBits_eq : BitVec hashOutputBits = HashOutput := rfl", "theorem hashOutputBits_eq : BitVec hashOutputBits = Message := rfl")]),
    ("L changed binder of a composed equation", True, [("new-L", "theorem digit_eq {n : Nat} (digest : Digest) (i : Fin n) :", "theorem digit_eq {n : Nat} (digest : Digest) (i : Fin (n + 1)) :")]),

    # The pinned source.
    ("pinned body", True, [("pinned", "def numChains : Nat := 58", "def numChains : Nat := 59")]),
    ("pinned doc", True, [("pinned", "/-- The sum of a word's digits. -/", "/-- The sum of the digits. -/")]),
    ("pinned extra attribute", True, [("pinned", "attribute [irreducible] verify", "attribute [irreducible] verify\nattribute [reducible] keyAt")]),
    ("pinned shifted lines", True, [("pinned", "def digestBits : Nat := 128\n", "def digestBits : Nat := 128\n\n\n\n\n")]),
    ("pinned variable", True, [("pinned", "variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]", "variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSpec m]")]),
]


def run(texts, changes):
    """The difference lines of the comparison after the changes."""
    texts = dict(texts)
    for text, before, after in changes:
        for target in (["old" + text[4:], "new" + text[4:]] if text.startswith("both") else [text]):
            assert before in texts[target], (target, before)
            texts[target] = texts[target].replace(before, after, 1)
    old, new = ({name: texts[side + letter] for letter, name in LETTERS.items()} for side in ("old-", "new-"))
    with contextlib.redirect_stdout(io.StringIO()):
        return bridge_compare.compare(old, new, texts["pinned"])


def main():
    old, new, pinned = bridge_compare.sides()
    texts = {"pinned": pinned}
    for letter, name in LETTERS.items():
        texts["old-" + letter], texts["new-" + letter] = old[name], new[name]
    wrong = 0
    for name, expected, changes in CASES:
        count = len(run(texts, changes))
        wrong += (count > 0) != expected
        print("ok  " if (count > 0) == expected else "FAIL",
              "expects a difference," if expected else "expects none,        ",
              f"has {count:3} difference lines,", name)
    print(f"{len(CASES)} cases, {wrong} with a wrong result.")
    return wrong


if __name__ == "__main__":
    sys.exit(1 if main() else 0)
