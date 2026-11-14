"""Compares the two sides of the bridge.

The bridge is the folder `ThresholdLeanXmssSecurity/Bridge` with four Lean files. The old side is
for VCVio `cbd4144` and leanVM `1acdff19`. The new side is for VCVio `5f9baf12` and leanVM
`f5f3672f`. The two sides prove the same statements. This script compares the text of the two
sides, and it compares the copies of `LeanXmss.lean` with the pinned source of leanVM `1acdff19`.
It reads the pinned source from the folder `.lake` of the project that holds the old side.

    python3 formal/tools/bridge_compare.py --old <Bridge folder> --new <Bridge folder>

The script reads each file with a lexer for the comments, the strings and the character literals
of Lean. It removes the module doc, each proof, each body of the dictionary and the axiom checks.
It keeps each removed line that holds a word of COMMANDS outside a comment. All text that stays
must be equal on the two sides, apart from the line pairs of LINE_PAIRS. Thus a `variable`, an
`include`, an `open`, an instance or an option is on the two sides, or it is a difference.

The dictionary is the part between the heading `Dictionary` and the first heading of the
statements. Its entries have different bodies on the two sides. The script prints the two bodies
of each entry, and it compares the text before each body.

In `LeanXmss.lean`, each copy has one equation on each side. The script removes the equations
from the compared text, because the two sides name different upstream definitions. It compares
each equation with the names of UPSTREAM. Some equations of the new side relate a copy to a
composition of upstream definitions. Each of them must be equal to its statement in COMPOSED, and
the script prints these statements.

The script compares text. It does not elaborate a term, and it does not read an imported module.
A person must read LINE_PAIRS, UPSTREAM, COMPOSED and the printed dictionaries. The script prints
each difference and one count line for each check. The exit code is 1 if a difference exists.
"""
import argparse, bisect, collections, difflib, os, re, sys

DICTIONARY = "/-! ## Dictionary -/"
AXIOM_CHECKS = re.compile(r"/-! The \w+ fails if the axioms")
DECLARATION = re.compile(r"(theorem|example|abbrev|def)\b")

# Each file with the heading that ends its dictionary, and the count of each keyword at the start
# of a line before the axiom checks. An `abbrev` of the dictionary counts as `dictionary`.
FILES = {
    "Characterization.lean": ("/-! ## The evaluation of a computation -/",
                              {"dictionary": 8, "theorem": 19, "example": 3, "abbrev": 4}),
    "Handlers.lean": ("/-! ## The simulation of a computation -/",
                      {"dictionary": 5, "theorem": 69, "example": 4, "abbrev": 3}),
    "Ambient.lean": ("/-! ## The numeric constants -/", {"dictionary": 2, "theorem": 28}),
    "LeanXmss.lean": (None, {"theorem": 33, "abbrev": 3, "def": 30}),
}

# Each line that is different on the two sides by design, as the old line, the new line and the
# reason. The old line is None if only the new side has the line. Each line occurs one time.
MEASURE_LEMMAS = "The proofs for VCVio `5f9baf12` read lemmas of this module."
HASH_SIG = "leanVM `f5f3672f` has a part of its names in the namespace `HashSig`."
SCHEME_IMPORT = "The new side imports the protocol file, and that file imports `LeanXmss.Scheme`."
FIELD_NAME = "`LayerSignature` has new field names at leanVM `f5f3672f`."
LINE_PAIRS = {
    "Characterization.lean": [
        (None, "import VCVio.OracleComp.EvalDist.Sum", MEASURE_LEMMAS),
        (None, "import VCVio.OracleComp.Constructions.SampleableType.Measure", MEASURE_LEMMAS),
        (None, "import ToMathlib.MeasureTheory.Measure.Coupling.Maximal", MEASURE_LEMMAS),
        ("open OracleComp OracleSpec LeanXmss ENNReal",
         "open OracleComp OracleSpec HashSig LeanXmss ENNReal", HASH_SIG),
        ("variable {ι : Type} {spec : OracleSpec ι} [IsUniformSpec spec] {α β : Type}",
         "variable {ι : Type} {spec : OracleSpec ι} [OracleSpec.UniformAnswerMeasure spec] {α β : Type}",
         "VCVio `5f9baf12` has the class `UniformAnswerMeasure` in the place of `IsUniformSpec`."),
    ],
    "Handlers.lean": [
        ("open OracleComp OracleSpec LeanXmss ENNReal",
         "open OracleComp OracleSpec HashSig LeanXmss ENNReal", HASH_SIG),
    ],
    "Ambient.lean": [
        ("import LeanXmss.Scheme", "import ThresholdLeanXmss.Scheme", SCHEME_IMPORT),
        ("open OracleComp OracleSpec LeanXmss", "open OracleComp OracleSpec HashSig LeanXmss", HASH_SIG),
    ],
    "LeanXmss.lean": [
        ("import LeanXmss.Scheme", "import ThresholdLeanXmss.Scheme", SCHEME_IMPORT),
        ("open OracleComp OracleSpec LeanXmss", "open OracleComp OracleSpec HashSig LeanXmss", HASH_SIG),
        ("  let some leaf ← otsLeaf parameter lay key message part.randomness part.chainValues | return none",
         "  let some leaf ← otsLeaf parameter lay key message part.randomizer part.chainValues | return none",
         FIELD_NAME),
        ("  let root ← treeFold parameter lay key part.path layerHeight leaf",
         "  let root ← treeFold parameter lay key part.authenticationPath layerHeight leaf", FIELD_NAME),
    ],
}

# Each copy of `LeanXmss.lean` with the upstream definition of its equation on the old side and on
# the new side. The equation of the copy `c` with the upstream definition `u` has the form
# `c x = u x`. Here `x` is the list of the explicit binders of the theorem, in their order, and
# this list can be empty. The type of each binder is the type of the same parameter of `c`. The
# new name is None if the equation of the new side does not have this form. COMPOSED holds such
# an equation.
EQUATION_SUFFIXES = ("_old", "_eq")
UPSTREAM = {
    "hashOutputBits": ("LeanXmss.hashOutputBits", None),
    "messageBits": ("LeanXmss.messageBits", None),
    "publicParameterBits": ("LeanXmss.publicParameterBits", None),
    "numChains": ("LeanXmss.numChains", "chainCount"),
    "numLayers": ("LeanXmss.numLayers", "layerCount"),
    "Randomness": ("LeanXmss.Randomness", "Randomizer"),
    "Digit": ("LeanXmss.Digit", "WinternitzDigit"),
    "keyAt": ("LeanXmss.keyAt", "keyIndexOnLayer"),
    "bytesLE": ("LeanXmss.bytesLE", "littleEndianBytes"),
    "fieldBytes": ("LeanXmss.fieldBytes", "addressBytes"),
    "layerHi": ("LeanXmss.layerHi", "LeanXmss.layerHi"),
    "hashDomainFields": ("LeanXmss.hashDomainFields", "LeanXmss.hashDomainFields"),
    "tweakBytes": ("LeanXmss.tweakBytes", "LeanXmss.tweakBytes"),
    "tweakableHashInput": ("LeanXmss.tweakableHashInput", "LeanXmss.tweakableHashInput"),
    "Codeword.digit": ("LeanXmss.Codeword.digit", None),
    "Codeword.encoding": ("LeanXmss.Codeword.encoding", "digestDigits"),
    "Codeword.sum": ("LeanXmss.Codeword.sum", "LeanXmss.Codeword.sum"),
    "Codeword.Valid": ("LeanXmss.Codeword.Valid", "LeanXmss.Codeword.Valid"),
    "Codeword.decode": ("LeanXmss.Codeword.decode", "LeanXmss.Codeword.decode"),
    "Concrete.sequenceFin": ("LeanXmss.Concrete.sequenceFin", "OverPermutation.sequenceFin"),
    "Concrete.oracleHash": ("LeanXmss.Concrete.oracleHash", "Verification.oracleHashWithHash"),
    "Concrete.tweakableHash": ("LeanXmss.Concrete.tweakableHash", "Verification.tweakableHashWithHash"),
    "Concrete.chainPayload": ("LeanXmss.Concrete.chainPayload", "Verification.chainPayload"),
    "Concrete.chainWalk": ("LeanXmss.Concrete.chainWalk", "Verification.chainWalkWithHash"),
    "Concrete.recoverChain": ("LeanXmss.Concrete.recoverChain", "Verification.recoverChainWithHash"),
    "Concrete.leafPayload": ("LeanXmss.Concrete.leafPayload", "digestsPayload"),
    "Concrete.leafHash": ("LeanXmss.Concrete.leafHash", "Verification.leafHashWithHash"),
    "Concrete.messageDigest": ("LeanXmss.Concrete.messageDigest", "Verification.messageDigestWithHash"),
    "Concrete.otsLeaf": ("LeanXmss.Concrete.otsLeaf", "Verification.otsLeafWithHash"),
    "Concrete.nodePayload": ("LeanXmss.Concrete.nodePayload", "OverPermutation.nodePayload"),
    "Concrete.treeFold": ("LeanXmss.Concrete.treeFold", "Verification.treeFoldWithHash"),
    "Concrete.layerRoot": ("LeanXmss.Concrete.layerRoot", "Verification.layerRootWithHash"),
    "Concrete.verify": ("LeanXmss.Concrete.verify", "Verification.verifyWithHash"),
}

# Each copy with an equation of the new side that relates the copy to a composition of upstream
# definitions, as the statement of the equation and the reason. The statement is the text before
# the proof with one space for each run of white space. The equation must be equal to it.
NO_WIDTH = "The namespaces `LeanXmss` and `HashSig` of leanVM `f5f3672f` have no constant for this width, and "
COMPOSED = {
    "hashOutputBits": ("theorem hashOutputBits_eq : BitVec hashOutputBits = HashOutput",
                       NO_WIDTH + "`HashOutput` is `BitVec 256`."),
    "messageBits": ("theorem messageBits_eq : BitVec messageBits = Message",
                    NO_WIDTH + "`Message` is `BitVec 256`."),
    "publicParameterBits": ("theorem publicParameterBits_eq : BitVec publicParameterBits = PublicParameter",
                            NO_WIDTH + "`PublicParameter` is `BitVec 128`."),
    "Codeword.digit": (
        "theorem digit_eq {n : Nat} (digest : Digest) (i : Fin n) : "
        "digit digest i.val = digestDigits digest i",
        "`digestDigits` of leanVM `f5f3672f` takes the index as a `Fin n`, and the copy takes it as a `Nat`."),
}
assert set(COMPOSED) == {name for name, (_, new_name) in UPSTREAM.items() if new_name is None}

# The pinned keyword and the copied keyword of a declaration with a named change.
NAMED_KEYWORDS = {"Codeword.Valid": ("def", "abbrev")}
# The instances and the attributes of the pinned source. They have no copy.
NAMED_OMISSIONS = ["instance : DecidablePred Valid :=", "attribute [irreducible] verify"]
# The path of the pinned source from the folder of the old side.
PINNED = "../../.lake/packages/lean-xmss-security/formal/lean_xmss/LeanXmss/Scheme.lean"

TOKEN = re.compile(r"""
    (?P<comment> --[^\n]* | /- )
  | (?P<string>  r(?P<hashes>\#*)"[\s\S]*?"(?P=hashes) | "(?:\\[\s\S]|[^"\\])*" )
  | (?P<char>    '(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])' )
  | (?P<word>    «[^»\n]*» | \w[\w'!?.]* )
  | (?P<space>   \s+ )
  | (?P<symbol>  := | [\s\S] )
""", re.VERBOSE)
OPEN, CLOSE = set("([{⟨⦃"), set(")]}⟩⦄")
# Each word that starts a command that can change the meaning of a later statement.
COMMANDS = {"variable", "include", "omit", "universe", "open", "export", "namespace", "section",
            "end", "notation", "notation3", "infix", "infixl", "infixr", "prefix", "postfix",
            "macro", "macro_rules", "syntax", "elab", "elab_rules", "instance", "attribute",
            "set_option", "axiom", "theorem", "lemma", "def", "abbrev", "alias", "opaque",
            "structure", "class", "inductive"}
# Each word that can put a `:=` into a statement outside all brackets. The script does not find
# the end of a statement that holds one of them outside all brackets.
UNREAD = {"let", "have", "letI", "haveI", "by", "do", "calc"}
# Each word that can put the `|` of a pattern into a statement outside all brackets.
PATTERN_OWNERS = {"match", "fun", "λ"}


def read(path):
    with open(path, encoding="utf-8") as file:
        return file.read()


def tokens(text):
    """Each token of Lean text as its kind, its first index and the index after its last
    character. A block comment is one token, and block comments nest."""
    index = 0
    while index < len(text):
        match = TOKEN.match(text, index)
        end = match.end()
        if match.group() == "/-":
            depth, end = 0, len(text)
            for mark in re.finditer(r"/-|-/", text[index:]):
                depth += 1 if mark.group() == "/-" else -1
                if depth == 0:
                    end = index + mark.end()
                    break
        yield match.lastgroup, index, end
        index = end


def scan(text):
    """The words and the symbols of `text` outside the comments and the strings, each one as its
    first index, the index after its last character and its line. The second result is the number
    of each line that starts in a comment or in a string."""
    code, inside, line = [], set(), 0
    for kind, start, end in tokens(text):
        newlines = text.count("\n", start, end)
        if kind in ("comment", "string"):
            inside.update(range(line + 1, line + newlines + 1))
        elif kind in ("word", "symbol"):
            code.append((start, end, line))
        line += newlines
    return code, inside


def words(text):
    """The words and the symbols of `text` outside the comments and the strings."""
    return [text[start:end] for start, end, _ in scan(text)[0]]


def statement_end(text, code):
    """The index of the `:=`, the `where` or the `|` that ends the statement of the declaration
    with the words and symbols `code`. A `|` ends the statement only if it has white space on its
    two sides and no word of PATTERN_OWNERS stands before it. Thus the `|` of an absolute value
    and the `|` of a `match` in the statement do not end it. The result is None if the script
    cannot find the end."""
    depth, patterns = 0, False
    for start, end, _ in code:
        token = text[start:end]
        if token in OPEN:
            depth += 1
        elif token in CLOSE:
            depth -= 1
        elif depth == 0 and token in UNREAD:
            return None
        elif depth == 0 and token in PATTERN_OWNERS:
            patterns = True
        elif depth == 0 and (token in (":=", "where") or token == "|" and not patterns
                             and text[start - 1].isspace() and text[end:end + 1].isspace()):
            return start
    return None


def statement(declaration):
    """The text of a declaration before the end of its statement, or None if the script cannot
    find the end."""
    cut = statement_end(declaration, scan(declaration)[0])
    return None if cut is None else declaration[:cut]


def declaration_end(lines, first, inside):
    """The index of the next line that is not empty, starts in column 0 and starts outside a
    comment."""
    index = first + 1
    while index < len(lines) and (lines[index] == "" or lines[index][0].isspace() or index in inside):
        index += 1
    return index


def without_module_doc(text):
    """The text without its first comment that starts with `/-!`."""
    for kind, start, end in tokens(text):
        if kind == "comment" and text.startswith("/-!", start):
            return text[:start] + text[end:]
    return text


def without_blank_runs(lines):
    return [line for index, line in enumerate(lines) if line != "" or (index > 0 and lines[index - 1] != "")]


def command_lines(text, lines, code, first):
    """Each line that holds a word of COMMANDS at the index `first` or after it."""
    numbers = {line for start, end, line in code if start >= first and text[start:end] in COMMANDS}
    return [lines[number] for number in sorted(numbers)]


def reduced(name, text):
    """The lines of one file that the two sides compare, the count of each keyword, the entries of
    the dictionary as the text before the body and the body, and the difference messages."""
    text = without_module_doc(text)
    lines = text.split("\n")
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line) + 1)
    code, inside = scan(text)
    starts = [start for start, _, _ in code]
    kept, counts, dictionary, found = [], collections.Counter(), [], []
    part, index = "header", 0
    while index < len(lines):
        line = lines[index]
        if line == DICTIONARY:
            part = "dictionary"
        elif line == FILES[name][0]:
            part = "statements"
        elif AXIOM_CHECKS.match(line):
            part = "axiom checks"
        declared = None if index in inside or part == "axiom checks" else DECLARATION.match(line)
        keyword = declared.group(1) if declared else None
        end = declaration_end(lines, index, inside) if keyword else index + 1
        inner = code[bisect.bisect_left(starts, offsets[index]):bisect.bisect_left(starts, offsets[end])]
        entry = keyword == "abbrev" and part == "dictionary"
        if keyword:
            counts["dictionary" if entry else keyword] += 1
        has_proof = entry or keyword in ("theorem", "example")
        cut = statement_end(text, inner) if has_proof else None
        if part == "axiom checks":
            kept += command_lines(text, lines, inner, offsets[index])
        elif cut is not None:
            before = text[offsets[index]:cut]
            if entry:
                dictionary.append((before, text[cut:offsets[end]].strip()))
            mark = (before + "<body>" if entry else
                    "<equation>" if name == "LeanXmss.lean" else before + "<proof>")
            kept += mark.split("\n") + command_lines(text, lines, inner, cut) + [""]
        else:
            if has_proof:
                found.append(f"The script cannot find the end of the statement of `{line}` in {name}.")
            kept += lines[index:end]
        index = end
    return without_blank_runs(kept), dict(counts), dictionary, found


def with_line_pairs(name, old_lines, new_lines):
    """The old lines with the new line of each pair of LINE_PAIRS, the new lines without each line
    that only the new side has, and one message for each pair that does not occur one time."""
    found = []
    for old_line, new_line, _ in LINE_PAIRS[name]:
        times = (1 if old_line is None else old_lines.count(old_line), new_lines.count(new_line))
        if times != (1, 1):
            found.append(f"{name} does not hold one time the line pair `{old_line}` and `{new_line}`.")
        elif old_line is None:
            new_lines = [line for line in new_lines if line != new_line]
        else:
            old_lines = [new_line if line == old_line else line for line in old_lines]
    return old_lines, new_lines, found


def compare_file(name, old, new):
    """The differences of one file of the two sides. Prints the dictionary and the counts."""
    old_lines, old_counts, old_dictionary, old_found = reduced(name, old)
    new_lines, new_counts, new_dictionary, new_found = reduced(name, new)
    old_lines, new_lines, found = with_line_pairs(name, old_lines, new_lines)
    found += old_found + new_found
    found += difflib.unified_diff(old_lines, new_lines, "old/" + name, "new/" + name, lineterm="")
    for side, counts in (("old", old_counts), ("new", new_counts)):
        if counts != FILES[name][1]:
            found.append(f"The {side} {name} has {shown(counts)}. The table FILES has {shown(FILES[name][1])}.")
    if old_dictionary or new_dictionary:
        print(f"The dictionary of {name}, with the body of each entry on the old side and on the new side.")
    for entries in zip(old_dictionary, new_dictionary):
        print("  " + " ".join(entries[0][0].split()))
        for side, (_, body) in zip(("old", "new"), entries):
            print("\n".join(f"    {side}  {line.strip()}" for line in body.split("\n")))
    print("\n".join(found + [f"{name} has {shown(new_counts)} and {len(found)} difference lines."]))
    return found


def shown(counts):
    """The count of each keyword as text, in the order of the keywords."""
    return ", ".join(f"{counts[keyword]} `{keyword}`" for keyword in sorted(counts))


def declarations(text):
    """Each `def`, `abbrev` and `theorem` by its name below the first namespace, with its keyword,
    its doc comment, its text after the keyword, its first line, its last line and its `-- Lines`
    comment."""
    lines, inside = text.split("\n"), scan(text)[1]
    found, namespaces, doc, cited, index = {}, [], [], None, 0
    while index < len(lines):
        line = lines[index]
        opened, closed = re.match(r"namespace (\S+)", line), re.match(r"end (\S+)", line)
        keyword = re.match(r"(def|abbrev|theorem) (\S+)", line)
        if index in inside:
            pass
        elif line.startswith("/--"):
            end = index
            while "-/" not in lines[end]:
                end += 1
            doc, index = lines[index:end + 1], end + 1
            continue
        elif opened:
            namespaces.append(opened.group(1))
        elif closed and namespaces and namespaces[-1] == closed.group(1):
            namespaces.pop()
        elif line.startswith("-- Line"):
            cited = [int(number) for number in re.findall(r"\d+", line)]
        elif keyword:
            end = declaration_end(lines, index, inside)
            while lines[end - 1] == "":
                end -= 1
            name = ".".join(namespaces[1:] + [keyword.group(2)])
            after = "\n".join(lines[index:end])[len(keyword.group(1)):]
            found[name] = (keyword.group(1), "\n".join(doc), after, index + 1, end, cited)
            index = end - 1
        doc, index = [], index + 1
    return found


def binders(signature):
    """The parts of a signature, which is the words of a statement after its name. The parts are
    the type of each explicit binder `(x y : T)` with one type for each name, the names of these
    binders, each other binder, and the words after the last binder."""
    types, names, others, index = [], [], [], 0
    while index < len(signature) and signature[index] in OPEN:
        depth, close = 0, index
        while close < len(signature):
            depth += (signature[close] in OPEN) - (signature[close] in CLOSE)
            if depth == 0:
                break
            close += 1
        group = signature[index:close + 1]
        if group[0] == "(" and ":" in group:
            colon = group.index(":")
            names += group[1:colon]
            types += [group[colon + 1:-1]] * (colon - 1)
        else:
            others.append(group)
        index = close + 1
    return types, names, others, signature[index:]


def parameters(copy):
    """The type of each explicit parameter of a copy, and each other binder of the copy. The
    parameters are the explicit binders and then the types before each `→` of the type of the
    copy. `copy` is the words of the statement of the copy."""
    types, _, others, rest = binders(copy[2:])
    arrows, depth = [[]], 0
    for token in rest[1:]:
        depth += (token in OPEN) - (token in CLOSE)
        if token == "→" and depth == 0:
            arrows.append([])
        else:
            arrows[-1].append(token)
    return types + arrows[:-1], others


def has_equation_form(equation, copy, theorem, name, upstream):
    """True if the equation `theorem` has the form `name x = upstream x` of UPSTREAM. The copy can
    have the argument `(m := m)`, and the two sides can start with `@`. `equation` and `copy` are
    the words of the two statements."""
    types, names, others, claim = binders(equation[2:])
    copy_types, copy_others = parameters(copy)
    forms = [[*at, name, *monad, *names, "=", *at, upstream, *names]
             for at in ([], ["@"]) for monad in ([], ["(", "m", ":=", "m", ")"])]
    return (equation[:2] == ["theorem", theorem] and types == copy_types[:len(types)]
            and all(other in copy_others for other in others)
            and claim[:1] == [":"] and claim[1:] in forms)


def compare_equations(old, new):
    """The differences between the equations of `LeanXmss.lean` and the tables UPSTREAM and
    COMPOSED. Prints the rows of COMPOSED."""
    found = []
    print("The equations of the new LeanXmss.lean that relate a copy to a composition of upstream "
          "definitions. Read each statement and its reason.")
    for name, (composed, reason) in COMPOSED.items():
        print(f"  {name}\n    {composed}\n    {reason}")
    for column, (side, text) in enumerate((("old", old), ("new", new))):
        entries = declarations(text)
        theorems = {name for name, entry in entries.items() if entry[0] == "theorem"}
        copies = [name for name in entries if name not in theorems]
        for name in sorted(set(copies) ^ set(UPSTREAM)):
            found.append(f"The {side} LeanXmss.lean and the table UPSTREAM do not agree on the copy `{name}`.")
        for name in copies:
            space, _, last = name.rpartition(".")
            theorem = last[0].lower() + last[1:] + EQUATION_SUFFIXES[column]
            qualified = space + "." + theorem if space else theorem
            if qualified not in theorems:
                found.append(f"The {side} LeanXmss.lean has no equation `{qualified}` for the copy `{name}`.")
                continue
            theorems.remove(qualified)
            equation = statement("theorem" + entries[qualified][2])
            copy = statement(entries[name][0] + entries[name][2])
            upstream = UPSTREAM.get(name, (None, None))[column]
            if None in (equation, copy):
                found.append(f"The script cannot find the end of the {side} statement of `{name}` or of `{qualified}`.")
            elif upstream is None:
                if " ".join(equation.split()) != COMPOSED.get(name, (None, None))[0]:
                    found.append(f"The {side} equation of the copy `{name}` is not its statement in COMPOSED. "
                                 f"The equation is `{' '.join(equation.split())}`.")
            elif not has_equation_form(words(equation), words(copy), theorem, last, upstream):
                found.append(f"The {side} equation of the copy `{name}` does not have the form of UPSTREAM "
                             f"with `{upstream}`. The equation is `{' '.join(equation.split())}`.")
        for name in sorted(theorems):
            found.append(f"The theorem `{name}` of the {side} LeanXmss.lean is not the equation of a copy.")
    print("\n".join(found + ["The equations of LeanXmss.lean and the tables UPSTREAM and COMPOSED "
                             f"have {len(found)} difference lines."]))
    return found


def compare_pinned(old, pinned):
    """The differences between the copies of the old `LeanXmss.lean` and the pinned source."""
    copies = {name: entry for name, entry in declarations(old).items() if entry[0] != "theorem"}
    pinned_lines = pinned.split("\n")
    source = declarations(pinned)
    found, spans = [], []
    for name, (keyword, doc, text, _, _, cited) in copies.items():
        if name not in source:
            found.append(f"The pinned source has no declaration `{name}`.")
            continue
        pinned_keyword, pinned_doc, pinned_text, first, last, _ = source[name]
        if (pinned_keyword, keyword) != NAMED_KEYWORDS.get(name, (keyword, keyword)):
            found.append(f"`{name}` has the pinned keyword `{pinned_keyword}` and the copied keyword `{keyword}`.")
        found += difflib.unified_diff((pinned_doc + pinned_text).split("\n"), (doc + text).split("\n"),
                                      f"pinned {name}", f"copied {name}", lineterm="")
        if not min(cited) <= first <= last <= max(cited):
            found.append(f"`{name}` has the pinned lines {first} to {last} and the cited lines {cited}.")
        spans += [first, last]
    omitted = [line for line in pinned_lines if re.match(r"(instance|attribute)\b", line)]
    if omitted != NAMED_OMISSIONS:
        found.append(f"The pinned source has the instances and the attributes {omitted}.")
    variables = [line for line in old.split("\n") if line.startswith("variable")]
    pinned_variables = [line for line in pinned_lines[min(spans) - 1:max(spans)] if line.startswith("variable")]
    if variables != pinned_variables:
        found.append(f"The pinned source has the variables {pinned_variables}. The copies have {variables}.")
    print("\n".join(found + [f"The {len(copies)} copies of LeanXmss.lean and the pinned source "
                             f"have {len(found)} difference lines."]))
    return found


def compare(old, new, pinned):
    """Each difference line. `old` and `new` give the text of each file by its name, and `pinned`
    is the text of the pinned source."""
    found = []
    for name in FILES:
        found += compare_file(name, old[name], new[name])
    found += compare_equations(old["LeanXmss.lean"], new["LeanXmss.lean"])
    found += compare_pinned(old["LeanXmss.lean"], pinned)
    print(f"The two sides have {len(found)} difference lines.")
    return found


def sides():
    """The text of each file of the old side and of the new side, and the pinned source."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--old", required=True, help="the folder Bridge of the old side")
    parser.add_argument("--new", required=True, help="the folder Bridge of the new side")
    arguments = parser.parse_args()
    return ({name: read(os.path.join(arguments.old, name)) for name in FILES},
            {name: read(os.path.join(arguments.new, name)) for name in FILES},
            read(os.path.join(arguments.old, PINNED)))


if __name__ == "__main__":
    sys.exit(1 if compare(*sides()) else 0)
