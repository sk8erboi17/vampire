"""Differential fuzz of the statements that conclude that two sets are
equipotent from what is known of the maps between them.

usage: VAMPIRE=/path/to/vampire [VAMPIRE_ARGS="-t 3"] python3 -I fuzz_bijections.py SEED COUNT WORK_DIRECTORY

Generates COUNT statements about three sets S, T, U and maps f: S -> T,
g: T -> S, h: T -> U. The hypotheses are drawn from: a map is injective, a
map is surjective, one map undoes another on one side, two sets are
equipotent. The conclusion says that two of the sets are equipotent, or
that they are not.

Such a conclusion is proved, inside this program, by a bijection that is
offered and then checked (rule 11m-f of Math/quaerens/checker.c: the line
"biject" of a certificate). The engine offers the pairs of maps that can be
written with the symbols at hand; Vampire refutes; the checker follows. A
rule that let a pair of maps prove an equipotence without their being
inverse to each other would prove "f is injective, so S and T are
equipotent": this script is its adversary.

THE ORACLE looks for a counterexample among the finite interpretations: S,
T and U with at most three elements each and every table of values for the
three maps. There, two sets are equipotent exactly when they have as many
elements. A statement with a counterexample there is false; one without may
be true, or false only on larger or infinite sets, so the oracle speaks only
of the first kind. It shares nothing with the engine, the checker or
Vampire.

What is compared: for each statement the line "% Result N: Code (who)" of
the program. A code that says the statement holds on a statement with a
finite counterexample is printed as BUG, with who decided: that is a false
proof, and nothing is worse. A code that says it fails on a statement that
the oracle knows true (its hypotheses give a bijection outright) is a BUG
too. The rest is counted.

The files written go to WORK_DIRECTORY. Only the Python 3 standard library;
nothing of this script is part of the program or of its checks.
"""
import itertools
import os
import random
import re
import subprocess
import sys

LARGEST = 3
SETS = "STU"
# The maps: name, the set it starts from, the set it arrives in.
MAPS = {"f": ("S", "T"), "g": ("T", "S"), "h": ("T", "U")}


def injective(name):
    start, _ = MAPS[name]
    latex = "\\forall a, b \\in %s\\ (%s(a) = %s(b) \\implies a = b)" % (start, name, name)
    return latex, lambda m: len(set(m[name])) == len(m[name])


def surjective(name):
    start, end = MAPS[name]
    latex = "\\forall y \\in %s\\ \\exists x \\in %s\\ (%s(x) = y)" % (end, start, name)
    return latex, lambda m: set(m[name]) == set(range(m[end]))


def undoes(outer, inner):
    """outer(inner(x)) = x for every x of the set inner starts from."""
    start, _ = MAPS[inner]
    latex = "\\forall x \\in %s\\ (%s(%s(x)) = x)" % (start, outer, inner)
    return latex, lambda m: all(m[outer][m[inner][x]] == x for x in range(m[start]))


def equipotent(first, second):
    return "%s \\sim %s" % (first, second), lambda m: m[first] == m[second]


HYPOTHESES = [lambda: injective("f"), lambda: surjective("f"), lambda: injective("g"), lambda: surjective("g"),
              lambda: injective("h"), lambda: surjective("h"), lambda: undoes("g", "f"), lambda: undoes("f", "g"),
              lambda: equipotent("S", "T"), lambda: equipotent("T", "U"), lambda: equipotent("U", "S")]

# The hypotheses that give a bijection outright, with the two sets it joins: what the oracle knows true.
KNOWN = [({"\\forall x \\in S\\ (g(f(x)) = x)", "\\forall x \\in T\\ (f(g(x)) = x)"}, ("S", "T")),
         ({injective("f")[0], surjective("f")[0]}, ("S", "T")),
         ({injective("g")[0], surjective("g")[0]}, ("S", "T")),
         ({injective("h")[0], surjective("h")[0]}, ("T", "U")),
         ({"S \\sim T"}, ("S", "T")), ({"T \\sim U"}, ("T", "U")), ({"U \\sim S"}, ("S", "U"))]


def statement(rng):
    chosen = [make() for make in rng.sample(HYPOTHESES, rng.randrange(1, 5))]
    first, second = rng.sample(SETS, 2)
    denied = rng.randrange(6) == 0
    claim_latex, claim = equipotent(first, second)
    declared = " \\land ".join("%s \\colon %s \\to %s" % (name, start, end) for name, (start, end) in MAPS.items())
    latex = "(%s \\land %s) \\implies (%s)" % (declared, " \\land ".join("(%s)" % text for text, _ in chosen),
                                               "\\lnot (%s)" % claim_latex if denied else claim_latex)
    holds = lambda m: not all(h(m) for _, h in chosen) or (claim(m) != denied)

    # What the hypotheses join outright, closed under "equipotent to the same set".
    texts = {text for text, _ in chosen}
    joined = {s: {s} for s in SETS}
    for needed, (a, b) in KNOWN:
        if needed <= texts:
            merged = joined[a] | joined[b]
            for s in merged:
                joined[s] = merged
    known_true = not denied and second in joined[first]
    return latex, holds, known_true


def interpretations():
    """Every interpretation with at most LARGEST elements in each set: the sizes and the tables of the maps."""
    for sizes in itertools.product(range(LARGEST + 1), repeat=3):
        m = dict(zip(SETS, sizes))
        tables = []
        for name, (start, end) in MAPS.items():
            if m[start] and not m[end]:
                tables = None       # no map from a set with elements to the empty set
                break
            tables.append([list(t) for t in itertools.product(range(m[end]), repeat=m[start])])
        if tables is None:
            continue
        for choice in itertools.product(*tables):
            yield dict(m, **dict(zip(MAPS, choice)))


def main():
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    seed, count, work = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    vampire = os.environ["VAMPIRE"]
    arguments = os.environ.get("VAMPIRE_ARGS", "-t 3").split()
    rng = random.Random(seed)
    statements = [statement(rng) for _ in range(count)]
    models = list(interpretations())
    refuted = [not all(holds(m) for m in models) for _, holds, _ in statements]

    os.makedirs(work, exist_ok=True)
    path = os.path.join(work, "fuzz_bijections_%d.tex" % seed)
    with open(path, "w", encoding="utf-8") as out:
        out.write("\\documentclass{article}\n\\usepackage{amsmath}\n\\usepackage{amssymb}\n\\begin{document}\n\\begin{enumerate}\n")
        for latex, _, _ in statements:
            out.write("\\item $\\displaystyle %s$\n" % latex)
        out.write("\\end{enumerate}\n\\end{document}\n")
    run = subprocess.run([vampire, "--proof", "off", *arguments, path], capture_output=True, text=True)
    with open(os.path.join(work, "fuzz_bijections_%d.out" % seed), "w", encoding="utf-8") as out:
        out.write(run.stdout + run.stderr)

    results = dict((int(number), (code, who)) for number, code, who in re.findall(r"^% Result (\d+): (\w+) \((\w+)\)$", run.stdout, re.M))
    counts = {}
    bugs = 0
    for number, ((latex, _, known_true), false) in enumerate(zip(statements, refuted), 1):
        code, who = results.get(number, ("NoAnswer", "nobody"))
        says = True if code.startswith("Theorem") else False if code.startswith(("Counterexample", "Refutation")) else None
        if (says is True and false) or (says is False and known_true):
            bugs += 1
            print("BUG %d [%s by %s, the oracle says %s]: %s" % (number, code, who, "false" if false else "true", latex))
        kind = "false" if false else "true" if known_true else "no small counterexample"
        key = "%s/%s by %s" % (kind, {True: "proved", False: "refuted", None: "undecided"}[says], who)
        counts[key] = counts.get(key, 0) + 1
    print("seed %d: %d statements, %d BUG; %s" % (seed, count, bugs, ", ".join("%s=%d" % item for item in sorted(counts.items()))))
    return 1 if bugs else 0


if __name__ == "__main__":
    sys.exit(main())
