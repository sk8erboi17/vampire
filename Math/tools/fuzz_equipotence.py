"""Differential fuzz of the statements that speak of two sets being equipotent.

usage: VAMPIRE=/path/to/vampire [VAMPIRE_ARGS="-t 3"] python3 -I fuzz_equipotence.py SEED COUNT WORK_DIRECTORY

Generates COUNT statements about two sets S and T, made of "S and T are
equipotent" and of conditions on how many elements they have ("at most k",
"at least k", "exactly k", written |S| <= k, |S| >= k, |S| = k), with the
equipotence in every place a statement can have it:

    (S ~ T and H) implies C          a hypothesis to use
    (not (S ~ T) and H) implies C    a hypothesis denied
    H implies (S ~ T or C)           something to prove
    H implies (not (S ~ T) or C)
    H implies (S ~ T iff C)

The mathematical engine goes first on such a statement. Where it has no
answer Vampire is asked: with the supposed bijection as two maps inverse to
each other when the equipotence is a hypothesis (Math/LogicStatement.cpp),
and on the clauses of the independent checker, where an equipotence can be
used and not proved (11m-e in Math/quaerens/checker.c). A proof accepted by
the checker for a statement that is false would show that rule wrong: this
script is its adversary.

THE ORACLE knows one thing: two sets are equipotent exactly when they have
the same number of elements, finite or not. So the statement holds exactly
when it holds for every pair of numbers of elements (m of S, n of T), with
"S ~ T" read as m = n. The numbers written are small, so it is enough to
try m and n up to one more than the largest of them and two different
infinite numbers (two infinite sets need not be equipotent). It shares
nothing with the engine, the translation, the checker or Vampire.

What is compared: for each statement the line "% Result N: Code (who)" of
the program. A code that says the statement holds on a statement the oracle
finds false, or one that says it fails on a statement the oracle finds true,
is printed as BUG, with who decided. Undecided statements are counted.

The files written go to WORK_DIRECTORY. Only the Python 3 standard library;
nothing of this script is part of the program or of its checks.
"""
import os
import random
import re
import subprocess
import sys

LARGEST = 5
INFINITE = [LARGEST + 100, LARGEST + 200]   # two infinite numbers of elements: larger than every number written, and different
NUMBERS = list(range(0, LARGEST + 2)) + INFINITE


def atom(rng):
    """A condition on the number of elements of S or of T: its LaTeX and its truth for the two numbers (of S, of T)."""
    of_s = rng.randrange(2) == 0
    bound = rng.randrange(0, LARGEST + 1)
    symbol, holds = rng.choice([("\\le", lambda n, k: n <= k), ("\\ge", lambda n, k: n >= k), ("=", lambda n, k: n == k)])
    return "|%s| %s %d" % ("S" if of_s else "T", symbol, bound), (lambda m, n: holds(m if of_s else n, bound))


def statement(rng):
    hypotheses = [atom(rng) for _ in range(rng.randrange(1, 3))]
    claims = [atom(rng) for _ in range(rng.randrange(1, 3))]
    disjunction = rng.randrange(2) == 0
    supposed_text = " \\land ".join(text for text, _ in hypotheses)
    claimed_text = (" \\lor " if disjunction else " \\land ").join(text for text, _ in claims)
    supposed = lambda m, n: all(holds(m, n) for _, holds in hypotheses)
    claimed = lambda m, n: (any if disjunction else all)(holds(m, n) for _, holds in claims)

    # Where the equipotence stands. The first shape twice as often: it is the one Vampire can do most with.
    shape = rng.choice(["hypothesis", "hypothesis", "denied", "to prove", "to refute", "iff"])
    if shape == "hypothesis":
        latex = "(S \\sim T \\land %s) \\implies (%s)" % (supposed_text, claimed_text)
        holds = lambda m, n: not (m == n and supposed(m, n)) or claimed(m, n)
    elif shape == "denied":
        latex = "(\\lnot (S \\sim T) \\land %s) \\implies (%s)" % (supposed_text, claimed_text)
        holds = lambda m, n: not (m != n and supposed(m, n)) or claimed(m, n)
    elif shape == "to prove":
        latex = "(%s) \\implies (S \\sim T \\lor %s)" % (supposed_text, claimed_text)
        holds = lambda m, n: not supposed(m, n) or m == n or claimed(m, n)
    elif shape == "to refute":
        latex = "(%s) \\implies (\\lnot (S \\sim T) \\lor %s)" % (supposed_text, claimed_text)
        holds = lambda m, n: not supposed(m, n) or m != n or claimed(m, n)
    else:
        latex = "(%s) \\implies (S \\sim T \\iff (%s))" % (supposed_text, claimed_text)
        holds = lambda m, n: not supposed(m, n) or ((m == n) == claimed(m, n))
    return latex, all(holds(m, n) for m in NUMBERS for n in NUMBERS)


def main():
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    seed, count, work = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    vampire = os.environ["VAMPIRE"]
    arguments = os.environ.get("VAMPIRE_ARGS", "-t 3").split()
    rng = random.Random(seed)
    statements = [statement(rng) for _ in range(count)]

    os.makedirs(work, exist_ok=True)
    path = os.path.join(work, "fuzz_equipotence_%d.tex" % seed)
    with open(path, "w", encoding="utf-8") as out:
        out.write("\\documentclass{article}\n\\usepackage{amsmath}\n\\usepackage{amssymb}\n\\begin{document}\n\\begin{enumerate}\n")
        for latex, _ in statements:
            out.write("\\item $\\displaystyle %s$\n" % latex)
        out.write("\\end{enumerate}\n\\end{document}\n")
    run = subprocess.run([vampire, "--proof", "off", *arguments, path], capture_output=True, text=True)
    with open(os.path.join(work, "fuzz_equipotence_%d.out" % seed), "w", encoding="utf-8") as out:
        out.write(run.stdout + run.stderr)

    results = dict((int(number), (code, who)) for number, code, who in re.findall(r"^% Result (\d+): (\w+) \((\w+)\)$", run.stdout, re.M))
    counts = {}
    bugs = 0
    for number, (latex, truth) in enumerate(statements, 1):
        code, who = results.get(number, ("NoAnswer", "nobody"))
        says = True if code.startswith("Theorem") else False if code.startswith(("Counterexample", "Refutation")) else None
        if says is not None and says != truth:
            bugs += 1
            print("BUG %d [%s by %s, the oracle says %s]: %s" % (number, code, who, "true" if truth else "false", latex))
        key = "%s/%s by %s" % ("true" if truth else "false", "decided" if says is not None else "undecided", who)
        counts[key] = counts.get(key, 0) + 1
    print("seed %d: %d statements, %d BUG; %s" % (seed, count, bugs, ", ".join("%s=%d" % item for item in sorted(counts.items()))))
    return 1 if bugs else 0


if __name__ == "__main__":
    sys.exit(main())
