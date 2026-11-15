"""Differential fuzz of the statements that suppose two sets equipotent.

usage: VAMPIRE=/path/to/vampire [VAMPIRE_ARGS="-t 3"] python3 -I fuzz_equipotence.py SEED COUNT WORK_DIRECTORY

Generates COUNT statements of the form

    (S ~ T  and  hypotheses on how many elements S and T have)  implies  claim on how many elements they have

with "has at most k", "has at least k" and "has exactly k elements" written
as |S| <= k, |S| >= k, |S| = k. The mathematical engine goes first on such a
statement; where it has no answer Vampire is asked, with the supposed
bijection given as two maps inverse to each other (Math/LogicStatement.cpp).

THE ORACLE knows one thing: equipotent sets have the same number of
elements, finite or not. So the statement holds exactly when, for every
number of elements n (0, 1, 2, ... and "infinitely many"), the hypotheses
with |S| = |T| = n give the claim. The numbers written are small, so trying
n up to one more than the largest of them, and infinity, tries every case.
It shares nothing with the engine, the translation or Vampire.

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

INFINITE = float("inf")
LARGEST = 5


def atom(rng):
    """A condition on the number of elements of S or of T: its LaTeX and its truth for that number."""
    name = rng.choice(["S", "T"])
    bound = rng.randrange(0, LARGEST + 1)
    symbol, holds = rng.choice([("\\le", lambda n, k: n <= k), ("\\ge", lambda n, k: n >= k), ("=", lambda n, k: n == k)])
    return "|%s| %s %d" % (name, symbol, bound), (lambda n: holds(n, bound))


def statement(rng):
    hypotheses = [atom(rng) for _ in range(rng.randrange(1, 3))]
    claims = [atom(rng) for _ in range(rng.randrange(1, 3))]
    disjunction = rng.randrange(2) == 0
    latex = "(S \\sim T \\land %s) \\implies (%s)" % (
        " \\land ".join(text for text, _ in hypotheses),
        (" \\lor " if disjunction else " \\land ").join(text for text, _ in claims))
    truth = True
    for n in list(range(0, LARGEST + 2)) + [INFINITE]:
        supposed = all(holds(n) for _, holds in hypotheses)
        claimed = (any if disjunction else all)(holds(n) for _, holds in claims)
        truth = truth and (not supposed or claimed)
    return latex, truth


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
