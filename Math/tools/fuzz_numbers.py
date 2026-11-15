"""Differential fuzz of the statements with quantifiers over integers that
reach Vampire's arithmetic theories.

usage: VAMPIRE=/path/to/vampire [VAMPIRE_ARGS="-t 3"] python3 -I fuzz_numbers.py SEED COUNT WORK_DIRECTORY

Generates COUNT statements about integers in the fragment that the
mathematical engine hands over when it cannot decide (Math/Engine.h,
qr_numbers_item()): quantifiers over N, N_0, Z and Z without 0, polynomial
expressions, comparisons, divisibility, connectives. Every quantified
variable is confined to a few values by a condition written in the
statement itself ("-3 <= x and x <= 3 implies ..."), so the truth of the
statement is a finite count.

THE ORACLE is that count, done here in Python by trying every value: it
shares nothing with the engine, with the translation into TPTP or with
Vampire. It knows the sets (N starts from 1), the integers of Python, and
that "d divides e" means "e is d times an integer", so that zero divides
only zero.

What is compared: for each statement the line "% Result N: Code (who)" of
the program. A code that says the statement holds (Theorem...) on a
statement the oracle finds false, or one that says it fails
(Counterexample..., Refutation...) on a statement the oracle finds true, is
printed as BUG, with who decided: that is a false proof or a false
refutation, and nothing is worse. Undecided statements are counted.

The files written (the statements, the output of the program) go to
WORK_DIRECTORY. Only the Python 3 standard library; nothing of this script
is part of the program or of its checks.
"""
import os
import random
import re
import subprocess
import sys

SETS = [
    ("\\mathbb{N}", lambda v: v >= 1),
    ("\\mathbb{N}_{0}", lambda v: v >= 0),
    ("\\mathbb{Z}", lambda v: True),
    ("\\mathbb{Z} \\setminus \\{0\\}", lambda v: v != 0),
]


class Term:
    """A polynomial expression: its LaTeX and its value for an assignment of the variables."""

    def __init__(self, latex, value):
        self.latex, self.value = latex, value


def term(rng, names, depth=0):
    kind = rng.randrange(6 if depth < 2 else 2)
    if kind == 0:
        number = rng.randrange(0, 5)
        return Term(str(number), lambda env: number)
    if kind == 1:
        name = rng.choice(names)
        return Term(name, lambda env: env[name])
    if kind == 2:
        left, right = term(rng, names, depth + 1), term(rng, names, depth + 1)
        return Term("%s + %s" % (left.latex, right.latex), lambda env: left.value(env) + right.value(env))
    if kind == 3:
        left, right = term(rng, names, depth + 1), term(rng, names, depth + 1)
        return Term("%s - (%s)" % (left.latex, right.latex), lambda env: left.value(env) - right.value(env))
    if kind == 4:
        left, right = term(rng, names, depth + 1), term(rng, names, depth + 1)
        return Term("(%s)(%s)" % (left.latex, right.latex), lambda env: left.value(env) * right.value(env))
    name, power = rng.choice(names), rng.randrange(2, 4)
    return Term("%s^{%d}" % (name, power), lambda env: env[name] ** power)


class Condition:
    """A condition: its LaTeX and its truth for an assignment of the variables."""

    def __init__(self, latex, holds):
        self.latex, self.holds = latex, holds


def divides(divisor, divided):
    return divided == 0 if divisor == 0 else divided % divisor == 0


def atom(rng, names):
    left, right = term(rng, names), term(rng, names)
    kind = rng.randrange(8)
    if kind == 6:
        return Condition("(%s) \\mid (%s)" % (left.latex, right.latex), lambda env: divides(left.value(env), right.value(env)))
    if kind == 7:
        return Condition("(%s) \\nmid (%s)" % (left.latex, right.latex), lambda env: not divides(left.value(env), right.value(env)))
    symbol, compare = [("=", lambda a, b: a == b), ("\\neq", lambda a, b: a != b), ("<", lambda a, b: a < b),
                       ("\\le", lambda a, b: a <= b), (">", lambda a, b: a > b), ("\\ge", lambda a, b: a >= b)][kind]
    return Condition("%s %s %s" % (left.latex, symbol, right.latex), lambda env: compare(left.value(env), right.value(env)))


def condition(rng, names, depth=0):
    kind = rng.randrange(5 if depth < 2 else 1)
    if kind == 0:
        return atom(rng, names)
    if kind == 1:
        inner = condition(rng, names, depth + 1)
        return Condition("\\lnot (%s)" % inner.latex, lambda env: not inner.holds(env))
    left, right = condition(rng, names, depth + 1), condition(rng, names, depth + 1)
    if kind == 2:
        return Condition("(%s) \\land (%s)" % (left.latex, right.latex), lambda env: left.holds(env) and right.holds(env))
    if kind == 3:
        return Condition("(%s) \\lor (%s)" % (left.latex, right.latex), lambda env: left.holds(env) or right.holds(env))
    return Condition("(%s) \\implies (%s)" % (left.latex, right.latex), lambda env: (not left.holds(env)) or right.holds(env))


def statement(rng):
    """A closed statement with one or two quantifiers, each variable confined to [-bound, bound]."""
    names = ["x", "y"][:rng.randrange(1, 3)]
    body = condition(rng, names)
    latex, holds = body.latex, body.holds
    for name in reversed(names):
        universal = rng.randrange(2) == 0
        set_latex, member = rng.choice(SETS)
        bound = rng.randrange(2, 5)
        values = [v for v in range(-bound, bound + 1) if member(v)]
        guard = "-%d \\le %s \\land %s \\le %d" % (bound, name, name, bound)
        inner_holds = holds
        if universal:
            latex = "\\forall %s \\in %s\\ ((%s) \\implies (%s))" % (name, set_latex, guard, latex)
            holds = (lambda inner, values, name: lambda env: all(inner({**env, name: v}) for v in values))(inner_holds, values, name)
        else:
            latex = "\\exists %s \\in %s\\ ((%s) \\land (%s))" % (name, set_latex, guard, latex)
            holds = (lambda inner, values, name: lambda env: any(inner({**env, name: v}) for v in values))(inner_holds, values, name)
    return latex, holds({})


def main():
    if len(sys.argv) != 4:
        sys.exit(__doc__)
    seed, count, work = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    vampire = os.environ["VAMPIRE"]
    arguments = os.environ.get("VAMPIRE_ARGS", "-t 3").split()
    rng = random.Random(seed)
    statements = [statement(rng) for _ in range(count)]

    os.makedirs(work, exist_ok=True)
    path = os.path.join(work, "fuzz_numbers_%d.tex" % seed)
    with open(path, "w", encoding="utf-8") as out:
        out.write("\\documentclass{article}\n\\usepackage{amsmath}\n\\usepackage{amssymb}\n\\begin{document}\n\\begin{enumerate}\n")
        for latex, _ in statements:
            out.write("\\item $\\displaystyle %s$\n" % latex)
        out.write("\\end{enumerate}\n\\end{document}\n")
    run = subprocess.run([vampire, "--proof", "off", *arguments, path], capture_output=True, text=True)
    with open(os.path.join(work, "fuzz_numbers_%d.out" % seed), "w", encoding="utf-8") as out:
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
