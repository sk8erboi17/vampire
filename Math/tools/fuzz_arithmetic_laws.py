"""Adversarial fuzz of the checker's proofs from the laws of the integers
(certificate "arithmetic", chapter 20f of Math/quaerens/checker.c).

usage: VAMPIRE=/path/to/vampire [CC=cc] python3 -I fuzz_arithmetic_laws.py SEED COUNT WORK_DIRECTORY

What a certificate "arithmetic" rests on, beyond the steps of 11m that are
tested elsewhere, is three things of chapter 20f: the translation of the
statement into clauses, the laws of the integers added to them, and the
step "compute". If one of them were wrong, the clauses of a FALSE claim
could be refutable, and a refutation that the checker follows would
certify it. In the program this never shows: Vampire's arithmetic proves
only true statements, and only those are handed to the checker. This
script hands the checker the false ones.

It generates COUNT statements about integers in the notation of the
certificates (the one the engine hands over, Math/Engine.h), with
quantifiers over Z, N_0, N and Z without 0, polynomial expressions,
comparisons, divisibility and connectives. Every quantified variable is
confined to a few values by a condition in the statement itself, so THE
ORACLE, a count in Python that shares nothing with the checker, knows
whether the statement holds. For each one:

  - the claim the oracle finds FALSE (the statement, or its negation) is
    given to the checker (proof_arithmetic_clauses(), through a small
    program this script compiles from Proof/IndependentChecker.c), with the
    facts about its numerals the program would give; its clauses are
    written as a TPTP problem and given to Vampire, with three strategies.
    A refutation is printed as BUG: those clauses are true among the
    integers, or something in 20f is wrong;
  - one false fact about the numerals is offered as a step "compute": the
    checker must refuse it. Accepting it is a BUG;
  - the TRUE claim is given to Vampire the same way, and how often it is
    refuted is counted: what the laws can prove, for a reader.

Only the Python 3 standard library and a C compiler; nothing of this script
is part of the program or of its checks.
"""
import os
import random
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))

HARNESS = r'''
#include "Proof/IndependentChecker.c"
#include <stdio.h>
int main(int argc, char** argv) {
  static char text[1 << 22];
  FILE* in = fopen(argv[1], "rb");
  if (!in) return 2;
  size_t n = fread(text, 1, sizeof text - 1, in);
  text[n] = 0;
  fclose(in);
  const char* why = "";
  char* out = proof_arithmetic_clauses(text, &why);
  if (!out) { printf("REFUSED %s\n", why); return 1; }
  fputs(out, stdout);
  free(out);
  return 0;
}
'''

# The sets of the quantifiers: the notation of the certificates, and membership for the oracle.
SETS = [("(set)", lambda v: True), ("(set ge 0)", lambda v: v >= 0), ("(set ge 1)", lambda v: v >= 1),
        ("(set except 0)", lambda v: v != 0)]
WINDOW = range(-3, 4)  # the values a confined variable may take


def number(v):
    return str(v) if v >= 0 else "(neg %d)" % -v


class Node:
    def __init__(self, text, value):
        self.text, self.value = text, value


def term(rng, letters, depth=0):
    kind = rng.randrange(7 if depth < 2 else 2)
    if kind == 0:
        v = rng.randrange(0, 5)
        return Node(str(v), lambda env: v)
    if kind == 1:
        x = rng.choice(letters)
        return Node("(var %d)" % x, lambda env: env[x])
    if kind in (2, 3, 4):
        a, b = term(rng, letters, depth + 1), term(rng, letters, depth + 1)
        op = ["add", "sub", "mul"][kind - 2]
        f = [lambda p, q: p + q, lambda p, q: p - q, lambda p, q: p * q][kind - 2]
        return Node("(%s %s %s)" % (op, a.text, b.text), lambda env: f(a.value(env), b.value(env)))
    if kind == 5:
        a = term(rng, letters, depth + 1)
        return Node("(neg %s)" % a.text, lambda env: -a.value(env))
    a, k = term(rng, letters, depth + 1), rng.randrange(2, 4)
    return Node("(pow %s %d)" % (a.text, k), lambda env: a.value(env) ** k)


def divides(d, e):
    return e == 0 if d == 0 else e % d == 0


def atom(rng, letters):
    a, b = term(rng, letters), term(rng, letters)
    kind = rng.randrange(5)
    word = ["=", "neq", "less", "lesseq", "divides"][kind]
    f = [lambda p, q: p == q, lambda p, q: p != q, lambda p, q: p < q, lambda p, q: p <= q, divides][kind]
    return Node("(%s %s %s)" % (word, a.text, b.text), lambda env: f(a.value(env), b.value(env)))


def condition(rng, letters, next_letter, depth=0):
    kind = rng.randrange(6 if depth < 3 else 1)
    if kind == 0 or not letters and kind < 3:
        return atom(rng, letters) if letters else quantified(rng, letters, next_letter, depth)
    if kind in (1, 2):
        a, b = condition(rng, letters, next_letter, depth + 1), condition(rng, letters, next_letter, depth + 1)
        word = ["and", "or", "implies", "iff"][rng.randrange(4)]
        f = {"and": lambda p, q: p and q, "or": lambda p, q: p or q,
             "implies": lambda p, q: (not p) or q, "iff": lambda p, q: p == q}[word]
        return Node("(%s %s %s)" % (word, a.text, b.text), lambda env: f(a.value(env), b.value(env)))
    if kind == 3:
        a = condition(rng, letters, next_letter, depth + 1)
        return Node("(not %s)" % a.text, lambda env: not a.value(env))
    return quantified(rng, letters, next_letter, depth)


def quantified(rng, letters, next_letter, depth):
    x = next_letter[0]
    next_letter[0] += 1
    every = rng.randrange(2) == 0
    s, member = rng.choice(SETS)
    low, high = rng.randrange(-3, 1), rng.randrange(0, 4)
    var = "(var %d)" % x
    window = "(and (lesseq %s %s) (lesseq %s %s))" % (number(low), var, var, number(high))
    body = condition(rng, letters + [x], next_letter, depth + 1)
    inner = "(%s %s %s)" % ("implies" if every else "and", window, body.text)
    text = "(%s %s %s %s)" % ("forall" if every else "exists", var, s, inner)

    def value(env):
        values = [v for v in range(low, high + 1) if member(v)]
        results = (body.value({**env, x: v}) for v in values)
        return all(results) if every else any(results)
    return Node(text, value)


def statement(rng):
    return quantified(rng, [], [97], 0)


# The facts the program gives (Math/NumberStatement.cpp, arithmeticFacts()), and a false one.
def facts(numerals):
    sym = {v: 4 + i for i, v in enumerate(numerals)}
    f = lambda v: "(f %d)" % sym[v]
    lines = []
    for i, a in enumerate(numerals):
        for b in numerals[i + 1:] if len(numerals) <= 16 else numerals[i + 1:i + 2]:
            lines += ["step compute (clause (ne %s %s))" % (f(a), f(b)),
                      "step compute (clause (pos (f 3 %s %s)))" % (f(a), f(b)),
                      "step compute (clause (neg (f 3 %s %s)))" % (f(b), f(a))]
    if len(numerals) <= 16:
        for i, a in enumerate(numerals):
            for b in numerals[i:]:
                if a > 0 and b > 0 and a + b in sym:
                    lines.append("step compute (clause (eq (f 0 %s %s) %s))" % (f(a), f(b), f(a + b)))
                if a > 1 and b > 1 and a * b in sym:
                    lines.append("step compute (clause (eq (f 2 %s %s) %s))" % (f(a), f(b), f(a * b)))
    return "".join(line + "\n" for line in lines)


def false_fact(rng, numerals):
    """A step compute whose clause is false among the integers."""
    f = lambda i: "(f %d)" % (4 + i)
    i, j = rng.randrange(len(numerals)), rng.randrange(len(numerals))
    a, b = numerals[i], numerals[j]
    kind = rng.randrange(4)
    if kind == 0:   # two numerals equal, or one different from itself
        return "step compute (clause (%s %s %s))\n" % ("eq" if a != b else "ne", f(i), f(j))
    if kind == 1:   # the order the wrong way
        return "step compute (clause (%s (f 3 %s %s)))\n" % ("neg" if a < b else "pos", f(i), f(j))
    # a sum or a product that is a numeral it is not (there are always 0 and 1)
    value = a + b if kind == 2 else a * b
    k = next(k for k, v in enumerate(numerals) if v != value)
    return "step compute (clause (eq (f %d %s %s) %s))\n" % (0 if kind == 2 else 2, f(i), f(j), f(k))


def tptp(listing):
    """The symbols and clauses of the listing as a TPTP problem, symbols declared in the checker's order."""
    lines = listing.split("\n")
    at = next(k for k, line in enumerate(lines) if line.startswith("symbols "))
    count = int(lines[at].split()[1])
    out = []
    for k in range(count):
        arity, predicate = map(int, lines[at + 1 + k].split())
        result = "$o" if predicate else "$i"
        args = " * ".join(["$i"] * arity)
        kind = result if arity == 0 else ("%s > %s" % (args, result) if arity == 1 else "(%s) > %s" % (args, result))
        out.append("tff(d%d, type, %s%d: %s)." % (k, "p" if predicate else "f", k, kind))
    at += 1 + count
    clauses = int(lines[at].split()[1])
    for k in range(clauses):
        out.append("cnf(c%d, axiom, %s)." % (k, clause(lines[at + 1 + k], [c for c in range(count)])))
    return "\n".join(out) + "\n"


def clause(text, _):
    tokens = re.findall(r"\(|\)|[^\s()]+", text)
    at = [0]

    def read():
        assert tokens[at[0]] == "("
        at[0] += 1
        head = tokens[at[0]]
        at[0] += 1
        args = []
        while tokens[at[0]] != ")":
            args.append(read() if tokens[at[0]] == "(" else tokens[at[0]])
            if not isinstance(args[-1], tuple):
                at[0] += 1
        at[0] += 1
        return (head, args)

    def written(t, predicate=False):
        head, args = t
        if head == "v":
            return "X" + args[0]
        name = ("p" if predicate else "f") + args[0]
        rest = [written(a) for a in args[1:]]
        return name + ("(" + ",".join(rest) + ")" if rest else "")

    _, literals = read()
    parts = []
    for head, args in literals:
        if head == "true":
            parts.append("$true")
        elif head == "false":
            parts.append("$false")
        elif head in ("eq", "ne"):
            parts.append("%s %s %s" % (written(args[0]), "=" if head == "eq" else "!=", written(args[1])))
        else:
            parts.append(("~" if head == "neg" else "") + written(args[0], predicate=True))
    return " | ".join(parts) if parts else "$false"


STRATEGIES = [["--selection", "1"], [], ["--saturation_algorithm", "otter"]]


def refuted(vampire, problem, seconds):
    for strategy in STRATEGIES:
        result = subprocess.run([vampire, "-t", str(seconds), "--proof", "off", "--theory_axioms", "off"] + strategy + [problem],
                                capture_output=True, text=True)
        if "Termination reason: Refutation\n" in result.stdout and "incomplete" not in result.stdout:
            return " ".join(strategy) or "default"
    return None


def main():
    if len(sys.argv) != 4 or "VAMPIRE" not in os.environ:
        sys.exit("usage: VAMPIRE=/path/to/vampire [CC=cc] python3 -I fuzz_arithmetic_laws.py SEED COUNT WORK_DIRECTORY")
    seed, count, work = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    vampire = os.environ["VAMPIRE"]
    os.makedirs(work, exist_ok=True)
    source, harness = os.path.join(work, "harness.c"), os.path.join(work, "harness")
    with open(source, "w") as out:
        out.write(HARNESS)
    subprocess.run([os.environ.get("CC", "cc"), "-std=c11", "-O2", "-I", ROOT, "-o", harness, source], check=True)

    rng = random.Random(seed)
    bugs = proved = refused = 0
    for n in range(count):
        s = statement(rng)
        truth = s.value({})
        claims = {truth: s.text, not truth: "(not %s)" % s.text}
        for holds in (False, True):
            beginning = "certificate arithmetic\nkind int\nstatement %s\nclausify forward\n" % claims[holds]
            path = os.path.join(work, "s%d-%d.txt" % (n, holds))
            with open(path, "w") as out:
                out.write(beginning + "end\n")
            listing = subprocess.run([harness, path], capture_output=True, text=True).stdout
            if listing.startswith("REFUSED"):
                print("REFUSED %d: %s" % (n, listing.strip()))
                refused += 1
                continue
            numerals = [int(v) for v in listing.split("\n")[0].split()[1:]]

            if not holds:
                # A false fact about the numerals must be refused.
                with open(path, "w") as out:
                    out.write(beginning + false_fact(rng, numerals) + "end\n")
                wrong = subprocess.run([harness, path], capture_output=True, text=True).stdout
                if not wrong.startswith("REFUSED"):
                    print("BUG %d: a false fact was accepted\n  %s" % (n, open(path).read().replace("\n", "\n  ")))
                    bugs += 1

            with open(path, "w") as out:
                out.write(beginning + facts(numerals) + "end\n")
            listing = subprocess.run([harness, path], capture_output=True, text=True).stdout
            if listing.startswith("REFUSED"):
                print("BUG %d: the facts of the program were refused: %s" % (n, listing.strip()))
                bugs += 1
                continue
            problem = os.path.join(work, "s%d-%d.p" % (n, holds))
            with open(problem, "w") as out:
                out.write(tptp(listing))
            how = refuted(vampire, problem, 2 if not holds else 1)
            if how and not holds:
                print("BUG %d: the clauses of a false claim were refuted (%s)\n  claim: %s" % (n, how, claims[holds]))
                bugs += 1
            if how and holds:
                proved += 1
        print("%d. %s" % (n, "true" if truth else "false"), flush=True)
    print("seed %d: %d statements, %d BUG, %d true claims refuted from the laws, %d refused" % (seed, count, bugs, proved, refused))


if __name__ == "__main__":
    main()
