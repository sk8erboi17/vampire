"""Presents the integrated Vampire with the command line and the output of
the standalone Quaerens program, so that the differential fuzz scripts of
the Quaerens repository (tools/fuzz/) can judge it.

usage: VAMPIRE=/path/to/vampire [VAMPIRE_ARGS="-t 3"] python3 -I as_quaerens.py FILE.tex

Those scripts generate statements, ask the program, and compare its answers
with an oracle of their own, which shares no reasoning with Quaerens and
none with Vampire. They expect one line per statement, "   N. VERDICT", in
the words of Quaerens. This script runs Vampire on the file and writes those
lines:

  - a statement decided by the mathematical engine keeps the engine's own line;
  - a theorem found by Vampire is "DIMOSTRATO", with "certificato verificato"
    if the independent checker accepted a certificate for it (an example, or
    Vampire's inferences rechecked one by one) and without certificate otherwise;
  - a counterexample found by Vampire and accepted by the independent checker
    is "FALSO: controesempio ...", with the model, which the oracle reads back
    and recomputes with its own evaluator;
  - "not a theorem" reported by Vampire without a model is "NON DIMOSTRATO":
    there is nothing the oracle could recompute, and a refutation that cannot
    be checked is not presented to it as one. The same for a request for an
    example that Vampire refutes, certified or not: Quaerens has no verdict
    that says "there is no example", and the scripts read none.

It is a tool for testing, like the fuzz scripts themselves: only the Python 3
standard library, nothing of it is part of the program or of its checks.
"""
import os
import re
import subprocess
import sys


def main():
    vampire = os.environ["VAMPIRE"]
    arguments = os.environ.get("VAMPIRE_ARGS", "-t 3").split()
    all_positive = True
    counts = {"proved": 0, "certified": 0, "refuted": 0, "not_proved": 0, "unsupported": 0, "solved": 0}
    for path in sys.argv[1:]:
        print(path)
        run = subprocess.run([vampire, "--proof", "off", *arguments, path], capture_output=True, text=True)

        # One block of output per statement, from its "% Statement N" line to its "% Result N" line.
        blocks = re.split(r"^% Statement \d+ of [^\n]*\n", run.stdout, flags=re.M)[1:]
        for number, block in enumerate(blocks, 1):
            result = re.search(r"^% Result \d+: (\w+) \((\w+)\)$", block, re.M)
            engine = re.search(r"^% Engine verdict: (.*)$", block, re.M)
            model = re.search(r"^% (?:Counterexample|Example) \(LaTeX\): (.*)$", block, re.M)
            if not result:
                line = "NON DIMOSTRATO: il programma non ha risposto"
            elif result.group(2) == "engine" and engine:
                line = engine.group(1)
            elif result.group(1) == "TheoremUnverified":
                line = "DIMOSTRATO da Vampire, per refutazione; senza certificato (la prova di Vampire non è ricontrollata dal verificatore indipendente)"
            elif result.group(1) == "TheoremCertified":
                line = "DIMOSTRATO da Vampire; certificato verificato"
            elif result.group(1) == "CounterexampleVerified" and model:
                line = "FALSO: controesempio %s; certificato verificato" % model.group(1)
            elif result.group(1) == "Unsupported":
                line = "NON SUPPORTATO: fuori dal frammento letto"
            elif result.group(1) == "CounterexampleUnverified":
                line = "NON DIMOSTRATO: Vampire riporta che non è un teorema, senza un modello finito da ricontrollare"
            elif result.group(1) == "RefutationCertified":
                line = "NON DIMOSTRATO: Vampire ha refutato la richiesta di un esempio, e il verificatore ha seguito la refutazione"
            else:
                line = "NON DIMOSTRATO: Vampire non ha deciso l'enunciato entro i limiti dati"
            print("%4d. %s" % (number, line))
            if line.startswith("DIMOSTRATO"):
                counts["proved"] += 1
                counts["certified"] += "certificato verificato" in line
            elif line.startswith("FALSO"):
                counts["refuted"] += 1
            elif line.startswith("RISOLTO"):
                counts["solved"] += 1
            elif line.startswith("NON DIMOSTRATO"):
                counts["not_proved"] += 1
            else:
                counts["unsupported"] += 1
            all_positive = all_positive and (line.startswith("DIMOSTRATO") or line.startswith("RISOLTO"))
        total = len(blocks)
        print("Riepilogo: %d enunciati, %d dimostrati (%d con certificato verificato), %d falsi, %d non dimostrati, %d non supportati%s."
              % (total, counts["proved"], counts["certified"], counts["refuted"], counts["not_proved"], counts["unsupported"],
                 ", %d risolti" % counts["solved"] if counts["solved"] else ""))
        sys.stderr.write(run.stderr)
    return 0 if all_positive else 1


sys.exit(main())
