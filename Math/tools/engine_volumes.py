"""Splits the mathematical engine into volumes by domain, and joins them back.

The engine of Quaerens is one C file, main.c, written as a book: a design
comment, an index, and numbered chapters. Inside Vampire it is kept as a
short main.c (the design comment, the index, and one #include per volume)
and one file per domain next to it: exact numbers and polynomials, sign
tables, limits, linear algebra, logic over arbitrary sets, and so on. The
volumes are still one translation unit, read in order: a chapter uses what
the chapters above it have presented, as before.

Nothing is rewritten: a volume is a run of consecutive chapters, cut at the
banner of its first chapter, and the volumes joined in order are, byte for
byte, the single file. That is what makes the two forms interchangeable:

    python3 -I engine_volumes.py split SINGLE_MAIN_C DIRECTORY
        writes DIRECTORY/main.c and DIRECTORY/engine_*.c from the single file
    python3 -I engine_volumes.py join DIRECTORY SINGLE_MAIN_C
        writes the single file from DIRECTORY/main.c and its volumes
    python3 -I engine_volumes.py check DIRECTORY
        joins, splits again, and fails unless the same files come back

To bring in a new version of main.c from the Quaerens repository: join, apply
the changes to the single file (or replace it), split.

Only the Python 3 standard library. It is a tool for maintenance: nothing of
it is part of the program or of its checks, except "check", which the checks
may run.
"""
import os
import re
import sys
import tempfile

# The volumes, in order: file name, number of its first chapter as written in
# the banner, and what it holds (in Italian, like every comment of the engine:
# it becomes a comment of main.c). A volume runs up to the next one's first
# chapter. The first volume starts at the first banner after the design
# comment and the index, which stay in main.c.
VOLUMES = [
    ("engine_foundations.c", "1", "limiti, errori e memoria, numeri esatti, monomi, polinomi, atomi, frazioni di polinomi (capitoli 1-7; include checker.c, plot.c e parser.c dove il libro ne ha bisogno)"),
    ("engine_evaluation.c", "10", "le successioni note come dati, la valutazione di un albero in una frazione, i test di annullamento (capitoli 10-12)"),
    ("engine_induction.c", "13", "induzione su somme e prodotti: caso base, passo, verdetto (capitolo 13)"),
    ("engine_sets.c", "15", "relazioni tra insiemi: decisione per regioni, verifica indipendente, dimostrazione scritta (capitoli 15-16)"),
    ("engine_intervals.c", "24", "i numeri reali come intervalli con l'errore garantito (capitolo 24)"),
    ("engine_quantifiers.c", "18", "enunciati con quantificatori sui numeri: le regole di dimostrazione (capitoli da 18 a 18.7)"),
    ("engine_sign_tables.c", "18.8", "la tabella dei segni: punti esatti, segni, righe, soluzioni, grafici, un parametro (capitoli 18.8-18.19)"),
    ("engine_explanation.c", "40", "la spiegazione: i passaggi registrati e ricontrollati (capitolo 40)"),
    ("engine_quantifiers_verdict.c", "19", "enunciati con quantificatori: verifica indipendente e verdetto (capitolo 19)"),
    ("engine_sequences.c", "25", "induzione su una disuguaglianza, successioni definite per ricorrenza (capitoli 25-26)"),
    ("engine_derivatives.c", "27", "derivate: dimostrarle, calcolarle, usarle negli studi di funzione (capitolo 27)"),
    ("engine_logic.c", "28", "insiemi qualsiasi: modelli finiti, istanze, saturazione, e i compiti svolti per Vampire (capitolo 28)"),
    ("engine_limits.c", "29", "limiti (capitolo 29)"),
    ("engine_integrals.c", "30", "integrali: primitive, integrali definiti e impropri (capitolo 30)"),
    ("engine_linear_algebra.c", "32", "algebra lineare esatta: matrici, determinanti, sistemi lineari (capitoli 32-33)"),
    ("engine_multivariable.c", "35", "funzioni di più variabili: derivate parziali, gradiente, hessiana, punti critici (capitoli 35-36)"),
    ("engine_indices.c", "38", "identità con gli indici: il conto su tutti i valori (capitolo 38)"),
    ("engine_statement.c", "20", "dimostrare un enunciato: quale capitolo lo legge; il documento (include output.c); main (capitoli 20 e 23)"),
]

BANNER = "/* ============================================================================="
MARK_START = "/* I VOLUMI DEL MOTORE (generato da Math/tools/engine_volumes.py: non modificare a mano)\n"
MARK_END = "/* Fine dei volumi. */\n"


def banners(text):
    """The offsets of the chapter banners, each with the number of its chapter."""
    found = []
    at = 0
    while True:
        at = text.find(BANNER + "\n", at)
        if at < 0:
            return found
        title = text[at + len(BANNER) + 1:text.find("\n", at + len(BANNER) + 1)]
        match = re.match(r" \* ([0-9]+(?:\.[0-9]+)?)\.? ", title)
        if match:
            found.append((at, match.group(1)))
        at += len(BANNER)


def split(single):
    """The short main.c and the volumes, as {name: text}, from the single file."""
    where = {}
    for offset, number in banners(single):
        where.setdefault(number, offset)   # a chapter number is cut where it first appears
    cuts = []
    for name, chapter, _ in VOLUMES:
        if chapter not in where:
            sys.exit("engine_volumes: no banner for chapter %s, the first of %s" % (chapter, name))
        cuts.append(where[chapter])
    if cuts != sorted(cuts):
        sys.exit("engine_volumes: the chapters of the volumes are not in the order of the file")
    if MARK_START in single:
        sys.exit("engine_volumes: this is already the short main.c, not the single file")

    files = {}
    head = single[:cuts[0]]
    includes = MARK_START + " *\n"
    includes += " * Il motore è un solo libro in più volumi, letti in quest'ordine in una sola\n"
    includes += " * unità di compilazione: un capitolo usa ciò che i capitoli sopra di lui\n"
    includes += " * hanno presentato, in questo volume o in quelli prima. I volumi uniti in\n"
    includes += " * quest'ordine sono, byte per byte, il file unico da cui sono stati tagliati\n"
    includes += " * (engine_volumes.py join lo riscrive, per confrontarlo con quello di Quaerens). */\n"
    for index, (name, chapter, holds) in enumerate(VOLUMES):
        end = cuts[index + 1] if index + 1 < len(cuts) else len(single)
        files[name] = single[cuts[index]:end]
        includes += "\n/* %s */\n#include \"%s\"\n" % (holds, name)
    includes += "\n" + MARK_END
    files["main.c"] = head + includes
    return files


def join(directory):
    """The single file, from the short main.c in the directory and its volumes."""
    short = open(os.path.join(directory, "main.c"), encoding="utf-8").read()
    start = short.find(MARK_START)
    if start < 0 or not short.endswith(MARK_END):
        sys.exit("engine_volumes: %s/main.c is not the short main.c" % directory)
    names = re.findall(r'^#include "(engine_[a-z_]+\.c)"$', short[start:], re.M)
    if names != [name for name, _, _ in VOLUMES]:
        sys.exit("engine_volumes: the volumes included by main.c are not the ones listed in this script, in this order")
    return short[:start] + "".join(open(os.path.join(directory, name), encoding="utf-8").read() for name in names)


def write(directory, files):
    for name, text in files.items():
        with open(os.path.join(directory, name), "w", encoding="utf-8", newline="") as out:
            out.write(text)


def main():
    if len(sys.argv) == 4 and sys.argv[1] == "split":
        write(sys.argv[3], split(open(sys.argv[2], encoding="utf-8", newline="").read()))
    elif len(sys.argv) == 4 and sys.argv[1] == "join":
        with open(sys.argv[3], "w", encoding="utf-8", newline="") as out:
            out.write(join(sys.argv[2]))
    elif len(sys.argv) == 3 and sys.argv[1] == "check":
        single = join(sys.argv[2])
        again = split(single)
        for name, text in again.items():
            if open(os.path.join(sys.argv[2], name), encoding="utf-8", newline="").read() != text:
                sys.exit("engine_volumes: %s is not what splitting the joined file gives" % name)
        with tempfile.TemporaryDirectory() as scratch:
            write(scratch, again)
            if join(scratch) != single:
                sys.exit("engine_volumes: joining the volumes twice does not give the same file")
        print("engine_volumes: %d volumes, %d bytes, joined and split back to the same files" % (len(VOLUMES), len(single.encode("utf-8"))))
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main()
