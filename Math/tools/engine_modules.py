"""Turns the mathematical engine from a book in one translation unit into
modules compiled apart, each with its interface, and checks that they stay so.

The engine of Quaerens is written as a book: chapters in the order a reader
needs them, nearly everything static, the whole read by the compiler as one
translation unit. Inside Vampire it is a set of modules: one .c per domain
(exact numbers and polynomials, the reader of LaTeX, sign tables, limits,
linear algebra, logic over arbitrary sets, ...) and next to it a header with
what the other modules use of it. What a module uses only for itself stays
static in its .c.

    python3 -I engine_modules.py split BOOK_DIRECTORY HOST_FILE OUT_DIRECTORY
        writes the modules from the book form: main.c, parser.c and output.c
        as the Quaerens repository has them. HOST_FILE is Math/Engine.c:
        what it uses of the engine is exported too.
    python3 -I engine_modules.py check DIRECTORY HOST_FILE
        fails unless the modules in DIRECTORY keep the discipline below.

"split" is how the modules were made, and how they would be made again from a
later book. From then on the modules are the source: a change is made in
them, and "check" is what keeps them modules.

HOW THE INTERFACES ARE FOUND. Nobody chose by hand what a module exports: it
is computed from use. The tool reads every declaration at file scope (a
macro, a type, a function, a variable) and every identifier each of them
mentions. Then:

  1. what is mentioned by a declaration of another module, or by the host
     file, is exported;
  2. what the exported form of something mentions is exported with it: the
     types in the signature of an exported function, everything in the body
     of an exported macro or of an exported inline function, the bounds of
     an exported array;
  3. a paragraph of limits or types (lines with no blank line between them)
     is exported whole if one of its lines is: they are read together. So is
     a declaration of several variables, "int a, b;", if one of them is.

A name is "mentioned" where it can mean the thing declared at file scope: not
where it is a parameter, a local variable or a member with the same name
(see mentions()). That is what keeps an interface to what is really used.

An exported macro, type or inline function moves to the header with its
comment. An exported function or variable keeps its definition, and its
comment, in the .c, where the book explains it, and loses "static"; the
header declares it. Everything else is left where it was, byte for byte.
The order of the book is kept inside every file, so each thing is still
declared before it is used.

NAMES AT LINK TIME. A function that was static in one translation unit and
is now called from another has external linkage, and the engine's names are
short (fail, note, gcd): two of them might be the name of a function of a
library the program is linked with, and the linker would quietly bind one to
the other. engine_names.h therefore gives every exported function and
variable a prefixed name at link time (#define fail qre_fail). The sources
keep the names of the book.

THE DISCIPLINE that "check" enforces on the modules, which are from then on
the source:

  a. a function or variable defined without "static" in a module is declared
     in that module's header and listed in engine_names.h, and nothing else
     is listed there;
  b. a function or variable that a header declares is used outside its
     module: by another module, by the host file or by main.c, or through a
     macro or an inline function of a header; otherwise it should be static
     again;
  c. no header includes, directly or not, a header that includes it;
  d. the first header a module includes is its own.

That each module compiles alone is checked by the build itself: every module
is a translation unit of the target. With (d), so is every header: it is
read first, with nothing before it.

Only the Python 3 standard library. It is a tool for maintenance: nothing of
it is part of the program.
"""
import os
import re
import sys

PREFIX = "qre_"
BANNER = "/* ===="

# The modules, in the order of the book: name, the parts of the book it is
# made of, and what it holds (in Italian, like every comment of the engine).
# A part is parser.c, output.c, or a run of chapters of main.c, named after
# the module that most of it becomes (CHAPTERS below says where each run
# starts); ":before FILE" or ":after FILE" means what stands above or below
# the line of that run that included FILE.
MODULES = [
    ("engine_foundations", ["engine_foundations.c:before parser.c"],
     "limiti, errori e memoria, numeri esatti, monomi, polinomi, atomi, frazioni di polinomi (capitoli 1-7)"),
    ("parser", ["parser.c"],
     "la lettura del LaTeX: gli alberi delle espressioni, degli enunciati sugli insiemi, di quelli con quantificatori, delle matrici e degli indici, i lettori che li costruiscono, gli \\item di un file (capitoli 8, 9, 14, 17, 21, 31, 34, 37 e 39)"),
    ("engine_evaluation", ["engine_evaluation.c"],
     "le successioni note come dati, la valutazione di un albero in una frazione, i test di annullamento (capitoli 10-12)"),
    ("engine_induction", ["engine_induction.c"],
     "induzione su somme e prodotti: caso base, passo, verdetto (capitolo 13)"),
    ("engine_sets", ["engine_sets.c"],
     "relazioni tra insiemi: decisione per regioni, verifica indipendente, dimostrazione scritta (capitoli 15-16)"),
    ("engine_intervals", ["engine_intervals.c"],
     "i numeri reali come intervalli con l'errore garantito (capitolo 24)"),
    ("engine_quantifiers", ["engine_quantifiers.c"],
     "enunciati con quantificatori sui numeri: le regole di dimostrazione (capitoli da 18 a 18.7)"),
    ("engine_sign_tables", ["engine_sign_tables.c"],
     "la tabella dei segni: punti esatti, segni, righe, soluzioni, grafici, un parametro (capitoli 18.8-18.19)"),
    ("engine_explanation", ["engine_explanation.c"],
     "la spiegazione: i passaggi registrati e ricontrollati (capitolo 40)"),
    ("engine_quantifiers_verdict", ["engine_quantifiers_verdict.c"],
     "enunciati con quantificatori: verifica indipendente e verdetto (capitolo 19)"),
    ("engine_sequences", ["engine_sequences.c"],
     "induzione su una disuguaglianza, successioni definite per ricorrenza (capitoli 25-26)"),
    ("engine_derivatives", ["engine_foundations.c:after parser.c", "engine_derivatives.c"],
     "derivate: dimostrarle, calcolarle, usarle negli studi di funzione (capitolo 27)"),
    ("engine_logic", ["engine_logic.c"],
     "insiemi qualsiasi: modelli finiti, istanze, saturazione, e i compiti svolti per Vampire (capitolo 28)"),
    ("engine_limits", ["engine_limits.c"],
     "limiti (capitolo 29)"),
    ("engine_integrals", ["engine_integrals.c"],
     "integrali: primitive, integrali definiti e impropri (capitolo 30)"),
    ("engine_linear_algebra", ["engine_linear_algebra.c"],
     "algebra lineare esatta: matrici, determinanti, sistemi lineari (capitoli 32-33)"),
    ("engine_multivariable", ["engine_multivariable.c"],
     "funzioni di più variabili: derivate parziali, gradiente, hessiana, punti critici (capitoli 35-36)"),
    ("engine_indices", ["engine_indices.c"],
     "identità con gli indici: il conto su tutti i valori (capitolo 38)"),
    ("engine_statement", ["engine_statement.c:before output.c"],
     "dimostrare un enunciato: quale capitolo lo legge, e il verdetto (capitolo 20)"),
    ("output", ["output.c"],
     "il documento finale: enunciati, spiegazioni, dimostrazioni, soluzioni e grafici in LaTeX, e la sua compilazione in PDF (capitoli 41 e 22)"),
]

# The program on its own: the last chapter of the book, with main(). It is
# not a module: nothing uses it, and Vampire does not compile it.
PROGRAM = ("main", ["engine_statement.c:after output.c"])

# The runs of chapters of main.c, in the order of the file: the name of each
# and the number of its first chapter, as its banner writes it. A run goes up
# to the banner that opens the next.
CHAPTERS = [
    ("engine_foundations.c", "1"), ("engine_evaluation.c", "10"), ("engine_induction.c", "13"),
    ("engine_sets.c", "15"), ("engine_intervals.c", "24"), ("engine_quantifiers.c", "18"),
    ("engine_sign_tables.c", "18.8"), ("engine_explanation.c", "40"), ("engine_quantifiers_verdict.c", "19"),
    ("engine_sequences.c", "25"), ("engine_derivatives.c", "27"), ("engine_logic.c", "28"),
    ("engine_limits.c", "29"), ("engine_integrals.c", "30"), ("engine_linear_algebra.c", "32"),
    ("engine_multivariable.c", "35"), ("engine_indices.c", "38"), ("engine_statement.c", "20"),
]


# ------------------------------------------------------------------------------
# Reading C: tokens, and the declarations at file scope
# ------------------------------------------------------------------------------

IDENT = re.compile(r"[A-Za-z_][A-Za-z_0-9]*")
NUMBER = re.compile(r"\.?[0-9](?:[eEpP][+-]|[A-Za-z_0-9.])*")
OPERATORS = ("<<=", ">>=", "...", "->", "++", "--", "<<", ">>", "<=", ">=", "==", "!=", "&&", "||",
             "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "##")
SPACE = " \t\r\f\v\n"
NOT_NAMES = {"_Alignas", "__attribute__", "sizeof", "_Alignof"}       # followed by "(" without being a function
QUALIFIERS = {"const", "volatile", "restrict", "static", "extern", "inline", "register", "_Alignas"}   # not a type, not a name


def scan(text):
    """The tokens of a C text as (kind, start, end). Kinds: ws, comment, pp (a whole preprocessor directive),
    string, char, ident, number, punct."""
    i, n = 0, len(text)
    line_start = True   # nothing but spaces and comments since the last newline: a '#' here opens a directive
    while i < n:
        c = text[i]
        if c in SPACE:
            j = i
            while j < n and text[j] in SPACE:
                j += 1
            if "\n" in text[i:j]:
                line_start = True
            yield ("ws", i, j)
            i = j
        elif text.startswith("/*", i):
            j = text.index("*/", i + 2) + 2
            yield ("comment", i, j)
            i = j
        elif text.startswith("//", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            yield ("comment", i, j)
            i = j
        elif c == "#" and line_start:
            # A directive ends at the first newline that is neither escaped nor inside a comment.
            j = i
            while j < n and text[j] != "\n":
                if text.startswith("/*", j):
                    j = text.index("*/", j + 2) + 2
                elif text.startswith("//", j):
                    j = text.find("\n", j)
                    j = n if j < 0 else j
                elif text[j] == "\\" and j + 1 < n and text[j + 1] == "\n":
                    j += 2
                elif text[j] in "\"'":
                    j = closing_quote(text, j)
                else:
                    j += 1
            yield ("pp", i, j)
            i = j
            line_start = False
        else:
            line_start = False
            if c in "\"'":
                j = closing_quote(text, i)
                yield ("string" if c == '"' else "char", i, j)
                i = j
                continue
            match = IDENT.match(text, i) or NUMBER.match(text, i)
            if match:
                yield ("ident" if (c.isalpha() or c == "_") else "number", i, match.end())
                i = match.end()
                continue
            for operator in OPERATORS:
                if text.startswith(operator, i):
                    yield ("punct", i, i + len(operator))
                    i += len(operator)
                    break
            else:
                yield ("punct", i, i + 1)
                i += 1


def closing_quote(text, i):
    """The position after the string or character literal that opens at i."""
    quote = text[i]
    j = i + 1
    while text[j] != quote:
        j += 2 if text[j] == "\\" else 1
    return j + 1


def directive_of(text):
    """The name of a preprocessor directive and what follows it."""
    match = re.match(r"#[ \t]*([a-z_]+)", text)
    if not match:
        raise SystemExit("a directive without a name: %r" % text[:60])
    return match.group(1), text[match.end():]


class Token:
    __slots__ = ("kind", "text", "start", "end")

    def __init__(self, kind, text, start, end):
        self.kind, self.text, self.start, self.end = kind, text, start, end


class Item:
    """One declaration at file scope, with the comment that is its own.

    floating: what stands above it and is not its comment (blank lines, a
        chapter banner, a comment followed by a blank line): it stays in the
        .c wherever the declaration goes.
    comment: the comments right above it, with no blank line in between.
    text: the declaration, up to the end of its line.
    kind: macro, undef, include, conditional, typedef, type, function, inline,
        prototype, variable, assert.
    names: what it declares. refs: every identifier it mentions.
    head_refs: the identifiers its exported form mentions (rule 2 above).
    """

    def __init__(self, module, source, floating, comment, text):
        self.module, self.source = module, source
        self.floating, self.comment, self.text = floating, comment, text
        self.kind, self.names, self.tag_names, self.refs, self.head_refs = None, [], [], set(), set()
        self.order = 0
        self.static = self.has_body = self.has_initialiser = False
        self.exported = False
        self.paragraph = 0
        self.tokens = [Token(kind, text[s:e], s, e) for kind, s, e in scan(text) if kind not in ("ws", "comment")]

    def where(self):
        return "%s (%s): %s" % (self.module, self.source, " ".join(self.text.split())[:90])


def split_leading(lead):
    """Splits what stands above a declaration into what floats and the declaration's own comment."""
    cut = len(lead)
    for kind, start, end in reversed(list(scan(lead))):
        piece = lead[start:end]
        if kind == "ws":
            if piece.count("\n") >= 2:
                break
        elif piece.startswith(BANNER):
            break
        else:
            cut = start
    return lead[:cut], lead[cut:]


def items_of(text, module, source):
    """The declarations at file scope of a C text, in order, and what follows the last one."""
    tokens = list(scan(text))
    items = []
    position, i = 0, 0
    while True:
        j = i
        while j < len(tokens) and tokens[j][0] in ("ws", "comment"):
            j += 1
        if j == len(tokens):
            return items, text[position:]
        start = tokens[j][1]
        k = j
        if tokens[k][0] == "pp":
            # A conditional is one declaration, up to its #endif.
            if directive_of(text[tokens[k][1]:tokens[k][2]])[0] in ("if", "ifdef", "ifndef"):
                depth = 0
                while True:
                    if tokens[k][0] == "pp":
                        name = directive_of(text[tokens[k][1]:tokens[k][2]])[0]
                        depth += name in ("if", "ifdef", "ifndef")
                        depth -= name == "endif"
                        if depth == 0:
                            break
                    k += 1
        else:
            # A declaration ends at its semicolon, or at the brace that closes the body of a function: a brace
            # opened right after a parenthesis, outside an initialiser.
            depth, body, assigned, previous = 0, False, False, None
            while True:
                kind, s, e = tokens[k]
                piece = text[s:e]
                if kind == "punct":
                    if piece in ("(", "[", "{"):
                        if piece == "{" and depth == 0 and previous == ")" and not assigned:
                            body = True
                        depth += 1
                    elif piece in (")", "]", "}"):
                        depth -= 1
                        if depth == 0 and piece == "}" and body:
                            break
                    elif depth == 0 and piece == ";":
                        break
                    elif depth == 0 and piece == "=":
                        assigned = True
                if kind not in ("ws", "comment", "pp"):
                    previous = piece
                k += 1
        end = tokens[k][2]

        # A comment that starts on the same line belongs to the declaration.
        k += 1
        if k < len(tokens) and tokens[k][0] == "ws" and "\n" not in text[tokens[k][1]:tokens[k][2]] \
                and k + 1 < len(tokens) and tokens[k + 1][0] == "comment":
            k += 1
        if k < len(tokens) and tokens[k][0] == "comment" and tokens[j][0] != "pp":
            end = tokens[k][2]
            k += 1
        floating, comment = split_leading(text[position:start])
        items.append(Item(module, source, floating, comment, text[start:end]))
        position, i = end, k


def identifiers(text):
    return {text[s:e] for kind, s, e in scan(text) if kind == "ident"}


def file_mentions(path):
    """What a C file outside the modules mentions of the names declared at file scope."""
    with open(path, encoding="utf-8") as source:
        items = items_of(source.read(), None, path)[0]
    found = set()
    for item in items:
        analyse(item)
        found |= item.refs
    return found


def enum_constants(tokens):
    """The constants of every enum whose body is among the tokens."""
    names = []
    for index, token in enumerate(tokens):
        if token.text != "enum":
            continue
        k = index + 1
        if k < len(tokens) and tokens[k].kind == "ident":
            k += 1
        if k >= len(tokens) or tokens[k].text != "{":
            continue
        depth, expect = 0, False
        while True:
            piece = tokens[k].text
            if piece in ("(", "[", "{"):
                depth += 1
                expect = depth == 1
            elif piece in (")", "]", "}"):
                depth -= 1
                if depth == 0:
                    break
            elif depth == 1 and piece == ",":
                expect = True
            elif expect and tokens[k].kind == "ident":
                names.append(piece)
                expect = False
            k += 1
    return names


def tags(tokens):
    """The tags of the structures, unions and enums whose body is among the tokens at file scope."""
    names, depth = [], 0
    for index, token in enumerate(tokens):
        if token.text in ("(", "[", "{"):
            depth += 1
        elif token.text in (")", "]", "}"):
            depth -= 1
        elif depth == 0 and token.text in ("struct", "union", "enum") and index + 2 < len(tokens) \
                and tokens[index + 1].kind == "ident" and tokens[index + 2].text == "{":
            names.append(tokens[index + 1].text)
    return names


def outer(tokens):
    """The tokens outside every bracket, with their indices, and the brackets themselves at depth 0."""
    depth = 0
    for index, token in enumerate(tokens):
        if token.text in (")", "]", "}") and token.kind == "punct":
            depth -= 1
        if depth == 0:
            yield index, token
        if token.text in ("(", "[", "{") and token.kind == "punct":
            depth += 1


BASIC_TYPES = {"int", "char", "long", "short", "unsigned", "signed", "double", "float", "void", "_Bool", "__int128"}
STATEMENT_WORDS = {"return", "goto", "if", "while", "for", "switch", "break", "continue", "case", "default",
                   "sizeof", "else", "do"}


def members(tokens):
    """The indices of the tokens that name a member where a structure or a union is declared."""
    found, braces = set(), []
    for index, token in enumerate(tokens):
        if token.kind == "ident":
            if braces and braces[-1] and index + 1 < len(tokens) and tokens[index + 1].text in (";", ",", "[", ":"):
                found.add(index)
        elif token.kind == "punct" and token.text == "{":
            before = [t.text for t in tokens[max(0, index - 2):index]]
            braces.append(bool(before) and (before[-1] in ("struct", "union") or
                                            (len(before) == 2 and before[0] in ("struct", "union"))))
        elif token.kind == "punct" and token.text in ("(", "["):
            braces.append(False)
        elif token.kind == "punct" and token.text in (")", "]", "}"):
            braces.pop()
    return found


def mentions(tokens, own=()):
    """The identifiers among the tokens that can name something declared at file scope: not the name of a
    member (after "." or "->", or where a structure is declared), and not one of the given names, which
    belong to the declaration itself (parameters, local variables).

    This is what keeps an interface to what is really used: a local variable called `now` does not make the
    function now() of another module one of its exports. It errs on the safe side: a name taken for a
    mention when it is not only widens an interface; one missed leaves something static that another module
    calls, and the build stops."""
    hidden, out = members(tokens), set()
    for index, token in enumerate(tokens):
        if token.kind == "pp":
            out |= identifiers(directive_of(token.text)[1])
        elif token.kind == "ident" and index not in hidden and token.text not in own \
                and not (index and tokens[index - 1].text in (".", "->")):
            out.add(token.text)
    return out


def parameters(tokens, opening):
    """The names of the parameters of the function whose parameter list opens at the given token."""
    names, depth, current = [], 0, []
    for token in tokens[opening:]:
        if token.kind == "punct" and token.text in ("(", "[", "{"):
            depth += 1
            if depth == 1:
                continue
        elif token.kind == "punct" and token.text in (")", "]", "}"):
            depth -= 1
        if depth == 0 or (depth == 1 and token.text == ","):
            texts = [t.text for t in current]
            pointer = next((i for i in range(len(texts) - 2) if texts[i] == "(" and texts[i + 1] == "*"), None)
            if pointer is not None and current[pointer + 2].kind == "ident":
                names.append(texts[pointer + 2])
            else:
                level, words = 0, []
                for t in current:
                    level += t.text in ("(", "[")
                    level -= t.text in (")", "]")
                    if level == 0 and t.kind == "ident" and t.text not in QUALIFIERS and t.text not in ("struct", "union", "enum"):
                        words.append(t.text)
                if len(words) >= 2:             # a type and a name: one word alone is a type
                    names.append(words[-1])
            current = []
            if depth == 0:
                return names
        else:
            current.append(token)
    return names


def declared_at(tokens, index):
    """The names declared by the statement that starts at the given token, if it is a declaration of local
    variables: a type (a keyword, a tag, or one identifier) followed by a name and then "=", ";", "," or "[".
    Two identifiers in a row, or "T *name =", are never an expression statement."""
    count = len(tokens)
    while index < count and tokens[index].text in QUALIFIERS:
        index += 1
    if index >= count:
        return []
    token = tokens[index]
    if token.text in ("struct", "union", "enum"):
        if index + 1 >= count or tokens[index + 1].kind != "ident":
            return []
        index += 2
    elif token.text in BASIC_TYPES:
        while index < count and (tokens[index].text in BASIC_TYPES or tokens[index].text in QUALIFIERS):
            index += 1
    elif token.kind == "ident" and token.text not in STATEMENT_WORDS:
        index += 1
    else:
        return []
    names = []
    while index < count:
        while index < count and (tokens[index].text == "*" or tokens[index].text in QUALIFIERS):
            index += 1
        if index + 2 < count and tokens[index].text == "(" and tokens[index + 1].text == "*" and tokens[index + 2].kind == "ident":
            name, index = tokens[index + 2].text, index + 3
        elif index < count and tokens[index].kind == "ident" and tokens[index].text not in STATEMENT_WORDS:
            name, index = tokens[index].text, index + 1
        else:
            break
        if index >= count or tokens[index].text not in ("=", ";", ",", "[", ")"):
            break
        names.append(name)
        depth = 0
        while index < count:                    # to the comma that opens the next declarator
            piece = tokens[index]
            if piece.kind == "punct" and piece.text in ("(", "[", "{"):
                depth += 1
            elif piece.kind == "punct" and piece.text in (")", "]", "}"):
                if depth == 0:
                    return names
                depth -= 1
            elif depth == 0 and piece.text == ";":
                return names
            elif depth == 0 and piece.text == ",":
                index += 1
                break
            index += 1
    return names


def local_names(tokens, body):
    """The names of the local variables declared in the body of a function, which opens at the given token."""
    names, parentheses = [], 0
    for index in range(body, len(tokens)):
        token = tokens[index]
        if token.kind != "punct":
            continue
        if token.text == "(":
            parentheses += 1
            if tokens[index - 1].text == "for":
                names += declared_at(tokens, index + 1)
        elif token.text == ")":
            parentheses -= 1
        elif token.text in (";", "{", "}") and parentheses == 0:
            names += declared_at(tokens, index + 1)
    return names


def analyse(item):
    """Fills kind, names, refs and head_refs of a declaration."""
    tokens = item.tokens
    first = tokens[0]
    item.refs = mentions(tokens)
    item.head_refs = set(item.refs)

    if first.kind == "pp":
        name, rest = directive_of(first.text)
        if name == "define":
            item.kind, item.names = "macro", [IDENT.match(rest.lstrip()).group(0)]
            own = re.match(r"\s*\w+\(([^)]*)\)", rest)       # the parameters of a macro with arguments
            if own:
                item.refs -= {word.strip() for word in own.group(1).split(",")}
                item.head_refs = set(item.refs)
        elif name in ("undef", "include"):
            item.kind = name
        elif name in ("if", "ifdef", "ifndef"):
            item.kind = "conditional"
        else:
            raise SystemExit("a directive this tool does not know at file scope: " + item.where())
        return
    if first.text == "_Static_assert":
        item.kind = "assert"
        return

    level = list(outer(tokens))
    item.static = any(t.text == "static" for _, t in level)
    last = tokens[-1] if tokens[-1].kind != "comment" else tokens[-2]
    if first.text == "typedef":
        item.kind = "typedef"
        before = [t for _, t in level][:-1]          # without the semicolon
        if any(t.text == "," for t in before):
            raise SystemExit("a typedef of several names: " + item.where())
        if before[-1].text == ")":
            # A function or a pointer to one: the name is before the first parenthesis, or right inside it.
            index = next(i for i, t in level if t.text == "(")
            name = tokens[index - 1].text if tokens[index + 1].text != "*" else \
                next(t.text for t in tokens[index + 1:] if t.kind == "ident" and t.text not in QUALIFIERS)
        elif before[-1].text == "]":
            index = next(i for i, t in level if t.text == "[")
            name = tokens[index - 1].text
        else:
            name = before[-1].text
        item.names = [name] + enum_constants(tokens)
        item.tag_names = tags(tokens)
        item.has_body = any(t.text == "{" for _, t in level)
        return
    if first.text in ("struct", "union", "enum"):
        shape = [t.text for _, t in level]
        if shape[-2:] == ["}", ";"] or (len(shape) == 3 and shape[2] == ";"):
            item.kind = "type"
            item.has_body = "{" in shape
            item.names = enum_constants(tokens)
            item.tag_names = tags(tokens) or [t.text for t in tokens[1:2] if t.kind == "ident"]
            return

    # A function or one or more variables. A parenthesis outside every bracket, before any "=", after a name,
    # opens the parameters of a function; after a type, with "*" inside, it declares a pointer to a function.
    function = None
    for index, token in level:
        if token.text == "=":
            break
        if token.text == "(":
            if tokens[index + 1].text == "*":
                inner = index + 1
                while tokens[inner].text == "*" or tokens[inner].text in QUALIFIERS:
                    inner += 1
                if tokens[inner + 1].text == "(":
                    function = (tokens[inner].text, index)
                break
            if tokens[index - 1].kind == "ident" and tokens[index - 1].text not in NOT_NAMES:
                function = (tokens[index - 1].text, index)
                break
    if function:
        item.names = [function[0]]
        own = set(parameters(tokens, function[1]))
        if last.text == "}":
            item.kind = "inline" if any(t.text == "inline" for _, t in level) else "function"
            body = max(i for i, t in level if t.text == "{")
            item.body_start = tokens[body].start
            item.head_refs = mentions(tokens[:body], own)
            item.refs = item.head_refs | mentions(tokens[body:], own | set(local_names(tokens, body)))
            if item.kind == "inline":
                item.head_refs = set(item.refs)
        else:
            item.kind = "prototype"
            item.refs = item.head_refs = mentions(tokens, own)
        return

    item.kind = "variable"
    item.names = variable_names(item, level)
    item.names += enum_constants(tokens)
    item.tag_names = tags(tokens)
    item.has_initialiser = any(t.text == "=" for _, t in level)
    spans = initialiser_spans(item)
    item.head_refs = mentions([t for i, t in enumerate(tokens) if not any(start <= i < end for start, end in spans)])


def declarators(level):
    """The declarators of a variable declaration as (first, last) indices of tokens, initialisers included."""
    cuts = [i for i, t in level if t.text in (",", ";")]
    spans, start = [], 0
    for cut in cuts:
        spans.append((start, cut))
        start = cut + 1
    return spans


def variable_names(item, level):
    tokens = item.tokens
    names = []
    for number, (start, end) in enumerate(declarators(level)):
        own = [(i, t) for i, t in level if start <= i < end]
        stop = next((i for i, t in own if t.text in ("=", "[")), end)
        pointer = next((i for i, t in own if t.text == "(" and tokens[i + 1].text == "*" and i < stop), None)
        if pointer is not None:
            name = next(t.text for t in tokens[pointer + 1:] if t.kind == "ident" and t.text not in QUALIFIERS)
        else:
            candidates = [t.text for i, t in own if i < stop and t.kind == "ident" and t.text not in QUALIFIERS]
            if not candidates:
                raise SystemExit("a declaration this tool cannot read: " + item.where())
            name = candidates[-1] if number == 0 else candidates[0]
        names.append(name)
    return names


def initialiser_spans(item):
    """The (first, last) indices of tokens of each initialiser, from its "=" up to the comma or semicolon."""
    level = list(outer(item.tokens))
    spans, opened = [], None
    for index, token in level:
        if token.text == "=" and opened is None:
            opened = index
        elif token.text in (",", ";") and opened is not None:
            spans.append((opened, index))
            opened = None
    return spans


# ------------------------------------------------------------------------------
# What is exported
# ------------------------------------------------------------------------------

class Engine:
    """The declarations of every module and of the program, and where each name is defined.

    modules: (name, declarations, what follows the last one, description), the program last.
    home: for a name, the declarations that define it: at most one for the ordinary names (functions,
        variables, types named by a typedef, macros, constants of an enum) and one for the tags.
    """

    def __init__(self, modules):
        self.modules = modules
        declared = [{}, {}]
        for _, items, _, _ in modules:
            for item in items:
                for space, names in enumerate((item.names, item.tag_names)):
                    for name in names:
                        declared[space].setdefault(name, []).append(item)
        self.declared = declared
        self.home = {}
        for space in declared:
            for name, items in space.items():
                defining = [item for item in items if item.kind != "prototype"]
                if not defining:
                    raise SystemExit("declared and never defined: " + items[0].where())
                complete = [item for item in defining
                            if item.has_body or item.has_initialiser or item.kind in ("function", "inline", "macro")]
                chosen = (complete or defining)[0]
                for other in defining:
                    if other is not chosen and other in complete:
                        raise SystemExit("defined twice: %s\n  and %s" % (chosen.where(), other.where()))
                    if other is not chosen and other.module != chosen.module and other.kind == "variable":
                        raise SystemExit("a variable declared in two modules: %s\n  and %s" % (chosen.where(), other.where()))
                self.home.setdefault(name, []).append(chosen)

    def elsewhere(self, item, names, header=False):
        """The declarations, in other modules, that the item needs to see, among those that define the given
        names. A name mentioned before the book defines it does not need the definition there: it is a
        structure known by its tag, or a function or a variable declared ahead. The interface of the item
        never needs it; its source needs it for a function or a variable, which the interface of the other
        module declares."""
        return [home for name in names for home in self.home.get(name, ())
                if home.module != item.module and
                (home.order < item.order or (not header and home.kind in ("function", "variable")))]

    def mark_exported(self, host_refs):
        """Rules 1, 2 and 3 of the comment at the top."""
        pending = []

        def mark(item):
            if not item.exported:
                item.exported = True
                pending.append(item)

        by_paragraph = {}
        for _, items, _, _ in self.modules:
            for item in items:
                by_paragraph.setdefault((item.module, item.paragraph), []).append(item)
                for home in self.elsewhere(item, item.refs):
                    mark(home)
        for name in host_refs:
            for home in self.home.get(name, ()):
                mark(home)
        while pending:
            item = pending.pop()
            for name in item.head_refs:
                for home in self.home.get(name, ()):
                    if home.module == item.module:
                        mark(home)
            if item.kind in ("macro", "type", "typedef"):
                for other in by_paragraph[(item.module, item.paragraph)]:
                    if other.kind in ("macro", "type", "typedef"):
                        mark(other)

        # A prototype, or the declaration of a variable defined further down, follows the definition.
        for space in self.declared:
            for name, items in space.items():
                for item in items:
                    if any(home.exported for home in self.home[name]) and item.kind in ("prototype", "variable"):
                        item.exported = True

    def is_home(self, item):
        return all(item in self.home[name] for name in item.names)

    def expanded_refs(self, item):
        """What a declaration mentions, with what the macros it mentions expand to."""
        seen, pending = set(), list(item.refs)
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            for home in self.home.get(name, ()):
                if home.kind == "macro":
                    pending.extend(home.refs)
        return seen


# The parts of the book, in the order the compiler read them.
BOOK = ["engine_foundations.c:before parser.c", "parser.c", "engine_foundations.c:after parser.c",
        "engine_evaluation.c", "engine_induction.c", "engine_sets.c", "engine_intervals.c", "engine_quantifiers.c",
        "engine_sign_tables.c", "engine_explanation.c", "engine_quantifiers_verdict.c", "engine_sequences.c",
        "engine_derivatives.c", "engine_logic.c", "engine_limits.c", "engine_integrals.c",
        "engine_linear_algebra.c", "engine_multivariable.c", "engine_indices.c",
        "engine_statement.c:before output.c", "output.c", "engine_statement.c:after output.c"]


def chapter_runs(main_text):
    """main.c of the book cut at the banners of CHAPTERS: what stands above the first chapter (the design
    comment and the index), and the text of each run by name."""
    banner = "/* " + "=" * 77 + "\n"
    where, at = {}, main_text.find(banner)
    while at >= 0:
        title = re.match(r" \* ([0-9]+(?:\.[0-9]+)?)\.? ", main_text[at + len(banner):])
        if title:
            where.setdefault(title.group(1), at)        # a chapter starts where its number first appears
        at = main_text.find(banner, at + len(banner))
    cuts = []
    for name, chapter in CHAPTERS:
        if chapter not in where:
            raise SystemExit("main.c has no banner for chapter %s, the first of %s" % (chapter, name))
        cuts.append(where[chapter])
    if cuts != sorted(cuts):
        raise SystemExit("the chapters of main.c are not in the order this tool expects")
    runs = {name: main_text[cuts[index]:cuts[index + 1] if index + 1 < len(cuts) else len(main_text)]
            for index, (name, _) in enumerate(CHAPTERS)}
    return main_text[:cuts[0]], runs


def read_book(directory):
    """The engine as the book form in a directory gives it (main.c, parser.c and output.c, as in the
    Quaerens repository), and what main.c says above its first chapter."""
    def read(name):
        with open(os.path.join(directory, name), encoding="utf-8") as source:
            return source.read()

    preface, texts = chapter_runs(read("main.c"))
    texts.update({name: read(name) for name in ("parser.c", "output.c")})
    parsed = {}

    def part(spec):
        name, _, cut = spec.partition(":")
        if name not in parsed:
            parsed[name] = items_of(texts[name], None, name)
        items, tail = parsed[name]
        if cut:
            side, included = cut.split()
            at = next(i for i, item in enumerate(items) if item.text.startswith('#include "%s"' % included))
            items, tail = (items[:at], "\n") if side == "before" else (items[at + 1:], tail)
        return items, tail

    order = 0
    for spec in BOOK:
        for item in part(spec)[0]:
            order += 1
            item.order = order
    modules = []
    for name, specs, description in MODULES + [PROGRAM + ("",)]:
        items, tail = [], ""
        for spec in specs:
            more, after = part(spec)
            if items and more:
                more[0].floating = tail + more[0].floating     # what closed the part above
            items, tail = items + more, after
        paragraph = 0
        for item in items:
            item.module = name
            analyse(item)
            if item.floating.count("\n") >= 2 or "/*" in item.floating or not paragraph:
                paragraph += 1
            item.paragraph = paragraph
        modules.append((name, items, tail, description))
    return Engine(modules), preface


# ------------------------------------------------------------------------------
# Writing the modules
# ------------------------------------------------------------------------------

def without(text, spans):
    """The text without the given (start, end) spans."""
    out, position = [], 0
    for start, end in sorted(spans):
        out.append(text[position:start])
        position = end
    return "".join(out) + text[position:]


def static_span(item):
    """The span of the "static" of a declaration, with the space after it."""
    token = next(t for _, t in outer(item.tokens) if t.text == "static")
    end = token.end
    while item.text[end] in " \t":
        end += 1
    return token.start, end


def array_length(item):
    """The number of elements of an array declared without a length and initialised with a list, with the index
    of the token that opens its empty brackets; None if there is no such array or the list has designators.
    A wrong count cannot pass: the module that defines the array includes the header, and the compiler
    compares the two lengths."""
    tokens = item.tokens
    for index in range(len(tokens) - 3):
        if tokens[index].text != "[" or tokens[index + 1].text != "]":
            continue
        k = index + 2
        while tokens[k].text == "[":            # further dimensions, with their lengths
            while tokens[k].text != "]":
                k += 1
            k += 1
        if tokens[k].text != "=" or tokens[k + 1].text != "{":
            return None
        depth, count, pending = 0, 0, False
        for token in tokens[k + 1:]:
            opens = token.kind == "punct" and token.text in ("(", "[", "{")
            closes = token.kind == "punct" and token.text in (")", "]", "}")
            if depth == 1 and not pending and token.text in ("[", "."):
                return None                     # a designator: the length is not a count
            if opens:
                depth += 1
                pending = depth > 1
            elif closes:
                depth -= 1
                if depth == 0:
                    return count + pending, index
            elif depth == 1 and token.text == ",":
                count += 1
                pending = False
            elif depth == 1:
                pending = True
        return None
    return None


def unnamed_structure(item):
    """The span of a structure without a tag that is the type of a variable, "struct {...}", as (start of the
    brace, end of the brace), or None. Two modules can share such a variable only if its type has a name: an
    exported one gets the name of the variable as its tag (tags are a name space of their own)."""
    tokens = item.tokens
    for index, token in outer(tokens):
        if token.text in ("struct", "union") and tokens[index + 1].text == "{":
            depth = 0
            for closing in tokens[index + 1:]:
                depth += closing.text in ("(", "[", "{")
                depth -= closing.text in (")", "]", "}")
                if depth == 0:
                    return tokens[index + 1].start, closing.end
    return None


def definition(item):
    """An exported function or variable as its module defines it: without "static", and with the tag that
    the header gave to a structure without one."""
    text, spans = item.text, [static_span(item)]
    body = unnamed_structure(item) if item.kind == "variable" else None
    if body:
        text = text[:body[0]] + item.names[0] + text[body[1]:]
    return without(text, spans)


def declaration(item):
    """How the header declares an exported function or variable."""
    if item.kind == "function":
        return without(item.text[:item.body_start].rstrip(), [static_span(item)]) + ";"
    spans = [static_span(item)]
    body = unnamed_structure(item)
    if body:
        keyword = item.text[:body[0]].split()[-1]
        named = "%s %s %s;\n" % (keyword, item.names[0], item.text[body[0]:body[1]])
        return named + "extern " + declaration_text(item, spans + [(body[0], body[1])], item.names[0])
    return "extern " + declaration_text(item, spans, "")


def declaration_text(item, spans, tag):
    """The declaration of a variable without the given spans and without its initialisers; tag is written
    where the body of a structure was taken away."""
    tokens = item.tokens
    spans = spans + [(tokens[start - 1].end, tokens[end].start) for start, end in initialiser_spans(item)]
    semicolon = max(t.end for _, t in outer(tokens) if t.text == ";")
    length = array_length(item)
    pieces, position = [], 0
    insert = tokens[length[1]].end if length else None
    for start, end in sorted(spans):
        if insert is not None and position <= insert <= start:
            pieces.append(item.text[position:insert] + str(length[0]))
            position = insert
            insert = None
        pieces.append(item.text[position:start])
        if tag and item.text[start] == "{":
            pieces.append(tag)
        position = end
    pieces.append(item.text[position:semicolon])
    return "".join(pieces)


def comment(text, width=76):
    """A C comment with the given paragraphs (separated by blank lines), wrapped."""
    lines = []
    for paragraph in text.strip().split("\n\n"):
        if lines:
            lines.append("")
        line = ""
        for word in paragraph.split():
            if line and len(line) + 1 + len(word) > width:
                lines.append(line)
                line = word
            else:
                line = (line + " " + word).strip()
        lines.append(line)
    return "/* " + "\n".join((" * " + line).rstrip() if number else line for number, line in enumerate(lines)) + " */\n"


FOUNDATION_INTERFACES = """
/* I nomi con cui il programma collega le funzioni e le variabili che un
 * modulo del motore offre agli altri: va letto dopo la libreria standard e
 * prima di ogni altra cosa, perché cambia quei nomi dovunque compaiono. */
#include "engine_names.h"

/* Il verificatore dei certificati (13h). È un modulo a sé, compilato una
 * volta sola (Proof/IndependentChecker), che giudica sia ciò che dimostra
 * il motore sia ciò che trova Vampire. Di lui il motore vede soltanto
 * ck_check() e il tipo della sua risposta, CkAnswer, con i suoi tre valori:
 * li dichiara Math/EngineModules.h. Il verificatore non sa nulla del motore.
 *
 * Warning: non usare qui altri nomi del verificatore. Il controllo vale
 * qualcosa solo finché i due non hanno codice in comune: nemmeno un'utilità
 * "innocua". Che il motore veda solo quell'interfaccia lo rende un fatto. */
#include "Math/EngineModules.h"

/* I grafici (18q). Anche i grafici sono un modulo a sé (Math/Plot), che non
 * sa nulla del motore: disegna ciò che gli si dice e scrive un PDF. Se ne
 * usano solo le funzioni e i tipi dell'interfaccia, Math/Plot.h, che
 * cominciano con pl_, Pl o PL_. */
#include "Math/Plot.h"
"""


# What the comments of the book say about the files it is made of, said for the modules. Each entry is the
# file, the text of the book and the text of the modules; a text that is not found exactly once stops the tool,
# so a book that has changed there is noticed.
REWORDED = [
    ("main.c", """ * Il programma è fatto di cinque file, e questo include gli altri quattro:
 *
 *   main.c     il motore: cerca, calcola, decide, ricontrolla;
 *   parser.c   la lettura del LaTeX: dal testo agli alberi;
 *   output.c   il documento finale, con dimostrazioni, soluzioni e grafici;
 *   plot.c     i grafici: un piccolo matplotlib in C, che scrive PDF;
 *   checker.c  il verificatore indipendente dei certificati.
 *
 * parser.c e output.c sono volumi di questo stesso libro: usano ciò che qui
 * viene prima della riga che li include. plot.c e checker.c sono programmi a
 * sé, che non sanno nulla degli altri, e di loro si usa solo l'interfaccia.
""", """ * Il motore è un libro diviso in moduli, ognuno compilato per conto suo:
 *
 *   engine_*.c  il motore: cerca, calcola, decide, ricontrolla;
 *   parser.c    la lettura del LaTeX: dal testo agli alberi;
 *   output.c    il documento finale, con dimostrazioni, soluzioni e grafici;
 *   main.c      questo file: il programma a sé, con main();
 *   plot.c      i grafici: un piccolo matplotlib in C, che scrive PDF;
 *   checker.c   il verificatore indipendente dei certificati.
 *
 * Ogni modulo ha i suoi capitoli in NOME.c e la sua interfaccia in NOME.h:
 * ciò che gli altri moduli ne usano. Il resto è static, e fuori dal modulo
 * non si vede. L'elenco dei moduli segue l'indice dei capitoli. plot.c e
 * checker.c sono programmi a sé, che non sanno nulla degli altri, e di loro
 * si usa solo l'interfaccia.
"""),
    ("main.c", """ * aritmetica e i suoi polinomi, non usa nulla di questo file, ed è abbastanza
""", """ * aritmetica e i suoi polinomi, non usa nulla del motore, ed è abbastanza
"""),
    ("main.c", """ *     cc -std=c11 -O2 -Wall -Wextra -o mathresearcher main.c
 *
 * Servono GCC o Clang: i conti esatti usano __int128. main.c include
 * parser.c, output.c, plot.c e checker.c, che devono stare nella stessa
 * cartella; il verificatore si compila anche da solo (vedi la testa di
 * checker.c). Per avere il documento finale in PDF serve inoltre un
 * compilatore LaTeX installato (tectonic oppure pdflatex); senza, il
 * programma scrive comunque il documento .tex e il PDF dei grafici.
""", """ * La fa CMake, con il resto di Vampire. Ogni modulo è un'unità di
 * compilazione dell'obiettivo mathengine; questo file, con quei moduli, dà
 * il programma a sé (l'obiettivo quaerens), che legge gli stessi enunciati
 * senza Vampire.
 *
 * Servono GCC o Clang: i conti esatti usano __int128. Il verificatore si
 * compila anche da solo (vedi la testa di checker.c). Per avere il
 * documento finale in PDF serve inoltre un compilatore LaTeX installato
 * (tectonic oppure pdflatex); senza, il programma scrive comunque il
 * documento .tex e il PDF dei grafici.
"""),
    ("main.c", """ * La numerazione è una sola per i tre file che formano il programma. I
 * capitoli segnati con un nome di file stanno in quel file, incluso da qui
 * nel punto in cui compaiono nell'elenco. Il capitolo 18, il più lungo, è
""", """ * La numerazione è una sola per tutti i moduli. I capitoli segnati con un
 * nome di file stanno in quel file; gli altri nei moduli engine_*.c, come
 * dice l'elenco che segue l'indice. Il capitolo 18, il più lungo, è
"""),
    ("parser.c", """ * enunciato costruisce l'albero che il motore, in main.c, dimostra o
""", """ * enunciato costruisce l'albero che il motore dimostra o
"""),
    ("parser.c", """ * Non è un programma a sé: è un volume dello stesso libro di main.c, che lo
 * include dopo il suo capitolo 7. Usa ciò che main.c ha già presentato: i
 * limiti (capitolo 1), gli errori e la memoria di lavoro (capitolo 2), e i
 * tipi dei numeri esatti e delle frazioni di polinomi (capitoli 3-7), che
 * compaiono nei nodi degli alberi come annotazioni lasciate dal motore. Del
 * motore, che viene dopo, usa solo eval(), dichiarata nel capitolo 17. I
 * capitoli conservano il numero che avevano quando stavano in main.c, perché
 * i commenti, i test e il README citano le regole per numero (17d, 17h): la
 * numerazione è una sola per main.c, parser.c e output.c.
""", """ * È un modulo del motore, compilato per conto suo: ciò che gli altri ne
 * usano, gli alberi e i loro lettori, è dichiarato in parser.h. Usa i
 * limiti (capitolo 1), gli errori e la memoria di lavoro (capitolo 2), e i
 * tipi dei numeri esatti e delle frazioni di polinomi (capitoli 3-7), che
 * compaiono nei nodi degli alberi come annotazioni lasciate dal motore: li
 * riceve da engine_foundations.h. Del motore, che nel libro viene dopo, usa
 * solo eval(), dichiarata nel capitolo 17. I capitoli conservano il numero
 * che hanno nel libro, perché i commenti, i test e il README citano le
 * regole per numero (17d, 17h): la numerazione è una sola per tutti i
 * moduli.
"""),
    ("output.c", """ * È un volume dello stesso libro di main.c, che lo include dopo il suo
 * capitolo 20. Usa ciò che main.c ha già presentato: il verdetto (capitolo
 * 13), la riga che lo riassume, verdict_print() (capitolo 20), e la
 * spiegazione (capitolo 40). Di plot.c usa l'apertura del PDF e l'aggiunta
 * di una pagina. I capitoli hanno i numeri 41 e 22: la numerazione è una
 * sola per main.c, parser.c e output.c, e il 41, nato dopo, sta prima
 * perché il 22 lo usa.
""", """ * È un modulo del motore, compilato per conto suo: ciò che gli altri ne
 * usano, il documento e le funzioni che lo scrivono, è dichiarato in
 * output.h. Usa il verdetto (capitolo 13), la riga che lo riassume,
 * verdict_print() (capitolo 20), e la spiegazione (capitolo 40): li riceve
 * dalle interfacce dei loro moduli. Dei grafici usa l'apertura del PDF e
 * l'aggiunta di una pagina. I capitoli hanno i numeri 41 e 22: la
 * numerazione è una sola per tutti i moduli, e il 41, nato dopo, sta prima
 * perché il 22 lo usa.
"""),
]


def reworded(file_name, text):
    """The text of a file of the modules with what its comments say about the files brought up to date: the
    passages of REWORDED, and "il capitolo 32 di main.c", which is now a chapter of the engine."""
    for name, old, new in REWORDED:
        if name == file_name:
            if text.count(old) != 1:
                raise SystemExit("%s: a passage to reword is not there exactly once:\n%s" % (file_name, old))
            text = text.replace(old, new)
    if file_name != "main.c":
        text = re.sub(r"\b(di|in)(\s+\*\s+|\s+)main\.c\b",
                      lambda found: {"di": "del", "in": "nel"}[found.group(1)] + found.group(2) + "motore", text)
        text = text.replace("dopo l'inclusione di parser.c", "in testa a questo file")
        if "main.c" in text:
            line = next(line for line in text.split("\n") if "main.c" in line)
            raise SystemExit("%s still speaks of main.c: %s" % (file_name, line))
    return text


def join_source(pieces, tail):
    """Joins the pieces of a source, given as (text, taken): where a declaration was taken away, its line goes
    with it and the blank lines that stood on its two sides are not left piled up."""
    out, taken_before = "", False
    for piece, taken in pieces + [(tail, False)]:
        if taken_before:
            piece = piece[1:] if piece.startswith("\n") else piece
            if out.endswith("\n\n") or not out:
                piece = piece.lstrip("\n")
        out += piece
        taken_before = taken
    return out.rstrip("\n") + "\n"


def module_texts(engine, name, items, tail, description):
    """The header and the source of a module, the names it gives the linker, and the modules whose interfaces
    its own interface includes."""
    first = engine.modules[0][0]
    order = [module for module, _, _, _ in engine.modules]

    # The header: in the order of the book, what moves there with its comment and the declarations of the rest.
    header, last, linked, uses_header = [], None, [], set()
    for item in items:
        if not item.exported or item.kind in ("prototype", "conditional", "include") or not engine.is_home(item):
            continue
        uses_header.update(home.module for home in engine.elsewhere(item, item.head_refs, header=True))
        if item.kind in ("function", "variable"):
            piece, shape = declaration(item), "declared"
            linked.extend(item.names if item.kind == "function" else variable_names(item, list(outer(item.tokens))))
        else:
            piece, shape = item.comment + item.text, ("moved", item.paragraph)
        if last is None:
            separator = ""
        elif shape == "declared" and last == "declared":
            separator = "\n"
        elif shape == last and item.floating.count("\n") < 2:
            separator = "\n"
        else:
            separator = "\n\n"
        header.append(separator + piece)
        last = shape
    if name != first:
        uses_header.add(first)

    # The source: the book as it was, without what moved, and without "static" on what is exported.
    pieces, uses_source = [], set()
    for item in items:
        uses_source.update(home.module for home in engine.elsewhere(item, engine.expanded_refs(item)))
        if item.kind in ("conditional", "include") or (item.exported and item.kind in ("macro", "type", "typedef", "inline")):
            pieces.append((item.floating, True))
            continue
        text = definition(item) if item.exported and item.static else item.text
        pieces.append((item.floating + item.comment + text, False))
    body = join_source(pieces, tail)

    includes = lambda modules: "".join('#include "%s.h"\n' % module for module in order if module in modules)
    guard = "QUAERENS_%s_H" % name.upper()
    head = comment("""INTERFACCIA DI %s.c: %s.

Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il libro lo presenta: i limiti e i tipi
con i loro commenti, e le dichiarazioni delle variabili e delle funzioni. Il significato di una variabile e il
contratto di una funzione sono nel commento sopra la loro definizione, in %s.c. Ciò che il modulo usa solo per
sé non è qui: là è static.

Warning: una funzione o una variabile aggiunta qui va aggiunta anche a engine_names.h.""" % (name, description, name))
    header_text = head + "#ifndef %s\n#define %s\n\n" % (guard, guard)
    if name == first:
        header_text += "".join(item.text + "\n" for item in items if item.kind == "include") + FOUNDATION_INTERFACES
    else:
        header_text += includes(uses_header)
    header_text += "\n" + "".join(header) + "\n\n#endif /* %s */\n" % guard

    head = comment("""MODULO %s: %s.

Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce incluse qui sotto; ciò che gli altri
usano di lui è in %s.h, e il resto è static.""" % (name, description, name))
    source_text = head + '#include "%s.h"\n' % name + includes(uses_source - {name}) + "\n" + body.lstrip("\n")
    return header_text, source_text, linked, uses_header


def program_text(engine, preface, items, tail):
    """main.c: the design comment and the index of the book, the table of the modules, and the last chapter."""
    order = [module for module, _, _, _ in engine.modules]
    uses = set()
    pieces = []
    for item in items:
        uses.update(home.module for home in engine.elsewhere(item, engine.expanded_refs(item)))
        pieces.append((item.floating + item.comment + item.text, False))
    table = ""
    for name, _, _, description in engine.modules[:-1]:
        lines = comment(description, 60)[3:-4].replace(" * ", "").split("\n")
        table += " *   %s\n" % name + "".join(" *       %s\n" % line for line in lines)
    text = preface
    text += ("/* I MODULI DEL MOTORE\n"
             " *\n"
             " * Il libro è diviso in moduli, ognuno un'unità di compilazione con la sua\n"
             " * interfaccia: NOME.c ha i capitoli, NOME.h ciò che gli altri moduli ne\n"
             " * usano. Un capitolo usa ancora ciò che i capitoli sopra di lui hanno\n"
             " * presentato, e lo riceve includendo l'interfaccia del modulo che lo\n"
             " * contiene. In ordine di lettura:\n"
             " *\n" + table +
             " *\n"
             " * Questo file è il programma a sé: l'ultimo capitolo, con main(). Vampire\n"
             " * non lo compila: usa i moduli attraverso Math/Engine.h. */\n")
    text += "".join('#include "%s.h"\n' % module for module in order if module in uses)
    return text + "\n" + join_source(pieces, tail).lstrip("\n")


def split(book, host, out):
    engine, preface = read_book(book)
    engine.mark_exported(file_mentions(host))
    os.makedirs(out, exist_ok=True)
    names = []
    for name, items, tail, description in engine.modules:
        if name == PROGRAM[0]:
            texts = {"main.c": program_text(engine, preface, items, tail)}
        else:
            header, source, linked, uses_header = module_texts(engine, name, items, tail, description)
            names += linked
            texts = {name + ".h": header, name + ".c": source}
            print("%-28s %4d declarations, %4d exported; its interface needs %s" % (
                name, len(items), sum(item.exported for item in items), " ".join(sorted(uses_header)) or "nothing"))
        for file_name, text in texts.items():
            with open(os.path.join(out, file_name), "w", encoding="utf-8") as target:
                target.write(reworded(file_name, text))
    with open(os.path.join(out, "engine_names.h"), "w", encoding="utf-8") as target:
        target.write(names_text(names))
    print("%d names at link time" % len(names))
    return engine


def names_text(names):
    head = comment("""I NOMI DEL MOTORE PER IL LINKER.

Una funzione o una variabile che un modulo offre agli altri ha un nome che il linker vede, e i nomi del libro
sono corti (fail, note, gcd): uno potrebbe essere anche il nome di una funzione di una libreria con cui il
programma è collegato, e il linker legherebbe in silenzio l'uno all'altra. Qui ogni nome offerto riceve, per il
linker, un prefisso; nei sorgenti resta quello del libro.

Va incluso dopo la libreria standard e prima di ogni dichiarazione del motore: lo fa engine_foundations.h, che
ogni modulo include per primo.

Warning: una riga per ogni funzione e variabile dichiarata nell'interfaccia di un modulo, in ordine alfabetico;
Math/tools/engine_modules.py check controlla che ci siano tutte e solo quelle.""")
    lines = "".join("#define %s %s%s\n" % (name, PREFIX, name) for name in sorted(set(names)))
    return head + "#ifndef QUAERENS_ENGINE_NAMES_H\n#define QUAERENS_ENGINE_NAMES_H\n\n" + lines + "\n#endif /* QUAERENS_ENGINE_NAMES_H */\n"


# ------------------------------------------------------------------------------
# The discipline of the modules
# ------------------------------------------------------------------------------

def check(directory, host):
    """The problems of the modules in a directory against the discipline a, b, c, d of the comment at the top."""
    def read(name):
        with open(os.path.join(directory, name), encoding="utf-8") as source:
            return source.read()

    def declarations(text, module):
        items = items_of(text, module, module)[0]
        for item in items:
            analyse(item)
        return items

    problems = []
    names = set(re.findall(r"^#define (\w+) %s\1$" % PREFIX, read("engine_names.h"), re.M))
    order = [name for name, _, _ in MODULES]
    headers, sources, includes = {}, {}, {}
    for name in order:
        text = read(name + ".h")
        guard = re.search(r"^#ifndef (\w+)\n#define \1\n", text, re.M)
        if not guard or not text.rstrip().endswith("#endif /* %s */" % guard.group(1)):
            problems.append("%s.h: no include guard around the whole file" % name)
            continue
        inside = text[guard.end():text.rstrip().rindex("#endif")]
        headers[name] = declarations(inside, name)
        includes[name] = re.findall(r'^#include "(\w+)\.h"', inside, re.M)
        text = read(name + ".c")
        sources[name] = declarations(text, name)
        first = re.search(r'^#include "([^"]+)"', text, re.M)
        if not first or first.group(1) != name + ".h":
            problems.append("%s.c: the first interface it includes is not its own" % name)
    if problems:
        return problems

    # Who mentions what: every module (its source and its interface), the program, and the host file.
    mentioned = {name: set() for name in order}
    expanded = set()                                # what the macros and the inline functions of the interfaces mention
    for name in order:
        for item in headers[name] + sources[name]:
            mentioned[name] |= item.refs
        for item in headers[name]:
            if item.kind in ("macro", "inline"):
                expanded |= item.refs
    outside = file_mentions(os.path.join(directory, "main.c")) | file_mentions(host)

    # a. What a module defines without "static" is declared in its interface and listed among the names.
    linked = set()
    for name in order:
        declared = {n for item in headers[name] if item.kind in ("prototype", "variable") for n in item.names}
        for item in sources[name]:
            if item.kind in ("function", "variable") and not item.static:
                for defined in item.names:
                    linked.add(defined)
                    if defined not in declared:
                        problems.append("%s.c defines %s without static, and %s.h does not declare it" % (name, defined, name))
                    if defined not in names:
                        problems.append("%s.c defines %s without static, and engine_names.h does not list it" % (name, defined))
        defined_here = {n for item in sources[name] if item.kind in ("function", "variable") and not item.static for n in item.names}
        for item in headers[name]:
            if item.kind in ("prototype", "variable") and not set(item.names) & defined_here:
                problems.append("%s.h declares %s, and %s.c does not define it" % (name, ", ".join(item.names), name))
    for extra in sorted(names - linked):
        problems.append("engine_names.h lists %s, which no module defines" % extra)

    # b. What an interface declares is used outside its module.
    for name in order:
        elsewhere = outside | expanded
        for other in order:
            if other != name:
                elsewhere |= mentioned[other]
        for item in headers[name]:
            if item.kind in ("prototype", "variable") and not set(item.names) & elsewhere:
                problems.append("%s.h declares %s, which nothing outside %s.c uses: it should be static"
                                % (name, ", ".join(item.names), name))

    # c. No interface includes one that includes it.
    def reaches(start, target, seen):
        for following in includes.get(start, ()):
            if following == target or (following not in seen and not seen.add(following) and reaches(following, target, seen)):
                return True
        return False

    for name in order:
        if reaches(name, name, set()):
            problems.append("%s.h includes, directly or not, an interface that includes it" % name)
    return problems


if __name__ == "__main__":
    if len(sys.argv) == 5 and sys.argv[1] == "split":
        split(sys.argv[2], sys.argv[3], sys.argv[4])
    elif len(sys.argv) == 4 and sys.argv[1] == "check":
        found = check(sys.argv[2], sys.argv[3])
        for problem in found:
            print(problem)
        print("the modules of the engine: %s" % ("%d problems" % len(found) if found else "in order"))
        sys.exit(1 if found else 0)
    else:
        sys.exit(__doc__)
