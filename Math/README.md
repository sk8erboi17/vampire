# Mathematics in Vampire

Vampire reads mathematical statements written in LaTeX. The ones that are
logic it proves or refutes with its own provers; the ones that are mathematics
proper (an induction, an inequality, a derivative, a matrix) go to the
algorithm made for each; and of every answer it says how far it was checked.

This is the Quaerens project absorbed into Vampire as a set of modules. It is
one program, and its two parts work on a statement together, each where it is
the better one: Vampire searches for proofs and for finite models; the
mathematical engine reads the statement and judges the models Vampire finds
in its own structure for models; the independent checker follows Vampire's
proofs inference by inference. Where sets of all the parts of a set come in,
and in mathematics proper, the engine goes first, and Vampire is asked when
the engine has no answer: for a proof from the laws of those sets, for a
proof from a supposed bijection given as two maps, for a refutation of the
checker's clauses when a statement quantifies over parts, and with its
arithmetic theories when a statement quantifies over numbers; what those
theories prove about integers it proves once more from the laws of the
integers alone, on the checker's clauses, so that the checker can follow it.
Neither decides against the other: an answer of one is always put to the
test of the other, or of the checker, and what nobody rechecked is labelled
as such.

```
vampire statements.tex                         every \item of the document, one after the other
vampire --input_syntax latex < formula.txt     one bare formula
vampire --math_document out.pdf statements.tex also the document: worked solutions, proofs, plots
vampire --math_certificates out.cert ...       also the certificates the checker accepted
certificate-checker out.cert                   recheck them, without Vampire
```

## What happens to a statement

```
LaTeX -> Parse/LaTeX: read, unfold, type (Math/LogicStatement)
           |
           +-- first-order logic over plain sets ------------> VAMPIRE LEADS
           |      Vampire: proof search and finite-model search, together
           |        model -> engine: loaded into its own structure for models,
           |                 recomputed (also as written), certified
           |        saturated, no finite model -> an interpretation over the
           |                 integers, the claim that it is a counterexample
           |                 proved from their laws, followed by the checker
           |        proof -> checker: Vampire's inferences as its steps (Proof/Replay);
           |                 failing that, the engine rebuilds a proof
           |
           +-- logic with sets of all parts / all maps ------> THE ENGINE LEADS
           |      engine: model search with the real sets, certifying proof
           |        no answer -> Vampire: proof from the laws the engine supplies
           |
           +-- logic with a quantifier over the parts of a set -> THE ENGINE LEADS
           |        no answer -> Vampire: refutation of the checker's clauses,
           |                     with the parts the engine proposes
           |
           +-- mathematics proper ------------------------------> THE ENGINE
           |        one integer variable -> the checker's complete count:
           |                     the certificate, or the answer
           |        no answer, quantifiers over numbers of one kind
           |                  -> Vampire's arithmetic: the statement, and its negation
           |        proved among integers, no number shows it
           |                  -> Vampire: refutation of the checker's clauses with
           |                     the laws of the integers, followed by the checker
           |
           +-- two sets supposed equipotent --------------------> THE ENGINE LEADS
           |        no answer -> Vampire: proof with the bijection as two maps
           |                     inverse to each other
           |
           +-- two sets to be proved equipotent ----------------> THE ENGINE LEADS
           |        no answer -> Vampire: refutation of the checker's clauses,
           |                     with the bijections the engine offers
           |
           v
   Proof/IndependentChecker judges every certificate
   verification status, document, certificates
```

The two parts work on a statement together, and who goes first depends on
what the statement is, by measurement (see "Measures").

- **First-order logic over plain sets** (elements, maps and relations of
  sets that are not given; quantifiers; equality). Vampire leads. The
  frontend unfolds the notation of the books into quantifiers and rechecks
  the unfolding on finite models; the statement is typed
  (`Math/LogicStatement`) and translated (`Math/LogicTranslator`); child
  processes load the units and from there on *are* Vampire on that problem,
  in whatever mode was asked for. A search for a finite counter-model
  (`--math_model_time`) runs together with the proof search, and the first
  answer that settles the statement ends the other. Then the engine takes
  what Vampire found:
  - a **model** is loaded into the engine's own structure for models
    (`qr_adopt_model`) and from there on is a model like the ones the
    engine finds: the statement is recomputed in it, also as it was written
    before the notation was unfolded, and the certificate is written;
  - a **proof** is rechecked by the independent checker, inference by
    inference. The checker follows a refutation that starts from clauses it
    builds itself from the statement, so Vampire refutes those very clauses
    once more (the engine hands them over, `qr_clauses_item`), and
    `Proof/Replay` writes every inference of that refutation as explicit
    steps of the checker: resolution, superposition, the splitting of
    AVATAR with its names, and the verdict of the SAT solver rebuilt as
    resolutions. The theorem is certified when the checker accepts the
    finished text. If Vampire's inferences cannot be followed, the engine,
    knowing that the statement is a theorem, rebuilds a proof of its own in
    a form the checker can recheck (`qr_certify_item`); if that fails too,
    the theorem stands on Vampire's proof alone and is reported as not
    verified;
  - a **refutation of a request for an example** ("there are a set and a
    map such that ...") is a theorem too, that the condition never holds,
    and is rechecked the same way: the certificate says "not ...".
  - a **saturation without a contradiction and without a finite model**
    ("an injective map of a set into itself is onto" holds in every finite
    set) may have an infinite counter-model. A few interpretations over the
    integers are tried (every set the integers from 0 on, every symbol one
    of a short list by its kind: for a map x + 1, then x - 1 except at 0,
    and so on), and for each the checker writes by itself the claim "the
    symbols are maps of those sets, and the statement is false there", a
    statement about integers (certificate `infinite`, 20g of `checker.c`).
    Vampire's arithmetic theories try the claim and its negation at once,
    and give values for the claim's outer "there is" (where f takes the
    same value twice); a claim whose negation they prove is dropped. Then
    Vampire proves the claim once more from the laws of the integers, as
    for numbers (below), and the checker follows it: the counterexample is
    verified. For a request for an example the same interpretation is the
    example.
- **Logic with sets of all the parts or of all the maps of a set, or with
  written numbers.** The engine leads: a model must have every part and
  every map, which the engine builds and a first-order model builder does
  not promise, and a proof must choose the parts it needs. When the engine
  has no answer Vampire is asked for a proof, from the laws of those sets
  that the engine supplies as axioms ("two parts with the same elements are
  the same part", "the elements that satisfy this condition are a part").
  What Vampire proves from the laws is a theorem, rechecked as above; that
  it finds no proof says nothing, and is never read as a refutation.
- **Logic with a quantifier over the parts of a set** ("for every part X of
  S ..."). It has no first-order form of its own, and the engine leads. When
  the engine has no answer, Vampire looks for a refutation of the clauses
  of the independent checker, which are first-order: there a part chosen by
  the negated claim is a predicate, and "for every part" is used through
  instances. Vampire cannot choose a part, so the engine hands the clauses
  over with the instances that can be proposed without a search: the empty
  part, the whole set, and the parts that the ground literals of the
  statement suggest (for "f(y) = y for every y" with an induction principle
  among the hypotheses, the part of the x with f(x) = x). What Vampire
  refutes there is a certificate at once.
- **Two sets supposed equipotent** ("if S and T are equipotent and ...").
  The engine leads: in a finite model equipotent sets are sets of the same
  size, and its proofs use the bijection through witnesses the checker
  knows. When it has no answer, Vampire is asked for a proof of the
  statement with each supposed bijection given as two maps, one each way,
  that undo each other; `Math/LogicStatement.cpp` shows that the statement
  means the same. This holds only for an equipotence that is a hypothesis.
  The proof is then rechecked like any other, on the checker's clauses:
  there an equipotence is a proposition that implies that two maps undo
  each other, so that a refutation can use it (11m-e in
  `Math/quaerens/checker.c`, with the argument that no model is lost).
- **Two sets to be proved equipotent** ("if f and g undo each other, S and
  T are equipotent"; "if f is injective and surjective, ..."). To prove it
  is to exhibit a bijection, and a first-order prover does not invent one.
  But the bijection is nearly always written in the statement: a declared
  map, the composite of two, the inverse that "f is surjective" promises
  (the Skolem function of that hypothesis), the bijection of another
  equipotence among the hypotheses. The engine goes first; where it has no
  answer it hands the checker's clauses to Vampire with every pair of such
  maps, up to two composed, that goes from one set to the other and back
  (`sp_static_bijections()`). Each pair is a line `biject` of the
  certificate, which assumes nothing: it adds "if these two maps undo each
  other between the two sets, the sets are equipotent" (11m-f in
  `checker.c`), and it is the refutation that has to show that they do.
  Vampire finds it, the checker follows it. What this does not reach: a
  bijection defined by cases (two sets of two elements), or one that
  exists without being written (Cantor-Bernstein).
- **Mathematics proper.** The statement goes to its algorithm in the engine:
  induction on sums and products, sign tables for equations and inequalities
  (also solving them), limits, derivatives, integrals, matrices and linear
  systems, functions of several variables, identities with indices. One
  kind of statement has a faithful translation for Vampire, and is given to
  it when the engine has no answer: **quantifiers over numbers**, when
  every variable ranges over numbers of one kind (all integers, or all
  rationals, or all reals) and the expressions are sums, products, written
  powers, comparisons and, among integers, divisibility. The engine hands
  the statement over as it read it (`qr_numbers_item`),
  `Math/NumberStatement` writes it as a TPTP problem over `$int`, `$rat` or
  `$real`, which Vampire's own parser reads, and two searches run together,
  for a proof of the statement and for a proof of its negation. Where
  numbers settle the statement (a "for all" refuted by a counterexample, a
  "there is" proved by an example, with the values of the quantifiers they
  go through), Vampire is asked for the numbers too, by question
  answering, and the checker recomputes the statement on them
  ("certificate numbers", chapter 20 of `checker.c`): the answer is then
  verified. A "for all" that is true, and a "there is" that is false, need
  a proof for every value. The checker gives one by itself in one case:
  **one integer variable** with nothing quantified inside, once every other
  variable has a value. There every comparison is a polynomial in that
  variable, constant in sign beyond the bound of its roots, and every
  divisibility by a number repeats with its period: trying the integers up
  to that bound and one period more is a finite and complete count (20e in
  `checker.c`). Three uses. A statement in one integer variable needs
  nobody: the checker settles it, as the certificate of a verdict of the
  engine that had none, or as the answer when neither the engine nor
  Vampire has one (reported as decided by `checker`). And a refutation
  that numbers alone do not show ("for every m there is a positive x
  with ..." fails at m = 0 because no x works) is verified with the number
  Vampire gives and the count for the variable that is left; there Vampire
  is asked for the number in a second search, and the checker is given each
  tuple that its answer offers. With several variables left no count is
  complete, and among integers there is a proof instead: **from the laws of
  the integers** (chapter 20f of `checker.c`, certificate `arithmetic`).
  The checker translates the statement by itself into a statement of logic
  over one set Z, in which sum, opposite, product and the order are symbols
  it knows only by a fixed table of laws that are true among the integers
  (a commutative ring with unit and no divisors of zero, a total order
  compatible with sums and with products of positives, nothing between x
  and x + 1), adds the laws, and follows a refutation by saturation as for
  logic; the one step that computes is `compute`, a clause without
  variables that it accepts if it is true among the integers ("0 and 2 are
  different", "1 + 1 = 2"). Vampire's arithmetic proves the statement;
  Vampire then refutes the checker's clauses with no theory, with the
  options whose inferences can be followed (first with literal selection 1,
  the saturation algorithm discount and clauses chosen mostly by weight:
  among the laws of a ring the default search gets lost), and `Proof/Replay`
  writes the steps. The clauses are asked of the checker itself
  (`proof_arithmetic_clauses()` in `Proof/IndependentChecker.h`, which says
  why that is no weakness): for logic the engine mirrors the checker to
  know them, and a mirror can only agree with it. There is no induction
  among the laws, and none for rationals and reals: what needs them is
  found, not verified. The same holds for a **verdict of the engine
  without a certificate** on such a statement ("proved with the rules for
  quantifiers", "trying all the remainders"): Vampire's arithmetic is asked
  too (`--math_confirm_engine`), and if what it proves is the engine's
  verdict and the checker certifies it, with Vampire's numbers or with a
  proof from the laws of the integers, that is the verdict's certificate.
  If Vampire proves the opposite, one of the two is wrong: the statement
  is unsolved, with a warning. That has not happened in any test.
  Variables of two kinds, exponents that are
  letters, divisions by an expression, functions and roots are not handed
  over: they would need a choice the translation must not make.
- **Not a statement.** An ambiguous or invalid writing is refused with the
  reason. Nothing is read one way when it could be read two.

The sets of a statement may be empty; Vampire's sorts cannot. The translation
keeps the difference with one proposition per sort, and the comment at the top
of `Math/LogicTranslator.hpp` proves that the translated problem means the
same.

## How far an answer was checked

Every statement gets a verification status (`Math/Verification.hpp`), printed
as `% Verification status: ... [Code]` and, for scripts, `% Result N: Code (who)`,
where who is `engine`, `vampire`, or `checker` for a statement in one
integer variable that the checker settled by its own count.

| Code | Meaning |
|---|---|
| `TheoremCertified` | proved, and the independent checker accepted the certificate |
| `TheoremUnverified` | a proof was found; the checker did not confirm it |
| `ResultValidated` | a result was computed (solutions, a derivative), certificate accepted |
| `ResultUnverified` | a result was computed and reread by the engine only |
| `CounterexampleVerified` | false: the checker recomputed the counterexample |
| `CounterexampleUnverified` | refuted, without a counterexample the checker could confirm |
| `RefutationCertified` | a request for an example refuted: the checker followed the proof that there is none |
| `Unsolved` | neither proved nor refuted within the limits |
| `Unsupported` | outside the fragment that is read |

Rules that are not negotiable:

- **A proof printed by Vampire is not a certified proof.** A theorem found
  by Vampire is `TheoremCertified` only when the independent checker has
  accepted a certificate: Vampire's own inferences written as the checker's
  steps, or a proof rebuilt by the engine. Otherwise it is
  `TheoremUnverified`. What rebuilds the steps (`Proof/Replay`) is on the
  side of whoever claims the proof and is not trusted: a step rebuilt
  wrongly is a certificate rejected.
- **The checker takes nobody's word for an unsatisfiability.** Where
  Vampire's SAT solver says that the clauses of names of a splitting cannot
  all hold, the certificate has the resolutions that show it.
- **A finite model found by Vampire is a counterexample only after the
  engine recomputed the statement in it and the checker accepted the
  certificate**, the checker being `Proof/IndependentChecker`, compiled apart
  from the engine and from Vampire. A model that is not confirmed is
  reported as `Unsolved`, with the reason.
- **"Not a theorem" without a model is not a verified refutation.** When
  saturation ends without a contradiction there may be only infinite
  counter-models ("an injective map of a set into itself is onto"): the status
  is `CounterexampleUnverified`, unless an infinite counter-model over the
  integers is certified (20g): the checker writes by itself what it means
  for the interpretation to be a counterexample, a statement about
  integers, and follows its proof from the laws of the integers.
- **With sets of parts or of maps, no proof from Vampire means nothing.**
  It reasons from finitely many laws about sets that have all their parts.
- **If Vampire has a proof and the engine a certified counterexample**, one
  of them is wrong: neither is reported, the statement is `Unsolved`, and
  the output says `CONTRADICTION`. None has occurred in any test.
- **No numerical test makes a theorem.** The engine never reports one on such
  grounds, and nothing in this module upgrades a status.
- **A proof by Vampire's arithmetic theories is never certified as it is.**
  If the statement is one that values settle and Vampire gives them, the
  checker recomputes the statement on them: `CounterexampleVerified`, or
  `TheoremCertified` for an example. The numbers are Vampire's; that they
  do what is claimed is the checker's count, and nothing else is believed.
  Among integers Vampire proves it once more from the laws of the integers
  alone, on the clauses the checker makes, and the checker follows that
  proof (20f): `TheoremCertified`, or `CounterexampleVerified` for a
  negation. The laws are the checker's, fixed, each true among the
  integers; Vampire's theories are not in that proof. Otherwise the answer
  is `TheoremUnverified`, or `CounterexampleUnverified` when what was
  proved is the negation, and the output says which. That is where the
  engine's own proofs of such statements stand too ("proved with the rules
  for quantifiers; no certificate"), unless the checker's count settles
  them (one integer variable).

## The account of a proof

`Humanizer/ProofNarrator` tells a refutation found by Vampire as a numbered
list: each step shows the formula, says in plain words what the rule does, and
cites the steps it used. Every step is one inference of Vampire's proof;
nothing is merged, guessed or added, and a rule without a description is cited
by its name. English or Italian (`--math_language`). The account goes into the
document, or to the output when no document is written.

The worked solutions of the engine (equations and inequalities step by step,
derivatives rule by rule, inductions) are in the document as before, in
English.

## Options

| Option | Default | |
|---|---|---|
| `--input_syntax latex` | `auto` | `auto` picks LaTeX for a file ending in `.tex` |
| `--math_document FILE` (`-mdoc`) | | the LaTeX document; `.pdf` also compiles it |
| `--math_certificates FILE` (`-mcert`) | | the accepted certificates |
| `--math_explanations on/off` (`-mexp`) | `on` | worked solutions and accounts of proofs |
| `--math_language en/it` (`-mlang`) | `en` | accounts of Vampire's proofs, verification statuses |
| `--math_model_time T` (`-mmt`) | `2` | seconds of finite-model search beside the proof search; `0` skips it |
| `--math_recheck_time T` (`-mrt`) | `5` | seconds Vampire may take to refute the checker's clauses again, for the recheck of a proof it has found; `0` skips the recheck |
| `--math_numbers_time T` (`-mnt`) | `5` | seconds Vampire's arithmetic theories may work on a statement about numbers that the engine could not decide; `0` does not ask them |
| `--math_confirm_engine on/off` (`-mce`) | `on` | also put to Vampire's arithmetic a statement about numbers that the engine proved or refuted without a certificate, so that the checker can certify the verdict; a proof of the opposite leaves it unsolved, with a warning |

There is no option to have the engine decide a statement that Vampire can be
given: that would be a second prover for the same statements.

Every other option of Vampire applies to the statements of logic as it does to
a TPTP problem: `-t`, `--mode casc`, `-sa fmb`, `--proof off`. `--mode output`
prints a statement as TPTP.

## Where things are

| | |
|---|---|
| `Parse/LaTeX` | the frontend as the rest of Vampire sees it: the statements of an input, each read and classified |
| `Math/Engine.h`, `Math/Engine.c` | the C interface of the mathematical engine, and its implementation over the interfaces of the engine's modules |
| `Math/quaerens/` | the engine: one module per domain, `NAME.c` with its chapters and `NAME.h` with what the other modules use of it (see below); `engine_names.h`, the names the modules export, prefixed for the linker; `main.c`, the design of the engine, the index of its chapters and the program on its own (`quaerens`); `plot.c` (plots), `checker.c` (checker) |
| `Math/LogicStatement` | a statement of logic as a typed tree: sorts, symbols with signatures, formulas |
| `Math/LogicTranslator` | that tree into Vampire units; possibly empty sorts |
| `Math/NumberStatement` | a statement with quantifiers over numbers, as the engine hands it over, into a TPTP problem for Vampire's arithmetic; the form of the problem whose proof comes with numbers, and the certificate written with them |
| `Math/LogicProblem` | the statement of the running process: what Vampire found (a refutation, a model), written down as data |
| `Math/Driver` | the run over the statements of an input; the searches of Vampire in child processes; models and proofs back to the engine |
| `Math/Verification.hpp` | the statuses |
| `Math/Names.hpp` | names of symbols back into LaTeX |
| `Proof/IndependentChecker` | the checker of certificates, a module compiled once: the engine uses it for its own proofs and the driver for what Vampire finds, both through its two functions; also the program `certificate-checker` |
| `Math/Plot` | the plots, a module compiled apart from the engine: the interface of `plot.c` |
| `Math/EngineModules.h` | what the engine sees of the checker: its entry point and its three answers |
| `Proof/Replay` | a refutation by Vampire, inference by inference, into the explicit steps the checker follows |
| `Humanizer/ProofNarrator` | the account of a refutation, in English and Italian |
| `Math/tools/as_quaerens.py` | presents this executable to the fuzz scripts of the Quaerens repository |
| `Math/tools/engine_modules.py` | made the modules and their interfaces from the engine's single translation unit, and checks that they stay modules |
| `Math/tools/fuzz_numbers.py` | differential fuzz of the statements on integers that reach Vampire's arithmetic, against an oracle that counts |
| `Math/tools/fuzz_equipotence.py` | differential fuzz of the statements that suppose two sets equipotent, against an oracle that compares numbers of elements |
| `Math/tools/fuzz_bijections.py` | differential fuzz of the statements that conclude that two sets are equipotent from what is known of the maps between them, against an oracle that looks for a finite counterexample |
| `Math/tools/fuzz_arithmetic_laws.py` | adversarial fuzz of the proofs from the laws of the integers: the checker's clauses of the claim an oracle finds false, given to Vampire, must not be refuted, and a false fact offered as `compute` must be refused |

The engine by domain. In Quaerens the engine is one file of 52 thousand
lines, a book of numbered chapters, nearly everything in it static, read by
the compiler as one translation unit. Here it is twenty modules, each
compiled on its own. A module is `NAME.c`, with its chapters as the book has
them, and `NAME.h`, its interface: what the other modules use of it. The rest
is static and no other module can reach it.

| Module | Chapters | | Functions and variables: exported of all |
|---|---|---|---|
| `engine_foundations` | 1-7 | limits, errors and memory, exact numbers, monomials, polynomials, atoms, fractions of polynomials | 94 of 99 |
| `parser` | 8, 9, 14, 17, 21, 31, 34, 37, 39 | LaTeX into trees: expressions, statements on sets, statements with quantifiers, matrices, indices | 134 of 503 |
| `engine_evaluation` | 10-12 | the known sequences, an expression tree to a fraction, tests of vanishing | 53 of 95 |
| `engine_induction` | 13 | induction on sums and products; the verdict and its proof | 45 of 103 |
| `engine_sets` | 15-16 | relations between sets by regions | 2 of 65 |
| `engine_intervals` | 24 | real numbers as intervals with a guaranteed error | 23 of 27 |
| `engine_quantifiers` | 18-18.7 | quantifiers over numbers: the rules of proof | 41 of 161 |
| `engine_sign_tables` | 18.8-18.19 | sign tables, solutions, plots, one parameter | 43 of 297 |
| `engine_explanation` | 40 | worked solutions | 8 of 53 |
| `engine_quantifiers_verdict` | 19 | quantifiers: independent verification and verdict | 3 of 60 |
| `engine_sequences` | 25-26 | induction on an inequality, sequences by recurrence | 7 of 29 |
| `engine_derivatives` | 27 | derivatives and the study of a function | 19 of 54 |
| `engine_logic` | 28 | arbitrary sets: finite models, instances, saturation, the tasks done for Vampire | 7 of 386 |
| `engine_limits` | 29 | limits | 3 of 102 |
| `engine_integrals` | 30 | integrals | 3 of 113 |
| `engine_linear_algebra` | 32-33 | matrices, determinants, linear systems | 6 of 154 |
| `engine_multivariable` | 35-36 | functions of several variables | 2 of 43 |
| `engine_indices` | 38 | identities with indices | 2 of 36 |
| `engine_statement` | 20 | which chapter reads a statement; the verdict in one line | 3 of 16 |
| `output` | 41, 22 | the document | 5 of 20 |

In all, 503 of the 2416 functions and variables of the engine are in an
interface, and 280 of its 501 limits and types; the other 1913 functions and
variables are private to their module. `Math/Engine.c` is one more user of
those interfaces, and `Math/quaerens/main.c`, with the last chapter of the
book, is the engine as a program on its own, built from the same modules.

Nobody chose the interfaces by hand: they are what is used.
`Math/tools/engine_modules.py` read every declaration at file scope of the
single translation unit and every name each one mentions, without the names
that are its own (parameters, local variables, members). What a declaration
of another module mentions is exported, with what its exported form needs
(the types of a signature, the body of a macro). An exported limit or type
moved to the header with its comment; an exported function or variable kept
its definition and its comment where the book explains it, lost `static`,
and is declared in the header. Everything else is where it was, byte for
byte, so the chapters still read as in Quaerens. The modules are the source
from now on, and the same tool checks that they stay modules
(`python3 -I Math/tools/engine_modules.py check Math/quaerens Math/Engine.c`):
whatever a module defines without `static` is declared in its interface;
whatever an interface declares is used outside its module, or it should be
static again; no interface includes one that includes it. That each module
compiles alone is the build itself.

Two things follow from compiling apart. A function that was static and is
now called from another module has a name the linker sees, and the engine's
names are short (`fail`, `note`, `gcd`): `engine_names.h` gives each of the
518 a prefix at link time (`qre_`), so that none can be mistaken for a
function of a library; the sources keep the names of the book. And calls
across modules are no longer inlined: on the corpus the engine takes 92.2 s
of processor time as modules and 93.2 s as one unit, so nothing was lost.

To bring in a later `main.c` from the Quaerens repository, either make the
same change in the module that holds the chapter, or run the tool's `split`
again on the three files of the book (`main.c`, `parser.c`, `output.c`):
it writes the modules anew, so what was changed only here has to be in
that book first.

Vampire's own files are touched in a handful of places, each a few lines and
each inert unless the input is LaTeX: the options (`Shell/Options`), the
loading of units built by a frontend (`UIHelper::loadUnits`), two hooks where
results are reported (`Shell/UIHelper.cpp`), two where the finite model
builder has, or could have, a model (`FMB/FiniteModelBuilder.cpp`), a size
accessor (`FMB/FiniteModelMultiSorted.hpp`), a way to name an input unit
(`Parse::TPTP::assignAxiomName`), and `main()`.

The engine is touched in one place, its procedure for logic
(`prove_abstract()` in `Math/quaerens/main.c`), which no longer only decides:
it does the task it is asked for. It hands a statement over, read, unfolded
and rechecked, with the laws of its sets of parts and of maps; it adopts a
model found by Vampire; it hands over the clauses from which the checker
starts a proof by saturation, with the instances of the formulas on parts;
it writes a certifiable proof of a statement Vampire proved; or it decides,
as it always did. A second, smaller place is at the end of the file, where
statements are sent to their chapters: a statement with quantifiers over
numbers can be handed over instead of decided (`numbers_handed_over()`).
A third is two lines of `engine_foundations.c`: the engine includes
`checker.c` and `plot.c` only when it is built alone; here it is given
their interfaces instead. The other four files, the checker among them, are
byte for byte those of Quaerens. Vampire's proofs are written in the steps
the checker already had, and among integers in one more, compute. Six things were added to the checker, in Quaerens
too, each with its justification and its tests: a rule to use an
equipotence among the clauses of a proof by saturation (11m-e in
`checker.c`) and one to prove it from a bijection that is written down
(11m-f); a kind of certificate for a statement about numbers that a few
numbers settle (chapter 20), in it the complete count that settles a
quantifier over one integer (20e), the proof of a statement about
integers from their laws (20f), with `compute`, its one step that
computes, and the clausification without domain predicates that one set
which is the whole domain allows (`whole` in `ck_r`), and the infinite
counterexample over the integers (20g), whose claim is checked as 20f.

## Migration: what is where, and what is not done

| Capability of Quaerens | In Vampire | State |
|---|---|---|
| Reading LaTeX: expressions, sets, quantifiers, solution sets, `\item` | `Parse/LaTeX` over `parser.c` | in use, in C behind `Math/Engine.h` |
| Unfolding the notation of the books, rechecked on finite models | frontend | in use, before a statement is handed to Vampire |
| Logic over plain sets: the search for a proof and for a finite model | **Vampire** (saturation, AVATAR, finite model builder) | Vampire leads; the engine's model finder is not used here |
| Logic over plain sets: making the answer checkable | checker, engine | the checker follows Vampire's inferences one by one (`Proof/Replay`); the engine's structure for models judges Vampire's models; its certifying provers rebuild a proof only where the inferences cannot be followed; an infinite counter-model over the integers is certified by a proof from their laws (20g) |
| Logic with sets of *all* parts or *all* maps, written numbers | engine first, then **Vampire** | the engine leads (measured); Vampire proves from the engine's laws what the engine cannot |
| Logic with a quantifier over the parts of a set | engine first, then **Vampire** | Vampire refutes the checker's clauses, with the parts the engine proposes |
| Two sets supposed equipotent | engine first, then **Vampire** | the engine leads; Vampire proves what the engine cannot, with the bijection as two maps inverse to each other, and the checker follows the proof |
| A bijection between two sets, to be proved | engine first, then **Vampire** | the engine's search for witnesses leads; where it has no answer Vampire refutes the checker's clauses with the pairs of maps the engine offers as a bijection and its inverse, and the checker follows |
| Relations between parts by regions (complete decision) | engine | in use |
| Induction: sums, products, recurrences, inequalities | engine | in use |
| Sign tables: equations, inequalities, solving, parameters, congruences | engine | in use |
| Quantifiers over integers, rationals, reals | engine first, then the checker's count and **Vampire** | the engine's rules and sign tables lead; a statement in one integer variable is settled by the checker's complete count (the certificate of the engine's verdict, or the answer); what is left goes to Vampire's arithmetic theories, when every variable is of one kind; a counterexample or an example found there is recomputed by the checker, with the count for one integer variable that numbers leave; a proof about integers that no number shows is found again by Vampire from the laws of the integers, on the checker's clauses, and the checker follows it |
| Limits, derivatives, integrals | engine | in use |
| Matrices, determinants, linear systems, discussion by a parameter | engine | in use |
| Partial derivatives, gradients, Hessians, critical points | engine | in use |
| Identities with indices, declared metrics | engine | in use |
| Worked solutions (step by step) | engine, into the document | in use, English only |
| Account of a proof | `Humanizer/ProofNarrator`, for Vampire's refutations | new, English and Italian |
| Document, plots | `output.c`, `plot.c` through `Math/Engine.h` | in use; Vampire's answers are added to the same document |
| Independent checker | `Proof/IndependentChecker`, `certificate-checker` | in use; also judges Vampire's finite models |

Not done, and not claimed:

- **The engine is reentrant across threads, not within one.** Every
  variable of static duration of the modules, of the checker and of the
  plots, those inside functions too, is `_Thread_local`: each thread has an
  engine of its own, and several decide statements at once (`quaerens
  --threads N`). The two arenas, the engine's and the checker's, are memory
  taken the first time a thread needs them, being too large to be copied
  into every thread. That nothing is left shared is shown by the object
  files (with all the state thread-local, the sections `__data`, `__bss`
  and common of the modules hold no symbol, only constants) and by
  ThreadSanitizer. Within one thread the engine is what it was: what it
  keeps of its last verdict, for the document, the next call erases. The
  state was not made a context passed to the 2400 functions: nothing in the
  program needs two engines in one thread, and the threads have what they
  need. It costs: on the corpus, single-threaded, 95 s of processor time
  instead of 89 s, the price of reaching a thread's variables on this
  system.
- **The typed C++ form exists for statements of logic only.** Mathematical
  expressions are typed trees inside the engine and are not visible to C++.
- **Not every inference of Vampire can be followed.** The run whose
  refutation is rechecked has splitting, but not the parts of Vampire whose
  inferences are not instances of the checker's steps: unit-resulting
  resolution, global subsumption, the eliminations of definitions,
  congruence closure inside the SAT solver. A name of AVATAR that two
  splittings meet written with an equation the two ways round cannot be
  followed either (the checker compares literal by literal, and no step
  turns an equation round). Where the recheck fails the engine rebuilds
  the proof, or the theorem is reported as not verified.
- **"Not a theorem" by saturation is verified only with a counter-model
  over the integers from a short list.** Every set is the integers from 0
  on, every symbol one of a few expressions or conditions; a counter-model
  that needs elements of another kind (the monoid with an element that has
  two right inverses, whose elements are maps of the naturals) is not
  found, and then the refutation is Vampire's word alone.
- **No reasoning inside one proof across the two.** They pass statements,
  models and proofs to each other; Vampire cannot ask the engine for a
  computation in the middle of a proof.
- **Vampire's arithmetic gets only statements about numbers of one kind**,
  with polynomial expressions. A statement that mixes integers and
  rationals, or has a declared map, an exponent that is a letter, a
  function or a root, stays with the engine. What is proved about numbers
  is verified when numbers settle it, when one integer variable is left
  for the checker's count, or, among integers, when Vampire proves it again
  from the laws of the integers on the checker's clauses. Not otherwise: a
  proof that needs induction (the laws do not have it), a statement about
  rationals or reals (the checker has no laws for them), or one that
  Vampire does not prove from the laws within the time of a recheck, is
  found, not verified. The engine's own proofs of such statements are not
  handed to Vampire for that: only what Vampire's theories proved is.
- **A bijection is proved only if it can be written.** Vampire proves that
  two sets are equipotent from the pairs of maps the engine offers: maps of
  the statement, Skolem functions, the maps of other equipotences, up to
  two composed. A bijection defined by cases, or one that exists without
  being written, is not found. Two writings of the same equipotence are not
  recognised as one, and an equipotence with a product of sets is not
  handed over.
- **On the parts of a set Vampire only proves.** It works with the parts
  the engine proposes; that it finds no refutation says nothing.
- **The engine's worked solutions are in English only**, and the engine's
  one-line verdicts (`% Engine verdict:`) are in Italian.
- **The engine's work budgets** (model search, verification, stack) are not
  options of Vampire: the defaults apply.
- **Interactive mode** does not read LaTeX.

## Tests

- `UnitTests/tProofReplay.cpp` (ctest `ProofReplay`): inferences rebuilt as
  steps of the checker (a resolution with an equation written the other
  way round, a splitting with its names, the verdict of the SAT solver as
  resolutions, a ground literal named by resolution, a second attempt when
  a name was given the other way round); what is not an inference, a
  splitting with other names and a satisfiable set of clauses of names are
  not rebuilt; a rebuilt refutation is accepted by the checker and rejected
  once its statement is denied or its last step removed; a refuted request
  for an example is certified as the negation; a statement on the parts of
  a set is handed over with the parts to try. A superposition at a place after a
  variable that the step instantiates with a term is rebuilt with the place
  the checker counts, in the instance (it was not rebuilt before: the
  place pointed elsewhere).
- `UnitTests/tMathNumbers.cpp` also: a statement that numbers settle asked
  with its quantifiers in front; none for a statement that needs a proof
  for every value, or under an "if and only if"; the certificate written
  with Vampire's numbers accepted by the checker, and not with other
  numbers or for the opposite claim; an answer of Vampire is a witness
  only if it is a number. (The checker's chapter is tested in the Quaerens
  repository, `tests/checker/test_number_witnesses.c`, against an oracle.)
- `UnitTests/tMathNumbers.cpp` also: the beginning of a certificate from the
  laws of the integers, the clauses the checker gives for it (with the
  numerals of the translation) and the facts about the numerals, which the
  checker accepts and `Proof::Replay` reads; a false fact refused, and no
  beginning among rationals. (Chapter 20f is tested in the Quaerens
  repository, `tests/checker/test_arithmetic_laws.c`: a certificate written
  by Vampire accepted, and refused with its statement denied, with a number
  changed, without its last step, with a false fact, for the rationals;
  `compute` against an oracle that computes; the laws true on a window of
  integers; the translation of random statements evaluated among the
  integers, against an oracle that counts.)
- `UnitTests/tMathNumbers.cpp` also: the claim of an infinite
  interpretation (x + 1 on the integers from 0 on, for "an injective map of
  S into itself is onto"), read as the engine's statements are, its outer
  "there is" asked of Vampire, a witness taken where it counts as a "there
  is" and refused for the closure, a definition with a letter that is not
  an argument refused. (Chapter 20g is tested in the Quaerens repository,
  `tests/checker/test_infinite_models.c`: two certificates written by
  Vampire, accepted, and refused with another interpretation, with one that
  maps out of its set, with the statement denied, without the last step,
  with a wrong witness; the rules of the lines; and the claim of 3000
  random statements and interpretations evaluated on a window of integers
  against an oracle that applies the interpretation itself, with and
  without a witness.)
- `UnitTests/tMathNumbers.cpp` (ctest `MathNumbers`): what the engine hands
  over of a statement on numbers (the sets with their bounds and removed
  points, divisibility, the three sorts) and the TPTP problem written from
  it; what cannot be said exactly is not handed over (variables of two
  kinds, an exponent that is a letter, a division by an expression or among
  integers, functions, roots, declared maps, requests for solutions); a
  text that is not what the engine hands over is refused.
- `UnitTests/tProofReplay.cpp` also: an equipotence handed over as a
  proposition and two maps; a refutation that uses one accepted by the
  checker, and not accepted for the statement without the hypothesis, with
  the hypothesis denied or with a false claim; an equipotence never proved
  by the rule alone; an equipotence to prove handed over with the
  bijections to try, which prove nothing without a refutation. (The two
  rules are tested in the Quaerens repository,
  `tests/checker/test_equipotence_clauses.c` and
  `tests/checker/test_equipotence_proved.c`, each against a finite oracle.)
- `UnitTests/tMathLogic.cpp` also: an equipotence that is a hypothesis read
  as two maps inverse to each other, and refused anywhere else (to be
  proved, under a negation, in an "or", under a quantifier, with a product
  of sets, in a request for an example).
- `UnitTests/tMathLogic.cpp` (ctest `MathLogic`): the typed reading, the
  translation (plain sets, sets of parts and of maps, written numbers), the
  checker on correct and altered counterexamples, the engine adopting and
  refusing models found elsewhere, the engine rebuilding a proof and
  refusing to rebuild one of a false statement, the engine on false,
  ill-defined and ambiguous statements.
- `checks/latex-sanity build/vampire`: six documents in `checks/latex/`
  (logic, sets of parts, numbers, mathematics, false statements, invalid
  writings)
  with the expected result of every statement and of who reached it; no
  false statement is a theorem, among them one on the parts of a set that
  holds in every finite set; a theorem is certified only when the checker
  accepted a certificate, with and without the recheck of Vampire's
  inferences; certificates are accepted by `certificate-checker` and
  rejected once altered, and every rechecked refutation is rejected once
  its last step is removed; TPTP input is untouched.
- `python3 -I Math/tools/engine_modules.py check Math/quaerens Math/Engine.c`:
  the modules of the engine keep their discipline (what is exported is
  declared, named for the linker and used elsewhere; no cycle of
  interfaces).
- `quaerens --threads 4` on every document of the corpus: the verdict
  lines of all the 309 documents those of Quaerens, word for word; and
  under ThreadSanitizer, with four threads, on 77 documents of every
  domain, no report and the same lines.
- `quaerens`, the engine as a program on its own, built from the same
  modules: on the corpus it prints, line by line, what standalone Quaerens
  prints.
- Fuzz, outside the checks (Python 3, standard library only): the scripts
  of the Quaerens repository run against this executable through
  `Math/tools/as_quaerens.py`, each with an oracle of its own; and
  `Math/tools/fuzz_numbers.py`, for the statements on integers that go to
  Vampire's arithmetic: every quantified variable is confined to a few
  values by the statement itself, and the oracle tries them all; and
  `Math/tools/fuzz_equipotence.py`, for the statements that suppose two
  sets equipotent; and `Math/tools/fuzz_bijections.py`, for the statements
  that conclude that two sets are equipotent from what is known of the maps
  between them, against an oracle that looks for a counterexample among
  the interpretations with at most three elements in each set. And
  `Math/tools/fuzz_arithmetic_laws.py`, the adversary of the proofs from
  the laws of the integers: for statements whose truth an oracle counts,
  the checker's clauses of the false claim go to Vampire, which must not
  refute them, and a false fact offered as `compute` must be refused (it
  also needs a C compiler, for the small program that asks the checker for
  its clauses). A line `BUG` is a false proof or a false refutation.
- `checks/latex-sanity` also: statement 1 of numbers.tex, which the engine
  proves without a certificate, certified by the confirmation, and not
  with `--math_confirm_engine off`; no proof of the opposite of the engine.
- `checks/sanity` and the unit tests of Vampire are unchanged and must pass
  as before.

## Measures

All on the corpus of the engine: 155 documents, 6506 statements. 6247 are
mathematics proper, or logic that the engine decides or keeps; 259 get their
answer through Vampire.

**Who goes first**, decided by what each does alone:

| Kind of statement | Vampire | The engine | Goes first |
|---|---|---|---|
| First-order logic over plain sets (245 statements) | decides 244 | decides 229 | Vampire |
| With sets of all parts or all maps (19 theorems of `parts_and_maps.tex`) | proves 16, from the engine's laws | proves 19 | the engine |

**What working together gives**, on those 259 statements:

| | The engine alone | Together |
|---|---|---|
| Theorems certified | 141 | 147 |
| Counterexamples verified | 88 | 103 |
| Requests for an example refuted, certified | 0 | 7 |
| Theorems found, not verified | 0 | 0 |
| Refutations found, not verified | 0 | 1 |
| No answer, or no method | 30 | 1 |

Every certified answer of the engine is still certified, by the same checker;
Vampire adds answers the engine did not have, and they are labelled for what
they are. No statement is answered one way by one and the other way by the
other. Among the statements the engine decides alone, 28 verdicts about
integers that had no certificate now have one: each has one integer
variable, and the checker's complete count says what the engine said. The
count never said the opposite. The engine now writes a certificate
numbers for its own counterexamples (19z, in Quaerens too): the statement
as it was read, with the numbers it found as witnesses; on the 309
documents below 116 refutations of the engine that had none have one.
Asking Vampire's arithmetic about the verdicts on numbers that are still
without a certificate gives certificates to 60 more, and it never proved
the opposite of the engine. On all the 309 documents that the Quaerens
repository has by now (7470 statements) the same 259 statements get their
answer through Vampire, the other 7211 verdict lines are those of Quaerens
word for word, and `certificate-checker`, the checker as a program of its
own, accepts all the certificates the run writes: 3679 (3492 before the
proofs from the laws of the integers, which add three, the infinite
counter-models, which add eight, the engine's counterexamples, which add
116, and the verdicts of the engine confirmed by Vampire's arithmetic,
which add 60). In the run that measured the infinite
counter-models, with the machine under a load of 130, the search of
Vampire's arithmetic for "if x = k + 100 then x = m + 101"
(`false_rare_witnesses.tex`, 14) ran out of its five seconds and that
statement was left unsolved, so that run had 3502 certificates and 102
counterexamples verified; run alone the statement is verified, three
times out of three. The tables count it verified.

**Size.** The executable is 14.3 MB; Vampire alone is 12.0 MB. It was
15.0 MB with the checker compiled twice, once inside the engine, and 14.6 MB
with the engine as one translation unit.

**Vampire's proofs, followed by the checker.** Vampire finds a refutation for
134 of those statements: 127 theorems and 7 requests for an example that
cannot exist. All 134 are rechecked inference by inference: 15431 steps of
the checker in all, 72 for the median proof, 2091 for the longest. (The other
16 certified theorems are proved by an example, a finite model.) Before this
recheck the engine rebuilt the proofs it could; the theorems only Vampire can
prove were not verified, and the refuted requests neither. Three more, the
theorems on integers below, are refutations by Vampire of the checker's
clauses with the laws of the integers, followed in 87, 131 and 130 steps.

The 29 answers that are new were looked at one by one, and all are right:

- 8 statements that hold in every finite set and fail in an infinite one
  ("an injective map of a set into itself is onto", and the like): Vampire's
  saturation ends without a contradiction and there is no finite model.
  7 have a counter-model over the integers, certified (20g): S the integers
  from 0 on, and f(x) = x + 1, or f(x) = x - 1 except f(0) = 0, or both
  (for "f(g(x)) = x gives g(f(x)) = x"), or x + 1 with Y = {0} (for
  "f(f^{-1}(Y)) = Y"). The eighth, a monoid in which an element has two
  right inverses, has counter-models whose elements are maps of the
  naturals, not integers: it is refuted, not verified;
- 7 requests for an example of something that cannot exist (two sets that
  are equal by definition and should differ, a reflexive relation with an
  element not related to itself, a map that moves every part of a set, the
  empty one included): Vampire refutes them and the checker follows the
  refutation;
- 1 counterexample with six elements, verified, which the engine's own
  search did not reach;
- 1 request for an example that exists only in an infinite set (an
  injective map that is not onto): found by saturation, and certified with
  the same interpretation over the integers, which is the example;
- 2 theorems the engine could not prove, both certified: an order between
  the maps of two sets, from the engine's laws on sets of maps; and
  "f(z) = z and f(s(y)) = s(f(y)) give f(y) = y for every y" with the
  induction principle written as a hypothesis on all the parts of S, which
  Vampire proves on the checker's clauses with the part of the x with
  f(x) = x;
- 10 statements on numbers, by Vampire's arithmetic theories (24 statements
  of the corpus reach them). 7 are false statements, all seven from the
  documents of false statements, refuted by a proof of their negation, and
  all seven are counterexamples verified. For 5 of them Vampire gives the
  numbers and the checker recomputes the statement on them ("if
  x = k^2 + 7 and y = j^2 + 7 then x = y" with x = 7, y = 8, k = 0, j = 1;
  "x^2 + a^2 + b^2 > 0 for all reals" with three zeros). The other 2 need
  more than numbers ("if x = k + 100 with k positive then x = m + 101 with
  m positive" fails at x = 101, k = 1 because no positive m works): there
  Vampire gives the numbers and the checker settles the one integer
  variable that is left by its complete count. 3 are theorems on integers
  in several variables, which no number shows: "(ab - 2)(a - b) = 0 and
  (bc - 2)(b - c) = 0 give (ac - 2)(a - c) = 0" and two on divisibility.
  They were found and not verified until Vampire proved them again from
  the laws of the integers, on the checker's clauses (20f): now all three
  are certified.

No statement of the corpus speaks of two equipotent sets and is left without
an answer by the engine, so what Vampire proves with an equipotence adds
nothing there; it does on other statements ("if S and T are equipotent and
S has at most three elements, so has T": certified, 183 steps), and on the
fuzz below.

**Cost** (one document after the other, `-t 3`; the machine was busy with
other programs, so the figures of one run are comparable with each other
more than with those of another day):

| | Time | CPU time | Peak memory |
|---|---|---|---|
| Quaerens alone | 90.0 s | 87.9 s | 465 MB |
| Together | 164.6 s | 197.8 s | 467 MB |
| Together, without the arithmetic theories (`--math_numbers_time 0`) | 128.9 s | 118.3 s | 469 MB |

Working together costs time: 83% on the whole corpus, 43% without the
arithmetic theories. Where it goes:

- the statements on numbers that Vampire's arithmetic does not decide take
  their whole time, with two processes each (14 of the 24 that reach it):
  35 seconds here. `--math_numbers_time` bounds this, at 5 seconds by
  default whatever the time limit is;
- the search for finite models waits its full time on the statements whose
  only counter-models are infinite (in another run of the same evening:
  160.5 s, and 156.7 s with `--math_model_time 0.5`);
- a statement on the parts of a set for which neither the engine nor
  Vampire finds an answer takes Vampire's whole time limit (2 statements);
- having the checker follow Vampire's inferences does not cost more than
  having the engine rebuild the proofs, which is what happened before and
  still happens without the recheck (160.5 s with it, 170.3 s with
  `--math_recheck_time 0`).

- confirming the engine's verdicts about numbers without a certificate
  (`--math_confirm_engine`) costs the most: on the 309 documents, six at a
  time, 519 s of processor time instead of 176 s, and 2:24 instead of
  0:51, for the 60 certificates it adds. Each such statement gets two
  searches of Vampire's arithmetic, which use their whole five seconds
  when they prove nothing; `--math_confirm_engine off` gives the time back.
  (Before the engine certified its own counterexamples it was 674 s
  instead of 133 s for 114.)

No improvement in speed is claimed for Vampire; what is gained is in the
tables above. For the engine on its own there is one: `quaerens --threads 4`
decides the statements of a document four at a time, and the whole corpus,
one document after the other, takes 48 s instead of 108 s (101 s of
processor time instead of 97 s), with the same verdict lines.

Vampire itself, on TPTP input, is not changed: `checks/sanity` passes as
before, and on the 33 problems of `checks/Problems`, with three sets of
options, the untouched and the integrated executable print the same output
(99 runs of 99).

**Fuzz and sanitizers**, on the last version. The scripts of the Quaerens
repository, each with an oracle of its own: 22 scripts, 1220 statements, no
`BUG` (one `SUSPECT`, looked at: a correct proof of the engine about x = 4/5,
outside the window of that oracle). `Math/tools/fuzz_numbers.py`: 800
statements on integers with eight seeds, no `BUG`; Vampire's arithmetic
decides 661 of them, 393 true ones proved and 268 false ones refuted, all as
the counting oracle says; in the three seeds run with the witnesses, 143 of
the 248 answers came with numbers that the checker recomputed. `Math/tools/fuzz_equipotence.py`: 500 statements
with five seeds, the equipotence in every place a statement can have it (a
hypothesis, a hypothesis denied, something to prove or to refute, one side
of an "if and only if"), no `BUG`; the engine decides 433, Vampire proves 41
where the engine had no answer, all 41 certified by the checker and all
true for an oracle that only knows that equipotent sets have as many
elements, and 26 stay without an answer (16 of them false: none was
proved). This run is the adversary of the checker's rule for equipotence.
With the engine as modules: the 22 scripts again, against `quaerens`, the
engine as a program on its own, 1220 statements with new seeds, no `BUG`
(two `SUSPECT`, looked at: a false statement whose refutation needs y =
2x^3 - 2x, outside the window of that oracle, and an equipotence with a set
of parts, which that oracle does not read; both verdicts are right); eight
of them against this executable, 720 statements, no `BUG`;
`fuzz_numbers.py`, 400 statements, and `fuzz_equipotence.py`, 300
statements, no `BUG`.
`Math/tools/fuzz_bijections.py`: 1000 statements with eleven seeds, no
`BUG`; 653 have a finite counterexample and the engine refutes every one,
none is proved; the engine proves 223, Vampire proves 107 more with a
bijection the engine offered, all followed by the checker, and 17 stay
without an answer. This run is the adversary of the rule that proves an
equipotence. `Math/tools/fuzz_arithmetic_laws.py`: 420 statements with five
seeds, no `BUG`: the checker's clauses of no false claim were refuted by
Vampire (three strategies, two seconds each), and every false fact offered
as `compute` was refused; of the true claims, 296 were refuted from the
laws. This run is the adversary of the proofs from the laws of the
integers. On 120 of those true claims, with two seconds, the default
saturation refutes 100, selection 1 with discount and four clauses by
weight for one by age 93, the two one after the other 106: that is what
the driver does. Through the whole program, `fuzz_numbers.py` with the
proofs from the laws: 450 statements with three seeds, no `BUG`; of the 194
theorems Vampire's arithmetic proves, 163 are certified, 95 of them by a
proof from the laws that the checker followed, and 31 are found, not
verified. Under the sanitizers, the documents of the three theorems, of
the numbers, of logic and of the parts of a set: no report. With the checker's count: `fuzz_numbers.py` again, 1260
statements, no `BUG`; the checker settles 125 of them by itself, 69 true
and 56 false, all as the counting oracle says; and the scripts of Quaerens
on numbers through `as_quaerens.py`, 480 statements, no `BUG`. Under the
sanitizers: the 65 runs of `checks/latex-sanity` and 100 of these
statements, no report.
AddressSanitizer and UndefinedBehaviorSanitizer: with the engine as modules,
no report on the whole corpus run through `quaerens` (6506 statements, the
same output as without the sanitizers) nor on the 56 runs of
`checks/latex-sanity`. Before that,
no report on 386 statements of 15 documents that use every path (161
refutations rechecked, 97 answers of the arithmetic theories), with the
document and the certificates written; none on 145 statements of 6
documents run again with the checker and the plots as modules and the rule
for equipotence; and none on 153 statements of 5 documents with the
numbers asked of Vampire and recomputed by the checker (50 certificates
"numbers").

## Licences

Vampire is under its modified BSD 3-clause licence (`LICENCE`). The files
added by this integration outside `Math/quaerens/` carry Vampire's header.
The sources in `Math/quaerens/` are the Quaerens project, under the BSD
3-clause licence (`Math/quaerens/LICENCE`), which is compatible with
Vampire's. They use the C standard library only. The LaTeX compiler
used for the PDF is an external program, run if present and never linked.
