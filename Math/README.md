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
arithmetic theories when a statement quantifies over numbers.
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
           |        no answer, quantifiers over numbers of one kind
           |                  -> Vampire's arithmetic: the statement, and its negation
           |
           +-- two sets supposed equipotent --------------------> THE ENGINE LEADS
           |        no answer -> Vampire: proof with the bijection as two maps
           |                     inverse to each other
           |
           +-- a bijection between two sets, to be proved ------> the engine alone
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
  means the same. This holds only for an equipotence that is a hypothesis:
  to *prove* that two sets are equipotent is to build a bijection, which
  the engine's search for witnesses does and a first-order prover cannot.
  The proof is then rechecked like any other, on the checker's clauses:
  there an equipotence is a proposition that implies that two maps undo
  each other, so that a refutation can use it and cannot prove it (11m-e
  in `Math/quaerens/checker.c`, with the argument that no model is lost).
  The same clauses are given to Vampire when the equipotence stands
  anywhere else in a statement the engine could not decide.
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
  for a proof of the statement and for a proof of its negation. What is
  proved there is found, not verified: the checker has no language for
  arithmetic with quantifiers. Variables of two kinds, exponents that are
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
as `% Verification status: ... [Code]` and, for scripts, `% Result N: Code (who)`.

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
  is `CounterexampleUnverified`.
- **With sets of parts or of maps, no proof from Vampire means nothing.**
  It reasons from finitely many laws about sets that have all their parts.
- **If Vampire has a proof and the engine a certified counterexample**, one
  of them is wrong: neither is reported, the statement is `Unsolved`, and
  the output says `CONTRADICTION`. None has occurred in any test.
- **No numerical test makes a theorem.** The engine never reports one on such
  grounds, and nothing in this module upgrades a status.
- **A proof by Vampire's arithmetic theories is never certified.** It is
  `TheoremUnverified`, or `CounterexampleUnverified` when what was proved
  is the negation, and the output says which. That is where the engine's
  own proofs of such statements stand too ("proved with the rules for
  quantifiers; no certificate"): the checker has a language for one real
  variable (sign tables), and none for integers or for several variables
  with quantifiers. On these statements nothing is lost by asking Vampire,
  and nothing is certified by either.

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

There is no option to have the engine decide a statement that Vampire can be
given: that would be a second prover for the same statements.

Every other option of Vampire applies to the statements of logic as it does to
a TPTP problem: `-t`, `--mode casc`, `-sa fmb`, `--proof off`. `--mode output`
prints a statement as TPTP.

## Where things are

| | |
|---|---|
| `Parse/LaTeX` | the frontend as the rest of Vampire sees it: the statements of an input, each read and classified |
| `Math/Engine.h`, `Math/Engine.c` | the C interface of the mathematical engine, and the translation unit that holds it |
| `Math/quaerens/` | the engine's sources: `main.c` (its design, the index of its chapters, and one include per volume), the volumes `engine_*.c` (see below), `parser.c` (LaTeX), `output.c` (document), `plot.c` (plots), `checker.c` (checker) |
| `Math/LogicStatement` | a statement of logic as a typed tree: sorts, symbols with signatures, formulas |
| `Math/LogicTranslator` | that tree into Vampire units; possibly empty sorts |
| `Math/NumberStatement` | a statement with quantifiers over numbers, as the engine hands it over, into a TPTP problem for Vampire's arithmetic |
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
| `Math/tools/engine_volumes.py` | splits the engine's single file into its volumes, joins them back, checks that the two are the same |
| `Math/tools/fuzz_numbers.py` | differential fuzz of the statements on integers that reach Vampire's arithmetic, against an oracle that counts |
| `Math/tools/fuzz_equipotence.py` | differential fuzz of the statements that suppose two sets equipotent, against an oracle that compares numbers of elements |

The engine by domain. In Quaerens the engine is one file of 52 thousand
lines, a book of numbered chapters. Here the book is in volumes, one per
domain, each a run of consecutive chapters:

| Volume | Chapters | |
|---|---|---|
| `engine_foundations.c` | 1-7 | limits, errors and memory, exact numbers, monomials, polynomials, atoms, fractions of polynomials |
| `engine_evaluation.c` | 10-12 | the known sequences, an expression tree to a fraction, tests of vanishing |
| `engine_induction.c` | 13 | induction on sums and products |
| `engine_sets.c` | 15-16 | relations between sets by regions |
| `engine_intervals.c` | 24 | real numbers as intervals with a guaranteed error |
| `engine_quantifiers.c` | 18-18.7 | quantifiers over numbers: the rules of proof |
| `engine_sign_tables.c` | 18.8-18.19 | sign tables, solutions, plots, one parameter |
| `engine_explanation.c` | 40 | worked solutions |
| `engine_quantifiers_verdict.c` | 19 | quantifiers: independent verification and verdict |
| `engine_sequences.c` | 25-26 | induction on an inequality, sequences by recurrence |
| `engine_derivatives.c` | 27 | derivatives and the study of a function |
| `engine_logic.c` | 28 | arbitrary sets: finite models, instances, saturation, the tasks done for Vampire |
| `engine_limits.c` | 29 | limits |
| `engine_integrals.c` | 30 | integrals |
| `engine_linear_algebra.c` | 32-33 | matrices, determinants, linear systems |
| `engine_multivariable.c` | 35-36 | functions of several variables |
| `engine_indices.c` | 38 | identities with indices |
| `engine_statement.c` | 20, 23 | which chapter reads a statement; the document; `main` |

Nothing was rewritten to make them: a volume is cut at the banner of its
first chapter, and the volumes joined in order are, byte for byte, the single
file (`python3 -I Math/tools/engine_volumes.py check Math/quaerens`). They
are read in that order into one translation unit, exactly as the chapters
were, so the compiled engine is the same program: the preprocessed
translation unit before and after the split is identical. To bring in a new
`main.c` from the Quaerens repository: `join`, apply the changes to the
single file, `split`.

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
the checker already had; one rule was added to it, in Quaerens too, with
its justification and its tests: an equipotence among the clauses of a
proof by saturation (11m-e in `checker.c`).

## Migration: what is where, and what is not done

| Capability of Quaerens | In Vampire | State |
|---|---|---|
| Reading LaTeX: expressions, sets, quantifiers, solution sets, `\item` | `Parse/LaTeX` over `parser.c` | in use, in C behind `Math/Engine.h` |
| Unfolding the notation of the books, rechecked on finite models | frontend | in use, before a statement is handed to Vampire |
| Logic over plain sets: the search for a proof and for a finite model | **Vampire** (saturation, AVATAR, finite model builder) | Vampire leads; the engine's model finder is not used here |
| Logic over plain sets: making the answer checkable | checker, engine | the checker follows Vampire's inferences one by one (`Proof/Replay`); the engine's structure for models judges Vampire's models; its certifying provers rebuild a proof only where the inferences cannot be followed |
| Logic with sets of *all* parts or *all* maps, written numbers | engine first, then **Vampire** | the engine leads (measured); Vampire proves from the engine's laws what the engine cannot |
| Logic with a quantifier over the parts of a set | engine first, then **Vampire** | Vampire refutes the checker's clauses, with the parts the engine proposes |
| Two sets supposed equipotent | engine first, then **Vampire** | the engine leads; Vampire proves what the engine cannot, with the bijection as two maps inverse to each other, and the checker follows the proof |
| A bijection between two sets, to be proved | engine | proving one means building it: the engine's search for witnesses is the only procedure |
| Relations between parts by regions (complete decision) | engine | in use |
| Induction: sums, products, recurrences, inequalities | engine | in use |
| Sign tables: equations, inequalities, solving, parameters, congruences | engine | in use |
| Quantifiers over integers, rationals, reals | engine first, then **Vampire** | the engine's rules and sign tables lead; what they do not decide goes to Vampire's arithmetic theories, when every variable is of one kind |
| Limits, derivatives, integrals | engine | in use |
| Matrices, determinants, linear systems, discussion by a parameter | engine | in use |
| Partial derivatives, gradients, Hessians, critical points | engine | in use |
| Identities with indices, declared metrics | engine | in use |
| Worked solutions (step by step) | engine, into the document | in use, English only |
| Account of a proof | `Humanizer/ProofNarrator`, for Vampire's refutations | new, English and Italian |
| Document, plots | `output.c`, `plot.c` through `Math/Engine.h` | in use; Vampire's answers are added to the same document |
| Independent checker | `Proof/IndependentChecker`, `certificate-checker` | in use; also judges Vampire's finite models |

Not done, and not claimed:

- **Two parts of the engine are modules; the rest is volumes.** The
  checker (`Proof/IndependentChecker`) and the plots (`Math/Plot`) are
  compiled apart and used through interfaces: the engine no longer holds
  their sources, and the checker is in the executable once instead of
  twice. The other parts (numbers and polynomials, sign tables, limits,
  integrals, linear algebra, logic, indices) are files of their own, by
  domain, but are still read in order into one translation unit behind one
  C interface: a volume uses whatever the volumes before it define, and
  none has an interface of its own. Making those modules means deciding,
  volume by volume, what each exports, and giving up the shared static
  state (the arena, the table of atoms, the proof being written): the
  checker and the plots could be separated because Quaerens already keeps
  them independent, and nothing else in the engine is.
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
- **"Not a theorem" by saturation is still not verified**: there is no
  finite model to recompute and no refutation to follow.
- **No reasoning inside one proof across the two.** They pass statements,
  models and proofs to each other; Vampire cannot ask the engine for a
  computation in the middle of a proof.
- **Vampire's arithmetic gets only statements about numbers of one kind**,
  with polynomial expressions. A statement that mixes integers and
  rationals, or has a declared map, an exponent that is a letter, a
  function or a root, stays with the engine; and what Vampire proves about
  numbers is not rechecked by anything.
- **A bijection can be used by Vampire, not proved.** To prove that two
  sets are equipotent is to build a bijection: the engine's search for
  witnesses does that, and it stays the only way. Among the clauses an
  equipotence is used wherever it stands, but two writings of the same
  equipotence are not recognised as one, and an equipotence with a product
  of sets is not handed over.
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
  a set is handed over with the parts to try.
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
  by the rule alone. (The rule itself is tested in the Quaerens repository,
  `tests/checker/test_equipotence_clauses.c`, against a finite oracle.)
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
- `python3 -I Math/tools/engine_volumes.py check Math/quaerens`: the
  volumes of the engine, joined, split again, are the same files.
- Fuzz, outside the checks (Python 3, standard library only): the scripts
  of the Quaerens repository run against this executable through
  `Math/tools/as_quaerens.py`, each with an oracle of its own; and
  `Math/tools/fuzz_numbers.py`, for the statements on integers that go to
  Vampire's arithmetic: every quantified variable is confined to a few
  values by the statement itself, and the oracle tries them all; and
  `Math/tools/fuzz_equipotence.py`, for the statements that suppose two
  sets equipotent. A line `BUG` is a false proof or a false refutation.
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
| Theorems certified | 141 | 143 |
| Counterexamples verified | 88 | 89 |
| Requests for an example refuted, certified | 0 | 7 |
| Theorems found, not verified | 0 | 4 |
| Refutations found, not verified | 0 | 15 |
| No answer, or no method | 30 | 1 |

Every certified answer of the engine is still certified, by the same checker;
Vampire adds answers the engine did not have, and they are labelled for what
they are. No statement is answered one way by one and the other way by the
other. The run writes 3454 certificates, and `certificate-checker`, the
checker as a program of its own, accepts all of them.

**Size.** With the checker compiled once, and not also inside the engine,
the executable is 14.6 MB (15.0 MB before; Vampire alone is 12.0 MB).

**Vampire's proofs, followed by the checker.** Vampire finds a refutation for
134 of those statements: 127 theorems and 7 requests for an example that
cannot exist. All 134 are rechecked inference by inference: 15431 steps of
the checker in all, 72 for the median proof, 2091 for the longest. (The other
16 certified theorems are proved by an example, a finite model.) Before this
recheck the engine rebuilt the proofs it could; the theorems only Vampire can
prove were not verified, and the refuted requests neither.

The 29 answers that are new were looked at one by one, and all are right:

- 8 statements that hold in every finite set and fail in an infinite one
  ("an injective map of a set into itself is onto", and the like): Vampire's
  saturation ends without a contradiction, there is no finite model to
  check, and they are reported as refuted, not verified;
- 7 requests for an example of something that cannot exist (two sets that
  are equal by definition and should differ, a reflexive relation with an
  element not related to itself, a map that moves every part of a set, the
  empty one included): Vampire refutes them and the checker follows the
  refutation;
- 1 counterexample with six elements, verified, which the engine's own
  search did not reach;
- 1 request for an example that exists only in an infinite set (an
  injective map that is not onto): found by saturation, not verified;
- 2 theorems the engine could not prove, both certified: an order between
  the maps of two sets, from the engine's laws on sets of maps; and
  "f(z) = z and f(s(y)) = s(f(y)) give f(y) = y for every y" with the
  induction principle written as a hypothesis on all the parts of S, which
  Vampire proves on the checker's clauses with the part of the x with
  f(x) = x;
- 10 statements on numbers, by Vampire's arithmetic theories, not verified
  (24 statements of the corpus reach them): 3 theorems on integers,
  "(ab - 2)(a - b) = 0 and (bc - 2)(b - c) = 0 give (ac - 2)(a - c) = 0" and
  two on divisibility; and 7 false statements refuted by a proof of their
  negation, all seven from the documents of false statements ("if
  x = k^2 + 7 and y = j^2 + 7 then x = y" on integers, "x^2 + a^2 + b^2 > 0
  for all reals").

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

No improvement in speed is claimed; what is gained is in the tables above.

Vampire itself, on TPTP input, is not changed: `checks/sanity` passes as
before, and on the 33 problems of `checks/Problems`, with three sets of
options, the untouched and the integrated executable print the same output
(99 runs of 99).

**Fuzz and sanitizers**, on the last version. The scripts of the Quaerens
repository, each with an oracle of its own: 22 scripts, 1220 statements, no
`BUG` (one `SUSPECT`, looked at: a correct proof of the engine about x = 4/5,
outside the window of that oracle). `Math/tools/fuzz_numbers.py`: 500
statements on integers with five seeds, no `BUG`; Vampire's arithmetic
decides 413 of them, 245 true ones proved and 168 false ones refuted, all as
the counting oracle says. `Math/tools/fuzz_equipotence.py`: 500 statements
with five seeds, the equipotence in every place a statement can have it (a
hypothesis, a hypothesis denied, something to prove or to refute, one side
of an "if and only if"), no `BUG`; the engine decides 433, Vampire proves 41
where the engine had no answer, all 41 certified by the checker and all
true for an oracle that only knows that equipotent sets have as many
elements, and 26 stay without an answer (16 of them false: none was
proved). This run is the adversary of the checker's rule for equipotence.
AddressSanitizer and UndefinedBehaviorSanitizer:
no report on 386 statements of 15 documents that use every path (161
refutations rechecked, 97 answers of the arithmetic theories), with the
document and the certificates written, and none on 145 statements of 6
documents run again with the checker and the plots as modules and the rule
for equipotence.

## Licences

Vampire is under its modified BSD 3-clause licence (`LICENCE`). The files
added by this integration outside `Math/quaerens/` carry Vampire's header.
The sources in `Math/quaerens/` are the Quaerens project, under the BSD
3-clause licence (`Math/quaerens/LICENCE`), which is compatible with
Vampire's. They use the C standard library only. The LaTeX compiler
used for the PDF is an external program, run if present and never linked.
