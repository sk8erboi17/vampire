# Mathematics in Vampire

Vampire reads mathematical statements written in LaTeX, proves or refutes the
ones that are logic with its own provers, hands the ones that are mathematics
proper (an induction, an inequality, a derivative, a matrix) to the algorithm
made for each, and says of every answer how far it was checked.

This is the Quaerens project absorbed into Vampire as a set of modules. It is
one program: there is no second executable and no second prover competing for
the same statements.

```
vampire statements.tex                         every \item of the document, one after the other
vampire --input_syntax latex < formula.txt     one bare formula
vampire --math_document out.pdf statements.tex also the document: worked solutions, proofs, plots
vampire --math_certificates out.cert ...       also the certificates the checker accepted
certificate-checker out.cert                   recheck them, without Vampire
```

## What happens to a statement

```
LaTeX  ->  Parse/LaTeX  ->  first-order logic over arbitrary sets?
                               |yes                          |no
                     Math/LogicStatement (typed)      the mathematical engine
                     Math/LogicTranslator             (Math/quaerens, through Math/Engine.h)
                               |                             |
                     Vampire, in any mode:            result + certificate
                     saturation, finite models               |
                               |                             |
          proof  ->  Humanizer/ProofNarrator                 |
          model  ->  certificate  ->  Proof/IndependentChecker  <-+
                               |
                     verification status, document, certificates
```

- **Logic** (elements, maps and relations of sets that are not given;
  quantifiers; equality). The frontend unfolds the notation of the books into
  quantifiers and rechecks the unfolding on finite models; the statement is
  typed (`Math/LogicStatement`) and translated (`Math/LogicTranslator`); a
  child process loads the units and from there on *is* Vampire on that
  problem, with whatever mode and options were given. By default a search
  for a finite counter-model (`--math_model_time`) runs together with the
  proof search, and the first answer that settles the statement ends the
  other; before a portfolio (`--mode casc`) the model search goes first.
- **Mathematics proper.** No faithful first-order translation exists that
  Vampire could use, so the statement goes to its algorithm in the engine:
  induction on sums and products, sign tables for equations and inequalities
  (also solving them), limits, derivatives, integrals, matrices and linear
  systems, functions of several variables, identities with indices.
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
| `Unsolved` | neither proved nor refuted within the limits |
| `Unsupported` | outside the fragment that is read |

Rules that are not negotiable:

- **A proof printed by Vampire is not a certified proof.** The checker cannot
  replay Vampire's inferences yet, so a theorem found by saturation is
  `TheoremUnverified`, always.
- **A finite model found by Vampire is a counterexample only after the
  checker recomputed the statement in it.** The model is rewritten as a
  certificate (`Math/LogicProblem.cpp`) and judged by
  `Proof/IndependentChecker`, which is compiled apart from the engine and from
  Vampire and shares no state with either. A model the checker does not
  accept is reported as `Unsolved`, with the reason.
- **"Not a theorem" without a model is not a verified refutation.** When
  saturation ends without a contradiction there may be only infinite
  counter-models ("an injective map of a set into itself is onto"): the status
  is `CounterexampleUnverified`.
- **No numerical test makes a theorem.** The engine never reports one on such
  grounds, and nothing in this module upgrades a status.

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
| `Math/quaerens/` | the engine's sources: `main.c` (search, calculus, decisions), `parser.c` (LaTeX), `output.c` (document), `plot.c` (plots), `checker.c` (checker) |
| `Math/LogicStatement` | a statement of logic as a typed tree: sorts, symbols with signatures, formulas |
| `Math/LogicTranslator` | that tree into Vampire units; possibly empty sorts |
| `Math/LogicProblem` | the statement of the running process: models to the checker, answers with their status |
| `Math/Driver` | the run over the statements of an input; one child process per statement of logic |
| `Math/Verification.hpp` | the statuses |
| `Math/Names.hpp` | names of symbols back into LaTeX |
| `Proof/IndependentChecker` | the checker of certificates as its own translation unit; also the program `certificate-checker` |
| `Humanizer/ProofNarrator` | the account of a refutation, in English and Italian |
| `Math/tools/as_quaerens.py` | presents this executable to the fuzz scripts of the Quaerens repository |

Vampire's own files are touched in a handful of places, each a few lines and
each inert unless the input is LaTeX: the options (`Shell/Options`), the
loading of units built by a frontend (`UIHelper::loadUnits`), two hooks where
results are reported (`Shell/UIHelper.cpp`), two where the finite model
builder has, or could have, a model (`FMB/FiniteModelBuilder.cpp`), a size
accessor (`FMB/FiniteModelMultiSorted.hpp`), a way to name an input unit
(`Parse::TPTP::assignAxiomName`), and `main()`.

The engine is touched in one place: `prove_abstract()` in
`Math/quaerens/main.c` stops after reading, unfolding and rechecking a
statement of logic and hands it over, instead of starting its own search. The
other four files are byte for byte those of Quaerens.

## Migration: what is where, and what is not done

| Capability of Quaerens | In Vampire | State |
|---|---|---|
| Reading LaTeX: expressions, sets, quantifiers, solution sets, `\item` | `Parse/LaTeX` over `parser.c` | in use, in C behind `Math/Engine.h` |
| Unfolding the notation of the books, rechecked on finite models | frontend | in use, before a statement is handed to Vampire |
| Logic over plain sets: finite models, instances, saturation, splitting | **Vampire** (finite model builder, saturation, AVATAR) | replaced; the engine's provers are never called for these |
| Logic with sets of *all* parts or *all* maps, equipotence, written numbers | engine | kept as specialised procedures: not first-order over plain sorts, so not translated |
| Relations between parts by regions (complete decision) | engine | in use |
| Induction: sums, products, recurrences, inequalities | engine | in use |
| Sign tables: equations, inequalities, solving, parameters, congruences | engine | in use |
| Limits, derivatives, integrals | engine | in use |
| Matrices, determinants, linear systems, discussion by a parameter | engine | in use |
| Partial derivatives, gradients, Hessians, critical points | engine | in use |
| Identities with indices, declared metrics | engine | in use |
| Worked solutions (step by step) | engine, into the document | in use, English only |
| Account of a proof | `Humanizer/ProofNarrator`, for Vampire's refutations | new, English and Italian |
| Document, plots | `output.c`, `plot.c` through `Math/Engine.h` | in use; Vampire's answers are added to the same document |
| Independent checker | `Proof/IndependentChecker`, `certificate-checker` | in use; also judges Vampire's finite models |

Not done, and not claimed:

- **The engine is still one C translation unit** behind a C interface. Its
  parts (algebra, analysis, linear algebra, tensors) are chapters of
  `main.c`, not modules with interfaces of their own. Splitting them is the
  next structural step; `Proof/` (the checker) is the first part that is a
  module in the build.
- **The typed C++ form exists for statements of logic only.** Mathematical
  expressions are typed trees inside the engine and are not visible to C++.
- **Vampire's proofs are not certified.** Replaying a refutation in the
  checker (proof reconstruction) is not implemented.
- **A counter-model found by Vampire is not rechecked against the statement
  as written**, only against its unfolding (by the checker). The engine does
  both for the models it finds itself; the unfolding is rechecked on finite
  models before the statement is handed over.
- **Sets of parts and of maps are not translated**, so those statements do
  not benefit from Vampire.
- **The engine's worked solutions are in English only**, and the engine's
  one-line verdicts (`% Engine verdict:`) are in Italian.
- **The engine's work budgets** (model search, verification, stack) are not
  options of Vampire: the defaults apply.
- **Interactive mode** does not read LaTeX.

## Tests

- `UnitTests/tMathLogic.cpp` (ctest `MathLogic`): the typed reading, the
  translation, the checker on correct and altered counterexamples, the engine
  on false, ill-defined and ambiguous statements.
- `checks/latex-sanity build/vampire`: four documents in `checks/latex/`
  (logic, mathematics, false statements, invalid writings) with the expected
  result of every statement; no false statement is a theorem; proofs are
  never called certified; certificates are accepted by `certificate-checker`
  and rejected once altered; TPTP input is untouched.
- `checks/sanity` and the unit tests of Vampire are unchanged and must pass
  as before.

## Licences

Vampire is under its modified BSD 3-clause licence (`LICENCE`). The files
added by this integration outside `Math/quaerens/` carry Vampire's header.
The sources in `Math/quaerens/` are the Quaerens project, under the BSD
3-clause licence (`Math/quaerens/LICENCE`), which is compatible with
Vampire's. They use the C standard library only. The LaTeX compiler
used for the PDF is an external program, run if present and never linked.
