# Mathematics in Vampire

Vampire reads mathematical statements written in LaTeX. The ones that are
logic it proves or refutes with its own provers; the ones that are mathematics
proper (an induction, an inequality, a derivative, a matrix) go to the
algorithm made for each; and of every answer it says how far it was checked.

This is the Quaerens project absorbed into Vampire as a set of modules. It is
one program, and its two parts work on a statement together, each where it is
the better one: Vampire searches for proofs and for finite models; the
mathematical engine reads the statement, judges the models Vampire finds in
its own structure for models, and rebuilds Vampire's proofs in a form that
the independent checker can recheck. Where sets of all the parts of a set
come in, the engine goes first and Vampire is asked when the engine has no
answer. Neither decides against the other: an answer of one is always put to
the test of the other, or of the checker.

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
           |        proof -> engine: rebuilt in a form the checker can recheck
           |
           +-- logic with sets of all parts / all maps ------> THE ENGINE LEADS
           |      engine: model search with the real sets, certifying proof
           |        no answer -> Vampire: proof from the laws the engine supplies
           |
           +-- mathematics proper, logic with no first-order form -> the engine
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
  - a **proof** tells the engine that the statement is a theorem, and the
    engine rebuilds a proof in a form the checker can recheck
    (`qr_certify_item`). If it cannot, the theorem stands on Vampire's
    proof alone and is reported as not verified.
- **Logic with sets of all the parts or of all the maps of a set, or with
  written numbers.** The engine leads: a model must have every part and
  every map, which the engine builds and a first-order model builder does
  not promise, and a proof must choose the parts it needs. When the engine
  has no answer Vampire is asked for a proof, from the laws of those sets
  that the engine supplies as axioms ("two parts with the same elements are
  the same part", "the elements that satisfy this condition are a part").
  What Vampire proves from the laws is a theorem; that it finds no proof
  says nothing, and is never read as a refutation.
- **Mathematics proper.** No faithful first-order translation exists that
  Vampire could use, so the statement goes to its algorithm in the engine:
  induction on sums and products, sign tables for equations and inequalities
  (also solving them), limits, derivatives, integrals, matrices and linear
  systems, functions of several variables, identities with indices. The
  same holds for logic with no first-order form: a quantifier over parts
  that are not a set of the statement, a bijection between two sets.
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

- **A proof printed by Vampire is not a certified proof.** A theorem found
  by Vampire is `TheoremCertified` only when the engine has rebuilt a proof
  and the independent checker has accepted its certificate; otherwise it is
  `TheoremUnverified`. The checker does not replay Vampire's inferences.
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
| `Math/LogicProblem` | the statement of the running process: what Vampire found (a refutation, a model), written down as data |
| `Math/Driver` | the run over the statements of an input; the searches of Vampire in child processes; models and proofs back to the engine |
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

The engine is touched in one place, its procedure for logic
(`prove_abstract()` in `Math/quaerens/main.c`), which no longer only decides:
it does the task it is asked for. It hands a statement over, read, unfolded
and rechecked, with the laws of its sets of parts and of maps; it adopts a
model found by Vampire; it writes a certifiable proof of a statement Vampire
proved; or it decides, as it always did. The other four files are byte for
byte those of Quaerens.

## Migration: what is where, and what is not done

| Capability of Quaerens | In Vampire | State |
|---|---|---|
| Reading LaTeX: expressions, sets, quantifiers, solution sets, `\item` | `Parse/LaTeX` over `parser.c` | in use, in C behind `Math/Engine.h` |
| Unfolding the notation of the books, rechecked on finite models | frontend | in use, before a statement is handed to Vampire |
| Logic over plain sets: the search for a proof and for a finite model | **Vampire** (saturation, AVATAR, finite model builder) | Vampire leads; the engine's model finder is not used here |
| Logic over plain sets: making the answer checkable | engine | the engine's structure for models judges Vampire's models; its certifying provers rebuild Vampire's proofs, and do not decide |
| Logic with sets of *all* parts or *all* maps, written numbers | engine first, then **Vampire** | the engine leads (measured); Vampire proves from the engine's laws what the engine cannot |
| Logic with a quantifier over parts, or a bijection between sets | engine | no first-order form: the engine's procedures are the only ones |
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
- **Vampire's proofs are not replayed.** A theorem found by Vampire is
  certified when the engine can prove the statement itself, which it can
  for most; there is no step-by-step check of Vampire's inferences, so a
  theorem only Vampire can prove stays `TheoremUnverified`.
- **No reasoning inside one proof across the two.** They pass statements,
  models and proofs to each other; Vampire cannot ask the engine for a
  computation in the middle of a proof, and statements that mix logic with
  arithmetic or analysis are not given to Vampire's arithmetic theories.
- **A quantifier over parts and a bijection between sets are not
  translated**; those statements are the engine's alone.
- **The engine's worked solutions are in English only**, and the engine's
  one-line verdicts (`% Engine verdict:`) are in Italian.
- **The engine's work budgets** (model search, verification, stack) are not
  options of Vampire: the defaults apply.
- **Interactive mode** does not read LaTeX.

## Tests

- `UnitTests/tMathLogic.cpp` (ctest `MathLogic`): the typed reading, the
  translation (plain sets, sets of parts and of maps, written numbers), the
  checker on correct and altered counterexamples, the engine adopting and
  refusing models found elsewhere, the engine rebuilding a proof and
  refusing to rebuild one of a false statement, the engine on false,
  ill-defined and ambiguous statements.
- `checks/latex-sanity build/vampire`: five documents in `checks/latex/`
  (logic, sets of parts, mathematics, false statements, invalid writings)
  with the expected result of every statement and of who reached it; no
  false statement is a theorem; a theorem is certified only when the checker
  accepted a certificate; certificates are accepted by `certificate-checker`
  and rejected once altered; TPTP input is untouched.
- `checks/sanity` and the unit tests of Vampire are unchanged and must pass
  as before.

## Measures

All on the corpus of the engine: 155 documents, 6506 statements, of which 6259
are mathematics proper or logic the engine decides, and 247 go through
Vampire.

**Who goes first**, decided by what each does alone:

| Kind of statement | Vampire | The engine | Goes first |
|---|---|---|---|
| First-order logic over plain sets (245 statements) | decides 244 | decides 229 | Vampire |
| With sets of all parts or all maps (19 theorems of `parts_and_maps.tex`) | proves 16, from the engine's laws | proves 19 | the engine |

**What working together gives**, on the 247 statements that go through
Vampire:

| | The engine alone | Together |
|---|---|---|
| Theorems certified | 141 | 141 |
| Counterexamples verified | 88 | 89 |
| Theorems found, not verified | 0 | 2 |
| Refutations found, not verified | 0 | 14 |
| No answer | 18 | 1 |

Every certified answer of the engine is still certified, by the same checker;
Vampire adds answers the engine did not have, and they are labelled for what
they are. No statement is answered one way by one and the other way by the
other.

**Cost** (one document after the other, idle machine, `-t 3`):

| | Time | Peak memory |
|---|---|---|
| Quaerens alone | 89.0 s | 463 MB |
| Together | 116.0 s | 467 MB |
| Together, `--math_model_time 0.5` | 101.0 s | 467 MB |

Working together costs time: 30% on the whole corpus, 13% with the search
for finite models cut to half a second. The search for models waits its full
time on the statements whose only counter-models are infinite, and a proof
found by Vampire is then rebuilt by the engine. No improvement in speed is
claimed; what is gained is in the table above.

Vampire itself, on TPTP input, is not changed: `checks/sanity` takes the same
time before and after, and on the 33 problems of `checks/Problems` the
untouched and the integrated executable print the same output.

## Licences

Vampire is under its modified BSD 3-clause licence (`LICENCE`). The files
added by this integration outside `Math/quaerens/` carry Vampire's header.
The sources in `Math/quaerens/` are the Quaerens project, under the BSD
3-clause licence (`Math/quaerens/LICENCE`), which is compatible with
Vampire's. They use the C standard library only. The LaTeX compiler
used for the PDF is an external program, run if present and never linked.
