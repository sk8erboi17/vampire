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
- **Mathematics proper.** No faithful first-order translation exists that
  Vampire could use, so the statement goes to its algorithm in the engine:
  induction on sums and products, sign tables for equations and inequalities
  (also solving them), limits, derivatives, integrals, matrices and linear
  systems, functions of several variables, identities with indices. The
  same holds for a bijection between two sets: to prove one is to build
  it, which the engine's search for witnesses does and a first-order prover
  cannot.
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
| `Proof/Replay` | a refutation by Vampire, inference by inference, into the explicit steps the checker follows |
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
model found by Vampire; it hands over the clauses from which the checker
starts a proof by saturation, with the instances of the formulas on parts;
it writes a certifiable proof of a statement Vampire proved; or it decides,
as it always did. The other four files, the checker among them, are byte
for byte those of Quaerens: nothing was added to the checker for Vampire's
proofs, which are written in the steps it already had.

## Migration: what is where, and what is not done

| Capability of Quaerens | In Vampire | State |
|---|---|---|
| Reading LaTeX: expressions, sets, quantifiers, solution sets, `\item` | `Parse/LaTeX` over `parser.c` | in use, in C behind `Math/Engine.h` |
| Unfolding the notation of the books, rechecked on finite models | frontend | in use, before a statement is handed to Vampire |
| Logic over plain sets: the search for a proof and for a finite model | **Vampire** (saturation, AVATAR, finite model builder) | Vampire leads; the engine's model finder is not used here |
| Logic over plain sets: making the answer checkable | checker, engine | the checker follows Vampire's inferences one by one (`Proof/Replay`); the engine's structure for models judges Vampire's models; its certifying provers rebuild a proof only where the inferences cannot be followed |
| Logic with sets of *all* parts or *all* maps, written numbers | engine first, then **Vampire** | the engine leads (measured); Vampire proves from the engine's laws what the engine cannot |
| Logic with a quantifier over the parts of a set | engine first, then **Vampire** | Vampire refutes the checker's clauses, with the parts the engine proposes |
| A bijection between two sets | engine | proving one means building it: the engine's search for witnesses is the only procedure |
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
  computation in the middle of a proof, and statements that mix logic with
  arithmetic or analysis are not given to Vampire's arithmetic theories.
- **A bijection between two sets is not given to Vampire**; those
  statements are the engine's alone. A hypothesis "S and T are equipotent"
  could be given as two maps inverse to each other, but the checker's
  translation into clauses has no rule for it, and it was not added.
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
- `UnitTests/tMathLogic.cpp` (ctest `MathLogic`): the typed reading, the
  translation (plain sets, sets of parts and of maps, written numbers), the
  checker on correct and altered counterexamples, the engine adopting and
  refusing models found elsewhere, the engine rebuilding a proof and
  refusing to rebuild one of a false statement, the engine on false,
  ill-defined and ambiguous statements.
- `checks/latex-sanity build/vampire`: five documents in `checks/latex/`
  (logic, sets of parts, mathematics, false statements, invalid writings)
  with the expected result of every statement and of who reached it; no
  false statement is a theorem, among them one on the parts of a set that
  holds in every finite set; a theorem is certified only when the checker
  accepted a certificate, with and without the recheck of Vampire's
  inferences; certificates are accepted by `certificate-checker` and
  rejected once altered, and every rechecked refutation is rejected once
  its last step is removed; TPTP input is untouched.
- `checks/sanity` and the unit tests of Vampire are unchanged and must pass
  as before.

## Measures

All on the corpus of the engine: 155 documents, 6506 statements. 6257 are
mathematics proper, or logic that the engine decides or keeps; 249 get their
answer through Vampire.

**Who goes first**, decided by what each does alone:

| Kind of statement | Vampire | The engine | Goes first |
|---|---|---|---|
| First-order logic over plain sets (245 statements) | decides 244 | decides 229 | Vampire |
| With sets of all parts or all maps (19 theorems of `parts_and_maps.tex`) | proves 16, from the engine's laws | proves 19 | the engine |

**What working together gives**, on those 249 statements:

| | The engine alone | Together |
|---|---|---|
| Theorems certified | 141 | 143 |
| Counterexamples verified | 88 | 89 |
| Requests for an example refuted, certified | 0 | 7 |
| Theorems found, not verified | 0 | 1 |
| Refutations found, not verified | 0 | 8 |
| No answer | 20 | 1 |

Every certified answer of the engine is still certified, by the same checker;
Vampire adds answers the engine did not have, and they are labelled for what
they are. No statement is answered one way by one and the other way by the
other. The run writes 3454 certificates, and `certificate-checker`, the
checker as a program of its own, accepts all of them.

**Vampire's proofs, followed by the checker.** Vampire finds a refutation for
134 of those statements: 127 theorems and 7 requests for an example that
cannot exist. All 134 are rechecked inference by inference: 15431 steps of
the checker in all, 72 for the median proof, 2091 for the longest. (The other
16 certified theorems are proved by an example, a finite model.) Before this
recheck the engine rebuilt the proofs it could; the theorems only Vampire can
prove were not verified, and the refuted requests neither.

The 19 answers that are new were looked at one by one, and all are right:

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
  f(x) = x.

**Cost** (one document after the other, `-t 3`; the machine was busy with
other programs, so the CPU time is the fairer figure):

| | Time | CPU time | Peak memory |
|---|---|---|---|
| Quaerens alone | 110.0 s | 96.4 s | 467 MB |
| Together | 130.1 s | 120.6 s | 468 MB |
| Together, without the recheck of inferences (`--math_recheck_time 0`) | 133.6 s | 123.2 s | 468 MB |
| Together, `--math_model_time 0.5` | 117.5 s | 103.4 s | 467 MB |

Working together costs time: 18% on the whole corpus (25% of CPU time), 7%
with the search for finite models cut to half a second. The search for
models waits its full time on the statements whose only counter-models are
infinite. Having the checker follow Vampire's inferences does not cost more
than having the engine rebuild the proofs, which is what happened before and
still happens without the recheck. A statement on the parts of a set for
which neither the engine nor Vampire finds an answer now takes Vampire's
whole time limit. No improvement in speed is claimed; what is gained is in
the tables above.

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
