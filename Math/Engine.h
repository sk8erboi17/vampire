/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file Engine.h
 * The C interface of the mathematical engine (the Quaerens sources in
 * Math/quaerens/), as the rest of Vampire sees it.
 *
 * The engine reads statements written in LaTeX and decides the ones that are
 * mathematics proper: identities and inequalities by induction, equations and
 * inequalities by sign tables, limits, derivatives, integrals, matrices,
 * linear systems, functions of several variables, identities with indices.
 * Every such result is rechecked, and where a certificate exists the
 * independent checker (Math/quaerens/checker.c) has accepted it. Whoever
 * needs the checker for something the engine did not produce uses
 * Proof/IndependentChecker.h, not this interface.
 *
 * Statements of first-order logic over arbitrary sets are NOT decided here
 * when the caller asks for them to be handed over (@c delegate_logic): the
 * engine reads them, unfolds the notation of the books into quantifiers,
 * rechecks the unfolding, and returns the statement in the language of the
 * certificates. Searching for a proof or a counterexample is Vampire's job.
 * What Vampire finds comes back here: a finite model is loaded into the
 * engine's own structure for models and judged as the engine judges its own
 * (qr_adopt_model()); a statement Vampire proved is given a proof that the
 * independent checker can recheck (qr_certify_item()).
 *
 * The interface is plain C so that the engine can stay in C while its parts
 * are being moved, one at a time, into C++ modules. Nothing else in Vampire
 * includes the engine's sources.
 *
 * Not thread-safe and not re-entrant: the engine has one state, and every
 * string it returns is valid only until the next call of this interface.
 */

#ifndef __Math_Engine__
#define __Math_Engine__

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/** What the engine established about a statement. */
typedef enum {
  QR_PROVED,      /* a theorem: proved, and rechecked */
  QR_REFUTED,     /* false: a counterexample was computed */
  QR_SOLVED,      /* a request ("find the solutions"): the result was computed and read back */
  QR_NOT_PROVED,  /* read, but neither proved nor refuted within the budgets */
  QR_UNSUPPORTED, /* outside the fragment the engine can read */
  QR_LOGIC        /* first-order logic over arbitrary sets: handed over, see QrVerdict::logic */
} QrOutcome;

/**
 * The verdict on one statement.
 *
 * All strings belong to the engine and stay valid until the next call of
 * this interface. A missing string is NULL.
 */
typedef struct {
  QrOutcome outcome;
  int certified;           /* 1 if the independent checker accepted the certificate of this verdict */
  const char* line;        /* the whole verdict in one line, in the engine's own words (Italian) */
  const char* method;      /* QR_PROVED, QR_SOLVED: how (Italian) */
  const char* reason;      /* why not, or why the certificate is missing (Italian) */
  const char* detail;      /* QR_REFUTED: the counterexample; QR_SOLVED: the solutions, in LaTeX */
  const char* note;        /* a caveat on how the statement was read (Italian) */
  const char* proof;       /* the written proof, in LaTeX */
  const char* certificate; /* the certificate accepted by the checker */
  int induction_variable;  /* the letter of the induction, or 0 */
  long long base;          /* QR_PROVED by induction: the base case */
  long long witness;       /* QR_REFUTED by induction: a value where the statement fails */

  /* QR_LOGIC only. */
  const char* logic;       /* the unfolded statement in the language of the certificates:
                              lines "sort", "symbol", "statement" */
  int wants_example;       /* 1 if the statement asks for an interpretation in which it holds
                              (to be satisfied), 0 if it claims to hold in all of them */
  int conditional;         /* 1 if the text after the formula restricts the claim in a way the
                              reader did not understand: a counterexample is then not conclusive */
  int remark;              /* 1 if a parenthesised remark after the formula was skipped */
} QrVerdict;

/** Prepares the engine. To be called once, before anything else. */
void qr_init(void);

/**
 * Finds the next \item of a LaTeX document, starting at *position. If there
 * is one, sets [*item, *end) to its text, moves *position past it and returns
 * 1; otherwise returns 0.
 */
int qr_next_item(const char** position, const char** item, const char** end);

/**
 * Extracts the formula of the item [item, end). Returns NULL and sets
 * *formula if the item is a usable statement; otherwise returns the reason
 * (Italian) and leaves *formula alone.
 */
const char* qr_item_formula(const char* item, const char* end, const char** formula);

/**
 * Decides the statement in the item [item, end) of a document.
 *
 * With delegate_logic != 0 a statement of first-order logic over arbitrary
 * sets comes back as QR_LOGIC instead of being decided by the engine's own
 * procedures; with 0 the engine decides everything it can.
 */
QrVerdict qr_decide_item(const char* item, const char* end, int delegate_logic);

/** As qr_decide_item(), for a bare formula that is not inside an \item. */
QrVerdict qr_decide_formula(const char* formula, int delegate_logic);

/**
 * A finite interpretation of a statement that was handed over (QR_LOGIC),
 * as plain data. Everything is in the order of the lines of
 * QrVerdict::logic: one size for each "sort" line, one table for each
 * "symbol" line.
 *
 * A table has one cell for every choice of the arguments of its symbol,
 * the first argument changing fastest: for an operation on a set of 2
 * elements the cells are (0,0), (1,0), (0,1), (1,1). A cell holds the value
 * as the number of an element of the range, from 0, or 1 and 0 for true and
 * false. A named element has one cell.
 */
typedef struct {
  unsigned sorts;               /* how many sets */
  const size_t* sizes;          /* the number of elements of each */
  unsigned symbols;             /* how many declared symbols */
  const size_t* const* tables;  /* the table of each */
  const size_t* cells;          /* how many cells each table has */
} QrModel;

/**
 * Judges a finite model found outside the engine for the statement in the
 * item [item, end), which must be one that qr_decide_item() handed over.
 *
 * The model is loaded into the engine's structure for models and from there
 * on it is treated as a model the engine found itself: the hypotheses and
 * the claim are recomputed in it, and so is the statement as it is written,
 * before the notation was unfolded; it is written out for a reader and as a
 * certificate, which the independent checker must accept. Nothing of what
 * comes in is trusted.
 *
 * The verdict is QR_REFUTED (a counterexample) or, for a statement that
 * wants an example, QR_PROVED, in both cases with certified set; or
 * QR_NOT_PROVED with the reason, if the data is not an interpretation of
 * the statement or the statement does not have in it the value claimed.
 */
QrVerdict qr_adopt_model(const char* item, const char* end, const QrModel* model);

/**
 * The clauses from which the independent checker starts a proof by
 * saturation of the statement in the item [item, end), which was handed
 * over. The verdict is QR_LOGIC and its logic field holds, in this order:
 *
 *   - the beginning of a certificate "saturation" for the statement, up to
 *     and including its line "clausify" (or "clausify forward"), and, if
 *     the statement quantifies over the parts of a set, the lines
 *     "comprehend" of the instances that can be proposed without a search:
 *     the empty part and the whole set, and the parts that the ground
 *     literals of the statement suggest (a first-order prover cannot choose
 *     a part by itself; each instance only says "what holds for every part
 *     holds for this one");
 *   - a line "symbols N" and N lines "ARITY PREDICATE" (PREDICATE is 1 or
 *     0), one for each symbol of the translation, in the order of their
 *     numbers: the declared symbols, one predicate per set saying "is an
 *     element of it" (the sets may be empty), the Skolem functions, the
 *     names of subformulas;
 *   - a line "clauses M" and M lines "(clause LITERAL...)", the clauses
 *     the checker has after that beginning, in the order of their indices,
 *     written as the checker reads them: (pos T), (neg T), (eq T T),
 *     (ne T T), with terms (f N T...) and variables (v N).
 *
 * The numbers and the indices are the ones the checker rebuilds by itself
 * from the first part, so a refutation of these clauses whose steps are
 * written after that part is a certificate the checker can check. The
 * logic field is NULL if the statement has no such translation (it speaks
 * of a bijection between sets).
 *
 * For a statement that wants an example of a condition E, the statement of
 * the certificate is "not E" and the clauses are those of E: a refutation
 * of them certifies that there is no example, which is the only thing a
 * refutation can say about such a statement.
 */
QrVerdict qr_clauses_item(const char* item, const char* end);

/**
 * A statement with quantifiers over numbers, handed over for the arithmetic
 * theories of a first-order prover: the statement in the item [item, end),
 * which the engine can read and could not decide. The verdict is QR_LOGIC
 * and its logic field holds a line "numbers int", "numbers rat" or
 * "numbers real" (every variable of the statement ranges over integers, or
 * every one over rationals, or every one over reals) and the statement in a
 * prefix notation:
 *
 *     (forall (var N) SET C)  (exists (var N) SET C)
 *     SET = (set [ge L | gt L] [except P/Q]...)      a lower bound, points removed
 *     (and C C) (or C C) (implies C C) (iff C C) (not C)
 *     (= E E) (neq E E) (less E E) (lesseq E E)
 *     (in E SET)                                      E satisfies the bound and avoids the points
 *     (divides E E)                                   the second is the first times an integer
 *     E = N | (var N) | (add E E) | (sub E E) | (neg E) | (mul E E) | (pow E K) | (div E N)
 *
 * with N a non-negative integer, K from 1 to 16, and (div E N) only among
 * rationals and reals, by a positive integer. The logic field is NULL if
 * the statement is outside this fragment (declared maps, parameters, pairs,
 * functions, variables of different kinds, an exponent that is a letter, a
 * division by an expression): then it stays the engine's alone.
 *
 * The engine decides nothing here, and has no checker for what a prover
 * finds on this text: a proof found there is found, not verified.
 */
QrVerdict qr_numbers_item(const char* item, const char* end);

/**
 * Writes a proof that the independent checker accepts for the statement in
 * the item [item, end), which was handed over and has been PROVED outside
 * the engine. The engine does not search for models with its SAT finder
 * here: whether the statement is a theorem is already known, what is asked
 * for is a proof in a form that can be rechecked.
 *
 * The verdict is QR_PROVED with certified set if a certificate was written
 * and accepted, QR_NOT_PROVED if the engine could not rebuild a proof. It is
 * QR_REFUTED only if the engine's check on small models found a
 * counterexample, which contradicts the proof found outside: the caller
 * must then report neither.
 */
QrVerdict qr_certify_item(const char* item, const char* end);

/**
 * The LaTeX commands the frontend reads as names of symbols, without the
 * backslash, in three lists: the operations written between their arguments
 * ("perp" for \perp), the order relations written between their arguments
 * ("le" for \le), and the Greek letters. A symbol written with one of them
 * carries its letters as its name wherever the statement goes (to Vampire,
 * into a certificate): whoever shows the symbol to a reader again asks here
 * which names are commands, so that the lists exist once.
 *
 * Returns the list and sets *count to its length. The strings are the
 * engine's and are never freed.
 */
typedef enum { QR_COMMANDS_OPERATIONS, QR_COMMANDS_RELATIONS, QR_COMMANDS_GREEK } QrCommands;
const char* const* qr_symbol_commands(QrCommands list, size_t* count);

/**
 * How many proof steps failed the engine's internal rechecks and were
 * discarded since qr_init(). Zero in a healthy run: anything else is an
 * error of the engine that the caller must report.
 */
int qr_unjustified_steps(void);

/* The final document: statements, worked solutions, proofs and plots.
 *
 * qr_document_open() starts the LaTeX document at path (a name ending in
 * ".pdf" also asks for the PDF, compiled at closing); explanations != 0 asks
 * the engine to record the steps of its computations, which the document
 * then shows before each proof. Returns NULL, or the problem (Italian).
 * Only one document can be open. */
const char* qr_document_open(const char* path, int explanations);
void qr_document_section(const char* title);
void qr_document_list(int opening);

/** Adds the item just decided by qr_decide_item(), with its plot and its worked solution. */
void qr_document_item(const char* item, const char* end);

/**
 * Adds an item decided outside the engine (by Vampire). proof is its written
 * account in LaTeX, or NULL; the other arguments have the meaning of the
 * fields of QrVerdict, and certificate is non-NULL only if the checker
 * accepted it.
 */
void qr_document_external_item(const char* item, const char* end, QrOutcome outcome, const char* method,
                               const char* reason, const char* detail, const char* proof, const char* certificate);

/** Closes the document and, if asked, compiles it. Returns NULL, or the problem (Italian). */
const char* qr_document_close(void);

#ifdef __cplusplus
}
#endif

#endif /* __Math_Engine__ */
