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
