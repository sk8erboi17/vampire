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
 * @file IndependentChecker.h
 * The independent checker of certificates, as a module of its own.
 *
 * A certificate is a text in a small fixed language: a statement and the few
 * data needed to recheck its proof, or a finite interpretation in which it
 * is false. The checker (Math/quaerens/checker.c) reads one and accepts it,
 * rejects it, or says it cannot check it. Finding a proof is hard, checking
 * one is easy: that is why the checker can be small, and why it is trusted
 * more than what found the proof.
 *
 * It is compiled here as its own translation unit, apart from the
 * mathematical engine and from Vampire: it uses the C standard library and
 * nothing else, has its own reader, its own arithmetic and its own
 * polynomials, and shares no state with either. What Vampire finds is judged
 * through this interface, never through the engine.
 *
 * The same source also builds as a program (target certificate-checker),
 * so that a file of certificates can be rechecked without this executable.
 *
 * WHAT AN ACCEPTED CERTIFICATE PROVES is stated, kind by kind, in the
 * comment at the top of Math/quaerens/checker.c. For the two kinds written
 * from Vampire's models: "certificate counterexample", the statement is
 * false in the finite interpretation given by the tables, so it does not
 * hold for every choice of the sets and symbols; "certificate example",
 * there are sets, with the sizes given, and symbols for which it holds.
 */

#ifndef __Proof_IndependentChecker__
#define __Proof_IndependentChecker__

#ifdef __cplusplus
extern "C" {
#endif

/** The three answers of the checker. The third is not a yes. */
typedef enum {
  PROOF_CHECK_ACCEPTED,  /* every check passed */
  PROOF_CHECK_REJECTED,  /* a check failed: the certificate is wrong */
  PROOF_CHECK_UNKNOWN    /* the certificate uses something the checker does not know, the numbers
                            are too large, or the work budget ran out */
} ProofCheck;

/**
 * Checks one certificate, a zero-terminated text ending with its "end"
 * line. On an answer other than PROOF_CHECK_ACCEPTED, *why (if not NULL)
 * receives the reason, in the checker's words (Italian); the string belongs
 * to the checker and is valid until the next call.
 *
 * Not re-entrant: the checker has one state.
 */
ProofCheck proof_check_certificate(const char* certificate, const char** why);

/**
 * Checks the certificate that begins at *text and moves *text just past
 * its "end" line, so that a text holding several certificates can be
 * checked one after the other. *why receives the reason when the answer is
 * not PROOF_CHECK_ACCEPTED. @b steps is the budget of work for recomputing
 * a finite model (how many elements the quantifiers may try); zero or less
 * asks for the usual one. The budget says how much the checker is willing
 * to compute, never what it accepts: past it the answer is
 * PROOF_CHECK_UNKNOWN.
 *
 * This is the entry point the mathematical engine uses (ck_check() of
 * checker.c), now that it no longer holds a copy of the checker.
 */
ProofCheck proof_check_next(const char** text, const char** why, long long steps);

/**
 * For whoever writes a certificate "arithmetic" or "infinite" (chapters
 * 20f and 20g of Math/quaerens/checker.c): the clauses the checker starts
 * from.
 *
 * @b beginning is the beginning of such a certificate, up to and including
 * its line "clausify" and any line "step" after it, followed by "end". The
 * checker reads it as it reads a certificate (it translates the statement,
 * adds the laws of the integers, makes the clauses and follows the steps)
 * and, if nothing in it is wrong, the result is a text on the heap, to be
 * released with free(), of these lines:
 *
 *     claim C               for a certificate "infinite" only: the statement
 *                           about integers the checker made of it (20g), the
 *                           one whose proof is then checked, in the notation of
 *                           qr_numbers_item()
 *     numerals V0 V1 ...    the value of each numeral of the translation, in the
 *                           order of their symbols, which come after add, neg,
 *                           mul and less (0, 1, 2, 3)
 *     symbols N             then N lines "ARITY PREDICATE", one per symbol of the
 *                           translation in the order of their numbers
 *     clauses M             then M lines "(clause LITERAL...)", the clauses the
 *                           checker has at the end of the beginning, by index
 *
 * which is what Proof::Replay reads after the beginning (without the lines
 * claim and numerals). NULL otherwise, with the reason in *why (if not NULL).
 *
 * WHY THIS IS NOT A WEAKNESS. A certificate by saturation starts from
 * clauses that the checker builds from the statement; whoever writes the
 * steps must know them exactly, with the checker's numbers. For logic the
 * engine computes them with code of its own that mirrors the checker's
 * (Engine.h, qr_clauses_item()); here they are asked of the checker. Either
 * way they must be the very clauses the checker will build, or the steps
 * are rejected: a mirror can only agree with the checker, and agreeing
 * with an error of the checker protects from nothing. What is accepted
 * depends on the finished certificate alone, which proof_check_certificate()
 * reads from the start, and the checker is right or wrong about it whatever
 * the clauses were used for.
 */
char* proof_arithmetic_clauses(const char* beginning, const char** why);

#ifdef __cplusplus
}
#endif

#endif /* __Proof_IndependentChecker__ */
