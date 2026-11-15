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

#ifdef __cplusplus
}
#endif

#endif /* __Proof_IndependentChecker__ */
