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
 * @file IndependentChecker.c
 * The translation unit of the independent checker (IndependentChecker.h).
 *
 * The checker's source is included whole, without its command-line main():
 * everything in it is static, and its one entry point, ck_check(), is
 * wrapped below. This file includes nothing else of the program, which is
 * the point: this is the only place where the checker is compiled, and
 * what uses it (the mathematical engine for its own proofs, the driver for
 * what Vampire finds) sees the two functions of the interface and nothing
 * of what is inside.
 */

#define CK_NO_MAIN
#include "Math/quaerens/checker.c"

#include "IndependentChecker.h"

ProofCheck proof_check_next(const char** text, const char** why, long long steps)
{
  const char* reason = "";
  CkAnswer answer = ck_check(text, &reason, steps);
  if (why) *why = reason;
  return answer == CK_ACCEPTED ? PROOF_CHECK_ACCEPTED : answer == CK_REJECTED ? PROOF_CHECK_REJECTED : PROOF_CHECK_UNKNOWN;
}

ProofCheck proof_check_certificate(const char* certificate, const char** why)
{
  /* Zero asks for the checker's usual budget of work on a model. */
  const char* text = certificate;
  return proof_check_next(&text, why, 0);
}
