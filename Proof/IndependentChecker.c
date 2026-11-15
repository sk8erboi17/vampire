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
 * the point: the copy of the checker that judges what Vampire finds is not
 * the one inside the mathematical engine's translation unit, and neither
 * can see the other.
 */

#define CK_NO_MAIN
#include "Math/quaerens/checker.c"

#include "IndependentChecker.h"

ProofCheck proof_check_certificate(const char* certificate, const char** why)
{
  const char* text = certificate;
  const char* reason = "";

  /* Zero asks for the checker's usual budget of work on a model. The
   * budget only says how much the checker is willing to compute, never
   * what it accepts: past it the answer is "cannot check". */
  CkAnswer answer = ck_check(&text, &reason, 0);
  if (why) *why = reason;
  return answer == CK_ACCEPTED ? PROOF_CHECK_ACCEPTED : answer == CK_REJECTED ? PROOF_CHECK_REJECTED : PROOF_CHECK_UNKNOWN;
}
