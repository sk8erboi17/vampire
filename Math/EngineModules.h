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
 * @file EngineModules.h
 * What the mathematical engine sees of the independent checker when the
 * checker is a module of its own.
 *
 * In Quaerens the engine includes checker.c in its one translation unit and
 * uses, by rule, only its entry point ck_check() and the three answers. In
 * Vampire the checker is compiled once, apart (Proof/IndependentChecker),
 * and judges both what the engine proves and what Vampire finds. The modules
 * of the engine include this header (through engine_foundations.h) instead
 * of checker.c: the same names, given by the module's interface. The rule
 * "the engine uses nothing else of the checker" is then a fact of the
 * build: nothing else is there to use.
 */

#ifndef __Math_EngineModules__
#define __Math_EngineModules__

#include "Proof/IndependentChecker.h"

/* The names the engine uses (13h in Math/quaerens/engine_foundations.h). */
typedef ProofCheck CkAnswer;
#define CK_ACCEPTED PROOF_CHECK_ACCEPTED
#define CK_REJECTED PROOF_CHECK_REJECTED
#define CK_UNSUPPORTED PROOF_CHECK_UNKNOWN

/** ck_check() of checker.c, through the module: same contract (Proof/IndependentChecker.h, proof_check_next()).
 *  Inline, because every module of the engine reads this header and not all of them call it. */
static inline CkAnswer ck_check(const char **text, const char **why, long long steps)
{
  return proof_check_next(text, why, steps);
}

#endif /* __Math_EngineModules__ */
