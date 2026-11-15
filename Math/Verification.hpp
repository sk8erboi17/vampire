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
 * @file Verification.hpp
 * What is known about a mathematical statement, and how far it was checked.
 *
 * Two questions are kept apart on purpose:
 *
 *   - WHAT was established: a theorem, a computed result (the solutions of
 *     an equation, a derivative), a counterexample, or nothing;
 *   - WHO CONFIRMED IT: the independent checker (Math/quaerens/checker.c),
 *     which shares no code with what found the result, or nobody else.
 *
 * A proof printed by Vampire is NOT certified by being printed: until the
 * checker can replay it, a theorem found by saturation is THEOREM_UNVERIFIED.
 * A finite model found by Vampire, instead, is rewritten as a certificate
 * and recomputed by the checker: only then is it COUNTEREXAMPLE_VERIFIED.
 * A numerical test never makes a theorem: the engine does not report one on
 * such grounds, and nothing here upgrades a status.
 */

#ifndef __Math_Verification__
#define __Math_Verification__

namespace Math {

enum class Status {
  THEOREM_CERTIFIED,         // theorem proved, certificate accepted by the independent checker
  THEOREM_UNVERIFIED,        // a proof was found, the checker did not confirm it
  RESULT_VALIDATED,          // result computed, certificate accepted by the independent checker
  RESULT_UNVERIFIED,         // result computed and reread by the engine, not confirmed by the checker
  COUNTEREXAMPLE_VERIFIED,   // counterexample recomputed and accepted by the independent checker
  COUNTEREXAMPLE_UNVERIFIED, // the statement was refuted, the checker did not confirm it
  UNSOLVED,                  // neither proved nor refuted within the limits
  UNSUPPORTED                // outside the fragment the program reads
};

/** The languages of the reports. */
enum class Language { ENGLISH, ITALIAN };

/** The name of a status, for a reader. */
inline const char* statusName(Status status, Language language)
{
  bool italian = language == Language::ITALIAN;
  switch (status) {
    case Status::THEOREM_CERTIFIED:         return italian ? "teorema dimostrato e certificato" : "theorem proved and certified";
    case Status::THEOREM_UNVERIFIED:        return italian ? "prova trovata ma non verificata indipendentemente" : "proof found but not independently verified";
    case Status::RESULT_VALIDATED:          return italian ? "risultato calcolato e validato" : "result computed and validated";
    case Status::RESULT_UNVERIFIED:         return italian ? "risultato calcolato ma non verificato indipendentemente" : "result computed but not independently verified";
    case Status::COUNTEREXAMPLE_VERIFIED:   return italian ? "controesempio verificato" : "counterexample verified";
    case Status::COUNTEREXAMPLE_UNVERIFIED: return italian ? "confutazione trovata ma non verificata indipendentemente" : "refutation found but not independently verified";
    case Status::UNSOLVED:                  return italian ? "problema non risolto" : "problem not solved";
    case Status::UNSUPPORTED:               return italian ? "frammento non supportato" : "fragment not supported";
  }
  return "";
}

/** A short fixed word for each status, for scripts: it does not depend on the language. */
inline const char* statusCode(Status status)
{
  switch (status) {
    case Status::THEOREM_CERTIFIED:         return "TheoremCertified";
    case Status::THEOREM_UNVERIFIED:        return "TheoremUnverified";
    case Status::RESULT_VALIDATED:          return "ResultValidated";
    case Status::RESULT_UNVERIFIED:         return "ResultUnverified";
    case Status::COUNTEREXAMPLE_VERIFIED:   return "CounterexampleVerified";
    case Status::COUNTEREXAMPLE_UNVERIFIED: return "CounterexampleUnverified";
    case Status::UNSOLVED:                  return "Unsolved";
    case Status::UNSUPPORTED:               return "Unsupported";
  }
  return "";
}

/** The SZS status that says the same, as far as the SZS ontology can. */
inline const char* statusSZS(Status status)
{
  switch (status) {
    case Status::THEOREM_CERTIFIED:
    case Status::THEOREM_UNVERIFIED:        return "Theorem";
    case Status::RESULT_VALIDATED:
    case Status::RESULT_UNVERIFIED:         return "Success";
    case Status::COUNTEREXAMPLE_VERIFIED:
    case Status::COUNTEREXAMPLE_UNVERIFIED: return "CounterSatisfiable";
    case Status::UNSOLVED:                  return "GaveUp";
    case Status::UNSUPPORTED:               return "Inappropriate";
  }
  return "";
}

/** True for the statuses that settle the statement in the positive: a theorem or a computed result. */
inline bool statusPositive(Status status)
{
  return status == Status::THEOREM_CERTIFIED || status == Status::THEOREM_UNVERIFIED
      || status == Status::RESULT_VALIDATED || status == Status::RESULT_UNVERIFIED;
}

} // namespace Math

#endif // __Math_Verification__
