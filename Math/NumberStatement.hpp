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
 * @file NumberStatement.hpp
 * A statement with quantifiers over numbers, as the mathematical engine
 * hands it over, turned into a problem for Vampire's arithmetic theories.
 *
 * WHAT IT IS FOR. "For all integers a, b, c: if (ab - 2)(a - b) = 0 and
 * (bc - 2)(b - c) = 0 then (ac - 2)(a - c) = 0." The engine reads such a
 * statement, and its rules for quantifiers may not be enough to prove or
 * refute it. Vampire reasons in the theories of the integers, the rationals
 * and the reals. The engine hands the statement over (Engine.h,
 * qr_numbers_item()) and this class writes it as a TPTP problem, which
 * Vampire's own parser reads: the terms, the sorts and the interpreted
 * symbols are then Vampire's, built by Vampire.
 *
 * WHY IT MEANS THE SAME. The engine hands over only statements in which
 * every variable ranges over numbers of one kind, so that one sort of
 * Vampire is the sort of everything: $int for the integers, $rat for the
 * rationals, $real for the reals. No number is ever moved from one sort to
 * another. A set of numbers is that sort with a lower bound and some points
 * removed, and a quantifier over it is the quantifier over the sort with
 * those conditions:
 *
 *     for every x in N, C     becomes     ![X:$int]: ($greatereq(X,1) => C)
 *     there is x in N, C      becomes     ?[X:$int]: ($greatereq(X,1) & C)
 *
 * Sum, difference, opposite and product are the interpreted functions. A
 * power with a written exponent k from 1 to 16 is the product of k copies.
 * A division, among rationals and reals only, is by a written positive
 * integer: $quotient with a non-zero numeral, the exact division of the
 * field. "u divides v", among integers only, is "v is u times an integer",
 * so that zero divides only zero: that is the engine's own definition.
 *
 * WHAT A PROOF FOUND THIS WAY IS WORTH. Vampire's theories of arithmetic are
 * sound: what it proves of $int, $rat and $real holds of the integers, the
 * rationals and the reals. But nothing rechecks such a proof here: the
 * independent checker has no language for arithmetic with quantifiers. A
 * theorem found this way is found, not verified, and the caller must say so.
 */

#ifndef __Math_NumberStatement__
#define __Math_NumberStatement__

#include <string>

namespace Math {

class NumberStatement {
public:
  /**
   * Reads what the engine hands over. Whatever the text contains the
   * result is safe to use: if it is not what is described in Engine.h,
   * ok() is false and there is no problem to give to Vampire.
   */
  static NumberStatement read(const std::string& handedOver);

  bool ok() const { return !_formula.empty(); }

  /** The sort of every variable and every term: "$int", "$rat" or "$real". */
  const std::string& sort() const { return _sort; }

  /**
   * The problem as one TPTP formula: the statement as a conjecture, or,
   * with @b denied, its negation as a conjecture. A refutation found by
   * Vampire proves the statement in the first case and refutes it in the
   * second.
   */
  std::string tptp(bool denied) const;

private:
  std::string _sort;     // of every variable and term
  std::string _formula;  // the statement in TPTP syntax, without the surrounding tff(...); empty if not read
};

} // namespace Math

#endif // __Math_NumberStatement__
