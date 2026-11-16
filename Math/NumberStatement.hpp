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
 * rationals and the reals. But the independent checker cannot follow such a
 * proof: it has no steps for arithmetic. A theorem found this way is found,
 * not verified, and the caller must say so, with one exception.
 *
 * WITNESSES. Some statements are settled by a few numbers. "For all x, y:
 * if x = k^2 + 7 for some k and y = j^2 + 7 for some j, then x = y" is
 * false, and x = 7, y = 8, k = 0, j = 1 show it: the checker only has to
 * recompute the statement on them (its certificate "numbers"). That works
 * when what has to be shown needs only values to exhibit: a "there is" to
 * be true, a "for all" to be false, each in a place of the statement where
 * that is what counts. Then the problem given to Vampire is written with
 * those quantifiers moved to the front as one "there are X, Y, K, J such
 * that ...", which says the same (the sorts are not empty), and Vampire is
 * asked not only for a proof but for the values (question answering):
 * witnessProblem(). With the values, certificate() writes what the checker
 * rechecks. A "for all" that is true, or a "there is" that is false, cannot
 * be shown by values. The checker settles one by itself in a single case:
 * an innermost quantifier over one integer, once every other variable has
 * a value, by trying every integer that can matter (its complete count).
 * Such a quantifier is left where it is, and Vampire is asked for the
 * values of the others; in every other case there is no witness problem.
 */

#ifndef __Math_NumberStatement__
#define __Math_NumberStatement__

#include <string>
#include <vector>

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

  /** A problem whose proof comes with numbers that settle the statement. */
  struct WitnessProblem {
    std::string tptp;                  // one conjecture "?[W..]: ...", or empty if values cannot settle the statement
    std::vector<unsigned> quantifiers; // for each variable of that conjecture, in order, the quantifier of the
                                       // statement it stands for, counted from 0 in the order they are written
    std::vector<std::string> letters;  // and the letter that quantifier binds, for a reader
    unsigned counted = 0;              // quantifiers left in place for the checker to settle by its complete count
  };

  /**
   * The statement (or, with @b denied, its negation) as a problem that
   * values can settle, if it is one: every quantifier that has to be used
   * is a "there is" to be made true or a "for all" to be made false, or
   * is an innermost quantifier over one integer, which the checker settles
   * by itself once the others have their values.
   */
  WitnessProblem witnessProblem(bool denied) const;

  /**
   * The certificate "numbers" that says the statement holds (or, with
   * @b denied, fails) and gives @b values, written as the checker reads
   * numbers ("7", "-3", "1/2"), to the quantifiers of @b problem.
   */
  std::string certificate(bool denied, const WitnessProblem& problem, const std::vector<std::string>& values) const;

  /**
   * Reads a number as Vampire writes one in an answer ("7", "-3", "1/2",
   * "$to_real(1/2)") into the checker's notation. Returns false for
   * anything else: an answer that is not a number is not a witness.
   */
  static bool answerValue(const std::string& answer, std::string& value);

private:
  std::string _sort;     // of every variable and term
  std::string _formula;  // the statement in TPTP syntax, without the surrounding tff(...); empty if not read
  std::string _text;     // the statement as it was handed over, one line, for the certificate and for a second reading
  int _kind = 0;         // 1 integers, 2 rationals, 3 reals
};

} // namespace Math

#endif // __Math_NumberStatement__
