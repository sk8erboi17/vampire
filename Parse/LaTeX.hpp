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
 * @file LaTeX.hpp
 * The LaTeX frontend: mathematical statements written as in a textbook.
 *
 * The input is either a LaTeX document whose statements are the \item
 * entries of its lists, each with one displayed formula, or a single bare
 * formula. Unlike the TPTP and SMT-LIB parsers, this frontend does not
 * always end in a list of units for the prover: what a statement is decides
 * where it goes.
 *
 *   - A statement of first-order logic over arbitrary sets (elements, maps,
 *     relations, quantifiers) is unfolded, typed (Math::LogicStatement) and
 *     translated into units for Vampire.
 *   - A statement of mathematics proper (an identity by induction, an
 *     inequality, a limit, a derivative, a matrix, ...) has no faithful
 *     translation into first-order logic that Vampire could use; it goes to
 *     the algorithm made for it, in the mathematical engine.
 *   - A statement the frontend cannot read is reported as such, with the
 *     reason. Nothing is guessed: an ambiguous writing is refused, never
 *     silently read one way.
 *
 * The reading itself (tokens, grammar, the notation of the books) is done
 * by the engine in Math/quaerens/parser.c, through Math/Engine.h; this
 * class is the face of it that the rest of Vampire sees.
 */

#ifndef __Parse_LaTeX__
#define __Parse_LaTeX__

#include <string>

#include "Math/Engine.h"
#include "Math/LogicStatement.hpp"

namespace Parse {

class LaTeX {
public:
  /** A statement of the input, as text. */
  struct Item {
    unsigned number = 0;   // 1, 2, 3, ... in the order of the input
    std::string text;      // the text of the \item, or "$\displaystyle F$" for a bare formula F
    std::string formula;   // the formula alone, as written; empty if the item has none that can be used
    std::string unreadable;// why the item is not a usable statement (in the engine's words), or empty
    bool bare = false;     // the input was a single formula, not a document
  };

  /** What a statement turned out to be. */
  enum class Kind {
    LOGIC,        // first-order logic: logic holds the typed statement
    MATHEMATICS   // everything else: verdict holds what the engine established
  };

  /** A statement read and classified. */
  struct Statement {
    Kind kind = Kind::MATHEMATICS;
    QrVerdict verdict = {};        // MATHEMATICS: the engine's verdict (strings valid until the next reading)
    Math::LogicStatement logic;    // LOGIC: the statement, first-order over plain sorts
    bool conditional = false;      // LOGIC: a condition after the formula was not read, so a counterexample is not conclusive
    bool engineHadNoAnswer = false;// LOGIC: the engine went first on this statement and neither proved nor refuted it;
                                   // verdict holds what it said, and Vampire is asked for a proof
    std::string notTranslated;     // MATHEMATICS reached from logic: why the statement was not given to Vampire, or empty
  };

  /** @param text the whole input. The frontend keeps a copy. */
  explicit LaTeX(std::string text);

  /** Finds the next statement of the input. Returns false when there are no more. */
  bool next(Item& item);

  /**
   * Reads and classifies an item, and gives the first turn on it to
   * whichever part of the program does better on its kind (the measures
   * are in Math/README.md).
   *
   *   - First-order logic over plain sets: LOGIC. Vampire leads; the engine
   *     judges the models it finds and rebuilds its proofs as certificates
   *     (Math/Driver.cpp).
   *   - Logic with sets of all the parts or of all the maps of a set, or
   *     with written numbers: the engine leads, because a model there must
   *     have every part and every map, and a proof must choose the parts
   *     it needs. If it proves or refutes, that is the verdict
   *     (MATHEMATICS). If it has no answer the statement comes back as
   *     LOGIC with engineHadNoAnswer set, and Vampire is asked for a proof
   *     from the laws of those sets that the engine supplies.
   *   - Everything else is the engine's alone (MATHEMATICS): mathematics
   *     proper, a statement that only computes with the numbers it writes,
   *     and logic with no first-order form (a quantifier over parts that
   *     are not a set of the statement, a bijection between two sets).
   */
  Statement read(const Item& item);

  /** True if a file with this name is LaTeX by its extension. */
  static bool isLatexFile(const std::string& name);

private:
  std::string _text;
  const char* _position;
  unsigned _count = 0;
  bool _bareDone = false;
  bool _anyItem = false;
};

} // namespace Parse

#endif // __Parse_LaTeX__
