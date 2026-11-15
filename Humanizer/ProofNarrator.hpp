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
 * @file ProofNarrator.hpp
 * Tells a refutation found by Vampire as a proof a person can follow.
 *
 * A refutation is a graph: every formula in it is either an input (a
 * hypothesis, the negated claim) or was obtained from earlier formulas by a
 * named rule. The narrator writes it out in order, in LaTeX, as a numbered
 * list in which every step shows the formula, says in plain words what the
 * rule does, and cites the steps it used.
 *
 * THE ONE RULE OF THIS CLASS: nothing is told that is not in the proof.
 * Every step of the account is one step of Vampire's refutation, with the
 * formula Vampire derived and the premises Vampire recorded; the words
 * describe the rule Vampire named and nothing more. A rule this class has
 * no description for is cited by its name. Steps are never merged, guessed
 * or reordered beyond the order of derivation, and the account ends by
 * saying that it has not been rechecked by the independent checker.
 *
 * The account is in English or in Italian.
 */

#ifndef __Humanizer_ProofNarrator__
#define __Humanizer_ProofNarrator__

#include <map>
#include <string>

#include "Forwards.hpp"
#include "Math/Verification.hpp"

namespace Humanizer {

class ProofNarrator {
public:
  explicit ProofNarrator(Math::Language language) : _language(language) {}

  /**
   * Gives an input formula the name a reader will see, e.g. "hypothesis 1".
   * An input without a label is called by what Vampire says it is (axiom,
   * negated conjecture).
   */
  void label(const Kernel::Unit* input, const std::string& label) { _labels[input] = label; }

  /**
   * The account of the refutation ending in @b refutation, as LaTeX text
   * to be placed inside a document: an opening sentence on the method, the
   * numbered steps, the conclusion.
   */
  std::string narrate(Kernel::Unit* refutation) const;

  /** A formula or clause of Vampire as LaTeX mathematics (without the dollars). */
  static std::string latex(Kernel::Unit* unit);

private:
  Math::Language _language;
  std::map<const Kernel::Unit*, std::string> _labels;

  std::string ruleSentence(const std::string& rule) const;
};

} // namespace Humanizer

#endif // __Humanizer_ProofNarrator__
