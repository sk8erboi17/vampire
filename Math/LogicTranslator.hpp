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
 * @file LogicTranslator.hpp
 * Turns a statement read from LaTeX (LogicStatement) into a Vampire problem.
 *
 * WHAT IS TRANSLATED, AND WHY IT MEANS THE SAME
 *
 * A LogicStatement holds in every interpretation in which the sets may be
 * EMPTY. Vampire's sorts never are. Translating sort for sort would
 * therefore prove too much: "for every x in S there is y in S with x = y
 * implies there is an element of S" holds in every non-empty S and fails in
 * the empty one.
 *
 * The translation keeps the difference with one proposition per sort,
 * inhabited_S, "S has an element":
 *
 *     for every x in S, C     becomes     inhabited_S  =>  ![X:S]: C'
 *     there is x in S, C      becomes     inhabited_S  &   ?[X:S]: C'
 *
 * and with one axiom for each function symbol f: S1 x ... x Sn -> T, saying
 * that a total map into T makes T inhabited as soon as its arguments exist:
 *
 *     inhabited_S1 & ... & inhabited_Sn  =>  inhabited_T.
 *
 * CLAIM. The statement holds in every interpretation with possibly empty
 * sets if and only if its translation follows from these axioms in ordinary
 * many-sorted logic.
 * PROOF. From an interpretation I with possibly empty sets build an ordinary
 * one J: inhabited_S is true exactly when S is not empty in I; a non-empty
 * set is itself; an empty set becomes a one-element set, on which the
 * symbols are defined at will. The axioms hold in J because a total map
 * from non-empty sets into T exists in I only if T is not empty. A guarded
 * quantifier over an empty set has in J the value it has in I (true for
 * "every", false for "there is") whatever is under it, and a quantifier
 * over a non-empty set ranges over the same elements: by induction every
 * condition has the same value in I and in J. Conversely, from an ordinary
 * J satisfying the axioms take I with S empty exactly when inhabited_S is
 * false; the axioms say that every symbol of I is then a total map between
 * the sets of I, and the same induction applies. So the statement fails in
 * some I exactly when the translation fails in some J satisfying the
 * axioms.  QED
 *
 * Two simplifications, both covered by the proof above: a sort with a named
 * element, or reached by a function from such sorts, is never empty and
 * gets no proposition; and inside the scope of a variable of sort S the
 * guard on S is omitted, because there S is not empty.
 *
 * HYPOTHESES AND CLAIM. A statement "H1 and ... and Hn implies C" becomes
 * the axioms H1, ..., Hn and the conjecture C, which is the same theorem
 * and lets Vampire treat the goal as a goal. A statement that wants an
 * example has no conjecture: it is an axiom to be satisfied.
 *
 * SETS OF PARTS, SETS OF MAPS, WRITTEN NUMBERS. In the statement a set of
 * parts is the set of ALL the parts of its base, and a set of maps the set
 * of ALL the maps between two sets. First-order logic cannot say "all": the
 * translation gives each of them an ordinary sort, with its structure
 * symbol (membership, application), and the LAWS the engine supplies with
 * the statement as axioms: two parts with the same elements are the same
 * part, the elements satisfying such and such a condition are a part, and
 * so on. Every intended interpretation satisfies the laws, so
 *
 *     what Vampire proves from the laws holds in every intended
 *     interpretation: a proof is a proof.
 *
 * The converse fails, and callers must not use it: the laws are finitely
 * many, and a model of them may lack parts or maps that really exist. So
 * for such a statement a saturation without a contradiction says NOTHING
 * about the statement, and a finite model found by Vampire is not a
 * counterexample (LogicStatement::plainOnly() tells the two kinds apart).
 * Counterexamples for these statements come from the engine's model finder,
 * which builds the real sets of parts and of maps.
 *
 * On emptiness: a set of parts is never empty (the empty part is there),
 * so it gets no proposition; a set of maps from S to T is empty exactly
 * when S has an element and T has none, which is one more axiom,
 * inhabited_M <=> (~inhabited_S | inhabited_T), true in every intended
 * interpretation. The written numbers are named elements, declared distinct
 * and declared to be all the elements of their sort.
 *
 * WHAT IS NOT TRANSLATED. A quantifier on the parts of a set that is not
 * itself a set of the statement, and equipotence, have no first-order form
 * here: LogicStatement::outside() refuses them and they never reach this
 * class.
 */

#ifndef __Math_LogicTranslator__
#define __Math_LogicTranslator__

#include <string>
#include <vector>

#include "Forwards.hpp"
#include "Kernel/Term.hpp"

#include "LogicStatement.hpp"

namespace Math {

class LogicTranslator {
public:
  /**
   * The part an input formula plays, for whoever explains a proof.
   *   HYPOTHESIS  a hypothesis of the statement
   *   CLAIM       its claim (what enters the search is the negation)
   *   STATEMENT   the whole statement, when it wants an example
   *   INHABITED   "a total map into T makes T inhabited"
   *   LAW         a law of the sets of parts and of maps, given by the engine
   *   STRUCTURE   what a set is: the written numbers are distinct and are
   *               all there is; when a set of maps is empty
   */
  enum class Role { HYPOTHESIS, CLAIM, STATEMENT, INHABITED, LAW, STRUCTURE };

  /** An input formula of the problem: the unit, its part, and its name in the proofs. */
  struct Input {
    Kernel::Unit* unit;
    Role role;
    std::string name;
  };

  /** @param statement must be one that can be translated: statement.outside() is empty. It must outlive the translator. */
  explicit LogicTranslator(const LogicStatement& statement);

  /**
   * Declares the sorts and symbols in env.signature and builds the input
   * formulas. To be called once. The units are also in inputs().
   */
  Kernel::UnitList* translate();

  const std::vector<Input>& inputs() const { return _inputs; }
  bool hasConjecture() const { return !_statement.wantsExample(); }

  /** The Vampire sort (type constructor number) of the i-th sort of the statement. */
  unsigned sort(unsigned i) const { return _sorts[i].term()->functor(); }
  /** The Vampire function or predicate number of the i-th symbol of the statement. */
  unsigned symbol(unsigned i) const { return _symbols[i]; }
  /** True if the i-th sort may be empty, i.e. has an inhabited_S proposition. */
  bool mayBeEmpty(unsigned i) const { return _mayBeEmpty[i]; }
  /** The predicate number of inhabited_S for a sort that may be empty. */
  unsigned inhabited(unsigned i) const { return _inhabited[i]; }

private:
  const LogicStatement& _statement;
  std::vector<Kernel::TermList> _sorts;
  std::vector<unsigned> _symbols;
  std::vector<bool> _mayBeEmpty;
  std::vector<unsigned> _inhabited;
  std::vector<Input> _inputs;
  unsigned _nextVariable = 0;  // the first variable number not used by the statement

  void declare();
  Kernel::TermList term(const LogicStatement::Term& term) const;
  Kernel::Formula* formula(const LogicStatement::Formula& formula, std::vector<unsigned>& bound) const;
  Kernel::Formula* inhabitedFormula(unsigned sort) const;
  void addInput(Kernel::Formula* formula, Role role, const std::string& name);
};

} // namespace Math

#endif // __Math_LogicTranslator__
