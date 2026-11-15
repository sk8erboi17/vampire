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
 * @file LogicStatement.hpp
 * The typed form of a statement of first-order logic read from LaTeX.
 *
 * A statement on arbitrary sets, once the LaTeX frontend has unfolded the
 * notation of the books, speaks of a few sets (sorts), of named elements,
 * maps and relations on them (symbols), and says something with the
 * connectives, the two quantifiers and equality. LogicStatement is that
 * statement as a typed tree: every term knows its sort, every symbol its
 * signature, every variable its binder.
 *
 * It is the meeting point of three parts that must agree on what the
 * statement means:
 *   - the LaTeX frontend (the engine in Math/quaerens/), which produces it;
 *   - LogicTranslator, which turns it into a Vampire problem;
 *   - LogicProblem, which reads a model found by Vampire as sizes and
 *     tables of this statement, for the engine to judge.
 *
 * MEANING. The statement is to hold in every interpretation: any choice of
 * the plain sets, finite or infinite and possibly EMPTY, of an element for
 * each name, a total map for each function symbol and a subset for each
 * relation. A set of parts is then the set of all the parts of its base, and
 * a set of maps the set of all the maps from its base to its target: an
 * interpretation does not choose them. A statement that "wants an example"
 * asks instead for one interpretation in which it holds.
 */

#ifndef __Math_LogicStatement__
#define __Math_LogicStatement__

#include <string>
#include <vector>

namespace Math {

class LogicStatement {
public:
  /** The range of a relation: it has no sort, it is a truth value. */
  static constexpr int BOOL = -1;

  /**
   * What a set of the statement is.
   *   PLAIN    any set: its elements are whatever an interpretation says
   *   PARTS    the set of ALL the parts (subsets) of the set base
   *   MAPS     the set of ALL the maps from the set base to the set target
   *   NUMBERS  the numbers the statement writes, all distinct, and nothing else
   * The last three are not chosen by an interpretation: once the plain sets
   * are given they are determined, with their structure symbol (membership
   * in a part, application of a map) or their named elements (the numbers).
   */
  enum class SortKind { PLAIN, PARTS, MAPS, NUMBERS };

  /** A set the statement speaks of. An index into sorts() names it. */
  struct Sort {
    std::string name;
    SortKind kind = SortKind::PLAIN;
    unsigned base = 0;    // PARTS, MAPS: an index into sorts()
    unsigned target = 0;  // MAPS: an index into sorts()
  };

  /**
   * A declared name: an element (no domain), a map, or a relation
   * (range == BOOL). domain and range are indices into sorts().
   */
  struct Symbol {
    std::string name;
    std::vector<unsigned> domain;
    int range;
    bool structure = false;  // not declared by the statement but given with a set: "t is in the part X"
                             // (domain: base, the parts), "the value of the map f at x" (domain: the
                             // maps, base; range: target), a written number (an element of NUMBERS)
    bool isRelation() const { return range == BOOL; }
  };

  /**
   * An element: a bound variable (variable >= 0, the number of its binder)
   * or a symbol applied to arguments (variable < 0). sort is its set.
   */
  struct Term {
    int variable = -1;
    unsigned symbol = 0;
    std::vector<Term> arguments;
    unsigned sort = 0;
  };

  enum class Connective { TRUE, EQUAL, HOLDS, NOT, AND, OR, IMPLIES, IFF, FORALL, EXISTS };

  /**
   * A condition.
   *   TRUE                  nothing else is used
   *   EQUAL                 terms[0] = terms[1], two elements of the same sort
   *   HOLDS                 the relation symbol holds of terms
   *   NOT                   parts[0]
   *   AND, OR, IMPLIES, IFF parts[0], parts[1]
   *   FORALL, EXISTS        parts[0], with the variable numbered variable,
   *                         called variableName in the source, ranging on sort.
   * Each quantifier has its own variable number, so numbers never clash.
   */
  struct Formula {
    Connective connective = Connective::TRUE;
    std::vector<Formula> parts;
    std::vector<Term> terms;
    unsigned symbol = 0;
    unsigned variable = 0;
    std::string variableName;
    unsigned sort = 0;
  };

  /**
   * Reads a statement written in the language of the certificates, as the
   * engine writes it: lines "certificate KIND"; "sort NAME", "sort NAME parts
   * BASE SYMBOL", "sort NAME maps BASE TARGET SYMBOL", "sort NAME numbers
   * NAME..."; "symbol NAME SORT... (SORT | bool)"; "statement CONDITION";
   * and "axiom CONDITION" for the laws of the sets of parts and of maps
   * that the engine gives with the statement.
   *
   * The reading checks the sorts: a symbol is applied to elements of its
   * domain, an equality compares two elements of the same set. Whatever the
   * text contains, the result is safe to use: if the statement has no
   * first-order form (a quantifier on the parts of a set, equipotence), or
   * the text is not what this reader expects, outside() says why and the
   * statement must not be translated.
   */
  static LogicStatement read(const std::string& text, bool wantsExample);

  const std::vector<Sort>& sorts() const { return _sorts; }
  const std::vector<Symbol>& symbols() const { return _symbols; }
  const Formula& formula() const { return _formula; }

  /**
   * The laws given with the statement: conditions that hold in every
   * interpretation because of what a set of parts or of maps is (two parts
   * with the same elements are the same part; the elements that satisfy a
   * condition are a part). A proof may use them as it uses the hypotheses.
   */
  const std::vector<Formula>& laws() const { return _laws; }

  /** True if every set is a plain one: then a finite model is just sizes and tables. */
  bool plainOnly() const
  {
    for (const Sort& sort : _sorts) if (sort.kind != SortKind::PLAIN) return false;
    return true;
  }
  unsigned variables() const { return _variables; }
  bool wantsExample() const { return _wantsExample; }

  /** Empty if the statement can be given to a first-order prover; otherwise the reason it cannot. */
  const std::string& outside() const { return _outside; }

private:
  std::vector<Sort> _sorts;
  std::vector<Symbol> _symbols;
  Formula _formula;
  std::vector<Formula> _laws;
  unsigned _variables = 0;
  bool _wantsExample = false;
  std::string _outside;

  friend class LogicStatementReader;
};

} // namespace Math

#endif // __Math_LogicStatement__
