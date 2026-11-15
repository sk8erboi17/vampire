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
 *   - ModelCertificate, which writes a model found by Vampire back in the
 *     language of the independent checker.
 *
 * MEANING. The statement is to hold in every interpretation: any choice of
 * the sets, finite or infinite and possibly EMPTY, of an element for each
 * name, a total map for each function symbol and a subset for each relation.
 * A statement that "wants an example" asks instead for one interpretation in
 * which it holds.
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

  /** A set the statement speaks of. An index into sorts() names it. */
  struct Sort {
    std::string name;
  };

  /**
   * A declared name: an element (no domain), a map, or a relation
   * (range == BOOL). domain and range are indices into sorts().
   */
  struct Symbol {
    std::string name;
    std::vector<unsigned> domain;
    int range;
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
   * Reads a statement written in the language of the certificates: lines
   * "certificate KIND", "sort NAME", "symbol NAME SORT... (SORT | bool)" and
   * "statement CONDITION", as the engine writes them.
   *
   * The reading checks the sorts: a symbol is applied to elements of its
   * domain, an equality compares two elements of the same set. Whatever the
   * text contains, the result is safe to use: if the statement is outside
   * first-order logic over plain sets (a set of parts or of maps, a
   * quantifier on parts, equipotence, written numbers), or the text is not
   * what this reader expects, outside() says why and the statement must not
   * be translated.
   */
  static LogicStatement read(const std::string& text, bool wantsExample);

  const std::vector<Sort>& sorts() const { return _sorts; }
  const std::vector<Symbol>& symbols() const { return _symbols; }
  const Formula& formula() const { return _formula; }
  unsigned variables() const { return _variables; }
  bool wantsExample() const { return _wantsExample; }

  /** Empty if the statement is first-order logic over plain sets; otherwise the reason it is not. */
  const std::string& outside() const { return _outside; }

  /** The first lines of a certificate for this statement: kind, sorts (with sizes, if given), symbols, statement. */
  std::string certificateHead(const std::string& kind, const std::vector<unsigned>* sizes) const;

private:
  std::vector<Sort> _sorts;
  std::vector<Symbol> _symbols;
  Formula _formula;
  unsigned _variables = 0;
  bool _wantsExample = false;
  std::string _outside;
  std::string _condition;  // the condition as it was read, for certificateHead()

  friend class LogicStatementReader;
};

} // namespace Math

#endif // __Math_LogicStatement__
