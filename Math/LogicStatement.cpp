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
 * @file LogicStatement.cpp
 * Reads a statement of first-order logic from the language of the
 * certificates into a typed tree (see LogicStatement.hpp).
 */

#include "LogicStatement.hpp"

#include <sstream>

namespace Math {

/**
 * The reader of one statement. It exists only during LogicStatement::read():
 * its state is the position in the text and the variables in scope.
 *
 * The grammar of a condition, with one word or one parenthesis per case:
 *
 *   true
 *   NAME                          a relation without arguments
 *   (not C)  (and C C)  (or C C)  (implies C C)  (iff C C)
 *   (forall NAME SORT C)  (exists NAME SORT C)
 *   (= T T)
 *   (NAME T ...)                  a relation applied
 *
 * and of an element:  NAME  |  (NAME T ...).
 * A name is the innermost bound variable called so, otherwise a symbol: the
 * same rule the independent checker follows, so that the two readings of a
 * certificate cannot differ.
 */
class LogicStatementReader {
public:
  LogicStatementReader(LogicStatement& statement) : _statement(statement) {}

  /** Reads the condition in text; on any problem leaves the reason in the statement's _outside. */
  void readCondition(const std::string& text)
  {
    _text = &text;
    _position = 0;
    LogicStatement::Formula formula = condition(0);
    skipSpaces();
    if (ok() && _position != text.size()) fail("there is text after the condition");
    if (ok()) _statement._formula = std::move(formula);
  }

private:
  using Formula = LogicStatement::Formula;
  using Term = LogicStatement::Term;
  using Connective = LogicStatement::Connective;

  /** A variable in scope. */
  struct Bound {
    std::string name;
    unsigned variable;
    unsigned sort;
  };

  /* Deeper than this the statement is left to the engine, which guards its
   * own stack: this reader and Vampire's preprocessing are recursive. */
  static constexpr unsigned MAX_DEPTH = 1000;

  LogicStatement& _statement;
  const std::string* _text = nullptr;
  size_t _position = 0;
  std::vector<Bound> _scope;

  bool ok() const { return _statement._outside.empty(); }
  void fail(const std::string& reason) { if (ok()) _statement._outside = reason; }

  void skipSpaces()
  {
    while (_position < _text->size() && ((*_text)[_position] == ' ' || (*_text)[_position] == '\t')) _position++;
  }

  bool accept(char c)
  {
    skipSpaces();
    if (_position < _text->size() && (*_text)[_position] == c) { _position++; return true; }
    return false;
  }

  void expect(char c)
  {
    if (!accept(c)) fail(std::string("'") + c + "' expected");
  }

  /** The next word: everything up to a space or a parenthesis. Empty at a parenthesis or at the end. */
  std::string word()
  {
    skipSpaces();
    size_t start = _position;
    while (_position < _text->size()) {
      char c = (*_text)[_position];
      if (c == ' ' || c == '\t' || c == '(' || c == ')') break;
      _position++;
    }
    return _text->substr(start, _position - start);
  }

  int findSort(const std::string& name) const
  {
    for (unsigned i = 0; i < _statement._sorts.size(); i++)
      if (_statement._sorts[i].name == name) return (int)i;
    return -1;
  }

  int findSymbol(const std::string& name) const
  {
    for (unsigned i = 0; i < _statement._symbols.size(); i++)
      if (_statement._symbols[i].name == name) return (int)i;
    return -1;
  }

  const Bound* findBound(const std::string& name) const
  {
    for (size_t i = _scope.size(); i-- > 0;)
      if (_scope[i].name == name) return &_scope[i];
    return nullptr;
  }

  /** Reads the arguments of the symbol into arguments, up to the closing parenthesis, checking their sorts. */
  void arguments(unsigned symbol, std::vector<Term>& arguments, unsigned depth)
  {
    const std::vector<unsigned> domain = _statement._symbols[symbol].domain;
    for (unsigned i = 0; i < domain.size() && ok(); i++) {
      Term argument = term(depth + 1);
      if (ok() && argument.sort != domain[i])
        fail("the symbol " + _statement._symbols[symbol].name + " is applied to an element of another set");
      arguments.push_back(std::move(argument));
    }
    expect(')');
  }

  Term term(unsigned depth)
  {
    Term result;
    if (depth > MAX_DEPTH) { fail("the statement is nested too deeply for the translation"); return result; }
    bool applied = accept('(');
    std::string name = word();
    if (name.empty()) { fail("a name is expected"); return result; }

    /* A variable is never applied: an applied name is a symbol. */
    const Bound* bound = applied ? nullptr : findBound(name);
    if (bound) {
      result.variable = (int)bound->variable;
      result.sort = bound->sort;
      return result;
    }
    int symbol = findSymbol(name);
    if (symbol < 0) { fail("the name " + name + " is not declared"); return result; }
    const LogicStatement::Symbol& declared = _statement._symbols[symbol];
    if (declared.isRelation()) { fail("the relation " + name + " is used as an element"); return result; }
    if (applied != !declared.domain.empty()) { fail("the symbol " + name + " has the wrong number of arguments"); return result; }
    result.symbol = (unsigned)symbol;
    result.sort = (unsigned)declared.range;
    if (applied) arguments(result.symbol, result.arguments, depth);
    return result;
  }

  Formula condition(unsigned depth)
  {
    Formula result;
    if (depth > MAX_DEPTH) { fail("the statement is nested too deeply for the translation"); return result; }
    bool compound = accept('(');
    std::string head = word();
    if (head.empty()) { fail("a condition is expected"); return result; }

    if (!compound) {
      if (head == "true") return result;

      /* A bare name: a relation without arguments. */
      int symbol = findBound(head) ? -1 : findSymbol(head);
      if (symbol < 0 || !_statement._symbols[symbol].isRelation() || !_statement._symbols[symbol].domain.empty()) {
        fail("the name " + head + " is not a condition");
        return result;
      }
      result.connective = Connective::HOLDS;
      result.symbol = (unsigned)symbol;
      return result;
    }

    if (head == "not") {
      result.connective = Connective::NOT;
      result.parts.push_back(condition(depth + 1));
      expect(')');
      return result;
    }
    if (head == "and" || head == "or" || head == "implies" || head == "iff") {
      result.connective = head == "and" ? Connective::AND : head == "or" ? Connective::OR
                        : head == "implies" ? Connective::IMPLIES : Connective::IFF;
      result.parts.push_back(condition(depth + 1));
      result.parts.push_back(condition(depth + 1));
      expect(')');
      return result;
    }
    if (head == "forall" || head == "exists") {
      result.connective = head == "forall" ? Connective::FORALL : Connective::EXISTS;
      result.variableName = word();
      int sort = findSort(word());
      if (result.variableName.empty() || sort < 0) { fail("a quantifier needs a variable and a declared set"); return result; }
      result.sort = (unsigned)sort;
      result.variable = _statement._variables++;

      /* The scope of the variable is the condition that follows, and no more. */
      _scope.push_back({result.variableName, result.variable, result.sort});
      result.parts.push_back(condition(depth + 1));
      _scope.pop_back();
      expect(')');
      return result;
    }
    if (head == "forallpart" || head == "existspart") { fail("the statement quantifies over the parts of a set"); return result; }
    if (head == "equipotent") { fail("the statement speaks of a bijection between two sets"); return result; }
    if (head == "=") {
      result.connective = Connective::EQUAL;
      result.terms.push_back(term(depth + 1));
      result.terms.push_back(term(depth + 1));
      if (ok() && result.terms[0].sort != result.terms[1].sort) fail("an equality compares elements of two different sets");
      expect(')');
      return result;
    }

    /* A relation applied. A bound name here would be a bound part, which is
     * not first-order: findSymbol() does not see it, and the reading stops. */
    int symbol = findBound(head) ? -1 : findSymbol(head);
    if (symbol < 0 || !_statement._symbols[symbol].isRelation() || _statement._symbols[symbol].domain.empty()) {
      fail("the name " + head + " is not a relation with arguments");
      return result;
    }
    result.connective = Connective::HOLDS;
    result.symbol = (unsigned)symbol;
    arguments(result.symbol, result.terms, depth);
    return result;
  }
};

/** Splits a line into its words. */
static std::vector<std::string> wordsOf(const std::string& line)
{
  std::vector<std::string> words;
  std::istringstream stream(line);
  std::string word;
  while (stream >> word) words.push_back(word);
  return words;
}

LogicStatement LogicStatement::read(const std::string& text, bool wantsExample)
{
  LogicStatement statement;
  statement._wantsExample = wantsExample;
  LogicStatementReader reader(statement);
  bool hasCondition = false;

  std::istringstream lines(text);
  std::string line;
  while (statement._outside.empty() && std::getline(lines, line)) {
    static const std::string STATEMENT = "statement ";
    if (line.compare(0, STATEMENT.size(), STATEMENT) == 0) {
      /* The declarations all come before the statement: it is read last, with every name known. */
      statement._condition = line.substr(STATEMENT.size());
      reader.readCondition(statement._condition);
      hasCondition = true;
      continue;
    }
    std::vector<std::string> words = wordsOf(line);
    if (words.empty() || words[0] == "certificate") continue;

    if (words[0] == "sort") {
      /* A plain set is its name alone. More words say what the set is made
       * of (parts, maps, the written numbers): not a first-order sort. */
      if (words.size() != 2) {
        statement._outside = words.size() > 2 && words[2] == "numbers" ? "the statement speaks of the numbers it writes"
                           : "the statement speaks of a set of parts or of a set of maps";
        break;
      }
      statement._sorts.push_back({words[1]});
      continue;
    }
    if (words[0] == "symbol" && words.size() >= 3) {
      Symbol symbol;
      symbol.name = words[1];
      symbol.range = BOOL;
      for (size_t i = 2; i < words.size(); i++) {
        bool last = i + 1 == words.size();
        if (last && words[i] == "bool") break;
        int sort = -1;
        for (unsigned s = 0; s < statement._sorts.size(); s++)
          if (statement._sorts[s].name == words[i]) sort = (int)s;
        if (sort < 0) { statement._outside = "the symbol " + symbol.name + " is declared on a set that is not declared"; break; }
        if (last) symbol.range = sort; else symbol.domain.push_back((unsigned)sort);
      }
      for (const Symbol& other : statement._symbols)
        if (other.name == symbol.name && statement._outside.empty()) statement._outside = "the symbol " + symbol.name + " is declared twice";
      statement._symbols.push_back(std::move(symbol));
      continue;
    }
    statement._outside = "a line of the statement is not understood: " + line;
  }
  if (statement._outside.empty() && !hasCondition) statement._outside = "the statement has no condition";
  return statement;
}

std::string LogicStatement::certificateHead(const std::string& kind, const std::vector<unsigned>* sizes) const
{
  std::ostringstream out;
  out << "certificate " << kind << "\n";
  for (unsigned i = 0; i < _sorts.size(); i++) {
    out << "sort " << _sorts[i].name;
    if (sizes) out << " " << (*sizes)[i];
    out << "\n";
  }
  for (const Symbol& symbol : _symbols) {
    out << "symbol " << symbol.name;
    for (unsigned sort : symbol.domain) out << " " << _sorts[sort].name;
    if (symbol.isRelation()) out << " bool"; else out << " " << _sorts[symbol.range].name;
    out << "\n";
  }
  out << "statement " << _condition << "\n";
  return out.str();
}

} // namespace Math
