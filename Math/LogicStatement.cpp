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

  /**
   * Reads the condition in text and returns it; on any problem leaves the
   * reason in the statement's _outside. @b wholeStatement says that the
   * condition is the statement itself, and not a law given with it: only
   * there can a hypothesis be a bijection between two sets (bijection()).
   */
  LogicStatement::Formula readCondition(const std::string& text, bool wholeStatement)
  {
    _text = &text;
    _position = 0;
    _scope.clear();
    LogicStatement::Formula formula = condition(0, wholeStatement ? Place::STATEMENT : Place::INSIDE);
    skipSpaces();
    if (ok() && _position != text.size()) fail("there is text after the condition");
    return formula;
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

  /**
   * Where a condition stands, for the one thing that depends on it, a
   * bijection between two sets (see bijection()): the whole statement, a
   * conjunct of the hypotheses of a statement "hypotheses imply claim", or
   * anywhere else.
   */
  enum class Place { STATEMENT, HYPOTHESIS, INSIDE };

  /**
   * "The sets A and B are equipotent", as a hypothesis of the statement:
   * two new maps, one from A to B and one from B to A, and the condition
   * that each undoes the other.
   *
   * WHY IT MEANS THE SAME. Let the statement be "E and H imply C", with E
   * the equipotence of A and B, and let D say of two maps p: A -> B and
   * q: B -> A that q(p(x)) = x for every x of A and p(q(y)) = y for every
   * y of B. Then "E and H imply C" holds in every interpretation exactly
   * when "D and H imply C" holds in every interpretation that also gives
   * p and q. If the second holds and E, H hold in an interpretation, take
   * a bijection of A onto B for p and its inverse for q: D holds, so C
   * does, and C does not speak of p and q. If the first holds and D, H
   * hold in an interpretation with p and q, then p is a bijection (q undoes
   * it on both sides), so E holds there, and so does C.
   *
   * The argument needs E to be a hypothesis. To PROVE that two sets are
   * equipotent is to build a bijection, which no choice of two symbols can
   * do; and under a negation or in one branch of an "or" the maps would
   * have to exist only in some cases. Everywhere else the equipotence is
   * refused, and the statement stays with the engine, as do products of
   * sets on either side.
   */
  Formula bijection(Place place)
  {
    Formula result;
    if (place != Place::HYPOTHESIS || _statement._wantsExample) {
      fail("the statement speaks of a bijection between two sets, and not as a hypothesis to use");
      return result;
    }
    if (accept('(')) { fail("the statement speaks of a bijection with a product of sets"); return result; }
    int from = findSort(word());
    if (accept('(')) { fail("the statement speaks of a bijection with a product of sets"); return result; }
    int to = findSort(word());
    if (from < 0 || to < 0) { fail("a bijection needs two declared sets"); return result; }

    /* Names no symbol has. */
    unsigned number = 1;
    while (findSymbol("phi" + std::to_string(number)) >= 0 || findSymbol("psi" + std::to_string(number)) >= 0) number++;
    LogicStatement::Symbol there, back;
    there.name = "phi" + std::to_string(number);
    there.domain = {(unsigned)from};
    there.range = to;
    back.name = "psi" + std::to_string(number);
    back.domain = {(unsigned)to};
    back.range = from;
    unsigned thereSymbol = (unsigned)_statement._symbols.size();
    _statement._symbols.push_back(there);
    _statement._symbols.push_back(back);
    _statement._bijections++;

    /* For every x of A, back(there(x)) = x; for every y of B, there(back(y)) = y. */
    auto undoes = [&](unsigned first, unsigned second, unsigned sort, unsigned other, const char* name) {
      Formula all;
      all.connective = Connective::FORALL;
      all.variable = _statement._variables++;
      all.variableName = name;
      all.sort = sort;
      Term element;
      element.variable = (int)all.variable;
      element.sort = sort;
      Term image;
      image.symbol = first;
      image.arguments = {element};
      image.sort = other;
      Term returned;
      returned.symbol = second;
      returned.arguments = {image};
      returned.sort = sort;
      Formula same;
      same.connective = Connective::EQUAL;
      same.terms = {returned, element};
      all.parts.push_back(same);
      return all;
    };
    result.connective = Connective::AND;
    result.parts.push_back(undoes(thereSymbol, thereSymbol + 1, (unsigned)from, (unsigned)to, "x"));
    result.parts.push_back(undoes(thereSymbol + 1, thereSymbol, (unsigned)to, (unsigned)from, "y"));
    return result;
  }

  Formula condition(unsigned depth, Place place = Place::INSIDE)
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

      /* The hypotheses of the statement are the conjuncts of what it
       * supposes, "H1 and ... and Hn imply C"; nothing else is one. */
      bool hypotheses = (head == "implies" && place == Place::STATEMENT) || (head == "and" && place == Place::HYPOTHESIS);
      result.parts.push_back(condition(depth + 1, hypotheses ? Place::HYPOTHESIS : Place::INSIDE));
      result.parts.push_back(condition(depth + 1, hypotheses && head == "and" ? Place::HYPOTHESIS : Place::INSIDE));
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
    if (head == "equipotent") {
      result = bijection(place);
      expect(')');
      return result;
    }
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
  auto fail = [&](const std::string& reason) { if (statement._outside.empty()) statement._outside = reason; };
  auto findSort = [&](const std::string& name) {
    for (unsigned s = 0; s < statement._sorts.size(); s++)
      if (statement._sorts[s].name == name) return (int)s;
    return -1;
  };
  auto addSymbol = [&](Symbol symbol) {
    for (const Symbol& other : statement._symbols)
      if (other.name == symbol.name) fail("the symbol " + symbol.name + " is declared twice");
    statement._symbols.push_back(std::move(symbol));
  };

  /* The names of the sets first: a set of parts or of maps names other sets, wherever they are declared. */
  {
    std::istringstream lines(text);
    std::string line;
    while (std::getline(lines, line)) {
      std::vector<std::string> words = wordsOf(line);
      if (words.size() >= 2 && words[0] == "sort") {
        if (findSort(words[1]) >= 0) fail("the set " + words[1] + " is declared twice");
        statement._sorts.push_back({words[1]});
      }
    }
  }

  std::istringstream lines(text);
  std::string line;
  unsigned sortsSeen = 0;
  while (statement._outside.empty() && std::getline(lines, line)) {
    static const std::string STATEMENT = "statement ", AXIOM = "axiom ";
    if (line.compare(0, STATEMENT.size(), STATEMENT) == 0) {
      /* The declarations all come before the statement: it is read with every name known. */
      statement._formula = reader.readCondition(line.substr(STATEMENT.size()), /* wholeStatement */ true);
      hasCondition = true;
      continue;
    }
    if (line.compare(0, AXIOM.size(), AXIOM) == 0) {
      statement._laws.push_back(reader.readCondition(line.substr(AXIOM.size()), /* wholeStatement */ false));
      continue;
    }
    std::vector<std::string> words = wordsOf(line);
    if (words.empty() || words[0] == "certificate") continue;

    if (words[0] == "sort" && words.size() >= 2) {
      unsigned index = sortsSeen++;
      Sort& sort = statement._sorts[index];
      if (words.size() == 2) continue;  // a plain set is its name alone

      /* More words say what the set is made of, and name what comes with it. */
      if (words[2] == "parts" && words.size() == 5) {
        int base = findSort(words[3]);
        if (base < 0) { fail("a set of parts is of a set that is not declared"); break; }
        sort.kind = SortKind::PARTS;
        sort.base = (unsigned)base;
        addSymbol({words[4], {(unsigned)base, index}, BOOL, true});
      } else if (words[2] == "maps" && words.size() == 6) {
        int base = findSort(words[3]), target = findSort(words[4]);
        if (base < 0 || target < 0) { fail("a set of maps is between sets that are not declared"); break; }
        sort.kind = SortKind::MAPS;
        sort.base = (unsigned)base;
        sort.target = (unsigned)target;
        addSymbol({words[5], {index, (unsigned)base}, target, true});
      } else if (words[2] == "numbers" && words.size() >= 4) {
        sort.kind = SortKind::NUMBERS;
        for (size_t i = 3; i < words.size(); i++) addSymbol({words[i], {}, (int)index, true});
      } else {
        fail("a line of the statement is not understood: " + line);
      }
      continue;
    }
    if (words[0] == "symbol" && words.size() >= 3) {
      Symbol symbol;
      symbol.name = words[1];
      symbol.range = BOOL;
      for (size_t i = 2; i < words.size(); i++) {
        bool last = i + 1 == words.size();
        if (last && words[i] == "bool") break;
        int sort = findSort(words[i]);
        if (sort < 0) { fail("the symbol " + symbol.name + " is declared on a set that is not declared"); break; }
        if (last) symbol.range = sort; else symbol.domain.push_back((unsigned)sort);
      }
      addSymbol(std::move(symbol));
      continue;
    }
    fail("a line of the statement is not understood: " + line);
  }
  if (!hasCondition) fail("the statement has no condition");
  return statement;
}

} // namespace Math
