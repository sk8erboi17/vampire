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
 * @file NumberStatement.cpp
 * Implements NumberStatement: the reader of the prefix notation of
 * Engine.h (qr_numbers_item()) and the writer of the TPTP formula.
 */

#include "NumberStatement.hpp"

#include <utility>
#include <vector>

namespace Math {

namespace {

/**
 * Reads the handed-over text and writes the TPTP formula as it goes: every
 * function returns the TPTP text of what it read, or sets _failed. The
 * grammar is the one in Engine.h; anything else fails, and nothing is
 * guessed.
 */
class Reader {
public:
  /**
   * @param lift moves to the front the quantifiers that values can settle
   *   (see condition()): the formula returned then has their variables
   *   free, named W0, W1, ... by the number of the quantifier.
   */
  Reader(const std::string& text, size_t at, int kind, bool lift = false) : _text(text), _at(at), _kind(kind), _lift(lift) {}

  bool failed() const { return _failed; }
  bool atEnd() { skip(); return _at == _text.size(); }

  /** With lift: false if some quantifier that has to be used can be settled neither by a value nor by the checker's count. */
  bool settled() const { return _settled; }
  /** With lift: how many quantifiers were left where they are, for the checker to settle by its complete count. */
  unsigned counted() const { return _counted; }
  /** With lift: the quantifiers moved to the front, outermost first, and the letters they bind. */
  const std::vector<unsigned>& lifted() const { return _lifted; }
  const std::vector<std::string>& liftedLetters() const { return _liftedLetters; }

  /** The truth value to be shown of a condition: true, false, or either (under an "if and only if"). */
  enum Want { FALSE = 0, TRUE = 1, EITHER = -1 };

  /**
   * A condition. @b want matters only with lift: it is the truth value
   * that has to be shown of this condition for the whole statement to get
   * the one wanted of it. A "for all" to be shown false and a "there is"
   * to be shown true need one value each: those are lifted. The other two
   * cases need a proof for every value, which no value gives. The checker
   * gives one by itself where, the outer values fixed, one integer
   * variable is left and nothing is quantified inside (its complete count,
   * 20e of checker.c): such a quantifier stays where it is. Being
   * innermost, it has no lifted quantifier in its scope, so moving the
   * others to the front still says the same. Anywhere else the statement
   * is not settled by values.
   */
  std::string condition(unsigned depth, Want want = EITHER)
  {
    if (depth > MAX_DEPTH || !open()) return fail();
    std::string head = word();
    std::string result;
    Want opposite = want == EITHER ? EITHER : want == TRUE ? FALSE : TRUE;
    if (head == "forall" || head == "exists") {
      bool universal = head == "forall";
      unsigned number = _quantifiers++;
      std::string letter = this->letter();
      bool lifted = _lift && want == (universal ? FALSE : TRUE);
      std::string variable = lifted ? "W" + std::to_string(number) : "X" + letter;
      if (lifted) { _lifted.push_back(number); _liftedLetters.push_back(letter); }
      std::string guard = set(variable);
      _scope.push_back({letter, variable});
      std::string body = condition(depth + 1, want);
      _scope.pop_back();
      if (_lift && !lifted) {
        if (_kind == INTEGERS && _quantifiers == number + 1) _counted++;
        else _settled = false;
      }
      if (!guard.empty()) body = "(" + guard + (universal ? " => " : " & ") + body + ")";
      result = lifted ? body : std::string(universal ? "(![" : "(?[") + variable + ":" + sort() + "]: " + body + ")";
    } else if (head == "and" || head == "or" || head == "implies" || head == "iff") {
      std::string first = condition(depth + 1, head == "iff" ? EITHER : head == "implies" ? opposite : want);
      std::string second = condition(depth + 1, head == "iff" ? EITHER : want);
      result = "(" + first + (head == "and" ? " & " : head == "or" ? " | " : head == "implies" ? " => " : " <=> ") + second + ")";
    } else if (head == "not") {
      result = "~(" + condition(depth + 1, opposite) + ")";
    } else if (head == "=" || head == "neq") {
      std::string left = term(depth + 1), right = term(depth + 1);
      result = "(" + left + (head == "=" ? " = " : " != ") + right + ")";
    } else if (head == "less" || head == "lesseq") {
      std::string left = term(depth + 1), right = term(depth + 1);
      result = std::string(head == "less" ? "$less(" : "$lesseq(") + left + "," + right + ")";
    } else if (head == "in") {
      /* E belongs to a set of numbers of its own kind: the bound and the removed points. */
      std::string element = term(depth + 1);
      std::string guard = set(element);
      result = guard.empty() ? "$true" : guard;
    } else if (head == "divides") {
      /* "u divides v": v is u times an integer, so zero divides only zero. Among integers only. */
      if (_kind != INTEGERS) return fail();
      std::string divisor = term(depth + 1), divided = term(depth + 1);
      std::string factor = "K" + std::to_string(_fresh++);
      result = "(?[" + factor + ":$int]: (" + divided + " = $product(" + divisor + "," + factor + ")))";
    } else {
      return fail();
    }
    if (!close()) return fail();
    return result;
  }

private:
  enum { INTEGERS = 1, RATIONALS = 2, REALS = 3 };
  static constexpr unsigned MAX_DEPTH = 400;  // of nested conditions and terms: the engine's formulas are far shallower

  const std::string& _text;
  size_t _at;
  int _kind;
  bool _lift;
  bool _failed = false;
  bool _settled = true;
  unsigned _counted = 0;      // quantifiers left to the checker's count
  unsigned _fresh = 0;        // names for the factors of "divides"
  unsigned _quantifiers = 0;  // how many quantifiers were met: the next one's number
  std::vector<unsigned> _lifted;
  std::vector<std::string> _liftedLetters;
  std::vector<std::pair<std::string, std::string>> _scope;  // the letters bound here, each with its variable

  std::string fail() { _failed = true; return ""; }

  void skip() { while (_at < _text.size() && (_text[_at] == ' ' || _text[_at] == '\n')) _at++; }
  bool open() { skip(); if (_at < _text.size() && _text[_at] == '(') { _at++; return true; } return false; }
  bool close() { skip(); if (_at < _text.size() && _text[_at] == ')') { _at++; return true; } return false; }
  std::string word()
  {
    skip();
    size_t start = _at;
    while (_at < _text.size() && _text[_at] != ' ' && _text[_at] != '\n' && _text[_at] != '(' && _text[_at] != ')') _at++;
    return _text.substr(start, _at - start);
  }

  /** A whole number, with at most 18 digits and possibly a sign. Returns false if the word is not one. */
  static bool whole(const std::string& text, bool mayBeNegative)
  {
    size_t digits = !text.empty() && text[0] == '-' && mayBeNegative ? 1 : 0;
    if (text.size() == digits || text.size() - digits > 18) return false;
    for (size_t i = digits; i < text.size(); i++) if (text[i] < '0' || text[i] > '9') return false;
    return true;
  }

  const char* sort() const { return _kind == INTEGERS ? "$int" : _kind == RATIONALS ? "$rat" : "$real"; }

  /** The numeral of the whole number, in the sort of the statement. */
  std::string numeral(const std::string& whole) const
  {
    return _kind == INTEGERS ? whole : _kind == RATIONALS ? whole + "/1" : whole + ".0";
  }

  /** The number P/Q, Q positive, in the sort of the statement. Among integers Q must be 1. */
  std::string fraction(const std::string& text)
  {
    size_t bar = text.find('/');
    if (bar == std::string::npos) return fail();
    std::string numerator = text.substr(0, bar), denominator = text.substr(bar + 1);
    if (!whole(numerator, true) || !whole(denominator, false) || denominator.find_first_not_of('0') == std::string::npos) return fail();
    if (_kind == INTEGERS) return denominator == "1" ? numerator : fail();
    if (_kind == RATIONALS) return numerator + "/" + denominator;
    return "$quotient(" + numerator + ".0," + denominator + ".0)";
  }

  /** (var N): the letter number N. */
  std::string letter()
  {
    if (!open() || word() != "var") return fail();
    std::string letter = word();
    if (!whole(letter, false) || !close()) return fail();
    return letter;
  }

  /** (var N) in an expression: the variable of the innermost quantifier that binds the letter. */
  std::string variable()
  {
    std::string letter = this->letter();
    for (size_t i = _scope.size(); i > 0; i--) if (_scope[i - 1].first == letter) return _scope[i - 1].second;
    return fail();
  }

  /**
   * (set [ge L | gt L] [except P/Q]...): the conditions that say that
   * @b element, a term of the sort, is in the set; empty if the set is
   * the whole sort.
   */
  std::string set(const std::string& element)
  {
    if (!open() || word() != "set") return fail();
    std::vector<std::string> conditions;
    while (!close()) {
      std::string what = word();
      std::string value = word();
      if (what == "ge" || what == "gt") {
        if (!whole(value, true)) return fail();
        conditions.push_back(std::string(what == "ge" ? "$greatereq(" : "$greater(") + element + "," + numeral(value) + ")");
      } else if (what == "except") {
        std::string point = fraction(value);
        if (_failed) return "";
        conditions.push_back("(" + element + " != " + point + ")");
      } else {
        return fail();
      }
    }
    std::string all;
    for (size_t i = 0; i < conditions.size(); i++) all += (i ? " & " : "") + conditions[i];
    return conditions.size() > 1 ? "(" + all + ")" : all;
  }

  /** An expression. */
  std::string term(unsigned depth)
  {
    if (depth > MAX_DEPTH) return fail();
    skip();
    if (_at < _text.size() && _text[_at] != '(') {
      std::string number = word();
      return whole(number, false) ? numeral(number) : fail();
    }
    size_t start = _at;
    if (!open()) return fail();
    std::string head = word();
    std::string result;
    if (head == "var") {
      _at = start;
      return variable();
    }
    if (head == "add" || head == "sub" || head == "mul") {
      std::string left = term(depth + 1), right = term(depth + 1);
      result = std::string(head == "add" ? "$sum(" : head == "sub" ? "$difference(" : "$product(") + left + "," + right + ")";
    } else if (head == "neg") {
      result = "$uminus(" + term(depth + 1) + ")";
    } else if (head == "pow") {
      /* A written exponent from 1 to 16: the product of that many copies. */
      std::string base = term(depth + 1);
      std::string exponent = word();
      if (!whole(exponent, false) || exponent.size() > 2) return fail();
      int copies = std::stoi(exponent);
      if (copies < 1 || copies > 16) return fail();
      result = base;
      for (int i = 1; i < copies; i++) result = "$product(" + result + "," + base + ")";
    } else if (head == "div") {
      /* By a written positive integer, in a field: the exact quotient. */
      if (_kind == INTEGERS) return fail();
      std::string dividend = term(depth + 1);
      std::string divisor = word();
      if (!whole(divisor, false) || divisor.find_first_not_of('0') == std::string::npos) return fail();
      result = "$quotient(" + dividend + "," + numeral(divisor) + ")";
    } else {
      return fail();
    }
    if (!close()) return fail();
    return result;
  }
};

} // namespace

NumberStatement NumberStatement::read(const std::string& handedOver)
{
  NumberStatement statement;
  static const char* const HEADS[] = {"numbers int ", "numbers rat ", "numbers real"};
  static const char* const SORTS[] = {"$int", "$rat", "$real"};
  size_t line = handedOver.find('\n');
  if (line == std::string::npos) return statement;
  std::string head = handedOver.substr(0, line);
  for (int kind = 0; kind < 3; kind++) {
    if (head != HEADS[kind]) continue;
    Reader reader(handedOver, line + 1, kind + 1);
    std::string formula = reader.condition(0);
    if (reader.failed() || !reader.atEnd()) return statement;
    statement._sort = SORTS[kind];
    statement._formula = formula;
    statement._kind = kind + 1;

    /* The statement alone, on one line, as the checker reads it. */
    statement._text = handedOver.substr(line + 1);
    while (!statement._text.empty() && (statement._text.back() == '\n' || statement._text.back() == ' ')) statement._text.pop_back();
  }
  return statement;
}

std::string NumberStatement::tptp(bool denied) const
{
  return "tff(statement, conjecture, " + (denied ? "~(" + _formula + ")" : _formula) + ").\n";
}

NumberStatement::WitnessProblem NumberStatement::witnessProblem(bool denied) const
{
  WitnessProblem problem;
  if (!ok()) return problem;
  Reader reader(_text, 0, _kind, /* lift */ true);
  std::string formula = reader.condition(0, denied ? Reader::FALSE : Reader::TRUE);
  if (reader.failed() || !reader.atEnd() || !reader.settled()) return problem;

  /* "There are W0, W1, ... such that the statement holds (or fails)":
   * the same as the statement, or its negation, because each of those
   * quantifiers stood where one value of it is what counts, and a sort of
   * numbers is never empty. */
  std::string variables;
  for (unsigned number : reader.lifted()) variables += (variables.empty() ? "" : ", ") + ("W" + std::to_string(number)) + ":" + _sort;
  std::string matrix = denied ? "~(" + formula + ")" : formula;
  problem.tptp = "tff(statement, conjecture, " + (variables.empty() ? matrix : "?[" + variables + "]: (" + matrix + ")") + ").\n";
  problem.quantifiers = reader.lifted();
  problem.letters = reader.liftedLetters();
  problem.counted = reader.counted();
  return problem;
}

std::string NumberStatement::certificate(bool denied, const WitnessProblem& problem, const std::vector<std::string>& values) const
{
  static const char* const KINDS[] = {"", "int", "rat", "real"};
  std::string text = std::string("certificate numbers\nkind ") + KINDS[_kind] + "\nstatement " + _text + "\n" + (denied ? "fails\n" : "holds\n");
  for (size_t i = 0; i < problem.quantifiers.size() && i < values.size(); i++)
    text += "witness " + std::to_string(problem.quantifiers[i]) + " " + values[i] + "\n";
  return text + "end\n";
}

std::string NumberStatement::arithmeticBeginning(bool denied) const
{
  if (!ok() || _kind != 1) return "";
  return "certificate arithmetic\nkind int\nstatement " + (denied ? "(not " + _text + ")" : _text) + "\nclausify forward\n";
}

std::string NumberStatement::arithmeticFacts(const std::vector<long long>& numerals)
{
  /* The symbols of the translation (checker.c, 20f): add 0, mul 2, less 3,
   * and the numerals from 4 on. With many numerals only neighbours are
   * compared: the order of the others follows from the laws. */
  static const size_t ALL_PAIRS = 16;
  auto numeral = [](size_t i) { return "(f " + std::to_string(4 + i) + ")"; };
  auto find = [&](long long value) {
    for (size_t i = 0; i < numerals.size(); i++) if (numerals[i] == value) return (long long)i;
    return -1LL;
  };
  std::string facts;
  for (size_t i = 0; i < numerals.size(); i++)
    for (size_t j = i + 1; j < numerals.size() && (numerals.size() <= ALL_PAIRS || j == i + 1); j++) {
      size_t low = numerals[i] < numerals[j] ? i : j, high = low == i ? j : i;
      facts += "step compute (clause (ne " + numeral(i) + " " + numeral(j) + "))\n";
      facts += "step compute (clause (pos (f 3 " + numeral(low) + " " + numeral(high) + ")))\n";
      facts += "step compute (clause (neg (f 3 " + numeral(high) + " " + numeral(low) + ")))\n";
    }
  if (numerals.size() > ALL_PAIRS) return facts;
  for (size_t i = 0; i < numerals.size(); i++)
    for (size_t j = i; j < numerals.size(); j++) {
      long long a = numerals[i], b = numerals[j];
      long long sum = a > 0 && b > 0 && a <= (1LL << 40) && b <= (1LL << 40) ? find(a + b) : -1;
      long long product = a > 1 && b > 1 && a <= (1LL << 20) && b <= (1LL << 20) ? find(a * b) : -1;
      if (sum >= 0) facts += "step compute (clause (eq (f 0 " + numeral(i) + " " + numeral(j) + ") " + numeral((size_t)sum) + "))\n";
      if (product >= 0) facts += "step compute (clause (eq (f 2 " + numeral(i) + " " + numeral(j) + ") " + numeral((size_t)product) + "))\n";
    }
  return facts;
}

bool NumberStatement::answerValue(const std::string& answer, std::string& value)
{
  std::string text = answer;
  auto trim = [&]() {
    while (!text.empty() && text.front() == ' ') text.erase(text.begin());
    while (!text.empty() && text.back() == ' ') text.pop_back();
  };
  trim();

  /* A number of one sort seen from another, and parentheses, change nothing. */
  for (bool unwrapped = true; unwrapped;) {
    unwrapped = false;
    for (const char* wrapper : {"$to_real(", "$to_rat(", "$to_int(", "("}) {
      size_t length = std::string(wrapper).size();
      if (text.size() > length && text.compare(0, length, wrapper) == 0 && text.back() == ')') {
        text = text.substr(length, text.size() - length - 1);
        trim();
        unwrapped = true;
      }
    }
  }

  /* An integer, a fraction, or a number with a point: digits, at most 18 of them each. */
  size_t at = !text.empty() && text[0] == '-' ? 1 : 0;
  auto digits = [&](std::string& into) {
    size_t start = at;
    while (at < text.size() && text[at] >= '0' && text[at] <= '9') at++;
    into = text.substr(start, at - start);
    return !into.empty() && into.size() <= 18;
  };
  std::string whole, rest;
  if (!digits(whole)) return false;
  std::string sign = text[0] == '-' ? "-" : "";
  if (at == text.size()) { value = sign + whole; return true; }
  char between = text[at++];
  if (!digits(rest) || at != text.size()) return false;
  if (between == '/') {
    if (rest.find_first_not_of('0') == std::string::npos) return false;
    value = sign + whole + "/" + rest;
    return true;
  }
  if (between != '.' || whole.size() + rest.size() > 18) return false;
  value = sign + whole + rest + "/1" + std::string(rest.size(), '0');
  return true;
}

} // namespace Math
