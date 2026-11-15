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
  Reader(const std::string& text, size_t at, int kind) : _text(text), _at(at), _kind(kind) {}

  bool failed() const { return _failed; }
  bool atEnd() { skip(); return _at == _text.size(); }

  /** A condition. */
  std::string condition(unsigned depth)
  {
    if (depth > MAX_DEPTH || !open()) return fail();
    std::string head = word();
    std::string result;
    if (head == "forall" || head == "exists") {
      std::string variable = this->variable();
      std::string guard = set(variable);
      std::string body = condition(depth + 1);
      bool universal = head == "forall";
      if (!guard.empty()) body = "(" + guard + (universal ? " => " : " & ") + body + ")";
      result = std::string(universal ? "(![" : "(?[") + variable + ":" + sort() + "]: " + body + ")";
    } else if (head == "and" || head == "or" || head == "implies" || head == "iff") {
      std::string first = condition(depth + 1), second = condition(depth + 1);
      result = "(" + first + (head == "and" ? " & " : head == "or" ? " | " : head == "implies" ? " => " : " <=> ") + second + ")";
    } else if (head == "not") {
      result = "~(" + condition(depth + 1) + ")";
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
  bool _failed = false;
  unsigned _fresh = 0;  // names for the factors of "divides"

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

  /** (var N): the variable of the letter number N. */
  std::string variable()
  {
    if (!open() || word() != "var") return fail();
    std::string letter = word();
    if (!whole(letter, false) || !close()) return fail();
    return "X" + letter;
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
  }
  return statement;
}

std::string NumberStatement::tptp(bool denied) const
{
  return "tff(statement, conjecture, " + (denied ? "~(" + _formula + ")" : _formula) + ").\n";
}

} // namespace Math
