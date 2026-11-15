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
 * @file LaTeX.cpp
 * Implements the LaTeX frontend described in LaTeX.hpp.
 */

#include "LaTeX.hpp"

namespace Parse {

LaTeX::LaTeX(std::string text) : _text(std::move(text)), _position(_text.c_str()) {}

bool LaTeX::isLatexFile(const std::string& name)
{
  static const std::string ending = ".tex";
  return name.size() >= ending.size() && name.compare(name.size() - ending.size(), ending.size(), ending) == 0;
}

bool LaTeX::next(Item& item)
{
  const char *begin, *end;
  if (qr_next_item(&_position, &begin, &end)) {
    _anyItem = true;
    item = Item();
    item.number = ++_count;
    item.text.assign(begin, end);
  } else {
    /* No \item at all: the input is one bare formula, on its first line
     * that is not blank. It is wrapped as the text of an \item, so that
     * from here on there is one way of reading a statement. */
    if (_anyItem || _bareDone) return false;
    _bareDone = true;
    size_t start = _text.find_first_not_of(" \t\r\n");
    if (start == std::string::npos) return false;
    size_t stop = _text.find_first_of("\r\n", start);
    std::string line = _text.substr(start, stop == std::string::npos ? std::string::npos : stop - start);
    item = Item();
    item.number = ++_count;
    item.bare = true;
    item.text = "$\\displaystyle " + line + "$";
  }

  const char* formula = nullptr;
  const char* problem = qr_item_formula(item.text.c_str(), item.text.c_str() + item.text.size(), &formula);
  if (problem) item.unreadable = problem;
  else item.formula = formula;
  return true;
}

LaTeX::Statement LaTeX::read(const Item& item)
{
  const char* begin = item.text.c_str();
  const char* end = begin + item.text.size();
  Statement statement;
  statement.verdict = qr_decide_item(begin, end, /* delegate_logic */ 1);
  if (statement.verdict.outcome != QR_LOGIC) return statement;

  /* The engine handed the statement over. It is given to Vampire only if
   * the typed reading succeeds and the statement is first-order over plain
   * sorts; otherwise it goes back to the engine, whose procedures know the
   * sets of parts and of maps for what they are. */
  if (statement.verdict.logic) {
    statement.logic = Math::LogicStatement::read(statement.verdict.logic, statement.verdict.wants_example != 0);
    statement.notTranslated = statement.logic.outside();
  } else {
    statement.notTranslated = "the statement cannot be written in the language of the certificates";
  }
  if (statement.notTranslated.empty()) {
    statement.kind = Kind::LOGIC;
    statement.conditional = statement.verdict.conditional != 0;
    return statement;
  }
  statement.verdict = qr_decide_item(begin, end, 0);
  return statement;
}

} // namespace Parse
