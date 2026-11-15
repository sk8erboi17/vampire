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
 * @file Names.hpp
 * How the name of a symbol is written for a reader, in LaTeX.
 *
 * A statement read from LaTeX reaches Vampire with the names the frontend
 * gives its symbols in the language of the certificates: a letter with its
 * subscript run together (x1 for x_{1}), or the letters of the LaTeX command
 * the symbol was written with (perp for \perp, alpha for \alpha, le for
 * \le). To show a formula or a model to a person the name must go back to
 * what was written; latexName() does that, and says whether the symbol is
 * one that is written between its two arguments.
 *
 * Which names are commands is asked of the frontend itself
 * (qr_symbol_commands() in Math/Engine.h): the lists exist once, there.
 */

#ifndef __Math_Names__
#define __Math_Names__

#include <cctype>
#include <string>

#include "Math/Engine.h"

namespace Math {

/** A name ready for a formula in LaTeX. */
struct LatexName {
  std::string latex;   // without dollars
  bool infix = false;  // an operation or an order relation: written between its two arguments
};

/** Text made safe for LaTeX text mode (inside \mathrm or \texttt). */
inline std::string latexEscape(const std::string& text)
{
  std::string result;
  for (char c : text) {
    switch (c) {
      case '_': case '$': case '%': case '&': case '#': case '{': case '}':
        result += '\\';
        result += c;
        break;
      case '\\': result += "\\textbackslash{}"; break;
      case '^':  result += "\\textasciicircum{}"; break;
      case '~':  result += "\\textasciitilde{}"; break;
      case '<':  result += "\\textless{}"; break;
      case '>':  result += "\\textgreater{}"; break;
      case '|':  result += "\\textbar{}"; break;
      default:   result += c;
    }
  }
  return result;
}

/**
 * The LaTeX form of a symbol name as Vampire holds it.
 *
 *   f, x1               a letter, with its digits as a subscript
 *   perp, circ2, leS    a command of the frontend, with a subscript of digits or of one letter
 *   sK0, inhabited_S    names made by Vampire or by the translation: upright, the last part as a subscript
 *   anything else       upright, as it is
 */
inline LatexName latexName(const std::string& printed)
{
  /* Vampire keeps a name that is not a lower-case word between single
   * quotes, as TPTP wants it written: the quotes are not part of the name. */
  std::string raw = printed;
  if (raw.size() >= 2 && raw.front() == '\'' && raw.back() == '\'') raw = raw.substr(1, raw.size() - 2);

  auto allDigits = [](const std::string& text) {
    for (char c : text) if (!std::isdigit((unsigned char)c)) return false;
    return true;
  };

  /* A command, alone or with its subscript: the whole name must be used up,
   * so that "pizza" is not \pi with something after it. */
  auto command = [&](const char* name, bool infix, LatexName& result) {
    std::string prefix(name);
    if (raw.compare(0, prefix.size(), prefix) != 0) return false;
    std::string rest = raw.substr(prefix.size());
    bool letter = rest.size() == 1 && std::isalpha((unsigned char)rest[0]);
    if (!rest.empty() && !allDigits(rest) && !letter) return false;
    result.latex = "\\" + prefix + (rest.empty() ? "" : "_{" + rest + "}");
    result.infix = infix;
    return true;
  };
  LatexName result;
  static const struct { QrCommands list; bool infix; } LISTS[] = {
    {QR_COMMANDS_RELATIONS, true}, {QR_COMMANDS_OPERATIONS, true}, {QR_COMMANDS_GREEK, false}};
  for (const auto& entry : LISTS) {
    size_t count = 0;
    const char* const* names = qr_symbol_commands(entry.list, &count);
    for (size_t i = 0; i < count; i++) if (command(names[i], entry.infix, result)) return result;
  }

  /* Letters, then digits, then possibly "_" and a last part. */
  size_t letters = 0;
  while (letters < raw.size() && std::isalpha((unsigned char)raw[letters])) letters++;
  size_t digits = letters;
  while (digits < raw.size() && std::isdigit((unsigned char)raw[digits])) digits++;
  if (letters == 0) { result.latex = "\\mathrm{" + latexEscape(raw) + "}"; return result; }

  std::string head = letters == 1 ? raw.substr(0, 1) : "\\mathrm{" + raw.substr(0, letters) + "}";
  if (digits == raw.size()) { result.latex = digits == letters ? head : head + "_{" + raw.substr(letters) + "}"; return result; }

  /* A last part after one underscore, made of letters and digits only, is
   * written as a subscript: inhabited_S is "inhabited" of S. */
  bool subscript = digits == letters && raw[letters] == '_' && letters + 1 < raw.size();
  for (size_t i = letters + 1; i < raw.size() && subscript; i++) subscript = std::isalnum((unsigned char)raw[i]);
  result.latex = subscript ? head + "_{" + raw.substr(letters + 1) + "}" : "\\mathrm{" + latexEscape(raw) + "}";
  return result;
}

} // namespace Math

#endif // __Math_Names__
