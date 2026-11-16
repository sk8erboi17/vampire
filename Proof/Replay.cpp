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
 * @file Replay.cpp
 * Implements Replay: the clauses and steps of the independent checker,
 * mirrored, and the search for the steps that rebuild an inference.
 */

#include "Replay.hpp"

#include <set>
#include <sstream>

namespace Proof {

/* How many steps of the checker one inference of Vampire may need. A
 * demodulation that rewrites a term occurring three times in a literal
 * needs three; a resolution whose result has to lose a repeated equation
 * needs two. Past this the inference is given up, not the proof search. */
static constexpr int MAX_CHAIN = 5;

/* How many steps may be tried to rebuild one inference. The chains are
 * tried shortest first, and nearly every inference is one step, found at
 * once; the limit only stops a long clause from being tried in every way. */
static constexpr unsigned MAX_WORK = 20000;

/* How many assignments may be tried to rebuild a verdict of the SAT solver
 * as resolutions. The clauses of names in a proof are few, and with unit
 * propagation nearly all of them are decided without a choice. */
static constexpr unsigned MAX_SAT_WORK = 200000;

/* ------------------------------------------------------------------------
 * Terms and clauses, as the checker writes and reads them
 * ------------------------------------------------------------------------ */

int Replay::term(int symbol, const std::vector<int>& arguments)
{
  auto key = std::make_pair(symbol, arguments);
  auto found = _termIndex.find(key);
  if (found != _termIndex.end()) return found->second;
  if (_terms.empty()) _terms.push_back({-1, {}});  // reference 0 is "no term"
  _terms.push_back({symbol, arguments});
  int index = (int)_terms.size() - 1;
  _termIndex[key] = index;
  return index;
}

/** Skips spaces. */
static void skip(const std::string& text, size_t& at)
{
  while (at < text.size() && (text[at] == ' ' || text[at] == '\t')) at++;
}

/** Reads the word at @b at, up to a space or a parenthesis. */
static std::string word(const std::string& text, size_t& at)
{
  skip(text, at);
  size_t start = at;
  while (at < text.size() && text[at] != ' ' && text[at] != '\t' && text[at] != '(' && text[at] != ')') at++;
  return text.substr(start, at - start);
}

/** Reads a non-negative number. Returns false if there is none. */
static bool number(const std::string& text, size_t& at, int& value)
{
  std::string digits = word(text, at);
  if (digits.empty() || digits.size() > 9) return false;
  value = 0;
  for (char c : digits) {
    if (c < '0' || c > '9') return false;
    value = 10 * value + (c - '0');
  }
  return true;
}

static bool open(const std::string& text, size_t& at)
{
  skip(text, at);
  if (at < text.size() && text[at] == '(') { at++; return true; }
  return false;
}

static bool close(const std::string& text, size_t& at)
{
  skip(text, at);
  if (at < text.size() && text[at] == ')') { at++; return true; }
  return false;
}

/** A term: (v N) or (f N TERM...). */
bool Replay::parseTerm(const std::string& text, size_t& at, int& result)
{
  if (!open(text, at)) return false;
  std::string head = word(text, at);
  int n;
  if (!number(text, at, n)) return false;
  if (head == "v") {
    result = -n - 1;
    return close(text, at);
  }
  if (head != "f" || n >= (int)_symbols.size()) return false;
  std::vector<int> arguments;
  while (!close(text, at)) {
    int argument;
    if (!parseTerm(text, at, argument)) return false;
    arguments.push_back(argument);
  }
  if ((int)arguments.size() != _symbols[n].arity) return false;
  result = term(n, arguments);
  return true;
}

bool Replay::parseClause(const std::string& text, Clause& clause)
{
  size_t at = 0;
  if (!open(text, at) || word(text, at) != "clause") return false;
  clause = Clause();
  int highest = -1;
  while (!close(text, at)) {
    if (!open(text, at)) return false;
    std::string kind = word(text, at);
    Literal literal;
    if (kind == "true" || kind == "false") {
      literal.negative = kind == "false";
    } else {
      bool equation = kind == "eq" || kind == "ne";
      if (!equation && kind != "pos" && kind != "neg") return false;
      literal.negative = kind == "ne" || kind == "neg";
      if (!parseTerm(text, at, literal.left) || (equation && !parseTerm(text, at, literal.right))) return false;

      /* An atom is a predicate applied, the sides of an equation are elements. */
      if (!equation && (literal.left < 0 || !_symbols[_terms[literal.left].symbol].predicate)) return false;
    }
    if (!close(text, at)) return false;
    clause.literals.push_back(literal);
  }

  /* The variables are counted by the largest number that occurs. */
  std::vector<int> pending;
  for (const Literal& literal : clause.literals) { pending.push_back(literal.left); pending.push_back(literal.right); }
  while (!pending.empty()) {
    int t = pending.back();
    pending.pop_back();
    if (t < 0) { if (-t - 1 > highest) highest = -t - 1; }
    else if (t > 0) for (int argument : _terms[t].arguments) pending.push_back(argument);
  }
  clause.variables = highest + 1;
  skip(text, at);
  return at == text.size();
}

std::string Replay::printTerm(int t) const
{
  if (t < 0) return "(v " + std::to_string(-t - 1) + ")";
  std::string text = "(f " + std::to_string(_terms[t].symbol);
  for (int argument : _terms[t].arguments) text += " " + printTerm(argument);
  return text + ")";
}

std::string Replay::printClause(const Clause& clause) const
{
  std::string text = "(clause";
  for (const Literal& literal : clause.literals) {
    if (!literal.left) { text += literal.negative ? " (false)" : " (true)"; continue; }
    text += literal.right ? (literal.negative ? " (ne " : " (eq ") : (literal.negative ? " (neg " : " (pos ");
    text += printTerm(literal.left);
    if (literal.right) text += " " + printTerm(literal.right);
    text += ")";
  }
  return text + ")";
}

bool Replay::start(const std::string& handedOver)
{
  /* The beginning of the certificate: up to the line "clausify", and the
   * lines that may follow it and that the checker turns into clauses by
   * itself: "comprehend" (an instance of a formula on the parts of a set)
   * and "biject" (a pair of maps offered as a bijection and its inverse). */
  std::istringstream lines(handedOver);
  std::string line;
  bool clausified = false, listed = false;
  while (!listed && std::getline(lines, line)) {
    listed = line.compare(0, 8, "symbols ") == 0;
    if (listed) break;
    if (clausified && line.compare(0, 11, "comprehend ") != 0 && line.compare(0, 7, "biject ") != 0) return false;
    _prefix += line + "\n";
    clausified = clausified || line.compare(0, 8, "clausify") == 0;
  }
  if (!clausified || !listed) return false;

  int count;
  size_t at = 0;
  if (word(line, at) != "symbols" || !number(line, at, count)) return false;
  for (int i = 0; i < count; i++) {
    int arity, predicate;
    at = 0;
    if (!std::getline(lines, line) || !number(line, at, arity) || !number(line, at, predicate)) return false;
    _symbols.push_back({arity, predicate != 0});
  }
  at = 0;
  if (!std::getline(lines, line) || word(line, at) != "clauses" || !number(line, at, count)) return false;
  for (int i = 0; i < count; i++) {
    Clause clause;
    if (!std::getline(lines, line) || !parseClause(line, clause)) return false;
    _clauses.push_back(clause);
  }
  _initial = count;
  _initialSymbols = _symbols.size();
  return true;
}

void Replay::restart()
{
  _clauses.resize(_initial);
  _stepLines.clear();
  _symbols.resize(_initialSymbols);
  _unitClause.clear();
  _components.clear();
  _symbolVariable.clear();
  _componentUnit.clear();
  _componentCount = 0;
  _again = false;
}

/* ------------------------------------------------------------------------
 * A step, computed as the checker computes it
 * ------------------------------------------------------------------------
 *
 * Checklist: these functions follow ck_r_instance(), ck_r_normal(),
 * ck_r_replace() and ck_r_step() in Math/quaerens/checker.c. They are not
 * what makes a certificate valid (the checker is), but if they compute a
 * result the checker would not, every certificate is rejected.
 */

/** The term with its variables moved by offset and then substituted; a substituted term is not substituted again. */
int Replay::instance(int t, int offset, const std::map<int, int>& substitution)
{
  if (!t) return 0;
  if (t < 0) {
    int variable = -t - 1 + offset;
    auto found = substitution.find(variable);
    return found != substitution.end() ? found->second : -variable - 1;
  }
  std::vector<int> arguments;
  for (int argument : _terms[t].arguments) arguments.push_back(instance(argument, offset, substitution));
  return term(_terms[t].symbol, arguments);
}

Replay::Clause Replay::instances(const Clause& clause, int offset, const std::map<int, int>& substitution)
{
  Clause result;
  for (Literal literal : clause.literals) {
    literal.left = instance(literal.left, offset, substitution);
    literal.right = instance(literal.right, offset, substitution);
    result.literals.push_back(literal);
  }
  return result;
}

int Replay::rename(int t, std::map<int, int>& names, int& used)
{
  if (!t) return 0;
  if (t < 0) {
    auto found = names.find(-t - 1);
    if (found == names.end()) found = names.emplace(-t - 1, used++).first;
    return -found->second - 1;
  }
  std::vector<int> arguments;
  for (int argument : _terms[t].arguments) arguments.push_back(rename(argument, names, used));
  return term(_terms[t].symbol, arguments);
}

/** Drops "false", renames the variables in the order they are met, drops a literal written twice. */
Replay::Clause Replay::normal(const Clause& source)
{
  Clause result;
  std::map<int, int> names;
  for (Literal literal : source.literals) {
    if (!literal.left && literal.negative) continue;
    literal.left = rename(literal.left, names, result.variables);
    literal.right = rename(literal.right, names, result.variables);
    bool duplicate = false;
    for (const Literal& kept : result.literals)
      duplicate = duplicate || (kept.left == literal.left && kept.right == literal.right && kept.negative == literal.negative);
    if (!duplicate) result.literals.push_back(literal);
  }
  return result;
}

/** The same atom, an equation being the same whichever way round it is written. */
bool Replay::sameAtom(const Literal& a, const Literal& b)
{
  return (a.left == b.left && a.right == b.right) || (a.right && b.right && a.left == b.right && a.right == b.left);
}

/** Replaces the subterm at the place number position (counting every subterm from 0, the term first) if it is expected. */
int Replay::replace(int t, int position, int& cursor, int expected, int replacement, bool& found)
{
  if (cursor++ == position) {
    if (t <= 0 || t != expected) return t;
    found = true;
    return replacement;
  }
  if (t <= 0) return t;
  std::vector<int> arguments;
  for (int argument : _terms[t].arguments) arguments.push_back(replace(argument, position, cursor, expected, replacement, found));
  return term(_terms[t].symbol, arguments);
}

/** Computes the result of a step, normalised. Returns false if the step is not one the checker would accept. */
bool Replay::apply(const Step& step, Clause& result)
{
  const Clause& first = _clauses[step.p];
  bool pair = step.rule == Rule::RESOLVE || step.rule == Rule::SUPER;
  const Clause& second = pair ? _clauses[step.q] : first;
  if (step.lp >= (int)first.literals.size() || step.lq >= (int)second.literals.size()) return false;

  Clause a = instances(first, 0, step.substitution);
  Clause b = instances(second, pair ? offsetOf(first) : 0, step.substitution);
  Literal x = a.literals[step.lp], y = b.literals[step.lq];
  Clause raw;
  auto allBut = [&](const Clause& clause, int omitted) {
    for (int i = 0; i < (int)clause.literals.size(); i++) if (i != omitted) raw.literals.push_back(clause.literals[i]);
  };

  switch (step.rule) {
    case Rule::RESOLVE:
      if (x.negative == y.negative || !x.left || !sameAtom(x, y)) return false;
      allBut(a, step.lp);
      allBut(b, step.lq);
      break;
    case Rule::REFLEX:
      if (!x.negative || !x.right || x.left != x.right) return false;
      allBut(a, step.lp);
      break;
    case Rule::FACTOR:
      if (step.lp == step.lq || x.negative != y.negative || !x.left || !sameAtom(x, y)) return false;
      allBut(a, step.lp);
      break;
    case Rule::SUPER: {
      if (x.negative || !x.right || (step.side && !y.right) || (!y.right && step.position == 0)) return false;
      int lhs = step.flip ? x.right : x.left, rhs = step.flip ? x.left : x.right, cursor = 0;
      bool found = false;
      int target = replace(step.side ? y.right : y.left, step.position, cursor, lhs, rhs, found);
      if (!found) return false;
      if (step.side) y.right = target; else y.left = target;
      allBut(a, step.lp);
      for (int i = 0; i < (int)b.literals.size(); i++) raw.literals.push_back(i == step.lq ? y : b.literals[i]);
      break;
    }
    case Rule::EQUALFACTOR: {
      if (step.lp == step.lq || x.negative || y.negative || !x.right || !y.right) return false;
      int xl = step.flip ? x.right : x.left, xr = step.flip ? x.left : x.right;
      int yl = step.otherflip ? y.right : y.left, yr = step.otherflip ? y.left : y.right;
      if (xl != yl) return false;
      allBut(a, step.lp);
      Literal difference;
      difference.left = xr;
      difference.right = yr;
      difference.negative = true;
      raw.literals.push_back(difference);
      break;
    }
  }
  result = normal(raw);
  return true;
}

/* ------------------------------------------------------------------------
 * Unification
 * ------------------------------------------------------------------------
 *
 * The bindings map a variable to a term, and a term may contain variables
 * that are bound in turn (the usual triangular form). The checker wants a
 * simultaneous substitution, in which a substituted term is not
 * substituted again: simultaneous() resolves every binding to the end.
 */

int Replay::resolve(int t, const std::map<int, int>& bindings)
{
  if (!t) return 0;
  if (t < 0) {
    auto found = bindings.find(-t - 1);
    return found == bindings.end() ? t : resolve(found->second, bindings);
  }
  std::vector<int> arguments;
  for (int argument : _terms[t].arguments) arguments.push_back(resolve(argument, bindings));
  return term(_terms[t].symbol, arguments);
}

bool Replay::occurs(int variable, int t, const std::map<int, int>& bindings)
{
  if (t < 0) {
    if (-t - 1 == variable) return true;
    auto found = bindings.find(-t - 1);
    return found != bindings.end() && occurs(variable, found->second, bindings);
  }
  for (int argument : _terms[t].arguments) if (occurs(variable, argument, bindings)) return true;
  return false;
}

bool Replay::unify(int a, int b, std::map<int, int>& bindings)
{
  /* A bound variable stands for its term. */
  for (auto found = bindings.end(); a < 0 && (found = bindings.find(-a - 1)) != bindings.end();) a = found->second;
  for (auto found = bindings.end(); b < 0 && (found = bindings.find(-b - 1)) != bindings.end();) b = found->second;
  if (a == b) return true;
  if (!a || !b) return false;
  if (a < 0 || b < 0) {
    int variable = a < 0 ? -a - 1 : -b - 1, other = a < 0 ? b : a;
    if (occurs(variable, other, bindings)) return false;
    bindings[variable] = other;
    return true;
  }
  if (_terms[a].symbol != _terms[b].symbol) return false;
  for (size_t i = 0; i < _terms[a].arguments.size(); i++)
    if (!unify(_terms[a].arguments[i], _terms[b].arguments[i], bindings)) return false;
  return true;
}

std::map<int, int> Replay::simultaneous(const std::map<int, int>& bindings)
{
  std::map<int, int> result;
  for (const auto& binding : bindings) result[binding.first] = resolve(binding.second, bindings);
  return result;
}

/* ------------------------------------------------------------------------
 * The same clause, as Vampire and as the checker write it
 * ------------------------------------------------------------------------
 *
 * Vampire's clause and the certificate's differ in the names of the
 * variables, in the order of the literals and in which way round an
 * equation is written. They are the same clause if there is a one-to-one
 * renaming of the variables and a one-to-one pairing of the literals that
 * makes them equal; this is found by trying, the clauses being short.
 */

bool Replay::matchTerms(int a, int b, std::map<int, int>& forward, std::map<int, int>& backward)
{
  if (a < 0 || b < 0) {
    if (a >= 0 || b >= 0) return false;
    auto there = forward.find(a), back = backward.find(b);
    if (there != forward.end() || back != backward.end())
      return there != forward.end() && back != backward.end() && there->second == b && back->second == a;
    forward[a] = b;
    backward[b] = a;
    return true;
  }
  if (!a || !b) return a == b;
  if (_terms[a].symbol != _terms[b].symbol) return false;
  for (size_t i = 0; i < _terms[a].arguments.size(); i++)
    if (!matchTerms(_terms[a].arguments[i], _terms[b].arguments[i], forward, backward)) return false;
  return true;
}

bool Replay::matchLiterals(const Clause& a, const Clause& b, size_t at, std::vector<bool>& used,
                           std::map<int, int>& forward, std::map<int, int>& backward)
{
  if (at == a.literals.size()) return true;
  const Literal& x = a.literals[at];
  for (size_t j = 0; j < b.literals.size(); j++) {
    const Literal& y = b.literals[j];
    if (used[j] || x.negative != y.negative || !x.right != !y.right || !x.left != !y.left) continue;
    for (int swapped = 0; swapped < (x.right ? 2 : 1); swapped++) {
      std::map<int, int> there = forward, back = backward;
      if (!matchTerms(x.left, swapped ? y.right : y.left, there, back)) continue;
      if (!matchTerms(x.right, swapped ? y.left : y.right, there, back)) continue;
      used[j] = true;
      if (matchLiterals(a, b, at + 1, used, there, back)) return true;
      used[j] = false;
    }
  }
  return false;
}

bool Replay::sameClause(const Clause& a, const Clause& b)
{
  if (a.literals.size() != b.literals.size()) return false;
  std::vector<bool> used(b.literals.size(), false);
  std::map<int, int> forward, backward;
  return matchLiterals(a, b, 0, used, forward, backward);
}

/* ------------------------------------------------------------------------
 * From an inference of Vampire to steps of the checker
 * ------------------------------------------------------------------------ */

/** Adds the clause a step gives, with the step written out. Returns its index. */
int Replay::push(const Step& step, const Clause& result)
{
  static const char* const NAMES[] = {"resolve", "reflex", "factor", "super", "equalfactor"};
  std::ostringstream line;
  line << "step " << NAMES[static_cast<int>(step.rule)] << " " << step.p << " " << step.lp;
  switch (step.rule) {
    case Rule::RESOLVE:     line << " " << step.q << " " << step.lq; break;
    case Rule::REFLEX:      break;
    case Rule::FACTOR:      line << " " << step.lq; break;
    case Rule::SUPER:       line << " " << step.flip << " " << step.q << " " << step.lq << " " << step.side << " " << step.position; break;
    case Rule::EQUALFACTOR: line << " " << step.flip << " " << step.lq << " " << step.otherflip; break;
  }
  line << " (subst";
  for (const auto& binding : step.substitution) line << " (" << binding.first << " " << printTerm(binding.second) << ")";
  line << ") " << printClause(result) << "\n";
  return add(line.str(), result);
}

/** Adds a clause with the line of the certificate that gives it. Returns its index. */
int Replay::add(const std::string& line, const Clause& clause)
{
  _clauses.push_back(clause);
  _stepLines.push_back(line);
  return (int)_clauses.size() - 1;
}

std::string Replay::certificate() const
{
  std::string text = _prefix;
  for (const std::string& line : _stepLines) text += line;
  return text + "end\n";
}

/** Forgets the clauses from index @b clauses on: steps that led nowhere. */
void Replay::pop(int clauses)
{
  _clauses.resize(clauses);
  _stepLines.resize(clauses - _initial);
}

/** Lists the subterms of a term that are not variables, each with its place number. */
void Replay::subterms(int t, int& cursor, std::vector<std::pair<int, int>>& found)
{
  int position = cursor++;
  if (t <= 0) return;
  found.emplace_back(position, t);
  for (int argument : _terms[t].arguments) subterms(argument, cursor, found);
}

/**
 * Merges the literals of the clause number @b index that are the same
 * equation written the two ways round, one factoring step for each, and
 * returns the index of the clause that has none left.
 *
 * The checker drops a literal that is written twice in the same way, but
 * keeps s = t beside t = s; Vampire has one literal for both. So after a
 * step the checker's clause may have such a pair where Vampire's has one
 * literal. Merging them is always right (it is factoring with no
 * substitution), and doing it at once, rather than leaving it to the
 * search, is what keeps the search short: a resolvent with three such
 * pairs would otherwise need a chain of four steps to be found by trying.
 */
int Replay::tidy(int index)
{
  for (bool merged = true; merged;) {
    merged = false;
    const Clause clause = _clauses[index];
    for (size_t i = 0; i < clause.literals.size() && !merged; i++) {
      for (size_t j = i + 1; j < clause.literals.size() && !merged; j++) {
        const Literal& x = clause.literals[i];
        const Literal& y = clause.literals[j];
        if (!x.left || x.negative != y.negative || !sameAtom(x, y)) continue;
        Step step;
        step.rule = Rule::FACTOR;
        step.p = index;
        step.lp = (int)j;
        step.lq = (int)i;
        Clause result;
        if (!apply(step, result)) continue;
        index = push(step, result);
        merged = true;
      }
    }
  }
  return index;
}

bool Replay::tryStep(const Step& step, const Clause& target, int depth, const std::vector<int>& equations, int& reached)
{
  Clause result;
  if (++_work > MAX_WORK || !apply(step, result)) return false;
  int mark = (int)_clauses.size();
  int index = tidy(push(step, result));
  if (reach(index, target, depth - 1, equations, reached)) return true;
  pop(mark);
  return false;
}

/**
 * Looks for steps that lead from the clause number @b from to @b target:
 * none, if it is the same clause already; otherwise a step on the clause
 * alone (an inequality s != s removed, two literals merged), or one more
 * rewriting with an equation of @b equations, and then again, for at most
 * @b depth steps. On success @b reached is the index of the clause that is
 * the target.
 */
bool Replay::reach(int from, const Clause& target, int depth, const std::vector<int>& equations, int& reached)
{
  if (sameClause(_clauses[from], target)) { reached = from; return true; }
  if (depth <= 0) return false;
  const Clause clause = _clauses[from];
  int count = (int)clause.literals.size();

  for (int i = 0; i < count; i++) {
    const Literal& x = clause.literals[i];

    /* s != t with s and t made equal: the inequality goes. */
    if (x.negative && x.right) {
      std::map<int, int> bindings;
      if (unify(x.left, x.right, bindings)) {
        Step step;
        step.rule = Rule::REFLEX;
        step.p = from;
        step.lp = i;
        step.substitution = simultaneous(bindings);
        if (tryStep(step, target, depth, equations, reached)) return true;
      }
    }
    for (int j = 0; j < count; j++) {
      const Literal& y = clause.literals[j];
      if (i == j || !x.left || !y.left || !x.right != !y.right) continue;

      /* Two literals of the same sign made equal: one goes. */
      for (int swapped = 0; x.negative == y.negative && swapped < (x.right ? 2 : 1); swapped++) {
        std::map<int, int> bindings;
        if (!unify(x.left, swapped ? y.right : y.left, bindings) || !unify(x.right, swapped ? y.left : y.right, bindings)) continue;
        Step step;
        step.rule = Rule::FACTOR;
        step.p = from;
        step.lp = i;
        step.lq = j;
        step.substitution = simultaneous(bindings);
        if (tryStep(step, target, depth, equations, reached)) return true;
      }

      /* Two equations with a side made equal: s = t or s = u gives s = u or t != u. */
      for (int flips = 0; !x.negative && !y.negative && x.right && flips < 4; flips++) {
        int flip = flips & 1, otherflip = flips >> 1;
        std::map<int, int> bindings;
        if (!unify(flip ? x.right : x.left, otherflip ? y.right : y.left, bindings)) continue;
        Step step;
        step.rule = Rule::EQUALFACTOR;
        step.p = from;
        step.lp = i;
        step.flip = flip;
        step.lq = j;
        step.otherflip = otherflip;
        step.substitution = simultaneous(bindings);
        if (tryStep(step, target, depth, equations, reached)) return true;
      }
    }
  }

  /* One more rewriting, or one more resolution, with a premise of the inference. */
  for (int equation : equations) {
    const Clause other = _clauses[equation];
    int offset = offsetOf(other);
    for (int i = 0; i < (int)other.literals.size(); i++) {
      const Literal& x = other.literals[i];
      for (int j = 0; j < count; j++) {
        const Literal& y = clause.literals[j];
        int yl = instance(y.left, offset, {}), yr = instance(y.right, offset, {});

        /* Resolution: a literal of one, the opposite literal of the other. */
        for (int swapped = 0; x.left && y.left && x.negative != y.negative && !x.right == !y.right && swapped < (x.right ? 2 : 1); swapped++) {
          std::map<int, int> bindings;
          if (!unify(x.left, swapped ? yr : yl, bindings) || !unify(x.right, swapped ? yl : yr, bindings)) continue;
          Step step;
          step.rule = Rule::RESOLVE;
          step.p = equation;
          step.lp = i;
          step.q = from;
          step.lq = j;
          step.substitution = simultaneous(bindings);
          if (tryStep(step, target, depth, equations, reached)) return true;
        }

        /* Superposition: a side of an equation of one, a subterm of the other. */
        if (x.negative || !x.right || !y.left) continue;
        for (int flip = 0; flip < 2; flip++) {
          int lhs = flip ? x.right : x.left;
          if (lhs < 0) continue;
          for (int side = 0; side < (y.right ? 2 : 1); side++) {
            std::vector<std::pair<int, int>> places;
            int cursor = 0;
            subterms(side ? yr : yl, cursor, places);
            for (const auto& place : places) {
              if (!y.right && place.first == 0) continue;  // the atom itself is not a term
              std::map<int, int> bindings;
              if (!unify(lhs, place.second, bindings)) continue;
              Step step;
              step.rule = Rule::SUPER;
              step.p = equation;
              step.lp = i;
              step.flip = flip;
              step.q = from;
              step.lq = j;
              step.side = side;
              step.position = place.first;
              step.substitution = simultaneous(bindings);
              if (tryStep(step, target, depth, equations, reached)) return true;
            }
          }
        }
      }
    }
  }
  return false;
}

bool Replay::derive(unsigned unit, const std::vector<unsigned>& premises, const Clause& written,
                    const std::vector<unsigned>& levels)
{
  /* The premises first: one that is a component clause may get its lines
   * in the certificate only now, and the names below need them. */
  std::vector<int> parents;
  for (unsigned premise : premises) {
    int parent = clauseOf(premise);
    if (parent < 0) return false;
    parents.push_back(parent);
  }
  if (parents.empty() || parents.size() > 2) return false;

  /* Vampire keeps a literal that an inference produces twice until a later
   * simplification removes it; the checker never has a literal twice in a
   * clause. The clause meant is the same: the copies are dropped here, and
   * the later simplification will find that nothing is left for it to do. */
  Clause conclusion;
  for (const Literal& literal : written.literals) {
    bool repeated = false;
    for (const Literal& kept : conclusion.literals)
      repeated = repeated || (kept.negative == literal.negative && literal.left && sameAtom(kept, literal));
    if (!repeated) conclusion.literals.push_back(literal);
  }

  /* The assumptions of Vampire's clause are literals of the checker's. */
  for (unsigned level : levels) {
    Literal name;
    if (!nameLiteral(level, name)) return false;
    conclusion.literals.push_back(name);
  }

  /* From one premise: steps on it alone. From two: each in turn is the
   * clause worked on, and the other is the one it is resolved or rewritten
   * with, as many times as the inference needs. The shortest chain is
   * looked for first: one step, then two, and so on. */
  int mark = (int)_clauses.size(), reached = -1;
  bool found = false;
  _work = 0;
  for (int depth = 0; depth <= MAX_CHAIN && !found && _work <= MAX_WORK; depth++) {
    if (parents.size() == 1) {
      found = reach(parents[0], conclusion, depth, {}, reached);
    } else {
      found = reach(parents[0], conclusion, depth, {parents[1]}, reached);
      if (!found) { pop(mark); found = reach(parents[1], conclusion, depth, {parents[0]}, reached); }
    }
    if (!found) pop(mark);
  }
  if (!found) return false;
  _unitClause[unit] = reached;
  return true;
}

/* ------------------------------------------------------------------------
 * Splitting: names for clauses, and the clauses of names
 * ------------------------------------------------------------------------
 *
 * Checklist: define(), split() and the lines they write follow
 * ck_r_define_component(), ck_r_complement_component() and ck_r_split() in
 * Math/quaerens/checker.c.
 */

/** True if the literal is the proposition of a component, with either sign. */
bool Replay::isName(const Literal& literal) const
{
  return literal.left > 0 && !literal.right && _symbolVariable.count(_terms[literal.left].symbol) != 0;
}

/**
 * Writes the lines that give a component its proposition: the clause
 * @b key, as it is here, becomes the named clause. For a ground literal the
 * converse clause is written too. Returns false if the checker would not
 * take the clause as a component (it is empty, or holds a logical constant
 * or another name).
 */
bool Replay::define(unsigned variable, const Clause& key)
{
  Component& component = _components[variable];
  Clause named = normal(key);
  if (named.literals.empty()) return false;
  for (const Literal& literal : named.literals) if (!literal.left || isName(literal)) return false;

  component.key = named;
  component.number = _componentCount++;
  component.symbol = (int)_symbols.size();
  _symbols.push_back({0, true});
  _symbolVariable[component.symbol] = variable;

  Literal proposition;
  proposition.left = term(component.symbol, {});
  Clause definition = named;
  proposition.negative = true;
  definition.literals.push_back(proposition);
  component.definition = add("component " + printClause(named) + "\n", definition);

  if (!named.variables && named.literals.size() == 1) {
    Clause converse;
    Literal opposite = named.literals[0];
    opposite.negative = !opposite.negative;
    converse.literals.push_back(opposite);
    proposition.negative = false;
    converse.literals.push_back(proposition);
    component.complement = add("complement " + std::to_string(component.number) + "\n", converse);
  }
  component.defined = true;
  return true;
}

/** The component of a SAT variable, with its lines in the certificate; null if Vampire gave no definition of it. */
Replay::Component* Replay::named(unsigned variable)
{
  auto found = _components.find(variable);
  if (found == _components.end()) return nullptr;
  if (!found->second.defined) {
    /* The clause as Vampire defines it, or, on a later attempt, as the
     * splitting that needs the name found it written (restart()). */
    auto preferred = _preferred.find(variable);
    if (!define(variable, preferred != _preferred.end() ? preferred->second : found->second.vampire)) return nullptr;
  }
  return &found->second;
}

/**
 * The literal that stands for an assumption of Vampire: a clause under the
 * assumption "b holds" is the clause with "not b" added, and under "b does
 * not hold" with "b" added.
 */
bool Replay::nameLiteral(unsigned level, Literal& literal)
{
  Component* component = named(level / 2 + 1);
  if (!component) return false;
  literal = Literal();
  literal.left = term(component->symbol, {});
  literal.negative = level % 2 == 0;
  return true;
}

/**
 * The clause of the certificate for a unit of Vampire's proof, or -1. A
 * component clause gets its lines here, the first time it is a premise,
 * unless a splitting has defined its name before: then the name stands for
 * the clause as that splitting found it written.
 */
int Replay::clauseOf(unsigned unit)
{
  auto found = _unitClause.find(unit);
  if (found != _unitClause.end()) return found->second;
  auto pending = _componentUnit.find(unit);
  if (pending == _componentUnit.end()) return -1;
  Component* component = named(pending->second / 2 + 1);
  if (!component) return -1;
  int index = pending->second % 2 ? component->complement : component->definition;
  if (index >= 0) _unitClause[unit] = index;
  return index;
}

/** True if the clause is made of names only and they are exactly @b names (v for a SAT variable, -v for its negation). */
bool Replay::namesAre(int index, const std::vector<int>& names) const
{
  std::set<int> got, wanted(names.begin(), names.end());
  for (const Literal& literal : _clauses[index].literals) {
    if (!isName(literal)) return false;
    int variable = (int)_symbolVariable.at(_terms[literal.left].symbol);
    got.insert(literal.negative ? -variable : variable);
  }
  return got == wanted;
}

/**
 * Finds in which order the literals of @b group must be listed so that,
 * with the variables renamed in the order they are met, they are @b key
 * literal by literal: that is how the checker compares a group with a
 * component. On success @b chosen holds the positions, in that order.
 */
bool Replay::inOrder(const Clause& group, const Clause& key, std::vector<int>& chosen, std::vector<bool>& used)
{
  if (chosen.size() == key.literals.size()) return true;
  for (size_t i = 0; i < group.literals.size(); i++) {
    if (used[i]) continue;
    chosen.push_back((int)i);
    Clause listed;
    for (int position : chosen) listed.literals.push_back(group.literals[position]);
    listed = normal(listed);
    const Literal& last = listed.literals.back();
    const Literal& wanted = key.literals[chosen.size() - 1];
    used[i] = true;
    if (listed.literals.size() == chosen.size() && last.left == wanted.left && last.right == wanted.right
        && last.negative == wanted.negative && inOrder(group, key, chosen, used)) return true;
    used[i] = false;
    chosen.pop_back();
  }
  return false;
}

bool Replay::split(unsigned unit, unsigned parent, const std::vector<int>& names)
{
  int current = clauseOf(parent);
  if (current < 0) return false;

  /* The components Vampire's clause of names speaks of. */
  std::vector<std::pair<int, unsigned>> candidates;  // the name as written, and its SAT variable
  for (int name : names) {
    unsigned variable = (unsigned)(name < 0 ? -name : name);
    if (_components.count(variable)) candidates.emplace_back(name, variable);
  }
  auto groundLiteral = [&](const Literal& literal) {
    Clause alone;
    alone.literals.push_back(literal);
    return normal(alone).variables == 0;
  };

  /* A ground literal is a component by itself, and its name means exactly
   * that literal: "A or not b" and "not A or b" are both there. Resolving
   * with the one that has the opposite literal puts the name in its place,
   * whichever way round an equation is written. */
  for (bool replaced = true; replaced;) {
    replaced = false;
    const Clause clause = _clauses[current];
    for (size_t i = 0; i < clause.literals.size() && !replaced; i++) {
      const Literal& literal = clause.literals[i];
      if (isName(literal) || !literal.left || !groundLiteral(literal)) continue;
      for (const auto& candidate : candidates) {
        Component& component = _components[candidate.second];
        const Clause& meant = component.vampire;
        if (meant.literals.size() != 1 || !groundLiteral(meant.literals[0]) || !sameAtom(meant.literals[0], literal)) continue;
        bool itself = meant.literals[0].negative == literal.negative;
        if (itself != (candidate.first > 0)) continue;  // v names the literal, -v its opposite
        if (!component.defined) {
          Clause key;
          key.literals.push_back(literal);
          key.literals[0].negative = meant.literals[0].negative;
          if (!define(candidate.second, key)) return false;
        }
        Step step;
        step.rule = Rule::RESOLVE;
        step.p = itself ? component.complement : component.definition;
        step.lp = 0;
        step.q = current;
        step.lq = (int)i;
        Clause result;
        if (step.p < 0 || !apply(step, result)) return false;
        current = push(step, result);
        replaced = true;
        break;
      }
      if (!replaced) return false;  // a ground literal that no name of Vampire's clause stands for
    }
  }

  /* What is left with variables: the groups of literals that share
   * variables, directly or through other literals. Two groups share none,
   * which is what lets "C or D, for all" be "C for all, or D for all". */
  const Clause clause = _clauses[current];
  std::vector<std::vector<int>> groups;
  std::vector<std::set<int>> groupVariables;
  for (size_t i = 0; i < clause.literals.size(); i++) {
    const Literal& literal = clause.literals[i];
    if (isName(literal)) continue;
    if (!literal.left) return false;
    std::set<int> variables;
    std::vector<int> pending = {literal.left, literal.right};
    while (!pending.empty()) {
      int t = pending.back();
      pending.pop_back();
      if (t < 0) variables.insert(t);
      else if (t > 0) for (int argument : _terms[t].arguments) pending.push_back(argument);
    }
    std::vector<int> members = {(int)i};
    for (size_t g = 0; g < groups.size();) {
      bool shares = false;
      for (int variable : groupVariables[g]) shares = shares || variables.count(variable);
      if (!shares) { g++; continue; }
      members.insert(members.begin(), groups[g].begin(), groups[g].end());
      variables.insert(groupVariables[g].begin(), groupVariables[g].end());
      groups.erase(groups.begin() + g);
      groupVariables.erase(groupVariables.begin() + g);
    }
    groups.push_back(members);
    groupVariables.push_back(variables);
  }

  if (!groups.empty()) {
    std::string line = "step split " + std::to_string(current) + " (groups";
    Clause raw;
    for (const std::vector<int>& members : groups) {
      Clause group;
      for (int position : members) group.literals.push_back(clause.literals[position]);
      Component* chosen = nullptr;
      std::vector<int> order;
      for (const auto& candidate : candidates) {
        Component& component = _components[candidate.second];
        if (candidate.first < 0 || !sameClause(normal(group), normal(component.vampire))) continue;
        if (!component.defined && !define(candidate.second, group)) return false;
        std::vector<bool> used(group.literals.size(), false);
        order.clear();
        if (component.key.literals.size() != group.literals.size() || !inOrder(group, component.key, order, used)) {
          /* The name stands for this clause with an equation the other
           * way round, and the checker would not take the group for it:
           * no step turns an equation round. If the name was given
           * before this splitting was met, giving it to the clause as it
           * is written here may do (restart()); if this is already the
           * second way it is found written, nothing will. */
          if (!_preferred.count(candidate.second)) {
            _preferred[candidate.second] = normal(group);
            _again = true;
          }
          continue;
        }
        chosen = &component;
        break;
      }
      if (!chosen) return false;
      line += " (" + std::to_string(chosen->number) + " 0";
      for (int position : order) line += " " + std::to_string(members[position]);
      line += ")";
      Literal name;
      name.left = term(chosen->symbol, {});
      raw.literals.push_back(name);
    }
    for (const Literal& literal : clause.literals) if (isName(literal)) raw.literals.push_back(literal);
    Clause result = normal(raw);
    current = add(line + ") " + printClause(result) + "\n", result);
  }

  if (!namesAre(current, names)) return false;
  _unitClause[unit] = current;
  return true;
}

bool Replay::contradiction(unsigned unit, unsigned parent, const std::vector<int>& names)
{
  int index = clauseOf(parent);
  if (index < 0 || !namesAre(index, names)) return false;
  _unitClause[unit] = index;
  return true;
}

/**
 * Looks for a clause, among those of @b pool or got from them by
 * resolution, all of whose literals are false when the propositions have
 * the values of @b value. Returns its index, or -1 if there is none (the
 * values can be completed so that every clause holds) or the work allowed
 * is used up.
 *
 * This is the classical reading of a search by cases as a proof. If a
 * clause of the pool is false already, that is the one. Otherwise take a
 * proposition b without a value (the only one left in some clause, if
 * there is such a clause). Let C1 be false with b true and C0 false with
 * b false. If C1 does not hold "not b", it is false whatever b is, and
 * likewise C0 without "b". Otherwise C1 = "not b or R1" and C0 = "b or R0",
 * and their resolvent "R0 or R1" is a clause all of whose literals are
 * false under the values given. With no values at all the clause found is
 * the empty one.
 */
int Replay::falsified(const std::vector<int>& pool, std::map<int, bool>& value)
{
  if (++_work > MAX_SAT_WORK) return -1;
  int chosen = 0;
  bool forced = false;
  for (int index : pool) {
    const Clause& clause = _clauses[index];
    int open = 0, candidate = 0;
    bool holds = false;
    for (const Literal& literal : clause.literals) {
      auto given = value.find(literal.left);
      if (given == value.end()) { open++; candidate = literal.left; }
      else if (given->second != literal.negative) holds = true;
    }
    if (holds) continue;
    if (!open) return index;
    if (open == 1 && !forced) { chosen = candidate; forced = true; }
    else if (!chosen) chosen = candidate;
  }
  if (!chosen) return -1;

  auto position = [&](int index, bool negative) {
    const Clause& clause = _clauses[index];
    for (size_t i = 0; i < clause.literals.size(); i++)
      if (clause.literals[i].left == chosen && clause.literals[i].negative == negative) return (int)i;
    return -1;
  };
  value[chosen] = true;
  int whenTrue = falsified(pool, value);
  value.erase(chosen);
  if (whenTrue < 0) return -1;
  int negativeAt = position(whenTrue, true);
  if (negativeAt < 0) return whenTrue;

  value[chosen] = false;
  int whenFalse = falsified(pool, value);
  value.erase(chosen);
  if (whenFalse < 0) return -1;
  int positiveAt = position(whenFalse, false);
  if (positiveAt < 0) return whenFalse;

  Step step;
  step.rule = Rule::RESOLVE;
  step.p = whenFalse;
  step.lp = positiveAt;
  step.q = whenTrue;
  step.lq = negativeAt;
  Clause result;
  if (!apply(step, result)) return -1;
  return push(step, result);
}

bool Replay::propositional(unsigned unit, const std::vector<unsigned>& premises)
{
  std::vector<int> pool;
  for (unsigned premise : premises) {
    int index = clauseOf(premise);
    if (index < 0) return false;
    for (const Literal& literal : _clauses[index].literals) if (!isName(literal)) return false;
    pool.push_back(index);
  }
  int mark = (int)_clauses.size();
  std::map<int, bool> value;
  _work = 0;
  int found = falsified(pool, value);
  if (found < 0 || !_clauses[found].literals.empty()) { pop(mark); return false; }
  _unitClause[unit] = found;
  return true;
}

bool Replay::refutes(unsigned unit) const
{
  auto found = _unitClause.find(unit);
  return found != _unitClause.end() && _clauses[found->second].literals.empty();
}

} // namespace Proof
