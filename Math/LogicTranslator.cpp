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
 * @file LogicTranslator.cpp
 * Implements the translation described in LogicTranslator.hpp.
 */

#include "LogicTranslator.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/Signature.hpp"
#include "Lib/Environment.hpp"
#include "Lib/List.hpp"
#include "Lib/Stack.hpp"
#include "Parse/TPTP.hpp"

namespace Math {

using namespace Kernel;
using Connective = LogicStatement::Connective;

LogicTranslator::LogicTranslator(const LogicStatement& statement) : _statement(statement) {}

/**
 * Declares sorts and symbols, and decides which sorts may be empty.
 *
 * A sort is certainly inhabited if
 *   - it is a set of parts (the empty part is always there), or
 *   - some function symbol into it has all its arguments in certainly
 *     inhabited sorts (a named element, or a written number, has none), or
 *   - it is a set of maps into a certainly inhabited sort (a constant map).
 * The least set closed under these rules is computed by repeating them
 * until nothing changes; the other sorts may be empty.
 */
void LogicTranslator::declare()
{
  const std::vector<LogicStatement::Sort>& sorts = _statement.sorts();
  const std::vector<LogicStatement::Symbol>& symbols = _statement.symbols();

  for (const LogicStatement::Sort& sort : sorts)
    _sorts.push_back(TermList(AtomicSort::createConstant(sort.name)));

  for (const LogicStatement::Symbol& symbol : symbols) {
    TermStack domain;
    for (unsigned sort : symbol.domain) domain.push(_sorts[sort]);
    if (symbol.isRelation())
      _symbols.push_back(env.signature->addPredicate(symbol.name, OperatorType::getPredicateType(domain))->number());
    else
      _symbols.push_back(env.signature->addFunction(symbol.name, OperatorType::getFunctionType(domain, _sorts[symbol.range]))->number());
  }

  std::vector<bool> inhabited(sorts.size(), false);
  for (unsigned i = 0; i < sorts.size(); i++) inhabited[i] = sorts[i].kind == LogicStatement::SortKind::PARTS;
  for (bool changed = true; changed;) {
    changed = false;
    for (const LogicStatement::Symbol& symbol : symbols) {
      if (symbol.isRelation() || inhabited[symbol.range]) continue;
      bool reached = true;
      for (unsigned sort : symbol.domain) reached = reached && inhabited[sort];
      if (reached) inhabited[symbol.range] = changed = true;
    }
    for (unsigned i = 0; i < sorts.size(); i++)
      if (sorts[i].kind == LogicStatement::SortKind::MAPS && !inhabited[i] && inhabited[sorts[i].target]) inhabited[i] = changed = true;
  }

  for (unsigned i = 0; i < sorts.size(); i++) {
    _mayBeEmpty.push_back(!inhabited[i]);
    _inhabited.push_back(inhabited[i] ? 0
      : env.signature->addPredicate("inhabited_" + sorts[i].name, OperatorType::getPredicateType(TermStack()))->number());
  }
}

/** The condition "the sort is not empty": the proposition inhabited_S. Only for a sort that may be empty. */
Formula* LogicTranslator::inhabitedFormula(unsigned sort) const
{
  return new AtomicFormula(Literal::create(_inhabited[sort], /* polarity */ true, {}));
}

TermList LogicTranslator::term(const LogicStatement::Term& term) const
{
  /* The number of a binder is the number of its Vampire variable: binders
   * are numbered once each, so the formula is rectified as it is built. */
  if (term.variable >= 0) return TermList::var((unsigned)term.variable);

  TermStack arguments;
  for (const LogicStatement::Term& argument : term.arguments) arguments.push(this->term(argument));
  return TermList(Term::create(_symbols[term.symbol], arguments.size(), arguments.begin()));
}

/**
 * Translates a condition. bound lists the sorts of the variables in scope:
 * a quantifier over one of them needs no guard, since there the sort has an
 * element.
 */
Formula* LogicTranslator::formula(const LogicStatement::Formula& formula, std::vector<unsigned>& bound) const
{
  switch (formula.connective) {
    case Connective::TRUE:
      return Formula::trueFormula();

    case Connective::EQUAL: {
      TermList left = term(formula.terms[0]), right = term(formula.terms[1]);
      return new AtomicFormula(Literal::createEquality(true, left, right, _sorts[formula.terms[0].sort]));
    }

    case Connective::HOLDS: {
      TermStack arguments;
      for (const LogicStatement::Term& argument : formula.terms) arguments.push(term(argument));
      return new AtomicFormula(Literal::create(_symbols[formula.symbol], arguments.size(), true, arguments.begin()));
    }

    case Connective::NOT:
      return new NegatedFormula(this->formula(formula.parts[0], bound));

    case Connective::AND:
    case Connective::OR: {
      /* The first part is translated first, so that the order of the
       * conditions in a proof is the one of the statement. */
      Formula* first = this->formula(formula.parts[0], bound);
      Formula* second = this->formula(formula.parts[1], bound);
      return new JunctionFormula(formula.connective == Connective::AND ? AND : OR,
                                 FormulaList::cons(first, FormulaList::singleton(second)));
    }

    case Connective::IMPLIES:
    case Connective::IFF: {
      Formula* first = this->formula(formula.parts[0], bound);
      Formula* second = this->formula(formula.parts[1], bound);
      return new BinaryFormula(formula.connective == Connective::IMPLIES ? IMP : IFF, first, second);
    }

    case Connective::FORALL:
    case Connective::EXISTS: {
      bool universal = formula.connective == Connective::FORALL;
      bool guarded = _mayBeEmpty[formula.sort];
      for (unsigned sort : bound) guarded = guarded && sort != formula.sort;

      bound.push_back(formula.sort);
      Formula* body = this->formula(formula.parts[0], bound);
      bound.pop_back();

      Formula* quantified = new QuantifiedFormula(universal ? FORALL : EXISTS,
                                                  VSList::singleton(VarSort(formula.variable, _sorts[formula.sort])), body);
      if (!guarded) return quantified;

      /* See the header: over a possibly empty sort "every" is true and
       * "there is" is false when the sort has no element. */
      Formula* inhabited = inhabitedFormula(formula.sort);
      if (universal) return new BinaryFormula(IMP, inhabited, quantified);
      return new JunctionFormula(AND, FormulaList::cons(inhabited, FormulaList::singleton(quantified)));
    }
  }
  ASSERTION_VIOLATION;
}

void LogicTranslator::addInput(Formula* formula, Role role, const std::string& name)
{
  Unit* unit;
  if (role == Role::CLAIM) {
    /* As the TPTP parser does for a conjecture: the claim is kept as the
     * parent, and what enters the search is its negation. */
    Unit* claim = new FormulaUnit(formula, FromInput(UnitInputType::CONJECTURE));
    Parse::TPTP::assignAxiomName(claim, name);
    unit = new FormulaUnit(new NegatedFormula(formula), FormulaClauseTransformation(InferenceRule::CONJECTURE_NEGATION, claim));
  } else {
    unit = new FormulaUnit(formula, FromInput(UnitInputType::AXIOM));
    Parse::TPTP::assignAxiomName(unit, name);
  }
  _inputs.push_back({unit, role, name});
}

/** Collects in parts the conjuncts of a condition, in the order they are written, without the trivial ones. */
static void conjuncts(const LogicStatement::Formula& formula, std::vector<const LogicStatement::Formula*>& parts)
{
  if (formula.connective == Connective::TRUE) return;
  if (formula.connective != Connective::AND) { parts.push_back(&formula); return; }
  conjuncts(formula.parts[0], parts);
  conjuncts(formula.parts[1], parts);
}

UnitList* LogicTranslator::translate()
{
  declare();

  /* The variables of the statement and of its laws are numbered by their
   * binders; the ones introduced here come after them. */
  _nextVariable = _statement.variables();
  std::vector<unsigned> bound;
  const LogicStatement::Formula& statement = _statement.formula();
  const std::vector<LogicStatement::Symbol>& symbols = _statement.symbols();

  /* The axioms on empty sorts: a total map into T from inhabited sorts
   * makes T inhabited. Only for a T that may be empty; then some argument
   * sort may be empty too, or T would be certainly inhabited. */
  for (unsigned i = 0; i < symbols.size(); i++) {
    const LogicStatement::Symbol& symbol = symbols[i];
    if (symbol.isRelation() || !_mayBeEmpty[symbol.range]) continue;

    /* A map with T itself among its arguments says "if T is inhabited then
     * T is inhabited": true, and no use to anybody. */
    bool intoItself = false;
    for (unsigned sort : symbol.domain) intoItself = intoItself || sort == (unsigned)symbol.range;
    if (intoItself) continue;
    FormulaList* arguments = FormulaList::empty();
    std::vector<bool> seen(_statement.sorts().size(), false);
    unsigned count = 0;
    for (unsigned sort : symbol.domain) {
      if (!_mayBeEmpty[sort] || seen[sort]) continue;
      seen[sort] = true;
      FormulaList::push(inhabitedFormula(sort), arguments);
      count++;
    }
    ASS(count > 0);
    Formula* premise = count == 1 ? arguments->head() : new JunctionFormula(AND, arguments);
    addInput(new BinaryFormula(IMP, premise, inhabitedFormula(symbol.range)), Role::INHABITED, "total_map_" + symbol.name);
  }

  /* What the sets of maps and the written numbers are (see the header). */
  const std::vector<LogicStatement::Sort>& sorts = _statement.sorts();
  for (unsigned i = 0; i < sorts.size(); i++) {
    if (sorts[i].kind == LogicStatement::SortKind::MAPS && _mayBeEmpty[i]) {
      /* The target may be empty here, or the set of maps would be certainly
       * inhabited: there is a map exactly when the base has no element or
       * the target has one. */
      Formula* target = inhabitedFormula(sorts[i].target);
      Formula* exists = !_mayBeEmpty[sorts[i].base] ? target
        : new JunctionFormula(OR, FormulaList::cons(new NegatedFormula(inhabitedFormula(sorts[i].base)), FormulaList::singleton(target)));
      addInput(new BinaryFormula(IFF, inhabitedFormula(i), exists), Role::STRUCTURE, "maps_exist_" + sorts[i].name);
    }
    if (sorts[i].kind != LogicStatement::SortKind::NUMBERS) continue;

    /* The written numbers: each different from the others, and no other element. */
    std::vector<TermList> numbers;
    for (unsigned s = 0; s < symbols.size(); s++)
      if (symbols[s].structure && !symbols[s].isRelation() && symbols[s].domain.empty() && symbols[s].range == (int)i)
        numbers.push_back(TermList(Term::createConstant(_symbols[s])));
    FormulaList* different = FormulaList::empty();
    FormulaList* one = FormulaList::empty();
    TermList x = TermList::var(_nextVariable++);
    for (size_t a = 0; a < numbers.size(); a++) {
      FormulaList::push(new AtomicFormula(Literal::createEquality(true, x, numbers[a], _sorts[i])), one);
      for (size_t b = a + 1; b < numbers.size(); b++)
        FormulaList::push(new AtomicFormula(Literal::createEquality(false, numbers[a], numbers[b], _sorts[i])), different);
    }
    if (numbers.size() > 2) addInput(new JunctionFormula(AND, different), Role::STRUCTURE, "numbers_distinct_" + sorts[i].name);
    else if (numbers.size() == 2) addInput(different->head(), Role::STRUCTURE, "numbers_distinct_" + sorts[i].name);
    Formula* some = numbers.size() == 1 ? one->head() : new JunctionFormula(OR, one);
    addInput(new QuantifiedFormula(FORALL, VSList::singleton(VarSort(x.var(), _sorts[i])), some), Role::STRUCTURE, "numbers_all_" + sorts[i].name);
  }

  /* The laws of the sets of parts and of maps, as the engine gives them. */
  for (unsigned i = 0; i < _statement.laws().size(); i++)
    addInput(formula(_statement.laws()[i], bound), Role::LAW, "law_" + std::to_string(i + 1));

  if (_statement.wantsExample()) {
    addInput(formula(statement, bound), Role::STATEMENT, "statement");
  } else if (statement.connective == Connective::IMPLIES) {
    std::vector<const LogicStatement::Formula*> hypotheses;
    conjuncts(statement.parts[0], hypotheses);
    for (unsigned i = 0; i < hypotheses.size(); i++)
      addInput(formula(*hypotheses[i], bound), Role::HYPOTHESIS, "hypothesis_" + std::to_string(i + 1));
    addInput(formula(statement.parts[1], bound), Role::CLAIM, "claim");
  } else {
    addInput(formula(statement, bound), Role::CLAIM, "claim");
  }

  UnitList::FIFO units;
  for (const Input& input : _inputs) units.pushBack(input.unit);
  return units.list();
}

} // namespace Math
