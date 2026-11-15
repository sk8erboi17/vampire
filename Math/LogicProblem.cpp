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
 * @file LogicProblem.cpp
 * Implements LogicProblem: what Vampire found, read out of Vampire's own
 * structures and written down for the process that asked.
 */

#include "LogicProblem.hpp"

#include <cctype>
#include <cstdio>
#include <fstream>
#include <set>
#include <sstream>

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/OperatorType.hpp"
#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Set.hpp"
#include "FMB/FiniteModelMultiSorted.hpp" // not self-contained: needs the five headers above
#include "Humanizer/ProofNarrator.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Exception.hpp"
#include "Lib/SharedSet.hpp"
#include "Lib/Stack.hpp"

namespace Math {

using namespace Kernel;

std::unique_ptr<LogicProblem> LogicProblem::_current;

/* A model with more cells than this is not passed on: the engine and the
 * checker would refuse to recompute it anyway (their budgets are far
 * smaller), and nobody could read it. The answer is then "saturated". */
static constexpr unsigned long long MAX_MODEL_CELLS = 1ull << 20;

/* ------------------------------------------------------------------------
 * The answer, from the process that found it to the one that asked
 * ------------------------------------------------------------------------
 *
 * A text file. First line: kind, goalUsed, proposed. Then the account and
 * the inferences, each as a line with its length in bytes followed by that
 * many bytes and a newline (the length makes any text safe to carry). Then
 * the model: a line with
 * the number of sorts and their sizes, a line with the number of symbols,
 * and for each symbol a line with the number of cells and their values.
 */

void VampireAnswer::write(const std::string& path) const
{
  std::string temporary = path + ".part";
  {
    std::ofstream out(temporary, std::ios::binary);
    out << static_cast<int>(kind) << " " << (goalUsed ? 1 : 0) << " " << (proposed ? 1 : 0) << "\n";
    out << account.size() << "\n" << account << "\n";
    out << inferences.size() << "\n" << inferences << "\n";
    out << sizes.size();
    for (size_t size : sizes) out << " " << size;
    out << "\n" << tables.size() << "\n";
    for (const std::vector<size_t>& table : tables) {
      out << table.size();
      for (size_t value : table) out << " " << value;
      out << "\n";
    }
    if (!out) return;
  }

  /* The name appears only when the file is complete: a reader never sees half an answer. */
  std::rename(temporary.c_str(), path.c_str());
}

bool VampireAnswer::read(const std::string& path, VampireAnswer& answer)
{
  std::ifstream in(path, std::ios::binary);
  int kind, goalUsed, proposed;
  size_t length, count;
  if (!(in >> kind >> goalUsed >> proposed >> length) || kind < 0 || kind > static_cast<int>(Kind::SATURATED)) return false;
  in.get();

  VampireAnswer read;
  read.kind = static_cast<Kind>(kind);
  read.goalUsed = goalUsed != 0;
  read.proposed = proposed != 0;
  read.account.resize(length);
  if (length && !in.read(&read.account[0], (std::streamsize)length)) return false;
  if (!(in >> length)) return false;
  in.get();
  read.inferences.resize(length);
  if (length && !in.read(&read.inferences[0], (std::streamsize)length)) return false;

  if (!(in >> count)) return false;
  read.sizes.resize(count);
  for (size_t& size : read.sizes) if (!(in >> size)) return false;
  if (!(in >> count)) return false;
  read.tables.resize(count);
  for (std::vector<size_t>& table : read.tables) {
    if (!(in >> count)) return false;
    table.resize(count);
    for (size_t& value : table) if (!(in >> value)) return false;
  }
  answer = std::move(read);
  return true;
}

/* ------------------------------------------------------------------------
 * The statement of this process
 * ------------------------------------------------------------------------ */

LogicProblem::LogicProblem(LogicStatement statement, const Settings& settings)
  : _statement(std::move(statement)), _translator(new LogicTranslator(_statement)), _settings(settings) {}

UnitList* LogicProblem::install(LogicStatement statement, const Settings& settings)
{
  _current.reset(new LogicProblem(std::move(statement), settings));
  return _current->_translator->translate();
}

/* ------------------------------------------------------------------------
 * The checker's clauses as the problem
 * ------------------------------------------------------------------------
 *
 * The clauses are over one domain: the checker's translation puts all the
 * sets of a statement into it, with a predicate per set for "is an element
 * of it". So every symbol is over Vampire's default sort, and its name is
 * its number in the checker's translation (f12, p7), which is all that the
 * way back needs.
 */

/** A term of the checker's clauses as a term of Vampire. */
static TermList clauseTerm(const Proof::Replay& clauses, int term, const std::vector<unsigned>& functions)
{
  if (Proof::Replay::isVariable(term)) return TermList::var((unsigned)Proof::Replay::variableOf(term));
  TermStack arguments;
  for (int argument : clauses.argumentsOf(term)) arguments.push(clauseTerm(clauses, argument, functions));
  return TermList(Term::create(functions[clauses.symbolOf(term)], arguments.size(), arguments.begin()));
}

UnitList* LogicProblem::installClauses(const Proof::Replay& clauses, const Settings& settings)
{
  _current.reset(new LogicProblem(LogicStatement(), settings));
  LogicProblem& problem = *_current;
  problem._translator.reset();

  TermList individual = AtomicSort::defaultSort();
  std::vector<unsigned> symbols;
  for (unsigned i = 0; i < clauses.symbols().size(); i++) {
    const Proof::Replay::Symbol& symbol = clauses.symbols()[i];
    if (symbol.predicate) {
      symbols.push_back(env.signature->addPredicate("p" + std::to_string(i), OperatorType::getPredicateTypeUniformRange(symbol.arity, individual))->number());
      problem._predicateSymbol[symbols.back()] = (int)i;
    } else {
      symbols.push_back(env.signature->addFunction("f" + std::to_string(i), OperatorType::getFunctionTypeUniformRange(symbol.arity, individual, individual))->number());
      problem._functionSymbol[symbols.back()] = (int)i;
    }
  }

  UnitList::FIFO units;
  for (int index = 0; index < clauses.initialClauses(); index++) {
    Stack<Literal*> literals;
    bool holds = false;  // a literal "true" makes the clause say nothing
    for (const Proof::Replay::Literal& literal : clauses.clause(index).literals) {
      if (!literal.left) { holds = holds || !literal.negative; continue; }
      if (literal.right) {
        literals.push(Literal::createEquality(!literal.negative, clauseTerm(clauses, literal.left, symbols),
                                              clauseTerm(clauses, literal.right, symbols), individual));
      } else {
        TermStack arguments;
        for (int argument : clauses.argumentsOf(literal.left)) arguments.push(clauseTerm(clauses, argument, symbols));
        literals.push(Literal::create(symbols[clauses.symbolOf(literal.left)], arguments.size(), !literal.negative, arguments.begin()));
      }
    }
    if (holds) continue;
    Clause* clause = Clause::fromStack(literals, FromInput(UnitInputType::AXIOM));
    problem._inputClause[clause->number()] = index;
    units.pushBack(clause);
  }
  return units.list();
}

/** A term of Vampire as the checker writes terms; empty if it uses a symbol that is not one of the checker's. */
static std::string checkerTerm(TermList term, const std::map<unsigned, int>& functions)
{
  if (term.isVar()) return term.isSpecialVar() ? "" : "(v " + std::to_string(term.var()) + ")";
  auto symbol = functions.find(term.term()->functor());
  if (symbol == functions.end()) return "";
  std::string text = "(f " + std::to_string(symbol->second);
  for (unsigned i = 0; i < term.term()->arity(); i++) {
    std::string argument = checkerTerm(*term.term()->nthArgument(i), functions);
    if (argument.empty()) return "";
    text += " " + argument;
  }
  return text + ")";
}

/**
 * The names in a propositional clause of AVATAR, as Vampire writes it: a
 * disjunction of named formulas, "7" or "~7" (with a prefix before the
 * number when the proof is printed for TPTP). Appends v for the SAT
 * variable v and -v for its negation. Returns false if the formula is not
 * such a clause.
 */
static bool namesOf(Formula* formula, std::vector<int>& names)
{
  if (formula->connective() == OR) {
    FormulaList::Iterator parts(formula->args());
    while (parts.hasNext()) if (!namesOf(parts.next(), names)) return false;
    return true;
  }
  if (formula->connective() != NAME) return false;
  std::string name = static_cast<NamedFormula*>(formula)->name();
  size_t digits = name.size();
  while (digits > 0 && std::isdigit((unsigned char)name[digits - 1])) digits--;
  if (digits == name.size() || name.size() - digits > 9) return false;
  int variable = std::stoi(name.substr(digits));
  names.push_back(!name.empty() && name[0] == '~' ? -variable : variable);
  return true;
}

/**
 * The refutation as lines, one per unit, in the order of derivation (see
 * VampireAnswer::inferences). A unit that is not a clause over the
 * checker's symbols, nor one of the units of AVATAR below, is written as
 * "unit N unknown": whoever rebuilds the refutation stops there.
 *
 * AVATAR (Saturation/Splitter.cpp) leaves five kinds of units in a proof:
 *   the definition of a name, a formula "7 <=> ![X]: (clause)";
 *   the component clause, the named clause under the assumption of its name;
 *   the clause of names got by splitting a clause, a formula over names;
 *   the clause of names read off an empty clause under assumptions;
 *   the empty clause, from the clauses of names the SAT solver found
 *   unsatisfiable.
 * And every clause may hold under assumptions, its split levels: level
 * 2(v-1) is "the SAT variable v is true", 2(v-1)+1 "it is false"
 * (Splitter::getNameFromLiteralUnsafe()).
 */
std::string LogicProblem::inferencesOf(Unit* refutation) const
{
  auto byNumber = [](Unit* left, Unit* right) { return left->number() < right->number(); };
  std::set<Unit*, decltype(byNumber)> units(byNumber);
  std::vector<Unit*> pending = {refutation};
  while (!pending.empty()) {
    Unit* unit = pending.back();
    pending.pop_back();
    if (!units.insert(unit).second) continue;
    UnitIterator parents = unit->getParents();
    while (parents.hasNext()) pending.push_back(parents.next());
  }

  /* A literal in the checker's notation, or "" if it is not over the checker's symbols. */
  auto checkerLiteral = [&](Literal* literal) -> std::string {
    if (literal->isEquality()) {
      std::string left = checkerTerm(*literal->nthArgument(0), _functionSymbol);
      std::string right = checkerTerm(*literal->nthArgument(1), _functionSymbol);
      if (left.empty() || right.empty()) return "";
      return std::string(literal->polarity() ? " (eq " : " (ne ") + left + " " + right + ")";
    }
    auto symbol = _predicateSymbol.find(literal->functor());
    if (symbol == _predicateSymbol.end()) return "";
    std::string atom = "(f " + std::to_string(symbol->second);
    for (unsigned a = 0; a < literal->arity(); a++) {
      std::string argument = checkerTerm(*literal->nthArgument(a), _functionSymbol);
      if (argument.empty()) return "";
      atom += " " + argument;
    }
    return std::string(literal->polarity() ? " (pos " : " (neg ") + atom + "))";
  };

  std::ostringstream out;
  for (Unit* unit : units) {
    auto input = _inputClause.find(unit->number());
    if (input != _inputClause.end()) { out << "input " << unit->number() << " " << input->second << "\n"; continue; }

    InferenceRule rule = unit->inference().rule();
    std::vector<unsigned> premises;
    Unit* clausePremise = nullptr;  // for a clause of names: the clause it was read off
    UnitIterator parents = unit->getParents();
    while (parents.hasNext()) {
      Unit* parent = parents.next();
      premises.push_back(parent->number());
      if (parent->isClause()) clausePremise = parent;
    }
    auto unknown = [&]() { out << "unit " << unit->number() << " unknown " << ruleName(rule) << "\n"; };

    if (!unit->isClause()) {
      Formula* formula = static_cast<FormulaUnit*>(unit)->formula();
      std::vector<int> names;
      if (rule == InferenceRule::AVATAR_DEFINITION && formula->connective() == IFF && namesOf(formula->left(), names) && names[0] > 0) {
        /* The named clause: a literal, or a disjunction of literals, under its quantifiers. */
        Formula* body = formula->right();
        while (body->connective() == FORALL) body = body->qarg();
        std::vector<Formula*> parts = {body};
        std::string clause;
        bool known = true;
        while (!parts.empty() && known) {
          Formula* part = parts.back();
          parts.pop_back();
          if (part->connective() == OR) {
            FormulaList::Iterator disjuncts(part->args());
            while (disjuncts.hasNext()) parts.push_back(disjuncts.next());
          } else {
            std::string literal = part->connective() == LITERAL ? checkerLiteral(part->literal()) : "";
            known = !literal.empty();
            clause += literal;
          }
        }
        if (!known) { unknown(); continue; }
        out << "definition " << unit->number() << " " << names[0] << " (clause" << clause << ")\n";
      } else if ((rule == InferenceRule::AVATAR_SPLIT_CLAUSE || rule == InferenceRule::AVATAR_CONTRADICTION_CLAUSE)
                 && clausePremise && namesOf(formula, names)) {
        out << (rule == InferenceRule::AVATAR_SPLIT_CLAUSE ? "split " : "contradiction ") << unit->number() << " "
            << clausePremise->number() << " " << names.size();
        for (int name : names) out << " " << name;
        out << "\n";
      } else {
        unknown();
      }
      continue;
    }

    Clause* clause = unit->asClause();
    std::vector<unsigned> levels;
    if (clause->splits()) {
      auto assumed = clause->splits()->iter();
      while (assumed.hasNext()) levels.push_back(assumed.next());
    }
    if (rule == InferenceRule::AVATAR_COMPONENT && levels.size() == 1) {
      out << "component " << unit->number() << " " << levels[0] << "\n";
      continue;
    }
    if (rule == InferenceRule::AVATAR_REFUTATION && clause->isEmpty() && levels.empty()) {
      out << "propositional " << unit->number() << " " << premises.size();
      for (unsigned premise : premises) out << " " << premise;
      out << "\n";
      continue;
    }

    std::string written = "(clause";
    bool known = true;
    for (unsigned i = 0; known && i < clause->length(); i++) {
      std::string literal = checkerLiteral((*clause)[i]);
      known = !literal.empty();
      written += literal;
    }
    if (!known) { unknown(); continue; }
    out << "unit " << unit->number() << " " << premises.size();
    for (unsigned premise : premises) out << " " << premise;
    out << " " << ruleName(rule) << " " << levels.size();
    for (unsigned level : levels) out << " " << level;
    out << " " << written << ")\n";
  }
  return out.str();
}

void LogicProblem::send() const
{
  if (!_settings.answerPath.empty()) _answer.write(_settings.answerPath);
}

/* ------------------------------------------------------------------------
 * A finite model, as the sizes and tables of the statement
 * ------------------------------------------------------------------------
 *
 * Vampire's model is for the translated problem: every sort has at least
 * one element, and the propositions inhabited_S say which sorts stand for
 * an empty set (LogicTranslator.hpp). The statement as it was read has
 * possibly empty sets: a set whose proposition is false has 0 elements, and
 * a symbol with such a set among its arguments has an empty table.
 *
 * Nothing is decided here. Whoever reads the answer loads these tables into
 * the engine's structure for models, where the statement is recomputed in
 * them; if the translation or this reading were wrong, the statement would
 * not come out false there (or true, for an example), and the model would
 * not be accepted.
 */

void LogicProblem::onFiniteModel(FMB::FiniteModelMultiSorted& model)
{
  /* With a set of parts or of maps a model of the translation is not a
   * model of the statement: it may lack parts or maps that really exist
   * (LogicTranslator.hpp). There is nothing to pass on. The same when the
   * problem is the checker's clauses: only their refutation is of use. */
  if (!_translator || !_statement.plainOnly()) return;

  const std::vector<LogicStatement::Sort>& sorts = _statement.sorts();
  const std::vector<LogicStatement::Symbol>& symbols = _statement.symbols();

  /* A symbol that occurs in no clause the model builder saw (preprocessing
   * removed it, or the statement declares it and never uses it) has no value
   * in Vampire's model: no clause depends on it, so the model is one whatever
   * value it gets. Vampire's own convention for such symbols, when it
   * evaluates formulas in a model, is that a relation is false and a map
   * sends everything to the first element; the same is done here. Without
   * this a declared and unused map made the table malformed, and a model
   * that was right was refused (f in "f: S -> T and |S| >= 2 implies
   * |T| >= 2"). If the convention gave something that is not a model, the
   * engine would say so: it recomputes the statement. */
  auto holds = [&](Literal* literal) {
    try {
      return model.evaluateGroundLiteral(literal);
    } catch (Lib::UserErrorException&) {
      return false;
    }
  };
  auto valueOf = [&](Term* term) {
    unsigned element = model.evaluateGroundTerm(term);  // from 1; 0 if the symbol has no value
    return element ? element - 1 : 0;
  };

  VampireAnswer answer;
  answer.kind = VampireAnswer::Kind::MODEL;
  try {
    /* The sizes: Vampire's, or 0 where the model says the set is empty. */
    for (unsigned i = 0; i < sorts.size(); i++) {
      size_t size = model.sortSize(_translator->sort(i));
      if (_translator->mayBeEmpty(i) && !holds(Literal::create(_translator->inhabited(i), /* polarity */ true, {})))
        size = 0;
      answer.sizes.push_back(size);
    }

    /* The tables, cell by cell: each is the value Vampire's model gives to
     * the symbol applied to elements of the model. */
    answer.tables.resize(symbols.size());
    unsigned long long total = 0;
    for (unsigned s = 0; s < symbols.size(); s++) {
      const LogicStatement::Symbol& symbol = symbols[s];
      unsigned long long cells = 1;
      for (unsigned sort : symbol.domain) {
        cells *= answer.sizes[sort];
        if (cells > MAX_MODEL_CELLS) break;
      }
      total += cells;
      if (cells > MAX_MODEL_CELLS || total > MAX_MODEL_CELLS) return;

      std::vector<size_t> index(symbol.domain.size(), 0);
      for (unsigned long long cell = 0; cell < cells; cell++) {
        TermStack arguments;
        for (size_t k = 0; k < symbol.domain.size(); k++)
          arguments.push(TermList(model.getDomainConstant((unsigned)index[k] + 1, _translator->sort(symbol.domain[k]))));

        if (symbol.isRelation()) {
          Literal* literal = Literal::create(_translator->symbol(s), arguments.size(), true, arguments.begin());
          answer.tables[s].push_back(holds(literal) ? 1 : 0);
        } else {
          Term* term = Term::create(_translator->symbol(s), arguments.size(), arguments.begin());
          answer.tables[s].push_back(valueOf(term));
        }

        /* The next choice of the arguments: the first changes fastest. */
        for (size_t k = 0; k < index.size(); k++) {
          if (++index[k] < answer.sizes[symbol.domain[k]]) break;
          index[k] = 0;
        }
      }
    }
  } catch (Lib::Exception&) {
    /* The model could not be read back: there is none to pass on. */
    return;
  }
  _answer = std::move(answer);
}

/**
 * No clause is left after preprocessing.
 *
 * Preprocessing removes clauses in ways that keep satisfiability: a relation
 * that occurs with one sign only is made true or false everywhere, a
 * definition that nobody uses is dropped. When nothing is left, every
 * interpretation of what remains is a model, and the removed symbols get
 * their values back from the record Vampire keeps of each removal (the
 * "interferences" of the problem), which is how the finite model builder
 * completes its own models. So a model exists; Vampire just does not build
 * one, because there was nothing to search.
 *
 * Here the smallest candidate is built, one element in every sort, completed
 * with those records, and passed on like any other model, marked as
 * proposed. It is a candidate and nothing more: if the engine does not
 * confirm it, nothing is wrong with Vampire's answer, there is only no
 * confirmed model at hand.
 */
void LogicProblem::onNoClauses()
{
  if (!_translator) return;
  try {
    Lib::DArray<unsigned> sizes(env.signature->typeCons());
    for (unsigned sort = 0; sort < env.signature->typeCons(); sort++)
      sizes[sort] = env.signature->isInterpretedNonDefault(sort) && !env.signature->isBoolCon(sort) ? 0 : 1;
    FMB::FiniteModelMultiSorted model(std::move(sizes));

    /* The symbols that were not removed are free, with no clause to
     * satisfy: they are read with the convention of onFiniteModel(). The
     * removed ones are computed from them, in the order Vampire recorded. */
    model.restoreEliminatedDefinitions(env.getMainProblem());
    onFiniteModel(model);
    _answer.proposed = true;
  } catch (Lib::Exception&) {
    _answer = VampireAnswer();
  }
}

/* ------------------------------------------------------------------------
 * The answers
 * ------------------------------------------------------------------------ */

void LogicProblem::onRefutation(Unit* refutation)
{
  bool italian = _settings.language == Language::ITALIAN;
  _answer = VampireAnswer();
  _answer.kind = VampireAnswer::Kind::REFUTATION;
  _answer.goalUsed = refutation->derivedFromGoal();

  /* The checker's clauses: what is wanted is the refutation itself, to be rechecked. */
  if (!_translator) {
    _answer.inferences = inferencesOf(refutation);
    send();
    return;
  }

  if (_settings.explain) {
    Humanizer::ProofNarrator narrator(_settings.language);
    unsigned hypothesis = 0;
    bool guards = false;
    for (const LogicTranslator::Input& input : _translator->inputs()) {
      switch (input.role) {
        case LogicTranslator::Role::HYPOTHESIS:
          narrator.label(input.unit, (italian ? "Ipotesi " : "Hypothesis ") + std::to_string(++hypothesis));
          break;
        case LogicTranslator::Role::CLAIM: {
          /* What entered the search is the negation; the claim itself is its parent. */
          UnitIterator parents = input.unit->getParents();
          if (parents.hasNext()) narrator.label(parents.next(), italian ? "La tesi" : "The claim");
          break;
        }
        case LogicTranslator::Role::STATEMENT:
          narrator.label(input.unit, italian ? "L'enunciato" : "The statement");
          break;
        case LogicTranslator::Role::INHABITED:
          narrator.label(input.unit, italian ? "Un'applicazione definita su insiemi con elementi arriva in un insieme con elementi"
                                             : "A map defined on sets with elements lands in a set with elements");
          break;
        case LogicTranslator::Role::LAW:
          narrator.label(input.unit, italian ? "Una legge degli insiemi di parti e di applicazioni: vale qualunque siano gli insiemi"
                                             : "A law of the sets of parts and of maps: it holds whatever the sets are");
          break;
        case LogicTranslator::Role::STRUCTURE:
          narrator.label(input.unit, italian ? "Per ci\\`o che l'insieme \\`e: i suoi elementi sono fissati dall'enunciato"
                                             : "By what the set is: its elements are fixed by the statement");
          break;
      }
    }
    for (unsigned i = 0; i < _statement.sorts().size(); i++) guards = guards || _translator->mayBeEmpty(i);
    if (guards)
      _answer.account = italian
        ? "Gli insiemi possono essere vuoti: $\\mathrm{inhabited}_{S}$ \\`e la condizione ``$S$ ha un elemento'', e accompagna i quantificatori su $S$. "
        : "The sets may be empty: $\\mathrm{inhabited}_{S}$ is the condition ``$S$ has an element'', and it goes with the quantifiers over $S$. ";
    _answer.account += narrator.narrate(refutation);
  }
  send();
}

void LogicProblem::onSatisfiable()
{
  /* With a model, read by onFiniteModel(), the answer is the model;
   * without one all there is to say is that the search saturated. */
  if (_answer.kind != VampireAnswer::Kind::MODEL) {
    _answer = VampireAnswer();
    _answer.kind = VampireAnswer::Kind::SATURATED;
  }
  send();
}

} // namespace Math
