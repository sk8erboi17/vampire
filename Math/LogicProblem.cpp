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

#include <cstdio>
#include <fstream>

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
 * A text file. First line: kind, goalUsed, proposed. Then the account, as a
 * line with its length in bytes followed by that many bytes and a newline
 * (the length makes any LaTeX safe to carry). Then the model: a line with
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
   * (LogicTranslator.hpp). There is nothing to pass on. */
  if (!_statement.plainOnly()) return;

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
