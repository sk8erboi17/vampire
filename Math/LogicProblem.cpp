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
 * Implements LogicProblem: the verification of a finite model found by
 * Vampire and the report of an answer with its verification status.
 */

#include "LogicProblem.hpp"

#include <cctype>
#include <cstdio>
#include <fstream>
#include <sstream>

#include "Kernel/Problem.hpp"
#include "Kernel/Signature.hpp"
#include "Lib/DArray.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Set.hpp"
#include "FMB/FiniteModelMultiSorted.hpp" // not self-contained: needs the five headers above
#include "Humanizer/ProofNarrator.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Stack.hpp"
#include "Shell/UIHelper.hpp"

#include "Names.hpp"
#include "Proof/IndependentChecker.h"

namespace Math {

using namespace Kernel;

std::unique_ptr<LogicProblem> LogicProblem::_current;

/* A model with more cells than this is not rewritten as a certificate: the
 * checker would refuse to recompute it anyway (its budget is far smaller),
 * and the text would be of no use to a reader. It stays unconfirmed. */
static constexpr unsigned long long MAX_MODEL_CELLS = 1ull << 20;

/* ------------------------------------------------------------------------
 * The result, from the process that found it to the one that asked
 * ------------------------------------------------------------------------
 *
 * A text file: a first line "decided status byRefutation", then four fields, each a line
 * with its length in bytes followed by that many bytes and a newline. The
 * lengths make any text safe to carry, LaTeX and certificates included.
 */

void LogicResult::write(const std::string& path) const
{
  std::string temporary = path + ".part";
  {
    std::ofstream out(temporary, std::ios::binary);
    out << (decided ? 1 : 0) << " " << static_cast<int>(status) << " " << (byRefutation ? 1 : 0) << "\n";
    for (const std::string* field : {&reason, &detail, &proof, &certificate})
      out << field->size() << "\n" << *field << "\n";
    if (!out) return;
  }

  /* The name appears only when the file is complete: a reader never sees half a result. */
  std::rename(temporary.c_str(), path.c_str());
}

bool LogicResult::read(const std::string& path, LogicResult& result)
{
  std::ifstream in(path, std::ios::binary);
  int decided, status, byRefutation;
  if (!(in >> decided >> status >> byRefutation) || status < 0 || status > static_cast<int>(Status::UNSUPPORTED)) return false;
  in.get();

  LogicResult read;
  read.decided = decided != 0;
  read.byRefutation = byRefutation != 0;
  read.status = static_cast<Status>(status);
  for (std::string* field : {&read.reason, &read.detail, &read.proof, &read.certificate}) {
    size_t length;
    if (!(in >> length)) return false;
    in.get();
    field->resize(length);
    if (length && !in.read(&(*field)[0], (std::streamsize)length)) return false;
    in.get();
  }
  result = std::move(read);
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
 * A finite model, to the independent checker
 * ------------------------------------------------------------------------
 *
 * Vampire's model is for the translated problem: every sort has at least
 * one element, and the propositions inhabited_S say which sorts stand for
 * an empty set (LogicTranslator.hpp). The certificate speaks of the
 * statement as it was read: a set whose proposition is false has 0
 * elements, and a symbol with such a set among its arguments has an empty
 * table. Each symbol's table lists its value for every choice of the
 * arguments, the first argument changing fastest, an element being its
 * number from 0 in its set and a truth value being 1 or 0: the format of
 * the checker ("certificate counterexample", "certificate example").
 *
 * The checker does not trust any of this: it evaluates the statement in the
 * tables with its own evaluator. If the translation or this rewriting were
 * wrong, the statement would not come out false (or true, for an example),
 * and the certificate would be rejected.
 */

/**
 * The name of the element number index of a set: the lower-case letter of
 * the set with the number as a subscript, s_0, s_1, ... for S, and
 * s_{2,0}, s_{2,1}, ... for S_2. So the elements of two sets are not confused.
 */
static std::string elementName(const std::string& sort, unsigned index)
{
  bool letterAndDigits = !sort.empty() && std::isalpha((unsigned char)sort[0]);
  for (size_t i = 1; i < sort.size() && letterAndDigits; i++) letterAndDigits = std::isdigit((unsigned char)sort[i]);
  if (!letterAndDigits) return "(" + latexName(sort).latex + ")_{" + std::to_string(index) + "}";
  std::string letter(1, (char)std::tolower((unsigned char)sort[0]));
  if (sort.size() == 1) return letter + "_{" + std::to_string(index) + "}";
  return letter + "_{" + sort.substr(1) + "," + std::to_string(index) + "}";
}

/**
 * The model for a reader: the sets, then every symbol with its table.
 *
 * It is written as the engine writes the models it finds itself (put_model()
 * in Math/quaerens/main.c), so that a counterexample reads the same whoever
 * found it: a relation as the set of the elements or pairs for which it
 * holds, a map by its values, an operation between its arguments, a map
 * from an empty set as the empty set.
 */
std::string LogicProblem::describeModel(const std::vector<unsigned>& sizes, const std::vector<std::vector<unsigned>>& tables) const
{
  const std::vector<LogicStatement::Sort>& sorts = _statement.sorts();
  const std::vector<LogicStatement::Symbol>& symbols = _statement.symbols();
  std::ostringstream out;

  for (unsigned i = 0; i < sorts.size(); i++) {
    out << (i ? ", $" : "$") << latexName(sorts[i].name).latex << " = \\{";
    for (unsigned e = 0; e < sizes[i]; e++) out << (e ? ", " : "") << elementName(sorts[i].name, e);
    out << "\\}$";
  }

  for (unsigned s = 0; s < symbols.size(); s++) {
    const LogicStatement::Symbol& symbol = symbols[s];
    const std::vector<unsigned>& table = tables[s];
    LatexName name = latexName(symbol.name);
    size_t arity = symbol.domain.size();
    out << "; $";

    /* A map from an empty set is the empty graph: it is shown all the same. */
    if (table.empty() && !symbol.isRelation()) { out << name.latex << " = \\emptyset$"; continue; }
    if (symbol.isRelation()) out << name.latex << " = \\{";

    unsigned written = 0;
    for (size_t cell = 0; cell < table.size(); cell++) {
      if (symbol.isRelation() && !table[cell]) continue;
      if (written++) out << ", ";

      /* The arguments of this cell, the first changing fastest. */
      std::vector<std::string> arguments;
      size_t rest = cell;
      for (size_t k = 0; k < arity; k++) {
        unsigned size = sizes[symbol.domain[k]];
        arguments.push_back(elementName(sorts[symbol.domain[k]].name, (unsigned)(rest % size)));
        rest /= size;
      }

      bool infix = name.infix && arity == 2 && !symbol.isRelation();
      bool parentheses = arity >= 2 || (arity == 1 && !symbol.isRelation());
      if (infix) {
        out << arguments[0] << " " << name.latex << " " << arguments[1];
      } else {
        if (!symbol.isRelation()) out << name.latex;
        if (parentheses) out << "(";
        for (size_t k = 0; k < arity; k++) out << (k ? ", " : "") << arguments[k];
        if (parentheses) out << ")";
      }
      if (!symbol.isRelation()) out << " = " << elementName(sorts[symbol.range].name, table[cell]);
    }
    if (symbol.isRelation()) out << (written ? "\\}" : "\\} = \\emptyset");
    out << "$";
  }
  return out.str();
}

void LogicProblem::onFiniteModel(FMB::FiniteModelMultiSorted& model)
{
  const std::vector<LogicStatement::Sort>& sorts = _statement.sorts();
  const std::vector<LogicStatement::Symbol>& symbols = _statement.symbols();
  bool italian = _settings.language == Language::ITALIAN;
  _hasModel = true;
  _modelCertificate.clear();

  /* A symbol that occurs in no clause the model builder saw (preprocessing
   * removed it, or the statement declares it and never uses it) has no value
   * in Vampire's model: no clause depends on it, so the model is one whatever
   * value it gets. Vampire's own convention for such symbols, when it
   * evaluates formulas in a model, is that a relation is false and a map
   * sends everything to the first element; the same is done here. Without
   * this a declared and unused map made the table malformed, and the
   * checker rejected a model that was right (f in "f: S -> T and |S| >= 2
   * implies |T| >= 2"). If the convention gave something that is not a
   * model the checker would say so: it recomputes the statement. */
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

  try {
    /* The sizes: Vampire's, or 0 where the model says the set is empty. */
    std::vector<unsigned> sizes;
    for (unsigned i = 0; i < sorts.size(); i++) {
      unsigned size = model.sortSize(_translator->sort(i));
      if (_translator->mayBeEmpty(i) && !holds(Literal::create(_translator->inhabited(i), /* polarity */ true, {})))
        size = 0;
      sizes.push_back(size);
    }

    /* The tables, cell by cell: each is the value Vampire's model gives to
     * the symbol applied to elements of the model. */
    std::vector<std::vector<unsigned>> tables(symbols.size());
    unsigned long long total = 0;
    for (unsigned s = 0; s < symbols.size(); s++) {
      const LogicStatement::Symbol& symbol = symbols[s];
      unsigned long long cells = 1;
      for (unsigned sort : symbol.domain) {
        cells *= sizes[sort];
        if (cells > MAX_MODEL_CELLS) break;
      }
      total += cells;
      if (cells > MAX_MODEL_CELLS || total > MAX_MODEL_CELLS) {
        _modelProblem = italian ? "il modello è troppo grande per essere riscritto come certificato"
                                : "the model is too large to be rewritten as a certificate";
        return;
      }

      std::vector<unsigned> index(symbol.domain.size(), 0);
      for (unsigned long long cell = 0; cell < cells; cell++) {
        TermStack arguments;
        for (size_t k = 0; k < symbol.domain.size(); k++)
          arguments.push(TermList(model.getDomainConstant(index[k] + 1, _translator->sort(symbol.domain[k]))));

        if (symbol.isRelation()) {
          Literal* literal = Literal::create(_translator->symbol(s), arguments.size(), true, arguments.begin());
          tables[s].push_back(holds(literal) ? 1 : 0);
        } else {
          Term* term = Term::create(_translator->symbol(s), arguments.size(), arguments.begin());
          tables[s].push_back(valueOf(term));
        }

        /* The next choice of the arguments: the first changes fastest. */
        for (size_t k = 0; k < index.size(); k++) {
          if (++index[k] < sizes[symbol.domain[k]]) break;
          index[k] = 0;
        }
      }
    }

    std::ostringstream certificate;
    certificate << _statement.certificateHead(_statement.wantsExample() ? "example" : "counterexample", &sizes);
    for (unsigned s = 0; s < symbols.size(); s++) {
      certificate << "table " << symbols[s].name;
      for (unsigned value : tables[s]) certificate << " " << value;
      certificate << "\n";
    }
    certificate << "end\n";

    /* The judge. Only an accepted certificate makes the model a counterexample. */
    const char* why = "";
    std::string text = certificate.str();
    ProofCheck answer = proof_check_certificate(text.c_str(), &why);
    if (answer == PROOF_CHECK_ACCEPTED) {
      _modelCertificate = text;
      _modelText = describeModel(sizes, tables);
    } else {
      _modelProblem = std::string(answer == PROOF_CHECK_REJECTED ? (italian ? "respinto: " : "rejected: ")
                                                              : (italian ? "non controllabile: " : "cannot be checked: ")) + why;
    }
  } catch (Lib::Exception&) {
    _modelProblem = italian ? "il modello di Vampire non si è potuto rileggere" : "Vampire's model could not be read back";
  }
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
 * with those records, and handed to the checker like any other model. It is
 * a candidate and nothing more: the checker recomputes the statement in it.
 * If it does not accept, this is not a sign that anything is wrong with
 * Vampire's answer, only that no confirmed model is at hand, and the answer
 * is reported as an unverified one.
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
  } catch (Lib::Exception&) {
    _modelCertificate.clear();
    _modelProblem = _settings.language == Language::ITALIAN ? "non si è potuto costruire" : "it could not be built";
  }
  if (_modelCertificate.empty()) _hasModel = false;
}

/* ------------------------------------------------------------------------
 * The report
 * ------------------------------------------------------------------------ */

void LogicProblem::report(std::ostream& out, const LogicResult& result) const
{
  Shell::addCommentSignForSZS(out) << "Verification status: " << statusName(result.status, _settings.language)
                                   << " [" << statusCode(result.status) << "]" << std::endl;
  if (!result.reason.empty()) Shell::addCommentSignForSZS(out) << result.reason << std::endl;
  if (!result.detail.empty())
    Shell::addCommentSignForSZS(out) << (_statement.wantsExample() ? "Example (LaTeX): " : "Counterexample (LaTeX): ") << result.detail << std::endl;
  if (_settings.printAccount && !result.proof.empty()) {
    Shell::addCommentSignForSZS(out) << "Explanation (LaTeX) start" << std::endl;
    out << result.proof;
    Shell::addCommentSignForSZS(out) << "Explanation (LaTeX) end" << std::endl;
  }
  if (!_settings.resultPath.empty()) result.write(_settings.resultPath);
}

void LogicProblem::onRefutation(std::ostream& out, Unit* refutation)
{
  bool italian = _settings.language == Language::ITALIAN;
  LogicResult result;
  result.decided = true;
  result.byRefutation = true;

  /* A refutation is a proof, and a proof printed by Vampire is not a
   * certified one: the checker has not replayed it. */
  if (_statement.wantsExample()) {
    result.status = Status::COUNTEREXAMPLE_UNVERIFIED;
    result.reason = italian
      ? "Vampire ha refutato l'enunciato stesso: nessuna interpretazione lo rende vero. La refutazione non è ricontrollata dal verificatore indipendente."
      : "Vampire refuted the statement itself: no interpretation makes it true. The refutation is not rechecked by the independent checker.";
  } else {
    result.status = Status::THEOREM_UNVERIFIED;
    result.reason = italian
      ? "Vampire ha trovato una refutazione; il verificatore indipendente non sa ancora ripercorrere le prove di Vampire, quindi la prova non è certificata."
      : "Vampire found a refutation; the independent checker cannot replay Vampire's proofs yet, so the proof is not certified.";
    if (!refutation->derivedFromGoal())
      result.reason += italian ? " Le ipotesi sono contraddittorie da sole: la tesi non è stata usata."
                               : " The hypotheses are contradictory by themselves: the claim was not used.";
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
      }
    }
    for (unsigned i = 0; i < _statement.sorts().size(); i++) guards = guards || _translator->mayBeEmpty(i);
    if (guards)
      result.proof = italian
        ? "Gli insiemi possono essere vuoti: $\\mathrm{inhabited}_{S}$ \\`e la condizione ``$S$ ha un elemento'', e accompagna i quantificatori su $S$. "
        : "The sets may be empty: $\\mathrm{inhabited}_{S}$ is the condition ``$S$ has an element'', and it goes with the quantifiers over $S$. ";
    result.proof += narrator.narrate(refutation);
  }
  report(out, result);
}

void LogicProblem::onSatisfiable(std::ostream& out)
{
  bool italian = _settings.language == Language::ITALIAN;
  LogicResult result;
  result.decided = true;

  if (_hasModel && !_modelCertificate.empty()) {
    /* For a statement that wants an example the model is the proof: "there
     * are sets and symbols for which it holds", and the checker agreed. */
    result.status = _statement.wantsExample() ? Status::THEOREM_CERTIFIED : Status::COUNTEREXAMPLE_VERIFIED;
    result.detail = _modelText;
    result.certificate = _modelCertificate;
  } else if (_hasModel) {
    /* A model the checker did not confirm is not a counterexample. */
    result.status = Status::UNSOLVED;
    result.reason = (italian ? "Vampire ha trovato un modello finito, ma il verificatore indipendente non lo ha confermato ("
                             : "Vampire found a finite model, but the independent checker did not confirm it (")
                  + _modelProblem + (italian ? "): non è riportato come controesempio." : "): it is not reported as a counterexample.");
  } else {
    result.status = _statement.wantsExample() ? Status::THEOREM_UNVERIFIED : Status::COUNTEREXAMPLE_UNVERIFIED;
    result.reason = italian
      ? "La ricerca di Vampire è finita senza contraddizione, il che per una strategia completa vuol dire che c'è un'interpretazione che soddisfa le formule date; "
        "non è stato prodotto un modello finito che il verificatore indipendente potesse ricalcolare."
      : "Vampire's search ended without a contradiction, which for a complete strategy means that some interpretation satisfies the given formulas; "
        "no finite model was produced for the independent checker to recompute.";

    /* onNoClauses() proposed a model and the checker did not take it: said, because it explains the status. */
    if (!_modelProblem.empty())
      result.reason += (italian ? " Il modello più piccolo, proposto al verificatore, non è stato confermato (" : " The smallest model, proposed to the checker, was not confirmed (")
                     + _modelProblem + ").";
  }
  report(out, result);
}

} // namespace Math
