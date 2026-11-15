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
 * @file Driver.cpp
 * Implements the run over the statements of a LaTeX input (Driver.hpp).
 */

#include "Driver.hpp"

#include <algorithm>
#include <csignal>
#include <cstdio>
#include <fcntl.h>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <unistd.h>
#include <vector>

#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/Sys/Multiprocessing.hpp"
#include "Lib/System.hpp"
#include "Parse/LaTeX.hpp"
#include "Shell/Options.hpp"
#include "Shell/UIHelper.hpp"

#include "Engine.h"
#include "LogicProblem.hpp"
#include "Proof/IndependentChecker.h"
#include "Verification.hpp"

namespace Math {

using namespace Shell;

namespace {

/** Everything one run of the driver needs to know, read once from the options. */
struct Run {
  std::string name;              // the input, as the reports call it
  Language language;
  bool explain;
  bool printAccount;
  bool document;                 // a final document is being written
  std::ofstream certificates;    // open if certificates were asked for
  unsigned counts[static_cast<int>(Status::UNSUPPORTED) + 1] = {};
  unsigned statements = 0;
};

/** The whole input: the file named in the options, or the standard input. */
std::string readInput()
{
  std::ostringstream text;
  const std::string file = env.options->inputFile();
  if (file.empty()) {
    text << std::cin.rdbuf();
  } else {
    std::ifstream input(file, std::ios::binary);
    if (input.fail()) USER_ERROR("Cannot open problem file: " + file);
    text << input.rdbuf();
  }
  return text.str();
}

/** A formula on one line, cut if very long: for the report, not for reading back. */
std::string oneLine(std::string text)
{
  std::replace(text.begin(), text.end(), '\n', ' ');
  std::replace(text.begin(), text.end(), '\r', ' ');
  static const size_t LIMIT = 300;
  if (text.size() > LIMIT) text = text.substr(0, LIMIT) + " ...";
  return text;
}

/** The status that says what an engine's verdict says. */
Status engineStatus(const QrVerdict& verdict)
{
  switch (verdict.outcome) {
    case QR_PROVED:      return verdict.certified ? Status::THEOREM_CERTIFIED : Status::THEOREM_UNVERIFIED;
    case QR_REFUTED:     return verdict.certified ? Status::COUNTEREXAMPLE_VERIFIED : Status::COUNTEREXAMPLE_UNVERIFIED;
    case QR_SOLVED:      return verdict.certified ? Status::RESULT_VALIDATED : Status::RESULT_UNVERIFIED;
    case QR_UNSUPPORTED: return Status::UNSUPPORTED;
    case QR_NOT_PROVED:
    case QR_LOGIC:       return Status::UNSOLVED;
  }
  return Status::UNSOLVED;
}

/** Copies the file at path to the output, if it exists. */
void copyToOutput(const std::string& path)
{
  std::ifstream in(path, std::ios::binary);
  if (in) std::cout << in.rdbuf();
  std::cout.flush();
}

/**
 * A verdict of the engine, kept: the strings of a QrVerdict are the
 * engine's and last only until the engine is called again.
 */
struct EngineVerdict {
  QrOutcome outcome = QR_NOT_PROVED;
  bool certified = false;
  std::string line, reason, detail, proof, certificate;
};

EngineVerdict keep(const QrVerdict& verdict)
{
  auto text = [](const char* s) { return std::string(s ? s : ""); };
  EngineVerdict kept;
  kept.outcome = verdict.outcome;
  kept.certified = verdict.certified != 0;
  kept.line = text(verdict.line);
  kept.reason = text(verdict.reason);
  kept.detail = text(verdict.detail);
  kept.proof = text(verdict.proof);
  kept.certificate = text(verdict.certificate);
  return kept;
}

/**
 * True if the verdict carries a certificate and the independent checker, as
 * the module of its own that it is (Proof/), accepts it. The engine has had
 * its own copy of the checker accept it already; what Vampire found is
 * called verified only when the checker that shares nothing with the engine
 * says so too.
 */
bool certifiedIndependently(const EngineVerdict& verdict)
{
  return verdict.certified && !verdict.certificate.empty()
      && proof_check_certificate(verdict.certificate.c_str(), nullptr) == PROOF_CHECK_ACCEPTED;
}

/**
 * Has the engine judge a finite model found by Vampire for the statement of
 * the item: the model is loaded into the engine's structure for models and
 * goes the way of the models the engine finds itself (qr_adopt_model()).
 */
EngineVerdict adoptModel(const Parse::LaTeX::Item& item, const VampireAnswer& answer)
{
  std::vector<const size_t*> tables;
  std::vector<size_t> cells;
  for (const std::vector<size_t>& table : answer.tables) {
    tables.push_back(table.data());
    cells.push_back(table.size());
  }
  QrModel model;
  model.sorts = (unsigned)answer.sizes.size();
  model.sizes = answer.sizes.data();
  model.symbols = (unsigned)answer.tables.size();
  model.tables = tables.data();
  model.cells = cells.data();
  return keep(qr_adopt_model(item.text.c_str(), item.text.c_str() + item.text.size(), &model));
}

/** One run of Vampire on a statement: a child process, its limits, and what it found. */
struct Phase {
  bool finiteModels;        // the search for a finite model, rather than the proof search the user configured
  int deciseconds;          // its time limit; 0 = none
  std::string answerPath;   // where the child writes its VampireAnswer
  std::string outputPath;   // where the child's output goes
  pid_t process = -1;
  bool running = false;
  bool signalled = false;   // the child was ended by a signal ...
  int signal = 0;           // ... this one
  VampireAnswer found;      // what it found; found.kind is NONE if nothing
  bool modelAccepted = false;  // found is a model, and the engine and the checker accepted it
  EngineVerdict model;         // the engine's verdict on that model
};

/**
 * True if the answer of a phase settles the statement, so that nothing else
 * has to be waited for.
 *
 *   - A model that the engine and the checker accepted settles it, whoever
 *     found the model.
 *   - A refutation found by the proof search settles it.
 *   - A refutation from the model search ("no model of any size") is a
 *     correct answer with no steps to follow: the proof search is given the
 *     chance to find one that can be told.
 *   - "Satisfiable" without a model, from the proof search, cannot be
 *     checked: the model search may still find a model that can.
 */
bool settles(const Phase& phase)
{
  return phase.modelAccepted || (phase.found.kind == VampireAnswer::Kind::REFUTATION && !phase.finiteModels);
}

/** What became of a statement of logic, for the report and for the document. */
struct LogicOutcome {
  Status status = Status::UNSOLVED;
  std::string reason;       // why the status is not a certified one, for a reader
  std::string engineLine;   // the engine's verdict on Vampire's model or on the rebuilt proof, in its words
  std::string detail;       // a counterexample, as LaTeX text
  std::string account;      // the account of Vampire's refutation, as LaTeX text
  std::string proof;        // what goes on the page of the document, as LaTeX text
  std::string certificate;  // the certificate the independent checker accepted
  bool byEngine = false;    // what stands is the engine's "not proved": Vampire, asked after it, had no proof either
};

/**
 * Has Vampire search, in child processes, for a proof and for a finite
 * model of a statement of first-order logic.
 *
 * Returns true in the process that asked, with *reported pointing to the
 * phase whose answer is to be used (its found.kind is NONE if Vampire did
 * not decide). Returns false in a child: there the problem is loaded, and
 * the caller must return at once so that the process goes on to prove it.
 *
 * THE PHASES. In the modes that search for a proof there are two: the
 * search for a finite model, for at most math_model_time, and the proof
 * search the user configured. With a single strategy (mode vampire) they
 * RUN TOGETHER, each with the whole time it may use, and the first answer
 * that settles the statement (settles()) ends the other. One after the
 * other, every true statement paid the whole model search before its
 * proof was looked for: measured on the corpus of the engine, 169 s
 * against 91 s for the engine alone. In the portfolio modes, where the
 * proof search is itself many processes, the model search still goes
 * first and the portfolio gets the time that is left.
 *
 * With a set of parts or of maps there is no model search here: a model
 * of the translation may lack parts or maps that really exist
 * (LogicTranslator.hpp), and the engine, which builds the real ones, has
 * already had its turn (Parse/LaTeX.hpp). Only the proof search runs.
 *
 * A model is judged as soon as its phase ends, here, by the engine
 * (adoptModel()): what the model search found is a model for this driver
 * only once the engine has recomputed the statement in it.
 *
 * Each phase writes its output to a temporary file, and only the output of
 * the phase whose answer is reported is copied to the real output: a phase
 * that found nothing would only print a time-out that is not the answer.
 */
bool searchWithVampire(const LogicStatement& statement, const Parse::LaTeX::Item& item, const std::string& problemName,
                       Run& run, std::vector<Phase>& phases, Phase** reported)
{
  Options& options = *env.options;
  int total = options.timeLimitInDeciseconds();
  int models = options.mathModelTime();
  Options::Mode mode = options.mode();
  bool proving = mode == Options::Mode::VAMPIRE || mode == Options::Mode::CASC || mode == Options::Mode::PORTFOLIO;
  bool alreadyModels = options.saturationAlgorithm() == Options::SaturationAlgorithm::FINITE_MODEL_BUILDING && mode == Options::Mode::VAMPIRE;
  bool together = mode == Options::Mode::VAMPIRE;
  if (proving && models > 0 && !alreadyModels && statement.plainOnly()) {
    if (total) models = std::min(models, total);
    phases.push_back({true, models, "", ""});
    phases.push_back({false, together || !total ? total : std::max(total - models, 1), "", ""});
  } else {
    /* One run: a statement with sets of parts or of maps; no model search asked
     * for; or a mode that transforms the problem (clausify, output, ...). */
    phases.push_back({false, total, "", ""});
  }

  std::string base = (std::filesystem::temp_directory_path()
    / ("vampire-latex-" + std::to_string(getpid()) + "-" + std::to_string(run.statements))).string();
  for (size_t i = 0; i < phases.size(); i++) {
    phases[i].answerPath = base + "-" + std::to_string(i) + ".answer";
    phases[i].outputPath = base + "-" + std::to_string(i) + ".out";
  }

  /* Starts a phase. Returns false in the child, with the problem loaded. */
  auto start = [&](Phase& phase) {
    /* Nothing buffered may cross the fork: the child would write it again
     * when it ends (the final document, the certificates, the output). */
    std::cout.flush();
    if (run.certificates.is_open()) run.certificates.flush();
    fflush(nullptr);

    pid_t child = Lib::Sys::fork();
    if (child != 0) {
      phase.process = child;
      phase.running = true;
      return true;
    }
    Lib::System::registerForSIGHUPOnParentDeath();
    int file = open(phase.outputPath.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (file < 0 || dup2(file, STDOUT_FILENO) < 0) _exit(1);
    close(file);

    options.problemName = problemName;
    options.setTimeLimitInDeciseconds(phase.deciseconds);
    if (phase.finiteModels) {
      options.setMode(Options::Mode::VAMPIRE);
      options.setSaturationAlgorithm(Options::SaturationAlgorithm::FINITE_MODEL_BUILDING);
    }

    LogicProblem::Settings settings;
    settings.language = run.language;
    settings.explain = run.explain;
    settings.answerPath = phase.answerPath;
    Kernel::UnitList* units = LogicProblem::install(statement, settings);
    UIHelper::loadUnits(units, LogicProblem::current()->hasConjecture());
    return false;
  };

  auto anyRunning = [&]() {
    for (const Phase& phase : phases) if (phase.running) return true;
    return false;
  };

  /* Start the phases, all at once or one when the one before has ended,
   * and wait until an answer settles the statement or all have ended. */
  size_t next = 0;
  Phase* settled = nullptr;
  while (!settled) {
    while (next < phases.size() && (together || !anyRunning())) {
      if (!start(phases[next])) return false;
      next++;
    }
    if (!anyRunning()) break;

    Lib::Sys::Headstone ended = Lib::Sys::waitForChildTermination(-1);
    for (Phase& phase : phases) {
      if (!phase.running || phase.process != ended.pid) continue;
      phase.running = false;
      phase.signalled = ended.signalled;
      phase.signal = ended.code;
      VampireAnswer::read(phase.answerPath, phase.found);
      if (phase.found.kind == VampireAnswer::Kind::MODEL) {
        phase.model = adoptModel(item, phase.found);
        bool model = phase.model.outcome == QR_REFUTED || phase.model.outcome == QR_PROVED;
        phase.modelAccepted = model && certifiedIndependently(phase.model);
      }
      if (settles(phase)) settled = &phase;
    }
  }

  /* The answer is in: a phase still running is of no use any more. */
  for (Phase& phase : phases) {
    if (!phase.running) continue;
    Lib::Sys::kill(phase.process, SIGINT);
    Lib::Sys::waitForChildTermination(phase.process);
    phase.running = false;
  }

  /* What to report. If nothing settled the statement: an answer of the
   * proof search first (it has its reasons written out), then one of the
   * model search, then the last phase, whose output says why it gave up. */
  *reported = settled;
  for (Phase& phase : phases) if (!*reported && phase.found.kind != VampireAnswer::Kind::NONE && !phase.finiteModels) *reported = &phase;
  for (Phase& phase : phases) if (!*reported && phase.found.kind != VampireAnswer::Kind::NONE) *reported = &phase;
  if (!*reported) *reported = &phases.back();

  copyToOutput((*reported)->outputPath);
  if ((*reported)->signalled)
    addCommentSignForSZS(std::cout) << "The process of the statement was ended by signal " << (*reported)->signal << std::endl;
  for (const Phase& phase : phases) {
    std::remove(phase.answerPath.c_str());
    std::remove(phase.outputPath.c_str());
  }
  return true;
}

/**
 * Decides a statement of first-order logic, the two parts of the program
 * working on it together.
 *
 *   1. Vampire searches: for a proof and, beside it, for a finite model
 *      (searchWithVampire()).
 *   2. A model goes to the engine, which loads it into its own structure
 *      for models, recomputes the statement in it (also as it was written,
 *      before the notation was unfolded) and writes the certificate; the
 *      independent checker judges it. Only then is it a counterexample.
 *   3. A proof goes to the engine too: knowing from Vampire that the
 *      statement is a theorem, the engine rebuilds a proof in a form that
 *      the independent checker can recheck (qr_certify_item()). If it
 *      succeeds the theorem is certified; if it cannot, the theorem stands
 *      on Vampire's proof alone and is reported as not verified.
 *   4. With sets of parts or of maps the turns are the other way round:
 *      the engine has gone first (Parse/LaTeX.hpp) and had no answer, and
 *      what it said comes in as engineSaid. Vampire is asked only for
 *      a proof, from the laws of those sets that the engine supplies. A
 *      proof is a theorem, on Vampire's word; no proof says nothing, and
 *      the engine's "not proved" stands.
 *
 * So the search is Vampire's, the judgement is the checker's, and the
 * engine is what turns the one into something the other can judge.
 *
 * If the engine, while rebuilding the proof, finds a counterexample that
 * the checker accepts, Vampire's proof and that counterexample cannot both
 * be right. Neither is reported: the statement is unsolved, and the output
 * says CONTRADICTION, which is a defect of this program to be looked at.
 *
 * @param engineSaid null if Vampire leads (plain sets); otherwise the
 *        verdict of the engine, which went first and had no answer.
 *
 * Returns false in a child process created for the search (see
 * searchWithVampire()).
 */
bool decideLogic(const LogicStatement& statement, const Parse::LaTeX::Item& item, const std::string& problemName,
                 Run& run, const EngineVerdict* engineSaid, LogicOutcome& outcome)
{
  bool italian = run.language == Language::ITALIAN;
  std::vector<Phase> phases;
  Phase* reported = nullptr;
  if (!searchWithVampire(statement, item, problemName, run, phases, &reported)) return false;
  const VampireAnswer& answer = reported->found;
  const char* begin = item.text.c_str();
  const char* end = begin + item.text.size();

  if (reported->modelAccepted) {
    /* For a statement that wants an example the model is the proof: "there
     * are sets and symbols for which it holds". */
    outcome.status = statement.wantsExample() ? Status::THEOREM_CERTIFIED : Status::COUNTEREXAMPLE_VERIFIED;
    outcome.engineLine = reported->model.line;
    outcome.detail = reported->model.detail;
    outcome.certificate = reported->model.certificate;
    outcome.proof = reported->model.proof
                  + (italian ? " (Il modello \\`e stato trovato da Vampire e ricalcolato qui.)" : " (The model was found by Vampire and recomputed here.)");
    return true;
  }

  if (answer.kind == VampireAnswer::Kind::MODEL && !answer.proposed) {
    /* A model the engine did not confirm is not a counterexample. */
    outcome.status = Status::UNSOLVED;
    outcome.reason = (italian ? "Vampire ha trovato un modello finito, ma il motore matematico non lo ha confermato ("
                              : "Vampire found a finite model, but the mathematical engine did not confirm it (")
                   + (reported->model.reason.empty() ? reported->model.line : reported->model.reason)
                   + (italian ? "): non è riportato come controesempio." : "): it is not reported as a counterexample.");
    return true;
  }

  if (answer.kind == VampireAnswer::Kind::REFUTATION) {
    outcome.account = answer.account;
    if (statement.wantsExample()) {
      outcome.status = Status::COUNTEREXAMPLE_UNVERIFIED;
      outcome.reason = italian
        ? "Vampire ha refutato l'enunciato stesso: nessuna interpretazione lo rende vero. La refutazione non è ricontrollata dal verificatore indipendente."
        : "Vampire refuted the statement itself: no interpretation makes it true. The refutation is not rechecked by the independent checker.";
      return true;
    }

    if (engineSaid) {
      /* The engine went first and could not prove it: there is no proof of
       * its own to rebuild. The theorem stands on Vampire's proof. */
      outcome.status = Status::THEOREM_UNVERIFIED;
      outcome.reason = (italian
        ? "Il motore matematico non aveva né una dimostrazione né un controesempio; Vampire ha dimostrato l'enunciato dalle leggi degli insiemi di parti e di applicazioni che il motore gli ha dato. La prova non è ricontrollata dal verificatore indipendente."
        : "The mathematical engine had neither a proof nor a counterexample; Vampire proved the statement from the laws of the sets of parts and of maps that the engine gave it. The proof is not rechecked by the independent checker.");
      if (!answer.goalUsed)
        outcome.reason += italian ? " Le ipotesi sono contraddittorie da sole: la tesi non è stata usata."
                                  : " The hypotheses are contradictory by themselves: the claim was not used.";
      return true;
    }

    /* A theorem, by Vampire. Now a proof the checker can recheck. */
    EngineVerdict rebuilt = keep(qr_certify_item(begin, end));
    if (rebuilt.outcome == QR_PROVED && certifiedIndependently(rebuilt)) {
      outcome.status = Status::THEOREM_CERTIFIED;
      outcome.engineLine = rebuilt.line;
      outcome.certificate = rebuilt.certificate;
      outcome.proof = rebuilt.proof;
    } else if (rebuilt.outcome == QR_REFUTED) {
      outcome.status = Status::UNSOLVED;
      outcome.account.clear();
      outcome.reason = std::string("CONTRADICTION: ")
        + (italian ? "Vampire ha riportato una dimostrazione, ma il motore matematico ha un controesempio ("
                   : "Vampire reported a proof, but the mathematical engine has a counterexample (")
        + rebuilt.line
        + (italian ? "). Uno dei due sbaglia: l'enunciato non è riportato né come teorema né come falso."
                   : "). One of the two is wrong: the statement is reported neither as a theorem nor as false.");
    } else {
      outcome.status = Status::THEOREM_UNVERIFIED;
      outcome.reason = (italian
        ? "Vampire ha trovato una refutazione; il motore matematico non è riuscito a riscriverla in una forma che il verificatore indipendente sa ricontrollare ("
        : "Vampire found a refutation; the mathematical engine could not rebuild it in a form that the independent checker can recheck (")
        + (rebuilt.reason.empty() ? rebuilt.line : rebuilt.reason) + ").";
    }
    if (!answer.goalUsed && outcome.status != Status::UNSOLVED)
      outcome.reason += italian ? " Le ipotesi sono contraddittorie da sole: la tesi non è stata usata."
                                : " The hypotheses are contradictory by themselves: the claim was not used.";
    return true;
  }

  if (engineSaid) {
    /* The engine went first and had no answer; Vampire has no proof from
     * the laws either. That refutes nothing: the laws are finitely many,
     * and the statement speaks of all the parts and all the maps
     * (LogicTranslator.hpp). What stands is what the engine said. */
    outcome.status = Status::UNSOLVED;
    outcome.engineLine = engineSaid->line;
    outcome.byEngine = true;
    outcome.reason = engineSaid->reason
                   + (italian ? "; nemmeno Vampire, dalle leggi degli insiemi di parti e di applicazioni date dal motore, ha una dimostrazione"
                              : "; Vampire has no proof either, from the laws of the sets of parts and of maps given by the engine");
    return true;
  }

  if (answer.kind == VampireAnswer::Kind::SATURATED || answer.kind == VampireAnswer::Kind::MODEL) {
    /* Saturation without a contradiction, and no model that could be
     * confirmed: "not a theorem" on Vampire's word alone. */
    outcome.status = statement.wantsExample() ? Status::THEOREM_UNVERIFIED : Status::COUNTEREXAMPLE_UNVERIFIED;
    outcome.reason = italian
      ? "La ricerca di Vampire è finita senza contraddizione, il che per una strategia completa vuol dire che c'è un'interpretazione che soddisfa le formule date; "
        "non è stato prodotto un modello finito che il motore matematico potesse ricalcolare."
      : "Vampire's search ended without a contradiction, which for a complete strategy means that some interpretation satisfies the given formulas; "
        "no finite model was produced for the mathematical engine to recompute.";
    return true;
  }

  outcome.status = Status::UNSOLVED;
  outcome.reason = italian ? "Vampire non ha deciso l'enunciato entro i limiti dati." : "Vampire did not decide the statement within the limits given.";
  return true;
}

/** Adds to the final document a statement of logic, decided as decideLogic() describes. */
void documentLogicItem(const Parse::LaTeX::Item& item, const LogicOutcome& outcome, Language language)
{
  bool italian = language == Language::ITALIAN;
  const char* begin = item.text.c_str();
  const char* end = begin + item.text.size();
  std::string verification = std::string(italian ? "\\textbf{Verifica.} " : "\\textbf{Verification.} ")
                           + statusName(outcome.status, language) + ".";
  const char* reason = outcome.reason.empty() ? nullptr : outcome.reason.c_str();
  const char* certificate = outcome.certificate.empty() ? nullptr : outcome.certificate.c_str();
  std::string page;

  switch (outcome.status) {
    case Status::THEOREM_CERTIFIED:
      /* Vampire's account, if there is one (a theorem by example has none),
       * then the proof the checker accepted, as the engine wrote it. */
      if (!outcome.account.empty())
        page = outcome.account + "\n" + verification
             + (italian ? " Il motore matematico ha riscritto la dimostrazione nella forma che il verificatore indipendente ha accettato:\n\n{\\small "
                        : " The mathematical engine rebuilt the proof in the form that the independent checker accepted:\n\n{\\small ")
             + outcome.proof + "\\par}";
      else
        page = outcome.proof;
      qr_document_external_item(begin, end, QR_PROVED, "da Vampire, con la prova riscritta dal motore", nullptr, nullptr, page.c_str(), certificate);
      return;

    case Status::COUNTEREXAMPLE_VERIFIED:
      qr_document_external_item(begin, end, QR_REFUTED, nullptr, nullptr, outcome.detail.c_str(), outcome.proof.c_str(), certificate);
      return;

    case Status::THEOREM_UNVERIFIED:
    case Status::COUNTEREXAMPLE_UNVERIFIED:
      /* With an account, the account is the proof on the page, closed by
       * what was and was not verified. Without one the document says "no
       * proof" and gives the verdict with its reason. */
      if (!outcome.account.empty()) page = outcome.account + "\n" + verification + " " + outcome.reason;
      if (outcome.status == Status::THEOREM_UNVERIFIED)
        qr_document_external_item(begin, end, QR_PROVED, "da Vampire, per refutazione", reason, nullptr,
                                  page.empty() ? nullptr : page.c_str(), nullptr);
      else
        qr_document_external_item(begin, end, page.empty() ? QR_NOT_PROVED : QR_REFUTED, nullptr, reason, nullptr,
                                  page.empty() ? nullptr : page.c_str(), nullptr);
      return;

    default:
      qr_document_external_item(begin, end, QR_NOT_PROVED, nullptr, reason, nullptr, nullptr, nullptr);
      return;
  }
}

} // namespace

bool Driver::wanted()
{
  Options::InputSyntax syntax = env.options->inputSyntax();
  return syntax == Options::InputSyntax::LATEX
      || (syntax == Options::InputSyntax::AUTO && Parse::LaTeX::isLatexFile(env.options->inputFile()));
}

std::optional<int> Driver::run()
{
  Options& options = *env.options;
  Run run;
  run.name = options.inputFile().empty() ? "<stdin>" : std::filesystem::path(options.inputFile()).filename().string();
  run.language = options.mathLanguage() == Options::MathLanguage::IT ? Language::ITALIAN : Language::ENGLISH;
  run.explain = options.mathExplanations();
  run.document = !options.mathDocument().empty();
  run.printAccount = run.explain && !run.document && options.proof() != Options::Proof::OFF;

  std::string text = readInput();
  qr_init();

  if (run.document) {
    const char* problem = qr_document_open(options.mathDocument().c_str(), run.explain);
    if (problem) USER_ERROR(std::string("Cannot write the document ") + options.mathDocument() + ": " + problem);
    qr_document_section(run.name.c_str());
    qr_document_list(1);
  }
  if (!options.mathCertificates().empty()) {
    run.certificates.open(options.mathCertificates(), std::ios::binary);
    if (!run.certificates) USER_ERROR("Cannot write the certificates to " + options.mathCertificates());
  }

  Parse::LaTeX frontend(text);
  Parse::LaTeX::Item item;
  while (frontend.next(item)) {
    run.statements++;
    std::string problemName = run.name + "#" + std::to_string(item.number);
    addCommentSignForSZS(std::cout) << "Statement " << item.number << " of " << run.name << ": "
                                    << oneLine(item.unreadable.empty() ? item.formula : item.text) << std::endl;

    Parse::LaTeX::Statement statement = frontend.read(item);
    Status status;
    const char* decidedBy;

    if (statement.kind == Parse::LaTeX::Kind::LOGIC) {
      /* First-order logic: Vampire searches, the engine and the checker
       * judge what it finds (decideLogic()). Vampire's own report, with the
       * SZS status and the proof or the model, is in the output already. */
      LogicOutcome outcome;
      EngineVerdict engineSaid = keep(statement.verdict);
      if (!decideLogic(statement.logic, item, problemName, run, statement.engineHadNoAnswer ? &engineSaid : nullptr, outcome))
        return std::nullopt;
      decidedBy = outcome.byEngine ? "engine" : "vampire";

      /* The caution the engine applies to its own counterexamples: after
       * the formula there was a condition nobody read, and the
       * counterexample may be one of the cases it excludes. */
      bool refuted = outcome.status == Status::COUNTEREXAMPLE_VERIFIED || outcome.status == Status::COUNTEREXAMPLE_UNVERIFIED;
      if (statement.conditional && refuted) {
        outcome = LogicOutcome();
        outcome.reason = run.language == Language::ITALIAN
          ? "in generale non vale, ma dopo la formula c'è una condizione che il programma non sa leggere"
          : "it does not hold in general, but after the formula there is a condition that the program cannot read";
      }
      status = outcome.status;

      addCommentSignForSZS(std::cout) << "Verification status: " << statusName(status, run.language)
                                      << " [" << statusCode(status) << "]" << std::endl;
      if (!outcome.reason.empty()) addCommentSignForSZS(std::cout) << outcome.reason << std::endl;
      if (!outcome.engineLine.empty()) addCommentSignForSZS(std::cout) << "Engine verdict: " << outcome.engineLine << std::endl;
      if (!outcome.detail.empty()) addCommentSignForSZS(std::cout) << "Counterexample (LaTeX): " << outcome.detail << std::endl;
      if (run.printAccount && !outcome.account.empty()) {
        addCommentSignForSZS(std::cout) << "Explanation (LaTeX) start" << std::endl;
        std::cout << outcome.account;
        addCommentSignForSZS(std::cout) << "Explanation (LaTeX) end" << std::endl;
      }
      if (!outcome.certificate.empty() && run.certificates.is_open()) run.certificates << outcome.certificate << "\n";
      if (run.document) documentLogicItem(item, outcome, run.language);
    } else {
      /* Mathematics proper, or logic that has no first-order translation:
       * the engine decided it, and its verdict is reported in its own words. */
      const QrVerdict& verdict = statement.verdict;
      status = engineStatus(verdict);
      decidedBy = "engine";
      addCommentSignForSZS(std::cout) << "SZS status " << statusSZS(status) << " for " << problemName << std::endl;
      addCommentSignForSZS(std::cout) << "Verification status: " << statusName(status, run.language)
                                      << " [" << statusCode(status) << "]" << std::endl;
      if (verdict.line) addCommentSignForSZS(std::cout) << "Engine verdict: " << verdict.line << std::endl;
      if (!statement.notTranslated.empty())
        addCommentSignForSZS(std::cout) << "Not given to Vampire: " << statement.notTranslated << std::endl;
      if (verdict.certificate && run.certificates.is_open()) run.certificates << verdict.certificate << "\n";
      if (run.document) qr_document_item(item.text.c_str(), item.text.c_str() + item.text.size());
    }

    run.counts[static_cast<int>(status)]++;
    addCommentSignForSZS(std::cout) << "Result " << item.number << ": " << statusCode(status) << " (" << decidedBy << ")" << std::endl;
  }

  /* The summary: how many statements, and how many in each status that occurred. */
  addCommentSignForSZS(std::cout) << "Summary of " << run.name << ": " << run.statements << " statements";
  bool allPositive = true;
  for (int i = 0; i <= static_cast<int>(Status::UNSUPPORTED); i++) {
    Status status = static_cast<Status>(i);
    if (!run.counts[i]) continue;
    std::cout << "; " << statusCode(status) << " " << run.counts[i];
    allPositive = allPositive && statusPositive(status);
  }
  std::cout << std::endl;

  if (qr_unjustified_steps())
    addCommentSignForSZS(std::cout) << "WARNING: " << qr_unjustified_steps()
      << " proof steps of the mathematical engine failed its independent recheck and were discarded" << std::endl;

  if (run.document) {
    qr_document_list(0);
    const char* problem = qr_document_close();
    if (problem) addCommentSignForSZS(std::cout) << "Document: " << problem << std::endl;
  }
  return allPositive && run.statements > 0 ? 0 : 1;
}

} // namespace Math
