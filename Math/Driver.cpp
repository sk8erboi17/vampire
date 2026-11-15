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
#include "Verification.hpp"

namespace Math {

using namespace Shell;

namespace {

/** Everything one run of the driver needs to know, read once from the options. */
struct Run {
  std::string name;              // the input, as the reports call it
  Language language;
  bool logicToVampire;
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

/** One run of Vampire on a statement: a child process, its limits, and what it found. */
struct Phase {
  bool finiteModels;        // the search for a finite model, rather than the proof search the user configured
  int deciseconds;          // its time limit; 0 = none
  std::string resultPath;   // where the child writes its LogicResult
  std::string outputPath;   // where the child's output goes
  pid_t process = -1;
  bool running = false;
  bool signalled = false;   // the child was ended by a signal ...
  int signal = 0;           // ... this one
  LogicResult found;        // what it found; found.decided is false if nothing
};

/**
 * True if the answer of a phase settles the statement, so that nothing else
 * has to be waited for.
 *
 *   - A model that the independent checker accepted settles it, whoever
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
  const LogicResult& found = phase.found;
  return found.decided && (!found.certificate.empty() || (found.byRefutation && !phase.finiteModels));
}

/**
 * Has Vampire decide a statement of first-order logic, in child processes.
 *
 * Returns true in the process that asked, with the answer in result
 * (result.decided is false if Vampire did not decide). Returns false in a
 * child: there the problem is loaded, and the caller must return at once so
 * that the process goes on to prove it.
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
 * Each phase writes its output to a temporary file, and only the output of
 * the phase whose answer is reported is copied to the real output: a phase
 * that found nothing would only print a time-out that is not the answer.
 */
bool decideWithVampire(const LogicStatement& statement, const std::string& problemName, Run& run, LogicResult& result)
{
  Options& options = *env.options;
  std::vector<Phase> phases;
  int total = options.timeLimitInDeciseconds();
  int models = options.mathModelTime();
  Options::Mode mode = options.mode();
  bool proving = mode == Options::Mode::VAMPIRE || mode == Options::Mode::CASC || mode == Options::Mode::PORTFOLIO;
  bool alreadyModels = options.saturationAlgorithm() == Options::SaturationAlgorithm::FINITE_MODEL_BUILDING && mode == Options::Mode::VAMPIRE;
  bool together = mode == Options::Mode::VAMPIRE;
  if (proving && models > 0 && !alreadyModels) {
    if (total) models = std::min(models, total);
    phases.push_back({true, models, "", ""});
    phases.push_back({false, together || !total ? total : std::max(total - models, 1), "", ""});
  } else {
    /* The other modes (clausify, output, ...) transform the problem, and do it once. */
    phases.push_back({false, total, "", ""});
  }

  std::string base = (std::filesystem::temp_directory_path()
    / ("vampire-latex-" + std::to_string(getpid()) + "-" + std::to_string(run.statements))).string();
  for (size_t i = 0; i < phases.size(); i++) {
    phases[i].resultPath = base + "-" + std::to_string(i) + ".result";
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
    settings.printAccount = run.printAccount;
    settings.resultPath = phase.resultPath;
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
      LogicResult::read(phase.resultPath, phase.found);
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
  Phase* reported = settled;
  for (Phase& phase : phases) if (!reported && phase.found.decided && !phase.finiteModels) reported = &phase;
  for (Phase& phase : phases) if (!reported && phase.found.decided) reported = &phase;
  if (!reported) reported = &phases.back();

  copyToOutput(reported->outputPath);
  if (reported->signalled)
    addCommentSignForSZS(std::cout) << "The process of the statement was ended by signal " << reported->signal << std::endl;
  for (const Phase& phase : phases) {
    std::remove(phase.resultPath.c_str());
    std::remove(phase.outputPath.c_str());
  }
  result = reported->found.decided ? reported->found : LogicResult();
  return true;
}

/** Adds to the final document a statement decided by Vampire. */
void documentVampireItem(const Parse::LaTeX::Item& item, const LogicResult& result, Language language)
{
  bool italian = language == Language::ITALIAN;
  const char* begin = item.text.c_str();
  const char* end = begin + item.text.size();
  std::string verification = std::string(italian ? "\\textbf{Verifica.} " : "\\textbf{Verification.} ")
                           + statusName(result.status, language) + ".";
  std::string proof;
  const char* reason = result.reason.empty() ? nullptr : result.reason.c_str();

  switch (result.status) {
    case Status::THEOREM_UNVERIFIED:
    case Status::COUNTEREXAMPLE_UNVERIFIED:
      /* With an account, the account is the proof on the page, closed by
       * what was and was not verified. Without one the document says "no
       * proof" and gives the verdict with its reason. */
      if (!result.proof.empty()) proof = result.proof + "\n" + verification + " " + result.reason;
      if (result.status == Status::THEOREM_UNVERIFIED)
        qr_document_external_item(begin, end, QR_PROVED, "da Vampire, per refutazione", reason, nullptr,
                                  proof.empty() ? nullptr : proof.c_str(), nullptr);
      else
        qr_document_external_item(begin, end, proof.empty() ? QR_NOT_PROVED : QR_REFUTED, nullptr, reason, nullptr,
                                  proof.empty() ? nullptr : proof.c_str(), nullptr);
      return;

    case Status::THEOREM_CERTIFIED:
      proof = (italian ? "\\textbf{Dimostrazione.} Un esempio, trovato da Vampire: " : "\\textbf{Proof.} An example, found by Vampire: ")
            + result.detail
            + (italian ? ". Il verificatore indipendente vi ha ricalcolato l'enunciato, che vale. $\\Box$"
                       : ". The independent checker recomputed the statement in it, and it holds. $\\Box$");
      qr_document_external_item(begin, end, QR_PROVED, "con un esempio trovato da Vampire", nullptr, nullptr,
                                proof.c_str(), result.certificate.c_str());
      return;

    case Status::COUNTEREXAMPLE_VERIFIED:
      proof = (italian ? "\\textbf{Controesempio}, trovato da Vampire: " : "\\textbf{Counterexample}, found by Vampire: ")
            + result.detail
            + (italian ? ". Il verificatore indipendente vi ha ricalcolato l'enunciato, che \\`e falso."
                       : ". The independent checker recomputed the statement in it, and it is false.");
      qr_document_external_item(begin, end, QR_REFUTED, nullptr, nullptr, result.detail.c_str(),
                                proof.c_str(), result.certificate.c_str());
      return;

    default:
      qr_document_external_item(begin, end, QR_NOT_PROVED, nullptr, reason ? reason : "Vampire non ha deciso l'enunciato entro i limiti dati",
                                nullptr, nullptr, nullptr);
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
  run.logicToVampire = options.mathLogic() == Options::MathLogic::VAMPIRE;
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

    Parse::LaTeX::Statement statement = frontend.read(item, run.logicToVampire);
    Status status;
    const char* decidedBy;

    if (statement.kind == Parse::LaTeX::Kind::LOGIC) {
      /* First-order logic: Vampire's. Its own report, with the SZS status
       * and the verification status, is in the output already. */
      LogicResult result;
      if (!decideWithVampire(statement.logic, problemName, run, result)) return std::nullopt;
      decidedBy = "vampire";

      /* The caution the engine applies to its own counterexamples: after
       * the formula there was a condition nobody read, and the
       * counterexample may be one of the cases it excludes. */
      bool refuted = result.status == Status::COUNTEREXAMPLE_VERIFIED || result.status == Status::COUNTEREXAMPLE_UNVERIFIED;
      if (statement.conditional && refuted) {
        result = LogicResult();
        result.reason = run.language == Language::ITALIAN
          ? "in generale non vale, ma dopo la formula c'è una condizione che il programma non sa leggere"
          : "it does not hold in general, but after the formula there is a condition that the program cannot read";
        addCommentSignForSZS(std::cout) << "Verification status: " << statusName(Status::UNSOLVED, run.language)
                                        << " [" << statusCode(Status::UNSOLVED) << "]: " << result.reason << std::endl;
      }
      status = result.decided ? result.status : Status::UNSOLVED;
      if (!result.certificate.empty() && run.certificates.is_open()) run.certificates << result.certificate << "\n";
      if (run.document) documentVampireItem(item, result, run.language);
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
