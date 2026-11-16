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
#include <chrono>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <fcntl.h>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
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
#include "Names.hpp"
#include "NumberStatement.hpp"
#include "Proof/IndependentChecker.h"
#include "Proof/Replay.hpp"
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
  int rechecked = -1;       // how many steps of Vampire's refutation the independent checker followed, or -1 if it
                            // did not (0 is a refutation without a step: the checker's clauses hold the empty one)
  std::string notRechecked; // if it did not, and the theorem is certified another way: where the recheck stopped
  bool byNumbers = false;   // a statement about numbers settled by numbers that the checker recomputed (askArithmetic())
  bool byCount = false;     // a statement in one integer variable settled by the checker's complete count (countByChecker())
  bool byInfinite = false;  // settled in an infinite interpretation over the integers (certifyInfinite())
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
 * Feeds a refutation by Vampire to the replay, unit by unit in the order
 * of derivation (the lines of VampireAnswer::inferences); the last unit is
 * the empty clause. Returns true if every inference was rebuilt as steps
 * of the checker and the last one is the empty clause; otherwise
 * @b problem says where it stopped.
 */
bool followRefutation(const std::string& inferences, Proof::Replay& replay, std::string& problem)
{
  std::istringstream lines(inferences);
  std::string line;
  std::map<unsigned, std::string> writtenAs;  // each unit's clause as Vampire wrote it, for the diagnosis
  unsigned last = 0;
  bool any = false;
  while (std::getline(lines, line)) {
    std::istringstream words(line);
    std::string kind;
    unsigned unit, count;
    problem = "the refutation of Vampire could not be read back";
    if (!(words >> kind >> unit)) return false;
    last = unit;
    any = true;
    problem = "an inference of Vampire is not one the checker's steps can rebuild: " + line;
    if (kind == "input") {
      int index;
      if (!(words >> index) || index < 0 || index >= replay.initialClauses()) return false;
      replay.input(unit, index);
      writtenAs[unit] = "initial clause " + std::to_string(index);
      continue;
    }

    /* Splitting (VampireAnswer::inferences): the definition of a name, its
     * component clause, a clause of names, the verdict of the SAT solver. */
    if (kind == "definition") {
      unsigned variable;
      std::string written;
      Proof::Replay::Clause clause;
      if (!(words >> variable) || !std::getline(words, written) || !replay.parseClause(written, clause)) return false;
      replay.definition(variable, clause);
      continue;
    }
    if (kind == "component") {
      unsigned level;
      if (!(words >> level)) return false;
      replay.component(unit, level);
      writtenAs[unit] = "the component clause of the split level " + std::to_string(level);
      continue;
    }
    if (kind == "split" || kind == "contradiction") {
      unsigned parent;
      if (!(words >> parent >> count)) return false;
      std::vector<int> names(count);
      for (int& name : names) if (!(words >> name)) return false;
      if (!(kind == "split" ? replay.split(unit, parent, names) : replay.contradiction(unit, parent, names))) {
        problem += "; split clause " + std::to_string(parent) + ": " + writtenAs[parent];
        return false;
      }
      writtenAs[unit] = "a clause of names";
      continue;
    }
    if (kind == "propositional") {
      if (!(words >> count)) return false;
      std::vector<unsigned> premises(count);
      for (unsigned& premise : premises) if (!(words >> premise)) return false;
      if (!replay.propositional(unit, premises)) return false;
      continue;
    }

    if (kind != "unit" || !(words >> count)) return false;  // also "unit N unknown"
    std::vector<unsigned> premises(count);
    for (unsigned& premise : premises) if (!(words >> premise)) return false;
    std::string rule, written;
    unsigned assumed;
    if (!(words >> rule >> assumed)) return false;
    std::vector<unsigned> levels(assumed);
    for (unsigned& level : levels) if (!(words >> level)) return false;
    std::getline(words, written);
    Proof::Replay::Clause clause;
    if (!replay.parseClause(written, clause) || !replay.derive(unit, premises, clause, levels)) {
      /* The inference in full, for whoever wants to see why: its premises as Vampire wrote them. */
      for (unsigned premise : premises) problem += "; premise " + std::to_string(premise) + ": " + writtenAs[premise];
      return false;
    }
    writtenAs[unit] = written;
  }
  problem = "the refutation of Vampire does not end in the empty clause";
  return any && replay.refutes(last);
}

/** What a refutation by Vampire of the checker's clauses gave. */
struct Recheck {
  bool certified = false;   // the independent checker accepted the certificate
  std::string certificate;
  unsigned steps = 0;       // how many steps the checker followed
  std::string problem;      // if not certified: where it stopped, for a reader
};

/**
 * Has Vampire refute the clauses that the independent checker builds from
 * the statement of the item, and has the checker follow that refutation
 * inference by inference.
 *
 * It serves two purposes. When Vampire has already proved the statement
 * (@b proved), this is the recheck of its proof: the first search worked on
 * Vampire's own translation, which the checker does not know. When nobody
 * has proved it and the statement has no first-order form of its own (it
 * quantifies over the parts of a set), this is the proof search itself:
 * the checker's clauses are first-order, with the instances of the
 * formulas on parts that the engine can propose (Engine.h,
 * qr_clauses_item()), and what Vampire refutes there is a certificate at
 * once. Finding no refutation says nothing about the statement.
 *
 * The checker checks a proof by saturation that starts from clauses it
 * builds itself from the statement (Proof/Replay.hpp). So Vampire is run
 * once more, in a child process, on those very clauses, which the engine
 * hands over with the checker's numbers; its refutation comes back as
 * data, each inference with its premises and its clause; Proof::Replay
 * rebuilds each inference as explicit steps of the checker; and the checker
 * reads the finished certificate. Nothing but its acceptance counts: an
 * inference that cannot be rebuilt, or a step rebuilt wrongly, only means
 * that the theorem is not certified this way.
 *
 * That run is Vampire's usual saturation, splitting included (the checker
 * has splitting too: Proof/Replay.hpp), without the parts whose inferences
 * are not instances of the checker's steps: the simplifications that work
 * on several clauses at once or ask a SAT solver, and the eliminations of
 * definitions. What is wanted from it is a refutation that can be
 * followed. A recheck has its own time limit (math_recheck_time): the
 * statement is already proved, and a recheck that does not come soon is
 * given up, not waited for. A proof search has the whole time limit.
 *
 * Returns false in the child process, with the clauses loaded: the caller
 * must return at once so that the process goes on to refute them.
 */
bool refuteHandedClauses(const char* handedOver, const std::string& problemName, Run& run, bool proved, Recheck& recheck,
                         const std::vector<std::pair<std::string, std::string>>& strategy = {}, int deciseconds = 0);

bool refuteCheckerClauses(const Parse::LaTeX::Item& item, const std::string& problemName, Run& run, bool proved, Recheck& recheck)
{
  recheck.problem = "no time was given to it (math_recheck_time 0)";
  if (proved && !env.options->mathRecheckTime()) return true;

  QrVerdict handed = qr_clauses_item(item.text.c_str(), item.text.c_str() + item.text.size());
  return refuteHandedClauses(handed.logic, problemName, run, proved, recheck);
}

/**
 * The work of refuteCheckerClauses(), on clauses already handed over: the
 * beginning of a certificate by saturation, the symbols and the clauses
 * the checker has after it (Proof/Replay.hpp). They come from the engine
 * for a statement of logic, and from the checker itself for a statement
 * about integers proved from their laws (certifyByLaws()). @b strategy is
 * options of Vampire set after those that make its inferences followable,
 * for a search that is known to need them; @b deciseconds, if not zero, a
 * time limit shorter than the one of a recheck, for a search that is one
 * guess among several.
 */
bool refuteHandedClauses(const char* handedOver, const std::string& problemName, Run& run, bool proved, Recheck& recheck,
                         const std::vector<std::pair<std::string, std::string>>& strategy, int deciseconds)
{
  Options& options = *env.options;
  /* A recheck with no time is no recheck (a time limit of zero would be none at all). */
  recheck.problem = "no time was given to it (math_recheck_time 0)";
  if (proved && !options.mathRecheckTime()) return true;
  Proof::Replay replay;
  recheck.problem = "the statement has no translation into the clauses of the checker";
  if (!handedOver || !replay.start(handedOver)) return true;

  std::string base = (std::filesystem::temp_directory_path()
    / ("vampire-latex-" + std::to_string(getpid()) + "-" + std::to_string(run.statements) + "-recheck")).string();
  std::string answerPath = base + ".answer", outputPath = base + ".out";

  /* Nothing buffered may cross the fork (see searchWithVampire()). */
  std::cout.flush();
  if (run.certificates.is_open()) run.certificates.flush();
  fflush(nullptr);

  pid_t child = Lib::Sys::fork();
  if (child == 0) {
    Lib::System::registerForSIGHUPOnParentDeath();
    int file = open(outputPath.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (file < 0 || dup2(file, STDOUT_FILENO) < 0) _exit(1);
    close(file);

    options.problemName = problemName;
    options.setMode(Options::Mode::VAMPIRE);
    int total = options.timeLimitInDeciseconds();
    if (proved) options.setTimeLimitInDeciseconds(total ? std::min(total, options.mathRecheckTime()) : options.mathRecheckTime());
    if (deciseconds > 0) options.setTimeLimitInDeciseconds(std::min(options.timeLimitInDeciseconds(), deciseconds));
    static const char* const FOLLOWABLE[][2] = {
      {"sat_solver", "minisat"}, {"splitting_congruence_closure", "off"}, {"function_definition_elimination", "none"},
      {"unused_predicate_definition_removal", "off"}, {"blocked_clause_elimination", "off"}, {"equality_proxy", "off"},
      {"general_splitting", "off"}, {"inequality_splitting", "0"}, {"sine_selection", "off"},
      {"simultaneous_superposition", "off"}, {"unit_resulting_resolution", "off"}, {"global_subsumption", "off"},
      {"condensation", "off"}, {"inner_rewriting", "off"}, {"forward_literal_rewriting", "off"},
      {"extensionality_resolution", "off"}, {"induction", "none"}, {"theory_axioms", "off"},
      {"superposition_from_variables", "off"}, {"forward_subsumption_demodulation", "off"},
      {"backward_subsumption_demodulation", "off"}, {"newcnf", "off"},
    };
    for (const auto& option : FOLLOWABLE) {
      try {
        options.set(option[0], option[1]);
      } catch (Lib::Exception&) {
        /* An option this Vampire does not have, or not with this value: the
         * run goes on, and an inference that cannot be followed will show. */
      }
    }
    for (const auto& option : strategy) {
      try {
        options.set(option.first, option.second);
      } catch (Lib::Exception&) {
        /* As above: the search goes on with the options it has. */
      }
    }

    LogicProblem::Settings settings;
    settings.explain = false;
    settings.answerPath = answerPath;
    UIHelper::loadUnits(LogicProblem::installClauses(replay, settings), false);
    return false;
  }

  Lib::Sys::waitForChildTermination(child);
  VampireAnswer answer;
  VampireAnswer::read(answerPath, answer);
  std::remove(answerPath.c_str());
  std::remove(outputPath.c_str());
  recheck.problem = "Vampire found no refutation of the checker's clauses within the limits";
  if (answer.kind != VampireAnswer::Kind::REFUTATION) return true;

  /* A splitting may ask for a second attempt, with a name given to its
   * clause the way that splitting has it written (Replay::restart()).
   * Each attempt settles at least one more name, and they are few. */
  bool followed = followRefutation(answer.inferences, replay, recheck.problem);
  for (int attempt = 0; !followed && replay.worthAnotherAttempt() && attempt < 8; attempt++) {
    replay.restart();
    followed = followRefutation(answer.inferences, replay, recheck.problem);
  }
  if (!followed) return true;

  std::string certificate = replay.certificate();
  const char* why = "";
  if (proof_check_certificate(certificate.c_str(), &why) != PROOF_CHECK_ACCEPTED) {
    recheck.problem = std::string("the independent checker did not accept the rebuilt steps: ") + why;
    return true;
  }
  recheck.problem.clear();
  recheck.certified = true;
  recheck.certificate = certificate;
  recheck.steps = replay.steps();
  return true;
}

/** What Vampire's arithmetic theories said of a statement about numbers. */
struct ArithmeticAnswer {
  bool asked = false;      // the statement was one that can be given to them
  bool found = false;      // a proof was found ...
  bool denied = false;     // ... of the negation of the statement, rather than of the statement
  std::string sort;        // the sort of the problem: $int, $rat or $real
  bool certified = false;  // Vampire also gave numbers that settle the statement, and the independent
                           // checker recomputed the statement on them
  bool counted = false;    // ... and settled by its complete count a quantifier over one integer that no number shows
  bool byLaws = false;     // or: the checker followed a refutation by Vampire of its own clauses with the laws of the
                           // integers (certifyByLaws())
  unsigned steps = 0;      // ... of so many steps
  std::string lawsProblem; // if that was tried and did not certify: where it stopped
  std::string certificate; // the certificate the checker accepted
  std::string numbers;     // those numbers, as LaTeX: "$x = 7$, $y = 8$"
};

/**
 * Has the independent checker follow a proof, by Vampire, that a statement
 * about integers holds, or with @b denied that it fails, from the laws of
 * the integers.
 *
 * Vampire's arithmetic theories have proved it, but their inferences
 * compute: they are not steps of the checker. The checker has a
 * certificate for this ("arithmetic", chapter 20f of checker.c): it
 * translates the statement by itself, with sum, opposite, product and
 * order as symbols of which it knows only the laws of the integers, which
 * it adds, and follows a refutation of the clauses it makes, together with
 * clauses without variables that it accepts by computing them. Vampire
 * refutes those very clauses, with no theory and with the options whose
 * inferences can be followed, and Proof::Replay writes its inferences as
 * the checker's steps, as for a statement of logic (refuteHandedClauses()).
 *
 * The clauses are asked of the checker (proof_arithmetic_clauses()):
 * first to know the numerals of the translation, then with the facts about
 * them (NumberStatement::arithmeticFacts()), which are given to Vampire
 * too. What counts is the checker accepting the finished certificate.
 *
 * Returns false in a child process, with the clauses loaded: the caller
 * must return at once.
 */
bool certifyBeginning(const std::string& beginning, const std::string& problemName, Run& run, Recheck& recheck, bool quick = false);

bool certifyByLaws(const NumberStatement& statement, bool denied, const std::string& problemName, Run& run, Recheck& recheck)
{
  std::string beginning = statement.arithmeticBeginning(denied);
  recheck.problem = "the statement is not about integers";
  if (beginning.empty()) return true;
  return certifyBeginning(beginning, problemName, run, recheck);
}

/**
 * The listing of proof_arithmetic_clauses() without its lines "claim" and
 * "numerals", which are not for Proof::Replay; the values of the numerals
 * go to @b numerals.
 */
std::string clausesListed(const char* listing, std::vector<long long>& numerals)
{
  std::istringstream lines(listing);
  std::string line, rest;
  bool started = false;
  while (std::getline(lines, line)) {
    if (!started && line.compare(0, 9, "numerals ") == 0) {
      started = true;
      std::istringstream values(line.substr(9));
      for (long long value; values >> value;) numerals.push_back(value);
      continue;
    }
    if (started) rest += line + "\n";
  }
  return rest;
}

/**
 * Has the independent checker follow a proof by Vampire of the claim of a
 * certificate "arithmetic" or "infinite" whose @b beginning is given, up
 * to its line "clausify": the clauses from the checker, the facts about
 * the numerals, the refutation from Vampire, the steps from Proof::Replay
 * (see certifyByLaws()). With @b quick, one search of two seconds with the
 * first strategy, for a beginning that is one guess among several.
 * Returns false in a child process.
 */
bool certifyBeginning(const std::string& beginning, const std::string& problemName, Run& run, Recheck& recheck, bool quick)
{
  const char* why = "";
  char* first = proof_arithmetic_clauses((beginning + "end\n").c_str(), &why);
  if (!first) {
    recheck.problem = std::string("the checker does not translate the statement: ") + why;
    return true;
  }
  std::vector<long long> numerals;
  clausesListed(first, numerals);
  std::free(first);

  std::string facts = NumberStatement::arithmeticFacts(numerals);
  char* clauses = proof_arithmetic_clauses((beginning + facts + "end\n").c_str(), &why);
  if (!clauses) {
    recheck.problem = std::string("the checker does not accept the facts about the numerals: ") + why;
    return true;
  }
  std::vector<long long> again;
  std::string handed = beginning + facts + clausesListed(clauses, again);
  std::free(clauses);

  /* Two searches, one after the other, each with the time of a recheck.
   * With the laws of a ring among the clauses the default selection of
   * literals gets lost in the sums and products: "(ab - 2)(a - b) = 0 and
   * (bc - 2)(b - c) = 0 give (ac - 2)(a - c) = 0" is not refuted in five
   * seconds with it. The first search has selection 1, the saturation
   * algorithm that does not discard clauses to meet the time limit
   * (discount: the default one finds that refutation with three seconds on
   * an idle machine and misses it with two, or with three on a busy one),
   * and four clauses chosen by weight for one by age: then it takes 0.06
   * seconds, and 1.5 with the build for debugging. The second search is the
   * default, which refutes other problems. Measured on 120 true claims of
   * Math/tools/fuzz_arithmetic_laws.py, two seconds each: the first refutes
   * 93, the default 100, the two one after the other 106. */
  static const std::vector<std::vector<std::pair<std::string, std::string>>> STRATEGIES = {
    {{"selection", "1"}, {"saturation_algorithm", "discount"}, {"age_weight_ratio", "1:4"}}, {}};
  std::string problems;   // where each search stopped, for a reader
  for (size_t i = 0; i < (quick ? 1 : STRATEGIES.size()); i++) {
    recheck = Recheck();
    if (!refuteHandedClauses(handed.c_str(), problemName, run, /* proved */ true, recheck, STRATEGIES[i], quick ? 20 : 0)) return false;
    if (recheck.certified) return true;
    problems += (i ? "; then " : "") + recheck.problem;
  }
  recheck.problem = problems;
  return true;
}

/** A number as the checker writes it ("7", "-1/2"), in LaTeX. */
std::string numberLatex(const std::string& value)
{
  size_t bar = value.find('/');
  if (bar == std::string::npos) return value;
  if (value.substr(bar + 1) == "1") return value.substr(0, bar);  // 0/1, as Vampire writes a whole number among rationals
  bool negative = !value.empty() && value[0] == '-';
  return std::string(negative ? "-" : "") + "\\frac{" + value.substr(negative ? 1 : 0, bar - (negative ? 1 : 0)) + "}{" + value.substr(bar + 1) + "}";
}

/** The letter number @b code of the engine, in LaTeX: a letter of the alphabet as it is, anything else by its number. */
std::string letterLatex(const std::string& code)
{
  int letter = code.size() <= 3 ? std::stoi(code) : 0;
  if ((letter >= 'a' && letter <= 'z') || (letter >= 'A' && letter <= 'Z')) return std::string(1, (char)letter);
  return "v_{" + code + "}";
}

/**
 * The tuples of numbers that an answer of Vampire offers, in the output
 * written to the file at @b path. The answer is one tuple,
 * "% SZS answers Tuple [[7,8,0,1]|_] for ...", or several of which at least
 * one is right, "[([101,1]|[102,2]|[101,sK1(102)])|_]"; each has one value
 * per variable of the conjecture. Appended to @b tuples are those made of
 * @b count numbers, as the checker writes numbers, each once: a value that
 * is not a number (a term that Vampire did not compute, a variable when any
 * value would do) leaves its tuple out. Which of them settles the statement
 * is for the checker to say.
 */
void answeredTuples(const std::string& path, size_t count, std::vector<std::vector<std::string>>& tuples)
{
  std::ifstream output(path);
  std::string line;
  static const std::string MARK = "SZS answers Tuple [";
  while (std::getline(output, line)) {
    size_t at = line.find(MARK);
    if (at == std::string::npos) continue;
    at += MARK.size();

    /* Every "[...]" from here on is one tuple: the terms inside have
     * parentheses, never brackets. */
    for (size_t open = line.find('[', at); open != std::string::npos; open = line.find('[', at)) {
      size_t close = line.find(']', open);
      if (close == std::string::npos) break;
      std::vector<std::string> values;
      std::string element;
      bool numbers = true;
      int depth = 0;
      auto finish = [&]() {
        std::string value;
        numbers = NumberStatement::answerValue(element, value) && numbers;
        values.push_back(value);
        element.clear();
      };
      /* The elements, separated by the commas that are not inside a term. */
      for (size_t i = open + 1; i < close; i++) {
        char c = line[i];
        if (c == '(') depth++;
        if (c == ')') depth--;
        if (c == ',' && depth == 0) finish();
        else element += c;
      }
      finish();
      if (numbers && values.size() == count && std::find(tuples.begin(), tuples.end(), values) == tuples.end()) tuples.push_back(values);
      at = close + 1;
    }
    return;
  }
}

/** What the independent checker's count said of a statement in one integer variable (countByChecker()). */
struct CountAnswer {
  bool asked = false;       // the statement was one the count applies to
  bool certified = false;   // the checker settled it ...
  bool denied = false;      // ... as false, rather than as true
  std::string certificate;  // the certificate it accepted
};

/**
 * Asks the independent checker to settle by itself a statement with
 * quantifiers over numbers that needs no number from anybody: one integer
 * variable, a "for all" or a "there is", with nothing quantified inside.
 * The checker tries every integer that can matter, which is a finite and
 * complete count (20e of Math/quaerens/checker.c), and accepts the
 * certificate that says the statement holds, or the one that says it
 * fails, or neither. Nothing is searched for here and nothing is believed:
 * @b handedOver is the statement as the engine read it and wrote it in the
 * notation of the certificates (Parse::LaTeX::Statement::numbers).
 *
 * This is how a theorem that holds "for every integer" gets a certificate:
 * the engine's own, when it proved the statement without one, and those
 * that neither the engine nor Vampire's arithmetic decides.
 */
void countByChecker(const std::string& handedOver, CountAnswer& answer)
{
  if (handedOver.empty()) return;
  NumberStatement statement = NumberStatement::read(handedOver);
  if (!statement.ok()) return;
  for (bool denied : {false, true}) {
    NumberStatement::WitnessProblem problem = statement.witnessProblem(denied);
    if (problem.tptp.empty() || !problem.quantifiers.empty()) continue;   // numbers would have to be found first
    answer.asked = true;
    std::string certificate = statement.certificate(denied, problem, {});
    const char* why = "";
    if (proof_check_certificate(certificate.c_str(), &why) != PROOF_CHECK_ACCEPTED) continue;
    answer.certified = true;
    answer.denied = denied;
    answer.certificate = certificate;
    return;
  }
}

/**
 * Gives a statement with quantifiers over numbers, which the engine read
 * and could not decide, to Vampire's arithmetic theories.
 *
 * The engine hands the statement over if every variable in it ranges over
 * numbers of one kind (Engine.h, qr_numbers_item(); it is @b handedOver,
 * read before the engine decided the statement); NumberStatement writes
 * it as a TPTP problem over $int, $rat or $real, and Vampire's own parser
 * reads it in a child process, which from there on is Vampire on that
 * problem with whatever options were given. Two such processes run
 * together, one with the statement as conjecture and one with its
 * negation: a statement about numbers is as likely to be false as true,
 * and a proof of the negation is the only refutation Vampire can give
 * (there are no finite models of arithmetic to look for). The first that
 * finds a proof ends the other, and its output, with Vampire's own report
 * of the proof, is copied to the output; the problem of the negation is
 * named as such there ("the negation of ..."), so that the status Vampire
 * prints for it is not read as the status of the statement.
 *
 * The searches have their own time limit (math_numbers_time): a statement
 * about numbers that Vampire does not decide soon is usually one it does
 * not decide, and a document may hold many.
 *
 * Where numbers can settle the statement (a "for all" to be refuted, a
 * "there is" to be proved: NumberStatement::witnessProblem()), the search
 * is given the problem in that form and Vampire is asked for the numbers
 * too, by question answering. With them a certificate is written, and the
 * independent checker recomputes the statement on them: then, and only
 * then, what was found is verified. Otherwise the caller must report it as
 * found, not verified (NumberStatement.hpp).
 *
 * Where the numbers leave a quantifier over one integer for the checker to
 * settle by its count, asking for them makes the problem harder, and the
 * answer may be several tuples of which one is right. So the first search
 * is the plain one, as if there were nothing to ask; if it finds a proof, a
 * second search of the same side asks for the numbers, and the checker is
 * given each tuple offered until it accepts one. That second search uses
 * the saturation algorithm that does not discard clauses to meet the time
 * limit (discount): with the default one the same problem is proved in a
 * second with ten seconds allowed and not at all with five. If it finds
 * nothing, what the first search found stands, not verified.
 *
 * Returns false in a child process, with the problem loaded: the caller
 * must return at once so that the process goes on to prove it.
 */
bool askArithmetic(const std::string& handedOver, const std::string& problemName, Run& run, ArithmeticAnswer& answer)
{
  /* How many of the tuples that an answer offers are given to the checker:
   * an answer has a handful, and each costs one recomputation. */
  static const size_t MAX_OFFERED_TUPLES = 16;
  Options& options = *env.options;
  if (!options.mathNumbersTime() || handedOver.empty()) return true;
  NumberStatement statement = NumberStatement::read(handedOver);
  if (!statement.ok()) return true;
  answer.asked = true;
  answer.sort = statement.sort();

  std::string base = (std::filesystem::temp_directory_path()
    / ("vampire-latex-" + std::to_string(getpid()) + "-" + std::to_string(run.statements) + "-numbers")).string();
  struct Search {
    bool denied;
    std::string answerPath, outputPath;
    NumberStatement::WitnessProblem witnesses;  // the problem in the form whose proof comes with numbers, if there is one
    pid_t process = -1;
    bool running = false;
    VampireAnswer found;
  };
  Search searches[2] = {{false, base + "-0.answer", base + "-0.out", statement.witnessProblem(false)},
                        {true, base + "-1.answer", base + "-1.out", statement.witnessProblem(true)}};

  /* Starts the search in a child process; with askNumbers, on the problem
   * whose proof names the numbers. Returns false in the child, with the
   * problem loaded. Nothing buffered may cross the fork (see
   * searchWithVampire()). */
  auto launch = [&](Search& search, bool askNumbers) {
    std::cout.flush();
    if (run.certificates.is_open()) run.certificates.flush();
    fflush(nullptr);
    pid_t child = Lib::Sys::fork();
    if (child != 0) {
      search.process = child;
      search.running = true;
      return true;
    }
    Lib::System::registerForSIGHUPOnParentDeath();
    int file = open(search.outputPath.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (file < 0 || dup2(file, STDOUT_FILENO) < 0) _exit(1);
    close(file);

    options.problemName = (search.denied ? "the negation of " : "") + problemName;
    int total = options.timeLimitInDeciseconds();
    options.setTimeLimitInDeciseconds(total ? std::min(total, options.mathNumbersTime()) : options.mathNumbersTime());
    /* With numbers to ask for: the same problem, written so that a proof
     * names them, and the request for the answer. */
    bool numbers = askNumbers;
    if (numbers) {
      try {
        options.set("question_answering", "plain");
        if (search.witnesses.counted) options.set("saturation_algorithm", "discount");
      } catch (Lib::Exception&) {
        numbers = false;
      }
    }
    std::istringstream problem(numbers ? search.witnesses.tptp : statement.tptp(search.denied));
    UIHelper::parseStream(problem, "", Options::InputSyntax::TPTP, /* verbose */ false, /* preferSMTonAuto */ false);
    LogicProblem::Settings settings;
    settings.explain = false;
    settings.answerPath = search.answerPath;
    LogicProblem::installLoaded(settings);
    return false;
  };
  for (Search& search : searches)
    if (!launch(search, !search.witnesses.quantifiers.empty() && !search.witnesses.counted)) return false;

  /* The first proof ends the other search. */
  Search* settled = nullptr;
  while (!settled && (searches[0].running || searches[1].running)) {
    Lib::Sys::Headstone ended = Lib::Sys::waitForChildTermination(-1);
    for (Search& search : searches) {
      if (!search.running || search.process != ended.pid) continue;
      search.running = false;
      VampireAnswer::read(search.answerPath, search.found);
      if (search.found.kind == VampireAnswer::Kind::REFUTATION) settled = &search;
    }
  }
  for (Search& search : searches) {
    if (!search.running) continue;
    Lib::Sys::kill(search.process, SIGINT);
    Lib::Sys::waitForChildTermination(search.process);
    search.running = false;
  }
  if (settled) {
    answer.found = true;
    answer.denied = settled->denied;
    copyToOutput(settled->outputPath);

    /* The numbers Vampire gave, if the statement is one that numbers
     * settle: the checker recomputes it on them, and nothing else makes
     * the answer a verified one. */
    std::vector<std::vector<std::string>> offered;
    const NumberStatement::WitnessProblem& witnesses = settled->witnesses;
    if (!witnesses.tptp.empty() && witnesses.quantifiers.empty()) {
      offered.push_back({});   // nothing to exhibit: the checker's count settles the statement, or nothing does
    } else if (!witnesses.tptp.empty() && !witnesses.counted) {
      answeredTuples(settled->outputPath, witnesses.quantifiers.size(), offered);
    } else if (!witnesses.tptp.empty()) {
      /* The second search, for the numbers (see above this function). */
      Search again = {settled->denied, base + "-2.answer", base + "-2.out", witnesses};
      if (!launch(again, true)) return false;
      Lib::Sys::waitForChildTermination(again.process);
      VampireAnswer::read(again.answerPath, again.found);
      if (again.found.kind == VampireAnswer::Kind::REFUTATION) answeredTuples(again.outputPath, witnesses.quantifiers.size(), offered);
      std::remove(again.answerPath.c_str());
      std::remove(again.outputPath.c_str());
    }
    for (size_t tried = 0; tried < offered.size() && tried < MAX_OFFERED_TUPLES && !answer.certified; tried++) {
      const std::vector<std::string>& values = offered[tried];
      std::string certificate = statement.certificate(settled->denied, witnesses, values);
      const char* why = "";
      if (proof_check_certificate(certificate.c_str(), &why) != PROOF_CHECK_ACCEPTED) continue;
      answer.certified = true;
      answer.counted = witnesses.counted != 0;
      answer.certificate = certificate;
      for (size_t i = 0; i < values.size(); i++)
        answer.numbers += std::string(i ? ", " : "") + "$" + letterLatex(witnesses.letters[i]) + " = " + numberLatex(values[i]) + "$";
    }

    /* No numbers settle it: a statement that holds for every value, or a
     * refutation that needs more than values. Among integers the checker
     * can follow a proof from their laws (certifyByLaws()). */
    if (!answer.certified && statement.sort() == "$int") {
      Recheck byLaws;
      if (!certifyByLaws(statement, settled->denied, problemName, run, byLaws)) return false;
      if (byLaws.certified) {
        answer.certified = answer.byLaws = true;
        answer.certificate = byLaws.certificate;
        answer.steps = byLaws.steps;
      } else {
        answer.lawsProblem = byLaws.problem;
      }
    }
  }
  for (const Search& search : searches) {
    std::remove(search.answerPath.c_str());
    std::remove(search.outputPath.c_str());
  }
  return true;
}

/**
 * Has Vampire's arithmetic theories try, in two child processes at once,
 * to prove the TPTP problem @b claim and the TPTP problem @b negation,
 * within @b deciseconds; the first proof ends the other search. With
 * @b count > 0 the search of the claim also asks for the values of the
 * variables of its conjecture (question answering), and @b tuples receives
 * those that are numbers, @b count in each (answeredTuples()). @b result
 * is 1 if the claim was proved, -1 if its negation was, 0 if neither.
 * Returns false in a child, with the problem loaded: the caller must
 * return at once.
 */
bool proveNumbers(const std::string& claim, const std::string& negation, size_t count, int deciseconds,
                  const std::string& problemName, Run& run, int& result, std::vector<std::vector<std::string>>& tuples)
{
  Options& options = *env.options;
  std::string base = (std::filesystem::temp_directory_path()
    / ("vampire-latex-" + std::to_string(getpid()) + "-" + std::to_string(run.statements) + "-interpretation")).string();
  struct Search { const std::string* tptp; bool answers; std::string answerPath, outputPath; pid_t process; bool running; };
  Search searches[2] = {{&claim, count > 0, base + "-0.answer", base + "-0.out", -1, false},
                        {&negation, false, base + "-1.answer", base + "-1.out", -1, false}};
  for (Search& search : searches) {
    /* Nothing buffered may cross the fork (see searchWithVampire()). */
    std::cout.flush();
    if (run.certificates.is_open()) run.certificates.flush();
    fflush(nullptr);
    pid_t child = Lib::Sys::fork();
    if (child != 0) {
      search.process = child;
      search.running = true;
      continue;
    }
    Lib::System::registerForSIGHUPOnParentDeath();
    int file = open(search.outputPath.c_str(), O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (file < 0 || dup2(file, STDOUT_FILENO) < 0) _exit(1);
    close(file);
    options.problemName = problemName;
    options.setMode(Options::Mode::VAMPIRE);
    options.setTimeLimitInDeciseconds(deciseconds);
    if (search.answers) {
      try {
        options.set("question_answering", "plain");
      } catch (Lib::Exception&) {
      }
    }
    std::istringstream problem(*search.tptp);
    UIHelper::parseStream(problem, "", Options::InputSyntax::TPTP, /* verbose */ false, /* preferSMTonAuto */ false);
    LogicProblem::Settings settings;
    settings.explain = false;
    settings.answerPath = search.answerPath;
    LogicProblem::installLoaded(settings);
    return false;
  }

  result = 0;
  while (!result && (searches[0].running || searches[1].running)) {
    Lib::Sys::Headstone ended = Lib::Sys::waitForChildTermination(-1);
    for (int i = 0; i < 2; i++) {
      Search& search = searches[i];
      if (!search.running || search.process != ended.pid) continue;
      search.running = false;
      VampireAnswer found;
      VampireAnswer::read(search.answerPath, found);
      if (found.kind == VampireAnswer::Kind::REFUTATION) result = i == 0 ? 1 : -1;
    }
  }
  for (Search& search : searches) {
    if (!search.running) continue;
    Lib::Sys::kill(search.process, SIGINT);
    Lib::Sys::waitForChildTermination(search.process);
    search.running = false;
  }
  if (result == 1 && count) answeredTuples(searches[0].outputPath, count, tuples);
  for (const Search& search : searches) {
    std::remove(search.answerPath.c_str());
    std::remove(search.outputPath.c_str());
  }
  return true;
}

/** What the search for an infinite interpretation over the integers gave (certifyInfinite()). */
struct InfiniteAnswer {
  bool certified = false;
  std::string certificate;    // the certificate "infinite" the checker accepted
  unsigned steps = 0;         // the steps of Vampire's refutation it followed
  std::string interpretation; // the interpretation, as LaTeX: "$S = \mathbb{N}_0$, $f(x) = x + 1$"
  std::string problem;        // if none was found: why, for a reader
};

/**
 * Looks for an infinite interpretation over the integers in which a
 * statement of logic is false, and has the independent checker certify it
 * (certificate "infinite", 20g of checker.c).
 *
 * WHEN. Vampire's saturation ended without a contradiction and no finite
 * model was found: "an injective map of a set into itself is onto" holds
 * in every finite set, and its counter-models are infinite. Such a
 * statement used to be reported as refuted on Vampire's word alone.
 *
 * HOW. The statement as the checker writes it (the beginning that
 * qr_clauses_item() hands over: its sets, its symbols, the statement) is
 * given a few interpretations to try, each set the integers from 0 on and
 * each symbol one of a short list by its kind (unary maps: x + 1, then x -
 * 1 except at 0, then x and 0; elements: 0 and 1; parts: {0}, the
 * positive ones, all, none; and so on). For each the checker writes the
 * claim "the symbols are maps of those sets, and the statement is false
 * there", a statement about integers (proof_arithmetic_clauses(), line
 * claim). Vampire's arithmetic theories are asked to prove it, briefly: a
 * claim they do not prove is not tried further. Its quantifiers that are a
 * "there is" at the outermost level are asked for values too (question
 * answering): they become the witnesses of the certificate, which make the
 * proof the checker follows much shorter ("f(0) = f(1) with 0 != 1"). Then
 * Vampire proves the claim once more from the laws of the integers on the
 * checker's clauses, as for a statement about numbers (certifyBeginning()),
 * and the certificate is what the checker accepts.
 *
 * The interpretations tried are few on purpose: every one costs a search
 * of Vampire, and the statements this is for have simple counter-models.
 * None of this is trusted: a wrong interpretation is a claim nobody proves,
 * and the certificate is the checker's verdict.
 *
 * Returns false in a child process.
 */
bool certifyInfinite(const Parse::LaTeX::Item& item, const std::string& problemName, Run& run, InfiniteAnswer& answer)
{
  Options& options = *env.options;
  static const size_t MAX_INTERPRETATIONS = 12, MAX_TUPLES = 4;
  answer.problem = "the arithmetic theories were not asked (math_numbers_time 0)";
  if (!options.mathNumbersTime() || !options.mathRecheckTime()) return true;
  int deciseconds = std::min(options.mathNumbersTime(), 50);

  /* The sets, the symbols and the statement, as the checker writes them. */
  QrVerdict handed = qr_clauses_item(item.text.c_str(), item.text.c_str() + item.text.size());
  answer.problem = "the statement has no translation for the checker";
  if (!handed.logic) return true;
  struct Symbol { std::string name; int arity; bool predicate; };
  std::vector<std::string> sorts;
  std::vector<Symbol> symbols;
  std::string declarations, statementLine;
  std::istringstream lines(handed.logic);
  std::string line;
  while (std::getline(lines, line) && line != "clausify" && line != "clausify forward") {
    std::istringstream words(line);
    std::vector<std::string> word;
    for (std::string w; words >> w;) word.push_back(w);
    if (word.empty() || line == "certificate saturation") continue;
    if (word[0] == "sort" && word.size() == 2) {
      sorts.push_back(word[1]);
    } else if (word[0] == "symbol" && word.size() >= 3 && word.size() <= 5) {
      symbols.push_back({word[1], (int)word.size() - 3, word.back() == "bool"});
    } else if (word[0] == "statement") {
      statementLine = line;
      continue;
    } else {
      answer.problem = "the statement has sets of parts or of maps, written numbers or laws, which are not interpreted here";
      return true;
    }
    declarations += line + "\n";
  }
  if (statementLine.empty() || sorts.empty()) return true;

  /* The candidates of each kind of symbol: the checker's notation, and the
   * LaTeX of "NAME(x) = ..." with the name in place of %s. */
  struct Candidate { const char* definition; const char* latex; };
  static const std::vector<Candidate> ELEMENTS = {{"0", "%s = 0"}, {"1", "%s = 1"}};
  static const std::vector<Candidate> MAPS = {
    {"(add (var 0) 1)", "%s(x) = x + 1"},
    {"(cases (less 0 (var 0)) (sub (var 0) 1) 0)", "%s(x) = x - 1 \\text{ for } x > 0,\\ %s(0) = 0"},
    {"(var 0)", "%s(x) = x"},
    {"0", "%s(x) = 0"}};
  static const std::vector<Candidate> OPERATIONS = {
    {"(add (var 0) (var 1))", "%s(x, y) = x + y"}, {"(mul (var 0) (var 1))", "%s(x, y) = x y"},
    {"(var 0)", "%s(x, y) = x"}, {"(var 1)", "%s(x, y) = y"}};
  static const std::vector<Candidate> PARTS = {
    {"(= (var 0) 0)", "%s = \\{0\\}"}, {"(less 0 (var 0))", "%s = \\{x \\mid x > 0\\}"},
    {"(= 0 0)", "%s = \\mathbb{N}_0"}, {"(neq 0 0)", "%s = \\emptyset"}};
  static const std::vector<Candidate> RELATIONS = {
    {"(less (var 0) (var 1))", "%s(x, y) \\iff x < y"}, {"(lesseq (var 0) (var 1))", "%s(x, y) \\iff x \\le y"},
    {"(= (var 0) (var 1))", "%s(x, y) \\iff x = y"}, {"(neq (var 0) (var 1))", "%s(x, y) \\iff x \\neq y"}};
  std::vector<const std::vector<Candidate>*> lists;
  for (const Symbol& symbol : symbols)
    lists.push_back(symbol.predicate ? (symbol.arity == 1 ? &PARTS : &RELATIONS)
                                     : (symbol.arity == 0 ? &ELEMENTS : symbol.arity == 1 ? &MAPS : &OPERATIONS));
  if (symbols.empty()) return true;

  std::string interpret;
  for (const std::string& sort : sorts) interpret += "interpret " + sort + " (set ge 0)\n";
  /* The interpretations to try, those with the first candidates of every
   * symbol first: by the sum of the places of the candidates chosen. A
   * counter-model of two maps, one a candidate's first and the other its
   * second, is then the third tried, not the fifth. */
  std::vector<std::vector<size_t>> order(1, std::vector<size_t>(symbols.size(), 0));
  for (size_t k = 0; k < order.size() && order.size() < 4096; k++)
    for (size_t i = 0; i < symbols.size(); i++) {
      std::vector<size_t> next = order[k];
      if (++next[i] >= lists[i]->size()) continue;
      if (std::find(order.begin(), order.end(), next) == order.end()) order.push_back(next);
    }
  std::stable_sort(order.begin(), order.end(), [](const std::vector<size_t>& a, const std::vector<size_t>& b) {
    size_t x = 0, y = 0;
    for (size_t v : a) x += v;
    for (size_t v : b) y += v;
    return x < y;
  });
  answer.problem = "no interpretation of those tried makes the statement false, as far as Vampire proves";
  /* All of it within a budget: six times the time of the arithmetic
   * theories, thirty seconds by default. */
  auto deadline = std::chrono::steady_clock::now() + std::chrono::milliseconds(600 * (long)options.mathNumbersTime());
  for (size_t tried = 0; tried < MAX_INTERPRETATIONS && tried < order.size(); tried++) {
    if (std::chrono::steady_clock::now() > deadline) { answer.problem += " (within its time)"; break; }
    const std::vector<size_t>& choice = order[tried];
    std::string defines;
    for (size_t i = 0; i < symbols.size(); i++) defines += "define " + symbols[i].name + " " + (*lists[i])[choice[i]].definition + "\n";
    std::string head = "certificate infinite\n" + declarations + statementLine + "\n" + interpret + defines;

    /* The claim, as the checker makes it. */
    const char* why = "";
    char* listing = proof_arithmetic_clauses((head + "clausify forward\nend\n").c_str(), &why);
    std::string claim;
    if (listing) {
      std::string text(listing);
      std::free(listing);
      if (text.compare(0, 6, "claim ") == 0) claim = text.substr(6, text.find('\n') - 6);
    }
    NumberStatement statement = NumberStatement::read("numbers int \n" + claim + "\n");
    if (statement.ok()) {
      /* Vampire's arithmetic first, with the values of the outer "there is". */
      NumberStatement::WitnessProblem outer = statement.outerWitnessProblem();
      int result = 0;
      std::vector<std::vector<std::string>> tuples;
      if (!proveNumbers(outer.tptp.empty() ? statement.tptp(false) : outer.tptp, statement.tptp(true), outer.quantifiers.size(),
                        deciseconds, problemName, run, result, tuples)) return false;
      /* The values to try: Vampire's, if it proved the claim; if it proved
       * neither the claim nor its negation, small ones, each tried with one
       * short search from the laws (for "f(g(x)) = x but not g(f(x)) = x"
       * the arithmetic theories prove nothing in twenty seconds, and the
       * laws with x = 0 in a hundredth of one). */
      bool guessed = false;
      if (result == 0 && !outer.quantifiers.empty() && outer.quantifiers.size() <= 2) {
        guessed = true;
        for (int sum = 0; sum <= 2 * (int)outer.quantifiers.size(); sum++)
          for (int a = 0; a <= 2; a++)
            for (int b = 0; b <= (outer.quantifiers.size() > 1 ? 2 : 0); b++) {
              if (a + b != sum) continue;
              std::vector<std::string> tuple = {std::to_string(a)};
              if (outer.quantifiers.size() > 1) tuple.push_back(std::to_string(b));
              tuples.push_back(tuple);
            }
      }
      if (outer.tptp.empty() && result == 1) tuples.push_back({});
      for (size_t t = 0; t < tuples.size() && t < (guessed ? 9 : MAX_TUPLES); t++) {
        if (std::chrono::steady_clock::now() > deadline) break;
        std::string witnesses;
        bool whole = true;
        for (size_t i = 0; i < tuples[t].size(); i++) {
          whole = whole && tuples[t][i].find('/') == std::string::npos;
          witnesses += "witness " + std::to_string(outer.quantifiers[i]) + " " + tuples[t][i] + "\n";
        }
        if (!whole) continue;
        Recheck recheck;
        if (!certifyBeginning(head + witnesses + "clausify forward\n", problemName, run, recheck, guessed)) return false;
        if (!recheck.certified) { answer.problem = "an interpretation was found, and its proof from the laws of the integers not followed: " + recheck.problem; continue; }
        answer.certified = true;
        answer.certificate = recheck.certificate;
        answer.steps = recheck.steps;
        std::string latex;
        for (const std::string& sort : sorts) latex += (latex.empty() ? "" : ", ") + ("$" + latexName(sort).latex + " = \\mathbb{N}_0$");
        for (size_t i = 0; i < symbols.size(); i++) {
          std::string name = latexName(symbols[i].name).latex, written = (*lists[i])[choice[i]].latex;
          for (size_t at = written.find("%s"); at != std::string::npos; at = written.find("%s", at + name.size()))
            written.replace(at, 2, name);
          latex += ", $" + written + "$";
        }
        answer.interpretation = latex;
        return true;
      }
    }

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
 *   3. A proof is rechecked. First Vampire's own inferences, one by one,
 *      by the independent checker (refuteCheckerClauses()). If they cannot
 *      be followed, the engine, knowing from Vampire that the statement is
 *      a theorem, rebuilds a proof in a form the checker can recheck
 *      (qr_certify_item()). If neither succeeds the theorem stands on
 *      Vampire's proof alone and is reported as not verified.
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
      /* The statement asks for an example and Vampire refuted it: there
       * is none. That is a theorem too ("the condition never holds"), and
       * the checker can follow its proof like any other. */
      Recheck recheck;
      if (!refuteCheckerClauses(item, problemName, run, /* proved */ true, recheck)) return false;
      outcome.reason = italian ? "Vampire ha refutato l'enunciato stesso: nessuna interpretazione lo rende vero."
                               : "Vampire refuted the statement itself: no interpretation makes it true.";
      if (recheck.certified) {
        outcome.status = Status::REFUTATION_CERTIFIED;
        outcome.certificate = recheck.certificate;
        outcome.rechecked = (int)recheck.steps;
        return true;
      }
      outcome.status = Status::COUNTEREXAMPLE_UNVERIFIED;
      outcome.reason += (italian ? " La refutazione non è ricontrollata dal verificatore indipendente: "
                                 : " The refutation is not rechecked by the independent checker: ") + recheck.problem + ".";
      return true;
    }

    /* A theorem, by Vampire. First its own inferences, rechecked one by
     * one by the independent checker. */
    Recheck recheck;
    if (!refuteCheckerClauses(item, problemName, run, /* proved */ true, recheck)) return false;
    if (recheck.certified) {
      outcome.status = Status::THEOREM_CERTIFIED;
      outcome.certificate = recheck.certificate;
      outcome.rechecked = (int)recheck.steps;
      if (!answer.goalUsed)
        outcome.reason = italian ? "Le ipotesi sono contraddittorie da sole: la tesi non è stata usata."
                                 : "The hypotheses are contradictory by themselves: the claim was not used.";
      return true;
    }

    if (engineSaid) {
      /* The engine went first and could not prove it: there is no proof of
       * its own to rebuild. The theorem stands on Vampire's proof. */
      outcome.status = Status::THEOREM_UNVERIFIED;
      outcome.reason = italian ? "Il motore matematico non aveva né una dimostrazione né un controesempio; Vampire ha dimostrato l'enunciato"
                               : "The mathematical engine had neither a proof nor a counterexample; Vampire proved the statement";
      /* From what: the laws of the sets of parts and of maps, and, for two
       * sets supposed equipotent, the bijection as two maps (LogicStatement.hpp). */
      if (!statement.laws().empty())
        outcome.reason += italian ? " dalle leggi degli insiemi di parti e di applicazioni che il motore gli ha dato"
                                  : " from the laws of the sets of parts and of maps that the engine gave it";
      if (statement.bijections())
        outcome.reason += italian ? ", con ogni biiezione supposta data come due applicazioni inverse l'una dell'altra"
                                  : ", with each supposed bijection given as two maps inverse to each other";
      outcome.reason += italian ? ". La prova non è ricontrollata dal verificatore indipendente."
                                : ". The proof is not rechecked by the independent checker.";
      outcome.reason += (italian ? " Il ricontrollo delle inferenze di Vampire si è fermato: " : " The recheck of Vampire's inferences stopped: ") + recheck.problem + ".";
      if (!answer.goalUsed)
        outcome.reason += italian ? " Le ipotesi sono contraddittorie da sole: la tesi non è stata usata."
                                  : " The hypotheses are contradictory by themselves: the claim was not used.";
      return true;
    }

    /* Vampire's inferences could not be followed by the checker. The
     * engine, knowing that the statement is a theorem, writes a proof of
     * its own that the checker can recheck. */
    EngineVerdict rebuilt = keep(qr_certify_item(begin, end));
    if (rebuilt.outcome == QR_PROVED && certifiedIndependently(rebuilt)) {
      outcome.status = Status::THEOREM_CERTIFIED;
      outcome.notRechecked = recheck.problem;
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
        + (rebuilt.reason.empty() ? rebuilt.line : rebuilt.reason) + ")."
        + (italian ? " Il ricontrollo delle inferenze di Vampire si è fermato: " : " The recheck of Vampire's inferences stopped: ") + recheck.problem + ".";
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
    /* Saturation without a contradiction, and no finite model that could
     * be confirmed: perhaps an infinite one over the integers, which the
     * checker certifies (certifyInfinite()). For a request for an example
     * the checker's statement is "not E", and an interpretation where it
     * fails is an example of E. */
    InfiniteAnswer infinite;
    if (!certifyInfinite(item, problemName, run, infinite)) return false;
    if (infinite.certified) {
      bool example = statement.wantsExample();
      outcome.status = example ? Status::THEOREM_CERTIFIED : Status::COUNTEREXAMPLE_VERIFIED;
      outcome.certificate = infinite.certificate;
      outcome.byInfinite = true;
      outcome.detail = infinite.interpretation;
      outcome.reason = italian
        ? std::string("La ricerca di Vampire è finita senza contraddizione e senza un modello finito. ")
          + (example ? "L'enunciato vale" : "L'enunciato è falso") + " in un'interpretazione infinita sugli interi (" + infinite.interpretation
          + "): Vampire lo ha dimostrato dalle leggi degli interi, e il verificatore indipendente ha seguito la dimostrazione ("
          + std::to_string(infinite.steps) + " passi)."
        : std::string("Vampire's search ended without a contradiction and without a finite model. The statement ")
          + (example ? "holds" : "is false") + " in an infinite interpretation over the integers (" + infinite.interpretation
          + "): Vampire proved it from the laws of the integers, and the independent checker followed the proof ("
          + std::to_string(infinite.steps) + " steps).";
      outcome.proof = std::string(example ? (italian ? "\\textbf{Dimostrazione.} Un esempio, infinito: " : "\\textbf{Proof.} An example, infinite: ")
                                          : (italian ? "\\textbf{L'enunciato \\`e falso.} Un controesempio infinito: " : "\\textbf{The statement is false.} An infinite counterexample: "))
        + infinite.interpretation
        + (italian ? ". Che lo sia lo ha dimostrato Vampire dalle leggi degli interi, e il verificatore indipendente ne ha seguito i "
                   : ". That it is one Vampire proved from the laws of the integers, and the independent checker followed the ")
        + std::to_string(infinite.steps) + (italian ? " passi." : " steps.") + (example ? " $\\Box$" : "");
      return true;
    }
    outcome.status = statement.wantsExample() ? Status::THEOREM_UNVERIFIED : Status::COUNTEREXAMPLE_UNVERIFIED;
    outcome.reason = italian
      ? "La ricerca di Vampire è finita senza contraddizione, il che per una strategia completa vuol dire che c'è un'interpretazione che soddisfa le formule date; "
        "non è stato prodotto un modello finito che il motore matematico potesse ricalcolare."
      : "Vampire's search ended without a contradiction, which for a complete strategy means that some interpretation satisfies the given formulas; "
        "no finite model was produced for the mathematical engine to recompute.";
    outcome.reason += (italian ? " Interpretazioni infinite sugli interi: " : " Infinite interpretations over the integers: ") + infinite.problem + ".";
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
      /* Vampire's inferences rechecked: the account, and what the checker did. */
      if (outcome.rechecked >= 0) {
        page = outcome.account + (outcome.account.empty() ? "" : "\n") + verification
             + (italian ? " Il verificatore indipendente ha ricontrollato, uno per uno, i " + std::to_string(outcome.rechecked)
                          + " passi di una refutazione trovata da Vampire sulle clausole che il verificatore stesso ricava dall'enunciato."
                        : " The independent checker rechecked, one by one, the " + std::to_string(outcome.rechecked)
                          + " steps of a refutation found by Vampire on the clauses that the checker itself builds from the statement.");
        if (!outcome.reason.empty()) page += " " + outcome.reason;
        qr_document_external_item(begin, end, QR_PROVED, "da Vampire, con le inferenze ricontrollate dal verificatore", nullptr, nullptr, page.c_str(), certificate);
        return;
      }

      /* Vampire's account, if there is one (a theorem by example has none),
       * then the proof the checker accepted, as the engine wrote it. */
      if (!outcome.account.empty())
        page = outcome.account + "\n" + verification
             + (italian ? " Il motore matematico ha riscritto la dimostrazione nella forma che il verificatore indipendente ha accettato:\n\n{\\small "
                        : " The mathematical engine rebuilt the proof in the form that the independent checker accepted:\n\n{\\small ")
             + outcome.proof + "\\par}";
      else
        page = outcome.proof;
      qr_document_external_item(begin, end, QR_PROVED, outcome.byCount ? "con il conto completo del verificatore"
                                                       : outcome.byInfinite ? "da Vampire, con un esempio infinito sugli interi seguito dal verificatore"
                                                       : outcome.byNumbers ? "da Vampire, con i numeri ricalcolati dal verificatore"
                                                                           : "da Vampire, con la prova riscritta dal motore",
                                nullptr, nullptr, page.c_str(), certificate);
      return;

    case Status::COUNTEREXAMPLE_VERIFIED:
      qr_document_external_item(begin, end, QR_REFUTED, nullptr, nullptr, outcome.detail.c_str(), outcome.proof.c_str(), certificate);
      return;

    case Status::REFUTATION_CERTIFIED:
      /* No example exists: Vampire's account, and what the checker did. */
      page = outcome.account + (outcome.account.empty() ? "" : "\n") + verification + " " + outcome.reason
           + (italian ? " Il verificatore indipendente ha ricontrollato, uno per uno, i " + std::to_string(outcome.rechecked)
                        + " passi di una refutazione trovata da Vampire sulle clausole che il verificatore stesso ricava dalla condizione: non c'\\`e nessun esempio."
                      : " The independent checker rechecked, one by one, the " + std::to_string(outcome.rechecked)
                        + " steps of a refutation found by Vampire on the clauses that the checker itself builds from the condition: there is no example.");
      qr_document_external_item(begin, end, QR_REFUTED, nullptr, nullptr, nullptr, page.c_str(), certificate);
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

    /* Reports what was established about a statement of logic: the status,
     * who confirmed it and how, the counterexample, the account of the
     * proof, the certificate, the page of the document. */
    auto reportLogic = [&](const LogicOutcome& outcome) {
      Status status = outcome.status;
      addCommentSignForSZS(std::cout) << "Verification status: " << statusName(status, run.language)
                                      << " [" << statusCode(status) << "]" << std::endl;
      if (!outcome.reason.empty()) addCommentSignForSZS(std::cout) << outcome.reason << std::endl;
      if (outcome.rechecked >= 0)
        addCommentSignForSZS(std::cout) << "Vampire's inferences rechecked by the independent checker: " << outcome.rechecked << " steps" << std::endl;
      if (!outcome.notRechecked.empty())
        addCommentSignForSZS(std::cout) << "Vampire's inferences were not rechecked (" << outcome.notRechecked
                                        << "); the certificate is of the proof rebuilt by the engine" << std::endl;
      if (!outcome.engineLine.empty()) addCommentSignForSZS(std::cout) << "Engine verdict: " << outcome.engineLine << std::endl;
      if (!outcome.detail.empty()) addCommentSignForSZS(std::cout) << "Counterexample (LaTeX): " << outcome.detail << std::endl;
      if (run.printAccount && !outcome.account.empty()) {
        addCommentSignForSZS(std::cout) << "Explanation (LaTeX) start" << std::endl;
        std::cout << outcome.account;
        addCommentSignForSZS(std::cout) << "Explanation (LaTeX) end" << std::endl;
      }
      if (!outcome.certificate.empty() && run.certificates.is_open()) run.certificates << outcome.certificate << "\n";
      if (run.document) documentLogicItem(item, outcome, run.language);
    };

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
      bool refuted = outcome.status == Status::COUNTEREXAMPLE_VERIFIED || outcome.status == Status::COUNTEREXAMPLE_UNVERIFIED
                  || outcome.status == Status::REFUTATION_CERTIFIED;
      if (statement.conditional && refuted) {
        outcome = LogicOutcome();
        outcome.reason = run.language == Language::ITALIAN
          ? "in generale non vale, ma dopo la formula c'è una condizione che il programma non sa leggere"
          : "it does not hold in general, but after the formula there is a condition that the program cannot read";
      }
      status = outcome.status;

      reportLogic(outcome);
    } else {
      /* Mathematics proper, or logic that has no first-order translation:
       * the engine decided it, and its verdict is reported in its own
       * words. (A copy: the engine's strings last until it is asked again.) */
      EngineVerdict verdict = keep(statement.verdict);
      status = engineStatus(statement.verdict);
      decidedBy = "engine";

      /* Logic with no first-order form of its own, a quantifier over the
       * parts of a set, that the engine neither proved nor refuted: Vampire
       * looks for a refutation of the clauses of the independent checker,
       * which are first-order. Found and followed by the checker, it is a
       * certified theorem (or, for a statement that wants an example, the
       * certified proof that there is none). */
      Recheck onClauses;
      ArithmeticAnswer arithmetic;
      CountAnswer count;
      bool undecided = statement.verdict.outcome == QR_NOT_PROVED || statement.verdict.outcome == QR_UNSUPPORTED;
      bool uncertified = (statement.verdict.outcome == QR_PROVED || statement.verdict.outcome == QR_REFUTED) && !statement.verdict.certified;
      bool conditional = statement.verdict.conditional != 0;
      /* Asking for the checker's clauses enters the engine again, and it
       * forgets what it kept of this verdict for the document:
       * restoreVerdict() decides the statement once more where the
       * document needs the engine's page. */
      auto restoreVerdict = [&]() {
        if (statement.clausesOnly && run.document) qr_decide_item(item.text.c_str(), item.text.c_str() + item.text.size(), /* delegate_logic */ 0);
      };
      if (statement.clausesOnly) {
        if (!refuteCheckerClauses(item, problemName, run, /* proved */ false, onClauses)) return std::nullopt;
      } else if ((undecided || uncertified) && statement.notTranslated.empty()) {
        /* A statement in one integer variable: the independent checker
         * settles it by itself (countByChecker()). For a statement the
         * engine decided without a certificate that is the certificate;
         * for one it did not decide, it is the answer. A statement found
         * false only where a condition nobody read may exclude it is not
         * reported false (the caution of the engine, below). */
        countByChecker(statement.numbers, count);
        if (count.certified && count.denied && conditional) count.certified = false;
      }
      if (undecided && !count.certified && !statement.clausesOnly && statement.notTranslated.empty()) {
        /* Mathematics that the engine neither proved nor refuted, or read
         * and had no method for: if it is a statement with quantifiers
         * over numbers of one kind, Vampire's arithmetic theories are
         * asked (askArithmetic()). What the engine could not read is not
         * handed over, so nothing is asked of it. */
        if (!askArithmetic(statement.numbers, problemName, run, arithmetic)) return std::nullopt;

        /* The caution of the engine: after the formula there was a
         * condition nobody read, and the statement may be false only in
         * the cases it excludes. A proof holds whatever the condition. */
        if (arithmetic.found && arithmetic.denied && conditional) arithmetic.found = false;
      }
      bool agrees = count.certified && uncertified && count.denied == (statement.verdict.outcome == QR_REFUTED);
      if (count.certified && undecided) {
        /* The checker's count is the answer. */
        bool italian = run.language == Language::ITALIAN;
        LogicOutcome outcome;
        outcome.status = count.denied ? Status::COUNTEREXAMPLE_VERIFIED : Status::THEOREM_CERTIFIED;
        outcome.reason = italian
          ? "Il motore matematico non aveva né una dimostrazione né una confutazione. L'enunciato ha una sola variabile intera: il verificatore indipendente lo ha stabilito da sé, provando tutti gli interi che contano."
          : "The mathematical engine had neither a proof nor a refutation. The statement has one integer variable: the independent checker settled it by itself, trying every integer that can matter.";
        outcome.certificate = count.certificate;
        outcome.byCount = true;
        outcome.proof = std::string(count.denied ? (italian ? "\\textbf{L'enunciato \\`e falso.} " : "\\textbf{The statement is false.} ")
                                                 : (italian ? "\\textbf{Dimostrazione.} " : "\\textbf{Proof.} "))
          + (italian ? "Una sola variabile intera: oltre il limite delle radici dei polinomi che vi compaiono ogni confronto ha un valore fisso, e ogni divisibilit\\`a si ripete con il suo periodo; il verificatore indipendente ha provato tutti gli interi fino a l\\`i."
                     : "One integer variable: beyond the bound of the roots of the polynomials in it every comparison has a fixed value, and every divisibility repeats with its period; the independent checker tried every integer up to there.")
          + (count.denied ? "" : " $\\Box$");
        status = outcome.status;
        decidedBy = "checker";
        addCommentSignForSZS(std::cout) << "SZS status " << statusSZS(status) << " for " << problemName << std::endl;
        reportLogic(outcome);
      } else if (arithmetic.found) {
        bool italian = run.language == Language::ITALIAN;
        LogicOutcome outcome;
        outcome.status = arithmetic.certified ? (arithmetic.denied ? Status::COUNTEREXAMPLE_VERIFIED : Status::THEOREM_CERTIFIED)
                                              : (arithmetic.denied ? Status::COUNTEREXAMPLE_UNVERIFIED : Status::THEOREM_UNVERIFIED);
        outcome.reason = italian
          ? "Il motore matematico non aveva né una dimostrazione né una confutazione; l'enunciato è stato dato alle teorie aritmetiche di Vampire come problema su " + arithmetic.sort + ", e Vampire ha dimostrato "
            + (arithmetic.denied ? "la sua negazione" : "l'enunciato")
          : "The mathematical engine had neither a proof nor a refutation; the statement was given to Vampire's arithmetic theories as a problem over " + arithmetic.sort + ", and Vampire proved "
            + (arithmetic.denied ? "its negation" : "the statement");
        if (arithmetic.byLaws) {
          /* From the laws of the integers: the checker followed Vampire's refutation of its clauses. */
          outcome.reason += italian
            ? ". Vampire ha poi refutato, senza teorie, le clausole che il verificatore indipendente ricava dall'enunciato con le leggi degli interi, e il verificatore ha seguito la refutazione passo per passo."
            : ". Vampire then refuted, with no theory, the clauses that the independent checker builds from the statement with the laws of the integers, and the checker followed the refutation step by step.";
          outcome.certificate = arithmetic.certificate;
          outcome.rechecked = (int)arithmetic.steps;
          if (arithmetic.denied)
            outcome.proof = (italian ? "\\textbf{L'enunciato \\`e falso.} Vampire ha dimostrato la negazione dalle leggi degli interi, e il verificatore indipendente ne ha seguito, uno per uno, i "
                                     : "\\textbf{The statement is false.} Vampire proved its negation from the laws of the integers, and the independent checker followed, one by one, the ")
              + std::to_string(arithmetic.steps) + (italian ? " passi." : " steps.");
        } else if (arithmetic.certified) {
          /* With the numbers: the checker has recomputed the statement on them. */
          std::string with = arithmetic.numbers.empty() ? "" : (italian ? " (" : " (") + arithmetic.numbers + ")";
          /* A quantifier over one integer that no number shows: the checker settled it by its complete count. */
          std::string count = !arithmetic.counted ? ""
            : italian ? ", e ha stabilito il quantificatore che resta, su un solo intero, provando tutti gli interi che contano"
                      : ", and settled the quantifier that is left, over one integer, by trying every integer that can matter";
          outcome.reason += italian
            ? ", con i numeri che lo mostrano" + with + ". Il verificatore indipendente ha ricalcolato l'enunciato su quei numeri" + count + "."
            : ", with the numbers that show it" + with + ". The independent checker recomputed the statement on those numbers" + count + ".";
          outcome.certificate = arithmetic.certificate;
          outcome.byNumbers = true;
          if (arithmetic.denied) outcome.detail = arithmetic.numbers;
          outcome.proof = (arithmetic.denied
              ? (italian ? "\\textbf{L'enunciato \\`e falso.} Un controesempio: " : "\\textbf{The statement is false.} A counterexample: ")
              : (italian ? "\\textbf{Dimostrazione.} Un esempio: " : "\\textbf{Proof.} An example: "))
            + (arithmetic.numbers.empty() ? (italian ? "il conto diretto" : "the direct computation") : arithmetic.numbers)
            + (italian ? ". I numeri sono stati trovati dalle teorie aritmetiche di Vampire, e il verificatore indipendente ha ricalcolato l'enunciato su di essi" + count + "."
                       : ". The numbers were found by Vampire's arithmetic theories, and the independent checker recomputed the statement on them" + count + ".")
            + (arithmetic.denied ? "" : " $\\Box$");
        } else {
          outcome.reason += italian ? ". La prova non è ricontrollata dal verificatore indipendente."
                                    : ". The proof is not rechecked by the independent checker.";
          if (!arithmetic.lawsProblem.empty())
            outcome.reason += (italian ? " Dalle leggi degli interi: " : " From the laws of the integers: ") + arithmetic.lawsProblem + ".";
        }
        status = outcome.status;
        decidedBy = "vampire";
        reportLogic(outcome);
      } else if (onClauses.certified) {
        bool italian = run.language == Language::ITALIAN;
        LogicOutcome outcome;
        outcome.status = statement.wantsExample ? Status::REFUTATION_CERTIFIED : Status::THEOREM_CERTIFIED;
        outcome.certificate = onClauses.certificate;
        outcome.rechecked = (int)onClauses.steps;
        outcome.reason = italian
          ? "Il motore matematico non aveva né una dimostrazione né un controesempio; Vampire ha refutato le clausole che il verificatore indipendente ricava dall'enunciato."
          : "The mathematical engine had neither a proof nor a counterexample; Vampire refuted the clauses that the independent checker builds from the statement.";
        if (statement.wantsExample)
          outcome.reason += italian ? " Nessuna interpretazione rende vero l'enunciato." : " No interpretation makes the statement true.";
        status = outcome.status;
        decidedBy = "vampire";
        addCommentSignForSZS(std::cout) << "SZS status " << statusSZS(status) << " for " << problemName << std::endl;
        reportLogic(outcome);
      } else {
        /* The engine's verdict stands. If the checker's count agrees with
         * a verdict that had no certificate, that is its certificate; if
         * it says the opposite, the engine was wrong, and nothing is
         * claimed of the statement. */
        if (agrees) status = count.denied ? Status::COUNTEREXAMPLE_VERIFIED : Status::THEOREM_CERTIFIED;
        else if (count.certified && uncertified) status = Status::UNSOLVED;
        addCommentSignForSZS(std::cout) << "SZS status " << statusSZS(status) << " for " << problemName << std::endl;
        addCommentSignForSZS(std::cout) << "Verification status: " << statusName(status, run.language)
                                        << " [" << statusCode(status) << "]" << std::endl;
        if (!verdict.line.empty()) addCommentSignForSZS(std::cout) << "Engine verdict: " << verdict.line << std::endl;
        if (agrees) {
          addCommentSignForSZS(std::cout) << "The engine's verdict had no certificate. The statement has one integer variable, and the independent"
                                             " checker settled it by itself the same way, trying every integer that can matter" << std::endl;
          if (run.certificates.is_open()) run.certificates << count.certificate << "\n";
        } else if (count.certified && uncertified) {
          addCommentSignForSZS(std::cout) << "WARNING: the independent checker's count over the one integer variable of the statement says the opposite"
                                             " of the engine's verdict; nothing is claimed of the statement" << std::endl;
        }
        if (!statement.notTranslated.empty())
          addCommentSignForSZS(std::cout) << "Not given to Vampire as a first-order problem: " << statement.notTranslated << std::endl;
        if (statement.clausesOnly)
          addCommentSignForSZS(std::cout) << "Vampire, asked for a refutation of the checker's clauses: " << onClauses.problem << std::endl;
        if (arithmetic.asked)
          addCommentSignForSZS(std::cout) << "Vampire's arithmetic theories, asked too (a problem over " << arithmetic.sort
                                          << "), proved neither the statement nor its negation" << std::endl;
        if (!verdict.certificate.empty() && run.certificates.is_open()) run.certificates << verdict.certificate << "\n";
        restoreVerdict();
        if (run.document) qr_document_item(item.text.c_str(), item.text.c_str() + item.text.size());
      }
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
