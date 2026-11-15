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
 * @file LogicProblem.hpp
 * The statement Vampire is working on, when it came from the LaTeX frontend.
 *
 * Vampire's proving code does not know where a problem comes from, and
 * should not. But two things must happen when the problem was a statement
 * read from LaTeX, in whatever mode and process Vampire finds its answer:
 *
 *   - a finite model must go to the independent checker before anybody
 *     calls it a counterexample (onFiniteModel());
 *   - the answer must be reported with its verification status, and told
 *     to whoever is collecting the statements of a document (onRefutation(),
 *     onSatisfiable()).
 *
 * LogicProblem is the place for both: one object per process, installed by
 * the frontend before the search starts, and consulted by three one-line
 * hooks (in FMB/FiniteModelBuilder.cpp and Shell/UIHelper.cpp). With TPTP or
 * SMT-LIB input nothing is installed, current() is null, and the hooks do
 * nothing: Vampire behaves exactly as before.
 *
 * A process forked after install() inherits the object, which is how the
 * strategies of a portfolio report through it.
 */

#ifndef __Math_LogicProblem__
#define __Math_LogicProblem__

#include <memory>
#include <ostream>
#include <string>
#include <vector>

#include "Forwards.hpp"

#include "LogicStatement.hpp"
#include "LogicTranslator.hpp"
#include "Verification.hpp"

namespace FMB { class FiniteModelMultiSorted; }

namespace Math {

/**
 * What the search established about one statement of logic, as the process
 * that found it tells the one that asked. Strings are empty when missing.
 */
struct LogicResult {
  bool decided = false;     // false: the search ended without an answer
  bool byRefutation = false;// the answer rests on a refutation (a proof), not on a model or on saturation
  Status status = Status::UNSOLVED;
  std::string reason;       // why the status is not a certified one, for a reader
  std::string detail;       // a counterexample or an example, as LaTeX text
  std::string proof;        // the account of the proof, as LaTeX text
  std::string certificate;  // the certificate the independent checker accepted

  /** Writes the result to the file path, whole or not at all (through a temporary name). */
  void write(const std::string& path) const;
  /** Reads a result written by write(). Returns false, leaving result alone, if there is none. */
  static bool read(const std::string& path, LogicResult& result);
};

class LogicProblem {
public:
  struct Settings {
    Language language = Language::ENGLISH;
    bool explain = true;        // write the account of a proof
    bool printAccount = false;  // also print that account on the output, after the proof
    std::string resultPath;     // where to write the LogicResult, or empty
  };

  /** The statement of this process, or null if the input was not LaTeX. */
  static LogicProblem* current() { return _current.get(); }

  /**
   * Makes statement the problem of this process and returns its units, to
   * be handed to Vampire. The statement must be first-order over plain
   * sorts (statement.outside() is empty).
   */
  static Kernel::UnitList* install(LogicStatement statement, const Settings& settings);

  bool hasConjecture() const { return _translator->hasConjecture(); }

  /**
   * Called by the finite model builder with the model it found. Rewrites
   * the model as a certificate and has the independent checker recompute
   * the statement in it; the outcome is reported by onSatisfiable().
   */
  void onFiniteModel(FMB::FiniteModelMultiSorted& model);

  /**
   * Called by the finite model builder when preprocessing removed every
   * clause: the problem is satisfiable, but Vampire builds no model then.
   * Proposes the smallest one to the checker, as onFiniteModel() does.
   */
  void onNoClauses();

  /** Called where Vampire reports a refutation: adds the verification status to out and records the result. */
  void onRefutation(std::ostream& out, Kernel::Unit* refutation);

  /** Called where Vampire reports satisfiability, with or without a model: as onRefutation(). */
  void onSatisfiable(std::ostream& out);

private:
  static std::unique_ptr<LogicProblem> _current;

  LogicProblem(LogicStatement statement, const Settings& settings);

  LogicStatement _statement;
  std::unique_ptr<LogicTranslator> _translator;
  Settings _settings;

  /* The model handed in by onFiniteModel(), if any. */
  bool _hasModel = false;
  std::string _modelCertificate;  // non-empty only if the checker accepted it
  std::string _modelProblem;      // why the model is not confirmed
  std::string _modelText;         // the model for a reader, LaTeX

  std::string describeModel(const std::vector<unsigned>& sizes, const std::vector<std::vector<unsigned>>& tables) const;
  void report(std::ostream& out, const LogicResult& result) const;
};

} // namespace Math

#endif // __Math_LogicProblem__
