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
 * The statement Vampire is working on, when it came from the LaTeX frontend,
 * and what Vampire found about it.
 *
 * Vampire's proving code does not know where a problem comes from, and
 * should not. But when the problem is a statement read from LaTeX, what
 * Vampire finds is not the end of the story: a finite model goes back to
 * the mathematical engine, which judges it as it judges its own, and a
 * refutation goes back to be rebuilt as a proof the independent checker can
 * recheck (Math/Driver.cpp). For that, the process in which Vampire finds
 * its answer, whatever mode it runs in, has to say WHAT it found, as data.
 *
 * LogicProblem is the place for it: one object per process, installed by
 * the frontend before the search starts, and consulted by a few one-line
 * hooks (in FMB/FiniteModelBuilder.cpp and Shell/UIHelper.cpp). It records a
 * VampireAnswer and writes it where the process that asked will read it.
 * It decides nothing and calls nothing verified. With TPTP or SMT-LIB input
 * nothing is installed, current() is null, and the hooks do nothing: Vampire
 * behaves exactly as before.
 *
 * A process forked after install() inherits the object, which is how the
 * strategies of a portfolio answer through it.
 */

#ifndef __Math_LogicProblem__
#define __Math_LogicProblem__

#include <cstddef>
#include <memory>
#include <string>
#include <vector>

#include "Forwards.hpp"

#include "LogicStatement.hpp"
#include "LogicTranslator.hpp"
#include "Verification.hpp"

namespace FMB { class FiniteModelMultiSorted; }

namespace Math {

/**
 * What Vampire found about one statement of logic: data for whoever asked,
 * not a verdict. Nothing in it has been checked by anybody else yet.
 */
struct VampireAnswer {
  enum class Kind {
    NONE,        // the search ended without an answer
    REFUTATION,  // a refutation: a proof of the statement (or, for a statement that wants an example, that there is none)
    MODEL,       // a finite model: sizes and tables
    SATURATED    // saturation without a contradiction and without a model to show
  };
  Kind kind = Kind::NONE;

  /* REFUTATION */
  bool goalUsed = true;   // false if the refutation does not use the claim: the hypotheses are contradictory
  std::string account;    // the account of the refutation, as LaTeX text; empty if none was asked for

  /* MODEL: in the order of the statement, one size per sort and one table
   * per symbol; a table has a cell for every choice of the arguments, the
   * first changing fastest, holding the number of an element from 0, or 1
   * and 0 for true and false (the layout of QrModel in Engine.h). */
  bool proposed = false;  // not found by the model builder: the smallest candidate, when preprocessing left no clause
  std::vector<size_t> sizes;
  std::vector<std::vector<size_t>> tables;

  /** Writes the answer to the file path, whole or not at all (through a temporary name). */
  void write(const std::string& path) const;
  /** Reads an answer written by write(). Returns false, leaving answer alone, if there is none. */
  static bool read(const std::string& path, VampireAnswer& answer);
};

class LogicProblem {
public:
  struct Settings {
    Language language = Language::ENGLISH;
    bool explain = true;      // write the account of a refutation
    std::string answerPath;   // where to write the VampireAnswer, or empty
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

  /** Called by the finite model builder with the model it found: reads it as sizes and tables of the statement. */
  void onFiniteModel(FMB::FiniteModelMultiSorted& model);

  /**
   * Called by the finite model builder when preprocessing removed every
   * clause: the problem is satisfiable, but Vampire builds no model then.
   * Proposes the smallest one, read as onFiniteModel() reads a model.
   */
  void onNoClauses();

  /** Called where Vampire reports a refutation: records it, with its account. */
  void onRefutation(Kernel::Unit* refutation);

  /** Called where Vampire reports satisfiability, with or without a model. */
  void onSatisfiable();

private:
  static std::unique_ptr<LogicProblem> _current;

  LogicProblem(LogicStatement statement, const Settings& settings);

  LogicStatement _statement;
  std::unique_ptr<LogicTranslator> _translator;
  Settings _settings;
  VampireAnswer _answer;

  void send() const;
};

} // namespace Math

#endif // __Math_LogicProblem__
