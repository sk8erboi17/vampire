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
 * @file Driver.hpp
 * Runs Vampire on LaTeX input: one statement after the other.
 *
 * A TPTP file is one problem, and Vampire is built for one problem per
 * process. A LaTeX document is a list of statements, each a problem of its
 * own and each going where it belongs (Parse/LaTeX.hpp):
 *
 *   - mathematics proper is decided here, in this process, by the
 *     mathematical engine;
 *   - a statement of first-order logic gets a child process, which loads
 *     the translated problem and then IS Vampire on that problem, in
 *     whatever mode and with whatever options the user chose. This is how
 *     Vampire's own portfolio mode runs its strategies, and it is why
 *     nothing in the prover had to learn about documents.
 *
 * THE DEFAULT PLAN FOR A STATEMENT OF LOGIC. Two searches, both Vampire's:
 * one for a finite model that refutes the statement (for at most
 * math_model_time), and the proof search. A false statement usually has a
 * small counter-model, which the independent checker can confirm, while a
 * saturation prover may run forever on it or stop without a model to show.
 * With a single strategy the two run together and the first answer that
 * settles the statement ends the other; before a portfolio the model
 * search goes first (see decideWithVampire() in Driver.cpp).
 *
 * For every statement the driver reports the SZS status, the verification
 * status (Math/Verification.hpp) and a line "% Result N: Code"; at the end a
 * summary. It also feeds the final document and the file of certificates.
 */

#ifndef __Math_Driver__
#define __Math_Driver__

#include <optional>

namespace Math {

class Driver {
public:
  /** True if the input of this run is LaTeX: asked for with input_syntax, or a ".tex" file with input_syntax auto. */
  static bool wanted();

  /**
   * Runs all the statements of the input.
   *
   * In the process that was started by the user it returns the exit code:
   * 0 if every statement was proved or solved, 1 otherwise.
   *
   * In a child process created for a statement of logic it returns nothing:
   * the problem is loaded (UIHelper::getInputProblem() will give it) and
   * the caller must go on exactly as after parsing a TPTP file.
   */
  static std::optional<int> run();
};

} // namespace Math

#endif // __Math_Driver__
