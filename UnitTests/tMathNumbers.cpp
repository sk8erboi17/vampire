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
 * @file tMathNumbers.cpp
 * Unit tests of the path of a statement with quantifiers over numbers from
 * the mathematical engine to Vampire's arithmetic theories: what the engine
 * hands over and what it keeps (Math/Engine.h, qr_numbers_item()), and the
 * TPTP problem written from it (Math/NumberStatement).
 *
 * The rule the tests defend: the problem says exactly what the statement
 * says, and a statement that cannot be said exactly is not handed over.
 */

#include <string>

#include "Math/Engine.h"
#include "Math/NumberStatement.hpp"
#include "Test/UnitTesting.hpp"

using namespace Math;

static std::string asItem(const std::string& formula)
{
  return "$\\displaystyle " + formula + "$";
}

/** What the engine hands over for the formula, or "" if it keeps the statement. */
static std::string handedOver(const std::string& formula)
{
  std::string item = asItem(formula);
  QrVerdict verdict = qr_numbers_item(item.c_str(), item.c_str() + item.size());
  ASS(verdict.outcome == QR_LOGIC);
  return verdict.logic ? verdict.logic : "";
}

TEST_FUN(a_statement_on_integers_is_handed_over_with_its_sets)
{
  qr_init();

  /* N starts from 1, N_0 from 0, Z has no bound; a point removed is a condition. */
  std::string text = handedOver("\\forall a \\in \\mathbb{Z}\\ \\forall n \\in \\mathbb{N}\\ \\exists m \\in \\mathbb{N}_{0}\\ (a + n \\neq m \\lor a \\le 0)");
  ASS(text.compare(0, 13, "numbers int \n") == 0);
  ASS(text.find("(set ge 1)") != std::string::npos);
  ASS(text.find("(set ge 0)") != std::string::npos);
  ASS(text.find("(set)") != std::string::npos);

  NumberStatement statement = NumberStatement::read(text);
  ASS(statement.ok());
  ASS_EQ(statement.sort(), "$int");
  std::string problem = statement.tptp(false);
  ASS(problem.compare(0, 27, "tff(statement, conjecture, ") == 0);
  ASS(problem.find(":$int]: ($greatereq(") != std::string::npos);   // a bound guards its quantifier
  ASS(problem.find(" => ") != std::string::npos);                    // "for every" with an implication
  ASS(problem.find(" & ") != std::string::npos);                     // "there is" with a conjunction
  ASS(problem.find("$rat") == std::string::npos && problem.find("$real") == std::string::npos);

  /* The negation is the same formula, denied. */
  std::string denied = statement.tptp(true);
  ASS(denied.compare(0, 29, "tff(statement, conjecture, ~(") == 0);
}

TEST_FUN(divisibility_is_the_second_being_the_first_times_an_integer)
{
  qr_init();
  std::string text = handedOver("\\forall a, b \\in \\mathbb{Z} \\setminus \\{0\\}\\ (a \\mid b \\implies a \\mid 2b)");
  ASS(text.find("(divides ") != std::string::npos);
  ASS(text.find("except 0/1") != std::string::npos);
  NumberStatement statement = NumberStatement::read(text);
  ASS(statement.ok());
  std::string problem = statement.tptp(false);
  ASS(problem.find("(?[K0:$int]: (") != std::string::npos);
  ASS(problem.find(" = $product(") != std::string::npos);
  ASS(problem.find(" != 0)") != std::string::npos);
}

TEST_FUN(rationals_and_reals_have_their_own_sort_and_numerals)
{
  qr_init();
  NumberStatement rationals = NumberStatement::read(handedOver("\\forall x \\in \\mathbb{Q}^{+}\\ \\exists y \\in \\mathbb{Q}\\ (2y = x)"));
  ASS(rationals.ok());
  ASS_EQ(rationals.sort(), "$rat");
  ASS(rationals.tptp(false).find("$greater(X") != std::string::npos);
  ASS(rationals.tptp(false).find("2/1") != std::string::npos);

  NumberStatement reals = NumberStatement::read(handedOver("\\forall x \\in \\mathbb{R}\\ (x^{2} \\ge 0)"));
  ASS(reals.ok());
  ASS_EQ(reals.sort(), "$real");
  ASS(reals.tptp(false).find("$product(X") != std::string::npos);   // a written power is a product
  ASS(reals.tptp(false).find("0.0") != std::string::npos);
}

TEST_FUN(what_cannot_be_said_exactly_is_not_handed_over)
{
  qr_init();

  /* Variables of different kinds: a number would have to be moved from one sort to another. */
  ASS(handedOver("\\forall x \\in \\mathbb{Q}\\ \\exists n \\in \\mathbb{Z}\\ (n \\le x)").empty());
  /* An exponent that is a letter, a division by an expression, a function, a root. */
  ASS(handedOver("\\forall a \\in \\mathbb{Z}\\ \\forall m, n \\in \\mathbb{N}\\ \\exists p \\in \\mathbb{N}\\ (a^{m} a^{n} = a^{p})").empty());
  ASS(handedOver("\\forall x \\in \\mathbb{Q}^{+}\\ (\\frac{1}{x} > 0)").empty());
  ASS(handedOver("\\forall x \\in \\mathbb{R}\\ (\\sin x \\le 1)").empty());
  ASS(handedOver("\\forall x \\in \\mathbb{R}^{+}\\ (\\sqrt{x} \\ge 0)").empty());
  /* A division among integers is not an integer. */
  ASS(handedOver("\\forall n \\in \\mathbb{Z}\\ (\\frac{n}{2} \\le n \\lor n < 0)").empty());
  /* A declared map, a request for solutions, membership in a set of another kind. */
  ASS(handedOver("(f \\colon \\mathbb{Z} \\to \\mathbb{Z} \\land \\forall n \\in \\mathbb{Z}\\ (f(n) = n + 1)) \\implies \\forall a, b \\in \\mathbb{Z}\\ (f(a) = f(b) \\implies a = b)").empty());
  ASS(handedOver("\\{x \\in \\mathbb{R} \\mid x^{2} < 4\\}").empty());
  ASS(handedOver("\\forall x \\in \\mathbb{R}\\ (x \\in \\mathbb{Q} \\lor x^{2} \\neq 2)").empty());
  /* Not a statement with quantifiers over numbers at all: nothing is decided, nothing handed over. */
  ASS(handedOver("\\sum_{k=1}^{n} k = \\frac{n(n+1)}{2}").empty());
  ASS(handedOver("(f \\colon S \\to S \\land \\forall x \\in S\\ (f(f(x)) = x)) \\implies \\forall x, y \\in S\\ (f(x) = f(y) \\implies x = y)").empty());
}

TEST_FUN(a_text_that_is_not_what_the_engine_hands_over_is_refused)
{
  ASS(!NumberStatement::read("").ok());
  ASS(!NumberStatement::read("numbers int \n").ok());
  ASS(!NumberStatement::read("numbers complex\n(= 1 1)\n").ok());
  ASS(!NumberStatement::read("numbers int \n(= 1 1) (= 2 2)\n").ok());                 // text after the statement
  ASS(!NumberStatement::read("numbers int \n(= (var 1) 1\n").ok());                    // a parenthesis left open
  ASS(!NumberStatement::read("numbers int \n(= (sqrt 4) 2)\n").ok());                  // an operation that is not there
  ASS(!NumberStatement::read("numbers int \n(= (div 4 2) 2)\n").ok());                 // a division among integers
  ASS(!NumberStatement::read("numbers rat \n(= (div 4 0) 2)\n").ok());                 // a division by zero
  ASS(!NumberStatement::read("numbers rat \n(divides 2 4)\n").ok());                   // divisibility among rationals
  ASS(!NumberStatement::read("numbers int \n(= (pow 2 0) 1)\n").ok());                 // an exponent that is not from 1 to 16
  ASS(!NumberStatement::read("numbers int \n(= (pow 2 17) 1)\n").ok());
  ASS(!NumberStatement::read("numbers int \n(forall (var 1) (set except 1/2) (= (var 1) 1))\n").ok());  // a half among integers
  ASS(!NumberStatement::read("numbers int \n(forall (var 1) (set ge x) (= (var 1) 1))\n").ok());
  ASS(NumberStatement::read("numbers int \n(= (pow 2 3) 8)\n").ok());
  ASS(NumberStatement::read("numbers real\n(forall (var 7) (set gt 0 except 1/2) (less 0 (div (var 7) 3)))\n").ok());
}

TEST_FUN(a_statement_the_engine_reads_and_has_no_method_for_is_handed_over)
{
  qr_init();

  /* An order relation among integers: the engine reads it and says that it
   * has no method. It is a statement like the others for whoever has one. */
  std::string item = asItem("\\forall n \\in \\mathbb{N}\\ (n^{2} \\ge n)");
  ASS(qr_decide_item(item.c_str(), item.c_str() + item.size(), 1).outcome == QR_UNSUPPORTED);
  std::string text = handedOver("\\forall n \\in \\mathbb{N}\\ (n^{2} \\ge n)");
  ASS_EQ(text, "numbers int \n(forall (var 110) (set ge 1) (lesseq (var 110) (pow (var 110) 2)))\n");
  ASS_EQ(NumberStatement::read(text).tptp(false),
         "tff(statement, conjecture, (![X110:$int]: ($greatereq(X110,1) => $lesseq(X110,$product(X110,X110))))).\n");
}
