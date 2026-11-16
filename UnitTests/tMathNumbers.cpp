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
#include <vector>

#include "Math/Engine.h"
#include "Math/NumberStatement.hpp"
#include "Proof/IndependentChecker.h"
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

TEST_FUN(a_statement_that_numbers_settle_is_asked_with_its_quantifiers_in_front)
{
  qr_init();

  /* "If x = k^2 + 7 and y = j^2 + 7 then x = y": false, and four numbers show it. */
  NumberStatement statement = NumberStatement::read(handedOver(
    "\\forall x, y \\in \\mathbb{Z}\\ ((\\exists k \\in \\mathbb{Z}\\ (x = k^{2} + 7) \\land \\exists k \\in \\mathbb{Z}\\ (y = k^{2} + 7)) \\implies x = y)"));
  ASS(statement.ok());

  /* To refute it: the two "for all" and the two "there is" of the hypothesis each need one value. */
  NumberStatement::WitnessProblem refuting = statement.witnessProblem(true);
  ASS(refuting.tptp.compare(0, 59, "tff(statement, conjecture, ?[W0:$int, W1:$int, W2:$int, W3:") == 0);
  ASS(refuting.tptp.find("]: (~(") != std::string::npos);
  ASS(refuting.tptp.find("![") == std::string::npos);     // no quantifier is left inside
  ASS_EQ(refuting.quantifiers.size(), 4u);
  ASS_EQ(refuting.quantifiers[0], 0u);
  ASS_EQ(refuting.quantifiers[3], 3u);
  ASS_EQ(refuting.letters[0], "120");                     // x
  ASS_EQ(refuting.letters[2], "107");                     // k

  /* To prove it would take a proof for every x and y: no numbers do that. */
  ASS(statement.witnessProblem(false).tptp.empty());

  /* The certificate with the numbers Vampire gives, and the checker's verdict on it. */
  std::string certificate = statement.certificate(true, refuting, {"7", "8", "0", "1"});
  ASS(certificate.find("certificate numbers\nkind int\nstatement (forall ") == 0);
  ASS(certificate.find("\nfails\nwitness 0 7\nwitness 1 8\nwitness 2 0\nwitness 3 1\nend\n") != std::string::npos);
  const char* why = "";
  ASS(proof_check_certificate(certificate.c_str(), &why) == PROOF_CHECK_ACCEPTED);

  /* Numbers that are not a counterexample, and the claim that the statement holds, are not accepted. */
  ASS(proof_check_certificate(statement.certificate(true, refuting, {"7", "7", "0", "0"}).c_str(), &why) != PROOF_CHECK_ACCEPTED);
  ASS(proof_check_certificate(statement.certificate(false, refuting, {"7", "8", "0", "1"}).c_str(), &why) != PROOF_CHECK_ACCEPTED);
}

TEST_FUN(a_quantifier_that_no_value_settles_is_left_to_the_checker_only_as_the_innermost_over_integers)
{
  qr_init();

  /* "For every m there is x with ...": to refute it one m is not enough, the inner "there is" must fail for all x.
   * Over the integers the checker settles that by its count, once m has a value: the inner quantifier stays, m is asked for. */
  NumberStatement alternating = NumberStatement::read(handedOver(
    "\\forall m \\in \\mathbb{Z}\\ \\exists x \\in \\mathbb{N}\\ (x - m \\in \\mathbb{N}_{0} \\land m - x \\in \\mathbb{N}_{0})"));
  ASS(alternating.ok());
  NumberStatement::WitnessProblem refutingIt = alternating.witnessProblem(true);
  ASS(refutingIt.tptp.compare(0, 37, "tff(statement, conjecture, ?[W0:$int]") == 0);
  ASS(refutingIt.tptp.find("?[X") != std::string::npos);
  ASS(refutingIt.quantifiers.size() == 1 && refutingIt.quantifiers[0] == 0 && refutingIt.counted == 1);
  const char* reason = "";
  ASS(proof_check_certificate(alternating.certificate(true, refutingIt, {"0"}).c_str(), &reason) == PROOF_CHECK_ACCEPTED);
  ASS(proof_check_certificate(alternating.certificate(true, refutingIt, {"-4"}).c_str(), &reason) == PROOF_CHECK_ACCEPTED);
  ASS(proof_check_certificate(alternating.certificate(true, refutingIt, {"3"}).c_str(), &reason) != PROOF_CHECK_ACCEPTED);   // x = 3 is there
  /* To prove it, the outer "for every m" would have to hold with a quantifier inside: nothing settles that. */
  ASS(alternating.witnessProblem(false).tptp.empty());

  /* One integer variable and nothing to ask anybody: the problem is the statement, and the count is the certificate. */
  NumberStatement single = NumberStatement::read(handedOver("\\forall n \\in \\mathbb{N}\\ (n^{2} \\ge n)"));
  ASS(single.ok());
  NumberStatement::WitnessProblem provingIt = single.witnessProblem(false);
  ASS(!provingIt.tptp.empty() && provingIt.quantifiers.empty() && provingIt.counted == 1);
  ASS(proof_check_certificate(single.certificate(false, provingIt, {}).c_str(), &reason) == PROOF_CHECK_ACCEPTED);
  ASS(proof_check_certificate(single.certificate(true, single.witnessProblem(true), {}).c_str(), &reason) != PROOF_CHECK_ACCEPTED);

  /* Among rationals there is no count: the same shapes have no witness problem. */
  NumberStatement dense = NumberStatement::read(handedOver("\\forall m \\in \\mathbb{Q}\\ \\exists x \\in \\mathbb{Q}\\ (x = m \\land x \\neq m)"));
  ASS(dense.ok());
  ASS(dense.witnessProblem(true).tptp.empty());
  ASS(dense.witnessProblem(false).tptp.empty());

  /* "There is x with x^2 = 49": to prove it one value is enough. To refute it no value is: over the integers
   * that is left to the checker's count, which here says the opposite. */
  NumberStatement existential = NumberStatement::read(handedOver("\\exists x \\in \\mathbb{N}\\ (x^{2} = 49)"));
  ASS(existential.ok());
  NumberStatement::WitnessProblem proving = existential.witnessProblem(false);
  ASS(proving.tptp.compare(0, 36, "tff(statement, conjecture, ?[W0:$int") == 0);
  NumberStatement::WitnessProblem refuting = existential.witnessProblem(true);
  ASS(!refuting.tptp.empty() && refuting.quantifiers.empty() && refuting.counted == 1);
  const char* why = "";
  ASS(proof_check_certificate(existential.certificate(true, refuting, {}).c_str(), &why) != PROOF_CHECK_ACCEPTED);
  ASS(proof_check_certificate(existential.certificate(false, proving, {"7"}).c_str(), &why) == PROOF_CHECK_ACCEPTED);
  ASS(proof_check_certificate(existential.certificate(false, proving, {"6"}).c_str(), &why) != PROOF_CHECK_ACCEPTED);
  ASS(proof_check_certificate(existential.certificate(false, proving, {"-7"}).c_str(), &why) != PROOF_CHECK_ACCEPTED);   // not in N

  /* Under an "if and only if" a quantifier counts both ways, and no value settles it: among rationals there is
   * no witness problem; among integers it is left to the checker's count, which settles the whole statement. */
  NumberStatement both = NumberStatement::read("numbers rat \n(iff (exists (var 1) (set) (= (var 1) 0)) (= 0 0))\n");
  ASS(both.ok());
  ASS(both.witnessProblem(false).tptp.empty());
  ASS(both.witnessProblem(true).tptp.empty());
  NumberStatement whole = NumberStatement::read("numbers int \n(iff (exists (var 1) (set) (= (var 1) 0)) (= 0 0))\n");
  ASS(whole.ok());
  NumberStatement::WitnessProblem holding = whole.witnessProblem(false);
  ASS(!holding.tptp.empty() && holding.quantifiers.empty() && holding.counted == 1);
  ASS(proof_check_certificate(whole.certificate(false, holding, {}).c_str(), &why) == PROOF_CHECK_ACCEPTED);
  ASS(proof_check_certificate(whole.certificate(true, whole.witnessProblem(true), {}).c_str(), &why) != PROOF_CHECK_ACCEPTED);
}

TEST_FUN(an_answer_of_vampire_is_a_witness_only_if_it_is_a_number)
{
  std::string value;
  ASS(NumberStatement::answerValue("7", value) && value == "7");
  ASS(NumberStatement::answerValue(" -3 ", value) && value == "-3");
  ASS(NumberStatement::answerValue("1/2", value) && value == "1/2");
  ASS(NumberStatement::answerValue("$to_real(0/1)", value) && value == "0/1");
  ASS(NumberStatement::answerValue("$to_rat(-5)", value) && value == "-5");
  ASS(NumberStatement::answerValue("2.5", value) && value == "25/10");
  ASS(!NumberStatement::answerValue("X0", value));
  ASS(!NumberStatement::answerValue("$sum(1,2)", value));
  ASS(!NumberStatement::answerValue("sK3", value));
  ASS(!NumberStatement::answerValue("1/0", value));
  ASS(!NumberStatement::answerValue("", value));
  ASS(!NumberStatement::answerValue("12345678901234567890", value));
}
