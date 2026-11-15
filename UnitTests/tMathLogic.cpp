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
 * @file tMathLogic.cpp
 * Unit tests of the path of a statement of logic read from LaTeX: the typed
 * reading (Math/LogicStatement), the translation into a Vampire problem
 * (Math/LogicTranslator), the independent checker (Proof/IndependentChecker.h),
 * what the mathematical engine does with a model or a proof found by
 * Vampire, and what it does with false, ill-defined and ambiguous
 * statements.
 *
 * The rule the tests defend: nothing false is ever reported as proved, and
 * nothing is called verified that the independent checker did not accept.
 */

#include <string>
#include <vector>

#include "Kernel/Unit.hpp"
#include "Math/Engine.h"
#include "Math/LogicStatement.hpp"
#include "Math/LogicTranslator.hpp"
#include "Math/Verification.hpp"
#include "Proof/IndependentChecker.h"
#include "Test/UnitTesting.hpp"

using namespace Math;

/* "If g(f(x)) = x for every x in S then f is onto T": false, e.g. with one
 * element in S and two in T. */
static const char* const LEFT_INVERSE =
  "certificate counterexample\n"
  "sort S\n"
  "sort T\n"
  "symbol f S T\n"
  "symbol g T S\n"
  "statement (implies (and (and true true) (forall x S (= (g (f x)) x))) (forall y T (exists x S (= (f x) y))))\n";

/** A certificate for LEFT_INVERSE with the given sizes and tables. */
static std::string leftInverseCertificate(const char* sizeS, const char* sizeT, const char* tableF, const char* tableG)
{
  return std::string("certificate counterexample\nsort S ") + sizeS + "\nsort T " + sizeT + "\n"
       + "symbol f S T\nsymbol g T S\n"
       + "statement (implies (and (and true true) (forall x S (= (g (f x)) x))) (forall y T (exists x S (= (f x) y))))\n"
       + "table f " + tableF + "\ntable g " + tableG + "\nend\n";
}

TEST_FUN(reads_a_first_order_statement)
{
  LogicStatement statement = LogicStatement::read(LEFT_INVERSE, false);
  ASS(statement.outside().empty());
  ASS_EQ(statement.sorts().size(), 2u);
  ASS_EQ(statement.symbols().size(), 2u);
  ASS_EQ(statement.symbols()[0].range, 1);
  ASS_EQ(statement.symbols()[1].domain[0], 1u);
  ASS(statement.formula().connective == LogicStatement::Connective::IMPLIES);
  ASS_EQ(statement.variables(), 3u);

  /* The claim: for every y in T there is x in S with f(x) = y. */
  const LogicStatement::Formula& claim = statement.formula().parts[1];
  ASS(claim.connective == LogicStatement::Connective::FORALL);
  ASS_EQ(claim.sort, 1u);
  const LogicStatement::Formula& equation = claim.parts[0].parts[0];
  ASS(equation.connective == LogicStatement::Connective::EQUAL);
  ASS_EQ(equation.terms[0].sort, 1u);
  ASS(equation.terms[1].variable >= 0);
}

TEST_FUN(a_bound_variable_hides_a_symbol_of_the_same_name)
{
  LogicStatement statement = LogicStatement::read(
    "sort S\nsymbol x S\nsymbol A S bool\nstatement (implies (A x) (forall x S (A x)))\n", false);
  ASS(statement.outside().empty());
  const LogicStatement::Formula& hypothesis = statement.formula().parts[0];
  const LogicStatement::Formula& body = statement.formula().parts[1].parts[0];
  ASS(hypothesis.terms[0].variable < 0);  // the named element
  ASS(body.terms[0].variable >= 0);       // the variable of the quantifier
}

TEST_FUN(reads_sets_of_parts_sets_of_maps_and_written_numbers)
{
  /* The set of all the parts of S comes with membership, the set of all
   * the maps from S to T with application, the written numbers with their
   * names; the laws the engine gives are read with the statement. */
  LogicStatement parts = LogicStatement::read(
    "sort S\nsort P_1 parts S inP_1\nsymbol f S P_1\n"
    "statement (forall x S (inP_1 x (f x)))\n"
    "axiom (forall h P_1 (forall j P_1 (implies (forall k S (iff (inP_1 k h) (inP_1 k j))) (= h j))))\n", false);
  ASS(parts.outside().empty());
  ASS(!parts.plainOnly());
  ASS(parts.sorts()[1].kind == LogicStatement::SortKind::PARTS);
  ASS_EQ(parts.sorts()[1].base, 0u);
  ASS_EQ(parts.symbols().size(), 2u);
  ASS(parts.symbols()[0].structure && parts.symbols()[0].isRelation());
  ASS(!parts.symbols()[1].structure);
  ASS_EQ(parts.laws().size(), 1u);

  LogicStatement maps = LogicStatement::read(
    "sort S\nsort T\nsort M_2 maps S T apM_2\nstatement (forall f M_2 (forall x S (= (apM_2 f x) (apM_2 f x))))\n", false);
  ASS(maps.outside().empty());
  ASS(maps.sorts()[2].kind == LogicStatement::SortKind::MAPS);
  ASS_EQ(maps.sorts()[2].target, 1u);
  ASS_EQ(maps.symbols()[0].range, 1);

  LogicStatement numbers = LogicStatement::read(
    "sort S\nsort Num numbers num1 num2\nsymbol f S Num\nstatement (forall x S (or (= (f x) num1) (= (f x) num2)))\n", false);
  ASS(numbers.outside().empty());
  ASS(numbers.sorts()[1].kind == LogicStatement::SortKind::NUMBERS);
  ASS_EQ(numbers.symbols().size(), 3u);
}

TEST_FUN(refuses_what_has_no_first_order_form)
{
  /* A quantifier on parts that are not a set of the statement, and a
   * bijection between two sets, are left to the engine. */
  ASS(!LogicStatement::read("sort S\nstatement (forallpart X S (forall x S (X x)))\n", false).outside().empty());
  ASS(!LogicStatement::read("sort S\nsort T\nstatement (equipotent S T)\n", false).outside().empty());

  /* A set of parts of a set that is not there, a law that is not a condition. */
  ASS(!LogicStatement::read("sort P_1 parts S inP_1\nstatement true\n", false).outside().empty());
  ASS(!LogicStatement::read("sort S\nstatement true\naxiom (forall x S\n", false).outside().empty());
}

TEST_FUN(the_laws_of_a_set_of_parts_go_to_vampire_as_axioms)
{
  LogicStatement statement = LogicStatement::read(
    "sort S\nsort P_1 parts S inP_1\n"
    "statement (forall X P_1 (forall Y P_1 (implies (forall x S (iff (inP_1 x X) (inP_1 x Y))) (= X Y))))\n"
    "axiom (forall h P_1 (forall j P_1 (implies (forall k S (iff (inP_1 k h) (inP_1 k j))) (= h j))))\n"
    "axiom (exists m P_1 (forall n S (iff (inP_1 n m) (not true))))\n", false);
  LogicTranslator translator(statement);
  translator.translate();

  /* The empty part is always there: the set of parts needs no guard. S may be empty. */
  ASS(translator.mayBeEmpty(0));
  ASS(!translator.mayBeEmpty(1));
  ASS_EQ(translator.inputs().size(), 3u);
  ASS(translator.inputs()[0].role == LogicTranslator::Role::LAW);
  ASS(translator.inputs()[1].role == LogicTranslator::Role::LAW);
  ASS(translator.inputs()[2].role == LogicTranslator::Role::CLAIM);
}

TEST_FUN(the_written_numbers_are_distinct_and_are_all_there_is)
{
  LogicStatement statement = LogicStatement::read(
    "sort Num numbers num1 num2 num3\nsymbol R Num Num bool\nstatement (R num1 num2)\n", false);
  LogicTranslator translator(statement);
  translator.translate();
  ASS(!translator.mayBeEmpty(0));
  ASS_EQ(translator.inputs().size(), 3u);
  ASS(translator.inputs()[0].role == LogicTranslator::Role::STRUCTURE);
  ASS(translator.inputs()[1].role == LogicTranslator::Role::STRUCTURE);
  std::string distinct = translator.inputs()[0].unit->toString();
  std::string all = translator.inputs()[1].unit->toString();
  ASS(distinct.find("num1 != num2") != std::string::npos);
  ASS(all.find("num3") != std::string::npos);
}

TEST_FUN(a_set_of_maps_is_empty_exactly_when_its_maps_cannot_exist)
{
  LogicStatement statement = LogicStatement::read(
    "sort S\nsort T\nsort M_2 maps S T apM_2\nstatement (exists f M_2 true)\n", false);
  LogicTranslator translator(statement);
  translator.translate();
  ASS(translator.mayBeEmpty(2));
  bool found = false;
  for (const LogicTranslator::Input& input : translator.inputs())
    found = found || (input.role == LogicTranslator::Role::STRUCTURE && input.unit->toString().find("inhabited_M_2 <=>") != std::string::npos);
  ASS(found);
}

TEST_FUN(refuses_a_statement_that_is_not_well_sorted_or_not_well_written)
{
  const char* declarations = "sort S\nsort T\nsymbol a S\nsymbol b T\nsymbol f S T\nsymbol R S S bool\n";
  auto refused = [&](const char* condition) {
    return !LogicStatement::read(std::string(declarations) + "statement " + condition + "\n", false).outside().empty();
  };
  ASS(!refused("(= (f a) b)"));
  ASS(refused("(= a b)"));              // two different sets
  ASS(refused("(= (f b) b)"));          // f applied outside its domain
  ASS(refused("(= (f a a) b)"));        // too many arguments
  ASS(refused("(= c a)"));              // a name that is not declared
  ASS(refused("(R a)"));                // a relation with an argument missing
  ASS(refused("(= (R a a) a)"));        // a relation used as an element
  ASS(refused("(forall x U (R x x))")); // a set that is not declared
  ASS(refused("(R a a) (R a a)"));      // text after the condition
  ASS(refused("(R a a"));               // a parenthesis left open
  ASS(!LogicStatement::read(declarations, false).outside().empty());  // no statement at all
}

TEST_FUN(a_sort_that_may_be_empty_is_guarded)
{
  /* "For every x in S there is y in S with x = y" holds also when S is
   * empty: the translation must not assume S has an element. */
  LogicStatement statement = LogicStatement::read("sort S\nstatement (forall x S (exists y S (= x y)))\n", false);
  LogicTranslator translator(statement);
  translator.translate();
  ASS(translator.mayBeEmpty(0));
  ASS_EQ(translator.inputs().size(), 1u);
  ASS(translator.inputs()[0].role == LogicTranslator::Role::CLAIM);
  std::string negatedClaim = translator.inputs()[0].unit->toString();
  ASS(negatedClaim.find("inhabited_S") != std::string::npos);
}

TEST_FUN(a_sort_with_a_named_element_is_not_guarded)
{
  LogicStatement statement = LogicStatement::read("sort S\nsymbol c S\nstatement (forall x S (exists y S (= x y)))\n", false);
  LogicTranslator translator(statement);
  translator.translate();
  ASS(!translator.mayBeEmpty(0));
  ASS(translator.inputs()[0].unit->toString().find("inhabited") == std::string::npos);
}

TEST_FUN(a_map_between_two_sorts_brings_its_axiom_and_hypotheses_are_split)
{
  LogicStatement statement = LogicStatement::read(LEFT_INVERSE, false);
  LogicTranslator translator(statement);
  translator.translate();

  /* f: S -> T and g: T -> S: "S inhabited implies T inhabited" and the
   * converse; then the one hypothesis that is not trivial, then the claim. */
  ASS_EQ(translator.inputs().size(), 4u);
  ASS(translator.inputs()[0].role == LogicTranslator::Role::INHABITED);
  ASS(translator.inputs()[1].role == LogicTranslator::Role::INHABITED);
  ASS(translator.inputs()[2].role == LogicTranslator::Role::HYPOTHESIS);
  ASS(translator.inputs()[3].role == LogicTranslator::Role::CLAIM);
  ASS(translator.hasConjecture());
}

TEST_FUN(a_map_from_a_sort_into_itself_brings_no_axiom)
{
  LogicStatement statement = LogicStatement::read(
    "sort S\nsymbol f S S\nstatement (forall x S (= (f (f x)) x))\n", false);
  LogicTranslator translator(statement);
  translator.translate();
  ASS_EQ(translator.inputs().size(), 1u);
}

TEST_FUN(a_statement_that_wants_an_example_has_no_conjecture)
{
  LogicStatement statement = LogicStatement::read("sort S\nsymbol A S bool\nstatement (exists x S (A x))\n", true);
  LogicTranslator translator(statement);
  translator.translate();
  ASS(!translator.hasConjecture());
  ASS(translator.inputs()[0].role == LogicTranslator::Role::STATEMENT);
}

TEST_FUN(the_checker_accepts_a_counterexample)
{
  /* S = {0}, T = {0, 1}, f(0) = 1, g = 0 everywhere: g(f(x)) = x holds and 0 in T is not reached. */
  ASS(proof_check_certificate(leftInverseCertificate("1", "2", "1", "0 0").c_str(), nullptr) == PROOF_CHECK_ACCEPTED);
}

TEST_FUN(the_checker_rejects_an_altered_counterexample)
{
  const char* why = nullptr;

  /* T with one element: f is onto, the statement holds, this is no counterexample. */
  ASS(proof_check_certificate(leftInverseCertificate("1", "1", "0", "0").c_str(), &why) == PROOF_CHECK_REJECTED);

  /* Two elements in S and a g that is not a left inverse: the hypothesis fails, the statement holds. */
  ASS(proof_check_certificate(leftInverseCertificate("2", "2", "0 1", "1 0").c_str(), &why) == PROOF_CHECK_REJECTED);

  /* A value outside its set, a table too short, a table missing. */
  ASS(proof_check_certificate(leftInverseCertificate("1", "2", "5", "0 0").c_str(), &why) != PROOF_CHECK_ACCEPTED);
  ASS(proof_check_certificate(leftInverseCertificate("1", "2", "1", "0").c_str(), &why) != PROOF_CHECK_ACCEPTED);
  std::string missing = leftInverseCertificate("1", "2", "1", "0 0");
  missing.erase(missing.find("table g"), std::string("table g 0 0\n").size());
  ASS(proof_check_certificate(missing.c_str(), &why) != PROOF_CHECK_ACCEPTED);

  /* The same model for another statement, a true one: a counterexample certifies its own statement only. */
  std::string other = leftInverseCertificate("1", "2", "1", "0 0");
  std::string claim = "(forall y T (exists x S (= (f x) y)))";
  other.replace(other.find(claim), claim.size(), "(forall y T (= y y))");
  ASS(proof_check_certificate(other.c_str(), &why) == PROOF_CHECK_REJECTED);

  /* An operator the checker does not know: the third answer, which is not a yes. */
  std::string unknown = leftInverseCertificate("1", "2", "1", "0 0");
  unknown.replace(unknown.find("(= (f x) y)"), std::string("(= (f x) y)").size(), "(almost (f x) y)");
  ASS(proof_check_certificate(unknown.c_str(), &why) != PROOF_CHECK_ACCEPTED);
}

TEST_FUN(the_engine_hands_logic_over_only_when_asked)
{
  qr_init();
  const char* involution = "(f \\colon S \\to S \\land \\forall x \\in S\\ (f(f(x)) = x)) \\implies "
                           "\\forall x, y \\in S\\ (f(x) = f(y) \\implies x = y)";
  QrVerdict handedOver = qr_decide_formula(involution, 1);
  ASS(handedOver.outcome == QR_LOGIC);
  ASS(handedOver.logic != nullptr);
  ASS(LogicStatement::read(handedOver.logic, handedOver.wants_example != 0).outside().empty());

  QrVerdict decided = qr_decide_formula(involution, 0);
  ASS(decided.outcome == QR_PROVED);
  ASS(decided.certified);
}

/* The statement of LEFT_INVERSE as it is written in LaTeX, as the text of an \\item. */
static const std::string LEFT_INVERSE_ITEM =
  "$\\displaystyle (f \\colon S \\to T \\land g \\colon T \\to S \\land \\forall x \\in S\\ (g(f(x)) = x)) "
  "\\implies \\forall y \\in T\\ \\exists x \\in S\\ (f(x) = y)$";

/** Has the engine judge a model of LEFT_INVERSE_ITEM given as sizes of S and T and tables of f and g. */
static QrVerdict adoptLeftInverse(std::vector<size_t> sizes, std::vector<size_t> f, std::vector<size_t> g)
{
  const size_t* tables[] = {f.data(), g.data()};
  size_t cells[] = {f.size(), g.size()};
  QrModel model = {(unsigned)sizes.size(), sizes.data(), 2, tables, cells};
  return qr_adopt_model(LEFT_INVERSE_ITEM.c_str(), LEFT_INVERSE_ITEM.c_str() + LEFT_INVERSE_ITEM.size(), &model);
}

TEST_FUN(the_engine_adopts_a_model_found_elsewhere_and_certifies_it)
{
  qr_init();

  /* S = {0}, T = {0, 1}, f(0) = 1, g = 0 everywhere. */
  QrVerdict verdict = adoptLeftInverse({1, 2}, {1}, {0, 0});
  ASS(verdict.outcome == QR_REFUTED);
  ASS(verdict.certified);
  ASS(verdict.certificate != nullptr);
  ASS(proof_check_certificate(verdict.certificate, nullptr) == PROOF_CHECK_ACCEPTED);
}

TEST_FUN(the_engine_does_not_adopt_what_is_not_a_counterexample)
{
  qr_init();

  /* T with one element: f is onto, the statement holds in this model. */
  ASS(adoptLeftInverse({1, 1}, {0}, {0}).outcome == QR_NOT_PROVED);

  /* g is not a left inverse of f: the hypothesis fails, the statement holds. */
  ASS(adoptLeftInverse({2, 2}, {0, 1}, {1, 0}).outcome == QR_NOT_PROVED);
}

TEST_FUN(the_engine_does_not_adopt_what_is_not_an_interpretation)
{
  qr_init();
  ASS(adoptLeftInverse({1}, {1}, {0, 0}).outcome == QR_NOT_PROVED);          // a set is missing
  ASS(adoptLeftInverse({1, 2}, {5}, {0, 0}).outcome == QR_NOT_PROVED);       // a value outside its set
  ASS(adoptLeftInverse({1, 2}, {1}, {0}).outcome == QR_NOT_PROVED);          // a table too short
  ASS(adoptLeftInverse({1, 2}, {1, 1}, {0, 0}).outcome == QR_NOT_PROVED);    // a table too long
  ASS(adoptLeftInverse({1, 0}, {0}, {}).outcome == QR_NOT_PROVED);           // a map into an empty set

  /* None of the above is a failed step of the engine: the model was not its own. */
  ASS_EQ(qr_unjustified_steps(), 0);
}

TEST_FUN(the_engine_adopts_a_model_with_an_empty_set)
{
  qr_init();

  /* "Every map of S into itself has a point x with f(x) = f(x)" fails in the empty set, and only there. */
  std::string item = "$\\displaystyle \\forall f \\in S^{S}\\ \\exists x \\in S\\ (f(x) = f(x))$";
  std::vector<size_t> sizes = {0};
  const size_t* tables[] = {nullptr};
  size_t cells[] = {0};
  QrModel model = {1, sizes.data(), 1, tables, cells};
  QrVerdict verdict = qr_adopt_model(item.c_str(), item.c_str() + item.size(), &model);
  ASS(verdict.outcome == QR_REFUTED);
  ASS(verdict.certified);
}

/** The text of an \\item with one displayed formula. */
static std::string asItem(const char* formula) { return std::string("$\\displaystyle ") + formula + "$"; }

TEST_FUN(the_engine_rebuilds_a_proof_found_elsewhere_as_a_certificate)
{
  qr_init();
  std::string involution = asItem("(f \\colon S \\to S \\land \\forall x \\in S\\ (f(f(x)) = x)) \\implies "
                                  "\\forall x, y \\in S\\ (f(x) = f(y) \\implies x = y)");
  QrVerdict verdict = qr_certify_item(involution.c_str(), involution.c_str() + involution.size());
  ASS(verdict.outcome == QR_PROVED);
  ASS(verdict.certified);
  ASS(proof_check_certificate(verdict.certificate, nullptr) == PROOF_CHECK_ACCEPTED);
}

TEST_FUN(rebuilding_a_proof_of_a_false_statement_gives_no_proof)
{
  qr_init();

  /* Asked to certify a statement that is false, the engine does not write
   * a proof: its check on small models finds the counterexample, and the
   * caller learns that the "proof" it was given cannot be right. */
  QrVerdict falseOne = qr_certify_item(LEFT_INVERSE_ITEM.c_str(), LEFT_INVERSE_ITEM.c_str() + LEFT_INVERSE_ITEM.size());
  ASS(falseOne.outcome == QR_REFUTED);

  /* True in every finite set and false in general: no counterexample to
   * find, and no proof to write either. */
  std::string trap = asItem("(f \\colon S \\to S \\land \\forall x, y \\in S\\ (f(x) = f(y) \\implies x = y)) \\implies "
                            "\\forall y \\in S\\ \\exists x \\in S\\ (f(x) = y)");
  ASS(qr_certify_item(trap.c_str(), trap.c_str() + trap.size()).outcome == QR_NOT_PROVED);
}

TEST_FUN(the_engine_does_not_hand_over_mathematics)
{
  qr_init();
  QrVerdict sum = qr_decide_formula("\\sum_{k=1}^{n} k = \\frac{n(n+1)}{2}", 1);
  ASS(sum.outcome == QR_PROVED);
  ASS(sum.certified);
}

TEST_FUN(the_engine_never_proves_a_false_statement)
{
  qr_init();

  /* A wrong coefficient. */
  ASS(qr_decide_formula("\\sum_{k=1}^{n} k = \\frac{n(n+2)}{2}", 1).outcome == QR_REFUTED);

  /* Division by zero: x / x is not 1 at x = 0, where it has no value. */
  ASS(qr_decide_formula("\\forall x \\in \\mathbb{R}\\ \\left(\\frac{x}{x} = 1\\right)", 1).outcome != QR_PROVED);

  /* A condition of existence ignored: the square root of x^2 is not x for negative x. */
  ASS(qr_decide_formula("\\forall x \\in \\mathbb{R}\\ \\left(\\sqrt{x^{2}} = x\\right)", 1).outcome != QR_PROVED);

  /* An inequality that holds only from some n on is not a theorem for every n. */
  ASS(qr_decide_formula("2^{n} > n^{2}", 1).outcome != QR_PROVED);

  /* False in the empty set... true there, and false elsewhere: "every map of S into itself has a fixed point". */
  ASS(qr_decide_formula("f \\colon S \\to S \\implies \\exists x \\in S\\ (f(x) = x)", 0).outcome != QR_PROVED);
}

TEST_FUN(the_engine_refuses_ambiguous_and_invalid_latex)
{
  qr_init();

  /* Where does the derived function end? The writing is refused, not read one way. */
  QrVerdict ambiguous = qr_decide_formula("\\frac{d}{dx}(x^{2}) \\cdot (x) = 3x^{2}", 1);
  ASS(ambiguous.outcome == QR_UNSUPPORTED);
  ASS(ambiguous.reason != nullptr);

  /* Not a formula at all, a brace left open, an unknown command. */
  ASS(qr_decide_formula("this is not a formula", 1).outcome == QR_UNSUPPORTED);
  ASS(qr_decide_formula("\\frac{1}{x", 1).outcome == QR_UNSUPPORTED);
  ASS(qr_decide_formula("\\thiscommanddoesnotexist{x} = x", 1).outcome == QR_UNSUPPORTED);
}

TEST_FUN(a_status_says_who_confirmed_it)
{
  /* A proof found is not a proof certified, in either language. */
  ASS(std::string(statusName(Status::THEOREM_CERTIFIED, Language::ENGLISH)) != statusName(Status::THEOREM_UNVERIFIED, Language::ENGLISH));
  ASS(std::string(statusName(Status::THEOREM_CERTIFIED, Language::ITALIAN)) != statusName(Status::THEOREM_UNVERIFIED, Language::ITALIAN));
  ASS(std::string(statusCode(Status::COUNTEREXAMPLE_VERIFIED)) != statusCode(Status::COUNTEREXAMPLE_UNVERIFIED));
  ASS(std::string(statusSZS(Status::THEOREM_UNVERIFIED)) == "Theorem");
  ASS(statusPositive(Status::RESULT_VALIDATED));
  ASS(!statusPositive(Status::COUNTEREXAMPLE_VERIFIED));

  /* A refutation that the checker followed is not a counterexample, and it is not a theorem. */
  ASS(std::string(statusCode(Status::REFUTATION_CERTIFIED)) != statusCode(Status::COUNTEREXAMPLE_VERIFIED));
  ASS(!statusPositive(Status::REFUTATION_CERTIFIED));
  ASS(std::string(statusSZS(Status::REFUTATION_CERTIFIED)) == "Unsatisfiable");
  ASS(!statusPositive(Status::UNSOLVED));
}
