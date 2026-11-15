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
 * @file tProofReplay.cpp
 * Unit tests of Proof::Replay, which turns the inferences of a refutation
 * found by Vampire into the explicit steps that the independent checker
 * follows: resolutions and rewritings, the splitting of AVATAR with its
 * names, and the verdict of the SAT solver rebuilt as resolutions.
 *
 * The rule the tests defend: an inference that is not an instance of the
 * checker's steps is not rebuilt, and what is rebuilt is accepted by the
 * checker only as long as nothing in it is altered.
 */

#include <string>
#include <vector>

#include "Math/Engine.h"
#include "Proof/IndependentChecker.h"
#include "Proof/Replay.hpp"
#include "Test/UnitTesting.hpp"

using Proof::Replay;

/** What the engine hands over, written by hand: a beginning, the symbols (arity, predicate or not), the initial clauses. */
static std::string handed(const std::vector<std::string>& symbols, const std::vector<std::string>& clauses)
{
  std::string text = "certificate saturation\nclausify\nsymbols " + std::to_string(symbols.size()) + "\n";
  for (const std::string& symbol : symbols) text += symbol + "\n";
  text += "clauses " + std::to_string(clauses.size()) + "\n";
  for (const std::string& clause : clauses) text += clause + "\n";
  return text;
}

static Replay::Clause clause(Replay& replay, const std::string& text)
{
  Replay::Clause result;
  ASS(replay.parseClause(text, result));
  return result;
}

static bool contains(const std::string& text, const std::string& part)
{
  return text.find(part) != std::string::npos;
}

/* p(x) or f(x) = b;  not p(a);  f(a) != b.  Symbols: 0 p, 1 a, 2 b, 3 f. */
static const std::vector<std::string> EQUATION_SYMBOLS = {"1 1", "0 0", "0 0", "1 0"};
static const std::vector<std::string> EQUATION_CLAUSES = {
  "(clause (pos (f 0 (v 0))) (eq (f 3 (v 0)) (f 2)))",
  "(clause (neg (f 0 (f 1))))",
  "(clause (ne (f 3 (f 1)) (f 2)))"};

TEST_FUN(rebuilds_a_resolution_whichever_way_round_vampire_writes_an_equation)
{
  Replay replay;
  ASS(replay.start(handed(EQUATION_SYMBOLS, EQUATION_CLAUSES)));
  ASS_EQ(replay.initialClauses(), 3);
  for (unsigned unit = 1; unit <= 3; unit++) replay.input(unit, (int)unit - 1);

  /* Vampire writes b = f(a), the certificate will have f(a) = b: the same clause. */
  ASS(replay.derive(4, {1, 2}, clause(replay, "(clause (eq (f 2) (f 3 (f 1))))")));
  ASS(!replay.refutes(4));
  ASS(replay.derive(5, {4, 3}, clause(replay, "(clause)")));
  ASS(replay.refutes(5));
  ASS_EQ(replay.steps(), 2u);
  ASS(contains(replay.certificate(), "step resolve"));
  ASS(contains(replay.certificate(), "(clause (eq (f 3 (f 1)) (f 2)))"));
}

TEST_FUN(does_not_rebuild_what_is_not_an_inference)
{
  Replay replay;
  ASS(replay.start(handed(EQUATION_SYMBOLS, EQUATION_CLAUSES)));
  for (unsigned unit = 1; unit <= 3; unit++) replay.input(unit, (int)unit - 1);

  /* The empty clause does not follow from "not p(a)" alone, nor f(a) = a from the first two clauses. */
  ASS(!replay.derive(4, {2}, clause(replay, "(clause)")));
  ASS(!replay.derive(4, {1, 2}, clause(replay, "(clause (eq (f 3 (f 1)) (f 1)))")));

  /* A premise that has no clause in the certificate, and an inference from no premise. */
  ASS(!replay.derive(4, {1, 9}, clause(replay, "(clause (eq (f 3 (f 1)) (f 2)))")));
  ASS(!replay.derive(4, {}, clause(replay, "(clause)")));
  ASS_EQ(replay.steps(), 0u);
}

TEST_FUN(refuses_a_text_that_is_not_what_the_engine_hands_over)
{
  Replay replay;
  ASS(!replay.start("certificate saturation\nsymbols 1\n0 0\nclauses 0\n"));      // no "clausify"
  Replay other;
  ASS(!other.start("certificate saturation\nclausify\nsymbols 1\n0 0\nclauses 1\n(clause (pos (f 0)))\n"));  // an atom that is not a predicate
  Replay third;
  ASS(third.start(handed(EQUATION_SYMBOLS, EQUATION_CLAUSES)));
  Replay::Clause unread;
  ASS(!third.parseClause("(clause (pos (f 7)))", unread));   // a symbol that does not exist
  ASS(!third.parseClause("(clause (pos (f 3 (f 1))))", unread));  // f is a function, not a predicate
  ASS(!third.parseClause("(clause (eq (f 1)))", unread));    // an equation with one side
}

/* p(x) or q(y);  not p(a);  not q(a).  Symbols: 0 p, 1 q, 2 a. */
static const std::vector<std::string> SPLIT_SYMBOLS = {"1 1", "1 1", "0 0"};
static const std::vector<std::string> SPLIT_CLAUSES = {
  "(clause (pos (f 0 (v 0))) (pos (f 1 (v 1))))",
  "(clause (neg (f 0 (f 2))))",
  "(clause (neg (f 1 (f 2))))"};

/** Feeds the refutation by splitting of SPLIT_CLAUSES up to the two contradictions; the clauses of names are the units 10, 14, 16. */
static void splitRefutation(Replay& replay)
{
  ASS(replay.start(handed(SPLIT_SYMBOLS, SPLIT_CLAUSES)));
  for (unsigned unit = 1; unit <= 3; unit++) replay.input(unit, (int)unit - 1);
  replay.definition(1, clause(replay, "(clause (pos (f 0 (v 0))))"));
  replay.definition(2, clause(replay, "(clause (pos (f 1 (v 0))))"));
  replay.component(11, 0);
  replay.component(12, 2);

  /* p(x) or q(y) becomes "1 or 2"; p(x) under the assumption 1 contradicts not p(a), and likewise q. */
  ASS(replay.split(10, 1, {1, 2}));
  ASS(replay.derive(13, {11, 2}, clause(replay, "(clause)"), {0}));
  ASS(replay.contradiction(14, 13, {-1}));
  ASS(replay.derive(15, {12, 3}, clause(replay, "(clause)"), {2}));
  ASS(replay.contradiction(16, 15, {-2}));
}

TEST_FUN(rebuilds_a_splitting_and_the_verdict_of_the_sat_solver)
{
  Replay replay;
  splitRefutation(replay);
  ASS(!replay.refutes(14));
  ASS(replay.propositional(17, {10, 14, 16}));
  ASS(replay.refutes(17));

  std::string certificate = replay.certificate();
  ASS(contains(certificate, "component (clause (pos (f 0 (v 0))))"));
  ASS(contains(certificate, "component (clause (pos (f 1 (v 0))))"));
  ASS(contains(certificate, "step split 0 (groups (0 0 0) (1 0 1)) (clause (pos (f 3)) (pos (f 4)))"));
}

TEST_FUN(does_not_take_the_word_of_the_sat_solver)
{
  /* "1 or 2" and "not 1" can both hold: there is no refutation to rebuild. */
  Replay replay;
  splitRefutation(replay);
  ASS(!replay.propositional(17, {10, 14}));
  ASS(!replay.refutes(17));

  /* A clause that is not made of names only is not a premise of the SAT solver. */
  ASS(!replay.propositional(18, {10, 14, 16, 2}));
}

TEST_FUN(does_not_rebuild_a_splitting_with_other_names)
{
  Replay replay;
  ASS(replay.start(handed(SPLIT_SYMBOLS, SPLIT_CLAUSES)));
  for (unsigned unit = 1; unit <= 3; unit++) replay.input(unit, (int)unit - 1);
  replay.definition(1, clause(replay, "(clause (pos (f 0 (v 0))))"));
  replay.definition(2, clause(replay, "(clause (pos (f 1 (v 0))))"));

  /* The clause has two parts, each with its name: "1" alone is not what splitting gives, nor "1 or not 2". */
  ASS(!replay.split(10, 1, {1}));
  ASS(!replay.split(10, 1, {1, -2}));
  /* A name that Vampire never defined. */
  ASS(!replay.split(10, 1, {1, 7}));
  /* An empty clause under no assumption is not the clause of names "not 1". */
  ASS(!replay.contradiction(14, 2, {-1}));
}

TEST_FUN(a_ground_literal_gets_its_name_by_resolution_whichever_way_round)
{
  /* a = b or p(x). Symbols: 0 p, 1 a, 2 b. Vampire's name 1 stands for b = a. */
  Replay replay;
  ASS(replay.start(handed({"1 1", "0 0", "0 0"}, {"(clause (eq (f 1) (f 2)) (pos (f 0 (v 0))))"})));
  replay.input(1, 0);
  replay.definition(1, clause(replay, "(clause (eq (f 2) (f 1)))"));
  replay.definition(2, clause(replay, "(clause (pos (f 0 (v 0))))"));
  ASS(replay.split(10, 1, {1, 2}));
  std::string certificate = replay.certificate();
  ASS(contains(certificate, "component (clause (eq (f 1) (f 2)))"));
  ASS(contains(certificate, "complement 0"));
  ASS(contains(certificate, "step resolve"));
  ASS(contains(certificate, "step split"));
}

TEST_FUN(a_name_given_the_other_way_round_asks_for_a_second_attempt)
{
  /* f(x) = a or q(y);  f(a) != a.  Symbols: 0 q, 1 a, 2 f. Vampire's name 1 stands for a = f(x). */
  const std::vector<std::string> symbols = {"1 1", "0 0", "1 0"};
  const std::vector<std::string> clauses = {
    "(clause (eq (f 2 (v 0)) (f 1)) (pos (f 0 (v 1))))",
    "(clause (ne (f 2 (f 1)) (f 1)))"};
  Replay replay;
  ASS(replay.start(handed(symbols, clauses)));
  auto feed = [&]() {
    replay.input(1, 0);
    replay.input(2, 1);
    replay.definition(1, clause(replay, "(clause (eq (f 1) (f 2 (v 0))))"));
    replay.definition(2, clause(replay, "(clause (pos (f 0 (v 0))))"));
    replay.component(11, 0);
    /* The component clause is used before the splitting is met: the name is given as Vampire writes the clause. */
    return replay.derive(20, {11, 2}, clause(replay, "(clause)"), {0}) && replay.split(10, 1, {1, 2});
  };

  /* The checker compares a group with a named clause literal by literal, and no step turns an equation round. */
  ASS(!feed());
  ASS(replay.worthAnotherAttempt());
  replay.restart();
  ASS_EQ(replay.steps(), 0u);
  ASS(feed());
  ASS(!replay.worthAnotherAttempt());
  ASS(contains(replay.certificate(), "component (clause (eq (f 2 (v 0)) (f 1)))"));
}

/**
 * Feeds the replay a refutation as Vampire could find it for a statement
 * whose negation has, among the clauses the checker builds, an inequality
 * of a term with itself under a name, and the name: the initial clauses
 * are the units 1, 2, ..., and the empty clause follows from two of them
 * (a resolution on the name and the inequality removed). Every pair is
 * tried, since which two they are is the checker's business. Returns the
 * unit that is the empty clause, or 0.
 */
static unsigned refuteFromTwoInputs(Replay& replay)
{
  unsigned count = (unsigned)replay.initialClauses();
  for (unsigned i = 0; i < count; i++) replay.input(i + 1, (int)i);
  Replay::Clause empty;
  ASS(replay.parseClause("(clause)", empty));
  for (unsigned i = 1; i <= count; i++)
    for (unsigned j = i + 1; j <= count; j++)
      if (replay.derive(100, {i, j}, empty)) return 100;
  return 0;
}

TEST_FUN(the_checker_accepts_a_rebuilt_refutation_and_rejects_it_altered)
{
  qr_init();

  /* "Every element of S is equal to itself": the negation gives an
   * element c with c != c, among the clauses the checker builds. */
  std::string item = "$\\displaystyle \\forall x \\in S\\ (x = x)$";
  QrVerdict handedOver = qr_clauses_item(item.c_str(), item.c_str() + item.size());
  ASS(handedOver.logic != nullptr);
  std::string text = handedOver.logic;
  Replay replay;
  ASS(replay.start(text));
  unsigned refuting = refuteFromTwoInputs(replay);
  ASS(refuting != 0);
  ASS(replay.refutes(refuting));
  ASS_EQ(replay.steps(), 2u);

  const char* why = "";
  std::string certificate = replay.certificate();
  ASS(proof_check_certificate(certificate.c_str(), &why) == PROOF_CHECK_ACCEPTED);

  /* The same steps for another statement, and the certificate without its step. */
  std::string other = certificate;
  size_t statement = other.find("\nstatement ");
  ASS(statement != std::string::npos);
  size_t line = other.find('\n', statement + 1);
  other = other.substr(0, statement) + "\nstatement (not " + other.substr(statement + 11, line - statement - 11) + ")" + other.substr(line);
  ASS(proof_check_certificate(other.c_str(), &why) != PROOF_CHECK_ACCEPTED);

  std::string cut = certificate;
  size_t step = cut.find("\nstep ");
  ASS(step != std::string::npos);
  cut = cut.substr(0, step) + "\nend\n";
  ASS(proof_check_certificate(cut.c_str(), &why) != PROOF_CHECK_ACCEPTED);
}

TEST_FUN(a_refuted_request_for_an_example_is_certified_as_the_negation)
{
  qr_init();

  /* "There are a set S and an element a of S different from itself": no
   * example. The certificate must say "not ...", and the clauses are those
   * of the condition itself. */
  std::string item = "$\\displaystyle \\exists S\\ \\exists a \\in S\\ (a \\neq a)$";
  QrVerdict handedOver = qr_clauses_item(item.c_str(), item.c_str() + item.size());
  ASS(handedOver.logic != nullptr);
  std::string text = handedOver.logic;
  ASS(contains(text, "\nstatement (not "));

  Replay replay;
  ASS(replay.start(text));
  unsigned refuting = refuteFromTwoInputs(replay);
  ASS(refuting != 0);
  const char* why = "";
  ASS(proof_check_certificate(replay.certificate().c_str(), &why) == PROOF_CHECK_ACCEPTED);
}

TEST_FUN(a_statement_on_the_parts_of_a_set_comes_with_the_parts_to_try)
{
  qr_init();

  /* Induction, with the principle among the hypotheses: what is handed
   * over has the instances of the principle that can be proposed without a
   * search, and among them the part of the x with f(x) = x. */
  std::string item = "$\\displaystyle (z \\in S \\land s \\colon S \\to S \\land f \\colon S \\to S \\land "
                     "(\\forall X \\subseteq S\\ ((z \\in X \\land \\forall y \\in S\\ (y \\in X \\implies s(y) \\in X)) \\implies \\forall y \\in S\\ (y \\in X))) "
                     "\\land f(z)=z \\land (\\forall y \\in S\\ (f(s(y))=s(f(y))))) \\implies \\forall y \\in S\\ (f(y)=y)$";
  QrVerdict handedOver = qr_clauses_item(item.c_str(), item.c_str() + item.size());
  ASS(handedOver.logic != nullptr);
  std::string text = handedOver.logic;
  ASS(contains(text, "\ncomprehend 0 (clause (eq (v 0) (v 0)))\n"));
  ASS(contains(text, "\ncomprehend 0 (clause (ne (v 0) (v 0)))\n"));
  ASS(contains(text, "\ncomprehend 0 (clause (eq (f 2 (v 0)) (v 0)))\n"));

  /* The beginning of the certificate is everything before the list of
   * symbols, and the checker, reading it alone, has the clauses listed. */
  Replay replay;
  ASS(replay.start(text));
  ASS(contains(replay.certificate(), "comprehend 0 (clause (eq (f 2 (v 0)) (v 0)))\nend\n"));
  ASS(!contains(replay.certificate(), "symbols"));
  ASS(replay.initialClauses() > 0);

  /* Without a refutation the beginning alone is no certificate. */
  const char* why = "";
  ASS(proof_check_certificate(replay.certificate().c_str(), &why) != PROOF_CHECK_ACCEPTED);
}

TEST_FUN(a_statement_about_a_bijection_has_no_clauses_to_hand_over)
{
  qr_init();
  std::string item = "$\\displaystyle S \\sim S$";
  QrVerdict handedOver = qr_clauses_item(item.c_str(), item.c_str() + item.size());
  ASS(handedOver.logic == nullptr);
}
