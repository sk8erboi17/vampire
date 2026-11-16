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
 * @file Replay.hpp
 * Turns a refutation found by Vampire into a certificate that the
 * independent checker rechecks inference by inference.
 *
 * WHAT THE CHECKER CAN CHECK. A certificate "saturation" refutes the
 * negation of a statement. The checker builds the initial clauses itself
 * from the statement (negation normal form, Skolem functions, names for
 * subformulas, and a predicate per set for "is an element of it", since the
 * sets may be empty), and then follows explicit steps, each with its
 * parents, the literals involved, the substitution and the resulting
 * clause:
 *
 *     step resolve P LP Q LQ (subst ...) (clause ...)       resolution
 *     step reflex P LP (subst ...) (clause ...)             s != s removed
 *     step factor P LP LQ (subst ...) (clause ...)          two equal literals merged
 *     step super P LP FLIP Q LQ SIDE POSITION (subst ...) (clause ...)
 *                                                           an equation of P rewrites Q at one place
 *     step equalfactor P LP FLIP LQ OTHERFLIP (subst ...) (clause ...)
 *
 * It applies the substitution and recomputes the step; it does not search
 * and does not unify. The last clause must be the empty one.
 *
 * WHAT THIS CLASS DOES. Vampire is run on the very clauses the checker
 * builds (the engine hands them over, with the checker's numbers:
 * qr_clauses_item()). Its refutation is a list of inferences, each a clause
 * with its premises, in Vampire's own rules: resolution, superposition,
 * demodulation, subsumption resolution, equality resolution, and so on.
 * Each of them is an instance of the checker's five steps, or a short chain
 * of them (a demodulation is a superposition with a unit equation; a
 * subsumption resolution is a resolution whose other literals were already
 * there). Replay finds that instance: it tries the steps that could give
 * Vampire's clause from Vampire's premises, computing the substitution by
 * unification, and keeps the one whose result is Vampire's clause.
 *
 * THE SEARCH IS NOT TRUSTED, AND NEED NOT BE. Everything here is on the side
 * of whoever claims the proof. If a step is rebuilt wrongly, the checker
 * rejects the certificate; if an inference of Vampire is not an instance of
 * the five steps that this class can find, derive() fails and there is no
 * certificate. In both cases the theorem is simply not certified this way.
 * What makes it certified is the checker accepting the finished text, and
 * the checker reads only the text.
 *
 * SPLITTING. Vampire also splits (AVATAR): a clause C or D whose two parts
 * share no variable is replaced by two names, s1 for "C holds for all its
 * variables" and s2 for the same of D; the clause becomes the propositional
 * clause s1 or s2, the search goes on with C under the assumption s1, and a
 * SAT solver looks after the names. The checker has this too, in three
 * lines:
 *
 *     component (clause ...)       a new proposition b names the clause K:
 *                                  the clause "K or not b" is added
 *     complement J                 for a K that is one ground literal A:
 *                                  the clause "not A or b" is added
 *     step split P (groups (J SIGN LITERAL...) ...) (clause ...)
 *                                  the literals of P, grouped so that two
 *                                  groups share no variable, each group a
 *                                  named clause: the clause of the names
 *
 * and a clause of Vampire "C under the assumptions s1, not s2" is for the
 * checker the plain clause "C or not b1 or b2". With that reading every
 * inference of Vampire between clauses with assumptions is the same
 * inference between the checker's clauses, and the SAT solver's verdict
 * "these propositional clauses cannot all hold" is rebuilt here as a chain
 * of resolutions (propositional()), since the checker takes nobody's word
 * for an unsatisfiability.
 *
 * The terms, literals and clauses here mirror the checker's own (a term
 * reference is positive for a term, -1-v for the variable v, 0 for none; a
 * clause is kept normalised exactly as the checker normalises it), because
 * a step refers to literals by their position and to variables by their
 * number, and the result must be written literal by literal as the checker
 * will compute it.
 */

#ifndef __Proof_Replay__
#define __Proof_Replay__

#include <map>
#include <string>
#include <vector>

namespace Proof {

class Replay {
public:
  /** A literal: left = right for an equation (right != 0), left alone for a predicate atom; left == 0 is "true". */
  struct Literal {
    int left = 0, right = 0;
    bool negative = false;
  };

  /** A clause: a disjunction of literals whose variables, numbered from 0, are universal. */
  struct Clause {
    std::vector<Literal> literals;
    int variables = 0;
  };

  /** A symbol of the translation into clauses. */
  struct Symbol {
    int arity = 0;
    bool predicate = false;
  };

  /**
   * Reads what the engine hands over (Engine.h, qr_clauses_item()): the
   * beginning of the certificate, the symbols and the clauses the checker
   * will have when it has read that beginning. Returns false if the text
   * is not that.
   */
  bool start(const std::string& handedOver);

  const std::vector<Symbol>& symbols() const { return _symbols; }
  /** How many clauses the checker has before the first step; they have indices 0, 1, ... */
  int initialClauses() const { return _initial; }
  const Clause& clause(int index) const { return _clauses[index]; }

  /** The symbol and the arguments of a term (a positive reference), or the number of a variable (a negative one). */
  int symbolOf(int term) const { return _terms[term].symbol; }
  const std::vector<int>& argumentsOf(int term) const { return _terms[term].arguments; }
  static bool isVariable(int term) { return term < 0; }
  static int variableOf(int term) { return -term - 1; }

  /** Reads a clause written as the checker writes it, "(clause LITERAL...)". Returns false if it is not one. */
  bool parseClause(const std::string& text, Clause& clause);

  /** Says that the unit number @b unit of Vampire's proof is the initial clause number @b index. */
  void input(unsigned unit, int index) { _unitClause[unit] = index; }

  /**
   * Rebuilds one inference of Vampire: the unit @b unit, the clause
   * @b written under the assumptions @b levels, obtained from the units
   * @b premises. On success the unit has a clause of the certificate, and
   * the steps that give it are written. Returns false if no chain of steps
   * this class can find gives the clause from the premises; the certificate
   * is then of no use.
   *
   * An assumption is a split level of Vampire: 2(v-1) for "the component
   * named by the SAT variable v holds", 2(v-1)+1 for "it does not".
   */
  bool derive(unsigned unit, const std::vector<unsigned>& premises, const Clause& written,
              const std::vector<unsigned>& levels = {});

  /** Vampire's definition of a name: the SAT variable @b variable stands for the clause @b clause, for all its variables. */
  void definition(unsigned variable, const Clause& clause) { _components[variable].vampire = clause; }

  /**
   * Says that the unit is the component clause of the split level: the
   * named clause itself under the assumption of its name, or, for an odd
   * level, the opposite of a ground literal under the opposite assumption.
   * Nothing is written yet: see clauseOf().
   */
  void component(unsigned unit, unsigned level) { _componentUnit[unit] = level; }

  /**
   * Rebuilds a splitting: the unit @b unit is the propositional clause
   * @b names (v for the SAT variable v, -v for its negation) that Vampire
   * got from the clause of the unit @b parent. Returns false if the
   * checker's steps do not give that clause of names.
   */
  bool split(unsigned unit, unsigned parent, const std::vector<int>& names);

  /**
   * Says that the unit is the propositional clause @b names that Vampire
   * read off the unit @b parent, an empty clause under assumptions: for the
   * checker the two are one clause. Returns false if they are not.
   */
  bool contradiction(unsigned unit, unsigned parent, const std::vector<int>& names);

  /**
   * Rebuilds the verdict of the SAT solver: the propositional clauses of
   * the units @b premises cannot all hold, so the unit @b unit is the
   * empty clause. Returns false if no refutation by resolution is found
   * within the work allowed.
   */
  bool propositional(unsigned unit, const std::vector<unsigned>& premises);

  /** True if the unit has a clause in the certificate and that clause is the empty one. */
  bool refutes(unsigned unit) const;

  /**
   * True if split() failed only because a name had already been given to
   * the clause written with an equation the other way round, and giving
   * the name to the clause as that splitting has it might succeed: call
   * restart() and feed the same refutation again.
   */
  bool worthAnotherAttempt() const { return _again; }

  /**
   * Forgets every step and every unit, back to the initial clauses, and
   * keeps how the splittings that failed found their clauses written: on
   * this attempt those names are defined that way.
   */
  void restart();

  /** How many lines the checker has to follow: steps, and definitions of names. */
  unsigned steps() const { return (unsigned)_stepLines.size(); }

  /** The whole certificate: its beginning, the steps, "end". Meaningful after an inference refutes(). */
  std::string certificate() const;

private:
  struct Term {
    int symbol;
    std::vector<int> arguments;
  };
  enum class Rule { RESOLVE, REFLEX, FACTOR, SUPER, EQUALFACTOR };

  /** One step, as the checker reads it. */
  struct Step {
    Rule rule;
    int p = 0, lp = 0, q = 0, lq = 0, flip = 0, otherflip = 0, side = 0, position = 0;
    std::map<int, int> substitution;  // variable (numbered as the step numbers them) -> term
  };

  /**
   * A name of AVATAR: a clause that stands, for all its variables, behind
   * a proposition. It is known from Vampire's definition, and gets its
   * lines in the certificate the first time it is needed: the clause is
   * then written the way the certificate has it at that moment, because
   * the checker compares a group of a splitting with the named clause
   * literal by literal, an equation the same way round.
   */
  struct Component {
    Clause vampire;        // the clause as Vampire defines it
    bool defined = false;  // the certificate has its "component" line
    int number = -1;       // which component of the certificate it is, counting from 0
    int symbol = -1;       // the proposition b that names it
    Clause key;            // the clause K as the certificate defines it, normalised
    int definition = -1;   // index of the clause "K or not b"
    int complement = -1;   // index of the clause "not A or b" when K is one ground literal A; -1 otherwise
  };

  std::string _prefix;
  std::vector<Symbol> _symbols;
  std::vector<Term> _terms;                  // _terms[0] is not a term
  std::map<std::pair<int, std::vector<int>>, int> _termIndex;
  std::vector<Clause> _clauses;              // the clauses of the certificate, by index
  std::vector<std::string> _stepLines;       // the step that gave each clause after the initial ones
  int _initial = 0;
  std::map<unsigned, int> _unitClause;
  std::map<unsigned, Component> _components; // by Vampire's SAT variable
  std::map<unsigned, Clause> _preferred;     // a SAT variable -> its clause as a splitting that failed found it written
  bool _again = false;                       // a splitting failed and left a new entry in _preferred
  size_t _initialSymbols = 0;                // how many symbols the translation into clauses has, before any name
  std::map<int, unsigned> _symbolVariable;   // the proposition of a component -> its SAT variable
  std::map<unsigned, unsigned> _componentUnit; // a unit that is a component clause -> its split level
  int _componentCount = 0;
  unsigned _work = 0;                        // steps tried for the inference being rebuilt

  int term(int symbol, const std::vector<int>& arguments);
  bool parseTerm(const std::string& text, size_t& at, int& result);
  std::string printTerm(int term) const;
  std::string printClause(const Clause& clause) const;

  static int offsetOf(const Clause& first) { return first.variables > 64 ? first.variables : 64; }
  int instance(int term, int offset, const std::map<int, int>& substitution);
  Clause instances(const Clause& clause, int offset, const std::map<int, int>& substitution);
  Clause normal(const Clause& clause);
  int rename(int term, std::map<int, int>& names, int& used);
  static bool sameAtom(const Literal& a, const Literal& b);
  int replace(int term, int position, int& cursor, int expected, int replacement, bool& found);
  bool apply(const Step& step, Clause& result);

  bool unify(int a, int b, std::map<int, int>& bindings);
  int resolve(int term, const std::map<int, int>& bindings);
  bool occurs(int variable, int term, const std::map<int, int>& bindings);
  std::map<int, int> simultaneous(const std::map<int, int>& bindings);

  bool sameClause(const Clause& a, const Clause& b);
  bool matchLiterals(const Clause& a, const Clause& b, size_t at, std::vector<bool>& used,
                     std::map<int, int>& forward, std::map<int, int>& backward);
  bool matchTerms(int a, int b, std::map<int, int>& forward, std::map<int, int>& backward);

  int push(const Step& step, const Clause& result);
  int add(const std::string& line, const Clause& clause);
  int tidy(int index);
  int clauseOf(unsigned unit);
  bool isName(const Literal& literal) const;
  bool define(unsigned variable, const Clause& key);
  Component* named(unsigned variable);
  bool nameLiteral(unsigned level, Literal& literal);
  bool namesAre(int index, const std::vector<int>& names) const;
  bool inOrder(const Clause& group, const Clause& key, std::vector<int>& chosen, std::vector<bool>& used);
  int falsified(const std::vector<int>& pool, std::map<int, bool>& value);
  void pop(int clauses);
  void subterms(int term, int& cursor, std::vector<std::pair<int, int>>& found);
  int size(int term) const;
  bool placeInInstance(int term, int position, int& cursor, int& placed, const std::map<int, int>& substitution, int& result) const;
  bool reach(int from, const Clause& target, int depth, const std::vector<int>& equations, int& reached);
  bool tryStep(const Step& step, const Clause& target, int depth, const std::vector<int>& equations, int& reached);
};

} // namespace Proof

#endif // __Proof_Replay__
