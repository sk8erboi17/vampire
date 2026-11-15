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
 * @file ProofNarrator.cpp
 * Implements the account of a refutation described in ProofNarrator.hpp.
 */

#include "ProofNarrator.hpp"

#include <cctype>
#include <set>
#include <sstream>
#include <vector>

#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Environment.hpp"
#include "Lib/SharedSet.hpp"
#include "Math/Names.hpp"
#include "Saturation/Splitter.hpp"

namespace Humanizer {

using namespace Kernel;

namespace {

using Math::latexEscape;
using Math::latexName;

/** The name of a symbol as mathematics (see Math/Names.hpp). */
std::string symbolName(const std::string& name) { return latexName(name).latex; }

/** Text made safe for LaTeX. */
std::string escape(const std::string& text) { return latexEscape(text); }

/**
 * Writes formulas, clauses and terms of plain first-order logic as LaTeX.
 * Anything else (terms that contain formulas, polymorphic symbols, sorts
 * with arguments) clears ok: the caller then shows the unit as Vampire
 * prints it, rather than risk writing something it does not say.
 */
struct Printer {
  bool ok = true;

  std::string variable(unsigned number) { return "x_{" + std::to_string(number) + "}"; }

  std::string term(TermList t)
  {
    if (t.isVar()) {
      if (t.isSpecialVar()) ok = false;
      return variable(t.var());
    }
    const Term* term = t.term();
    if (term->isSpecial() || term->isSort() || term->numTypeArguments() > 0) { ok = false; return ""; }
    Math::LatexName name = latexName(env.signature->functionName(term->functor()));
    std::string result = name.latex;
    if (term->arity() == 0) return result;

    /* An operation is written between its arguments, as in the source; an
     * argument that is itself such an operation gets its parentheses. */
    if (name.infix && term->arity() == 2) return infixArgument(*term->nthArgument(0)) + " " + name.latex + " " + infixArgument(*term->nthArgument(1));
    result += "(";
    for (unsigned i = 0; i < term->arity(); i++) {
      if (i) result += ", ";
      result += this->term(*term->nthArgument(i));
    }
    return result + ")";
  }

  /** An argument of an infix operation: in parentheses if it is an infix operation too. */
  std::string infixArgument(TermList t)
  {
    bool nested = t.isTerm() && !t.term()->isSpecial() && !t.term()->isSort() && t.term()->arity() == 2
               && latexName(env.signature->functionName(t.term()->functor())).infix;
    return nested ? "(" + term(t) + ")" : term(t);
  }

  std::string literal(const Literal* literal)
  {
    if (literal->isEquality())
      return term(*literal->nthArgument(0)) + (literal->polarity() ? " = " : " \\neq ") + term(*literal->nthArgument(1));
    if (literal->numTypeArguments() > 0) { ok = false; return ""; }
    Math::LatexName name = latexName(env.signature->predicateName(literal->functor()));
    if (name.infix && literal->arity() == 2) {
      /* An order relation, as it was written: a \le b, and its negation in parentheses. */
      std::string relation = term(*literal->nthArgument(0)) + " " + name.latex + " " + term(*literal->nthArgument(1));
      return literal->polarity() ? relation : "\\lnot (" + relation + ")";
    }
    std::string result = literal->polarity() ? "" : "\\lnot ";
    result += name.latex;
    if (literal->arity() == 0) return result;
    result += "(";
    for (unsigned i = 0; i < literal->arity(); i++) {
      if (i) result += ", ";
      result += term(*literal->nthArgument(i));
    }
    return result + ")";
  }

  /** A formula used as an operand: in parentheses unless it is atomic, a negation or a constant. */
  std::string operand(const Formula* formula)
  {
    Connective connective = formula->connective();
    bool plain = connective == LITERAL || connective == NOT || connective == TRUE || connective == FALSE;
    return plain ? this->formula(formula) : "(" + this->formula(formula) + ")";
  }

  std::string formula(const Formula* formula)
  {
    switch (formula->connective()) {
      case LITERAL: return literal(formula->literal());
      case TRUE:    return "\\top";
      case FALSE:   return "\\bot";
      case NOT:     return "\\lnot " + operand(formula->uarg());
      case AND:
      case OR: {
        std::string result;
        const char* sign = formula->connective() == AND ? " \\land " : " \\lor ";
        for (const FormulaList* args = formula->args(); args; args = args->tail()) {
          if (!result.empty()) result += sign;
          result += operand(args->head());
        }
        return result;
      }
      case IMP: return operand(formula->left()) + " \\implies " + operand(formula->right());
      case IFF: return operand(formula->left()) + " \\iff " + operand(formula->right());
      case XOR: return "\\lnot (" + operand(formula->left()) + " \\iff " + operand(formula->right()) + ")";
      case FORALL:
      case EXISTS: {
        std::string result;
        for (const VSList* vars = formula->vars(); vars; vars = vars->tail()) {
          TermList sort = vars->head().second;
          result += formula->connective() == FORALL ? "\\forall " : "\\exists ";
          result += variable(vars->head().first);
          if (sort.isVar() || sort.term()->arity() > 0) { ok = false; return ""; }

          /* The default sort of individuals is not a set of the statement: it is not written. */
          if (sort != AtomicSort::defaultSort()) result += " \\in " + symbolName(env.signature->typeConName(sort.term()->functor()));
          result += "\\ ";
        }
        return result + operand(formula->qarg());
      }
      default:
        ok = false;
        return "";
    }
  }

  /** A clause: the disjunction of its conditions, the contradiction if it has none. */
  std::string clause(Clause* clause)
  {
    if (clause->isEmpty()) return "\\bot";
    std::string result;
    for (unsigned i = 0; i < clause->length(); i++) {
      if (i) result += " \\lor ";
      result += literal((*clause)[i]);
    }
    return result;
  }
};

/** A rule of Vampire and what it does, in the two languages. */
struct RuleText {
  const char* rule;
  const char* english;
  const char* italian;
};

/* Checklist: the names are the ones returned by Kernel::ruleName(). A rule
 * that is not here is cited by its name: add a line only with a sentence
 * that says what the rule does, never what one would like it to do. */
const RuleText RULES[] = {
  {"conjecture_negation",
   "The claim is denied: this is the assumption to be refuted.",
   "Si nega la tesi: \\`e l'assunzione da confutare."},
  {"rectify",
   "The variables are renamed, so that each quantifier has its own.",
   "Le variabili sono rinominate, una diversa per ogni quantificatore."},
  {"flattening",
   "Nested conjunctions, disjunctions and negations are rewritten in flat form.",
   "Congiunzioni, disgiunzioni e negazioni annidate sono riscritte in forma piatta."},
  {"ennf_transformation",
   "Implications are rewritten and negations are moved inwards, down to atoms and equivalences.",
   "Le implicazioni sono riscritte e le negazioni portate all'interno, fino agli atomi e alle equivalenze."},
  {"nnf_transformation",
   "Negations are moved inwards down to the atoms (negation normal form).",
   "Le negazioni sono portate all'interno fino agli atomi (forma normale negativa)."},
  {"skolemize",
   "Each ``there exists'' is replaced by a new name for the element that exists (a Skolem symbol), which depends on the universally quantified variables before it.",
   "Ogni ``esiste'' \\`e sostituito da un nome nuovo per l'elemento che esiste (un simbolo di Skolem), che dipende dalle variabili universali che lo precedono."},
  {"cnf_transformation",
   "The formula is split into clauses: each is a disjunction that holds for all values of its variables.",
   "La formula \\`e spezzata in clausole: ognuna \\`e una disgiunzione che vale per ogni valore delle sue variabili."},
  {"true_and_false_elimination",
   "The constants true and false are simplified away.",
   "Le costanti vero e falso sono semplificate."},
  {"resolution",
   "Resolution: for suitable values of the variables one clause contains a condition and the other its negation; what remains of the two is put together.",
   "Risoluzione: per valori opportuni delle variabili una clausola contiene una condizione e l'altra la sua negazione; si mette insieme ci\\`o che resta delle due."},
  {"factoring",
   "Factoring: for suitable values of the variables two conditions of the clause become the same, and are merged.",
   "Fattorizzazione: per valori opportuni delle variabili due condizioni della clausola diventano la stessa, e si fondono."},
  {"superposition",
   "Superposition: an equation of one clause is used to replace equals by equals inside the other.",
   "Superposizione: un'equazione di una clausola \\`e usata per sostituire uguali con uguali dentro l'altra."},
  {"forward_demodulation",
   "Rewriting with an equation: a term is replaced by an equal one.",
   "Riscrittura con un'equazione: un termine \\`e sostituito da uno uguale."},
  {"backward_demodulation",
   "Rewriting with an equation: a term is replaced by an equal one.",
   "Riscrittura con un'equazione: un termine \\`e sostituito da uno uguale."},
  {"equality_resolution",
   "An inequality whose two sides become the same for suitable values of the variables is false there, and is removed.",
   "Una disuguaglianza i cui due membri diventano uguali per valori opportuni delle variabili l\\`i \\`e falsa, e si toglie."},
  {"equality_factoring",
   "Equality factoring: two equations of the clause with the same side are merged, at the price of an inequality between the other sides.",
   "Fattorizzazione dell'uguaglianza: due equazioni della clausola con lo stesso membro si fondono, al prezzo di una disuguaglianza tra gli altri membri."},
  {"trivial_inequality_removal",
   "A condition of the form $t \\neq t$ is false, and is removed.",
   "Una condizione della forma $t \\neq t$ \\`e falsa, e si toglie."},
  {"duplicate_literal_removal",
   "A condition written twice is kept once.",
   "Una condizione scritta due volte si tiene una volta."},
  {"forward_subsumption_resolution",
   "Subsumption resolution: a condition of the clause is contradicted by the other clause, which asks nothing more than the rest, and is removed.",
   "Risoluzione con sussunzione: una condizione della clausola \\`e contraddetta dall'altra clausola, che non chiede nulla di pi\\`u del resto, e si toglie."},
  {"backward_subsumption_resolution",
   "Subsumption resolution: a condition of the clause is contradicted by the other clause, which asks nothing more than the rest, and is removed.",
   "Risoluzione con sussunzione: una condizione della clausola \\`e contraddetta dall'altra clausola, che non chiede nulla di pi\\`u del resto, e si toglie."},
  {"unit_resulting_resolution",
   "All the conditions of a clause but one are contradicted by the other clauses: that one remains.",
   "Tutte le condizioni di una clausola tranne una sono contraddette dalle altre clausole: resta quella."},
  {"definition_unfolding",
   "A defined symbol is replaced by its definition.",
   "Un simbolo definito \\`e sostituito dalla sua definizione."},
  {"predicate_definition_unfolding",
   "A defined relation is replaced by its definition.",
   "Una relazione definita \\`e sostituita dalla sua definizione."},
  {"predicate_definition_introduction",
   "A new relation is introduced as a name for a part of the formula.",
   "Si introduce una relazione nuova come nome di una parte della formula."},
  {"avatar_definition",
   "A name is given to a part of a clause that shares no variable with the rest, so that cases can be distinguished on it.",
   "Si d\\`a un nome a una parte di clausola che non ha variabili in comune con il resto, per poter distinguere i casi su di essa."},
  {"avatar_split_clause",
   "The clause is split into parts with no variable in common: at least one of the named parts holds.",
   "La clausola \\`e divisa in parti senza variabili in comune: almeno una delle parti nominate vale."},
  {"avatar_component_clause",
   "This is what holds in the case in which the named part holds.",
   "\\`E ci\\`o che vale nel caso in cui vale la parte nominata."},
  {"avatar_contradiction_clause",
   "A contradiction was reached under the case assumptions listed: they cannot all hold.",
   "Si \\`e arrivati a una contraddizione sotto le assunzioni di caso elencate: non possono valere tutte."},
  {"avatar_sat_refutation",
   "The combinations of cases excluded so far leave no case open: there is a contradiction in every case.",
   "Le combinazioni di casi escluse fin qui non lasciano aperto nessun caso: c'\\`e una contraddizione in ogni caso."},
  {"condensation",
   "The clause is replaced by a special case of itself that has fewer conditions and says as much.",
   "La clausola \\`e sostituita da un suo caso particolare che ha meno condizioni e dice altrettanto."},
};

} // namespace

std::string ProofNarrator::latex(Unit* unit)
{
  Printer printer;
  std::string result;
  if (unit->isClause()) {
    Clause* clause = unit->asClause();
    result = printer.clause(clause);
    if (printer.ok && clause->splits() && clause->splits()->size() > 0) {
      /* A clause derived inside a case distinction holds only under the
       * assumptions of its cases: they are part of what it says. */
      result += " \\quad [";
      for (unsigned i = 0; i < clause->splits()->size(); i++) {
        if (i) result += ",\\ ";
        result += "\\texttt{" + escape(Saturation::Splitter::getFormulaStringFromName((*clause->splits())[i])) + "}";
      }
      result += "]";
    }
  } else {
    result = printer.formula(static_cast<FormulaUnit*>(unit)->formula());
  }
  if (printer.ok) return result;

  /* Outside plain first-order syntax: exactly what Vampire prints. */
  std::string printed = unit->isClause() ? unit->asClause()->literalsOnlyToString()
                                         : static_cast<FormulaUnit*>(unit)->formula()->toString();
  return "\\texttt{" + escape(printed) + "}";
}

std::string ProofNarrator::ruleSentence(const std::string& rule) const
{
  bool italian = _language == Math::Language::ITALIAN;
  for (const RuleText& text : RULES)
    if (rule == text.rule) return italian ? text.italian : text.english;
  return (italian ? "Per la regola \\texttt{" : "By the rule \\texttt{") + escape(rule) + (italian ? "} di Vampire." : "} of Vampire.");
}

std::string ProofNarrator::narrate(Unit* refutation) const
{
  bool italian = _language == Math::Language::ITALIAN;

  /* The steps: everything the refutation rests on, in the order of
   * derivation. Vampire numbers a formula when it derives it, so a premise
   * always has a smaller number than what follows from it. */
  auto byNumber = [](Unit* left, Unit* right) { return left->number() < right->number(); };
  std::set<Unit*, decltype(byNumber)> steps(byNumber);
  std::vector<Unit*> pending = {refutation};
  while (!pending.empty()) {
    Unit* unit = pending.back();
    pending.pop_back();
    if (!steps.insert(unit).second) continue;
    UnitIterator parents = unit->getParents();
    while (parents.hasNext()) pending.push_back(parents.next());
  }

  /* The readers' numbers, 1, 2, 3, ...; Vampire's own are shown beside them. */
  std::map<const Unit*, unsigned> position;
  bool hasClaim = false;
  for (Unit* unit : steps) {
    position[unit] = (unsigned)position.size() + 1;
    UnitInputType type = unit->inputType();
    if (unit->inference().rule() == InferenceRule::INPUT && (type == UnitInputType::CONJECTURE || type == UnitInputType::NEGATED_CONJECTURE))
      hasClaim = true;
  }

  std::ostringstream out;
  if (italian) {
    out << "\\textbf{Dimostrazione trovata da Vampire, per assurdo.} "
        << (hasClaim ? "Si suppongono vere le ipotesi e falsa la tesi, e si arriva a una contraddizione. "
                     : "Dalle assunzioni si arriva a una contraddizione: non possono valere tutte. ")
        << "Ogni passo \\`e un'inferenza della refutazione trovata da Vampire: la formula ottenuta, che cosa fa la regola usata, "
           "e i passi a cui \\`e stata applicata. In una clausola (una disgiunzione di condizioni) le variabili "
           "$x_{0}, x_{1}, \\dots$ indicano elementi qualsiasi. Tra parentesi quadre il numero del passo nella prova di Vampire.\n";
  } else {
    out << "\\textbf{Proof found by Vampire, by contradiction.} "
        << (hasClaim ? "We assume the hypotheses and deny the claim, and reach a contradiction. "
                     : "From the assumptions we reach a contradiction: they cannot all hold. ")
        << "Each step is one inference of the refutation Vampire found: the formula obtained, what the rule does, "
           "and the steps it was applied to. In a clause (a disjunction of conditions) the variables "
           "$x_{0}, x_{1}, \\dots$ stand for arbitrary elements. In square brackets, the number of the step in Vampire's proof.\n";
  }

  out << "\\begin{enumerate}\n";
  for (Unit* unit : steps) {
    out << "\\item[(" << position[unit] << ")] $" << latex(unit) << "$\\\\\n{\\small ";

    UnitIterator parents = unit->getParents();
    std::vector<unsigned> from;
    while (parents.hasNext()) from.push_back(position[parents.next()]);

    auto label = _labels.find(unit);
    if (label != _labels.end()) {
      out << label->second << ".";
    } else if (from.empty()) {
      /* An input, or a formula Vampire introduced: its own name for it. */
      std::string name = unit->inference().name();
      if (unit->inference().rule() == InferenceRule::INPUT) out << (italian ? "Dato del problema (" : "Given in the problem (") << escape(name) << ").";
      else out << ruleSentence(name);
    } else {
      out << ruleSentence(ruleName(unit->inference().rule()));
    }

    if (!from.empty()) {
      out << (italian ? " Da " : " From ");
      for (size_t i = 0; i < from.size(); i++) {
        if (i) out << (i + 1 == from.size() ? (italian ? " e " : " and ") : ", ");
        out << "(" << from[i] << ")";
      }
      out << ".";
    }
    if (unit->inference().satPremise()) {
      out << (italian ? " Il passo poggia su una refutazione proposizionale del SAT solver sui casi, che qui non \\`e riportata."
                      : " The step rests on a propositional refutation by the SAT solver over the cases, which is not spelled out here.");
    }
    out << " {\\scriptsize [" << unit->number() << "]}}\n";
  }
  out << "\\end{enumerate}\n";

  unsigned last = position[refutation];
  if (italian) {
    out << "Il passo (" << last << ") \\`e la contraddizione"
        << (hasClaim ? ": le ipotesi e la negazione della tesi non possono valere insieme, quindi la tesi segue dalle ipotesi."
                     : ": le assunzioni non possono valere insieme.");
  } else {
    out << "Step (" << last << ") is the contradiction"
        << (hasClaim ? ": the hypotheses and the negation of the claim cannot hold together, so the claim follows from the hypotheses."
                     : ": the assumptions cannot hold together.");
  }
  out << "\n";
  return out.str();
}

} // namespace Humanizer
