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
 * @file IndependentChecker.c
 * The translation unit of the independent checker (IndependentChecker.h).
 *
 * The checker's source is included whole, without its command-line main():
 * everything in it is static, and its one entry point, ck_check(), is
 * wrapped below. This file includes nothing else of the program, which is
 * the point: this is the only place where the checker is compiled, and
 * what uses it (the mathematical engine for its own proofs, the driver for
 * what Vampire finds) sees the two functions of the interface and nothing
 * of what is inside.
 */

#define CK_NO_MAIN
#include "Math/quaerens/checker.c"

#include <stdarg.h>

#include "IndependentChecker.h"

ProofCheck proof_check_next(const char** text, const char** why, long long steps)
{
  const char* reason = "";
  CkAnswer answer = ck_check(text, &reason, steps);
  if (why) *why = reason;
  return answer == CK_ACCEPTED ? PROOF_CHECK_ACCEPTED : answer == CK_REJECTED ? PROOF_CHECK_REJECTED : PROOF_CHECK_UNKNOWN;
}

ProofCheck proof_check_certificate(const char* certificate, const char** why)
{
  /* Zero asks for the checker's usual budget of work on a model. */
  const char* text = certificate;
  return proof_check_next(&text, why, 0);
}

ProofCheck proof_check_leaf(const char* certificate, const char** why)
{
  /* The only place where a certificate with one leaf of one part is read
   * as complete (ck_g_partial of 20g): the text cannot ask for it. */
  ck_g_partial = 1;
  ProofCheck answer = proof_check_certificate(certificate, why);
  ck_g_partial = 0;
  return answer;
}

/* ------------------------------------------------------------------------
 * The clauses of a certificate "arithmetic", for whoever writes one
 * ------------------------------------------------------------------------
 *
 * A text that grows, on the heap. A failed allocation leaves it NULL. */
typedef struct { char* text; size_t length, capacity; } ProofText;

static void proof_put(ProofText* out, const char* format, ...)
{
  if (!out->text && out->capacity) return;
  va_list arguments;
  va_start(arguments, format);
  int needed = vsnprintf(NULL, 0, format, arguments);
  va_end(arguments);
  if (needed < 0) return;
  if (out->length + (size_t)needed + 1 > out->capacity) {
    size_t capacity = 2 * (out->length + (size_t)needed + 1);
    char* grown = realloc(out->text, capacity);
    if (!grown) { free(out->text); out->text = NULL; out->capacity = 1; return; }
    out->text = grown;
    out->capacity = capacity;
  }
  va_start(arguments, format);
  vsnprintf(out->text + out->length, out->capacity - out->length, format, arguments);
  va_end(arguments);
  out->length += (size_t)needed;
}

/* A term of the checker's clauses, as the checker reads one: (v N) or (f N T...). */
static void proof_put_term(ProofText* out, int term)
{
  if (term < 0) { proof_put(out, "(v %d)", -term - 1); return; }
  CkRTerm t = ck_r.term[term];
  proof_put(out, "(f %d", t.symbol);
  for (int i = 0; i < t.count; i++) {
    proof_put(out, " ");
    proof_put_term(out, ck_r.argument[t.first + i]);
  }
  proof_put(out, ")");
}

/* A set of numbers in the notation of chapter 20: (set [ge L | gt L] [except P/Q]...). */
static void proof_put_set(ProofText* out, const CkNSet* set)
{
  proof_put(out, "(set");
  if (set->bounded) proof_put(out, " %s %lld", set->strict ? "gt" : "ge", set->low);
  for (int i = 0; i < set->holes; i++)
    proof_put(out, " except %lld/%lld", (long long)set->hole[i].num, (long long)set->hole[i].den);
  proof_put(out, ")");
}

/* A statement about numbers in the notation of chapter 20, as the checker reads it back. */
static void proof_put_numbers(ProofText* out, const CkNNode* n)
{
  static const char* const words[] = {
    [CK_N_FORALL] = "forall", [CK_N_EXISTS] = "exists", [CK_N_AND] = "and", [CK_N_OR] = "or", [CK_N_IMPLIES] = "implies",
    [CK_N_IFF] = "iff", [CK_N_NOT] = "not", [CK_N_EQ] = "=", [CK_N_NEQ] = "neq", [CK_N_LESS] = "less",
    [CK_N_LESSEQ] = "lesseq", [CK_N_IN] = "in", [CK_N_DIVIDES] = "divides", [CK_N_ADD] = "add", [CK_N_SUB] = "sub",
    [CK_N_NEG] = "neg", [CK_N_MUL] = "mul", [CK_N_POW] = "pow"};
  switch (n->kind) {
    case CK_N_NUMBER: proof_put(out, "%lld", n->value); return;
    case CK_N_VAR: proof_put(out, "(var %lld)", n->value); return;
    case CK_N_FORALL: case CK_N_EXISTS:
      proof_put(out, "(%s (var %lld) ", words[n->kind], n->value);
      proof_put_set(out, &n->set);
      proof_put(out, " ");
      proof_put_numbers(out, n->a);
      proof_put(out, ")");
      return;
    case CK_N_IN:
      proof_put(out, "(in ");
      proof_put_numbers(out, n->a);
      proof_put(out, " ");
      proof_put_set(out, &n->set);
      proof_put(out, ")");
      return;
    case CK_N_POW:
      proof_put(out, "(pow ");
      proof_put_numbers(out, n->a);
      proof_put(out, " %lld)", n->value);
      return;
    case CK_N_NOT: case CK_N_NEG:
      proof_put(out, "(%s ", words[n->kind]);
      proof_put_numbers(out, n->a);
      proof_put(out, ")");
      return;
    default:
      proof_put(out, "(%s ", words[n->kind] ? words[n->kind] : "?");
      proof_put_numbers(out, n->a);
      proof_put(out, " ");
      proof_put_numbers(out, n->b);
      proof_put(out, ")");
      return;
  }
}

char* proof_arithmetic_clauses(const char* beginning, const char** why)
{
  ck_begin(beginning, 0);
  ck_g_claim = NULL;
  ck_g_partial = 1;   /* a beginning with parts has one leaf (20g) */
  while (isspace((unsigned char)*ck_cursor)) ck_cursor++;
  if (!ck_word("certificate")) ck_reject("not the beginning of a certificate");
  else if (ck_word("arithmetic")) ck_a_read();
  else if (ck_word("infinite")) ck_g_read();
  else ck_reject("not the beginning of a certificate arithmetic or infinite");
  ck_g_partial = 0;
  if (ck_status == CK_ACCEPTED && !ck_r.started) ck_reject("the beginning has no line clausify");

  ProofText out = {0};
  if (ck_status == CK_ACCEPTED) {
    if (ck_g_claim) {
      proof_put(&out, "claim ");
      proof_put_numbers(&out, ck_g_claim);
      proof_put(&out, "\n");
    }
    proof_put(&out, "numerals");
    for (int i = 0; i < ck_a_numerals; i++) proof_put(&out, " %lld", ck_a_numeral[i]);
    proof_put(&out, "\nsymbols %d\n", ck_r.symbols);
    for (int i = 0; i < ck_r.symbols; i++) proof_put(&out, "%d %d\n", ck_r.symbol[i].arity, ck_r.symbol[i].predicate);
    proof_put(&out, "clauses %d\n", ck_r.clauses);
    for (int i = 0; i < ck_r.clauses; i++) {
      CkRClause c = ck_r.clause[i];
      proof_put(&out, "(clause");
      for (int j = 0; j < c.count; j++) {
        CkRLiteral l = c.literal[j];
        if (!l.left) { proof_put(&out, l.negative ? " (false)" : " (true)"); continue; }
        proof_put(&out, " (%s ", l.right ? (l.negative ? "ne" : "eq") : (l.negative ? "neg" : "pos"));
        proof_put_term(&out, l.left);
        if (l.right) { proof_put(&out, " "); proof_put_term(&out, l.right); }
        proof_put(&out, ")");
      }
      proof_put(&out, ")\n");
    }
  }
  if (why) *why = ck_reason;
  ck_finish();
  return out.text;
}

/* ------------------------------------------------------------------------
 * The parts of the claim of a certificate "infinite", and their cases
 * ------------------------------------------------------------------------
 *
 * None of this is trusted: the checker reads the atoms and leaves it is
 * given, and checks that they cover every case and that every leaf is
 * refuted (20g). Here they are only proposed. */

/* 1 if the trees a and b are the same, node by node. */
static int proof_same(const CkNNode* a, const CkNNode* b)
{
  if (!a || !b) return a == b;
  if (a->kind != b->kind || a->value != b->value) return 0;
  if (a->kind == CK_N_IN && memcmp(&a->set, &b->set, sizeof a->set) != 0) return 0;
  return proof_same(a->a, b->a) && proof_same(a->b, b->b) && proof_same(a->c, b->c);
}

/* t with every (cases C E F) whose condition is a decided atom replaced by
 * the case it gives: atom[i] has the value decided[i] (1, 0, or -1 for
 * undecided). */
static const CkNNode* proof_decide(const CkNNode* t, const CkNNode* const* atom, const int* decided, int atoms)
{
  if (!t || ck_status != CK_ACCEPTED) return t;
  if (t->kind == CK_N_CASES) {
    const CkNNode* condition = proof_decide(t->c, atom, decided, atoms);
    for (int i = 0; i < atoms; i++)
      if (decided[i] >= 0 && proof_same(condition, atom[i]))
        return proof_decide(decided[i] ? t->a : t->b, atom, decided, atoms);
    CkNNode* copy = ck_n_node(CK_N_CASES);
    *copy = *t;
    copy->c = condition;
    copy->a = proof_decide(t->a, atom, decided, atoms);
    copy->b = proof_decide(t->b, atom, decided, atoms);
    return copy;
  }
  CkNNode* copy = ck_n_node(t->kind);
  *copy = *t;
  copy->a = proof_decide(t->a, atom, decided, atoms);
  copy->b = proof_decide(t->b, atom, decided, atoms);
  return copy;
}

/* The condition of the innermost and leftmost (cases C E F) of t whose C
 * has no cases and names only letters of the chain, or NULL. */
static const CkNNode* proof_next_case(const CkNNode* t, const long long* letters, int count)
{
  if (!t) return NULL;
  const CkNNode* found = proof_next_case(t->c, letters, count);
  if (!found) found = proof_next_case(t->a, letters, count);
  if (!found) found = proof_next_case(t->b, letters, count);
  if (!found && t->kind == CK_N_CASES && ck_g_atom_ok(t->c, letters, count)) found = t->c;
  return found;
}

typedef struct {
  const CkNNode* atom[CK_G_ATOMS];
  int decided[CK_G_ATOMS], atoms;
  char leaf[CK_G_LEAVES][CK_G_ATOMS + 1];
  int leaves, failed;
  const long long* letters;
  int count;
} ProofCases;

/* The leaves of the part under the decisions so far: split on the next case. */
static void proof_split(ProofCases* cases, const CkNNode* part)
{
  if (cases->failed || ck_status != CK_ACCEPTED) return;
  const CkNNode* decided = proof_decide(part, cases->atom, cases->decided, cases->atoms);
  const CkNNode* next = proof_next_case(decided, cases->letters, cases->count);
  if (!next) {
    if (cases->leaves == CK_G_LEAVES) { cases->failed = 1; return; }
    for (int i = 0; i < cases->atoms; i++) cases->leaf[cases->leaves][i] = cases->decided[i] < 0 ? '.' : cases->decided[i] ? '+' : '-';
    cases->leaf[cases->leaves][cases->atoms] = 0;
    cases->leaves++;
    return;
  }
  int i = 0;
  while (i < cases->atoms && !proof_same(cases->atom[i], next)) i++;
  if (i == cases->atoms) {
    if (cases->atoms == CK_G_ATOMS) { cases->failed = 1; return; }
    cases->atom[cases->atoms] = next;
    cases->decided[cases->atoms++] = -1;
  }
  for (int value = 1; value >= 0; value--) {
    cases->decided[i] = value;
    proof_split(cases, part);
  }
  cases->decided[i] = -1;
}

char* proof_infinite_cases(const char* beginning, const char** why)
{
  /* The parts, as the checker makes them: read the beginning with a first
   * leaf of part 0, which also translates that leaf. */
  size_t length = strlen(beginning);
  char* text = malloc(length + 64);
  if (!text) { if (why) *why = "no memory"; return NULL; }
  memcpy(text, beginning, length);
  strcpy(text + length, "part 0\nleaf\nclausify forward\nend\n");
  ck_begin(text, 0);
  ck_g_partial = 1;
  while (isspace((unsigned char)*ck_cursor)) ck_cursor++;
  if (!ck_word("certificate") || !ck_word("infinite")) ck_reject("not the beginning of a certificate infinite");
  else ck_g_read();
  ck_g_partial = 0;

  ProofText out = {0};
  if (ck_status == CK_ACCEPTED) {
    proof_put(&out, "parts %d\n", ck_g_conjuncts);
    for (int k = 0; k < ck_g_conjuncts && ck_status == CK_ACCEPTED; k++) {
      long long letters[CK_N_QUANTIFIERS];
      int count = 0;
      ck_g_leaf_claim(ck_g_conjunct[k], NULL, letters, &count);
      ProofCases* cases = calloc(1, sizeof *cases);
      if (!cases) break;
      cases->letters = letters;
      cases->count = count;
      proof_split(cases, ck_g_conjunct[k]);
      proof_put(&out, "part %d\n", k);
      if (cases->failed) {
        /* Too many cases to list: the part as one leaf, which may still be refuted. */
        proof_put(&out, "leaf\n");
      } else {
        for (int i = 0; i < cases->atoms; i++) {
          proof_put(&out, "atom ");
          proof_put_numbers(&out, cases->atom[i]);
          proof_put(&out, "\n");
        }
        for (int l = 0; l < cases->leaves; l++) {
          proof_put(&out, "leaf ");
          proof_put(&out, "%s", cases->leaf[l]);
          for (int i = (int)strlen(cases->leaf[l]); i < cases->atoms; i++) proof_put(&out, ".");
          proof_put(&out, "\n");
        }
      }
      free(cases);
    }
  }
  if (why) *why = ck_reason;
  ck_finish();
  free(text);
  return out.text;
}

