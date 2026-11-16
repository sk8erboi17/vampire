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
  while (isspace((unsigned char)*ck_cursor)) ck_cursor++;
  if (!ck_word("certificate")) ck_reject("not the beginning of a certificate");
  else if (ck_word("arithmetic")) ck_a_read();
  else if (ck_word("infinite")) ck_g_read();
  else ck_reject("not the beginning of a certificate arithmetic or infinite");
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
