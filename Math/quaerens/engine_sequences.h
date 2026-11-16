/* INTERFACCIA DI engine_sequences.c: induzione su una disuguaglianza,
 * successioni definite per ricorrenza (capitoli 25-26).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_sequences.c. Ciò che il modulo usa solo per sé non è qui: là è
 * static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_SEQUENCES_H
#define QUAERENS_ENGINE_SEQUENCES_H

#include "engine_foundations.h"
#include "parser.h"
#include "engine_induction.h"

Verdict ask_method(Verdict (*method)(const char *), const char *question, const char *short_text, int keep);
Verdict prove_inequality(const char *formula, int variable, int has_base, long long base);
Node *node_replace(const Node *tree, int name, Node *value);
int node_has_variable(const Node *tree, int name);
Span put_comparison(const Node *lhs, Relation rel, const Node *rhs);
Verdict prove_sequence(const char *formula, int variable, int has_base, long long base);
Verdict decide_iterates(const Formula *thesis);

#endif /* QUAERENS_ENGINE_SEQUENCES_H */
