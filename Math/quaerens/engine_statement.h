/* INTERFACCIA DI engine_statement.c: dimostrare un enunciato: quale capitolo
 * lo legge, e il verdetto (capitolo 20).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_statement.c. Ciò che il modulo usa solo per sé non è qui: là è
 * static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_STATEMENT_H
#define QUAERENS_ENGINE_STATEMENT_H

#include "engine_foundations.h"
#include "engine_induction.h"

void verdict_print(FILE *out, const Verdict *verdict);
Verdict prove(const char *formula, int variable, int has_base, long long base);
Verdict prove_item(const char *item, const char *end);

#endif /* QUAERENS_ENGINE_STATEMENT_H */
