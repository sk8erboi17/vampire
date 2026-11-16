/* INTERFACCIA DI engine_quantifiers_verdict.c: enunciati con quantificatori:
 * verifica indipendente e verdetto (capitolo 19).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_quantifiers_verdict.c. Ciò che il modulo usa solo per sé non è qui:
 * là è static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_QUANTIFIERS_VERDICT_H
#define QUAERENS_ENGINE_QUANTIFIERS_VERDICT_H

#include "engine_foundations.h"
#include "parser.h"
#include "engine_induction.h"

void forget_choices(Formula *f);
Verdict prove_quantified(const char *formula);
int divisions_by_numbers(const Node *node);

#endif /* QUAERENS_ENGINE_QUANTIFIERS_VERDICT_H */
