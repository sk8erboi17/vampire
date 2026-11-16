/* INTERFACCIA DI engine_integrals.c: integrali: primitive, integrali definiti
 * e impropri (capitolo 30).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_integrals.c. Ciò che il modulo usa solo per sé non è qui: là è
 * static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_INTEGRALS_H
#define QUAERENS_ENGINE_INTEGRALS_H

#include "engine_foundations.h"
#include "engine_induction.h"

void frac_latex(Frac v, char *text, size_t size);
void term_latex(Frac coef, const char *body, char *text, size_t size);
Verdict prove_integral(const char *formula);

#endif /* QUAERENS_ENGINE_INTEGRALS_H */
