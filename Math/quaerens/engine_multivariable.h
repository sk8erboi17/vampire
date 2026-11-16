/* INTERFACCIA DI engine_multivariable.c: funzioni di più variabili: derivate
 * parziali, gradiente, hessiana, punti critici (capitoli 35-36).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_multivariable.c. Ciò che il modulo usa solo per sé non è qui: là è
 * static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_MULTIVARIABLE_H
#define QUAERENS_ENGINE_MULTIVARIABLE_H

#include "engine_foundations.h"
#include "engine_induction.h"

Verdict prove_partial(const char *formula);
int uses_partial_notation(const char *formula);

#endif /* QUAERENS_ENGINE_MULTIVARIABLE_H */
