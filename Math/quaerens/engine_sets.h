/* INTERFACCIA DI engine_sets.c: relazioni tra insiemi: decisione per regioni,
 * verifica indipendente, dimostrazione scritta (capitoli 15-16).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_sets.c. Ciò che il modulo usa solo per sé non è qui: là è static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_SETS_H
#define QUAERENS_ENGINE_SETS_H

#include "engine_foundations.h"
#include "engine_induction.h"

Verdict prove_sets(const char *formula);
Verdict prove_parts(const char *formula);

#endif /* QUAERENS_ENGINE_SETS_H */
