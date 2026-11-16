/* INTERFACCIA DI engine_indices.c: identità con gli indici: il conto su tutti
 * i valori (capitolo 38).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_indices.c. Ciò che il modulo usa solo per sé non è qui: là è static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_INDICES_H
#define QUAERENS_ENGINE_INDICES_H

#include "engine_foundations.h"
#include "engine_induction.h"

Verdict prove_indices(const char *formula);
int uses_index_notation(const char *formula);

#endif /* QUAERENS_ENGINE_INDICES_H */
