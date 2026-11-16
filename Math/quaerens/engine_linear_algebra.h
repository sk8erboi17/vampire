/* INTERFACCIA DI engine_linear_algebra.c: algebra lineare esatta: matrici,
 * determinanti, sistemi lineari (capitoli 32-33).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_linear_algebra.c. Ciò che il modulo usa solo per sé non è qui: là è
 * static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_LINEAR_ALGEBRA_H
#define QUAERENS_ENGINE_LINEAR_ALGEBRA_H

#include "engine_foundations.h"
#include "engine_induction.h"

extern const char *const LETTER_CASES;
Verdict prove_matrix(const char *formula);
int uses_matrices(const char *formula);
Verdict prove_parameter(const char *formula);
Verdict prove_linear(const char *formula);
int uses_linear_systems(const char *formula);

#endif /* QUAERENS_ENGINE_LINEAR_ALGEBRA_H */
