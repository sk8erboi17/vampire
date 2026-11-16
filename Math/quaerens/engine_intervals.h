/* INTERFACCIA DI engine_intervals.c: i numeri reali come intervalli con
 * l'errore garantito (capitolo 24).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_intervals.c. Ciò che il modulo usa solo per sé non è qui: là è
 * static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_INTERVALS_H
#define QUAERENS_ENGINE_INTERVALS_H

#include "engine_foundations.h"
#include "parser.h"

/* Un numero reale noto a meno di un errore: sta tra low e high, compresi.
 * Invariante: low <= high, tutti e due finiti; altrimenti vuol dire "non
 * so". */
typedef struct {
    double low, high;
} Range;

Range range_none(void);
int range_known(Range r);
Range range_wide(double low, double high);
Range range_ratio(__int128 num, __int128 den);
Range range_neg(Range a);
Range range_add(Range a, Range b);
Range range_mul(Range a, Range b);
Range range_sub(Range a, Range b);
Range range_div(Range a, Range b);
Range range_ln2(void);
Range range_ln(Range a);
Range range_exp_at(double v);
Range range_exp(Range a);
Range range_sqrt(Range a);
Range range_atan(Range a);
Range range_pi(void);
Range range_asin(Range a);
Range range_from_half_pi(Range b);
void range_sin_cos(Range a, Range *sine, Range *cosine);
int range_side(Range r, int *side);
Range range_power(Range a, long long e);
Range node_range(const Node *node, int name, Range x, int *undefined);
Range poly_range(Poly p);

#endif /* QUAERENS_ENGINE_INTERVALS_H */
