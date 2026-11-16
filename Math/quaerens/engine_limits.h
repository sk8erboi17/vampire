/* INTERFACCIA DI engine_limits.c: limiti (capitolo 29).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_limits.c. Ciò che il modulo usa solo per sé non è qui: là è static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_LIMITS_H
#define QUAERENS_ENGINE_LIMITS_H

#include "engine_foundations.h"
#include "engine_induction.h"
#include "engine_intervals.h"

Range constant_range(Rat c);
Verdict prove_limit(const char *formula);

/* Il termine principale di una funzione vicino a un punto, da un lato, nelle
 * lettere t e L di 29a; oppure, se della serie non si conosce nessun
 * coefficiente, solo il suo resto: f = O(t^{e}), cioè |f| <= C t^{e} per t
 * piccolo (29b), come x^{-2} \sin x all'infinito. */
typedef struct {
    int found;     /* 1 se il termine principale, o il resto, è noto */
    int bound;     /* 1 se si conosce solo il resto: f = O(t^{e}), e sign non conta */
    int sign;      /* il segno del coefficiente c: +1 o -1 */
    Frac e, d;     /* gli esponenti di t e di L */
    int growth;    /* 0 senza fattore e^{G}; +1 o -1 se G tende a +\infty o a -\infty */
} LeadingTerm;

LeadingTerm limit_leading(const char *formula);

#endif /* QUAERENS_ENGINE_LIMITS_H */
