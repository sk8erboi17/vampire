/* INTERFACCIA DI engine_derivatives.c: derivate: dimostrarle, calcolarle,
 * usarle negli studi di funzione (capitolo 27).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_derivatives.c. Ciò che il modulo usa solo per sé non è qui: là è
 * static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_DERIVATIVES_H
#define QUAERENS_ENGINE_DERIVATIVES_H

#include "engine_foundations.h"
#include "parser.h"
#include "engine_induction.h"
#include "engine_intervals.h"

extern _Thread_local int derivative_signs;
extern _Thread_local int derivative_edges;
extern const char *const DERIVATIVE_EDGES;
extern const char *const NOT_A_DERIVATIVE;
Node *node_fold(const Node *tree, int *closed);
Node *derive(const Node *f, int x);
Node *sample_tree(const Node *tree, int x, int order, long long at);

/* Quante derivate di f, oltre quella del caso base, vengono calcolate una
 * dopo l'altra per confrontarle con la formula; il più grande caso base
 * ammesso, perché ogni derivata allunga l'albero; la lunghezza oltre la
 * quale si smette di derivare; e quindi l'ordine più alto di una derivata
 * controllata con i numeri. */
#define DIRECT_ORDERS 3
#define MAX_DERIVATIVE_BASE 4
#define MAX_DERIVATIVE_NODES 20000
#define MAX_JET (MAX_DERIVATIVE_BASE + DIRECT_ORDERS)

/* Una funzione vicino a x0, data dai primi coefficienti della sua serie di
 * Taylor: c[k] contiene f^(k)(x0) / k!. Invariante, per le serie che
 * jet_eval() ritorna: se c[0] è "non so" lo sono tutti, e la serie dice "non
 * so". */
typedef struct {
    int order;             /* K: il grado più alto tenuto, da 0 a MAX_JET */
    Range c[MAX_JET + 1];  /* i coefficienti da 0 a order; gli altri non contano */
} Jet;

Jet jet_eval(const Node *node, int x, Range at, int order);
Range sample_value(const Node *tree, int x, Range at);
int numbers_agree(Range a, Range b);
long long node_count(const Node *tree);
Node *derivatives_expanded(Node *tree);
void formula_derivatives_expanded(Formula *f);
int derivative_identity(const Node *left, const Node *right, const Node *function, int order, long long base, int x);
const char *calculus_certificate(const char *kind, int x, const char *order, const Node *function, const Node *claim,
                                        const Node *lower, const Node *upper, const Node *value);
void calculus_certify(Verdict *verdict, const char *why, const Node *function, int x);
Node *node_tidy(const Node *tree);

/* Le regole di derivazione, per dire quale ha dato una riga: quelle da 27c
 * a 27f, in testa al capitolo.
 *
 * Warning: se aggiungi una regola a derive(), aggiungila qui, in
 * explain_rules(), e la sua frase in put_explanation_steps() (capitolo 41,
 * output.c). */
typedef enum {
    RULE_SUM,          /* somme, differenze, segno meno: termine per termine */
    RULE_FACTOR,       /* un fattore o un divisore che non contiene la variabile */
    RULE_PRODUCT,      /* (u v)' = u' v + u v' */
    RULE_QUOTIENT,     /* (u / v)' = (u' v - u v') / v^2 */
    RULE_POWER,        /* (u^c)' = c u^{c-1} u' */
    RULE_EXPONENTIAL,  /* (c^u)' = c^u ln(c) u' */
    RULE_TOWER,        /* u^v = e^{v ln u} */
    RULE_FUNCTION      /* f(u)' = f'(u) u', con f una funzione */
} DerivativeRule;

Verdict prove_derivative(const char *formula, int variable, int has_base, long long base);
const char *derivative_doubt(const Formula *thesis);

#endif /* QUAERENS_ENGINE_DERIVATIVES_H */
