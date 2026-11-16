/* INTERFACCIA DI engine_quantifiers.c: enunciati con quantificatori sui
 * numeri: le regole di dimostrazione (capitoli da 18 a 18.7).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_quantifiers.c. Ciò che il modulo usa solo per sé non è qui: là è
 * static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_QUANTIFIERS_H
#define QUAERENS_ENGINE_QUANTIFIERS_H

#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"

extern _Thread_local int universal_count;
extern _Thread_local unsigned char *universal_named;
extern _Thread_local size_t universal_named_capacity;
int universal_push(Bound bound);
extern _Thread_local int split_modulus, split_case;
extern _Thread_local int search_left;

/* Un valore dato a una variabile per dimostrare un "esiste". */
typedef struct {
    int name;     /* la lettera */
    Frac value;   /* il numero scelto */
} Choice;

extern _Thread_local Choice *chosen;
extern _Thread_local int chosen_count;
extern _Thread_local int chosen_by_cases;
extern _Thread_local int region_depth;
extern _Thread_local int excluded_count;
void choose(int name, Frac value);
extern _Thread_local int record_count, hypotheses_named;
void put_numbers(const NumberSet *set);
void put_poly(Poly p);
Poly poly_negate(Poly p);
int poly_is_constant(Poly p);
int poly_uses(Poly p, int x);
extern _Thread_local int power_letters;
int power_exponent(const Mono *m);
int power_letter(int atom);
int rat_polynomials(Rat r, Poly *num, Poly *den);
int closed_gap(const Formula *source);
int node_uses_letter(const Node *node, int name);
int formula_uses_letter(const Formula *f, int name);
extern _Thread_local int split_pending;
int establish_in_regions(Formula *body, int negated, int from);
int case_point(const Map *map, int piece, Frac *point);

/* Una parte di una disgiunzione da dimostrare, con il segno con cui va
 * letta: la disgiunzione vale quando vale una delle sue parti. */
typedef struct {
    Formula *source;  /* la condizione */
    int negated;      /* 1 se va presa negata */
} Leaf;

/* Ciò che 18u-3 ha affermato trovando un valore, annotato perché la verifica
 * del capitolo 19 lo ricontrolli con i numeri (record_holds()). Un'istanza
 * dice: per ogni valore delle variabili generiche per cui le parti `leaf`
 * della disgiunzione sono tutte false (cioè le ipotesi valgono), i valori
 * `value` degli "esiste" `quantifier` stanno nei loro insiemi e rendono vera
 * `body`, letta con il segno `sign`.
 *
 * Le espressioni, i nodi e gli insiemi a cui punta stanno nell'arena e negli
 * alberi della dimostrazione in corso: valgono finché questa non riparte. */
typedef struct {
    int generics;                    /* variabili generiche, in generic[] */
    Bound *generic;        /* nell'ordine in cui la verifica dà loro un valore: prima
                                        i testimoni a cui 18u-1 ha dato un nome, poi le altre;
                                        il vettore e posseduto dall'arena della dimostrazione */
    int bindings;                    /* variabili legate a un valore, in binding[] */
    Binding *binding;        /* quelle di env in quel momento: il valore è
                                        un'espressione nelle variabili generiche;
                                        il vettore e posseduto dall'arena */
    int leaves;                      /* parti della disgiunzione, in leaf[] */
    Leaf leaf[MAX_LEAVES];           /* tutte tranne quella dell'"esiste" */
    int names;                       /* "esiste" a cui è stato dato un valore, da 1 a MAX_NAMED */
    Formula *quantifier[MAX_NAMED];  /* i loro nodi, dal più esterno */
    Rat value[MAX_NAMED];            /* i valori: espressioni nelle variabili generiche */
    const Formula *body;             /* la condizione che segue gli "esiste" */
    int sign;                        /* 1 se body va presa negata */
} WitnessRecord;

extern _Thread_local WitnessRecord witness_records[MAX_RECORDS];
int letter_only_in_exponents(const Formula *f, int letter);
int map_defined(const Map *map);
int prove_claims(Formula *f);

/* Una condizione "modulus divide dividend" di un enunciato deciso sui resti. */
typedef struct {
    const Formula *source;  /* il nodo F_DIVIDES o F_IN, oppure l'uguaglianza
                               sotto un "esiste k" che dice la stessa cosa */
    long long modulus;      /* D, positivo */
    Poly dividend;          /* N, a coefficienti interi */
} Congruence;

extern _Thread_local Congruence congruences[MAX_CONGRUENCES];
extern _Thread_local int congruence_count;
extern _Thread_local long long residue_period;
extern _Thread_local int *residue_name;
extern _Thread_local long long *residue_value;
extern _Thread_local int residue_count;
int names_a_multiple(const Formula *f);
int congruences_read(const Formula *f, int *deepest);
int residue_holds(const Formula *f);

#endif /* QUAERENS_ENGINE_QUANTIFIERS_H */
