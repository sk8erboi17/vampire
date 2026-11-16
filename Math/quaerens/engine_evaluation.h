/* INTERFACCIA DI engine_evaluation.c: le successioni note come dati, la
 * valutazione di un albero in una frazione, i test di annullamento (capitoli
 * 10-12).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_evaluation.c. Ciò che il modulo usa solo per sé non è qui: là è
 * static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_EVALUATION_H
#define QUAERENS_ENGINE_EVALUATION_H

#include "engine_foundations.h"
#include "parser.h"

/* Una successione del vocabolario. */
typedef struct {
    int name;                   /* lettera con cui compare (pedice), o '!' */
    const char *definition;     /* 10a: formula in m; NULL nel caso 10b */
    int order;                  /* 10b: ordine d della ricorrenza */
    long long coef[MAX_ORDER];  /* 10b: coefficienti, dal termine più recente */
    long long init[MAX_ORDER];  /* 10b: X(0), ..., X(d-1) */
    Node *tree;                 /* 10a: la definizione già analizzata */
} Sequence;

extern Sequence library[3];

#define LIBRARY_COUNT ((int)(sizeof library / sizeof *library))

extern size_t arena_keep;
void engine_init(void);

/* Un legame numerico: name e il nome della variabile, value la frazione
 * negli atomi che la sostituisce. I polinomi di value sono posseduti
 * dall'arena della valutazione; la cella del legame non li libera. */
typedef struct {
    int name;
    Rat value;
} Binding;

extern int env_count;
Binding *env_at(int index);
extern int library_depth;
extern long long default_base;
extern long long domain_floor;
extern int point_name[MAX_POINT];
extern Frac point_value[MAX_POINT];
extern int point_count;
int env_push(int name, Rat value);
void env_pop(void);
const Rat *env_lookup(int name);

/* Un indice che nasconde una variabile dell'ambiente dentro una somma.
 * name e il nome locale, outer il contesto esterno preso in prestito.
 * La cella vive nel frame ricorsivo che la possiede: una cella per indice,
 * senza copiare un vettore sempre piu lungo a ogni livello. */
typedef struct NameScope NameScope;
struct NameScope { int name; const NameScope *outer; };

int name_shadowed(const NameScope *scope, int name);
Rat eval_body(const Node *node, Rat index);
int atom_is_nonnegative(int atom);
int atom_is_real(int atom);
int poly_is_real(Poly p);
extern int binomial_ok, binomial_used, binomial_live;
void term_times(Term *out, int atom, Frac exp);
int pop_prime(long long *value, long long *prime, long long *times);
Mono poly_common(Poly p);
int mono_is_integer(const Mono *m);
int rational_roots(const long long *c, int degree, Frac *root);
Rat fractional_power(Rat base, Frac q, int odd);
Rat logarithm(Rat x);
Rat logarithm_of_positive(Rat x);
extern Rat atan_args[MAX_ATOMS];
extern int atan_count;
Rat arctangent(Rat x);
Rat exp_i(Rat theta, int sign);
extern const Node *abs_node[MAX_ABS];
extern int abs_count;
extern unsigned abs_pattern;
extern const Node *surd_node[MAX_SURDS];
extern int surd_letter[MAX_SURDS];
extern Rat surd_inside[MAX_SURDS], surd_value[MAX_SURDS];
extern int surd_count;
int number_divides(Num u, Num v);

/* Una scelta di caso per un'applicazione definita per casi: f(t) vale il
 * caso piece. La fa la dimostrazione dopo aver dimostrato la condizione del
 * caso (18v-1), oppure la impone per tentativo chi cerca un valore e poi
 * ricontrolla tutto (18v-3). Vale solo per quel nodo e per quel valore di t,
 * che cambia con le variabili legate. */
typedef struct {
    const Node *node;  /* l'applicazione f(t), nell'albero dell'enunciato */
    Rat argument;      /* il valore di t quando il caso è stato scelto */
    int piece;         /* il caso: un indice di piece[] nell'applicazione */
} CaseChoice;

extern CaseChoice case_choice[MAX_CASE_CHOICES];
extern int case_choice_count;
extern const char *const CASE_UNDECIDED;
extern const Map *undecided_map;
extern const Node *undecided_node;
extern Rat undecided_argument;
int rat_same(Rat a, Rat b);
int condition_computed(const Formula *c);
int case_computed(const Map *map, Rat argument);
Rat eval(const Node *node);
int poly_vanishes(Poly p);
Rat difference(const Statement *statement, Rat n);
int vanishes_where_defined(const Statement *statement, const Node *source, Rat n);

#endif /* QUAERENS_ENGINE_EVALUATION_H */
