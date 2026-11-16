/* INTERFACCIA DI engine_sign_tables.c: la tabella dei segni: punti esatti,
 * segni, righe, soluzioni, grafici, un parametro (capitoli 18.8-18.19).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_sign_tables.c. Ciò che il modulo usa solo per sé non è qui: là è
 * static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_SIGN_TABLES_H
#define QUAERENS_ENGINE_SIGN_TABLES_H

#include "engine_foundations.h"
#include "parser.h"
#include "engine_induction.h"

/* Un razionale con numeratore e denominatore a 128 bit: i punti in cui si
 * dimezza un intervallo hanno denominatori che crescono in fretta.
 * Invariante: den > 0 e la frazione è ridotta. */
typedef struct {
    __int128 num, den;  /* il numeratore, con il segno, e il denominatore */
} Wide;

extern const char *const SIGN_LIMIT;

/* Un polinomio in una variabile a coefficienti interi:
 * c[0] + c[1] x + ... + c[degree] x^degree. Invariante: c[degree] non è
 * zero; il polinomio nullo ha degree -1. */
typedef struct {
    int degree;
    __int128 c[MAX_UNI + 1];
} Uni;

int uni_divide(const Uni *a, const Uni *b, Uni *q);
int uni_sign_at(const Uni *p, Wide x);
int uni_from_poly(Poly p, int x, Uni *out, int *shift);
extern Uni sign_base[2 * MAX_CRITICAL];
extern int sign_bases;
void text_add(char *text, size_t size, const char *format, ...);
void put_wide(Wide v);
void uni_latex(const Uni *p, int name, char *text, size_t size);
void put_uni(const Uni *p, int name);
int quadratic_latex(const Uni *q, int smaller, char *text, size_t size);

/* Un punto in cui può cambiare la verità dell'enunciato. Se exact è 1 il
 * punto è il razionale low (uguale a high). Altrimenti, se element non è
 * negativo, è la sola radice di sign_base[element] tra low e high, che non
 * sono radici, ed è irrazionale. Altrimenti è il numero kappa[kappa], che
 * non è radice di nessun polinomio (un logaritmo, per esempio): di lui si
 * sa solo che sta tra low e high. */
typedef struct {
    int exact;       /* 1 se il punto è il razionale low */
    Wide low, high;  /* l'intervallo chiuso che contiene il punto */
    int element;     /* il posto in sign_base[] del polinomio di cui è la sola
                        radice tra low e high; -1 per un punto esatto o kappa */
    int kappa;       /* il posto in kappa[]; -1 se il punto è una radice */
} Critical;

extern int kappas;
extern int spaces;
extern Critical sign_point[MAX_POINTS];
extern int sign_points_count;
int uni_quadratic_factor(const Uni *p, Uni *factor, Uni *rest);
long long lcm_small(long long a, long long b);
int exp_letters(const Node *node, Rat *out);
int exp_root(Rat r, long long index, Rat *out);
int log_letter(const Node *node, Rat *out);
extern int trig_on, trig_live, trig_at_pi, trig_bad;
int trig_value(const Node *node, Rat argument, Rat *out);
void abs_collect(const Node *node);
int sign_compare(const Formula *f, const int *sign, int *defined);
int sign_truth(const Formula *f, const int *sign);
int number_sign(Rat r, int *side);

/* Una riga della tabella dei segni (18p-2): un punto, oppure l'intervallo tra
 * due punti consecutivi. La riga 2 i è l'intervallo prima del punto i, la
 * riga 2 i + 1 il punto i; l'ultima è l'intervallo dopo l'ultimo punto. */
typedef struct {
    Wide sample;             /* il valore della variabile in cui si calcolano i
                                segni: il punto, o un razionale dell'intervallo;
                                per una radice irrazionale il punto medio
                                dell'intervallo che la isola (18p-5) */
    int sign[MAX_CRITICAL];  /* il segno (-1, 0, 1) di ogni polinomio di sign_poly[] */
    int inside;              /* 1 se la riga sta nell'insieme su cui varia la variabile */
    int rational;            /* 1 se sample è proprio il valore della riga: è 0
                                solo nelle radici irrazionali */
    int must;                /* 1 se la riga va confermata perché l'enunciato si
                                possa decidere: le righe con un valore razionale,
                                e in un enunciato periodico gli intervalli */
    int confirmed;           /* 1 se il conto con i numeri in sample ha dato la
                                stessa verità della tabella */
} SignRow;

extern SignRow sign_row[2 * MAX_POINTS + 1];
extern int sign_rows;
extern char solution_text[1024], solution_note[512];
int point_is_first_root(int k);

/* Un pezzo dell'insieme in cui una condizione vale: righe consecutive della
 * tabella in cui è vera, cioè un punto solo oppure un intervallo. */
typedef struct {
    int first, last;              /* la prima e l'ultima riga */
    int low, high;                /* i punti che lo delimitano; -1 se da quella
                                     parte non ha limite. Per un punto solo
                                     sono lo stesso punto */
    int low_closed, high_closed;  /* 1 se l'estremo fa parte del pezzo */
} Piece;

int sign_piece(const Formula *f, int from, Piece *piece);
Formula *condition_reread(const char *text);
extern PlFigure *figure;
extern int figures_wanted;
void comparisons_collect(const Formula *f, const Formula **list, int *count);
int formula_needs_signs(const Formula *f);
const Formula *without_negations(const Formula *f, int *negated);
void decide_by_signs(const Formula *thesis, Verdict *verdict);
int sign_node_plain(const Node *node, int name);
void sign_certify(const Formula *thesis, Verdict *verdict);
Uni uni_scaled(const Uni *p, __int128 k);
int has_parameter(const Formula *thesis);
void decide_with_parameter(const Formula *thesis, Verdict *verdict);

#endif /* QUAERENS_ENGINE_SIGN_TABLES_H */
