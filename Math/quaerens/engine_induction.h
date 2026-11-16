/* INTERFACCIA DI engine_induction.c: induzione su somme e prodotti: caso base,
 * passo, verdetto (capitolo 13).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_induction.c. Ciò che il modulo usa solo per sé non è qui: là è
 * static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_INDUCTION_H
#define QUAERENS_ENGINE_INDUCTION_H

#include "engine_foundations.h"
#include "parser.h"

/* Esito di un tentativo di dimostrazione. */
typedef enum { PROVED, REFUTED, NOT_PROVED, UNSUPPORTED, SOLVED } Outcome;

/* Il verdetto su un enunciato, di qualunque tipo.
 *
 * I campi variable, base e witness riguardano le dimostrazioni per induzione;
 * per gli altri enunciati variable vale 0, method dice come sono stati
 * dimostrati e il controesempio, se c'è, è il testo in detail. Le stringhe
 * puntate non appartengono al verdetto: method e note sono costanti; reason,
 * detail, proof e certificate restano valide fino al verdetto successivo. */
typedef struct {
    Outcome outcome;
    int variable;        /* variabile di induzione, o 0 */
    long long base;      /* PROVED per induzione: il caso base n0 */
    long long witness;   /* REFUTED per induzione: un n in cui non vale */
    const char *reason;  /* NOT_PROVED, UNSUPPORTED: perché, in italiano;
                            PROVED per induzione o con la tabella dei
                            segni, REFUTED e SOLVED con la tabella dei
                            segni, senza certificato: perché il certificato
                            manca; altrimenti NULL */
    const char *detail;  /* REFUTED senza induzione: il controesempio, o NULL;
                            SOLVED: le soluzioni, come condizione in LaTeX */
    const char *proof;   /* dimostrazione scritta in LaTeX, o NULL */
    const char *method;  /* PROVED senza induzione, SOLVED: come, in italiano */
    const char *note;    /* PROVED, REFUTED: avvertenza su come è stato letto
                            l'enunciato, o NULL;
                            SOLVED: che cosa indicano i nomi usati nelle
                            soluzioni, o dove vale una derivata, o NULL */
    const char *certificate;  /* PROVED: il certificato che il verificatore
                                 indipendente ha accettato (13h, 18p-15), o NULL;
                                 REFUTED su insiemi qualsiasi: il controesempio,
                                 come certificato accettato (28f); REFUTED e
                                 SOLVED con la tabella dei segni: la tabella,
                                 come certificato accettato (18p-15) */
} Verdict;

extern _Thread_local char *proof_text;
extern _Thread_local size_t proof_length, proof_capacity;
extern _Thread_local int proof_growable, proof_broken;
extern _Thread_local int unjustified_steps;
void proof_reset(void);
void proof_add(const char *format, ...);
int atom_is_positive(int atom, long long base);
int condition_holds(Requirement kind, Poly p, long long base, long long *where);
int condition_decided(const Condition *c, long long base, long long *where);
int defined_for_every(const Statement *statement, long long base, long long *where, const char **why);

/* Ciò che un conto di prova lascia dietro di sé e che va tolto quando il
 * conto non serve più: gli atomi, le basi e le arcotangenti nati durante il
 * conto, e la memoria presa dall'arena. */
typedef struct {
    int atoms, polys, atans;  /* quanti ce n'erano prima del conto */
    size_t arena;             /* byte dell'arena occupati prima del conto */
} Scratch;

Scratch scratch_mark(void);
void scratch_drop(Scratch mark);
void put_frac(Frac v);
extern _Thread_local int shown_name;
extern _Thread_local const Node *shown_value;
void put_node(const Node *n, int need);
Node *node_affine(long long a, int variable, long long c);
extern _Thread_local int unwritable;
void put_atom(int atom, Frac exp);
extern _Thread_local int surd_powers;
void put_mono(const Mono *m);
void put_terms(Poly p);
void put_rat(Rat r);

/* Un pezzo del testo della dimostrazione in corso: i caratteri [from, to) di
 * proof_text. È una formula appena scritta, che si vuole poter rileggere. */
typedef struct {
    size_t from, to;
} Span;

void proof_cut(size_t length);
Span put_side(const Node *side, const Node *value);
int put_value(const char *prefix, Rat r, Span *span);
int reread_equal(Span a, Span b, long long base);
Rat side_value(const Node *side, Rat n);
int put_new_terms(long long base);
extern _Thread_local char *certificate_text;
extern _Thread_local size_t certificate_length, certificate_capacity;
extern _Thread_local int certificate_broken;
void engine_texts_init(void);
extern _Thread_local unsigned certificate_sequences;
extern _Thread_local char certificate_problem[256];
extern _Thread_local int cert_signs;
extern _Thread_local int cert_real;
extern _Thread_local int cert_declared;
void cert_add(const char *format, ...);
void cert_letter(long long name);
void cert_node(const Node *n);
int brick_fits(const Atom *a);
void cert_base(const Atom *a);
void cert_frac(Frac c);
extern const char *const NOT_AN_EQUALITY;
Verdict induct(const Statement *input, int variable, int has_base, long long base, int nested);
Verdict prove_by_induction(const char *formula, int variable, int has_base, long long base);

#endif /* QUAERENS_ENGINE_INDUCTION_H */
