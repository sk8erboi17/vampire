/* INTERFACCIA DI engine_explanation.c: la spiegazione: i passaggi registrati e
 * ricontrollati (capitolo 40).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_explanation.c. Ciò che il modulo usa solo per sé non è qui: là è
 * static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_EXPLANATION_H
#define QUAERENS_ENGINE_EXPLANATION_H

#include "engine_foundations.h"
#include "parser.h"
#include "engine_induction.h"

#define EXPLAIN_BYTES 65536     /* testo di una spiegazione, tutte le formule insieme */
#define MAX_EXPLAIN_STEPS 200   /* passi di una spiegazione */
#define MAX_EXPLAIN_POINTS 12   /* punti di una tabella che si spiega: di più non sta in una pagina */
#define MAX_EXPLAIN_COLUMNS (2 * MAX_EXPLAIN_POINTS + 1)
#define MAX_EXPLAIN_FACTORS 24  /* fattori diversi di una tabella che si spiega */
#define MAX_EXPLAIN_LINES (MAX_EXPLAIN_FACTORS + 2 * MAX_PANELS + 3)

/* I tipi di passo di una spiegazione. Che cosa portano i campi di un passo
 * è scritto accanto a ogni tipo; un campo non nominato vale zero o NULL.
 *
 * Warning: se aggiungi un tipo, aggiungi la sua frase in put_explanation()
 * (capitolo 41, output.c). */
typedef enum {
    EXPLAIN_ASK,         /* che cosa si chiede: text[0] la condizione (il primo
                            membro, se l'enunciato è un'equivalenza), text[1]
                            l'insieme su cui varia la variabile, text[2] il
                            secondo membro di un'equivalenza */
    EXPLAIN_COMPARISON,  /* comincia il lavoro sul confronto numero group:
                            text[0] il confronto com'è scritto, count in quante
                            colonne non ha un valore, text[1] quali */
    EXPLAIN_MOVE,        /* tutto a un membro: text[0] la differenza dei due
                            membri, text[1] il segno di confronto con lo zero */
    EXPLAIN_COMBINE,     /* la stessa come una sola frazione di polinomi:
                            text[0] e text[1] come sopra, flag 1 se ha un
                            denominatore */
    EXPLAIN_FACTOR,      /* numeratore e denominatore scomposti in fattori:
                            text[0], text[1] e flag come sopra */
    EXPLAIN_ZERO,        /* gli zeri di un fattore: text[0] il fattore, count
                            quanti zeri (0, 1 o 2), text[1] e text[2] gli
                            zeri; se count è 0, flag è il segno del fattore */
    EXPLAIN_POINTS,      /* i punti della tabella, in ordine: count quanti,
                            text[0] l'elenco */
    EXPLAIN_TABLE,       /* la tabella dei segni: sta nei campi della spiegazione */
    EXPLAIN_TEST,        /* un valore di prova per il confronto numero group:
                            text[0] il valore della variabile, text[1] e
                            text[2] i valori dei due membri, text[3] il segno
                            di confronto, flag 1 se lì il confronto vale */
    EXPLAIN_DERIVE,      /* la derivata di un pezzo dell'espressione (27n):
                            text[0] il pezzo, text[1] la sua derivata, flag
                            la regola usata (DerivativeRule), count la
                            funzione se la regola è RULE_FUNCTION, group 1 se
                            serve anche la regola della catena */
    EXPLAIN_VALUE,       /* un caso di un enunciato per induzione (40b):
                            text[0] il valore di n, text[1] e text[2] i
                            valori dei due membri */
    EXPLAIN_BASE,        /* il caso base: text[0] e text[1] i due membri con
                            il numero al posto di n, text[2] e text[3] i loro
                            valori */
    EXPLAIN_HYPOTHESIS,  /* l'ipotesi induttiva: text[0] l'enunciato */
    EXPLAIN_TARGET,      /* un membro dell'enunciato scritto per n + 1, da cui
                            parte una catena: text[0] il membro, group 1 se è
                            il primo, 2 se è il secondo */
    EXPLAIN_REWRITE,     /* un passaggio della catena: text[0] la nuova forma,
                            flag che cosa si è fatto (ExplainRewrite), group
                            come sopra */
    EXPLAIN_ANSWER       /* la risposta. Per un'induzione: count 1 se il passo
                            è svolto nei passi che precedono. Per una
                            derivata: text[0] la derivata. Per una richiesta
                            di soluzioni:
                            text[0] le soluzioni, count 0, oppure 1 se sono
                            tutti i valori, 2 se nessuno. Per un "per ogni" o
                            un "esiste": flag 1 se l'enunciato è vero, count 1
                            se una colonna lo decide da sola, e allora text[0]
                            è quella colonna (NULL se la tabella ne ha una sola) */
} ExplainKind;

/* Un passo di una spiegazione: un fatto che il motore ha stabilito e
 * ricontrollato, con le formule che lo dicono. Le formule sono testi LaTeX
 * dentro il deposito della spiegazione (Explanation.text). */
typedef struct {
    ExplainKind kind;
    int group;            /* il confronto a cui si riferisce, da 1; 0 se a tutti */
    int count, flag;      /* secondo il tipo: vedi ExplainKind */
    const char *text[4];  /* secondo il tipo: vedi ExplainKind */
} ExplainStep;

/* Che cosa dice una riga della tabella di una spiegazione. */
typedef enum {
    EXPLAIN_LINE_FACTOR,      /* il segno di un fattore */
    EXPLAIN_LINE_VALUE,       /* il segno della differenza dei due membri di un
                                 confronto, o che lì non ha un valore */
    EXPLAIN_LINE_COMPARISON,  /* se un confronto vale */
    EXPLAIN_LINE_CONDITION,   /* se vale la condizione spiegata, quando non è un
                                 solo confronto */
    EXPLAIN_LINE_CLAIM,       /* se vale il secondo membro di un'equivalenza */
    EXPLAIN_LINE_AGREE        /* se i due membri di un'equivalenza dicono lo stesso */
} ExplainLineKind;

/* Una riga della tabella di una spiegazione: una casella per colonna. */
typedef struct {
    ExplainLineKind kind;
    int group;           /* EXPLAIN_LINE_VALUE, EXPLAIN_LINE_COMPARISON: il confronto, da 1 */
    const char *label;   /* la formula di cui la riga parla, o NULL se la riga
                            è di un tipo che si dice a parole */
    signed char cell[MAX_EXPLAIN_COLUMNS];
} ExplainLine;

/* Che cosa chiede l'enunciato spiegato: le soluzioni di una condizione, che
 * valga per ogni valore, che valga per uno, una derivata (27n), oppure
 * un'uguaglianza per ogni n, dimostrata per induzione (40b). */
typedef enum { EXPLAIN_SOLVE, EXPLAIN_FORALL, EXPLAIN_EXISTS, EXPLAIN_DERIVATIVE, EXPLAIN_INDUCTION } ExplainRequest;

/* La spiegazione di un enunciato: come ci si arriva, un passo alla volta.
 * La riempie il motore (explain_signs()) e la legge chi scrive il documento
 * (capitolo 41). Con steps = 0 non c'è spiegazione.
 *
 * Invariante: ogni testo puntato sta in text[], e ogni fatto registrato ha
 * superato i controlli di 40a. */
typedef struct {
    int variable;                /* la lettera della variabile */
    ExplainRequest request;      /* che cosa chiede l'enunciato */
    int equivalence;             /* 1 se la condizione è "A se e solo se B" e si
                                    spiega A, confrontandone la verità con B */
    int comparisons;             /* quanti confronti si spiegano */
    int steps;                   /* passi validi in step[] */
    ExplainStep step[MAX_EXPLAIN_STEPS];
    int columns;                 /* colonne della tabella: i punti e gli
                                    intervalli, da sinistra */
    const char *head[MAX_EXPLAIN_COLUMNS];  /* che cosa indica ogni colonna:
                                    "x = 2", "-3 < x < 2"; NULL se la tabella
                                    ha una sola colonna, tutti i valori */
    int lines;                   /* righe valide in line[] */
    ExplainLine line[MAX_EXPLAIN_LINES];
    char text[EXPLAIN_BYTES];    /* il deposito dei testi */
} Explanation;

extern Explanation explanation;
extern int explanations_wanted;
extern int explain_wrong, explain_broken;
void explain_capture(int on);
const char *explain_piece(size_t start);
ExplainStep *explain_step(ExplainKind kind, int group);
void explain_signs(const Formula *thesis, const Verdict *verdict);

/* Che cosa fa un passaggio della catena del passo induttivo (EXPLAIN_REWRITE).
 *
 * Warning: se aggiungi un passaggio, aggiungi la sua frase in
 * put_explanation_steps() (capitolo 41, output.c). */
typedef enum {
    REWRITE_SPLIT_SUM,      /* la somma fino a n + 1: quella fino a n, più l'ultimo termine */
    REWRITE_SPLIT_PRODUCT,  /* il prodotto fino a n + 1: quello fino a n, per l'ultimo fattore */
    REWRITE_HYPOTHESIS,     /* la somma (o il prodotto) fino a n sostituita con
                               l'altro membro: è l'ipotesi induttiva */
    REWRITE_EXPAND          /* i conti: l'espressione in forma di polinomio */
} ExplainRewrite;

void explain_induction(const char *formula, const Verdict *verdict);

#endif /* QUAERENS_ENGINE_EXPLANATION_H */
