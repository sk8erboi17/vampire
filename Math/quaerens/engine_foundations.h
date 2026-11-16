/* INTERFACCIA DI engine_foundations.c: limiti, errori e memoria, numeri
 * esatti, monomi, polinomi, atomi, frazioni di polinomi (capitoli 1-7).
 *
 * Ciò che gli altri moduli del motore usano di questo, nell'ordine in cui il
 * libro lo presenta: i limiti e i tipi con i loro commenti, e le dichiarazioni
 * delle variabili e delle funzioni. Il significato di una variabile e il
 * contratto di una funzione sono nel commento sopra la loro definizione, in
 * engine_foundations.c. Ciò che il modulo usa solo per sé non è qui: là è
 * static.
 *
 * Warning: una funzione o una variabile aggiunta qui va aggiunta anche a
 * engine_names.h. */
#ifndef QUAERENS_ENGINE_FOUNDATIONS_H
#define QUAERENS_ENGINE_FOUNDATIONS_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <float.h>
#include <stdarg.h>
#include <time.h>

/* I nomi con cui il programma collega le funzioni e le variabili che un
 * modulo del motore offre agli altri: va letto dopo la libreria standard e
 * prima di ogni altra cosa, perché cambia quei nomi dovunque compaiono. */
#include "engine_names.h"

/* Il verificatore dei certificati (13h). È un modulo a sé, compilato una
 * volta sola (Proof/IndependentChecker), che giudica sia ciò che dimostra
 * il motore sia ciò che trova Vampire. Di lui il motore vede soltanto
 * ck_check() e il tipo della sua risposta, CkAnswer, con i suoi tre valori:
 * li dichiara Math/EngineModules.h. Il verificatore non sa nulla del motore.
 *
 * Warning: non usare qui altri nomi del verificatore. Il controllo vale
 * qualcosa solo finché i due non hanno codice in comune: nemmeno un'utilità
 * "innocua". Che il motore veda solo quell'interfaccia lo rende un fatto. */
#include "Math/EngineModules.h"

/* I grafici (18q). Anche i grafici sono un modulo a sé (Math/Plot), che non
 * sa nulla del motore: disegna ciò che gli si dice e scrive un PDF. Se ne
 * usano solo le funzioni e i tipi dell'interfaccia, Math/Plot.h, che
 * cominciano con pl_, Pl o PL_. */
#include "Math/Plot.h"

#define ARENA_BYTES ((size_t)256 << 20)  /* memoria di lavoro per un enunciato */
#define MAX_ATOMS 256        /* atomi distinti in un enunciato */
#define MAX_FACTORS 8        /* atomi distinti in un monomio */
#define MAX_ORDER 4          /* ordine massimo di una ricorrenza del vocabolario */
#define MAX_GIVEN (MAX_ORDER + 1)  /* ipotesi su una successione dichiarata: i valori iniziali e la ricorrenza */
#define MAX_CLAIMS 3         /* tesi su una successione dichiarata */
#define MAX_UNROLL 4096      /* termini svolti a mano di una somma o prodotto */
#define MAX_POWER 512        /* massimo esponente intero costante */
#define MAX_DEGREE 4         /* grado massimo dell'ipotesi nel passo induttivo */
#define MAX_PRODUCT 4000000  /* termini di un prodotto di polinomi */
#define MAX_FORMULA 4096     /* lunghezza di un enunciato */
#define SEARCH_SPAN 10       /* valori di n provati in cerca di un controesempio */
#define MAX_SET_VARS 4       /* insiemi distinti in un enunciato sugli insiemi */
#define MAX_SET_LETTERS 12   /* lettere lette in un enunciato su relazioni e applicazioni tra parti (17r),
                                prima che lo svolgimento le riduca a MAX_SET_VARS */
#define MAX_PART_RULES 4     /* relazioni e applicazioni tra parti date da una regola, in un enunciato (17r) */
#define MAX_CONFIGS 16       /* configurazioni elencate in una dimostrazione */
#define PROOF_BYTES 1048576  /* deposito iniziale; modelli e prove per clausole crescono sullo heap (28t, 28u) */
#define CERTIFICATE_BYTES 262144 /* deposito iniziale dei certificati, poi crescita dinamica */
#define MAX_BRICKS 32        /* fattori suggeriti in un certificato: di più il verificatore non ne legge */
#define MAX_MAPS 4           /* applicazioni dichiarate in un enunciato */
#define MAX_PARAMETERS 4     /* parametri dichiarati tra le ipotesi con "k \in A" (17s) */
#define MAX_UNFOLDINGS 24    /* enunciati tra reali in cui 18v-8 svolge uno con applicazioni */
#define MAX_WITNESS_LETTERS 4  /* "esiste" tra i reali a cui 18v-11 dà un razionale, in testa a un enunciato */
#define PARAMETER_TRIES 4    /* valori di ogni parametro con cui si cerca di smentire un enunciato (17s) */
#define MAX_MAP_CASES 8      /* casi di un'applicazione definita per casi, contati dopo aver letto i valori assoluti (17s) */
#define MAX_CASE_CHOICES 16  /* casi scelti insieme, in un confronto, per le applicazioni definite per casi (18v-1) */
#define MAX_REGION_DEPTH 4   /* distinzioni di casi su una variabile, una dentro l'altra (18v-2) */
#define MAX_REGION_POINTS 8  /* numeri elencati uno per uno quando una distinzione lascia un pezzo finito (18v-2) */
#define MAX_HOLES 4          /* punti tolti da un insieme numerico con \setminus */
#define MAX_LITERALS 8       /* confronti in una disgiunzione (18z ne sostituisce fino a due: quattro ipotesi e la tesi) */
#define SAMPLE_SIZE 12       /* elementi di un insieme numerico provati uno a uno */
#define MAX_CHECKS 4096      /* combinazioni di valori provate dalla verifica sul campione */
#define MAX_SEARCH 20000     /* passi di ricerca per un enunciato con quantificatori */
#define MAX_POINT 8          /* parametri a cui la verifica numerica dà un valore */
#define MAX_CONDITIONS 64    /* condizioni di esistenza annotate in un conto */
#define MAX_DOMAIN_FACTS 16  /* fatti del dominio di un'uguaglianza "dove i due membri sono definiti" (11q) */
#define DOMAIN_PASSES 3      /* volte che quell'uguaglianza si calcola, con i fatti trovati nelle volte prima (12d) */
#define MAX_SIGN_FACTORS 8   /* fattori di cui una condizione chiede il segno del prodotto */
#define MAX_CASES 12         /* casi sul resto di una divisione, in una dimostrazione */
#define MAX_EQUATIONS 12     /* uguaglianze provate per ricavare il valore di un "esiste" */
#define MAX_SCAN 100000      /* valori di n provati uno a uno per il segno di un polinomio */
#define MAX_UNI 40           /* grado massimo di un polinomio in una tabella dei segni */
#define MAX_CRITICAL 160     /* polinomi diversi in una tabella dei segni */
#define MAX_POINTS 192       /* punti in cui una tabella dei segni può cambiare riga */
#define MAX_SIGN_ATOMS 32    /* confronti in un enunciato deciso con la tabella dei segni */
#define MAX_ABS 3            /* valori assoluti in un confronto della tabella dei segni */
#define MAX_SURDS 4          /* radici quadrate diverse in un confronto della tabella dei segni */
#define MAX_SPACES 6         /* esponenziali e logaritmi diversi in un enunciato (18p-8) */
#define MAX_STEPS 24         /* radici di un polinomio in un esponenziale o in un logaritmo */
#define MAX_KAPPAS 32        /* punti della tabella che non sono radici di polinomi, come log_2 3 */
#define MAX_ARCS 48          /* archi dell'insieme delle soluzioni di una condizione periodica */
#define MAX_TURNS 12         /* giri letti uno per uno quando una condizione periodica è ristretta a un intervallo */
#define MAX_LATTICE 32       /* famiglie x = a + k T e a + k T <= x <= b + k T in un enunciato */
#define MAX_LATTICE_HOLES 2  /* punti tolti, x \neq c + k T, accanto a un intervallo */
#define MAX_SIGN_NODES 8192  /* nodi degli alberi dei segni di un enunciato (18p-7) */
#define MAX_SIGN_NEEDS 2048  /* condizioni di esistenza dei confronti di un enunciato */
#define SURD_NAMES 1000      /* "nomi" delle lettere che stanno per le radici: non sono caratteri */
#define KRONECKER_LIMIT 100000  /* oltre questi valori non si cercano fattori di secondo grado (18p-6) */
#define KRONECKER_DIVISORS 160  /* divisori di un valore tra cui cercarli */
#define MAX_PANELS 4         /* confronti che un grafico mostra, uno per pannello */
#define FIGURE_SAMPLES 600   /* punti con cui il grafico traccia una curva */
#define MAX_PAIR_SETS 4      /* insiemi di coppie dati da una regola in un enunciato (17i) */
#define MAX_PAIR_VARIABLES 8 /* lettere che stanno per una coppia di numeri, in vista insieme (17t) */
#define MAX_RENAMED 16       /* lettere legate nella regola di un insieme di coppie */
#define MAX_GUARDS 64        /* appartenenze che fissano l'insieme di una lettera (17m) */
#define MAX_UNFOLDED 262144  /* caratteri riscritti svolgendo le definizioni di un enunciato */
#define OPERATION_NAMES 2000 /* "nomi" delle operazioni dichiarate (9g): non sono caratteri */
#define MAX_COUNT_CASES 20000000  /* valutazioni di un enunciato sugli insiemi deciso contando (15f) */
#define MAX_GENERATORS 256   /* multipli delle ipotesi provati per ottenere la tesi (18s, 18u) */
#define MAX_LEAVES 8         /* parti di una disgiunzione esaminate insieme (18u) */
#define MAX_NAMED 3          /* valori cercati insieme per degli "esiste" consecutivi (18u) */
#define MAX_RECORDS 32       /* valori trovati da 18u-3 in una dimostrazione, annotati per la verifica (capitolo 19) */
#define MIN_SATISFIED 1      /* valori del campione che soddisfano le ipotesi, almeno, perché la verifica di 18u conti (capitolo 19).
                                Warning: se lo alzi, cambia anche i motivi scritti in decide_quantified() e in records_doubt() */

/* Un insieme finito di indici: variabili della ricerca o tipi non vuoti
 * del parser, in contesti separati. low conserva le prime due
 * parole senza allocazioni, per non rallentare i problemi gia trattati;
 * extra conta le parole successive, high ne e la coda immutabile,
 * posseduta dall'arena della prova. Fuori da queste parole ogni bit e zero.
 * Copiare la struttura conserva il valore: nessuno modifica una coda gia
 * condivisa, e la sua durata e quella dell'arena da cui proviene. */
typedef struct {
    unsigned long long low[2];
    size_t extra;
    const unsigned long long *high;
} SlotSet;

/* L'insieme vuoto non richiede memoria e puo inizializzare ogni contesto. */
#define SLOT_EMPTY ((SlotSet){0})
#define SLOT_WORD_BITS (sizeof(unsigned long long) * CHAR_BIT)
#define MAX_ARITY 4          /* componenti di un membro di un insieme scritto come nei libri: 4 per una
                                relazione tra coppie (17p) */
#define MAX_LISTED 4         /* elementi scritti tra graffe, \{a, b\} (17p) */
#define MAX_DEFINITIONS 8    /* nomi dati dall'enunciato a un insieme, G = \{...\} (17p) */
#define MAX_CHECK_MODELS 4000  /* modelli su cui si confrontano l'enunciato scritto e quello svolto (28h) */
#define GREEK_NAMES 3000     /* "nomi" delle lettere greche usate come applicazioni (17o): non sono caratteri */
#define PAIR_NAMES 4000      /* "nomi" delle seconde componenti delle applicazioni a valori in coppie (17s):
                                PAIR_NAMES più la lettera dell'applicazione */
#define MAX_MODEL_SIZE 4     /* prefisso esaustivo di 28a; 28t prosegue senza tetto di cardinalita */
#define MAX_MODEL_CODES 4096 /* quota di configurazioni del solo prefisso esaustivo; SAT non la usa */
#define MAX_MODEL_OBJECTS 8  /* elementi di un insieme di parti o di applicazioni in un modello finito (28m):
                                le parti di un insieme di 3 elementi, nel solo prefisso esaustivo */
#define MAX_MODEL_CELLS 64   /* celle della tabella di un simbolo in un modello finito (28a, 28m) */
#define MAX_AXIOMS 16        /* leggi delle parti e delle applicazioni aggiunte alle ipotesi (28n) */
#define MAX_CASE_LEAVES 512  /* rami chiusi e scritti per un'affermazione, di cui si controlla la copertura (28p) */
#define MAX_CASE_STEPS 32    /* casi uno dentro l'altro nel cammino di uno di quei rami (28p) */
#define MAX_DESCRIBED 8      /* parti scritte come insiemi dove serve un elemento, in una condizione (17v) */
#define MAX_TEMPLATES 8      /* insiemi scritti dall'enunciato come parti, usati per le comprensioni (17v, 28n) */
#define MAX_LISTED_TUPLES 32 /* coppie in un elenco scritto tra graffe, \{(1, 1), (1, 2)\} (17v) */
#define RELATION_NAMES 3500  /* "nomi" delle relazioni scritte con un comando, come \le (17v): non sono
                                caratteri, e stanno tra le lettere greche e i numeri (NUMERAL_NAMES); i
                                simboli di struttura hanno nomi negativi */
#define LETTER_INDEX (-2)    /* un pedice letterale, \le_{S}, vale LETTER_INDEX meno la lettera (17v) */
#define NUMERAL_NAMES 5000   /* "nomi" dei numeri scritti come elementi (17v): il numero v è NUMERAL_NAMES + v */
#define MAX_NUMERAL 1000     /* il più grande numero scritto come elemento, più uno (17v) */
#define ZERO_INDEX (-1)      /* il pedice 0, x_{0}: zero resta "senza pedice", i numeri positivi restano distinti */
#define MAX_MODELS 400000    /* tabelle provate per una scelta delle grandezze degli insiemi */
#define MAX_MODEL_WORK 3000000  /* tabelle provate in tutto per un enunciato */

extern size_t model_memory_limit;
extern unsigned long long saturation_work_limit;
extern size_t saturation_memory_limit;
extern unsigned long long model_work_limit;
extern long long model_step_limit;
long long checker_steps(void);
extern unsigned long long verification_work_limit;

#define MAX_GROUND 2048      /* elementi nominati in una dimostrazione su insiemi qualsiasi (28b) */
#define MAX_KNOWN 2048       /* condizioni note in un ramo di quella dimostrazione */
#define MAX_DIFFERENT 256    /* fatti "diversi" noti in un ramo */
#define MAX_SPLITS 4         /* distinzioni di casi una dentro l'altra (28-5) */
#define MAX_ROUNDS 4         /* giri di istanze prima di arrendersi (28-3) */
#define MODEL_ROUNDS 8       /* giri di istanze scelte dal modello candidato prima di distinguere i casi (28r) */
#define MAX_CANDIDATE_STEPS 2000000  /* passi del calcolo nel modello candidato, per giro di istanze (28r) */
#define MAX_LOOKAHEAD 48     /* disgiunzioni di cui si guardano avanti i due casi, prima di sceglierne una (28o) */
#define LOOKAHEAD_ROUNDS 2   /* giri di istanze prima di distinguere dei casi, quando si guarda avanti (28o) */
#define MAX_TUPLES 20000     /* scelte di elementi esaminate per un "per ogni" in un giro */
#define MAX_FREE_TUPLES 128  /* istanze di un "per ogni" sugli elementi con un nome, in un giro */
#define MAX_PROP_ATOMS 12    /* condizioni elementari di un passo ricontrollato con la tabella di verità */
#define MAX_CHAIN 64         /* anelli di una catena di uguaglianze */
#define MAX_PATTERN 64       /* elementi in attesa mentre si confronta uno schema con ciò che è presente (28-3) */
#define MAX_NAMES_GIVEN 4096 /* nomi dati in tutti i rami della dimostrazione di un'affermazione (28f) */
#define MAX_PART_CANDIDATES 24  /* parti provate per una parte legata da un "per ogni parte" (28k) */
#define MAX_PART_CHOICES 2   /* scelte di parti una dentro l'altra, in un ramo (28k) */
#define MAX_PART_ATTEMPTS 600  /* scelte di parti provate in tutto per un'affermazione (28k) */
#define MAX_WITNESSES 8      /* testimoni di un'equipotenza provati, dal più corto, uno per tentativo (28q) */
#define MAX_BIJ 512          /* termini della grammatica dei testimoni costruiti per un'equipotenza (28q) */
#define MAX_BIJ_VISITS 200000  /* insiemi da cui si riparte cercando quei termini, per un'equipotenza (28q) */
#define MAX_BRANCHES 16      /* rami uno dentro l'altro: casi, scelte di parti e prove (28k, 28l) */
#define MAX_PROBES 8         /* disgiunzioni provate per trovarne una con un caso che si chiude subito (28l) */
#define MAX_CONGRUENCES 32   /* condizioni "m divide P" in un enunciato deciso sui resti (18r) */
#define MAX_PERIOD 100000    /* il multiplo comune dei moduli, al più */
#define MAX_RESIDUE_CASES 200000  /* assegnazioni di resti provate per un enunciato */
#define MAX_CLASSES 16       /* classi di resto elencate in un insieme di soluzioni */
#define MAX_QPOLY 24         /* grado massimo dei polinomi di una funzione razionale da integrare (30d) */
#define MAX_PRIMITIVE_DEPTH 4  /* metodi uno dentro l'altro nella ricerca di una primitiva (30c) */
#define MAX_PRIMITIVE_CALLS 600  /* chiamate alla ricerca di una primitiva, per un enunciato (30c) */
#define MAX_INNER 24         /* funzioni interne provate come nuova variabile (30g) */
#define MAX_EXP_TERMS 160    /* termini x^m e^{(a + i b) x} di una primitiva (30e) */
#define ANSWER_BYTES 4096    /* lunghezza di una primitiva o di un valore scritti */
#define RIEMANN_PIECES 256   /* intervalli in cui si divide [a, b] all'inizio (30i) */
#define RIEMANN_SPLITS 10    /* dimezzamenti di un intervallo in cui il calcolo non riesce (30i) */
#define MAX_PIECES 8         /* parti in cui un valore assoluto divide un integrale definito (30i-2) */

/* Valore di Token.ch per le graffe scritte \{ e \} e per l'a capo \\: 256 più
 * il carattere, per distinguerle dalle graffe di raggruppamento di LaTeX. */
#define ESCAPED 256
#define MAX_PARTS 24         /* fattori distinti nella scomposizione di un polinomio */
#define MAX_UNIVARIATE 16    /* grado massimo di un polinomio in n da scomporre */
#define MAX_DIVISORS 2048    /* divisori di un intero provati come radici razionali */

/* Nomi interni di variabili, fuori dall'intervallo dei caratteri: \pi, e una
 * lettera ausiliaria che vale zero o più (vedi body_is_positive()). */
#define VAR_PI 256
#define VAR_SLACK 257
#define VAR_ITERATE 258  /* il valore corrente mentre si calcola un'iterata f^{m}(a) con i numeri (17s) */

/* Nomi interni dei termini precedenti di una successione dichiarata
 * dall'enunciato, mentre la sua regola viene calcolata con i numeri
 * (capitolo 26): VAR_TERM, VAR_TERM + 1, ..., fino a MAX_ORDER. */
#define VAR_TERM 300

/* I razionali tengono numeratore e denominatore sotto 2^62, così il prodotto
 * di due di essi e la somma di due prodotti stanno sempre in un __int128. */
#define COEF_LIMIT ((__int128)1 << 62)

extern const char *failure;
extern int work_allocation_failed;
void fail(const char *reason);
extern int undefined;
void fail_undefined(const char *reason);
extern const char *const OUT_OF_MEMORY;
extern size_t arena_used;
void *arena_alloc(size_t bytes);
void *arena_node(size_t bytes);
int work_reserve(void **data, size_t *capacity, size_t need, size_t unit);
void *work_arena_array(size_t count, size_t unit);
extern size_t stack_budget;
extern const char *const STACK_EXHAUSTED;
extern uintptr_t stack_origin;
extern size_t stack_chain_levels;
extern int stack_guard;
extern int stack_exhausted;
int stack_room(void);

/* Una parola del bitset, zero oltre la sua fine. L'indice i corrisponde
 * alla parola i/W e al bit i%W: nessuno shift puo raggiungere W. */
static inline unsigned long long slot_set_word(SlotSet set, size_t word) {
    if (word < 2) return set.low[word];
    return word - 2 < set.extra ? set.high[word - 2] : 0;
}

/* Ritorna 1 se la variabile slot appartiene all'insieme. */
static inline int slot_set_contains(SlotSet set, int slot) {
    size_t i = (size_t)slot;
    return (int)(slot_set_word(set, i / SLOT_WORD_BITS) >> (i % SLOT_WORD_BITS) & 1);
}

/* Aggiunge slot (non negativo). Le due parole comuni si copiano nel
 * valore; la coda cresce nell'arena senza cambiare i valori condivisi. */
static inline SlotSet slot_set_with(SlotSet set, int slot) {
    size_t i = (size_t)slot, word = i / SLOT_WORD_BITS;
    unsigned long long bit = 1ULL << (i % SLOT_WORD_BITS);
    if (slot_set_word(set, word) & bit) return set;
    if (word < 2) { set.low[word] |= bit; return set; }
    size_t count = word - 1 > set.extra ? word - 1 : set.extra;
    unsigned long long *tail = work_arena_array(count, sizeof *tail);
    if (!tail) return SLOT_EMPTY;
    if (set.extra) memcpy(tail, set.high, set.extra * sizeof *tail);
    memset(tail + set.extra, 0, (count - set.extra) * sizeof *tail);
    tail[word - 2] |= bit;
    set.high = tail; set.extra = count;
    return set;
}

/* L'insieme contenente soltanto slot, con la stessa regola di crescita. */
static inline SlotSet slot_set_single(int slot) { return slot_set_with(SLOT_EMPTY, slot); }

/* Unione: OR di ogni parola. Si riusa una coda gia immutabile quando
 * l'altro insieme non ne ha una, o quando entrambe sono la stessa. */
static inline SlotSet slot_set_union(SlotSet a, SlotSet b) {
    SlotSet result = a;
    result.low[0] |= b.low[0]; result.low[1] |= b.low[1];
    if (!b.extra) return result;
    if (!a.extra || (a.high == b.high && a.extra == b.extra)) {
        result.high = b.high; result.extra = b.extra; return result;
    }
    size_t count = a.extra > b.extra ? a.extra : b.extra;
    unsigned long long *tail = work_arena_array(count, sizeof *tail);
    if (!tail) return SLOT_EMPTY;
    for (size_t i = 0; i < count; i++) tail[i] = slot_set_word(a, i + 2) | slot_set_word(b, i + 2);
    result.high = tail; result.extra = count;
    return result;
}

/* Ritorna 1 se set contiene tutti i bit di wanted, anche oltre le prime
 * due parole. Un bit mancante basta a smentire l'inclusione. */
static inline int slot_set_includes(SlotSet set, SlotSet wanted) {
    for (size_t i = 0; i < 2 + wanted.extra; i++)
        if (slot_set_word(wanted, i) & ~slot_set_word(set, i)) return 0;
    return 1;
}

/* Ritorna 1 se i due insiemi condividono almeno una variabile. */
static inline int slot_set_intersects(SlotSet a, SlotSet b) {
    size_t count = a.extra < b.extra ? a.extra : b.extra;
    for (size_t i = 0; i < 2 + count; i++)
        if (slot_set_word(a, i) & slot_set_word(b, i)) return 1;
    return 0;
}

/* Un numero razionale num/den. Invariante: den > 0 e la frazione è ridotta ai
 * minimi termini, quindi due Frac uguali hanno campi uguali. Lo stesso tipo
 * rappresenta gli esponenti dei monomi (capitolo 4). */
typedef struct { long long num, den; } Frac;

__int128 gcd128(__int128 a, __int128 b);
Frac frac_make(__int128 num, __int128 den);
Frac frac_int(long long v);
Frac frac_neg(Frac a);
Frac frac_add(Frac a, Frac b);
Frac frac_mul(Frac a, Frac b);
Frac frac_div(Frac a, Frac b);
int frac_cmp(Frac a, Frac b);
long long frac_floor(Frac a);

/* Un numero complesso re + im i a coordinate razionali: il coefficiente di un
 * termine di polinomio. */
typedef struct { Frac re, im; } Num;

Num num_int(long long v);
Num num_frac(Frac v);
int num_is_zero(Num a);
int num_equal(Num a, Num b);
Num num_neg(Num a);
Num num_add(Num a, Num b);
Num num_mul(Num a, Num b);
Num num_inv(Num a);

/* Un atomo elevato a un esponente razionale non nullo. */
typedef struct {
    int atom;  /* indice nella tabella `atoms` */
    Frac exp;  /* esponente, mai zero */
} Factor;

/* Un monomio: il prodotto dei suoi fattori. Invariante: i fattori sono in
 * ordine crescente di atomo e senza ripetizioni, così due monomi uguali hanno
 * la stessa rappresentazione. count == 0 è il monomio 1. */
typedef struct {
    int count;                   /* fattori validi in `factor` */
    Factor factor[MAX_FACTORS];
} Mono;

/* Un termine di polinomio: coefficiente per monomio. */
typedef struct {
    Num coef;
    Mono mono;
} Term;

typedef struct Node Node;  /* nodo dell'albero sintattico, capitolo 8 */

/* I tipi di atomo descritti sopra. */
typedef enum { ATOM_VAR, ATOM_BIGOP, ATOM_REC, ATOM_POW, ATOM_LN, ATOM_ATAN } AtomKind;

/* Cosa fa da base in un atomo POW o LN:
 *   BASE_EI:    la base è e^i, cioè l'atomo vale e^{i M} (trigonometria);
 *   BASE_PRIME: un numero primo;
 *   BASE_ATOM:  un altro atomo (un parametro, o n stesso);
 *   BASE_POLY:  un polinomio non riducibile a monomio, per esempio n + 1. */
typedef enum { BASE_EI, BASE_PRIME, BASE_ATOM, BASE_POLY } BaseKind;

/* Come un atomo e^{i M} si semplifica quando M contiene pi greco:
 *   PI_NONE:    nessuna regola;
 *   PI_CONST:   M = pi, l'atomo è il numero e^{i pi} = -1;
 *   PI_INTEGER: M = pi per una potenza di n: l'atomo vale 1 al quadrato. */
typedef enum { PI_NONE, PI_CONST, PI_INTEGER } PiMode;

/* Un atomo. I campi usati dipendono da kind:
 *
 *   VAR:   id = nome della variabile.
 *   BIGOP: node = il nodo somma/prodotto che lo definisce, dilation = a,
 *          offset = c: l'atomo vale la somma (o il prodotto) del corpo di
 *          node per l'indice dall'estremo inferiore fino ad a n + c.
 *   REC:   id = posizione nel vocabolario, dilation = a, offset = j:
 *          l'atomo vale X(a n + j).
 *   POW:   base e id dicono la base (id è il primo, l'atomo o la posizione in
 *          `base_polys`), exponent è il monomio M.
 *   LN:    base e id dicono la base, come per POW.
 *   ATAN:  id = posizione dell'argomento in `atan_args` (capitolo 11).
 *
 * pi e depends_on_n sono calcolati alla creazione. */
typedef struct {
    AtomKind kind;
    long long id;
    const Node *node;
    long long dilation, offset;
    BaseKind base;
    Mono exponent;
    PiMode pi;
    int depends_on_n;  /* 1 se il valore cambia al variare di n */
    int positive;      /* BIGOP: 1 se è un prodotto di fattori tutti positivi */
} Atom;

extern Atom atoms[MAX_ATOMS];
extern int atom_count;
extern int induction_var;
Mono mono_atom(int atom, Frac exp);
Mono mono_mul(const Mono *a, const Mono *b);
Mono mono_pow(const Mono *m, Frac q);
int mono_cmp(const Mono *a, const Mono *b);
int mono_depends_on_n(const Mono *m);
Frac mono_exponent(const Mono *m, int atom);
Mono mono_with_exponent(const Mono *m, int atom, Frac exp);

/* Un polinomio in forma canonica. `term` punta a `count` termini nell'arena
 * (NULL se count == 0); la memoria è dell'arena, non del polinomio. */
typedef struct {
    int count;
    Term *term;
} Poly;

Term *terms_alloc(long long capacity);
Poly poly_finish(Term *buffer, long long capacity, int used);
Poly poly_term(Term t);
Poly poly_const(Num c);
Poly poly_add(Poly a, Poly b, int subtract);
Poly poly_mul(Poly a, Poly b);
int poly_is_one(Poly p);
int poly_equal(Poly a, Poly b);
int poly_proportional(Poly a, Poly b);
int poly_depends_on_n(Poly p);
int poly_split(Poly p, int x, Poly *part, int max_degree);
int poly_coefficients(Poly p, int x, long long *c, long long *scale);
extern Poly base_polys[MAX_ATOMS];
extern int base_poly_count;
int atom_intern(const Atom *proto);
int atom_var(int name);
int atom_bigop(const Node *node, long long dilation, long long offset);
int atom_rec(int sequence, long long dilation, long long offset);
int atom_pow(BaseKind base, long long id, const Mono *exponent);
int atom_ln(BaseKind base, long long id);
int base_poly_intern(Poly p);

/* La frazione num/den. */
typedef struct { Poly num, den; } Rat;

Rat rat_make(Poly num, Poly den);
Rat rat_int(long long v);
Rat rat_frac(Frac v);
Rat rat_atom(int atom);
Rat rat_add(Rat a, Rat b, int subtract);
Rat rat_mul(Rat a, Rat b);

/* Cosa si chiede a un'espressione perché un'operazione sia definita. */
typedef enum { NEVER_ZERO, ALWAYS_POSITIVE, NEVER_NEGATIVE } Requirement;

/* Una condizione di esistenza: il prodotto dei `count` polinomi di factor[]
 * deve rispettare `kind` per ogni n ammesso. Quasi sempre il fattore è uno
 * solo; sono di più quando chi pone la condizione conosce l'espressione già
 * divisa in fattori, e conviene non perderli moltiplicandoli (vedi
 * require_positive() nel capitolo 11). `why` dice che cosa succede se la
 * condizione non vale, con le stesse parole di fail_undefined(). I termini
 * dei polinomi stanno nell'arena: la condizione vale finché l'arena non viene
 * svuotata. */
typedef struct {
    Requirement kind;
    int count;                      /* fattori validi in factor: almeno 1 */
    Poly factor[MAX_SIGN_FACTORS];
    const char *why;
} Condition;

extern Condition conditions[MAX_CONDITIONS];
extern int condition_count;
extern int conditions_on;
extern int conditions_lost;
extern const char *const REWRITTEN;
extern int rewriting;
void require_product(Requirement kind, const Poly *factor, int count, const char *why);
void require(Requirement kind, Poly value, const char *why);
Rat rat_div(Rat a, Rat b);
Rat rat_pow_int(Rat a, long long e);
Rat poly_substitute(Poly p, int x, Rat value);
int rat_number(Rat r, Num *value);
int rat_integer(Rat r, long long *value);
int rat_affine(Rat r, long long *a, long long *c);
int rat_affine_in(Rat e, int x, Frac *alpha, Frac *beta);

#endif /* QUAERENS_ENGINE_FOUNDATIONS_H */
