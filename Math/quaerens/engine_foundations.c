/* =============================================================================
 * 1. INCLUDE E LIMITI
 * ============================================================================
 *
 * Solo libreria standard. I limiti servono a fermare un conto che cresce
 * troppo con un NON SUPPORTATO, invece di esaurire la macchina.
 */

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

/* Il verificatore dei certificati (13h). È un programma a sé, incluso qui
 * solo perché il progetto resti un unico comando di compilazione: senza il
 * suo main(), e di tutto ciò che contiene questo file usa soltanto
 * ck_check() e il tipo della sua risposta, CkAnswer, con i suoi tre valori.
 * Il verificatore non sa nulla di questo file.
 *
 * Warning: non usare qui altri nomi che cominciano con ck_, Ck o CK_, nemmeno
 * una costante. Il controllo vale qualcosa solo finché i due programmi non
 * hanno codice in comune: nemmeno un'utilità "innocua". */
#define CK_NO_MAIN
#include "checker.c"

/* I grafici (18q). Anche plot.c è un file a sé, che non sa nulla di questo:
 * disegna ciò che gli si dice e scrive un PDF. Di ciò che contiene si usano
 * solo le funzioni e i tipi della sua interfaccia, che cominciano con pl_,
 * Pl o PL_. */
#include "plot.c"

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
/* Budget di ricerca, modificabili dalla riga di comando: non cardinalita
 * massime. Anche i depositi SAT crescono entro la memoria richiesta. */
static size_t model_memory_limit = 128u * 1024u * 1024u;
/* Budget effettivi della saturazione: visite e memoria posseduta, senza
 * fissare quante variabili, clausole o argomenti puo avere un problema. */
static unsigned long long saturation_work_limit = 2000000;
static size_t saturation_memory_limit = 128u * 1024u * 1024u;
static unsigned long long model_work_limit = 20000000ULL;
/* Elementi provati dai quantificatori, in tutto, nel calcolare un enunciato
 * sui modelli (--model-steps). E un budget di lavoro come gli altri: era una
 * costante, e allora nessun --model-work faceva confermare un controesempio
 * di 83 elementi sotto quattro quantificatori. Resta sotto LLONG_MAX, perche
 * model_steps lo supera di uno per dire "conto interrotto". */
static long long model_step_limit = 40000000LL;

/* Ritorna il budget che il motore dà al verificatore per ricalcolare un
 * modello (il terzo argomento di ck_check()): due volte e mezza il proprio,
 * il rapporto che c'è sempre stato tra i due (40 e 100 milioni). Così
 * --model-steps allarga insieme il ricalcolo del motore e quello del
 * verificatore, e un controesempio che il primo conferma il secondo lo può
 * controllare. */
static long long checker_steps(void) {
    return model_step_limit <= (LLONG_MAX - 1) / 5 ? model_step_limit * 5 / 2 : LLONG_MAX - 1;
}
static unsigned long long verification_work_limit = 20000000ULL;
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

/* =============================================================================
 * 2. ERRORI E MEMORIA
 * ============================================================================
 *
 * Errori. Un conto può uscire dai limiti in molti punti (overflow, divisione
 * per zero, notazione senza regola). Invece di propagare un codice attraverso
 * ogni chiamata, la prima causa viene annotata in `failure` e il conto
 * prosegue producendo valori senza significato: chi lo ha avviato controlla
 * `failure` alla fine e scarta tutto.
 *
 * Memoria. Polinomi e nodi dell'albero vivono in un'unica zona ("arena") da
 * cui si prende spazio in fila e che si svuota tutta insieme tra un enunciato
 * e il successivo. Non c'è free(): i valori intermedi sono tanti e piccoli, e
 * la loro vita finisce comunque con l'enunciato.
 *
 * Pila. Le funzioni che visitano un albero sono ricorsive, e la pila non
 * cresce: un enunciato lungo, che può avere alberi profondi, si legge
 * tenendo il conto di quanta ne chiederà (in fondo al capitolo).
 */

/* Motivo del primo errore del conto in corso, in italiano; NULL se va bene. */
static const char *failure;
/* Una crescita fallita delle strutture dinamiche non puo essere cancellata
 * da un tentativo euristico: il punto d'ingresso scarta comunque l'esito. */
static int work_allocation_failed;

/* Annota reason come causa del fallimento, se è la prima. */
static void fail(const char *reason) { if (!failure) failure = reason; }

/* 1 se il conto in corso è fallito perché un'espressione non è definita nel
 * punto in cui la si calcolava: divisione per zero, logaritmo di un numero non
 * positivo, radice di un numero negativo. Serve a distinguere questo caso dai
 * limiti del programma, come i numeri troppo grandi. Chi vuole la distinzione
 * lo azzera prima del conto, insieme a `failure`. */
static int undefined;

/* Come fail(), per i casi in cui un'espressione non è definita. */
static void fail_undefined(const char *reason) {
    if (!failure) undefined = 1;
    fail(reason);
}

/* Il messaggio dell'arena piena. Ha un nome perché una ricerca che la
 * riempie (capitolo 19) lo riconosce: lì vuol dire "troppi tentativi", non
 * un enunciato fuori portata. */
static const char *const OUT_OF_MEMORY = "memoria di lavoro esaurita";

/* L'arena: arena_used è il numero di byte già assegnati. */
static _Alignas(16) char arena[ARENA_BYTES];
static size_t arena_used;

/* Arrotonda bytes al multiplo di 16 successivo, l'unità di assegnazione. */
static size_t arena_round(size_t bytes) { return (bytes + 15) & ~(size_t)15; }

/* Ritorna un blocco di bytes byte, allineato a 16 e non inizializzato, oppure
 * NULL (con fail()) se l'arena è piena. */
static void *arena_alloc(size_t bytes) {
    bytes = arena_round(bytes);
    if (bytes > ARENA_BYTES - arena_used) { fail(OUT_OF_MEMORY); return NULL; }
    void *block = arena + arena_used;
    arena_used += bytes;
    return block;
}

/* Come arena_alloc(), per i nodi degli alberi degli enunciati su insiemi
 * qualsiasi (parser.c): entrando negli ultimi ARENA_RESERVE byte annota già
 * "memoria di lavoro esaurita", ma continua a dare blocchi finché ce ne
 * sono.
 *
 * Perché una riserva. Annotato l'errore, chi legge e chi svolge si fermano
 * al primo controllo, ma prima di arrivarci chiedono ancora qualche nodo.
 * Senza riserva quei nodi erano tutti lo stesso nodo di riserva, riscritto
 * a ogni richiesta mentre altri lo stavano ancora riempiendo: un albero che
 * conteneva sé stesso, o un campo azzerato sotto chi lo leggeva, e il
 * programma si fermava. Con la riserva sono nodi veri, distinti; il nodo
 * unico resta per quando finisce anche lei. Le altre parti del programma
 * usano l'arena fino in fondo, come prima. */
#define ARENA_RESERVE ((size_t)8 << 20)
static void *arena_node(size_t bytes) {
    if (ARENA_BYTES - arena_used < ARENA_RESERVE + arena_round(bytes)) fail(OUT_OF_MEMORY);
    return arena_alloc(bytes);
}

/* Allarga un vettore di lavoro posseduto dal chiamante. capacity conta
 * elementi di unit byte; i dati esistenti restano validi per indice, ma
 * gli indirizzi possono cambiare. Le celle nuove sono azzerate. Overflow
 * e memoria esaurita annotano failure e lasciano intatto il vecchio blocco. */
static int work_reserve(void **data, size_t *capacity, size_t need, size_t unit) {
    if (need <= *capacity) return 1;
    size_t cap = *capacity ? *capacity : 16;
    while (cap < need) {
        if (cap > (size_t)-1 / 2) { cap = need; break; }
        cap *= 2;
    }
    if (unit && cap > (size_t)-1 / unit) { work_allocation_failed = 1; fail(OUT_OF_MEMORY); return 0; }
    void *next = realloc(*data, cap * unit);
    if (!next) { work_allocation_failed = 1; fail(OUT_OF_MEMORY); return 0; }
    memset((unsigned char *)next + *capacity * unit, 0, (cap - *capacity) * unit);
    *data = next; *capacity = cap;
    return 1;
}

/* Alloca metadati nell'arena, controllando dimensione e fallimento. Per
 * questi dati un ripiego non puo cancellare l'errore: maschere o snapshot
 * incompleti cambierebbero il significato di una deduzione. Zero elementi
 * non richiedono un blocco; unit deve essere positivo. */
static void *work_arena_array(size_t count, size_t unit) {
    if (!count) return NULL;
    if (!unit || count > ARENA_BYTES / unit) {
        work_allocation_failed = 1; fail(OUT_OF_MEMORY); return NULL;
    }
    void *data = arena_alloc(count * unit);
    if (!data) work_allocation_failed = 1;
    return data;
}

/* LA PILA DI LAVORO
 *
 * Quasi ogni funzione che visita un albero è ricorsiva: scende di un livello
 * di pila per ogni livello dell'albero. A differenza dell'arena e dei vettori
 * di lavoro la pila non cresce, e oltre il suo fondo il programma non dà un
 * esito: si ferma. Finché un enunciato stava in MAX_FORMULA caratteri i suoi
 * alberi non potevano essere abbastanza profondi; da quando il linguaggio
 * degli insiemi qualsiasi (17o-17x) legge enunciati di lunghezza qualsiasi
 * (gli altri linguaggi no: prove_core()) possono esserlo, e 20.000 negazioni
 * una dentro l'altra fermavano il programma. Ora la lettura di un enunciato
 * lungo tiene il conto della pila che i suoi alberi chiederanno, e si ferma
 * prima, con l'esito "pila di lavoro esaurita".
 *
 * Due cose rendono profondo un albero.
 *
 *   - L'annidamento vero: parentesi, negazioni, f(f(f(x))). Lo legge una
 *     discesa ricorsiva, che usa lei stessa la pila: quanta, lo dice la
 *     distanza tra l'indirizzo di una variabile locale e quello preso
 *     all'avvio (stack_used()). Si misura, e non si contano i livelli, perché
 *     il costo di un livello cambia di venti volte tra una compilazione
 *     ottimizzata e una con i sanitizer.
 *   - Le catene e gli elenchi: "a \iff b \iff c", o le lettere di
 *     "\forall x, y, z", si leggono con un ciclo, che non usa pila, ma danno
 *     un albero a pettine, con un livello per anello o per lettera. Chi li
 *     legge conta i livelli in stack_chain_levels (chain_link() in
 *     parser.c), e ognuno vale CHAIN_LEVEL_BYTES. Le catene di \land e di
 *     \lor, le sole che in un enunciato possono essere lunghe quanto si
 *     vuole (le ipotesi), in un enunciato lungo non sono a pettine: il
 *     lettore le unisce a metà (abstract_chain() in parser.c).
 *
 * C'è un terzo modo, che questo budget non conta: un numero scritto. Lo
 * svolgimento di |T| \ge n (17x in parser.c) ha n quantificatori uno dentro
 * l'altro anche in un enunciato corto. Lì il limite è la memoria: le sue
 * n(n - 1)/2 coppie riempiono l'arena poco oltre n = 1000 (misurato: 1150
 * si svolge, 1300 no), e con una pila di 8 MB quei livelli sono stati
 * visitati senza fermarsi anche con i sanitizer.
 *
 * La lettura conta il doppio: chi visiterà l'albero può usare, per livello,
 * più pila di chi lo ha letto. Sono misure fatte (novembre 2026, pila di
 * 8 MB, compilazione ottimizzata): la lettura usa da 600 a 1400 byte per
 * livello di annidamento e le visite meno; un anello di catena costa alle
 * visite da 140 a 210 byte. stack_budget, di default, è metà di quella pila.
 *
 * Non è un tetto alla grandezza dei modelli né al numero delle ipotesi: è
 * il budget di una risorsa che il programma non può allargare, e chi lo
 * esaurisce riceve un NON DIMOSTRATO che lo dice, come per la memoria. */
#define CHAIN_LEVEL_BYTES 256  /* byte di pila che un anello di una catena a pettine costa a chi la visita */

/* Byte di pila concessi agli alberi di un enunciato lungo (--stack-budget):
 * la metà di una pila di 8 MB, quella consueta. Chi lavora con una pila più
 * piccola (ulimit -s) deve abbassarlo, perché in C standard il programma non
 * può sapere quanta ne ha: con 2 MB di pila e il budget di default 2000
 * parentesi annidate lo fermano ancora. */
static size_t stack_budget = (size_t)4 << 20;

/* L'esito di chi esaurisce il budget della pila. Ha un nome perché prove()
 * lo mette nel verdetto al posto di ciò che i lettori, fermati a metà,
 * hanno detto. */
static const char *const STACK_EXHAUSTED = "pila di lavoro esaurita: l'enunciato è troppo annidato";

static uintptr_t stack_origin;     /* Indirizzo di una variabile locale di engine_init(): il punto da cui si misura. */
static size_t stack_chain_levels;  /* Anelli delle catene a pettine lette nell'enunciato in corso. */
static int stack_guard;            /* 1 mentre si lavora a un enunciato lungo: solo allora si misura. */
/* 1 se il budget è finito lavorando all'enunciato in corso. Come
 * work_allocation_failed, non lo cancella un tentativo successivo: lo
 * azzera e lo legge solo prove(). */
static int stack_exhausted;

/* Ritorna i byte di pila tra il punto di avvio e chi chiama. La differenza
 * si fa tra interi e in valore assoluto, perché il verso in cui la pila
 * cresce dipende dalla macchina. */
static size_t stack_used(void) {
    char here;
    uintptr_t now = (uintptr_t)(void *)&here;
    return (size_t)(now > stack_origin ? now - stack_origin : stack_origin - now);
}

/* Ritorna 1 se gli alberi dell'enunciato in corso stanno ancora nel budget
 * della pila: il doppio di quella in uso, più quella delle catene lette.
 * Altrimenti annota stack_exhausted e ritorna 0, e così a ogni chiamata
 * successiva: nessun lettore deve proseguire. Per un enunciato corto
 * ritorna sempre 1, senza misurare. */
static int stack_room(void) {
    if (!stack_guard) return 1;
    size_t reading = 2 * stack_used();
    if (reading > stack_budget || stack_chain_levels > (stack_budget - reading) / CHAIN_LEVEL_BYTES) stack_exhausted = 1;
    return !stack_exhausted;
}

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

/* =============================================================================
 * 3. NUMERI ESATTI: RAZIONALI E RAZIONALI COMPLESSI
 * ============================================================================
 *
 * Nessun numero in virgola mobile: un errore di arrotondamento farebbe
 * sembrare diverso da zero un valore nullo, e la dimostrazione crollerebbe.
 *
 * I coefficienti dei polinomi sono numeri a + b i con a e b razionali. La
 * parte immaginaria serve solo alla trigonometria (capitolo 11): negli
 * enunciati senza seni e coseni resta sempre zero.
 */

/* Un numero razionale num/den. Invariante: den > 0 e la frazione è ridotta ai
 * minimi termini, quindi due Frac uguali hanno campi uguali. Lo stesso tipo
 * rappresenta gli esponenti dei monomi (capitolo 4). */
typedef struct { long long num, den; } Frac;

/* Massimo comun divisore di |a| e |b| con l'algoritmo di Euclide:
 * gcd(a, b) = gcd(b, a mod b), finché il resto è zero. */
static __int128 gcd128(__int128 a, __int128 b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) { __int128 t = a % b; a = b; b = t; }
    return a;
}

/* Ritorna num/den ridotta ai minimi termini. Fallisce se den è zero o se il
 * risultato esce da COEF_LIMIT. */
static Frac frac_make(__int128 num, __int128 den) {
    if (den == 0) { fail_undefined("divisione per zero"); return (Frac){0, 1}; }
    if (den < 0) { num = -num; den = -den; }
    __int128 g = gcd128(num, den);
    if (g > 1) { num /= g; den /= g; }
    if (num >= COEF_LIMIT || num <= -COEF_LIMIT || den >= COEF_LIMIT) {
        fail("numeri troppo grandi per il calcolo esatto");
        return (Frac){0, 1};
    }
    return (Frac){(long long)num, (long long)den};
}

/* Operazioni elementari sui razionali. */
static Frac frac_int(long long v) { return (Frac){v, 1}; }
static Frac frac_neg(Frac a) { return (Frac){-a.num, a.den}; }
static Frac frac_add(Frac a, Frac b) {
    return frac_make((__int128)a.num * b.den + (__int128)b.num * a.den, (__int128)a.den * b.den);
}
static Frac frac_mul(Frac a, Frac b) {
    return frac_make((__int128)a.num * b.num, (__int128)a.den * b.den);
}
static Frac frac_div(Frac a, Frac b) {
    return frac_make((__int128)a.num * b.den, (__int128)a.den * b.num);
}

/* Confronto: negativo, zero o positivo secondo che a sia minore, uguale o
 * maggiore di b. */
static int frac_cmp(Frac a, Frac b) {
    __int128 left = (__int128)a.num * b.den, right = (__int128)b.num * a.den;
    return (left > right) - (left < right);
}

/* Parte intera inferiore di a: il più grande intero non maggiore di a. La
 * divisione del C tronca verso zero, quindi i negativi vanno corretti. */
static long long frac_floor(Frac a) {
    long long q = a.num / a.den;
    return (a.num % a.den < 0) ? q - 1 : q;
}

/* Un numero complesso re + im i a coordinate razionali: il coefficiente di un
 * termine di polinomio. */
typedef struct { Frac re, im; } Num;

static Num num_int(long long v) { return (Num){frac_int(v), frac_int(0)}; }
static Num num_frac(Frac v) { return (Num){v, frac_int(0)}; }
static int num_is_zero(Num a) { return a.re.num == 0 && a.im.num == 0; }
static int num_equal(Num a, Num b) { return frac_cmp(a.re, b.re) == 0 && frac_cmp(a.im, b.im) == 0; }
static Num num_neg(Num a) { return (Num){frac_neg(a.re), frac_neg(a.im)}; }
static Num num_add(Num a, Num b) { return (Num){frac_add(a.re, b.re), frac_add(a.im, b.im)}; }

/* (a + b i)(c + d i) = (ac - bd) + (ad + bc) i. */
static Num num_mul(Num a, Num b) {
    return (Num){frac_add(frac_mul(a.re, b.re), frac_neg(frac_mul(a.im, b.im))),
                 frac_add(frac_mul(a.re, b.im), frac_mul(a.im, b.re))};
}

/* 1 / (a + b i) = (a - b i) / (a^2 + b^2): si moltiplica sopra e sotto per il
 * coniugato. Fallisce se a + b i è zero.
 *
 * Un numero reale si inverte da solo, senza passare per a^2: quel quadrato
 * usciva dai limiti del calcolo esatto già per 1 / 11^9, e una radice cubica
 * di 11^9 non veniva calcolata. */
static Num num_inv(Num a) {
    if (a.im.num == 0) return (Num){frac_div(frac_int(1), a.re), frac_int(0)};
    Frac norm = frac_add(frac_mul(a.re, a.re), frac_mul(a.im, a.im));
    return (Num){frac_div(a.re, norm), frac_neg(frac_div(a.im, norm))};
}

/* =============================================================================
 * 4. MONOMI E ATOMI
 * ============================================================================
 *
 * Un ATOMO è una quantità che l'algebra tratta come una lettera indivisibile.
 * Ce ne sono sei tipi (le etichette da 4f a 4h sono più sotto, in
 * term_reduce()):
 *
 *   4a. VAR: una variabile dell'enunciato: n, oppure un parametro come x.
 *   4b. BIGOP: una somma o un prodotto con estremo superiore a n + c, per
 *       esempio la somma di f(k) per k da 1 a n.
 *   4c. REC: un termine X(a n + j) di una successione definita da una
 *       ricorrenza lineare, per esempio il numero di Fibonacci F(n).
 *   4d. POW: una potenza base^M, dove M è un monomio. Con M non banale è una
 *       potenza a esponente simbolico: 2^n, a^n, (n+1)^n, e^{i n x}. Con
 *       M = 1 è la base stessa presa come lettera, e serve per le radici:
 *       la radice quadrata di n + 1 è l'atomo "(n+1)" elevato a 1/2.
 *   4e. LN: il logaritmo naturale del valore assoluto di una base.
 *   4i. ATAN: l'arcotangente di un'espressione reale.
 *
 * Un MONOMIO è un prodotto di atomi elevati a esponenti razionali, anche
 * negativi: 1/2^n è il monomio (2^n)^{-1}, e^{i x/2} è (e^{i x})^{1/2}.
 *
 * Perché gli atomi si possono trattare come lettere indipendenti. Il test "è
 * zero?" cancella solo termini con lo stesso monomio. Se due monomi diversi
 * rappresentassero in realtà la stessa quantità, il test potrebbe non
 * accorgersi di uno zero (e rispondere NON DIMOSTRATO), ma non dichiarerà mai
 * nullo qualcosa che non lo è: ogni cancellazione è un'uguaglianza vera. Per
 * perdere il meno possibile, il capitolo 6 crea gli atomi in forma canonica:
 * 4^n diventa (2^n)^2, non un atomo a sé.
 */

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

/* Tabella degli atomi dell'enunciato in corso. */
static Atom atoms[MAX_ATOMS];
static int atom_count;

/* Nome della variabile su cui si fa induzione nell'enunciato in corso. */
static int induction_var = 'n';

/* Ritorna il monomio atom^exp. */
static Mono mono_atom(int atom, Frac exp) {
    Mono m;
    m.count = 1;
    m.factor[0] = (Factor){atom, exp};
    return m;
}

/* Ritorna a * b: i fattori si fondono mantenendo l'ordine, e gli esponenti
 * dello stesso atomo si sommano (x^p * x^q = x^{p+q}). Un esponente che
 * diventa zero fa sparire il fattore. */
static Mono mono_mul(const Mono *a, const Mono *b) {
    Mono r;
    r.count = 0;
    int i = 0, j = 0;
    while (i < a->count || j < b->count) {
        Factor f;
        if (j == b->count || (i < a->count && a->factor[i].atom < b->factor[j].atom)) {
            f = a->factor[i++];
        } else if (i == a->count || b->factor[j].atom < a->factor[i].atom) {
            f = b->factor[j++];
        } else {
            f = a->factor[i++];
            f.exp = frac_add(f.exp, b->factor[j++].exp);
            if (f.exp.num == 0) continue;
        }
        if (r.count == MAX_FACTORS) { fail("monomio con troppi fattori"); break; }
        r.factor[r.count++] = f;
    }
    return r;
}

/* Ritorna m^q: ogni esponente viene moltiplicato per q. */
static Mono mono_pow(const Mono *m, Frac q) {
    Mono r;
    r.count = 0;
    if (q.num == 0) return r;
    for (int i = 0; i < m->count; i++)
        r.factor[r.count++] = (Factor){m->factor[i].atom, frac_mul(m->factor[i].exp, q)};
    return r;
}

/* Ordine totale sui monomi, usato per tenere i polinomi ordinati: confronto
 * fattore per fattore, prima per atomo e poi per esponente; a parità vince il
 * più corto. Ritorna negativo, zero o positivo. */
static int mono_cmp(const Mono *a, const Mono *b) {
    for (int i = 0; i < a->count && i < b->count; i++) {
        if (a->factor[i].atom != b->factor[i].atom) return a->factor[i].atom - b->factor[i].atom;
        int c = frac_cmp(a->factor[i].exp, b->factor[i].exp);
        if (c) return c;
    }
    return a->count - b->count;
}

/* Ritorna 1 se il monomio contiene un atomo che dipende da n. */
static int mono_depends_on_n(const Mono *m) {
    for (int i = 0; i < m->count; i++)
        if (atoms[m->factor[i].atom].depends_on_n) return 1;
    return 0;
}

/* Ritorna l'esponente con cui atom compare nel monomio m, zero se manca. */
static Frac mono_exponent(const Mono *m, int atom) {
    for (int i = 0; i < m->count; i++)
        if (m->factor[i].atom == atom) return m->factor[i].exp;
    return frac_int(0);
}

/* Ritorna m con l'esponente di atom sostituito da exp (zero lo toglie). */
static Mono mono_with_exponent(const Mono *m, int atom, Frac exp) {
    Mono rest;
    rest.count = 0;
    for (int i = 0; i < m->count; i++)
        if (m->factor[i].atom != atom) rest.factor[rest.count++] = m->factor[i];
    if (exp.num == 0) return rest;
    Mono factor = mono_atom(atom, exp);
    return mono_mul(&rest, &factor);
}

/* Applica al termine t le identità che legano un atomo a un numero,
 * modificandolo sul posto. Dopo la chiamata gli esponenti interessati sono in
 * forma canonica, così monomi uguali restano riconoscibili.
 *
 * 4f. Un atomo E = e^{i pi} elevato a r:
 *       - E^2 = 1, quindi r si riduce modulo 2 all'intervallo [0, 2);
 *       - E^1 = -1, quindi da r >= 1 si toglie 1 cambiando segno al
 *         coefficiente;
 *       - E^{1/2} = e^{i pi/2} = i, quindi da r >= 1/2 si toglie 1/2
 *         moltiplicando il coefficiente per i.
 *     Resta r in [0, 1/2).
 *
 * 4g. Un atomo E = e^{i pi n} (o e^{i pi n^2}, ...): vale solo la prima
 *     regola, E^2 = e^{2 pi i n} = 1 perché n è intero. E^1 = (-1)^n resta
 *     un atomo.
 *
 * 4h. Un atomo "primo p preso come lettera" elevato a r (nasce dalle radici:
 *     la radice di 2 è p^{1/2}): la parte intera k di r è un numero vero,
 *     p^k, che passa nel coefficiente. Resta r in [0, 1). */
static void term_reduce(Term *t) {
    for (int i = 0; i < t->mono.count; i++) {
        Factor *f = &t->mono.factor[i];
        const Atom *atom = &atoms[f->atom];
        Frac r = f->exp;

        if (atom->pi != PI_NONE) {
            /* 4f, 4g. Riduzione modulo 2. */
            r = frac_add(r, frac_int(-2 * frac_floor(frac_div(r, frac_int(2)))));

            /* 4f. Estrazione di -1 e di i, solo per la costante e^{i pi}. */
            if (atom->pi == PI_CONST) {
                if (frac_cmp(r, frac_int(1)) >= 0) {
                    t->coef = num_neg(t->coef);
                    r = frac_add(r, frac_int(-1));
                }
                if (frac_cmp(r, (Frac){1, 2}) >= 0) {
                    t->coef = num_mul(t->coef, (Num){frac_int(0), frac_int(1)});
                    r = frac_add(r, (Frac){-1, 2});
                }
            }
        } else if (atom->kind == ATOM_POW && atom->base == BASE_PRIME && atom->exponent.count == 0) {
            /* 4h. Parte intera dell'esponente di un primo. */
            long long whole = frac_floor(r);
            if (whole > MAX_POWER || whole < -MAX_POWER) { fail("esponente costante troppo grande"); return; }
            Num step = num_frac(whole > 0 ? frac_int(atom->id) : (Frac){1, atom->id});
            for (long long k = (whole > 0 ? whole : -whole); k > 0 && !failure; k--) t->coef = num_mul(t->coef, step);
            r = frac_add(r, frac_int(-whole));
        } else {
            continue;
        }

        /* Il fattore sparisce se l'esponente è diventato zero. */
        f->exp = r;
        if (r.num == 0) {
            for (int j = i + 1; j < t->mono.count; j++) t->mono.factor[j - 1] = t->mono.factor[j];
            t->mono.count--;
            i--;
        }
    }
}

/* =============================================================================
 * 5. POLINOMI NEGLI ATOMI
 * ============================================================================
 *
 * Un polinomio è una somma di termini. La forma è canonica: termini ordinati
 * per monomio, monomi tutti diversi, nessun coefficiente nullo. Ne segue il
 * test su cui si regge tutto il programma: un polinomio è zero se e solo se
 * non ha termini.
 *
 * I polinomi sono valori immutabili: ogni operazione ne costruisce uno nuovo
 * nell'arena e non tocca gli operandi.
 */

/* Un polinomio in forma canonica. `term` punta a `count` termini nell'arena
 * (NULL se count == 0); la memoria è dell'arena, non del polinomio. */
typedef struct {
    int count;
    Term *term;
} Poly;

/* Confronto tra termini per qsort: ordine dei monomi. */
static int term_cmp(const void *a, const void *b) {
    return mono_cmp(&((const Term *)a)->mono, &((const Term *)b)->mono);
}

/* Ritorna spazio per capacity termini, o NULL se l'arena è piena. */
static Term *terms_alloc(long long capacity) {
    if (capacity > MAX_PRODUCT) { fail("espressione troppo grande"); return NULL; }
    return arena_alloc((size_t)capacity * sizeof(Term));
}

/* Porta in forma canonica i primi `used` termini di buffer, che era stato
 * chiesto con terms_alloc(capacity), e ritorna il polinomio risultante. */
static Poly poly_finish(Term *buffer, long long capacity, int used) {
    /* Ordina, poi somma i coefficienti dei termini con lo stesso monomio. */
    qsort(buffer, (size_t)used, sizeof(Term), term_cmp);
    int merged = 0;
    for (int i = 0; i < used; i++) {
        if (merged > 0 && mono_cmp(&buffer[merged - 1].mono, &buffer[i].mono) == 0)
            buffer[merged - 1].coef = num_add(buffer[merged - 1].coef, buffer[i].coef);
        else
            buffer[merged++] = buffer[i];
    }

    /* Elimina i termini che la somma ha annullato. */
    int count = 0;
    for (int i = 0; i < merged; i++)
        if (!num_is_zero(buffer[i].coef)) buffer[count++] = buffer[i];

    /* Restituisce all'arena lo spazio non usato. Si può fare solo se il buffer
     * è l'ultimo blocco assegnato, ed è il caso normale: il prodotto di due
     * polinomi chiede spazio per tutti i prodotti parziali, quasi tutti poi
     * fusi tra loro. Senza questo passo l'arena si riempirebbe di vuoti. */
    size_t old_bytes = arena_round((size_t)capacity * sizeof(Term));
    size_t new_bytes = arena_round((size_t)count * sizeof(Term));
    if ((char *)buffer + old_bytes == arena + arena_used) arena_used -= old_bytes - new_bytes;

    return (Poly){count, count ? buffer : NULL};
}

/* Ritorna il polinomio formato dal solo termine t (o zero se il coefficiente è
 * nullo), dopo aver applicato le identità di term_reduce(). */
static Poly poly_term(Term t) {
    term_reduce(&t);
    Term *buffer = terms_alloc(1);
    if (!buffer) return (Poly){0, NULL};
    buffer[0] = t;
    return poly_finish(buffer, 1, 1);
}

/* Ritorna il polinomio costante c. */
static Poly poly_const(Num c) {
    Term t;
    t.coef = c;
    t.mono.count = 0;
    return poly_term(t);
}

/* Ritorna a + b, oppure a - b se subtract è diverso da zero. */
static Poly poly_add(Poly a, Poly b, int subtract) {
    long long capacity = (long long)a.count + b.count;
    Term *buffer = terms_alloc(capacity);
    if (!buffer) return (Poly){0, NULL};
    for (int i = 0; i < a.count; i++) buffer[i] = a.term[i];
    for (int i = 0; i < b.count; i++) {
        buffer[a.count + i] = b.term[i];
        if (subtract) buffer[a.count + i].coef = num_neg(b.term[i].coef);
    }
    return poly_finish(buffer, capacity, (int)capacity);
}

/* Ritorna a * b: ogni termine di a per ogni termine di b. */
static Poly poly_mul(Poly a, Poly b) {
    long long capacity = (long long)a.count * b.count;
    Term *buffer = terms_alloc(capacity);
    if (!buffer) return (Poly){0, NULL};
    int used = 0;
    for (int i = 0; i < a.count; i++)
        for (int j = 0; j < b.count; j++) {
            Term t;
            t.coef = num_mul(a.term[i].coef, b.term[j].coef);
            t.mono = mono_mul(&a.term[i].mono, &b.term[j].mono);
            term_reduce(&t);
            buffer[used++] = t;
        }
    return poly_finish(buffer, capacity, used);
}

/* Ritorna 1 se p è il polinomio costante 1. */
static int poly_is_one(Poly p) {
    return p.count == 1 && p.term[0].mono.count == 0 && num_equal(p.term[0].coef, num_int(1));
}

/* Ritorna 1 se a e b sono lo stesso polinomio. Grazie alla forma canonica
 * basta il confronto termine per termine. */
static int poly_equal(Poly a, Poly b) {
    if (a.count != b.count) return 0;
    for (int i = 0; i < a.count; i++)
        if (mono_cmp(&a.term[i].mono, &b.term[i].mono) != 0 || !num_equal(a.term[i].coef, b.term[i].coef))
            return 0;
    return 1;
}

/* Ritorna 1 se a = lambda * b per una costante lambda non nulla. */
static int poly_proportional(Poly a, Poly b) {
    if (a.count != b.count || a.count == 0) return 0;
    Num ratio = num_mul(a.term[0].coef, num_inv(b.term[0].coef));
    for (int i = 0; i < a.count; i++)
        if (mono_cmp(&a.term[i].mono, &b.term[i].mono) != 0 ||
            !num_equal(a.term[i].coef, num_mul(ratio, b.term[i].coef)))
            return 0;
    return 1;
}

/* Ritorna 1 se in p compare un atomo che dipende da n. */
static int poly_depends_on_n(Poly p) {
    for (int i = 0; i < p.count; i++)
        if (mono_depends_on_n(&p.term[i].mono)) return 1;
    return 0;
}

/* Scompone p secondo le potenze dell'atomo x: p = part[0] + part[1] x + ... +
 * part[d] x^d, con le part[j] prive di x. Ritorna il grado d (0 se x non
 * compare), oppure -1 se x compare con esponente negativo, frazionario o
 * maggiore di max_degree. part deve avere max_degree + 1 posti. */
static int poly_split(Poly p, int x, Poly *part, int max_degree) {
    int degree = 0;
    for (int j = 0; j <= max_degree; j++) {
        Term *buffer = terms_alloc(p.count);
        if (!buffer && p.count) return -1;
        int used = 0;
        for (int i = 0; i < p.count; i++) {
            /* Il termine va in part[j] se x vi compare alla j, senza x. */
            Term t = p.term[i];
            Frac e = mono_exponent(&t.mono, x);
            if (e.den != 1 || e.num < 0 || e.num > max_degree) return -1;
            if (e.num != j) continue;
            t.mono = mono_with_exponent(&t.mono, x, frac_int(0));
            buffer[used++] = t;
            if (j > degree) degree = j;
        }
        part[j] = poly_finish(buffer, p.count, used);
    }
    return degree;
}

/* Legge p come polinomio nel solo atomo x, a coefficienti razionali.
 *
 * Se p ha questa forma, con grado al più MAX_UNIVARIATE, mette in *scale il
 * più piccolo intero positivo che moltiplicato per p dà coefficienti interi,
 * in c[0..MAX_UNIVARIATE] quei coefficienti (zero dove mancano) e ritorna il
 * grado, 0 per il polinomio nullo. Altrimenti ritorna -1: quando compare un
 * altro atomo, un esponente negativo o non intero, un coefficiente complesso,
 * oppure un numero oltre il miliardo. Quest'ultimo tetto tiene lontani
 * dall'overflow i conti di chi poi usa i coefficienti. */
static int poly_coefficients(Poly p, int x, long long *c, long long *scale) {
    const long long cap = 1000000000;
    int degree = 0;

    /* Il moltiplicatore: il minimo comune multiplo dei denominatori. */
    *scale = 1;
    for (int i = 0; i < p.count; i++) {
        long long den = p.term[i].coef.re.den;
        __int128 multiple = (__int128)*scale / gcd128(*scale, den) * den;
        if (multiple > cap) return -1;
        *scale = (long long)multiple;
    }

    /* I coefficienti, ciascuno al posto del suo esponente. */
    for (int j = 0; j <= MAX_UNIVARIATE; j++) c[j] = 0;
    for (int i = 0; i < p.count; i++) {
        const Term *t = &p.term[i];
        Frac e = frac_int(0);
        if (t->mono.count == 1 && t->mono.factor[0].atom == x) e = t->mono.factor[0].exp;
        else if (t->mono.count != 0) return -1;
        if (t->coef.im.num != 0 || e.den != 1 || e.num < 0 || e.num > MAX_UNIVARIATE) return -1;
        __int128 value = (__int128)t->coef.re.num * (*scale / t->coef.re.den);
        if (value > cap || value < -cap) return -1;
        c[e.num] = (long long)value;
        if (e.num > degree) degree = (int)e.num;
    }
    return degree;
}

/* =============================================================================
 * 6. CREAZIONE DEGLI ATOMI
 * ============================================================================
 *
 * Ogni atomo è registrato una volta sola: chiedere due volte "2^n" restituisce
 * lo stesso indice. È questo a far sì che due occorrenze della stessa quantità
 * si riconoscano e si cancellino.
 */

/* Polinomi che fanno da base a un atomo POW con BASE_POLY, ciascuno una volta. */
static Poly base_polys[MAX_ATOMS];
static int base_poly_count;

/* Prototipo in avanti necessario: il confronto tra due somme guarda dentro i
 * nodi dell'albero, che sono definiti nel capitolo 8. */
static int bigop_same(const Node *a, const Node *b);

/* Cerca nella tabella un atomo uguale a proto e ne ritorna l'indice;
 * se non c'è lo aggiunge. Due atomi sono uguali se coincidono in tutti i campi
 * che li identificano; per i BIGOP l'offset non conta (vedi atom_bigop()), e
 * le somme si confrontano per come sono scritte, con bigop_same(). */
static int atom_intern(const Atom *proto) {
    for (int i = 0; i < atom_count; i++) {
        const Atom *a = &atoms[i];
        if (a->kind != proto->kind || a->id != proto->id || a->dilation != proto->dilation || a->base != proto->base)
            continue;
        if (a->kind == ATOM_BIGOP && !bigop_same(a->node, proto->node)) continue;
        if (a->kind == ATOM_REC && a->offset != proto->offset) continue;
        if (a->kind == ATOM_POW && mono_cmp(&a->exponent, &proto->exponent) != 0) continue;
        return i;
    }
    if (atom_count == MAX_ATOMS) { fail("troppe quantità distinte nell'enunciato"); return 0; }
    atoms[atom_count] = *proto;
    return atom_count++;
}

/* Ritorna l'atomo della variabile name. */
static int atom_var(int name) {
    Atom a = {0};
    a.kind = ATOM_VAR;
    a.id = name;
    a.depends_on_n = (name == induction_var);
    return atom_intern(&a);
}

/* Ritorna l'atomo della somma (o prodotto) definita da node con estremo
 * superiore dilation * n + offset.
 *
 * L'offset vale solo alla prima richiesta: fissa quale somma l'atomo
 * rappresenta, e le richieste successive con la stessa somma e la stessa
 * dilation ritornano quell'atomo anche con un offset diverso. Sta al chiamante
 * aggiungere o togliere i termini di differenza (vedi eval_bigop()).
 *
 * "La stessa somma" vuol dire scritta allo stesso modo, non lo stesso nodo:
 * due copie della somma dei k da 1 a n nello stesso enunciato sono un atomo
 * solo. Prima erano due lettere indipendenti, e il programma non riusciva a
 * dimostrare nemmeno che 2 diviso un prodotto è uguale a se stesso: dove le
 * due copie erano moltiplicate o divise per qualcosa, l'ipotesi induttiva non
 * bastava a legarle. */
static int atom_bigop(const Node *node, long long dilation, long long offset) {
    Atom a = {0};
    a.kind = ATOM_BIGOP;
    a.node = node;
    a.dilation = dilation;
    a.offset = offset;
    a.depends_on_n = 1;
    return atom_intern(&a);
}

/* Ritorna l'atomo X(dilation * n + offset) della successione del vocabolario
 * in posizione sequence. */
static int atom_rec(int sequence, long long dilation, long long offset) {
    Atom a = {0};
    a.kind = ATOM_REC;
    a.id = sequence;
    a.dilation = dilation;
    a.offset = offset;
    a.depends_on_n = 1;
    return atom_intern(&a);
}

/* Ritorna l'atomo base^exponent, con la base descritta da base e id. */
static int atom_pow(BaseKind base, long long id, const Mono *exponent) {
    Atom a = {0};
    a.kind = ATOM_POW;
    a.base = base;
    a.id = id;
    a.exponent = *exponent;

    /* Dipende da n se ne dipende l'esponente oppure la base. */
    a.depends_on_n = mono_depends_on_n(exponent) ||
                     (base == BASE_ATOM && atoms[id].depends_on_n) ||
                     (base == BASE_POLY && poly_depends_on_n(base_polys[id]));

    /* Riconosce e^{i pi} ed e^{i pi n^j}, a cui si applicano le identità di
     * term_reduce(): l'esponente deve essere pi per (eventualmente) una
     * potenza intera positiva di n, e nient'altro. */
    if (base == BASE_EI) {
        int has_pi = 0, has_n = 0, other = 0;
        for (int i = 0; i < exponent->count; i++) {
            const Atom *f = &atoms[exponent->factor[i].atom];
            Frac e = exponent->factor[i].exp;
            if (f->kind == ATOM_VAR && f->id == VAR_PI && e.num == 1 && e.den == 1) has_pi = 1;
            else if (f->kind == ATOM_VAR && f->id == induction_var && e.den == 1 && e.num > 0) has_n = 1;
            else other = 1;
        }
        if (has_pi && !other) a.pi = has_n ? PI_INTEGER : PI_CONST;
    }
    return atom_intern(&a);
}

/* Ritorna l'atomo ln|base|, con la base descritta da base e id. */
static int atom_ln(BaseKind base, long long id) {
    Atom a = {0};
    a.kind = ATOM_LN;
    a.base = base;
    a.id = id;
    a.depends_on_n = (base == BASE_ATOM && atoms[id].depends_on_n) ||
                     (base == BASE_POLY && poly_depends_on_n(base_polys[id]));
    return atom_intern(&a);
}

/* Ritorna la posizione di p in base_polys, aggiungendolo se manca. */
static int base_poly_intern(Poly p) {
    for (int i = 0; i < base_poly_count; i++)
        if (poly_equal(base_polys[i], p)) return i;
    if (base_poly_count == MAX_ATOMS) { fail("troppe basi distinte nell'enunciato"); return 0; }
    base_polys[base_poly_count] = p;
    return base_poly_count++;
}

/* =============================================================================
 * 7. FRAZIONI DI POLINOMI
 * ============================================================================
 *
 * Il valore di un'espressione è una frazione num/den di polinomi negli atomi,
 * con le regole delle frazioni di scuola:
 *
 *     a1/b1 + a2/b2 = (a1 b2 + a2 b1) / (b1 b2)
 *     a1/b1 * a2/b2 = (a1 a2) / (b1 b2)
 *     a1/b1 : a2/b2 = (a1 b2) / (b1 a2)
 *
 * Le frazioni non vengono ridotte ai minimi termini (il perché è nel commento
 * di design), con un'eccezione che non costa nulla: se il denominatore è un
 * solo termine lo si porta al numeratore cambiando segno agli esponenti. Così
 * 1/2^n diventa (2^n)^{-1} e i denominatori restano piccoli.
 *
 * Invariante: senza errori den non è mai il polinomio nullo. Per questo "la
 * frazione è zero" equivale a "num non ha termini".
 */

/* La frazione num/den. */
typedef struct { Poly num, den; } Rat;

/* Ritorna num/den, applicando la semplificazione del denominatore monomio.
 * Fallisce se den è zero. */
static Rat rat_make(Poly num, Poly den) {
    Rat r = {num, den};
    if (den.count == 0) {
        fail_undefined("divisione per zero");
        r.den = poly_const(num_int(1));
    } else if (den.count == 1 && !poly_is_one(den)) {
        Term inverse;
        inverse.coef = num_inv(den.term[0].coef);
        inverse.mono = mono_pow(&den.term[0].mono, frac_int(-1));
        r.num = poly_mul(num, poly_term(inverse));
        r.den = poly_const(num_int(1));
    }
    return r;
}

/* Frazioni elementari: l'intero v, il razionale v e l'atomo `atom`. */
static Rat rat_int(long long v) { return (Rat){poly_const(num_int(v)), poly_const(num_int(1))}; }
static Rat rat_frac(Frac v) { return (Rat){poly_const(num_frac(v)), poly_const(num_int(1))}; }
static Rat rat_atom(int atom) {
    Term t;
    t.coef = num_int(1);
    t.mono = mono_atom(atom, frac_int(1));
    return (Rat){poly_term(t), poly_const(num_int(1))};
}

/* Ritorna a + b, oppure a - b se subtract è diverso da zero. Se i denominatori
 * coincidono si sommano solo i numeratori: capita spesso, e tiene piccole le
 * frazioni. */
static Rat rat_add(Rat a, Rat b, int subtract) {
    if (poly_equal(a.den, b.den)) return rat_make(poly_add(a.num, b.num, subtract), a.den);
    return rat_make(poly_add(poly_mul(a.num, b.den), poly_mul(b.num, a.den), subtract),
                    poly_mul(a.den, b.den));
}

/* Ritorna a * b. */
static Rat rat_mul(Rat a, Rat b) { return rat_make(poly_mul(a.num, b.num), poly_mul(a.den, b.den)); }

/* CONDIZIONI DI ESISTENZA
 *
 * Una divisione, un logaritmo, una radice hanno senso solo se ciò su cui
 * operano rispetta una condizione: diverso da zero, positivo, non negativo.
 * Quando il valore è un numero la condizione si controlla sul momento (vedi
 * fail_undefined()). Quando è un'espressione in n non si può: vale per certi
 * n e non per altri. Allora la si annota in questo elenco, e chi ha chiesto
 * il conto decide poi se vale per ogni n (capitolo 13, 13c).
 *
 * L'elenco si riempie solo mentre conditions_on è diverso da zero: durante la
 * dimostrazione resta spento, perché lì le condizioni sono ipotesi
 * dell'enunciato ("vale dove i due membri sono definiti"). */

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

static Condition conditions[MAX_CONDITIONS];
static int condition_count;
static int conditions_on;    /* 1 mentre le condizioni vanno annotate */
static int conditions_lost;  /* 1 se l'elenco non è bastato a contenerle */

/* Il perché di una divisione che non è scritta nell'enunciato: la fa il
 * conto, quando riscrive un prodotto fino a n - 1 come il prodotto fino a n
 * diviso per l'ultimo fattore (vedi eval_bigop()). `rewriting` è diverso da
 * zero mentre il conto fa una divisione di questo tipo. */
static const char *const REWRITTEN = "la dimostrazione divide un prodotto per un suo fattore, che lì vale zero";
static int rewriting;

/* Annota che il prodotto dei `count` polinomi di factor[] deve rispettare
 * kind, se l'elenco è acceso. Una condizione già presente non viene ripetuta.
 * Dividere per un numero diverso da zero non pone condizioni, e lo zero è già
 * stato rifiutato da chi divide. */
static void require_product(Requirement kind, const Poly *factor, int count, const char *why) {
    if (!conditions_on || failure) return;
    if (kind == NEVER_ZERO && count == 1 && factor[0].count == 1 && factor[0].term[0].mono.count == 0) return;
    for (int i = 0; i < condition_count; i++) {
        int same = conditions[i].kind == kind && conditions[i].count == count;
        for (int f = 0; f < count && same; f++) same = poly_equal(conditions[i].factor[f], factor[f]);
        if (same) return;
    }
    if (condition_count == MAX_CONDITIONS || count > MAX_SIGN_FACTORS) { conditions_lost = 1; return; }
    Condition *c = &conditions[condition_count++];
    c->kind = kind;
    c->count = count;
    c->why = why;
    for (int f = 0; f < count; f++) c->factor[f] = factor[f];
}

/* Annota che value deve rispettare kind. */
static void require(Requirement kind, Poly value, const char *why) { require_product(kind, &value, 1, why); }

/* Ritorna a / b. Fallisce se b è la frazione nulla, e annota che b non deve
 * annullarsi (il suo denominatore è già stato annotato quando b è nata da
 * un'altra divisione). */
static Rat rat_div(Rat a, Rat b) {
    require(NEVER_ZERO, b.num, rewriting ? REWRITTEN : "divisione per zero");
    return rat_make(poly_mul(a.num, b.den), poly_mul(a.den, b.num));
}

/* Ritorna a^e per e intero, anche negativo, con a^0 = 1. Moltiplicazioni
 * ripetute: gli esponenti costanti degli enunciati sono piccoli. */
static Rat rat_pow_int(Rat a, long long e) {
    if (e < -MAX_POWER || e > MAX_POWER) { fail("esponente costante troppo grande"); return rat_int(0); }
    if (e < 0) { a = rat_div(rat_int(1), a); e = -e; }
    Rat r = rat_int(1);
    for (long long i = 0; i < e && !failure; i++) r = rat_mul(r, a);
    return r;
}

/* Ritorna p con l'atomo x sostituito da value. In p l'atomo deve comparire
 * con esponenti interi tra 0 e MAX_UNIVARIATE, altrimenti fallisce.
 *
 * Schema di Horner: p = c0 + c1 x + ... + cd x^d si calcola come
 * (...(cd x + c(d-1)) x + ...) x + c0, con d moltiplicazioni. */
static Rat poly_substitute(Poly p, int x, Rat value) {
    Poly part[MAX_UNIVARIATE + 1], one = poly_const(num_int(1));
    int degree = poly_split(p, x, part, MAX_UNIVARIATE);
    if (degree < 0) { fail("polinomio di grado troppo alto in una variabile da sostituire"); return rat_int(0); }
    Rat result = {part[degree], one};
    for (int j = degree - 1; j >= 0; j--) result = rat_add(rat_mul(result, value), (Rat){part[j], one}, 0);
    return result;
}

/* Se r è un numero (nessun atomo) lo mette in *value e ritorna 1. */
static int rat_number(Rat r, Num *value) {
    if (!poly_is_one(r.den)) return 0;
    if (r.num.count == 0) { *value = num_int(0); return 1; }
    if (r.num.count != 1 || r.num.term[0].mono.count != 0) return 0;
    *value = r.num.term[0].coef;
    return 1;
}

/* Se r è un numero intero lo mette in *value e ritorna 1. */
static int rat_integer(Rat r, long long *value) {
    Num v;
    if (!rat_number(r, &v) || v.im.num != 0 || v.re.den != 1) return 0;
    *value = v.re.num;
    return 1;
}

/* Se r ha la forma a * n + c con a e c interi (n è la variabile di induzione)
 * mette i due numeri in *a e *c e ritorna 1. Un intero è il caso a = 0. */
static int rat_affine(Rat r, long long *a, long long *c) {
    int n = atom_var(induction_var);
    *a = *c = 0;
    if (!poly_is_one(r.den)) return 0;
    for (int i = 0; i < r.num.count; i++) {
        const Term *t = &r.num.term[i];
        if (t->coef.im.num != 0 || t->coef.re.den != 1) return 0;
        if (t->mono.count == 0) *c = t->coef.re.num;
        else if (t->mono.count == 1 && t->mono.factor[0].atom == n &&
                 t->mono.factor[0].exp.num == 1 && t->mono.factor[0].exp.den == 1)
            *a = t->coef.re.num;
        else return 0;
    }
    return 1;
}

/* Se e = alpha x + beta, con x l'atomo della variabile e alpha diverso da
 * zero, mette i due razionali in *alpha e *beta e ritorna 1. */
static int rat_affine_in(Rat e, int x, Frac *alpha, Frac *beta) {
    *alpha = *beta = frac_int(0);
    if (failure || e.den.count != 1 || e.den.term[0].mono.count != 0 || e.den.term[0].coef.im.num != 0) return 0;
    for (int i = 0; i < e.num.count; i++) {
        const Term *t = &e.num.term[i];
        if (t->coef.im.num != 0) return 0;
        if (t->mono.count == 0) *beta = t->coef.re;
        else if (t->mono.count == 1 && t->mono.factor[0].atom == x && frac_cmp(t->mono.factor[0].exp, frac_int(1)) == 0) *alpha = t->coef.re;
        else return 0;
    }
    *alpha = frac_div(*alpha, e.den.term[0].coef.re);
    *beta = frac_div(*beta, e.den.term[0].coef.re);
    return alpha->num != 0 && !failure;
}

/* I capitoli 8, 9, 14, 17 e 21, cioè tutta la lettura del LaTeX, stanno in
 * parser.c: gli alberi (delle espressioni, degli enunciati sugli insiemi,
 * degli enunciati con quantificatori), i tre lettori che li costruiscono e la
 * lettura degli \item di un file .tex. Va incluso qui, dopo le frazioni di
 * polinomi che i suoi alberi nominano e prima del motore che li usa. */
#include "parser.c"

/* Il segno di derivata dentro un'espressione (9d) arriva dal lettore come un
 * nodo N_DERIV, che nessun conto sa trattare: lo sostituisce con la derivata
 * il capitolo 27 (27j), con le regole di derive() e il loro controllo con i
 * numeri. Chi legge un enunciato fatto di espressioni (capitoli 13, 18, 25)
 * chiama queste funzioni subito dopo il parsing, prima di ogni conto, ma sta
 * più in alto del capitolo 27, che a sua volta usa la valutazione, gli
 * intervalli e la tabella dei segni: per questo i prototipi sono qui.
 *
 * derivatives_expanded() ritorna l'albero con le derivate al posto dei
 * segni, oppure annota in `failure` perché un segno non si espande;
 * formula_derivatives_expanded() fa lo stesso su ogni confronto di un
 * enunciato con quantificatori. derivative_signs conta i segni espansi
 * dall'ultima volta che qualcuno l'ha azzerato. derivative_doubt() dice se
 * un enunciato deciso dalla tabella dei segni dipende da punti in cui una
 * funzione è definita ma le regole non ne danno la derivata (27l): NULL se
 * no, altrimenti il motivo. */
static Node *derivatives_expanded(Node *tree);
static void formula_derivatives_expanded(Formula *f);
static const char *derivative_doubt(const Formula *thesis);
static int derivative_signs;

/* 1 se derivative_doubt() ha trovato un estremo del dominio di una funzione
 * in cui la derivata (da tutte e due le parti) non esiste: il verdetto lo
 * dice, perché chi conta la derivata da una parte sola leggerebbe in un
 * altro modo la risposta. */
static int derivative_edges;
static const char *const DERIVATIVE_EDGES = "negli estremi del dominio la derivata, che chiede la funzione definita da tutte e due le parti, non c'è";

