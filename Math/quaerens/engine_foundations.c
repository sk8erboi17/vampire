/* MODULO engine_foundations: limiti, errori e memoria, numeri esatti, monomi,
 * polinomi, atomi, frazioni di polinomi (capitoli 1-7).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in engine_foundations.h,
 * e il resto è static. */
#include "engine_foundations.h"
#include "parser.h"

/* =============================================================================
 * 1. INCLUDE E LIMITI
 * ============================================================================
 *
 * Solo libreria standard. I limiti servono a fermare un conto che cresce
 * troppo con un NON SUPPORTATO, invece di esaurire la macchina.
 */

/* Budget di ricerca, modificabili dalla riga di comando: non cardinalita
 * massime. Anche i depositi SAT crescono entro la memoria richiesta. */
_Thread_local size_t model_memory_limit = 128u * 1024u * 1024u;
/* Budget effettivi della saturazione: visite e memoria posseduta, senza
 * fissare quante variabili, clausole o argomenti puo avere un problema. */
_Thread_local unsigned long long saturation_work_limit = 2000000;
_Thread_local size_t saturation_memory_limit = 128u * 1024u * 1024u;
_Thread_local unsigned long long model_work_limit = 20000000ULL;
/* Elementi provati dai quantificatori, in tutto, nel calcolare un enunciato
 * sui modelli (--model-steps). E un budget di lavoro come gli altri: era una
 * costante, e allora nessun --model-work faceva confermare un controesempio
 * di 83 elementi sotto quattro quantificatori. Resta sotto LLONG_MAX, perche
 * model_steps lo supera di uno per dire "conto interrotto". */
_Thread_local long long model_step_limit = 40000000LL;

/* Ritorna il budget che il motore dà al verificatore per ricalcolare un
 * modello (il terzo argomento di ck_check()): due volte e mezza il proprio,
 * il rapporto che c'è sempre stato tra i due (40 e 100 milioni). Così
 * --model-steps allarga insieme il ricalcolo del motore e quello del
 * verificatore, e un controesempio che il primo conferma il secondo lo può
 * controllare. */
long long checker_steps(void) {
    return model_step_limit <= (LLONG_MAX - 1) / 5 ? model_step_limit * 5 / 2 : LLONG_MAX - 1;
}
_Thread_local unsigned long long verification_work_limit = 20000000ULL;

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
_Thread_local const char *failure;
/* Una crescita fallita delle strutture dinamiche non puo essere cancellata
 * da un tentativo euristico: il punto d'ingresso scarta comunque l'esito. */
_Thread_local int work_allocation_failed;

/* Annota reason come causa del fallimento, se è la prima. */
void fail(const char *reason) { if (!failure) failure = reason; }

/* 1 se il conto in corso è fallito perché un'espressione non è definita nel
 * punto in cui la si calcolava: divisione per zero, logaritmo di un numero non
 * positivo, radice di un numero negativo. Serve a distinguere questo caso dai
 * limiti del programma, come i numeri troppo grandi. Chi vuole la distinzione
 * lo azzera prima del conto, insieme a `failure`. */
_Thread_local int undefined;

/* Come fail(), per i casi in cui un'espressione non è definita. */
void fail_undefined(const char *reason) {
    if (!failure) undefined = 1;
    fail(reason);
}

/* Il messaggio dell'arena piena. Ha un nome perché una ricerca che la
 * riempie (capitolo 19) lo riconosce: lì vuol dire "troppi tentativi", non
 * un enunciato fuori portata. */
const char *const OUT_OF_MEMORY = "memoria di lavoro esaurita";

/* L'arena: arena_used è il numero di byte già assegnati. Ogni thread ha la
 * sua (lo stato del motore è di ogni thread, vedi main.c), presa dalla
 * memoria la prima volta che serve: ARENA_BYTES sono troppi per stare tra le
 * variabili di ogni thread, che il sistema copia e azzera per intero. Da
 * malloc() un blocco è allineato a 16, come vuole arena_alloc(). */
static _Thread_local char *arena;
_Thread_local size_t arena_used;

/* Arrotonda bytes al multiplo di 16 successivo, l'unità di assegnazione. */
static size_t arena_round(size_t bytes) { return (bytes + 15) & ~(size_t)15; }

/* Ritorna un blocco di bytes byte, allineato a 16 e non inizializzato, oppure
 * NULL (con fail()) se l'arena è piena. */
void *arena_alloc(size_t bytes) {
    bytes = arena_round(bytes);
    if (!arena && !(arena = malloc(ARENA_BYTES))) { fail(OUT_OF_MEMORY); return NULL; }
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
void *arena_node(size_t bytes) {
    if (ARENA_BYTES - arena_used < ARENA_RESERVE + arena_round(bytes)) fail(OUT_OF_MEMORY);
    return arena_alloc(bytes);
}

/* Allarga un vettore di lavoro posseduto dal chiamante. capacity conta
 * elementi di unit byte; i dati esistenti restano validi per indice, ma
 * gli indirizzi possono cambiare. Le celle nuove sono azzerate. Overflow
 * e memoria esaurita annotano failure e lasciano intatto il vecchio blocco. */
int work_reserve(void **data, size_t *capacity, size_t need, size_t unit) {
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
void *work_arena_array(size_t count, size_t unit) {
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
_Thread_local size_t stack_budget = (size_t)4 << 20;

/* L'esito di chi esaurisce il budget della pila. Ha un nome perché prove()
 * lo mette nel verdetto al posto di ciò che i lettori, fermati a metà,
 * hanno detto. */
const char *const STACK_EXHAUSTED = "pila di lavoro esaurita: l'enunciato è troppo annidato";

_Thread_local uintptr_t stack_origin;     /* Indirizzo di una variabile locale di engine_init(): il punto da cui si misura. */
_Thread_local size_t stack_chain_levels;  /* Anelli delle catene a pettine lette nell'enunciato in corso. */
_Thread_local int stack_guard;            /* 1 mentre si lavora a un enunciato lungo: solo allora si misura. */
/* 1 se il budget è finito lavorando all'enunciato in corso. Come
 * work_allocation_failed, non lo cancella un tentativo successivo: lo
 * azzera e lo legge solo prove(). */
_Thread_local int stack_exhausted;

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
int stack_room(void) {
    if (!stack_guard) return 1;
    size_t reading = 2 * stack_used();
    if (reading > stack_budget || stack_chain_levels > (stack_budget - reading) / CHAIN_LEVEL_BYTES) stack_exhausted = 1;
    return !stack_exhausted;
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

/* Massimo comun divisore di |a| e |b| con l'algoritmo di Euclide:
 * gcd(a, b) = gcd(b, a mod b), finché il resto è zero. */
__int128 gcd128(__int128 a, __int128 b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) { __int128 t = a % b; a = b; b = t; }
    return a;
}

/* Ritorna num/den ridotta ai minimi termini. Fallisce se den è zero o se il
 * risultato esce da COEF_LIMIT. */
Frac frac_make(__int128 num, __int128 den) {
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
Frac frac_int(long long v) { return (Frac){v, 1}; }
Frac frac_neg(Frac a) { return (Frac){-a.num, a.den}; }
Frac frac_add(Frac a, Frac b) {
    return frac_make((__int128)a.num * b.den + (__int128)b.num * a.den, (__int128)a.den * b.den);
}
Frac frac_mul(Frac a, Frac b) {
    return frac_make((__int128)a.num * b.num, (__int128)a.den * b.den);
}
Frac frac_div(Frac a, Frac b) {
    return frac_make((__int128)a.num * b.den, (__int128)a.den * b.num);
}

/* Confronto: negativo, zero o positivo secondo che a sia minore, uguale o
 * maggiore di b. */
int frac_cmp(Frac a, Frac b) {
    __int128 left = (__int128)a.num * b.den, right = (__int128)b.num * a.den;
    return (left > right) - (left < right);
}

/* Parte intera inferiore di a: il più grande intero non maggiore di a. La
 * divisione del C tronca verso zero, quindi i negativi vanno corretti. */
long long frac_floor(Frac a) {
    long long q = a.num / a.den;
    return (a.num % a.den < 0) ? q - 1 : q;
}

Num num_int(long long v) { return (Num){frac_int(v), frac_int(0)}; }
Num num_frac(Frac v) { return (Num){v, frac_int(0)}; }
int num_is_zero(Num a) { return a.re.num == 0 && a.im.num == 0; }
int num_equal(Num a, Num b) { return frac_cmp(a.re, b.re) == 0 && frac_cmp(a.im, b.im) == 0; }
Num num_neg(Num a) { return (Num){frac_neg(a.re), frac_neg(a.im)}; }
Num num_add(Num a, Num b) { return (Num){frac_add(a.re, b.re), frac_add(a.im, b.im)}; }

/* (a + b i)(c + d i) = (ac - bd) + (ad + bc) i. */
Num num_mul(Num a, Num b) {
    return (Num){frac_add(frac_mul(a.re, b.re), frac_neg(frac_mul(a.im, b.im))),
                 frac_add(frac_mul(a.re, b.im), frac_mul(a.im, b.re))};
}

/* 1 / (a + b i) = (a - b i) / (a^2 + b^2): si moltiplica sopra e sotto per il
 * coniugato. Fallisce se a + b i è zero.
 *
 * Un numero reale si inverte da solo, senza passare per a^2: quel quadrato
 * usciva dai limiti del calcolo esatto già per 1 / 11^9, e una radice cubica
 * di 11^9 non veniva calcolata. */
Num num_inv(Num a) {
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

/* Tabella degli atomi dell'enunciato in corso. */
_Thread_local Atom atoms[MAX_ATOMS];
_Thread_local int atom_count;

/* Nome della variabile su cui si fa induzione nell'enunciato in corso. */
_Thread_local int induction_var = 'n';

/* Ritorna il monomio atom^exp. */
Mono mono_atom(int atom, Frac exp) {
    Mono m;
    m.count = 1;
    m.factor[0] = (Factor){atom, exp};
    return m;
}

/* Ritorna a * b: i fattori si fondono mantenendo l'ordine, e gli esponenti
 * dello stesso atomo si sommano (x^p * x^q = x^{p+q}). Un esponente che
 * diventa zero fa sparire il fattore. */
Mono mono_mul(const Mono *a, const Mono *b) {
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
Mono mono_pow(const Mono *m, Frac q) {
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
int mono_cmp(const Mono *a, const Mono *b) {
    for (int i = 0; i < a->count && i < b->count; i++) {
        if (a->factor[i].atom != b->factor[i].atom) return a->factor[i].atom - b->factor[i].atom;
        int c = frac_cmp(a->factor[i].exp, b->factor[i].exp);
        if (c) return c;
    }
    return a->count - b->count;
}

/* Ritorna 1 se il monomio contiene un atomo che dipende da n. */
int mono_depends_on_n(const Mono *m) {
    for (int i = 0; i < m->count; i++)
        if (atoms[m->factor[i].atom].depends_on_n) return 1;
    return 0;
}

/* Ritorna l'esponente con cui atom compare nel monomio m, zero se manca. */
Frac mono_exponent(const Mono *m, int atom) {
    for (int i = 0; i < m->count; i++)
        if (m->factor[i].atom == atom) return m->factor[i].exp;
    return frac_int(0);
}

/* Ritorna m con l'esponente di atom sostituito da exp (zero lo toglie). */
Mono mono_with_exponent(const Mono *m, int atom, Frac exp) {
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

/* Confronto tra termini per qsort: ordine dei monomi. */
static int term_cmp(const void *a, const void *b) {
    return mono_cmp(&((const Term *)a)->mono, &((const Term *)b)->mono);
}

/* Ritorna spazio per capacity termini, o NULL se l'arena è piena. */
Term *terms_alloc(long long capacity) {
    if (capacity > MAX_PRODUCT) { fail("espressione troppo grande"); return NULL; }
    return arena_alloc((size_t)capacity * sizeof(Term));
}

/* Porta in forma canonica i primi `used` termini di buffer, che era stato
 * chiesto con terms_alloc(capacity), e ritorna il polinomio risultante. */
Poly poly_finish(Term *buffer, long long capacity, int used) {
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
Poly poly_term(Term t) {
    term_reduce(&t);
    Term *buffer = terms_alloc(1);
    if (!buffer) return (Poly){0, NULL};
    buffer[0] = t;
    return poly_finish(buffer, 1, 1);
}

/* Ritorna il polinomio costante c. */
Poly poly_const(Num c) {
    Term t;
    t.coef = c;
    t.mono.count = 0;
    return poly_term(t);
}

/* Ritorna a + b, oppure a - b se subtract è diverso da zero. */
Poly poly_add(Poly a, Poly b, int subtract) {
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
Poly poly_mul(Poly a, Poly b) {
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
int poly_is_one(Poly p) {
    return p.count == 1 && p.term[0].mono.count == 0 && num_equal(p.term[0].coef, num_int(1));
}

/* Ritorna 1 se a e b sono lo stesso polinomio. Grazie alla forma canonica
 * basta il confronto termine per termine. */
int poly_equal(Poly a, Poly b) {
    if (a.count != b.count) return 0;
    for (int i = 0; i < a.count; i++)
        if (mono_cmp(&a.term[i].mono, &b.term[i].mono) != 0 || !num_equal(a.term[i].coef, b.term[i].coef))
            return 0;
    return 1;
}

/* Ritorna 1 se a = lambda * b per una costante lambda non nulla. */
int poly_proportional(Poly a, Poly b) {
    if (a.count != b.count || a.count == 0) return 0;
    Num ratio = num_mul(a.term[0].coef, num_inv(b.term[0].coef));
    for (int i = 0; i < a.count; i++)
        if (mono_cmp(&a.term[i].mono, &b.term[i].mono) != 0 ||
            !num_equal(a.term[i].coef, num_mul(ratio, b.term[i].coef)))
            return 0;
    return 1;
}

/* Ritorna 1 se in p compare un atomo che dipende da n. */
int poly_depends_on_n(Poly p) {
    for (int i = 0; i < p.count; i++)
        if (mono_depends_on_n(&p.term[i].mono)) return 1;
    return 0;
}

/* Scompone p secondo le potenze dell'atomo x: p = part[0] + part[1] x + ... +
 * part[d] x^d, con le part[j] prive di x. Ritorna il grado d (0 se x non
 * compare), oppure -1 se x compare con esponente negativo, frazionario o
 * maggiore di max_degree. part deve avere max_degree + 1 posti. */
int poly_split(Poly p, int x, Poly *part, int max_degree) {
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
int poly_coefficients(Poly p, int x, long long *c, long long *scale) {
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
_Thread_local Poly base_polys[MAX_ATOMS];
_Thread_local int base_poly_count;

/* Prototipo in avanti necessario: il confronto tra due somme guarda dentro i
 * nodi dell'albero, che sono definiti nel capitolo 8. */
int bigop_same(const Node *a, const Node *b);

/* Cerca nella tabella un atomo uguale a proto e ne ritorna l'indice;
 * se non c'è lo aggiunge. Due atomi sono uguali se coincidono in tutti i campi
 * che li identificano; per i BIGOP l'offset non conta (vedi atom_bigop()), e
 * le somme si confrontano per come sono scritte, con bigop_same(). */
int atom_intern(const Atom *proto) {
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
int atom_var(int name) {
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
int atom_bigop(const Node *node, long long dilation, long long offset) {
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
int atom_rec(int sequence, long long dilation, long long offset) {
    Atom a = {0};
    a.kind = ATOM_REC;
    a.id = sequence;
    a.dilation = dilation;
    a.offset = offset;
    a.depends_on_n = 1;
    return atom_intern(&a);
}

/* Ritorna l'atomo base^exponent, con la base descritta da base e id. */
int atom_pow(BaseKind base, long long id, const Mono *exponent) {
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
int atom_ln(BaseKind base, long long id) {
    Atom a = {0};
    a.kind = ATOM_LN;
    a.base = base;
    a.id = id;
    a.depends_on_n = (base == BASE_ATOM && atoms[id].depends_on_n) ||
                     (base == BASE_POLY && poly_depends_on_n(base_polys[id]));
    return atom_intern(&a);
}

/* Ritorna la posizione di p in base_polys, aggiungendolo se manca. */
int base_poly_intern(Poly p) {
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

/* Ritorna num/den, applicando la semplificazione del denominatore monomio.
 * Fallisce se den è zero. */
Rat rat_make(Poly num, Poly den) {
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
Rat rat_int(long long v) { return (Rat){poly_const(num_int(v)), poly_const(num_int(1))}; }
Rat rat_frac(Frac v) { return (Rat){poly_const(num_frac(v)), poly_const(num_int(1))}; }
Rat rat_atom(int atom) {
    Term t;
    t.coef = num_int(1);
    t.mono = mono_atom(atom, frac_int(1));
    return (Rat){poly_term(t), poly_const(num_int(1))};
}

/* Ritorna a + b, oppure a - b se subtract è diverso da zero. Se i denominatori
 * coincidono si sommano solo i numeratori: capita spesso, e tiene piccole le
 * frazioni. */
Rat rat_add(Rat a, Rat b, int subtract) {
    if (poly_equal(a.den, b.den)) return rat_make(poly_add(a.num, b.num, subtract), a.den);
    return rat_make(poly_add(poly_mul(a.num, b.den), poly_mul(b.num, a.den), subtract),
                    poly_mul(a.den, b.den));
}

/* Ritorna a * b. */
Rat rat_mul(Rat a, Rat b) { return rat_make(poly_mul(a.num, b.num), poly_mul(a.den, b.den)); }

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

_Thread_local Condition conditions[MAX_CONDITIONS];
_Thread_local int condition_count;
_Thread_local int conditions_on;    /* 1 mentre le condizioni vanno annotate */
_Thread_local int conditions_lost;  /* 1 se l'elenco non è bastato a contenerle */

/* Il perché di una divisione che non è scritta nell'enunciato: la fa il
 * conto, quando riscrive un prodotto fino a n - 1 come il prodotto fino a n
 * diviso per l'ultimo fattore (vedi eval_bigop()). `rewriting` è diverso da
 * zero mentre il conto fa una divisione di questo tipo. */
const char *const REWRITTEN = "la dimostrazione divide un prodotto per un suo fattore, che lì vale zero";
_Thread_local int rewriting;

/* Annota che il prodotto dei `count` polinomi di factor[] deve rispettare
 * kind, se l'elenco è acceso. Una condizione già presente non viene ripetuta.
 * Dividere per un numero diverso da zero non pone condizioni, e lo zero è già
 * stato rifiutato da chi divide. */
void require_product(Requirement kind, const Poly *factor, int count, const char *why) {
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
void require(Requirement kind, Poly value, const char *why) { require_product(kind, &value, 1, why); }

/* Ritorna a / b. Fallisce se b è la frazione nulla, e annota che b non deve
 * annullarsi (il suo denominatore è già stato annotato quando b è nata da
 * un'altra divisione). */
Rat rat_div(Rat a, Rat b) {
    require(NEVER_ZERO, b.num, rewriting ? REWRITTEN : "divisione per zero");
    return rat_make(poly_mul(a.num, b.den), poly_mul(a.den, b.num));
}

/* Ritorna a^e per e intero, anche negativo, con a^0 = 1. Moltiplicazioni
 * ripetute: gli esponenti costanti degli enunciati sono piccoli. */
Rat rat_pow_int(Rat a, long long e) {
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
Rat poly_substitute(Poly p, int x, Rat value) {
    Poly part[MAX_UNIVARIATE + 1], one = poly_const(num_int(1));
    int degree = poly_split(p, x, part, MAX_UNIVARIATE);
    if (degree < 0) { fail("polinomio di grado troppo alto in una variabile da sostituire"); return rat_int(0); }
    Rat result = {part[degree], one};
    for (int j = degree - 1; j >= 0; j--) result = rat_add(rat_mul(result, value), (Rat){part[j], one}, 0);
    return result;
}

/* Se r è un numero (nessun atomo) lo mette in *value e ritorna 1. */
int rat_number(Rat r, Num *value) {
    if (!poly_is_one(r.den)) return 0;
    if (r.num.count == 0) { *value = num_int(0); return 1; }
    if (r.num.count != 1 || r.num.term[0].mono.count != 0) return 0;
    *value = r.num.term[0].coef;
    return 1;
}

/* Se r è un numero intero lo mette in *value e ritorna 1. */
int rat_integer(Rat r, long long *value) {
    Num v;
    if (!rat_number(r, &v) || v.im.num != 0 || v.re.den != 1) return 0;
    *value = v.re.num;
    return 1;
}

/* Se r ha la forma a * n + c con a e c interi (n è la variabile di induzione)
 * mette i due numeri in *a e *c e ritorna 1. Un intero è il caso a = 0. */
int rat_affine(Rat r, long long *a, long long *c) {
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
int rat_affine_in(Rat e, int x, Frac *alpha, Frac *beta) {
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
