/* MODULO engine_quantifiers: enunciati con quantificatori sui numeri: le
 * regole di dimostrazione (capitoli da 18 a 18.7).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in engine_quantifiers.h,
 * e il resto è static. */
#include "engine_quantifiers.h"
#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"
#include "engine_induction.h"
#include "engine_quantifiers_verdict.h"

/* =============================================================================
 * 18. QUANTIFICATORI: REGOLE DI DIMOSTRAZIONE
 * ============================================================================
 *
 * establish() dimostra una condizione seguendone la struttura. Ogni caso è una
 * regola di deduzione, e ogni regola scrive nella dimostrazione la frase che
 * la giustifica: il testo finale è la traccia di ciò che il programma ha
 * fatto, non un riassunto scritto dopo.
 *
 * Lo stato di una dimostrazione in corso è fatto di due elenchi di variabili.
 *
 *   - Le variabili "generiche", in universal[]: quelle introdotte con "sia x
 *     un elemento di A" per dimostrare un "per ogni". Nell'algebra restano
 *     lettere, cioè atomi, e ciò che si dimostra deve valere per ogni loro
 *     valore nell'insieme.
 *   - Le variabili a cui è stato dato un valore, nell'ambiente di eval()
 *     (capitolo 11): quelle di un "esiste", legate al numero o
 *     all'espressione scelti.
 *
 * Un confronto tra due espressioni diventa così una frazione di polinomi
 * nelle sole variabili generiche, e tutto si riduce a tre domande su un
 * polinomio: è il polinomio nullo? Si annulla da qualche parte, negli insiemi
 * dati? Che segno ha? Le regole sono queste:
 *
 *   18a. Una costante non nulla non si annulla.
 *   18b. Un polinomio in una variabile si annulla solo nelle sue radici, e
 *        quelle razionali si trovano tutte.
 *   18c. Regola dei segni: su una semiretta, un polinomio senza coefficienti
 *        negativi non è negativo.
 *   18d. Un polinomio di grado d che è intero in d + 1 interi consecutivi è
 *        intero in tutti gli interi.
 *   18e. Appartenenza a un insieme numerico: intero, non sotto l'estremo
 *        inferiore, diverso dai punti tolti. Serve alle altre regole, per
 *        il valore scelto per un "esiste", ed è una regola a sé quando
 *        l'enunciato scrive x \in A come condizione (17k).
 *   18f. Ogni divisione scritta ha il divisore diverso da zero.
 *   18g. Un confronto tra numeri, o tra espressioni identiche, si decide
 *        calcolando.
 *   18h. Fattore comune: se p = e q e q non si annulla, p = 0 implica e = 0.
 *   18i. "Esiste x" con un'equazione in x: di primo grado la si risolve; di
 *        grado più alto, con coefficienti numerici, si provano le sue radici
 *        razionali. Se la condizione è una disgiunzione si prova l'equazione
 *        di ciascuna parte: "esiste x con A o B" vale se esiste x con A.
 *   18j. "Esiste x" negli altri casi: si provano i numeri più semplici.
 *   18k. "Per ogni x": si introduce una variabile generica.
 *   18l. Connettivi: una congiunzione chiede tutte le parti, a una
 *        disgiunzione ne basta una.
 *   18m. La regola di un'applicazione la definisce davvero: il valore esiste
 *        e sta nel codominio.
 *   18n. "Per ogni n" in un insieme di interi da un certo punto in su, di
 *        un'uguaglianza: per induzione, con il metodo del capitolo 13.
 *   18o. "Per ogni x" intero: per casi sul resto di x in una divisione.
 *   18p. Una variabile sola, reale o razionale, con relazioni d'ordine: la
 *        tabella dei segni. È una regola a parte: decide da sola, vero o
 *        falso, gli enunciati della sua forma, e trova gli insiemi di
 *        soluzioni; le altre regole non li vedono.
 *   18q. Il grafico di ciò che la tabella dei segni ha deciso.
 *   18s. Più ipotesi insieme: la tesi è una combinazione delle ipotesi, con
 *        dei polinomi per moltiplicatori. È il seguito di 18h, che tratta il
 *        caso di un'ipotesi sola di cui la tesi è un fattore.
 *   18r. Un enunciato fatto solo di congruenze tra interi, con moduli che
 *        sono numeri: si provano tutti i resti. Come la tabella dei segni
 *        decide da sola, vero o falso, e trova gli insiemi di soluzioni.
 *   18t. Due variabili reali, un parametro e una variabile: la retta del
 *        parametro si divide in casi, e in ognuno decide la tabella dei
 *        segni. Anche questa è una regola a parte, e risolve: i valori del
 *        parametro, o le soluzioni per ogni valore del parametro.
 *   18u. Le ipotesi "esiste k", con il loro testimone: una disgiunzione
 *        guardata tutta insieme. Ciò che un'ipotesi dice esistere riceve un
 *        nome, appartenenze e divisibilità si svolgono nella loro
 *        definizione, e il valore di un "esiste" della tesi si cerca tra i
 *        polinomi nelle variabili generiche, con il sistema lineare di 18s.
 *        È il seguito di 18i.
 *   18v. Le applicazioni definite per casi (17s): il caso di f(t) si
 *        dimostra prima di usarlo; quando non si sa, una variabile si divide
 *        nei casi che servono (un resto, un lato di un numero, un punto,
 *        l'essere un intero o un multiplo), e il valore di un "esiste" si
 *        cerca caso per caso. Le stesse distinzioni servono a ogni "esiste"
 *        il cui valore sta nell'insieme solo da un lato di un numero. Prima
 *        di tutto si dimostra che i casi definiscono un'applicazione. E una
 *        disgiunzione di "diversi" vale quando le loro condizioni non
 *        possono mancare insieme: 1 è una combinazione dei polinomi
 *        (18v-7, il seguito di 18s), come per le coppie (x + 1, 2x) \neq
 *        (0, 0). Tra gli interi c + k M non si annulla se le variabili di M
 *        non possono dividere -c/k (18v-10, accanto a 18w e alla regola dei
 *        segni di 18z: vedi divisor_excludes()). Il valore di un "esiste"
 *        che è un parametro più un numero, y = b + 1, lo trovano i testimoni
 *        di primo grado di 18z, che contano anche le lettere scritte nella
 *        regola di un'applicazione (la regola 18v-9 di prima). Tra i reali
 *        le applicazioni si svolgono nella definizione e decide la tabella
 *        dei segni (18v-8), dando dei razionali agli "esiste" in testa a ciò
 *        che resta quando le lettere sono troppe (18v-11): queste due stanno
 *        nel capitolo 19, perché decidono da capo gli enunciati svolti.
 *   18w. Una variabile intera che deve dividere un numero diverso da zero:
 *        i valori che contano sono i divisori di quel numero, finiti, e si
 *        provano tutti. Un "per ogni" diventa un caso per divisore, un
 *        "esiste" cerca tra i divisori.
 *   18x. Le potenze come lettere: 2^{n}, con n una variabile generica
 *        intera, è un numero razionale positivo, e nelle identità tra
 *        polinomi fa da lettera; il valore di un "esiste" che compare solo
 *        negli esponenti si cerca tra le combinazioni degli esponenti delle
 *        ipotesi (a = 2^{n} b, b = 2^{k} c danno a = 2^{n + k} c).
 *   18y. Le variabili reali senza relazioni d'ordine: le regole precedenti
 *        valgono anche per loro, tranne ciò che presuppone variabili
 *        razionali (le radici di 18b oltre il primo grado, "è un numero
 *        razionale" in 18e); un valore positivo che sta in \mathbb{Q} ha il
 *        nome in \mathbb{Q}^{+}, e il valore di un "esiste" si cerca anche
 *        diviso per una variabile che non è zero, come 1/q. Più in generale
 *        il nome di un'ipotesi "esiste" che ne fissa un valore positivo
 *        varia nella parte positiva del suo insieme: da y = a x, con x e y
 *        naturali, a è naturale.
 *   18z. Tre regole per i ragionamenti tra interi: un'ipotesi che dà il
 *        valore di una variabile si sostituisce nel resto (da y = a x e x =
 *        b y segue x (1 - a b) = 0, e con a, b naturali a = b = 1); un
 *        polinomio con un fattore monomio che non si annulla è zero solo
 *        dove lo è l'altro fattore (m (1 - 2a) con m naturale); un "esiste"
 *        prova anche le espressioni di primo grado più semplici nelle
 *        variabili generiche (x = 2m, y = b + 1).
 *
 * I capitoli che seguono, numerati da 18.1 a 18.19, raccolgono queste regole
 * per argomento, nell'ordine in cui un lettore ne ha bisogno: ognuno usa solo
 * ciò che sta nei capitoli prima di lui. Le etichette delle regole restano
 * quelle dell'elenco qui sopra, perché le citano commenti, test e README.
 *
 *   18.1   Lo stato della dimostrazione e la scrittura dei polinomi    18x
 *   18.2   Polinomi nelle variabili generiche              18a-18f, 18v-4, 18v-5,
 *                                                          18v-10, 18y, 18z
 *   18.3   Confronti e disgiunzioni di confronti           18g, 18h, 18s, 18v-7,
 *                                                          18z
 *   18.4   "Per ogni" ed "esiste": induzione, resti,       18n, 18o, 18v,
 *          casi di una definizione, equazioni              18i
 *   18.5   Le ipotesi "esiste", con il loro testimone      18u, 18x, 18y
 *   18.6   establish(): la dimostrazione per struttura     18e, 18j, 18k, 18l,
 *                                                          18m, 18v-6, 18w, 18z
 *   18.7   Sole congruenze: tutti i resti                  18r
 *   18.8   La tabella dei segni: numeri e polinomi         18p-1 ... 18p-6
 *          esatti, i punti
 *   18.9   Le lettere della tabella: esponenziali,         18p-8, 18p-11,
 *          logaritmi, funzioni goniometriche, famiglie     18p-13
 *   18.10  L'albero dei segni                              18p-7, 18p-9, 18p-10
 *   18.11  I confronti preparati, e la loro verità         18p-14, 18p-8, 18p-13
 *          in una riga
 *   18.12  Il controllo con i numeri                       18p-2
 *   18.13  Le righe della tabella e le soluzioni           18p-2
 *   18.14  Le soluzioni di una condizione periodica        18p-12, 18p-14
 *   18.15  Il grafico                                      18q
 *   18.16  Il verdetto della tabella e il certificato      18p, 18p-15
 *   18.17  Un parametro: la proiezione e le celle          18t-a, 18t-b
 *   18.18  Un parametro: le celle decise e scritte         18t-c, 18t-d, 18t-e
 *   18.19  Un parametro: i controlli e il verdetto         18t-f, 18t-g, 18t-h
 *
 * Il verdetto di un enunciato con quantificatori, e la verifica indipendente
 * di ciò che queste regole hanno dimostrato, sono nel capitolo 19.
 *
 * Le espressioni possono contenere anche somme, potenze e funzioni, come
 * nel capitolo 9. Le regole da 18a a 18h lavorano sui polinomi, e davanti a
 * un'espressione che non lo è semplicemente non si applicano: restano
 * l'induzione (18n) e, quando le variabili hanno un valore, il calcolo.
 *
 * Ogni regola è un'implicazione vera, quindi un "sì" è una dimostrazione. Non
 * sono complete: quando nessuna si applica la risposta è "no", e il verdetto
 * sarà NON DIMOSTRATO.
 *
 * Controllo dei passi. Prima di scrivere un fatto ricavato con un conto, la
 * regola lo ricontrolla per un'altra strada: una scomposizione rimoltiplicando
 * i fattori, una sostituzione tornando indietro, un elenco di radici
 * sostituendole una per una e cercandone di dimenticate tra i primi elementi
 * dell'insieme, una copertura con semirette guardando dove cadono quegli
 * elementi. Se il controllo fallisce la regola non si applica, e il contatore
 * unjustified_steps (capitolo 13) lo registra: così ciò che il testo afferma
 * non dipende da un solo calcolo.
 *
 * La negazione non ha regole sue. Dimostrare "non A" è stabilire A con il
 * segno rovesciato: i due quantificatori si scambiano (non per ogni x vale P
 * equivale a esiste x per cui non vale P), e così congiunzione e
 * disgiunzione. Per questo le funzioni prendono, oltre alla condizione, il
 * parametro `negated`.
 */

/* =============================================================================
 * 18.1 LO STATO DELLA DIMOSTRAZIONE E LA SCRITTURA DEI POLINOMI
 * ============================================================================
 *
 * Ciò che tutte le regole condividono. Lo stato della prova in corso: le
 * variabili generiche, i valori scelti per gli "esiste" (in chosen[], per
 * il controesempio, e nei loro nodi, per la verifica: witness_keep()), i
 * tentativi che restano, e il punto (Mark) a cui tornare quando un tentativo
 * fallisce, cancellando il testo e le scelte fatte dopo. Poi il modo di
 * scrivere nella dimostrazione un polinomio nelle variabili dell'enunciato,
 * e di ottenerlo da una frazione negli atomi (rat_polynomials()): le regole
 * che seguono lavorano tutte su polinomi così.
 */

/* Le variabili generiche della dimostrazione in corso, dalla più esterna. */
static Bound *universal;
static size_t universal_capacity;
int universal_count;

/* Una cella per variabile, invece di una maschera a 32 bit: 1 se e stata
 * nominata da un'ipotesi esistenziale. Il vettore segue quello dei legami. */
unsigned char *universal_named;
size_t universal_named_capacity;

/* Introduce una variabile generica, azzerandone la qualifica di testimone.
 * 0 e failure quando uno dei depositi non puo crescere. Gli insiemi restano
 * posseduti dagli alberi, quindi il loro indirizzo non cambia con realloc. */
int universal_push(Bound bound) {
    size_t need = (size_t)universal_count + 1;
    if (!work_reserve((void **)&universal, &universal_capacity, need, sizeof *universal) ||
        !work_reserve((void **)&universal_named, &universal_named_capacity, need, sizeof *universal_named)) return 0;
    universal_named[universal_count] = 0;
    universal[universal_count++] = bound;
    return 1;
}

/* La dimostrazione per casi sul resto in corso (regola 18o): il modulo m, o 0
 * se non ce n'è una, e il resto r del caso che si sta trattando. split_case
 * dice anche quale dei valori di un "esiste" si sta scegliendo, o
 * ricontrollando (vedi Formula): fuori dai casi vale 0. */
int split_modulus, split_case;

/* Quante volte establish() può ancora essere chiamata per la prova in corso.
 * Provare un valore dopo l'altro per più "esiste" annidati, o le due letture
 * di una lunga catena di equivalenze, fa crescere i tentativi in modo
 * esponenziale: finiti i passi la ricerca si ferma e il verdetto è NON
 * DIMOSTRATO, invece di esaurire tempo e memoria. */
int search_left;

/* Mette da parte i tentativi rimasti oltre MAX_SEARCH / 10 e ritorna quanti
 * sono; chi chiama li restituisce, con search_left += ..., quando ha finito.
 * Serve alle regole che provano molte strade (i moduli di 18o, i testimoni
 * di 18u): i loro tentativi si contano a parte, e quando non portano a nulla
 * non consumano la ricerca di chi sta intorno.
 *
 * Perché un decimo. Era un ventesimo, mille passi: la transitività di una
 * relazione tra numeri complessi (17t-4) dà un nome a quattro testimoni e ne
 * cerca altri due, tutto dentro 18u, e la sua dimostrazione chiede quasi
 * duemila passi. */
static int search_set_aside(void) {
    int outside = search_left > MAX_SEARCH / 10 ? search_left - MAX_SEARCH / 10 : 0;
    search_left -= outside;
    return outside;
}

/* Ritorna la posizione in universal[] della variabile il cui atomo è atom, o
 * -1 se atom non è una variabile generica. */
static int universal_index(int atom) {
    for (int i = 0; i < universal_count; i++)
        if (atom_var(universal[i].name) == atom) return i;
    return -1;
}

/* I numeri scelti finora, dal quantificatore più esterno. Quando la
 * dimostrazione smentisce l'enunciato, sono il controesempio da riportare. */
Choice *chosen;
static size_t chosen_capacity;
int chosen_count;

/* 1 se una scelta è stata fatta dentro un caso sul resto (18o), o dentro una
 * distinzione di casi su una variabile (18v-2): allora i numeri scelti
 * cambiano da un caso all'altro, e non formano un controesempio da
 * riportare. */
int chosen_by_cases;

/* Quante distinzioni di casi su una variabile (18v-2) racchiudono il punto
 * della dimostrazione in cui si è. */
int region_depth;

/* 18v-4. I fatti "u non divide w" del caso in esame. Nascono da una
 * distinzione di casi (18v-2): nel caso "k \nmid y" la variabile y non si
 * scrive come k s, e il fatto resta scritto qui finché dura il caso. u = 1
 * dice che w non è un intero. Le regole 18v-1 e 18v-4 li usano. */
typedef struct {
    Rat divisor;  /* u: un numero, o un'espressione nelle variabili generiche */
    Poly value;   /* w: un polinomio nelle variabili generiche */
} Exclusion;

static Exclusion *excluded;
static size_t excluded_capacity;
int excluded_count;

/* Annota che alla variabile name è stato dato il valore value. */
void choose(int name, Frac value) {
    if (split_modulus || region_depth) chosen_by_cases = 1;
    if (work_reserve((void **)&chosen, &chosen_capacity, (size_t)chosen_count + 1, sizeof *chosen))
        chosen[chosen_count++] = (Choice){name, value};
}

/* Annota nel quantificatore "esiste" f il valore value con cui la sua
 * condizione è stata dimostrata, nel caso split_case (vedi Formula): la
 * verifica del capitolo 19 lo rilegge. witness_drop() lo toglie, quando per
 * lo stesso caso si ricomincia, o il valore non va usato.
 *
 * Dentro una distinzione di casi su una variabile (18v-2) il valore non si
 * annota: cambia da un caso all'altro, e quei casi non hanno un numero come
 * quelli sul resto. La verifica cerca allora da sé un valore che renda vera
 * la condizione, come per un "esiste" che la dimostrazione non ha scelto. */
static void witness_keep(Formula *f, Rat value) {
    if (region_depth) return;
    f->has_witness |= 1u << split_case;
    f->witness[split_case] = value;
}

static void witness_drop(Formula *f) { f->has_witness &= ~(1u << split_case); }

/* Ciò che la regola 18u lascia da ricontrollare alla verifica del capitolo
 * 19: quanti valori trovati da 18u-3 sono annotati in witness_records[] (vedi
 * WitnessRecord, nel capitolo 18.5), e quante ipotesi "esiste" 18u-1 ha
 * preso con il loro testimone. Come le scelte, tornano indietro con un
 * tentativo abbandonato: di quel tentativo non resta nulla da ricontrollare. */
int record_count, hypotheses_named;

/* Un punto della dimostrazione scritta e dell'elenco delle scelte a cui si
 * può tornare quando un tentativo fallisce. */
typedef struct {
    size_t proof;  /* lunghezza del testo */
    int chosen;    /* numero di scelte */
    int records;   /* valori annotati da 18u-3 */
    int named;     /* ipotesi "esiste" prese da 18u-1 */
} Mark;

/* Ritorna il punto in cui si è adesso. */
static Mark mark_here(void) { return (Mark){proof_length, chosen_count, record_count, hypotheses_named}; }

/* Cancella il testo, le scelte e le annotazioni di 18u aggiunti dopo mark. */
static void rollback(Mark mark) {
    proof_length = mark.proof;
    proof_text[proof_length] = 0;
    chosen_count = mark.chosen;
    record_count = mark.records;
    hypotheses_named = mark.named;
}

/* Lettere da scrivere con un apice, per atomo: la regola dei segni (18c)
 * indica con x' il parametro della semiretta su cui fa variare x. */
static char primed[MAX_ATOMS];

/* Scrive il testo dell'enunciato che corrisponde alla condizione f. */
static void put_source(const Formula *f) { proof_add("%.*s", (int)(f->end - f->start), f->start); }

/* Scrive l'insieme set com'è scritto nell'enunciato. */
void put_numbers(const NumberSet *set) { proof_add("%.*s", (int)(set->end - set->start), set->start); }

/* Ritorna il grado del monomio: la somma dei suoi esponenti. */
static long long mono_degree(const Mono *m) {
    long long degree = 0;
    for (int i = 0; i < m->count; i++) degree += m->factor[i].exp.num;
    return degree;
}

/* Ritorna il termine di p che put_poly() scrive per primo: il primo, nella
 * forma canonica, tra quelli di grado più alto. p non deve essere nullo. */
static const Term *poly_leading(Poly p) {
    const Term *leading = &p.term[0];
    for (int i = 1; i < p.count; i++)
        if (mono_degree(&p.term[i].mono) > mono_degree(&leading->mono)) leading = &p.term[i];
    return leading;
}

/* Scrive in LaTeX il polinomio p, dai termini di grado più alto. p deve essere
 * un polinomio "vero" nelle variabili dell'enunciato (vedi rat_polynomials()). */
void put_poly(Poly p) {
    if (p.count == 0) { proof_add("0"); return; }
    int written = 0;
    for (long long degree = mono_degree(&poly_leading(p)->mono); degree >= 0; degree--)
        for (int i = 0; i < p.count; i++) {
            const Term *t = &p.term[i];
            if (mono_degree(&t->mono) != degree) continue;

            /* Segno e valore assoluto del coefficiente. Davanti a delle
             * lettere il coefficiente 1 non si scrive. */
            Frac size = t->coef.re;
            int negative = size.num < 0;
            if (negative) size = frac_neg(size);
            proof_add("%s", written++ ? (negative ? " - " : " + ") : (negative ? "-" : ""));
            if (t->mono.count == 0 || size.num != 1 || size.den != 1) put_frac(size);

            /* Le lettere, con apice ed esponente. Una potenza che fa da
             * lettera (18x) la scrive put_atom(), con l'esponente; dopo un
             * numero ci vuole il punto, perché 2 e 2^{n} accostati si
             * leggerebbero 22^{n}. */
            for (int k = 0; k < t->mono.count; k++) {
                const Factor *f = &t->mono.factor[k];
                if (atoms[f->atom].kind != ATOM_VAR) {
                    if (k == 0 && (size.num != 1 || size.den != 1)) proof_add(" \\cdot ");
                    else if (k) proof_add("\\,");
                    put_atom(f->atom, frac_int(f->exp.num));
                    continue;
                }
                proof_add("%c%s", (int)atoms[f->atom].id, primed[f->atom] ? "'" : "");
                if (f->exp.num != 1) proof_add("^{%lld}", f->exp.num);
            }
        }
}

/* Scrive p come fattore di un prodotto: tra parentesi se ha più termini. */
static void put_factor(Poly p) {
    if (p.count > 1) { proof_add("\\left("); put_poly(p); proof_add("\\right)"); }
    else put_poly(p);
}

/* Ritorna -p. */
Poly poly_negate(Poly p) { return poly_add(poly_const(num_int(0)), p, 1); }

/* Scrive la frazione num/den, o solo num se den è 1. Se den comincia con un
 * segno meno si cambia segno a entrambi: si legge meglio. */
static void put_ratio(Poly num, Poly den) {
    if (poly_is_one(den)) { put_poly(num); return; }
    if (poly_leading(den)->coef.re.num < 0) { num = poly_negate(num); den = poly_negate(den); }
    proof_add("\\frac{");
    put_poly(num);
    proof_add("}{");
    put_poly(den);
    proof_add("}");
}

/* Ritorna 1 se p è una costante, zero compreso. */
int poly_is_constant(Poly p) { return p.count == 0 || (p.count == 1 && p.term[0].mono.count == 0); }

/* Ritorna 1 se l'atomo x compare in p. */
int poly_uses(Poly p, int x) {
    for (int i = 0; i < p.count; i++)
        if (mono_exponent(&p.term[i].mono, x).num != 0) return 1;
    return 0;
}

/* 18x. LE POTENZE COME LETTERE
 *
 * A che cosa serve. "a = 2^{n} b con n intero" è una relazione di
 * equivalenza: con m = -n si ha b = 2^{m} a, e da a = 2^{n} b, b = 2^{k} c
 * segue a = 2^{n + k} c. Sono identità tra polinomi, purché 2^{n} e 2^{k}
 * siano lettere come le altre: (a - 2^{n} b) + 2^{n} (b - 2^{k} c) =
 * a - 2^{n} 2^{k} c. Il conto le scrive già così, perché 2^{n + k} diventa
 * 2^{n} 2^{k} e 2^{-n} l'inverso di 2^{n} (capitolo 11); ma le regole del
 * capitolo 18 lavorano solo con le variabili, e davanti a un atomo che non
 * lo è si fermavano.
 *
 * Una potenza fa da lettera quando l'esponente è un prodotto di variabili
 * generiche intere e la base è positiva e razionale: un numero positivo, o
 * una variabile generica che varia tra i razionali positivi. Allora, per
 * ogni valore delle variabili, la potenza è un numero razionale positivo.
 *
 * Perché è lecito. Un'identità tra polinomi in lettere indipendenti vale
 * per ogni valore delle lettere, quindi anche quando una lettera vale 2^{n}:
 * tutto ciò che le regole ricavano da un'identità resta vero. Le lettere
 * nuove non sono però indipendenti davvero (2^{n} è sempre positivo, e
 * dipende da n), e una regola che ragionasse sul loro insieme sbaglierebbe:
 * per questo ogni regola che guarda gli insiemi lavora soltanto sulle
 * variabili di universal[], e davanti a una potenza non si applica. La
 * regola dei segni e quella delle radici (18b, 18c) guardano
 * universal_index(), e così 18d; 18e dice di una potenza soltanto che è un
 * numero razionale, ed è vero per quanto detto sopra; 18s la usa come
 * moltiplicatore, come una variabile.
 *
 * Solo dentro la ricerca. power_letters vale 1 mentre il capitolo 18 cerca
 * una dimostrazione, e 0 altrove: la regola dei resti (18r) e la verifica del
 * capitolo 19 vogliono polinomi nelle sole variabili, e per loro una potenza
 * resta ciò che era. */
int power_letters;

/* 18x. Ritorna 1 se il monomio m è fatto di variabili generiche intere con
 * esponenti interi positivi: l'esponente di una potenza che fa da lettera. */
int power_exponent(const Mono *m) {
    for (int i = 0; i < m->count; i++) {
        int who = universal_index(m->factor[i].atom);
        Frac e = m->factor[i].exp;
        if (who < 0 || !universal[who].numbers->integers || e.den != 1 || e.num < 1) return 0;
    }
    return 1;
}

/* 18x. Ritorna 1 se l'atomo è una potenza che fa da lettera (vedi sopra):
 * esponente fatto di variabili generiche intere, con esponenti interi
 * positivi, e base un numero positivo o una variabile generica dei
 * razionali positivi. Fuori dalla ricerca (power_letters a 0) ritorna 0. */
int power_letter(int atom) {
    const Atom *a = &atoms[atom];
    if (!power_letters || a->kind != ATOM_POW || a->exponent.count == 0 || !power_exponent(&a->exponent)) return 0;
    if (a->base == BASE_PRIME) return 1;
    if (a->base == BASE_POLY) {
        Poly b = base_polys[a->id];
        return b.count == 1 && b.term[0].mono.count == 0 && b.term[0].coef.im.num == 0 && b.term[0].coef.re.num > 0;
    }
    if (a->base != BASE_ATOM) return 0;
    int who = universal_index((int)a->id);
    const NumberSet *set = who >= 0 ? universal[who].numbers : NULL;
    return set && !set->reals && set->bounded && (set->low > 0 || (set->low == 0 && set->strict));
}

/* Scrive r come frazione di due polinomi "veri": coefficienti razionali, solo
 * atomi che sono variabili (o, durante la ricerca, potenze che fanno da
 * lettere: 18x), esponenti interi non negativi. Mette i due polinomi in *num
 * e *den e ritorna 1; ritorna 0 se r non si può scrivere così.
 *
 * Serve perché rat_make() porta al numeratore un denominatore fatto di un
 * solo termine, lasciando esponenti negativi: 1/x diventa x^{-1}. Qui si fa
 * il passo inverso, moltiplicando sopra e sotto per la potenza di x che
 * manca. Dove r è definita quella potenza non è zero, quindi r si annulla
 * esattamente dove si annulla *num. */
int rat_polynomials(Rat r, Poly *num, Poly *den) {
    *num = r.num;
    *den = r.den;

    /* Solo variabili, con esponenti interi e coefficienti reali. */
    for (int side = 0; side < 2; side++) {
        Poly p = side ? r.den : r.num;
        for (int i = 0; i < p.count; i++) {
            if (p.term[i].coef.im.num != 0) return 0;
            for (int k = 0; k < p.term[i].mono.count; k++) {
                int atom = p.term[i].mono.factor[k].atom;
                if ((atoms[atom].kind != ATOM_VAR && !power_letter(atom)) || p.term[i].mono.factor[k].exp.den != 1) return 0;
            }
        }
    }

    /* Per ogni variabile, l'esponente più basso con cui compare: se è
     * negativo si moltiplica tutto per la potenza opposta. */
    for (int x = 0; x < atom_count && !failure; x++) {
        Frac lowest = frac_int(0);
        for (int side = 0; side < 2; side++) {
            Poly p = side ? *den : *num;
            for (int i = 0; i < p.count; i++) {
                Frac e = mono_exponent(&p.term[i].mono, x);
                if (frac_cmp(e, lowest) < 0) lowest = e;
            }
        }
        if (lowest.num == 0) continue;
        Term lift;
        lift.coef = num_int(1);
        lift.mono = mono_atom(x, frac_neg(lowest));
        *num = poly_mul(*num, poly_term(lift));
        *den = poly_mul(*den, poly_term(lift));
    }
    return !failure;
}

/* Scrive il valore r come frazione di due polinomi "veri" (vedi
 * rat_polynomials()), o \ldots se non lo è. */
static void put_fraction(Rat r) {
    Poly num, den;
    if (rat_polynomials(r, &num, &den)) put_ratio(num, den);
    else proof_add("\\ldots");
}

/* =============================================================================
 * 18.2 POLINOMI NELLE VARIABILI GENERICHE: ZERI, SEGNI, INTERI, APPARTENENZA
 * ============================================================================
 *
 * Le regole da 18a a 18f: dato un polinomio "vero" nelle variabili generiche
 * (rat_polynomials()), stabilire per ogni loro valore che non si annulla, che
 * ha un segno, che è un intero, che sta in un insieme numerico; e che ogni
 * divisore di un'espressione è diverso da zero. Ognuna scrive il proprio
 * ragionamento, e ricontrolla prima ciò che il testo sta per affermare: le
 * radici sostituendole (roots_confirmed()), le semirette guardando dove
 * cadono i primi elementi dell'insieme, la sostituzione tornando indietro.
 */

/* Controllo di un passo: ciò che la dimostrazione sta per dire delle radici
 * del polinomio p, nella variabile di atomo x che varia in set. Ritorna 1 se
 *
 *   - ognuno dei `roots` numeri di root[] è davvero una radice;
 *   - tra i primi elementi di set non c'è una radice che manca dall'elenco.
 *
 * rational_roots() le ha trovate con un conto su interi; qui si sostituisce
 * ogni numero nel polinomio com'è. Il secondo controllo non può essere
 * completo, ma guarda proprio dove un errore farebbe danno: una radice
 * dimenticata dentro l'insieme renderebbe falso "p non si annulla mai".
 * Se un controllo fallisce annota il passo come non giustificato e ritorna 0. */
static int roots_confirmed(Poly p, int x, const Frac *root, int roots, const NumberSet *set) {
    Frac sample[2 * SAMPLE_SIZE];
    Num value;
    for (int k = 0; k < roots; k++) {
        Rat at = poly_substitute(p, x, rat_frac(root[k]));
        if (failure) return 0;
        if (!rat_number(at, &value) || !num_is_zero(value)) { unjustified_steps++; return 0; }
    }
    numbers_sample(set, sample, 2 * SAMPLE_SIZE);
    for (int i = 0; i < 2 * SAMPLE_SIZE; i++) {
        int listed = 0;
        for (int k = 0; k < roots; k++)
            if (frac_cmp(sample[i], root[k]) == 0) listed = 1;
        if (!listed && rat_number(poly_substitute(p, x, rat_frac(sample[i])), &value) && num_is_zero(value)) { unjustified_steps++; return 0; }
    }
    return 1;
}

/* Una semiretta su cui la regola dei segni fa variare una variabile x:
 * x = origin + direction * t, con t >= 0, oppure t > 0 se strict. */
typedef struct {
    long long origin;  /* il punto di partenza */
    int direction;     /* +1 verso destra, -1 verso sinistra */
    int strict;        /* 1 se il punto di partenza è escluso */
    int used;          /* 1 se x compare nel polinomio in esame */
} Ray;

/* La semiretta in esame per ogni variabile generica, nella stessa posizione
 * di universal[]. Vale durante una chiamata a signs(). */
static Ray *ray;
static size_t ray_capacity;

/* Che cosa signs() deve stabilire di un polinomio. */
typedef enum {
    SIGN_NONNEGATIVE,  /* non è mai negativo */
    SIGN_POSITIVE,     /* è sempre positivo */
    SIGN_NONZERO       /* non è mai zero, oppure lo è solo dove lo è `guard` */
} SignGoal;

/* 18z. Ritorna 1 se il monomio a divide il monomio b: ogni suo atomo
 * compare in b con un esponente almeno uguale. */
static int mono_divides(const Mono *a, const Mono *b) {
    for (int i = 0; i < a->count; i++)
        if (frac_cmp(mono_exponent(b, a->factor[i].atom), a->factor[i].exp) < 0) return 0;
    return 1;
}

/* 18c. Regola dei segni.
 *
 * Stabilisce il segno del polinomio p per tutti i valori delle variabili
 * generiche, secondo goal, e scrive il ragionamento. Ritorna 1 se ci riesce.
 * Va chiamata con index = 0 e shown = p: shown è il polinomio di partenza, da
 * citare nel testo, mentre p cambia a ogni sostituzione.
 *
 * L'idea. Un polinomio in t >= 0 i cui coefficienti non sono negativi è una
 * somma di termini non negativi: non è negativo, ed è positivo se uno dei
 * termini lo è di sicuro (il termine noto, oppure un termine in sole variabili
 * strettamente positive). Per ricondursi a questo caso si copre l'insieme di
 * ogni variabile x con una o due semirette:
 *
 *   - un insieme con estremo inferiore c, come \mathbb{N}: x = c + t;
 *   - tutti gli interi: x = t, oppure x = -1 - t;
 *   - tutti i razionali: x = t, oppure x = -t.
 *
 * e su ciascuna si sostituisce x. Con più variabili si esaminano tutte le
 * combinazioni di semirette: il segno deve risultare in ognuna.
 *
 * Con guard e goal SIGN_NONZERO c'è un caso in più. Una somma di termini non
 * negativi è zero solo se lo è ogni termine; se tra i termini c'è una potenza
 * di una sola variabile, quella variabile deve valere zero. Se ogni termine
 * di guard contiene una variabile così forzata, dove p è zero lo è anche
 * guard. È ciò che serve per a + b con a, b >= 0: è zero solo per
 * a = b = 0, dove a - b è zero. */
static int signs(Poly shown, Poly p, const Poly *guard, int index, SignGoal goal) {
    if (failure || !work_reserve((void **)&ray, &ray_capacity, (size_t)universal_count, sizeof *ray)) return 0;

    /* 18c-1. Una variabile alla volta: le semirette che coprono il suo
     * insieme. Dopo la sostituzione x = origin + direction * x la lettera x
     * indica il parametro t della semiretta. */
    if (index < universal_count) {
        const NumberSet *set = universal[index].numbers;
        int x = atom_var(universal[index].name);
        ray[index].used = poly_uses(p, x) || (guard && poly_uses(*guard, x));
        if (!ray[index].used) return signs(shown, p, guard, index + 1, goal);

        Ray cover[2] = {{set->bounded ? set->low : 0, 1, set->bounded && set->strict, 1},
                        {set->integers ? -1 : 0, -1, 0, 1}};
        int covers = set->bounded ? 1 : 2;

        /* Controllo del passo: ogni elemento dell'insieme deve stare su una
         * delle semirette, altrimenti il ragionamento per casi ne lascerebbe
         * fuori qualcuno. Lo si verifica sui primi elementi dell'insieme: il
         * parametro t = direction * (x - origin) non deve essere negativo. */
        Frac sample[SAMPLE_SIZE];
        numbers_sample(set, sample, SAMPLE_SIZE);
        for (int i = 0; i < SAMPLE_SIZE; i++) {
            int covered = 0;
            for (int k = 0; k < covers; k++) {
                Frac t = frac_mul(frac_int(cover[k].direction), frac_add(sample[i], frac_int(-cover[k].origin)));
                if (t.num > 0 || (t.num == 0 && !cover[k].strict)) covered = 1;
            }
            if (!covered) { unjustified_steps++; return 0; }
        }
        for (int k = 0; k < covers; k++) {
            Rat line = rat_add(rat_int(cover[k].origin), rat_mul(rat_int(cover[k].direction), rat_atom(x)), 0);
            Poly moved = poly_substitute(p, x, line).num, moved_guard = {0, NULL};
            if (guard) moved_guard = poly_substitute(*guard, x, line).num;
            ray[index] = cover[k];
            if (!signs(shown, moved, guard ? &moved_guard : NULL, index + 1, goal)) return 0;
        }
        return 1;
    }

    /* 18c-2. Tutte le variabili sono su una semiretta: si guardano i
     * coefficienti. `certain` dice se c'è un termine sicuramente diverso da
     * zero; forced[i] se un termine è potenza della sola variabile i. */
    int negative = 0, positive = 0, certain = 0, constant = 0, multiples = 0;
    char forced[universal_count ? universal_count : 1];
    memset(forced, 0, sizeof forced);
    for (int i = 0; i < p.count; i++) {
        const Term *t = &p.term[i];
        int all_strict = 1;
        if (t->coef.re.num < 0) negative++; else positive++;
        for (int k = 0; k < t->mono.count; k++) {
            int who = universal_index(t->mono.factor[k].atom);
            if (who < 0) return 0;
            if (!ray[who].strict) all_strict = 0;
            if (t->mono.count == 1) forced[who] = 1;
        }
        if (all_strict) certain = 1;
        if (t->mono.count == 0) constant = 1;
    }

    /* 18c-3. Il segno che ne segue. `conclusion` è la parola con cui lo si
     * dirà, oppure NULL nel caso con guard: zero solo dove ogni termine è
     * zero, e lì deve annullarsi anche guard. */
    const char *conclusion = NULL;
    if (goal == SIGN_NONNEGATIVE && !negative) {
        conclusion = "not negative";
    } else if (goal != SIGN_NONNEGATIVE && !negative && certain) {
        conclusion = "positive";
    } else if (goal == SIGN_NONZERO && !positive && certain) {
        conclusion = "negative";
    } else if (goal == SIGN_NONZERO && guard && p.count && !(negative && positive)) {
        /* Un termine di guard si annulla se contiene una variabile forzata
         * a zero, oppure (18z) se è un multiplo di un termine di p: quando
         * ogni termine di p vale zero, vale zero anche il suo monomio, e con
         * lui ogni suo multiplo. Così a (1 - m n) = 0 con m, n naturali e a
         * intero dà a (1 - m) = 0 anche per a = 0, dove nessuna variabile è
         * forzata. */
        for (int i = 0; i < guard->count; i++) {
            int vanishes = 0;
            for (int k = 0; k < guard->term[i].mono.count; k++) {
                int who = universal_index(guard->term[i].mono.factor[k].atom);
                if (who >= 0 && forced[who]) vanishes = 1;
            }
            for (int j = 0; j < p.count && !vanishes; j++)
                if (mono_divides(&p.term[j].mono, &guard->term[i].mono)) vanishes = multiples = 1;
            if (!vanishes) return 0;
        }
    } else {
        return 0;
    }

    /* Controllo del passo: tornando indietro dalle semirette, cioè
     * sostituendo t = direction * (x - origin), si deve ritrovare il
     * polinomio di partenza. È ciò che il testo affermerà scrivendo
     * "p = ..." con le variabili nuove. */
    Rat back = {p, poly_const(num_int(1))};
    for (int i = 0; i < universal_count; i++) {
        if (!ray[i].used) continue;
        int x = atom_var(universal[i].name);
        Rat inverse = rat_mul(rat_int(ray[i].direction), rat_add(rat_atom(x), rat_int(ray[i].origin), 1));
        back = poly_substitute(back.num, x, inverse);
    }
    if (failure) return 0;
    if (!poly_is_one(back.den) || !poly_equal(back.num, shown)) { unjustified_steps++; return 0; }

    /* 18c-4. Il testo: le semirette, poi il polinomio prima e dopo la
     * sostituzione. Una variabile su una semiretta che non parte da zero
     * verso destra viene riscritta, e da lì in poi porta l'apice. */
    int listed = 0, shifted = 0;
    for (int i = 0; i < universal_count; i++) {
        if (!ray[i].used) continue;
        int name = universal[i].name;
        const char *order = ray[i].strict ? ">" : "\\ge";
        proof_add("%s", listed++ ? ", " : " For ");
        if (ray[i].origin == 0 && ray[i].direction > 0) { proof_add("$%c %s 0$", name, order); continue; }
        shifted = 1;
        proof_add("$%c = ", name);
        if (ray[i].origin) proof_add("%lld %c ", ray[i].origin, ray[i].direction > 0 ? '+' : '-');
        else proof_add("-");
        proof_add("%c'$ with $%c' %s 0$", name, name, order);
    }
    proof_add("%s $", listed ? ":" : "");
    put_poly(shown);
    for (int i = 0; i < universal_count; i++)
        primed[atom_var(universal[i].name)] = ray[i].used && (ray[i].origin != 0 || ray[i].direction < 0);
    if (shifted) { proof_add(" = "); put_poly(p); }
    proof_add("$");
    if (conclusion) {
        /* Per "non negativo" bastano i coefficienti; per un segno stretto
         * serve anche il termine sicuramente diverso da zero. */
        proof_add(" has no %s coefficient", negative ? "positive" : "negative");
        if (goal != SIGN_NONNEGATIVE) proof_add(" and %s", constant ? "a constant term" : "a term whose variables are all positive");
        proof_add(", so it is %s.", conclusion);
    } else {
        int written = 0;
        proof_add(" has no %s coefficient, so it is zero only if each of its terms is zero.", negative ? "positive" : "negative");
        for (int i = 0; i < universal_count; i++)
            if (forced[i]) proof_add("%s $%c%s = 0$", written++ ? "," : " That forces", universal[i].name, primed[atom_var(universal[i].name)] ? "'" : "");
        proof_add("%s $", written ? ", and then" : " Then");
        put_poly(*guard);
        proof_add(" = 0$%s.", multiples ? ": each of its terms has a factor forced to zero, or is a multiple of a term that is zero" : "");
    }
    memset(primed, 0, sizeof primed);
    return 1;
}

/* 18y. LE VARIABILI REALI, SENZA RELAZIONI D'ORDINE
 *
 * A che cosa serve. "a b^{-1} \in \mathbb{Q}" tra numeri reali positivi è
 * una relazione di equivalenza: a a^{-1} = 1, il reciproco di un razionale
 * diverso da zero è razionale, e (a b^{-1})(b c^{-1}) = a c^{-1}. Sono conti
 * con = e con l'appartenenza, senza disuguaglianze: la tabella dei segni non
 * li tratta, e le regole del capitolo 18 sì, purché nessuna di loro dia per
 * scontato che una variabile sia razionale. Lo davano per scontato in due:
 *
 *   18y-1. La regola delle radici (18b): un polinomio in una variabile reale
 *          può annullarsi in una radice irrazionale, come x^2 - 2, e le
 *          radici razionali non le dicono tutte. Per una variabile reale la
 *          regola vale solo al primo grado, dove l'unica radice, -r/c, è
 *          razionale.
 *   18y-2. L'appartenenza (18e): "è un numero razionale" vale per
 *          un'espressione razionale nelle variabili razionali e nelle
 *          potenze che fanno da lettere (18x), non in una variabile reale, né
 *          nelle costanti e e \pi. Che lo fosse anche lì era un errore già
 *          presente: "esiste x razionale con x = e" passava le regole, e lo
 *          fermava solo la verifica del capitolo 19.
 *
 * Le altre regole non dipendono dall'insieme in questo modo: la regola dei
 * segni (18c) copre una semiretta di reali come una di razionali, 18d e 18o
 * vogliono interi, 18j prova numeri razionali, che sono anche reali, e le
 * identità tra polinomi valgono per ogni valore delle lettere. Il valore di
 * un "esiste" tra i razionali, cercato da 18u-3, va però scritto con le sole
 * lettere razionali (`need` in combination()), e due passi servono al
 * reciproco di un razionale:
 *
 *   18y-3. Il valore cercato può essere w / v, con v una variabile generica
 *          che non vale zero (in witnesses_solve()): da x = q y segue
 *          y = (1/q) x.
 *   18y-4. Un valore sempre positivo che sta in \mathbb{Q} ha il nome in
 *          \mathbb{Q}^{+} (positive_part()), che non contiene lo zero: così
 *          da x y^{-1} = q, con x e y reali positivi, q non è zero, e si può
 *          dividere per lui. Una potenza con esponente intero negativo, come
 *          y^{-1}, è un'espressione razionale, e la sua base fa da divisore
 *          (negative_power(), term_defined()).
 *
 * Che cosa resta da sapere. La verifica del capitolo 19 prova numeri
 * razionali anche al posto delle variabili reali: su di loro "a b^{-1} \in
 * \mathbb{Q}" vale sempre, e un enunciato vero sui razionali ma falso sui
 * reali non la fermerebbe. Per questi enunciati la correttezza riposa sulle
 * regole, e i test ne contengono di falsi di quel tipo, che non devono
 * risultare dimostrati (false_number_relations.tex). */
/* Ritorna 1 se p ha coefficienti interi e contiene solo variabili generiche
 * intere: allora vale un intero per ogni loro valore. Non scrive nulla. */
static int poly_whole(Poly p) {
    for (int i = 0; i < p.count; i++) {
        if (p.term[i].coef.im.num != 0 || p.term[i].coef.re.den != 1) return 0;
        for (int k = 0; k < p.term[i].mono.count; k++) {
            const Factor *f = &p.term[i].mono.factor[k];
            int who = universal_index(f->atom);
            if (who < 0 || !universal[who].numbers->integers || f->exp.den != 1 || f->exp.num < 0) return 0;
        }
    }
    return 1;
}

/* 18v-4. Dimostra che p non si annulla perché, se fosse zero, una variabile
 * avrebbe il valore che il caso in esame esclude. Scrive il ragionamento e
 * ritorna 1 se ci riesce.
 *
 * Se p = gamma y + delta, con gamma un numero diverso da zero e delta senza y,
 * allora p = 0 vuol dire y = rho = -delta/gamma. Se nel caso in esame vale
 * "u non divide w" (excluded[]) e w, con rho al posto di y, è u per un
 * polinomio a coefficienti interi nelle variabili intere, cioè u per un
 * intero, allora p = 0 porterebbe a "u divide w": falso. È ciò che serve con
 * k \nmid b e k s + k - b, o con b \notin \mathbb{Z} e a + 1 - b. */
static int excluded_root(Poly p) {
    Poly one = poly_const(num_int(1));
    for (int e = 0; e < excluded_count && !failure; e++) {
        for (int i = 0; i < universal_count && !failure; i++) {
            Poly part[2], q, d;
            int y = atom_var(universal[i].name);
            if (!poly_uses(excluded[e].value, y) || poly_split(p, y, part, 1) != 1 || !poly_is_constant(part[1]) || part[1].count == 0) continue;
            Rat root = rat_div((Rat){poly_negate(part[0]), one}, (Rat){part[1], one});
            Rat image = poly_substitute(excluded[e].value, y, root);
            if (failure || !rat_polynomials(rat_div(image, excluded[e].divisor), &q, &d) || !poly_is_one(d) || !poly_whole(q)) continue;

            /* Controllo del passo: u per il quoziente deve ridare w. */
            Rat back = rat_add(rat_mul((Rat){q, one}, excluded[e].divisor), image, 1);
            if (failure) return 0;
            if (back.num.count != 0) { unjustified_steps++; return 0; }

            Num unit;
            int integer = rat_number(excluded[e].divisor, &unit) && num_equal(unit, num_int(1));
            /* Il testo: il valore della variabile, quello di w se w non è
             * la variabile stessa, perché è un multiplo, e il fatto del caso. */
            proof_add(" If it were zero, then $%c = ", universal[i].name);
            put_fraction(root);
            if (!poly_equal(excluded[e].value, rat_atom(y).num)) {
                proof_add("$, and so $");
                put_poly(excluded[e].value);
                proof_add(" = ");
                put_fraction(image);
            }
            if (integer) {
                proof_add("$, an integer (integer coefficients, integer variables); but in this case $");
                put_poly(excluded[e].value);
                proof_add(" \\notin \\mathbb{Z}$.");
            } else {
                proof_add("$, which is $");
                put_fraction(excluded[e].divisor);
                proof_add("$ times the integer $");
                put_poly(q);
                proof_add("$; but in this case $");
                put_fraction(excluded[e].divisor);
                proof_add(" \\nmid ");
                put_poly(excluded[e].value);
                proof_add("$.");
            }
            return 1;
        }
    }
    return 0;
}

/* Controllo del passo di 18v-5 e 18v-10: p, che la regola dichiara mai
 * nullo, non deve annullarsi in nessuna scelta dei primi elementi degli
 * insiemi delle sue variabili, dalla variabile di posto from in su. È un
 * conto diverso dalla regola: sostituisce numeri e guarda il risultato.
 * Ritorna 0 se trova uno zero (o se un conto non riesce). */
static int no_zero_on_sample(Poly p, int from) {
    Num value;
    if (failure) return 0;
    if (from == universal_count) return !rat_number((Rat){p, poly_const(num_int(1))}, &value) || !num_is_zero(value);
    int x = atom_var(universal[from].name);
    if (!poly_uses(p, x)) return no_zero_on_sample(p, from + 1);
    Frac sample[5];
    numbers_sample(universal[from].numbers, sample, 5);
    for (int i = 0; i < 5; i++) {
        Rat moved = poly_substitute(p, x, rat_frac(sample[i]));
        if (failure || !poly_is_one(moved.den) || !no_zero_on_sample(moved.num, from + 1)) return 0;
    }
    return 1;
}

/* 18v-5. Dimostra che p, a coefficienti razionali in variabili generiche
 * intere, non si annulla guardando i resti: scrive il ragionamento e ritorna
 * 1 se ci riesce.
 *
 * Moltiplicato p per il minimo comune multiplo s dei denominatori, s p =
 * g Q + c, dove c è il termine noto, g il massimo comun divisore degli altri
 * coefficienti e Q un polinomio a coefficienti interi: per valori interi
 * delle variabili Q è un intero, e s p = 0 direbbe che g divide c. Se g non
 * divide c, quindi, p non è mai zero. Così 4s - 10t - 5 = 0 non ha soluzioni
 * intere: 4s - 10t è pari, 5 no. */
static int content_excludes(Poly p) {
    long long scale = 1;
    for (int i = 0; i < p.count; i++) {
        const Term *t = &p.term[i];
        if (t->coef.im.num != 0) return 0;
        for (int k = 0; k < t->mono.count; k++) {
            int who = universal_index(t->mono.factor[k].atom);
            if (who < 0 || !universal[who].numbers->integers || t->mono.factor[k].exp.den != 1) return 0;
        }
        __int128 multiple = (__int128)scale / gcd128(scale, t->coef.re.den) * t->coef.re.den;
        if (multiple > 1000000000) return 0;
        scale = (long long)multiple;
    }
    __int128 g = 0, c = 0;
    for (int i = 0; i < p.count; i++) {
        __int128 value = (__int128)p.term[i].coef.re.num * (scale / p.term[i].coef.re.den);
        if (p.term[i].mono.count == 0) c = value;
        else g = gcd128(g, value);
    }
    if (g < 2 || c % g == 0) return 0;
    if (!no_zero_on_sample(p, 0)) { if (!failure) unjustified_steps++; return 0; }
    proof_add(" The variables are integers, and every coefficient of $");
    if (scale != 1) proof_add("%lld\\left(", scale);
    put_poly(p);
    if (scale != 1) proof_add("\\right)");
    proof_add("$ except the constant term is a multiple of $%lld$, while the constant term $%lld$ is not: so it is never zero.",
              (long long)g, (long long)c);
    return 1;
}

/* 18v-10. Dimostra che p = c + k M, con c e k numeri, c diverso da zero, e M
 * un prodotto di potenze di variabili generiche intere, non si annulla
 * perché una delle variabili non può dividere il numero che servirebbe.
 * Scrive il ragionamento e ritorna 1 se ci riesce.
 *
 * Se p = 0 allora M = -c/k: questo deve essere un intero N (M lo è), e ogni
 * variabile x di M divide M, cioè N: x è uno dei divisori di N, positivi o
 * negativi, che sono in numero finito perché N non è zero. Se nessuno di
 * loro sta nell'insieme di x, p non si annulla mai. Così a x - 1 non è mai
 * zero con a intero diverso da 1 e da -1: a dovrebbe dividere 1.
 *
 * Le altre due regole sui divisori e sui prodotti che valgono 1. È lo stesso
 * fatto di 18w, che prova uno per uno i divisori di un numero quando la
 * condizione dice "d divide c"; qui la divisibilità non è scritta, e nasce
 * dal polinomio. E un prodotto di naturali che vale 1 ha ogni fattore uguale
 * a 1 lo dice la regola dei segni con la guardia (18c, dopo la sostituzione
 * di 18z): quella dice dove p può annullarsi, a = b = 1 in 1 - a b, questa
 * che non si annulla mai, anche tra gli interi e con -c/k diverso da 1. Le
 * tre restano, perché nessuna fa ciò che fanno le altre; un enunciato che due
 * di loro sanno dimostrare lo dimostra la prima che lo prova. */
static int divisor_excludes(Poly p) {
    if (p.count != 2) return 0;
    const Term *constant = p.term[0].mono.count == 0 ? &p.term[0] : &p.term[1], *product = constant == &p.term[0] ? &p.term[1] : &p.term[0];
    if (constant->mono.count != 0 || product->mono.count == 0 || constant->coef.im.num || product->coef.im.num) return 0;
    Frac needed = frac_neg(frac_div(constant->coef.re, product->coef.re));
    if (failure || needed.den != 1 || needed.num == 0 || llabs(needed.num) > 1000000) return 0;
    for (int k = 0; k < product->mono.count; k++) {
        const Factor *f = &product->mono.factor[k];
        int who = universal_index(f->atom);
        if (who < 0 || !universal[who].numbers->integers || f->exp.den != 1 || f->exp.num < 1) return 0;
    }
    for (int k = 0; k < product->mono.count; k++) {
        int who = universal_index(product->mono.factor[k].atom), inside = 0;
        for (long long d = 1; d * d <= llabs(needed.num) && !inside; d++) {
            if (llabs(needed.num) % d) continue;
            long long pair[4] = {d, -d, llabs(needed.num) / d, -(llabs(needed.num) / d)};
            for (int j = 0; j < 4; j++) inside = inside || numbers_contain(universal[who].numbers, frac_int(pair[j]));
        }
        if (inside) continue;
        if (!no_zero_on_sample(p, 0)) { if (!failure) unjustified_steps++; return 0; }
        proof_add(" If it were zero, then $");
        Term alone = *product;
        alone.coef = num_int(1);
        put_poly(poly_term(alone));
        proof_add(" = %lld$, and $%c$, an integer that divides it, would be one of the divisors of $%lld$; none of them is in $",
                  needed.num, universal[who].name, needed.num);
        put_numbers(universal[who].numbers);
        proof_add("$.");
        return 1;
    }
    return 0;
}

/* 18a, 18b, 18c. Dimostra che il polinomio p non si annulla per nessun valore
 * delle variabili generiche; se guard non è NULL basta meno: che p si annulli
 * solo dove si annulla anche guard. Scrive il ragionamento e ritorna 1 se ci
 * riesce. p deve essere un polinomio "vero" (vedi rat_polynomials()). Le
 * regole 18v-4 e 18v-5, provate prima di 18b e dopo 18c, dimostrano qualcosa
 * di più: che p non si annulla mai. */
static int zero_only_where(Poly p, const Poly *guard) {
    if (failure || p.count == 0) return 0;

    /* 18a. Una costante. */
    if (poly_is_constant(p)) {
        proof_add(" The constant $");
        put_poly(p);
        proof_add("$ is not zero.");
        return 1;
    }

    /* 18v-4. Un fatto "u non divide w" del caso in esame può escludere la
     * radice anche quando sta nell'insieme: va guardato prima di 18b, che
     * altrimenti si fermerebbe lì. C'è solo dentro una distinzione di casi. */
    if (excluded_count && excluded_root(p)) return 1;

    /* 18b. Una sola variabile: si annulla solo nelle radici, e quelle che
     * contano stanno nell'insieme, che è fatto di razionali. */
    for (int i = 0; i < universal_count; i++) {
        long long c[MAX_UNIVARIATE + 1], scale;
        Frac root[MAX_UNIVARIATE + 1];
        const NumberSet *set = universal[i].numbers;
        int x = atom_var(universal[i].name);
        int degree = poly_coefficients(p, x, c, &scale);
        if (degree < 1) continue;

        /* 18y-1. Per una variabile reale le radici razionali sono tutte le
         * radici solo al primo grado. */
        if (set->reals && degree > 1) continue;
        int roots = rational_roots(c, degree, root);
        if (roots < 0) break;
        if (!roots_confirmed(p, x, root, roots, set)) return 0;

        /* Una radice nell'insieme è ammessa solo se lì si annulla guard. */
        int inside = 0;
        for (int k = 0; k < roots; k++) {
            Num value;
            if (!numbers_contain(set, root[k])) continue;
            if (!guard || !rat_number(poly_substitute(*guard, x, rat_frac(root[k])), &value) || !num_is_zero(value)) return 0;
            inside++;
        }

        proof_add(" The polynomial $");
        put_poly(p);
        if (roots == 0) {
            proof_add("$ has no rational root: the rational root theorem leaves finitely many candidates, and none of them is a root.");
            return 1;
        }
        proof_add("$ has the rational root%s $", roots > 1 ? "s" : "");
        for (int k = 0; k < roots; k++) {
            if (k) proof_add(",\\ ");
            put_frac(root[k]);
        }
        proof_add("$ and no other; ");
        if (!inside) {
            proof_add("%s in $", roots > 1 ? "none of them is" : "it is not");
            put_numbers(set);
            proof_add("$.");
        } else {
            proof_add("wherever a root is in $");
            put_numbers(set);
            proof_add("$, also $");
            put_poly(*guard);
            proof_add("$ is zero.");
        }
        return 1;
    }

    /* 18z. Un fattore comune che non si annulla: p = M q, con M un monomio
     * le cui lettere non valgono mai zero (variabili generiche il cui
     * insieme non contiene lo zero, o potenze di 18x, che sono positive).
     * Un prodotto di numeri è zero solo se lo è un fattore, quindi p è zero
     * esattamente dove lo è q, e basta dimostrare di q ciò che si chiede di
     * p. Così m (1 - 2a), con m naturale e a intero, non è mai zero: lo dice
     * 18b di 1 - 2a, la cui radice 1/2 non è intera. Se q non riesce, resta
     * la regola dei segni su p. */
    Mono common = poly_common(p);
    int factor = common.count > 0;
    for (int k = 0; k < common.count && factor; k++) {
        int atom = common.factor[k].atom, who = universal_index(atom);
        factor = power_letter(atom) || (who >= 0 && !numbers_contain(universal[who].numbers, frac_int(0)));
    }
    if (factor) {
        Term inverse = {num_int(1), mono_pow(&common, frac_int(-1))}, whole = {num_int(1), common};
        Poly q = poly_mul(p, poly_term(inverse));
        Mark mark = mark_here();

        /* Controllo del passo: M q deve ridare p. */
        if (failure) return 0;
        if (!poly_equal(poly_mul(q, poly_term(whole)), p)) { unjustified_steps++; return 0; }
        proof_add(" The polynomial $");
        put_poly(p);
        proof_add("$ is $");
        put_poly(poly_term(whole));
        proof_add("$ times $");
        put_factor(q);
        proof_add("$, and the letters of the first factor are never zero.");
        if (zero_only_where(q, guard)) return 1;
        rollback(mark);
    }

    /* 18c. Più variabili, o radici non determinabili: la regola dei segni.
     * Se non basta, il testo che ha scritto si toglie, e restano 18v-5, i
     * resti, e 18v-10, i divisori. Vengono dopo perché dove la regola dei
     * segni basta la dimostrazione resta quella di sempre. */
    size_t before = proof_length;
    if (signs(p, p, guard, 0, SIGN_NONZERO)) return 1;
    if (failure) return 0;
    proof_cut(before);
    return content_excludes(p) || divisor_excludes(p);
}

/* 18d. Dimostra che il polinomio p è un numero intero per ogni valore delle
 * variabili generiche, scrive il ragionamento e ritorna 1 se ci riesce.
 *
 * Due casi. Se le variabili sono intere e i coefficienti pure, è ovvio. Se p
 * ha una sola variabile n e grado d, basta che sia intero per n = 0, 1, ...,
 * d. Infatti (formula di Newton) p(n) è la somma, per k da 0 a d, di
 * D_k * binom(n, k), dove D_k è la differenza k-esima di p in zero: una
 * combinazione a coefficienti interi di p(0), ..., p(k), quindi un intero. E
 * binom(n, k) è intero per ogni n intero, anche negativo. Così (n^2 + n)/2 è
 * sempre intero, pur avendo coefficienti frazionari. */
static int always_integer(Poly p) {
    /* Le variabili devono essere tutte intere. */
    int whole = 1;
    for (int i = 0; i < p.count; i++) {
        if (p.term[i].coef.re.den != 1) whole = 0;
        for (int k = 0; k < p.term[i].mono.count; k++) {
            int who = universal_index(p.term[i].mono.factor[k].atom);
            if (who < 0 || !universal[who].numbers->integers) return 0;
        }
    }
    if (whole) {
        proof_add(" It is an integer, because the coefficients of $");
        put_poly(p);
        proof_add("$ are integers.");
        return 1;
    }

    /* Una sola variabile: i valori in 0, ..., grado. I coefficienti c sono
     * quelli di p moltiplicati per scale, quindi p(k) è intero quando scale
     * divide la somma dei c[j] k^j. Con c fino a un miliardo e k, j fino a
     * 16 la somma sta comodamente in un __int128. */
    for (int i = 0; i < universal_count; i++) {
        long long c[MAX_UNIVARIATE + 1], scale;
        int degree = poly_coefficients(p, atom_var(universal[i].name), c, &scale);
        if (degree < 1) continue;
        for (long long k = 0; k <= degree; k++) {
            __int128 value = 0;
            for (int j = degree; j >= 0; j--) value = value * k + c[j];
            if (value % scale != 0) return 0;
        }
        proof_add(" It is an integer: $");
        put_poly(p);
        proof_add("$ is an integer for $%c = 0, \\ldots, %d$, and a polynomial of degree $%d$ that is an integer at "
                  "$%d$ consecutive integers is an integer at every integer.", universal[i].name, degree, degree, degree + 1);
        return 1;
    }
    return 0;
}

/* 18e. Dimostra che value appartiene a set per ogni valore delle variabili
 * generiche, scrive il ragionamento e ritorna 1 se ci riesce. Le frasi hanno
 * per soggetto "it": chi chiama ha appena nominato il valore. */
static int always_in(Rat value, const NumberSet *set) {
    Poly num, den;
    Num number;
    if (!rat_polynomials(value, &num, &den)) return 0;

    /* Un numero: basta guardarlo. */
    if (rat_number(value, &number)) {
        if (!numbers_contain(set, number.re)) return 0;
        proof_add(" Indeed $");
        put_frac(number.re);
        proof_add("$ is in $");
        put_numbers(set);
        proof_add("$.");
        return 1;
    }

    /* Intero, se l'insieme è di interi; razionale, se è di razionali, e
     * questo lo è solo un'espressione nelle variabili razionali e nelle
     * potenze che fanno da lettere (18y-2). Ogni espressione razionale è un
     * numero reale. */
    if (set->integers) {
        if (!poly_is_one(den) || !always_integer(num)) return 0;
    } else if (set->reals) {
        proof_add(" It is a real number.");
    } else {
        for (int side = 0; side < 2; side++)
            for (int i = 0; i < (side ? den : num).count; i++) {
                const Mono *m = &(side ? den : num).term[i].mono;
                for (int k = 0; k < m->count; k++) {
                    int who = universal_index(m->factor[k].atom);
                    if (!power_letter(m->factor[k].atom) && (who < 0 || universal[who].numbers->reals)) return 0;
                }
            }
        proof_add(" It is a rational number.");
    }

    /* Non sotto l'estremo inferiore: value - low = above/den, e si guarda il
     * segno di above e quello di den. */
    if (set->bounded) {
        Poly above = poly_add(num, poly_mul(poly_const(num_int(set->low)), den), 1);
        if (set->low == 0) {
            proof_add(set->strict ? " It is positive." : " It is not negative.");
        } else {
            proof_add(" It is %s $%lld$, since subtracting $%lld$ leaves $", set->strict ? "greater than" : "at least", set->low, set->low);
            put_ratio(above, den);
            proof_add("$.");
        }
        if (!poly_is_one(den)) proof_add(" We look at the numerator and at the denominator.");
        if (!signs(above, above, NULL, 0, set->strict ? SIGN_POSITIVE : SIGN_NONNEGATIVE)) return 0;
        if (!poly_is_one(den) && !signs(den, den, NULL, 0, SIGN_POSITIVE)) return 0;
    }

    /* Diverso da ogni punto tolto: value = h vorrebbe dire num - h den = 0. */
    for (int i = 0; i < set->holes; i++) {
        Poly gap = poly_add(num, poly_mul(poly_const(num_frac(set->hole[i])), den), 1);
        proof_add(" It is not $");
        put_frac(set->hole[i]);
        proof_add("$: that would mean $");
        put_poly(gap);
        proof_add(" = 0$.");
        if (!zero_only_where(gap, NULL)) return 0;
    }
    return 1;
}

/* 18f. Dimostra che ogni divisione scritta nell'espressione node ha il
 * divisore diverso da zero, per ogni valore delle variabili generiche. Scrive
 * il ragionamento, salvo per i divisori che sono numeri, e ritorna 1 se ci
 * riesce.
 *
 * Non entra nelle regole delle applicazioni: che f(x) sia definita per x nel
 * dominio lo stabilisce una volta per tutte map_defined() (18m), e
 * term_check() garantisce che l'argomento stia nel dominio.
 *
 * Si controllano prima le divisioni più interne: un divisore si può calcolare
 * solo se ciò che contiene è definito. */
/* 18y. Ritorna 1 se node è una potenza con esponente un intero negativo
 * scritto in cifre, come b^{-1}: un'espressione razionale, dove la base non
 * è zero. */
static int negative_power(const Node *node) {
    const Node *e = node->kind == N_POW ? node->b : NULL;
    return e && e->kind == N_NEG && e->a->kind == N_NUM && e->a->value >= 1 && e->a->value <= MAX_POWER;
}

static int term_defined(const Node *node) {
    Poly num, den;
    if (!node || node->kind == N_APPLY) return 1;
    if (!term_defined(node->a) || !term_defined(node->b)) return 0;

    /* 18y. Una potenza con esponente intero negativo, come b^{-1}, è una
     * divisione per una potenza della base: la base fa da divisore. */
    if (node->kind == N_POW && negative_power(node)) {
        if (!rat_polynomials(eval(node->a), &num, &den)) return 0;
        if (poly_is_constant(num)) return num.count != 0;
        proof_add(" The base $");
        put_ratio(num, den);
        proof_add("$ of a negative power is never zero.");
        return zero_only_where(num, NULL);
    }
    if (node->kind != N_DIV) return 1;
    if (!rat_polynomials(eval(node->b), &num, &den)) return 0;
    if (poly_is_constant(num)) return num.count != 0;
    proof_add(" The divisor $");
    put_ratio(num, den);
    proof_add("$ is never zero.");
    return zero_only_where(num, NULL);
}

/* =============================================================================
 * 18.3 CONFRONTI E DISGIUNZIONI DI CONFRONTI
 * ============================================================================
 *
 * Le regole 18g, 18h e 18s, che dimostrano "per ogni valore delle variabili
 * generiche vale almeno uno di questi confronti". Ogni confronto diventa un
 * Literal: il numeratore della differenza dei due membri, calcolato dopo
 * aver controllato i divisori (18f), con ciò che si chiede (uguali o
 * diversi) tenuto conto delle negazioni. Un confronto tra espressioni che
 * non sono razionali si decide solo tra numeri (closed_gap()). Qui stanno
 * anche le leggi di De Morgan (junction()), che servono a ogni regola sui
 * connettivi.
 */

/* Un confronto dentro una disgiunzione da dimostrare. */
typedef struct {
    Formula *source;  /* il confronto com'è scritto nell'enunciato */
    int equation;     /* 1 se si chiede che i due membri siano uguali, 0 se
                         diversi: dipende dal confronto e dalle negazioni */
    int cleared;      /* 1 se value è stato ottenuto togliendo denominatori */
    int computed;     /* 1 se il confronto è stato deciso tra numeri, con
                         closed_gap(): allora value è 0 (uguali) o 1 (diversi) */
    Poly value;       /* il numeratore di membro sinistro - membro destro */
} Literal;

/* Ritorna 1 se ogni variabile dell'espressione node ha in questo momento un
 * numero per valore, cioè se l'espressione si può calcolare. shadow elenca
 * gli indici di somma che nascondono una variabile con lo stesso nome. */
static int term_is_closed(const Node *node, const NameScope *shadow) {
    Num value;
    if (!node) return 1;
    if (node->kind == N_VAR) {
        if (name_shadowed(shadow, node->name)) return 1;
        const Rat *bound = env_lookup(node->name);
        return node->name == VAR_PI || (bound && rat_number(*bound, &value));
    }
    if (node->kind == N_BIGOP) {
        if (!term_is_closed(node->a, shadow) || !term_is_closed(node->b, shadow)) return 0;
        NameScope inner = {node->name, shadow};
        return term_is_closed(node->c, &inner);
    }
    return term_is_closed(node->a, shadow) && term_is_closed(node->b, shadow) && term_is_closed(node->c, shadow);
}

/* 18g, per le espressioni che non sono razionali. Calcola i due membri del
 * confronto source, in cui ogni variabile ha un numero per valore, e decide
 * se sono uguali: ritorna 1 se lo sono, 0 se sono diversi, -1 se non lo sa
 * dire o se un membro non è definito.
 *
 * Qui "definito" non si riduce ai divisori: il conto annota le condizioni di
 * esistenza (capitolo 7) e ognuna deve risultare vera, con le regole del
 * paragrafo 13c. Senza questo passo ln(cos 2) = ln(cos 2) sarebbe "la stessa
 * espressione", e quindi vero, pur non esistendo. Che due valori siano
 * diversi si conclude solo se una di quelle regole prova che la differenza
 * non è zero. Un errore di calcolo vuol dire solo che non si sa. */
int closed_gap(const Formula *source) {
    long long where;
    if (failure || !term_is_closed(source->left, NULL) || !term_is_closed(source->right, NULL)) return -1;
    condition_count = conditions_lost = 0;
    conditions_on = 1;
    Rat gap = rat_add(eval(source->left), eval(source->right), 1);
    conditions_on = 0;
    int answer = failure || conditions_lost ? -1 : 1;
    for (int i = 0; i < condition_count && answer == 1; i++)
        if (condition_decided(&conditions[i], 1, &where) != 1) answer = -1;
    if (answer == 1 && !poly_vanishes(gap.num)) answer = condition_holds(NEVER_ZERO, gap.num, 1, &where) == 1 ? 0 : -1;
    if (failure) answer = -1;
    failure = NULL;
    return answer;
}

/* Come si legge un connettivo tenuto conto della negazione: una congiunzione
 * o una disgiunzione di due parti, ognuna con il suo segno. */
typedef struct {
    int conjunction;  /* 1 congiunzione, 0 disgiunzione */
    Formula *x, *y;   /* le due parti */
    int nx, ny;       /* 1 se la parte va presa negata */
} Junction;

/* Se f è una congiunzione, una disgiunzione o un'implicazione mette in *j il
 * modo di leggerla, negata se negated, e ritorna 1.
 *
 * Leggi di De Morgan: non (A e B) = (non A) o (non B), e viceversa. Per
 * l'implicazione: A implica B = (non A) o B, quindi la sua negazione è
 * A e (non B). */
static int junction(Formula *f, int negated, Junction *j) {
    if (f->kind != F_AND && f->kind != F_OR && f->kind != F_IMPLIES) return 0;
    j->conjunction = (f->kind == F_AND) != negated;
    j->x = f->a;
    j->y = f->b;
    j->nx = f->kind == F_IMPLIES ? !negated : negated;
    j->ny = negated;
    return 1;
}

/* Se f, negata se negated, è un confronto o una disgiunzione di confronti, li
 * aggiunge a literal[] aggiornando *count e ritorna 1. Altrimenti ritorna 0,
 * e literal[] può contenere confronti raccolti a metà, da ignorare. */
static int gather(Formula *f, int negated, Literal *literal, int *count) {
    Junction j;
    if (f->kind == F_NOT) return gather(f->a, !negated, literal, count);
    if (f->kind == F_EQUAL || f->kind == F_DISTINCT) {
        if (*count == MAX_LITERALS) return 0;
        literal[(*count)++] = (Literal){f, (f->kind == F_EQUAL) != negated, 0, 0, {0, NULL}};
        return 1;
    }
    return junction(f, negated, &j) && !j.conjunction &&
           gather(j.x, j.nx, literal, count) && gather(j.y, j.ny, literal, count);
}

/* Scrive "il confronto vale" oppure "il confronto non vale", secondo che ciò
 * che si chiede (uguali se equation) coincida o no con ciò che è scritto. */
static void put_outcome(const Formula *source, int equation) {
    proof_add(" $");
    put_source(source);
    proof_add("$ %s", (source->kind == F_EQUAL) == equation ? "holds" : "fails");
}

/* 18h, prima parte. Divide *h per e finché la divisione è esatta, lasciando
 * in *h il quoziente, e ritorna quante volte ha diviso. e deve essere di primo
 * grado, con coefficiente costante, in una variabile generica x: e = c x + r.
 *
 * Regola di Ruffini. Sia rho = -r/c la radice di e in x. Scritto h come
 * p_d x^d + ... + p_0, con i p_j senza x, il quoziente per x - rho ha
 * coefficienti q_{d-1} = p_d e q_{j-1} = p_j + rho q_j, e il resto è
 * p_0 + rho q_0. La divisione è esatta quando il resto è il polinomio nullo;
 * allora h = (x - rho) Q = e (Q / c). */
static int divide_out(Poly *h, Poly e) {
    for (int i = 0; i < universal_count; i++) {
        int x = atom_var(universal[i].name), times = 0;
        Poly linear[2];
        if (poly_split(e, x, linear, 1) != 1 || !poly_is_constant(linear[1])) continue;
        Num c = linear[1].term[0].coef;
        Poly rho = poly_mul(linear[0], poly_const(num_neg(num_inv(c))));

        for (;;) {
            Poly piece[MAX_UNIVARIATE + 1];
            int degree = poly_split(*h, x, piece, MAX_UNIVARIATE);
            if (degree < 1) break;

            /* carry vale q_j quando comincia il passo j. */
            Poly quotient = poly_const(num_int(0)), carry = piece[degree];
            for (int j = degree - 1; j >= 0; j--) {
                Term power;
                power.coef = num_int(1);
                power.mono.count = 0;
                if (j > 0) power.mono = mono_atom(x, frac_int(j));
                quotient = poly_add(quotient, poly_mul(carry, poly_term(power)), 0);
                carry = poly_add(piece[j], poly_mul(rho, carry), 0);
            }
            if (failure || carry.count != 0) break;
            *h = poly_mul(quotient, poly_const(num_inv(c)));
            times++;
        }
        return times;
    }
    return 0;
}

/* 18x. Ritorna 1 se r è un polinomio a coefficienti interi nelle variabili
 * generiche intere, con esponenti interi non negativi: un intero, per ogni
 * valore delle variabili. */
static int rat_is_integer_polynomial(Rat r) {
    if (!poly_is_one(r.den)) return 0;
    for (int i = 0; i < r.num.count; i++) {
        const Term *t = &r.num.term[i];
        if (t->coef.im.num != 0 || t->coef.re.den != 1) return 0;
        for (int k = 0; k < t->mono.count; k++) {
            int who = universal_index(t->mono.factor[k].atom);
            Frac e = t->mono.factor[k].exp;
            if (who < 0 || !universal[who].numbers->integers || e.den != 1 || e.num < 0) return 0;
        }
    }
    return 1;
}

/* 18x. Ritorna 1 se l'esponente node vale un intero per ogni valore delle
 * variabili generiche, per come è scritto: numeri interi, variabili
 * generiche intere o legate a un polinomio intero in quelle, somme,
 * differenze, prodotti e opposti. */
static int exponent_is_integer(const Node *node) {
    switch (node->kind) {
    case N_NUM:
        return 1;
    case N_VAR: {
        const Rat *bound = env_lookup(node->name);
        if (bound) return rat_is_integer_polynomial(*bound);
        int who = universal_index(atom_var(node->name));
        return who >= 0 && universal[who].numbers->integers;
    }
    case N_NEG:
        return exponent_is_integer(node->a);
    case N_ADD: case N_SUB: case N_MUL:
        return exponent_is_integer(node->a) && exponent_is_integer(node->b);
    default:
        return 0;
    }
}

/* 18x. Ritorna 1 se la base node è un razionale positivo per ogni valore
 * delle variabili generiche, per come è scritta: un numero positivo, o una
 * variabile generica che varia tra i razionali positivi. */
static int base_is_positive(const Node *node) {
    Num value;
    if (node_is_numeral(node)) return rat_number(eval(node), &value) && value.im.num == 0 && value.re.num > 0;

    /* Una potenza intera, un prodotto o un quoziente di numeri positivi è
     * positivo: (x^{n})^{m} ha una base positiva se ce l'ha x^{n}. */
    if (node->kind == N_POW) return exponent_is_integer(node->b) && base_is_positive(node->a);
    if (node->kind == N_MUL || node->kind == N_DIV) return base_is_positive(node->a) && base_is_positive(node->b);

    /* Una variabile legata a un valore (18z la lega a ciò che un'ipotesi
     * dice): positiva se il valore è un monomio con coefficiente positivo
     * nelle lettere positive, come x^{n} con x naturale. */
    const Rat *bound = node->kind == N_VAR ? env_lookup(node->name) : NULL;
    if (bound) {
        Poly num, den;
        if (!rat_polynomials(*bound, &num, &den) || num.count != 1 || den.count != 1) return 0;
        for (int side = 0; side < 2; side++) {
            const Term *t = side ? &den.term[0] : &num.term[0];
            if (t->coef.im.num != 0 || t->coef.re.num <= 0) return 0;
            for (int k = 0; k < t->mono.count; k++) {
                int atom = t->mono.factor[k].atom, who = universal_index(atom);
                const NumberSet *set = who >= 0 ? universal[who].numbers : NULL;
                if (!power_letter(atom) && !(set && set->bounded && (set->low > 0 || (set->low == 0 && set->strict)))) return 0;
            }
        }
        return 1;
    }
    if (node->kind != N_VAR || env_lookup(node->name)) return 0;
    int who = universal_index(atom_var(node->name));
    const NumberSet *set = who >= 0 ? universal[who].numbers : NULL;
    return set && !set->reals && set->bounded && (set->low > 0 || (set->low == 0 && set->strict));
}

/* Ritorna 1 se l'espressione node è razionale in questo momento: lo è per
 * come è scritta (term_is_rational()), oppure lo diventa perché ogni
 * esponente che è una lettera ha adesso per valore un intero non negativo,
 * come quando si prova e = 1 in a^{e} = a. Allora la potenza è un prodotto
 * ripetuto, e le regole sui polinomi si applicano come a ogni altro. */
static int term_is_rational_now(const Node *node) {
    Num exponent;
    if (!node || term_is_rational(node)) return 1;
    switch (node->kind) {
    case N_NEG: case N_ADD: case N_SUB: case N_MUL: case N_DIV: case N_APPLY:
        return term_is_rational_now(node->a) && term_is_rational_now(node->b);
    case N_POW: {
        /* 18x. Durante la ricerca anche una potenza con un esponente intero
         * scritto con le variabili è un numero razionale, se la base è
         * positiva: il conto ne fa delle lettere, e se non ci riesce
         * rat_polynomials() lo dirà. */
        if (power_letters && exponent_is_integer(node->b) && base_is_positive(node->a)) return 1;

        /* 18y. b^{-1}: razionale dove la base non è zero, cosa che
         * term_defined() controlla. */
        if (negative_power(node)) return term_is_rational_now(node->a);
        const Rat *bound = node->b->kind == N_VAR ? env_lookup(node->b->name) : NULL;
        return bound && rat_number(*bound, &exponent) && exponent.im.num == 0 && exponent.re.den == 1 && exponent.re.num >= 0 &&
               exponent.re.num <= MAX_POWER && term_is_rational_now(node->a);
    }
    default:
        return 0;
    }
}

/* Calcola il polinomio di ognuno dei `count` confronti di literal[], il
 * numeratore della differenza dei due membri, dopo aver controllato le
 * divisioni (18f): riempie value, cleared e computed. Ritorna 0 se un
 * confronto non si può trattare; può aver scritto, nella dimostrazione, le
 * frasi sui divisori. */
static int clause_polynomials(Literal *literal, int count) {
    for (int i = 0; i < count; i++) {
        const Formula *source = literal[i].source;
        Poly den;

        /* Espressioni non razionali: solo tra numeri, con closed_gap(). */
        literal[i].computed = !term_is_rational_now(source->left) || !term_is_rational_now(source->right);
        if (literal[i].computed) {
            int equal = closed_gap(source);
            if (equal < 0) return 0;
            literal[i].value = poly_const(num_int(equal ? 0 : 1));
            continue;
        }
        if (!term_defined(source->left) || !term_defined(source->right)) return 0;
        Rat gap = rat_add(eval(source->left), eval(source->right), 1);
        if (failure || !rat_polynomials(gap, &literal[i].value, &den)) return 0;
        literal[i].cleared = !poly_is_one(den);
    }
    return 1;
}

/* 18s. La tesi come combinazione delle ipotesi.
 *
 * "Se x - y = k e y - z = j allora x - z = k + j" usa due ipotesi insieme: la
 * regola 18h ne sa usare una sola, e solo quando la tesi ne è un fattore. Qui
 * le ipotesi sono uguaglianze H_1 = 0, ..., H_m = 0 tra polinomi, la tesi è
 * T = 0, e si cercano dei polinomi c_1, ..., c_m con
 *
 *     T = c_1 H_1 + ... + c_m H_m.
 *
 * Trovarli è una dimostrazione: è un'identità tra polinomi, quindi vale per
 * ogni valore delle variabili, e dove tutte le H_i sono zero lo è anche T.
 * Non trovarli non dice nulla: T può annullarsi dove si annullano le H_i
 * senza esserne una combinazione (H = x^2, T = x), oppure solo tra gli
 * interi. Allora la regola non si applica.
 *
 * Un fattore che non si annulla. A volte la tesi non è una combinazione
 * delle ipotesi ma lo è un suo multiplo: da d a = d b, con d diverso da
 * zero, segue a = b, eppure a - b non è un multiplo di d a - d b. Per questo
 * si cerca anche g T = c_1 H_1 + ... + c_m H_m con g una variabile generica
 * il cui insieme non contiene lo zero: dove le H_i sono zero lo è g T, e
 * poiché g non è zero lo è T. Che g non si annulli lo dimostra, e lo
 * scrive, la regola 18b.
 *
 * La ricerca. Si fissa l'elenco dei "generatori" m H_i, con m un monomio
 * nelle variabili generiche di grado al più top - grado(H_i), dove top è il
 * grado di ciò che si vuole ottenere: i moltiplicatori cercati sono le
 * combinazioni a coefficienti razionali di questi monomi. Trovare i
 * coefficienti è un sistema lineare, risolto per eliminazione: ogni
 * generatore serve a togliere un monomio dai successivi e da T, e alla fine
 * T deve essere diventato il polinomio nullo.
 *
 * Il controllo. I moltiplicatori trovati sono dati: chi chiama ricalcola
 * c_1 H_1 + ... + c_m H_m con prodotti e somme e lo confronta con T. Un
 * errore nell'eliminazione produce moltiplicatori sbagliati, che quel
 * confronto respinge.
 *
 * La stessa ricerca serve alla regola 18u, che tra i moltiplicatori cerca
 * anche il valore di un "esiste": per lei alcuni dei polinomi dati possono
 * avere per moltiplicatore solo un polinomio nelle variabili intere, o in
 * quelle razionali (vedi `need` in combination()): il valore di un "esiste"
 * tra i razionali, scritto con una variabile reale, non si saprebbe
 * razionale (18y).
 */

/* Ritorna il coefficiente con cui il monomio m compare in p, zero se manca. */
static Frac poly_coefficient(Poly p, const Mono *m) {
    for (int i = 0; i < p.count; i++)
        if (mono_cmp(&p.term[i].mono, m) == 0) return p.term[i].coef.re;
    return frac_int(0);
}

/* Ritorna il grado di p: il più alto tra i gradi dei suoi monomi. */
static long long poly_degree(Poly p) {
    long long degree = 0;
    for (int i = 0; i < p.count; i++)
        if (mono_degree(&p.term[i].mono) > degree) degree = mono_degree(&p.term[i].mono);
    return degree;
}

/* Un generatore di 18s: il monomio `by` per l'ipotesi di posto owner. */
typedef struct {
    int owner;  /* quale ipotesi */
    Mono by;    /* il monomio che la moltiplica */
    Poly left;  /* ciò che ne resta durante l'eliminazione */
} Generator;

/* Che cosa vale sempre una lettera dei moltiplicatori di 18s, e che cosa si
 * chiede a quelle del moltiplicatore di un'ipotesi: un numero qualsiasi, un
 * razionale, un intero. L'ordine conta: una lettera va bene per una
 * richiesta se il suo tipo non è più basso. */
enum { LETTER_REAL, LETTER_RATIONAL, LETTER_INTEGER };

/* Le lettere con cui 18s forma i monomi dei moltiplicatori: le variabili
 * generiche, e poi le potenze che fanno da lettere (18x) che compaiono nei
 * polinomi in esame. letter_kind[i] dice che cosa vale sempre la lettera i:
 * una potenza è razionale ma non intera, perché 2^{-n} non lo è, e una
 * variabile reale (18y) solo reale. Le riempie combination(). */
static int *multiplier_letter, *letter_kind, multiplier_letters;
static size_t multiplier_capacity, letter_kind_capacity;

/* Aggiunge una lettera con il suo dominio numerico; entrambi i vettori
 * sono posseduti dal calcolo della combinazione, e riusati tra chiamate. */
static int multiplier_push(int atom, int kind) {
    size_t need = (size_t)multiplier_letters + 1;
    if (!work_reserve((void **)&multiplier_letter, &multiplier_capacity, need, sizeof *multiplier_letter) ||
        !work_reserve((void **)&letter_kind, &letter_kind_capacity, need, sizeof *letter_kind)) return 0;
    letter_kind[multiplier_letters] = kind;
    multiplier_letter[multiplier_letters++] = atom;
    return 1;
}

/* 18x. Aggiunge a multiplier_letter[] le potenze che fanno da lettere nel
 * polinomio p, ognuna una volta, finché c'è posto. */
static void power_letters_add(Poly p) {
    for (int i = 0; i < p.count; i++)
        for (int k = 0; k < p.term[i].mono.count; k++) {
            int atom = p.term[i].mono.factor[k].atom, seen = 0;
            if (!power_letter(atom)) continue;
            for (int j = 0; j < multiplier_letters && !seen; j++) seen = multiplier_letter[j] == atom;
            if (!seen && !multiplier_push(atom, LETTER_RATIONAL)) return;
        }
}

/* Aggiunge a list[], che ha già *count elementi, i generatori dell'ipotesi
 * hypothesis, di posto owner: uno per ogni monomio di grado esattamente
 * degree nelle lettere di multiplier_letter[] da `from` in poi, moltiplicato
 * per `prefix`. Si usano solo le lettere il cui tipo (letter_kind[]) non è
 * più basso di need. Si ferma quando l'elenco è pieno. */
static void generators_add(Generator *list, int *count, Poly hypothesis, int owner, Mono prefix, int from, long long degree, int need) {
    if (degree == 0) {
        Term by = {num_int(1), prefix};
        if (*count < MAX_GENERATORS) list[(*count)++] = (Generator){owner, prefix, poly_mul(hypothesis, poly_term(by))};
        return;
    }
    for (int v = from; v < multiplier_letters && *count < MAX_GENERATORS; v++) {
        if (letter_kind[v] < need) continue;
        Mono letter = mono_atom(multiplier_letter[v], frac_int(1));
        generators_add(list, count, hypothesis, owner, mono_mul(&prefix, &letter), v, degree - 1, need);
    }
}

/* 18s. Cerca di scrivere thesis come combinazione dei `count` polinomi di
 * hypothesis[]: se ci riesce mette in multiplier[i] il polinomio c_i e
 * ritorna 1. I polinomi devono essere "veri" (vedi rat_polynomials()). Ogni
 * prodotto c_i H_i ha grado al più top. Se need non è NULL, il
 * moltiplicatore dell'ipotesi i contiene solo lettere che valgono sempre un
 * intero se need[i] è LETTER_INTEGER, un razionale se è LETTER_RATIONAL.
 *
 * Ogni chiamata toglie alla ricerca in corso un numero di tentativi
 * proporzionale ai generatori: un sistema grande costa quanto molti passi di
 * establish(), e senza questo conto una ricerca che ne risolve migliaia non
 * si fermerebbe più.
 *
 * L'eliminazione. I generatori si esaminano in fila: il primo monomio di
 * ciò che resta di un generatore fa da perno, e un suo multiplo viene tolto
 * da ogni generatore successivo e dalla tesi, in modo che quel monomio non
 * vi compaia più. remove[j][g] ricorda quante volte il generatore g è stato
 * tolto dal generatore j, share[g] quante volte dalla tesi. Se alla fine
 * della tesi non resta nulla, tesi = somma di share[g] per ciò che restava
 * di g; tornando indietro dall'ultimo generatore al primo, ciò che restava
 * di g è g meno i multipli dei precedenti, e i coefficienti dei generatori
 * veri si ottengono correggendo share[] con remove[][]. */
static int combination(Poly thesis, const Poly *hypothesis, int count, Poly *multiplier, long long top, const int *need) {
    static Generator list[MAX_GENERATORS];
    static Frac remove[MAX_GENERATORS][MAX_GENERATORS], share[MAX_GENERATORS];
    Mono one;
    one.count = 0;

    /* Le lettere dei moltiplicatori: le variabili generiche, poi le potenze
     * che fanno da lettere (18x). */
    multiplier_letters = 0;
    for (int v = 0; v < universal_count; v++) {
        const NumberSet *set = universal[v].numbers;

        /* Solo le variabili che compaiono nella tesi o in un'ipotesi: se
         * c'è una combinazione con una lettera che non compare in nessuno di
         * quei polinomi, mettendo zero al suo posto nei moltiplicatori se ne
         * ottiene un'altra, senza. Con le dieci variabili generiche della
         * transitività di una relazione tra numeri complessi (17t-4), i
         * generatori inutili esaurivano i tentativi. */
        int x = atom_var(universal[v].name), used = poly_uses(thesis, x);
        for (int i = 0; i < count && !used; i++) used = poly_uses(hypothesis[i], x);
        if (!used) continue;
        if (!multiplier_push(atom_var(universal[v].name), set->integers ? LETTER_INTEGER : set->reals ? LETTER_REAL : LETTER_RATIONAL)) return 0;
    }
    power_letters_add(thesis);
    for (int i = 0; i < count; i++) power_letters_add(hypothesis[i]);

    /* I generatori, per grado crescente del monomio: se l'elenco si riempie
     * restano fuori i più grandi. */
    int generators = 0;
    for (long long degree = 0; degree <= top; degree++)
        for (int i = 0; i < count; i++)
            if (poly_degree(hypothesis[i]) + degree <= top)
                generators_add(list, &generators, hypothesis[i], i, one, 0, degree, need ? need[i] : LETTER_REAL);
    search_left -= generators / 16;

    /* L'eliminazione. */
    for (int g = 0; g < generators && !failure; g++) {
        share[g] = frac_int(0);
        for (int j = g + 1; j < generators; j++) remove[j][g] = frac_int(0);
        if (list[g].left.count == 0) continue;
        const Mono *pivot = &list[g].left.term[0].mono;
        Frac lead = list[g].left.term[0].coef.re;
        for (int j = g + 1; j < generators; j++) {
            Frac times = frac_div(poly_coefficient(list[j].left, pivot), lead);
            if (times.num == 0) continue;
            remove[j][g] = times;
            list[j].left = poly_add(list[j].left, poly_mul(list[g].left, poly_const(num_frac(times))), 1);
        }
        share[g] = frac_div(poly_coefficient(thesis, pivot), lead);
        if (share[g].num != 0) thesis = poly_add(thesis, poly_mul(list[g].left, poly_const(num_frac(share[g]))), 1);
    }
    if (failure || thesis.count != 0) return 0;

    /* All'indietro: i coefficienti dei generatori veri, e i moltiplicatori. */
    for (int i = 0; i < count; i++) multiplier[i] = poly_const(num_int(0));
    for (int g = generators - 1; g >= 0; g--) {
        for (int k = 0; k < g; k++) share[k] = frac_add(share[k], frac_neg(frac_mul(share[g], remove[g][k])));
        Term part = {num_frac(share[g]), list[g].by};
        if (share[g].num != 0) multiplier[list[g].owner] = poly_add(multiplier[list[g].owner], poly_term(part), 0);
    }
    return !failure;
}

/* 18s. Dimostra che, per ogni valore delle variabili generiche, vale almeno
 * uno dei `count` confronti di literal[], quando hanno la forma "H_1 diverso
 * da 0, oppure ..., oppure T = 0" e T, o T per una variabile che non può
 * valere zero, è una combinazione delle H_i. Scrive il ragionamento, come
 * seguito di un \item già aperto, e ritorna 1 se ci riesce. I confronti che
 * non valgono mai (costanti) non contano. */
static int prove_combination(Literal *literal, int count) {
    Poly hypothesis[MAX_LITERALS], multiplier[MAX_LITERALS];
    const Literal *assumed[MAX_LITERALS], *thesis = NULL;
    int hypotheses = 0, theses = 0;
    if (!clause_polynomials(literal, count)) return 0;
    for (int i = 0; i < count; i++) {
        if (poly_is_constant(literal[i].value)) continue;
        if (literal[i].equation) { thesis = &literal[i]; theses++; continue; }
        hypothesis[hypotheses] = literal[i].value;
        assumed[hypotheses++] = &literal[i];
    }
    if (theses > 1 || !hypotheses || (!theses && hypotheses < 2)) return 0;

    /* Prima la tesi com'è; poi, una per volta, moltiplicata per una
     * variabile generica che non può valere zero. `factor` è il posto di
     * quella variabile, -1 se non è servita.
     *
     * 18v-7. Senza tesi la disgiunzione dice che le H_i non sono zero tutte
     * insieme: basta trovare 1 = c_1 H_1 + ... + c_m H_m, perché dove le H_i
     * fossero tutte zero sarebbe 1 = 0. I moltiplicatori arrivano al grado
     * delle ipotesi. Serve a confronti tra coppie, (x + 1, 2x) \neq (0, 0):
     * 1 = (x + 1) - \frac{1}{2}(2x). */
    Poly target = thesis ? thesis->value : poly_const(num_int(1));
    long long top = poly_degree(target);
    for (int i = 0; i < hypotheses && !thesis; i++)
        if (poly_degree(hypothesis[i]) > top) top = poly_degree(hypothesis[i]);
    int factor = -1, found = combination(target, hypothesis, hypotheses, multiplier, top, NULL);
    for (int v = 0; v < universal_count && !found && thesis && !failure && search_left > 0; v++) {
        if (numbers_contain(universal[v].numbers, frac_int(0))) continue;
        target = poly_mul(thesis->value, rat_atom(atom_var(universal[v].name)).num);
        found = combination(target, hypothesis, hypotheses, multiplier, poly_degree(target), NULL);
        if (found) factor = v;
    }
    if (!found) return 0;

    /* Controllo del passo: rifatto il conto con prodotti e somme, la
     * combinazione deve dare il polinomio cercato. */
    Poly rebuilt = poly_const(num_int(0));
    for (int i = 0; i < hypotheses; i++) rebuilt = poly_add(rebuilt, poly_mul(multiplier[i], hypothesis[i]), 0);
    if (failure) return 0;
    if (!poly_equal(rebuilt, target)) { unjustified_steps++; return 0; }

    /* Il testo: le ipotesi, l'identità, la conclusione. */
    proof_add(" Suppose that");
    for (int i = 0; i < hypotheses; i++) {
        proof_add("%s $", i ? " and that" : "");
        put_source(assumed[i]->source);
        proof_add("$ %s%s that is $", assumed[i]->source->kind == F_EQUAL ? "holds" : "fails", assumed[i]->cleared ? ", after clearing denominators," : ",");
        put_poly(hypothesis[i]);
        proof_add(" = 0$");
    }
    proof_add(". As polynomials, $");
    if (factor >= 0) proof_add("%c\\left(", universal[factor].name);
    put_poly(target);
    proof_add(factor >= 0 ? "\\right) = " : " = ");
    for (int i = 0, written = 0; i < hypotheses; i++) {
        if (multiplier[i].count == 0) continue;
        proof_add("%s\\left(", written++ ? " + " : "");
        put_poly(multiplier[i]);
        proof_add("\\right)\\left(");
        put_poly(hypothesis[i]);
        proof_add("\\right)");
    }
    proof_add("$: multiplying out gives the same terms. So $");
    if (!thesis) {
        proof_add("1 = 0$, which is impossible: the conditions cannot fail together.");
        return 1;
    }

    /* Il fattore: il prodotto è zero, e il fattore non lo è mai (18b). */
    if (factor >= 0) {
        proof_add("%c\\left(", universal[factor].name);
        put_poly(thesis->value);
        proof_add("\\right) = 0$.");
        if (!zero_only_where(rat_atom(atom_var(universal[factor].name)).num, NULL)) return 0;
        proof_add(" Hence $");
    }
    put_poly(thesis->value);
    proof_add(" = 0$, %s $", thesis->source->kind == F_EQUAL ? "that is" : "so");
    put_source(thesis->source);
    proof_add(thesis->source->kind == F_EQUAL ? "$." : "$ fails.");
    return 1;
}

/* Prototipo in avanti inevitabile: quando il fattore che resta a 18h si
 * annulla in un punto, la regola chiede di distinguere quel punto (18v-2, nel
 * capitolo 18.4, che usa le regole di questo). */
static void split_at_zero(Rat gap);

/* 18g, 18h. Dimostra che, per ogni valore delle variabili generiche, vale
 * almeno uno dei `count` confronti di literal[]. Scrive il ragionamento, come
 * seguito di un \item già aperto, e ritorna 1 se ci riesce.
 *
 * Ogni confronto diventa un polinomio, il numeratore della differenza dei due
 * membri: "uguali" vuol dire polinomio zero, "diversi" polinomio non zero.
 *
 *   18g. Se un confronto vale sempre la disgiunzione è dimostrata: un
 *        "uguali" con polinomio nullo, o un "diversi" con una costante non
 *        nulla. È sempre il caso quando non ci sono variabili generiche,
 *        perché allora i polinomi sono numeri. Un confronto tra espressioni
 *        non razionali si decide solo così, tra numeri, e con le condizioni
 *        di esistenza controllate (closed_gap()).
 *   18h. Tolti i confronti che non valgono mai, la forma trattata è
 *        "p diverso da 0, oppure e = 0", cioè "p = 0 implica e = 0", anche
 *        senza la seconda parte. Si divide p per e finché si può (p = e^k q:
 *        dove e non è zero, p è zero solo se lo è q), poi si chiede a
 *        zero_only_where() che q si annulli al più dove si annulla e.
 *
 * Una disgiunzione di soli "uguali" non identici non può valere per ogni
 * valore: il prodotto dei polinomi non è nullo, e gli insiemi sono infiniti. */
static int prove_clause(Literal *literal, int count) {
    if (!clause_polynomials(literal, count)) return 0;

    /* 18g. Un confronto che vale sempre. Se i due membri sono numeri si
     * riportano, così il lettore può rifare il conto. */
    for (int i = 0; i < count; i++) {
        const Literal *l = &literal[i];
        Num left, right;
        int always = l->equation ? l->value.count == 0 : (poly_is_constant(l->value) && l->value.count != 0);
        if (!always) continue;
        put_outcome(l->source, l->equation);
        if (l->computed) {
            proof_add(l->equation ? ": computed exactly, the two sides are equal." : ": computed exactly, the two sides are different.");
        } else if (rat_number(eval(l->source->left), &left) && rat_number(eval(l->source->right), &right)) {
            proof_add(l->equation ? ": both sides are equal to $" : ": the two sides are $");
            put_frac(left.re);
            if (!l->equation) { proof_add("$ and $"); put_frac(right.re); }
            proof_add("$.");
        } else if (l->equation) {
            proof_add(": written out, the two sides are the same expression.");
        } else {
            proof_add(": the difference of the two sides has the numerator $");
            put_poly(l->value);
            proof_add("$, a constant that is not zero.");
        }
        return 1;
    }

    /* 18h. Restano i confronti che dipendono dalle variabili: le costanti
     * rimaste sono confronti che non valgono mai. */
    const Literal *distinct = NULL, *equal = NULL;
    for (int i = 0; i < count; i++) {
        if (poly_is_constant(literal[i].value)) continue;
        if (!literal[i].equation && !distinct) distinct = &literal[i];
        else if (literal[i].equation && !equal) equal = &literal[i];
        else return 0;
    }
    if (!distinct) return 0;
    Poly h = distinct->value;
    const char *clearing = distinct->cleared ? ", after clearing denominators," : "";

    /* Un solo "diversi": il polinomio non deve annullarsi mai. */
    if (!equal) {
        int written_equal = distinct->source->kind == F_EQUAL;
        proof_add(written_equal ? " The equality $" : " The condition $");
        put_source(distinct->source);
        proof_add(written_equal ? "$%s would mean $" : "$%s means $", clearing);
        put_poly(h);
        proof_add(written_equal ? " = 0$." : " \\neq 0$.");
        if (!zero_only_where(h, NULL)) return 0;
        if (written_equal) proof_add(" So the equality never holds.");
        return 1;
    }

    /* "Diversi oppure uguali": p = 0 deve implicare e = 0. */
    Poly e = equal->value;
    proof_add(" Suppose that $");
    put_source(distinct->source);
    proof_add("$ %s%s that is $", distinct->source->kind == F_EQUAL ? "holds" : "fails", distinct->cleared ? clearing : ",");
    put_poly(h);
    proof_add(" = 0$.");
    int times = divide_out(&h, e);

    /* Controllo del passo: rimoltiplicando i fattori si deve ritrovare il
     * polinomio di partenza. La divisione è fatta con la regola di Ruffini,
     * il controllo con il prodotto. */
    Poly rebuilt = h;
    for (int i = 0; i < times; i++) rebuilt = poly_mul(rebuilt, e);
    if (failure) return 0;
    if (!poly_equal(rebuilt, distinct->value)) { unjustified_steps++; return 0; }
    if (times && !poly_is_one(h)) {
        proof_add(" Now $");
        put_poly(distinct->value);
        proof_add(" = ");
        put_factor(h);

        /* Il fattore e: tra parentesi se ha più termini o un esponente. */
        int brackets = e.count > 1 || times > 1;
        proof_add(brackets ? "\\left(" : " \\cdot ");
        put_poly(e);
        if (brackets) proof_add("\\right)");
        if (times > 1) proof_add("^{%d}", times);
        proof_add("$.");
    }
    if (!poly_is_one(h) && !zero_only_where(h, &e)) {
        split_at_zero((Rat){h, poly_const(num_int(1))});
        return 0;
    }
    proof_add(" Hence $");
    put_poly(e);
    proof_add(" = 0$, ");
    proof_add(equal->source->kind == F_EQUAL ? "that is $" : "so $");
    put_source(equal->source);
    proof_add(equal->source->kind == F_EQUAL ? "$." : "$ fails.");
    return 1;
}

/* 18z. SOSTITUIRE UN'IPOTESI
 *
 * A che cosa serve. "Se y = a x e x = b y allora x = y", con x, y naturali
 * e a, b interi: la tesi non è una combinazione delle ipotesi (18s), perché
 * è vera solo grazie ai segni. Un matematico scrive: "metto a x al posto di
 * y; allora x = b a x, cioè x (1 - a b) = 0". Da lì la regola dei segni con
 * guardia (18c) conclude: con a = 1 + a', b = 1 + b' (18y-4 sa che a e b
 * sono naturali) e x = 1 + x', x - a b x ha tutti i coefficienti negativi e
 * i termini a' e b', quindi si annulla solo se a' = b' = 0, e allora x - a x
 * = 0. La regola dei segni fa da sola la parte "un prodotto di naturali che
 * vale 1 ha tutti i fattori uguali a 1".
 *
 * La regola. Tra i confronti di una disgiunzione da dimostrare, un "diversi"
 * è un'ipotesi H = 0. Se H è di primo grado in una variabile generica v, con
 * un coefficiente c che è un numero, H = c v + R con R senza v, allora dove
 * vale l'ipotesi v = -R/c. Si lega v a quel valore e si dimostrano le altre
 * parti, ricalcolate con v al suo posto, per ogni valore delle variabili che
 * restano: dove l'ipotesi vale, le parti valgono quanto le loro copie
 * ricalcolate, e dove non vale la disgiunzione è già vera. È lecito anche
 * se v ha un insieme: lo si dimentica, e si dimostra di più.
 *
 * Perché il calcolo e non i polinomi. Le altre parti si ricalcolano dalle
 * loro espressioni, con v legata, e non sostituendo nei polinomi: così anche
 * una potenza di v cambia, y^{m} con y = x^{n} diventa x^{n m} (18x), ed è
 * ciò che serve alla transitività di "y è una potenza di x".
 *
 * Il controllo del passo. Anche l'ipotesi si ricalcola con v legata, e deve
 * diventare il polinomio nullo: se v comparisse anche dentro un altro atomo
 * di H, come in y - 2^{y}, il valore -R/c non risolverebbe l'ipotesi, e la
 * regola non si applica. Le sostituzioni una dopo l'altra sono al più
 * MAX_SUBSTITUTIONS. */

/* Quante sostituzioni 18z fa una dopo l'altra, al più. */
#define MAX_SUBSTITUTIONS 2

/* 18z. Dimostra che, per ogni valore delle variabili generiche, vale almeno
 * uno dei `count` confronti di literal[], sostituendo una variabile con il
 * valore che un'ipotesi le dà (vedi la testa del paragrafo) e passando il
 * resto a 18h, a 18s o a un'altra sostituzione, al più `depth`. Scrive il
 * ragionamento, come seguito di un \item già aperto, e ritorna 1 se ci
 * riesce; se ritorna 0 il testo scritto va cancellato da chi chiama. */
static int prove_by_substitution(Literal *literal, int count, int depth) {
    Mark mark = mark_here();
    if (depth <= 0 || count < 2 || failure || !clause_polynomials(literal, count)) return 0;
    rollback(mark);
    for (int i = 0; i < count; i++) {
        if (literal[i].equation || literal[i].computed) continue;
        for (int v = 0; v < universal_count && !failure && search_left > 0; v++) {
            int name = universal[v].name;
            Poly part[2], shown_num, shown_den;
            if (env_lookup(name) || poly_split(literal[i].value, atom_var(name), part, 1) != 1 || !poly_is_constant(part[1])) continue;
            Rat value = rat_make(poly_negate(part[0]), part[1]);
            if (!rat_polynomials(value, &shown_num, &shown_den)) continue;

            /* Il controllo del passo: l'ipotesi, con v al suo valore. */
            Literal again = literal[i];
            env_push(name, value);
            int solved = clause_polynomials(&again, 1) && again.value.count == 0 && !failure;
            rollback(mark);
            if (!solved) { env_pop(); continue; }

            /* Le altre parti, ricalcolate. */
            Literal rest[MAX_LITERALS];
            int left = 0;
            for (int j = 0; j < count; j++)
                if (j != i) rest[left++] = literal[j];
            proof_add(" Suppose that $");
            put_source(literal[i].source);
            proof_add("$ %s: then $%c = ", literal[i].source->kind == F_EQUAL ? "holds" : "fails", name);
            put_ratio(shown_num, shown_den);
            proof_add("$, and we write that in place of $%c$.\n\\item", name);
            Mark inner = mark_here();
            int proved = prove_clause(rest, left);
            if (!proved && !failure) { rollback(inner); proved = prove_combination(rest, left); }

            /* Una disgiunzione vale se ne vale una parte: si prova anche con
             * una sola ipotesi accanto agli "uguali", quando le altre
             * parlano d'altro (le componenti b, d accanto ad a, c). */
            for (int j = 0; j < left && left > 2 && !proved && !failure; j++) {
                Literal some[MAX_LITERALS];
                int kept = 0;
                if (rest[j].equation) continue;
                for (int k = 0; k < left; k++)
                    if (k == j || rest[k].equation) some[kept++] = rest[k];
                rollback(inner);
                proved = prove_clause(some, kept);
            }
            if (!proved && !failure) { rollback(inner); proved = prove_by_substitution(rest, left, depth - 1); }
            env_pop();
            if (proved) return 1;
            rollback(mark);
        }
    }
    return 0;
}

/* =============================================================================
 * 18.4 "PER OGNI" ED "ESISTE": INDUZIONE, CASI, EQUAZIONI
 * ============================================================================
 *
 * Le regole che dimostrano un quantificatore con un metodo proprio, quando
 * introdurre una variabile generica (18k) non basta: "per ogni n" di
 * un'uguaglianza per induzione (18n), "per ogni x" intero per casi sul resto
 * in una divisione (18o), per casi chiesti da ciò che si sta dimostrando
 * (18v: i casi di un'applicazione definita per casi, o i lati di un numero
 * per il valore di un "esiste"), "esiste x" risolvendo un'equazione in x
 * (18i), anche caso per caso (18v-3). L'induzione è il metodo del capitolo
 * 13; le altre dimostrano ciò che resta chiamando establish() (18.6), con la
 * variabile legata al caso in esame o al valore trovato.
 */

/* Prototipo in avanti inevitabile: establish() (18.6) e le regole 18i, 18o e
 * 18u (18.4, 18.5) si chiamano a vicenda. */
static int establish(Formula *f, int negated);

/* Ritorna 1 se la lettera name compare nel sotto-albero node, come variabile,
 * come indice di una somma o come nome di una successione. */
int node_uses_letter(const Node *node, int name) {
    if (!node) return 0;
    if (node->name == name && (node->kind == N_VAR || node->kind == N_BIGOP || node->kind == N_SEQ || node->kind == N_APPLY)) return 1;
    return node_uses_letter(node->a, name) || node_uses_letter(node->b, name) || node_uses_letter(node->c, name);
}

/* Ritorna 1 se la lettera name compare nella condizione f: quantificata, o
 * dentro un'espressione. */
int formula_uses_letter(const Formula *f, int name) {
    if (!f) return 0;
    if ((f->kind == F_FORALL || f->kind == F_EXISTS) && f->variable == name) return 1;
    return node_uses_letter(f->left, name) || node_uses_letter(f->right, name) ||
           formula_uses_letter(f->a, name) || formula_uses_letter(f->b, name);
}

/* Ritorna 1 se l'espressione node dipende dalla lettera name: la scrive,
 * oppure la scrive la regola, o uno dei casi, di un'applicazione che node
 * calcola, come il parametro b di f(n) = a n + b (17s). */
static int node_mentions(const Node *node, int name) {
    if (!node) return 0;
    if (node->kind == N_VAR && node->name == name) return 1;
    const Map *map = node->kind == N_APPLY ? map_find(node->name) : NULL;
    if (map && node_uses_letter(map->body, name)) return 1;
    for (int k = 0; map && k < map->cases; k++)
        if (node_uses_letter(map->piece[k].value, name) || formula_uses_letter(map->piece[k].when, name)) return 1;
    return node_mentions(node->a, name) || node_mentions(node->b, name) || node_mentions(node->c, name);
}

/* Come formula_uses_letter(), contando anche le lettere delle regole delle
 * applicazioni calcolate (node_mentions()). */
static int formula_mentions(const Formula *f, int name) {
    if (!f) return 0;
    if ((f->kind == F_FORALL || f->kind == F_EXISTS) && f->variable == name) return 1;
    return node_mentions(f->left, name) || node_mentions(f->right, name) || formula_mentions(f->a, name) || formula_mentions(f->b, name);
}

/* 18n. Dimostra "per ogni n in A vale L = R" per induzione su n, quando A è
 * un insieme di interi da un certo punto in su e non ci sono altre variabili
 * in gioco. all è il nodo del quantificatore ed equation il confronto.
 * Scrive la dimostrazione, con i suoi passaggi, e ritorna 1 se ci riesce.
 *
 * È il metodo del capitolo 13 usato come una regola: lì arriva un enunciato
 * intero, qui un pezzo di un enunciato più grande. Le due espressioni sono
 * già alberi dello stesso tipo, quindi non c'è nulla da rileggere.
 *
 * L'induzione vuole la tabella degli atomi per sé: un atomo ricorda se
 * dipende dalla variabile di induzione, e quelli nati finora sono stati
 * creati senza saperlo. La tabella viene quindi messa da parte e ripristinata
 * alla fine, com'era: i valori scelti per gli "esiste" già dimostrati, che la
 * verifica rileggerà, contengono i numeri d'ordine dei vecchi atomi. */
static int by_induction(const Formula *all, const Formula *equation) {
    static Atom kept_atoms[MAX_ATOMS];
    static Poly kept_polys[MAX_ATOMS];
    static Rat kept_atans[MAX_ATOMS];
    Statement statement = {equation->left, equation->right, REL_EQ};
    int atoms_before = atom_count, polys_before = base_poly_count, atans_before = atan_count, variable_before = induction_var;
    long long default_before = default_base, floor_before = domain_floor;
    size_t arena_before = arena_used, start = proof_length;
    const char *syntax_before = syntax_error;

    /* Via la tabella di prima; l'arena continua da dov'è. */
    memcpy(kept_atoms, atoms, sizeof(Atom) * (size_t)atoms_before);
    memcpy(kept_polys, base_polys, sizeof(Poly) * (size_t)polys_before);
    memcpy(kept_atans, atan_args, sizeof(Rat) * (size_t)atans_before);
    atom_count = base_poly_count = atan_count = 0;

    proof_add("\\item We prove $");
    put_source(equation);
    proof_add("$ for every $%c \\in ", all->variable);
    put_numbers(&all->numbers);
    proof_add("$.\n");
    int proved = induct(&statement, all->variable, 1, all->numbers.low + all->numbers.strict, 1).outcome == PROVED;
    if (!proved) proof_cut(start);

    /* Tutto com'era. Un errore dell'induzione vuol dire solo che questa
     * regola non si applica. */
    memcpy(atoms, kept_atoms, sizeof(Atom) * (size_t)atoms_before);
    memcpy(base_polys, kept_polys, sizeof(Poly) * (size_t)polys_before);
    memcpy(atan_args, kept_atans, sizeof(Rat) * (size_t)atans_before);
    atom_count = atoms_before;
    base_poly_count = polys_before;
    atan_count = atans_before;
    induction_var = variable_before;
    default_base = default_before;
    domain_floor = floor_before;
    arena_used = arena_before;
    syntax_error = syntax_before;
    failure = NULL;
    env_count = 0;
    return proved;
}

/* 18o. Dimostra "per ogni x in A vale P", con A un insieme di interi senza
 * punti tolti, per casi sul resto di x in una divisione. f è il nodo del
 * quantificatore e negated il segno con cui va letta P. Scrive la
 * dimostrazione e ritorna 1 se ci riesce; se ritorna 0 il testo scritto va
 * cancellato da chi chiama.
 *
 * Divisione con resto: fissato m > 0, ogni intero x si scrive in un solo
 * modo come x = m t + r, con t intero e r tra 0 e m - 1. Dimostrare P per
 * ogni x equivale quindi a dimostrarla per x = m t + r, per ogni t, in
 * ognuno degli m casi. In ciascun caso x è legata all'espressione m t + r, e
 * t è una variabile generica nuova: le altre regole lavorano come sempre. È
 * così che "ogni intero è pari o dispari" si riduce a due equazioni di primo
 * grado: con x = 2 t si prende y = t, con x = 2 t + 1 ancora y = t.
 *
 * Il modulo non si conosce in anticipo: si provano m = 2, 3, ... fino a
 * MAX_CASES. Se x deve stare in A = {x >= a}, allora m t + r >= a, cioè t
 * parte dal più piccolo intero non minore di (a - r)/m.
 *
 * Un caso dentro l'altro non si fa: il valore scelto per un "esiste" è
 * ricordato caso per caso (vedi Formula), con un solo numero di caso. */
static int by_remainders(Formula *f, int negated) {
    static char written[48];
    const NumberSet *set = &f->numbers;
    int quotient = 0;
    if (!set->integers || set->holes || split_modulus || failure) return 0;

    /* Una lettera per il quoziente che l'enunciato non usa. */
    for (const char *letter = "tsuvwpqhgedcba"; *letter && !quotient; letter++) {
        int taken = map_find(*letter) != NULL || formula_uses_letter(f, *letter) || env_lookup(*letter) != NULL;
        for (int i = 0; i < universal_count; i++) taken = taken || universal[i].name == *letter;
        if (!taken) quotient = *letter;
    }
    if (!quotient) return 0;

    /* I tentativi di questa regola sono contati a parte: provare cinque
     * moduli non deve consumare la ricerca di chi sta intorno. */
    int outside = search_set_aside();
    for (int m = 2; m <= MAX_CASES && search_left > 0 && !failure; m++) {
        Mark mark = mark_here();
        int holds = 1;
        proof_add("\\item Every integer is $%d%c + r$ for exactly one integer $%c$ and one $r$ among $0", m, quotient, quotient);
        for (int r = 1; r < m; r++) proof_add(", %d", r);
        proof_add("$: division by $%d$ with remainder. So there are $%d$ cases.\n", m, m);
        split_modulus = m;
        for (int r = 0; r < m && holds; r++) {
            /* L'insieme in cui varia il quoziente, e come scriverlo. */
            NumberSet part = {0};
            long long first = set->low + set->strict - r;
            part.integers = 1;
            part.bounded = set->bounded;
            part.low = first >= 0 ? (first + m - 1) / m : -((-first) / m);
            if (!part.bounded) snprintf(written, sizeof written, "\\mathbb{Z}");
            else if (part.low == 0 || part.low == 1) snprintf(written, sizeof written, part.low ? "\\mathbb{N}" : "\\mathbb{N}_{0}");
            else snprintf(written, sizeof written, "\\{%lld, %lld, \\ldots\\}", part.low, part.low + 1);
            part.start = written;
            part.end = written + strlen(written);

            proof_add("\\item \\emph{Case $%c = %d%c", f->variable, m, quotient);
            if (r) proof_add(" + %d", r);
            proof_add("$}, with $%c \\in %s$.\n\\begin{itemize}\n", quotient, written);

            /* x legata a m t + r, e t generica. */
            split_case = r;
            if (!universal_push((Bound){quotient, &part})) return 0;
            env_push(f->variable, rat_add(rat_mul(rat_int(m), rat_atom(atom_var(quotient))), rat_int(r), 0));
            holds = establish(f->a, negated);
            env_pop();
            universal_count--;
            proof_add("\\end{itemize}\n");
        }
        split_modulus = split_case = 0;
        if (holds) {
            f->modulus = m;
            f->quotient = quotient;
            search_left += outside;
            return 1;
        }
        rollback(mark);
    }
    search_left += outside;
    return 0;
}

/* 18v. LE APPLICAZIONI DEFINITE PER CASI, E LE DISTINZIONI DI CASI
 *
 * A che cosa serve. "f(n) = 2n se n è pari, 5n se n è dispari: f è
 * iniettiva." Un matematico distingue i casi, n = 2s e n = 2s + 1, e in
 * ognuno f(n) è un polinomio. Le regole di questo paragrafo fanno lo stesso,
 * in tre passi.
 *
 *   18v-1. Il caso di f(t). Prima di calcolare una condizione in cui compare
 *          f(t), con f definita per casi (17s) e t un'espressione nelle
 *          variabili generiche, si dimostra la condizione di uno dei casi
 *          per tutti i loro valori: allora f(t) è il valore di quel caso.
 *          Lo dice l'ipotesi stessa, "se vale la condizione allora f(t) è
 *          quel valore", e non serve altro. Le condizioni si dimostrano con
 *          le regole di sempre: 18d per "m divide v" (il quoziente è un
 *          intero), 18c per i confronti d'ordine, 18b per "diverso", 18e per
 *          le appartenenze; e "u non divide v" in due modi: v = m q + c con
 *          q intero e c non multiplo del numero m, oppure v = w + u q con q
 *          intero e "u non divide w" noto nel caso in esame (18v-4).
 *   18v-2. Distinguere i casi. Quando nessuna condizione si sa dimostrare,
 *          la regola annota che cosa servirebbe sapere di una variabile
 *          generica y (split_wanted): un resto (y = 2s oppure 2s + 1), un
 *          lato di un numero (y \ge 2 oppure y \le 1), un punto (y = -2
 *          oppure no), l'essere un intero o un multiplo di k. Il "per ogni"
 *          che ha introdotto y (18k) raccoglie la richiesta e ripete la
 *          dimostrazione in ognuno dei casi. È lecito perché i casi coprono
 *          l'insieme di y per come sono fatti: un resto tra 0 e M - 1, un
 *          lato o l'altro di un numero, un punto o il resto, una proprietà
 *          o la sua negazione. La stessa richiesta la fa chi cerca il
 *          valore di un "esiste" (18i) e trova un valore che sta
 *          nell'insieme solo da un lato di un numero (x = 2y + 2 è in
 *          \mathbb{N} solo per y \ge 0), o un coefficiente che si annulla in
 *          un punto.
 *   18v-3. "Esiste x con f(x) = y". Per trovare x si prova ogni caso: la sua
 *          equazione, risolta da 18i, dà un valore, oppure il caso stesso è
 *          un punto (x = -2). Il valore è solo una proposta: con x legata a
 *          lui, 18v-1 dimostra da capo quale caso vale, e l'uguaglianza si
 *          ricontrolla.
 *
 * In un caso nato da 18v-2 la variabile cambia: diventa 2s + 1, o -1 - s con
 * s \ge 0, oppure resta y ma in un insieme più piccolo (y \ge 2, y \neq -2,
 * y intero), oppure le si affianca un fatto "u non divide y" (excluded[]).
 * Così le regole dei capitoli precedenti vedono di nuovo polinomi in
 * variabili generiche, e i fatti del caso stanno nei loro insiemi.
 *
 * Quante distinzioni. Ogni caso può chiederne un'altra, fino a
 * MAX_REGION_DEPTH una dentro l'altra: un'iniettività ne vuole due (una su
 * a, una su b), qualcuna in più quando i casi della definizione si
 * intrecciano con quelli del valore di un "esiste". Poi la ricerca si
 * ferma. Una richiesta che parla di una variabile più esterna passa al "per
 * ogni" che l'ha introdotta; tra più richieste vale la prima.
 *
 * La verifica. Ogni distinzione divide l'insieme in parti che lo coprono, e
 * in ogni parte valgono le regole di sempre. Il capitolo 19 ricontrolla
 * comunque tutto sui numeri: f si calcola con i numeri (11v), i casi della
 * definizione si ricontrollano punto per punto (map_holds_on_sample()), e i
 * valori degli "esiste" scelti dentro una distinzione la verifica li cerca
 * da sé (witness_keep()).
 */

/* Scrive la condizione c di un caso, negata se negated, con i valori del
 * momento: ogni confronto tra $...$, i connettivi a parole. Le
 * disuguaglianze si scrivono nel verso in cui le ha scritte l'enunciato. */
static void put_condition(const Formula *c, int negated) {
    if (c->kind == F_NOT) { put_condition(c->a, !negated); return; }
    if (c->kind == F_AND || c->kind == F_OR) {
        put_condition(c->a, negated);
        proof_add((c->kind == F_AND) != negated ? " and " : " or ");
        put_condition(c->b, negated);
        return;
    }
    Rat u = eval(c->left);
    proof_add("$");
    switch (c->kind) {
    case F_EQUAL: case F_DISTINCT:
        put_fraction(u);
        proof_add((c->kind == F_EQUAL) != negated ? " = " : " \\neq ");
        put_fraction(eval(c->right));
        break;
    case F_LESS: case F_LESS_EQ: {
        /* u < v e u \le v; negate, v \le u e v < u. */
        int strict = (c->kind == F_LESS) != negated;
        Rat v = eval(c->right), low = negated ? v : u, high = negated ? u : v;
        if (c->swapped) { put_fraction(high); proof_add(strict ? " > " : " \\ge "); put_fraction(low); }
        else { put_fraction(low); proof_add(strict ? " < " : " \\le "); put_fraction(high); }
        break;
    }
    case F_DIVIDES:
        put_fraction(u);
        proof_add(c->swapped == negated ? " \\mid " : " \\nmid ");
        put_fraction(eval(c->right));
        break;
    case F_IN:
        put_fraction(u);
        proof_add(c->swapped == negated ? " \\in " : " \\notin ");
        put_numbers(&c->numbers);
        break;
    default:
        break;
    }
    proof_add("$");
}

/* Scrive " + c" oppure " - |c|". */
static void put_added(Frac c) {
    proof_add(c.num < 0 ? " - " : " + ");
    put_frac(c.num < 0 ? frac_neg(c) : c);
}

/* 18v-1. Dimostra che u non divide v per ogni valore delle variabili
 * generiche, in uno dei due modi descritti in testa al paragrafo. Scrive il
 * ragionamento e ritorna 1 se ci riesce; altrimenti il testo va cancellato
 * da chi chiama.
 *
 * Perché basta. Con u = m un numero e v = m q + c, dove q vale sempre un
 * intero: v/m = q + c/m, intero esattamente quando lo è c/m. Con v = w + u q
 * e q intero: v/u = w/u + q, intero esattamente quando lo è w/u. */
static int not_multiple(Rat u, Rat v) {
    Poly num, den, q, d, one = poly_const(num_int(1));
    Num m;
    if (failure) return 0;

    /* v = m q + c, con c il termine noto di v. */
    if (rat_number(u, &m) && m.im.num == 0 && m.re.num != 0 && rat_polynomials(v, &num, &den) && poly_is_one(den)) {
        Num c = num_int(0);
        for (int i = 0; i < num.count; i++)
            if (num.term[i].mono.count == 0) c = num.term[i].coef;
        Rat rest = rat_div(rat_add(v, (Rat){poly_const(c), one}, 1), u);
        if (!failure && c.im.num == 0 && !number_divides(m, c) && rat_polynomials(rest, &q, &d) && poly_is_one(d)) {
            size_t start = proof_length;
            proof_add(" Indeed $");
            put_poly(num);
            proof_add(" = ");
            put_frac(m.re);
            proof_add(" q");
            put_added(c.re);
            proof_add("$ with $q = ");
            put_poly(q);
            proof_add("$.");
            if (always_integer(q)) {
                proof_add(" The number $");
                put_frac(m.re);
                proof_add("$ does not divide $");
                put_frac(c.re);
                proof_add("$.");
                return 1;
            }
            proof_cut(start);
        }
    }

    /* v = w + u q, o v = -w + u q, con "u non divide w" noto nel caso in
     * esame: u divide v esattamente quando divide w, perché divide w
     * quando divide -w. Se v è w stessa, è il fatto del caso. */
    for (int e = 0; e < 2 * excluded_count && !failure; e++) {
        const Exclusion *x = &excluded[e / 2];
        int opposite = e % 2;
        Rat same = rat_add(x->divisor, u, 1);
        if (failure || same.num.count != 0) continue;
        Rat rest = rat_div(rat_add(v, (Rat){x->value, one}, !opposite), u);
        if (failure || !rat_polynomials(rest, &q, &d) || !poly_is_one(d)) continue;
        if (q.count == 0 && !opposite) { proof_add(" It is the fact of this case."); return 1; }
        size_t start = proof_length;
        proof_add(" Indeed $");
        put_fraction(v);
        proof_add(" = %s", opposite ? "-\\left(" : "");
        put_poly(x->value);
        proof_add("%s + ", opposite ? "\\right)" : "");
        put_fraction(u);
        proof_add(" q$ with $q = ");
        put_poly(q);
        proof_add("$.");
        if (always_integer(q)) {
            proof_add(" In this case $");
            if (rat_number(u, &m) && num_equal(m, num_int(1))) {
                put_poly(x->value);
                proof_add(" \\notin \\mathbb{Z}$.");
            } else {
                put_fraction(u);
                proof_add(" \\nmid ");
                put_poly(x->value);
                proof_add("$.");
            }
            return 1;
        }
        proof_cut(start);
    }
    return 0;
}

/* 18v-1. Dimostra la condizione c di un caso, negata se negated, per ogni
 * valore delle variabili generiche; la variabile della regola è già legata
 * al valore dell'argomento. Scrive, per ogni confronto, che vale e perché, e
 * ritorna 1 se ci riesce; altrimenti il testo va cancellato da chi chiama. */
static int case_proved(const Formula *c, int negated) {
    Poly num, den;
    if (failure) return 0;
    if (c->kind == F_NOT) return case_proved(c->a, !negated);
    if (c->kind == F_AND || c->kind == F_OR) {
        if ((c->kind == F_AND) != negated) return case_proved(c->a, negated) && case_proved(c->b, negated);
        size_t start = proof_length;
        if (case_proved(c->a, negated)) return 1;
        proof_cut(start);
        return case_proved(c->b, negated);
    }

    /* Tra numeri si calcola. */
    proof_add(" ");
    put_condition(c, negated);
    proof_add(" holds.");
    int computed = condition_computed(c);
    if (failure) return 0;
    if (computed >= 0) {
        if ((computed == 1) == negated) return 0;
        proof_add(" Computed with the numbers.");
        return 1;
    }

    /* Altrimenti, una regola per ogni tipo di confronto. */
    Rat u = eval(c->left), v = c->kind == F_IN ? rat_int(0) : eval(c->right);
    if (failure) return 0;
    switch (c->kind) {
    case F_EQUAL: case F_DISTINCT:
        /* Uguali: la differenza è il polinomio nullo. Diversi: il suo
         * numeratore non si annulla, e il denominatore nemmeno, perché la
         * differenza esista. */
        if (!rat_polynomials(rat_add(u, v, 1), &num, &den)) return 0;
        if ((c->kind == F_EQUAL) != negated) {
            if (num.count) return 0;
            proof_add(" The two sides are the same expression.");
            return 1;
        }
        if (!poly_is_constant(den)) {
            proof_add(" The difference of the two sides has the denominator $");
            put_poly(den);
            proof_add("$.");
            if (!zero_only_where(den, NULL)) return 0;
        }
        proof_add(" The difference of the two sides has the numerator $");
        put_poly(num);
        proof_add("$.");
        return zero_only_where(num, NULL);
    case F_LESS: case F_LESS_EQ: {
        /* u < v vuol dire v - u > 0; la negazione u - v \ge 0. */
        int strict = (c->kind == F_LESS) != negated;
        Rat gap = negated ? rat_add(u, v, 1) : rat_add(v, u, 1);
        if (!rat_polynomials(gap, &num, &den) || !poly_is_one(den)) return 0;
        return signs(num, num, NULL, 0, strict ? SIGN_POSITIVE : SIGN_NONNEGATIVE);
    }
    case F_DIVIDES:
        if (c->swapped != negated) return not_multiple(u, v);
        if (u.num.count == 0 || !rat_polynomials(rat_div(v, u), &num, &den) || !poly_is_one(den)) return 0;
        proof_add(" The quotient is $");
        put_poly(num);
        proof_add("$.");
        return always_integer(num);
    case F_IN:
        if (c->swapped == negated) return always_in(u, &c->numbers);
        return c->numbers.integers && !c->numbers.bounded && !c->numbers.holes && not_multiple(rat_int(1), u);
    default:
        return 0;
    }
}

/* 18v-2. Che cosa si distingue: vedi Split. */
typedef enum {
    SPLIT_ORDER,    /* un lato o l'altro del numero at */
    SPLIT_POINT,    /* il numero at, o tutti gli altri */
    SPLIT_RESIDUE,  /* il resto nella divisione per modulus */
    SPLIT_MEMBER,   /* alpha y + beta multiplo del numero divisor, o no: per y razionale */
    SPLIT_DIVISOR   /* y multiplo di divisor, o no: per y intero */
} SplitKind;

/* Una distinzione di casi richiesta per una variabile generica y (18v-2):
 * che cosa servirebbe sapere di y per proseguire. */
typedef struct {
    int atom;           /* y, come atomo */
    SplitKind kind;
    Frac at;            /* ORDER, POINT: il numero */
    int upper_closed;   /* ORDER: 1 se at sta con i valori più grandi (y \ge at
                           oppure y < at), 0 se con i più piccoli (y > at
                           oppure y \le at) */
    long long modulus;  /* RESIDUE: il modulo, da 2 a MAX_CASES */
    Rat divisor;        /* MEMBER: un numero; DIVISOR: un'espressione senza y */
    Frac alpha, beta;   /* MEMBER: la condizione è "divisor divide alpha y + beta" */
} Split;

/* La richiesta in attesa, se split_pending: la raccoglie in_regions(). */
static Split split_wanted;
int split_pending;

/* Annota la richiesta s, se non ce n'è già una: vale la prima. */
static void split_ask(Split s) {
    if (split_pending) return;
    split_wanted = s;
    split_pending = 1;
}

/* Ritorna, per una distinzione ORDER su una variabile intera, il primo
 * intero c del lato di sopra: y \ge at vuol dire y \ge c con c = \lceil at
 * \rceil, y > at vuol dire y \ge \lfloor at \rfloor + 1. */
static long long order_cut(const Split *s) {
    return s->upper_closed ? -frac_floor(frac_neg(s->at)) : frac_floor(s->at) + 1;
}

/* Ritorna il posto in universal[] dell'unica variabile generica di p, o -1
 * se p non ne ha, ne ha più di una o contiene altri atomi. */
static int sole_generic(Poly p) {
    int who = -1;
    for (int i = 0; i < p.count; i++)
        for (int k = 0; k < p.term[i].mono.count; k++) {
            int w = universal_index(p.term[i].mono.factor[k].atom);
            if (w < 0 || (who >= 0 && w != who)) return -1;
            who = w;
        }
    return who;
}

/* Legge il numeratore di gap come alpha y + beta, con y l'unica variabile
 * generica e alpha, beta numeri: mette il posto di y in *who e ritorna 1. */
static int gap_affine(Rat gap, int *who, Frac *alpha, Frac *beta) {
    Poly num, den;
    if (failure || !rat_polynomials(gap, &num, &den) || !poly_is_constant(den) || den.count == 0) return 0;
    *who = sole_generic(num);
    if (*who < 0) return 0;
    return rat_affine_in((Rat){num, poly_const(num_int(1))}, atom_var(universal[*who].name), alpha, beta);
}

/* Chiede di distinguere il punto in cui gap si annulla, se gap è di primo
 * grado in una sola variabile e quel punto sta nel suo insieme. */
static void split_at_zero(Rat gap) {
    Frac alpha, beta;
    int who;
    if (split_pending || !gap_affine(gap, &who, &alpha, &beta)) return;
    Frac at = frac_neg(frac_div(beta, alpha));
    if (failure || !numbers_contain(universal[who].numbers, at)) return;
    split_ask((Split){atom_var(universal[who].name), SPLIT_POINT, at, 0, 0, rat_int(0), frac_int(0), frac_int(0)});
}

/* Chiede di distinguere i due lati del punto in cui gap si annulla, per
 * sapere se gap > 0 (strict) o gap \ge 0: il punto sta dal lato in cui la
 * condizione vale se non è stretta, dall'altro se lo è. Serve che i due lati
 * abbiano elementi dell'insieme: per gli interi, che l'estremo inferiore
 * stia sotto il punto; per i razionali, che non ci sia un estremo. */
static void split_at_sign(Rat gap, int strict) {
    Frac alpha, beta;
    int who;
    if (split_pending || !gap_affine(gap, &who, &alpha, &beta)) return;
    Frac at = frac_neg(frac_div(beta, alpha));
    int upper_closed = (alpha.num > 0) == !strict;
    const NumberSet *set = universal[who].numbers;
    if (failure) return;
    Split s = {atom_var(universal[who].name), SPLIT_ORDER, at, upper_closed, 0, rat_int(0), frac_int(0), frac_int(0)};
    if (set->integers ? set->bounded && order_cut(&s) <= set->low + set->strict : set->bounded) return;
    split_ask(s);
}

/* Chiede di distinguere se u divide v. Con u un intero e v un polinomio in
 * una sola variabile y: per y intera i resti modulo |u| per il minimo comune
 * multiplo dei denominatori di v (con quel periodo v cambia di un multiplo
 * di u); per y razionale, se v è di primo grado, "multiplo o no". Con u
 * un'espressione: se v = y + u q, con q a coefficienti interi in variabili
 * intere e y intera senza estremi, "u divide y o no". */
static void split_at_multiple(Rat u, Rat v) {
    Poly num, den, part[2], q, d, one = poly_const(num_int(1));
    Num m;
    if (split_pending || failure || !rat_polynomials(v, &num, &den) || !poly_is_one(den)) return;
    if (rat_number(u, &m)) {
        int who = sole_generic(num);
        if (who < 0 || m.im.num != 0 || m.re.den != 1 || m.re.num == 0) return;
        const NumberSet *set = universal[who].numbers;
        int y = atom_var(universal[who].name);
        if (set->integers && !set->holes) {
            long long scale = 1;
            for (int i = 0; i < num.count && scale <= MAX_CASES; i++) scale = scale / (long long)gcd128(scale, num.term[i].coef.re.den) * num.term[i].coef.re.den;
            long long modulus = llabs(m.re.num) * scale;
            if (scale > MAX_CASES || modulus < 2 || modulus > MAX_CASES) return;
            split_ask((Split){y, SPLIT_RESIDUE, frac_int(0), 0, modulus, rat_int(0), frac_int(0), frac_int(0)});
        } else if (!set->integers && !set->reals && !set->bounded && !set->holes) {
            Frac alpha, beta;
            if (rat_affine_in((Rat){num, one}, y, &alpha, &beta))
                split_ask((Split){y, SPLIT_MEMBER, frac_int(0), 0, 0, u, alpha, beta});
        }
        return;
    }
    for (int i = 0; i < universal_count && !failure; i++) {
        const NumberSet *set = universal[i].numbers;
        int y = atom_var(universal[i].name);
        if (!set->integers || set->bounded || set->holes || poly_uses(u.num, y) || poly_uses(u.den, y)) continue;
        if (poly_split(num, y, part, 1) != 1 || !poly_is_one(part[1])) continue;
        if (!rat_polynomials(rat_div((Rat){part[0], one}, u), &q, &d) || !poly_is_one(d) || !poly_whole(q)) continue;
        split_ask((Split){y, SPLIT_DIVISOR, frac_int(0), 0, 0, u, frac_int(0), frac_int(0)});
        return;
    }
}

/* Chiede ciò che servirebbe perché value stia in set: non sotto l'estremo,
 * diverso dai punti tolti. */
static void split_for_membership(Rat value, const NumberSet *set) {
    if (set->bounded) split_at_sign(rat_add(value, rat_int(set->low), 1), set->strict);
    for (int i = 0; i < set->holes; i++) split_at_zero(rat_add(value, rat_frac(set->hole[i]), 1));
}

/* Chiede di distinguere ciò che decide la condizione c di un caso, letta con
 * i valori del momento: il primo dei suoi confronti che non si sa già
 * dimostrare né smentire. */
static void split_from_condition(const Formula *c) {
    if (split_pending || failure) return;
    if (c->kind == F_NOT) { split_from_condition(c->a); return; }
    if (c->kind == F_AND || c->kind == F_OR) {
        split_from_condition(c->a);
        split_from_condition(c->b);
        return;
    }

    /* Un confronto che si sa già decidere non va distinto. */
    size_t start = proof_length;
    int decided = case_proved(c, 0);
    proof_cut(start);
    if (!decided && !failure) decided = case_proved(c, 1);
    proof_cut(start);
    if (decided || failure) return;

    Rat u = eval(c->left), v = c->kind == F_IN ? rat_int(0) : eval(c->right);
    if (failure) return;
    switch (c->kind) {
    case F_EQUAL: case F_DISTINCT: split_at_zero(rat_add(u, v, 1)); return;
    case F_LESS:                   split_at_sign(rat_add(v, u, 1), 1); return;
    case F_LESS_EQ:                split_at_sign(rat_add(v, u, 1), 0); return;
    case F_DIVIDES:                split_at_multiple(u, v); return;
    case F_IN:
        if (c->numbers.integers) split_at_multiple(rat_int(1), u);
        split_for_membership(u, &c->numbers);
        return;
    default:
        return;
    }
}

/* Chiede ciò che decide il caso di f(t), con f = map e t = argument. */
static void split_from_cases(const Map *map, Rat argument) {
    env_push(map->parameter, argument);
    for (int i = 0; i < map->cases && !split_pending && !failure; i++) split_from_condition(map->piece[i].when);
    env_pop();
}

/* Che cosa diventa la variabile y in un caso di una distinzione. */
typedef enum {
    REGION_SET,      /* resta y, in un insieme più piccolo */
    REGION_VALUE,    /* y è un'espressione in una variabile generica nuova */
    REGION_POINT,    /* y è un numero */
    REGION_EXCLUDED  /* resta y, con un fatto "u non divide w" in più */
} RegionKind;

/* Uno dei casi di una distinzione (18v-2). */
typedef struct {
    RegionKind kind;
    const NumberSet *set;  /* SET: il nuovo insieme di y; VALUE: quello della variabile nuova */
    int letter;            /* VALUE: la variabile nuova */
    Rat value;             /* VALUE: y come espressione nella variabile nuova; POINT: il numero */
    Exclusion excluded;    /* EXCLUDED: il fatto del caso */
} Region;

/* Ritorna un insieme uguale a set, nell'arena, con il testo che lo scrive.
 * Prima lo riporta all'invariante di NumberSet: un insieme di interi con
 * l'estremo escluso comincia dal successivo, un punto tolto sull'estremo lo
 * sposta (come in parse_numbers()), e restano solo i punti tolti che
 * appartengono all'insieme. Ritorna NULL, con fail(), se l'arena è piena. */
static const NumberSet *numbers_made(NumberSet set) {
    NumberSet *made = arena_alloc(sizeof *made);
    char *text = arena_alloc(192);
    if (!made || !text) return NULL;
    if (set.integers && set.bounded && set.strict) { set.low++; set.strict = 0; }
    for (int i = 0; set.integers && set.bounded && i < set.holes; ) {
        if (frac_cmp(set.hole[i], frac_int(set.low)) != 0) { i++; continue; }
        set.hole[i] = set.hole[--set.holes];
        set.low++;
        i = 0;
    }
    NumberSet plain = set;
    plain.holes = 0;
    int kept = 0;
    for (int i = 0; i < set.holes; i++)
        if (numbers_contain(&plain, set.hole[i])) set.hole[kept++] = set.hole[i];
    set.holes = kept;

    /* Il testo: l'insieme di partenza, poi i punti tolti. */
    const char *field = set.reals ? "\\mathbb{R}" : "\\mathbb{Q}";
    int n;
    if (set.integers && !set.bounded) n = snprintf(text, 192, "\\mathbb{Z}");
    else if (set.integers && set.low == 0) n = snprintf(text, 192, "\\mathbb{N}_{0}");
    else if (set.integers && set.low == 1) n = snprintf(text, 192, "\\mathbb{N}");
    else if (set.integers) n = snprintf(text, 192, "\\{%lld, %lld, \\ldots\\}", set.low, set.low + 1);
    else if (!set.bounded) n = snprintf(text, 192, "%s", field);
    else if (set.low == 0 && set.strict) n = snprintf(text, 192, "%s^{+}", field);
    else n = snprintf(text, 192, "\\{q \\in %s \\mid q %s %lld\\}", field, set.strict ? ">" : "\\ge", set.low);
    for (int i = 0; i < set.holes && n < 150; i++) {
        Frac h = set.hole[i];
        n += snprintf(text + n, 192 - (size_t)n, "%s", i ? ", " : " \\setminus \\{");
        if (h.den == 1) n += snprintf(text + n, 192 - (size_t)n, "%lld", h.num);
        else n += snprintf(text + n, 192 - (size_t)n, "%s\\frac{%lld}{%lld}", h.num < 0 ? "-" : "", llabs(h.num), h.den);
    }
    if (set.holes) snprintf(text + n, 192 - (size_t)n, "\\}");
    *made = set;
    made->start = text;
    made->end = text + strlen(text);
    return made;
}

/* Ritorna una lettera per una variabile nuova: non è usata in body, né tra le
 * variabili generiche, legate o dei parametri, né dalle applicazioni e dalle
 * loro regole. 0 se non ce n'è. */
static int region_letter(const Formula *body) {
    for (const char *letter = "stuvwpqrhgmjz"; *letter; letter++) {
        int taken = map_find(*letter) != NULL || formula_uses_letter(body, *letter) || env_lookup(*letter) != NULL;
        for (int i = 0; i < universal_count; i++) taken = taken || universal[i].name == *letter;
        for (int i = 0; i < map_count; i++) taken = taken || maps[i].parameter == *letter;
        for (int i = 0; i < statement_parameter_count; i++) taken = taken || statement_parameters[i].name == *letter;
        if (!taken) return *letter;
    }
    return 0;
}

/* Mette in out[] i casi della distinzione s per la variabile generica di
 * posto index, e ritorna quanti sono; 0 se la distinzione non si sa fare.
 * body è la condizione da dimostrare in ogni caso, che serve solo a
 * scegliere la lettera di una variabile nuova. Ogni elenco copre l'insieme
 * di y:
 *
 *   - ORDER, y intera, c il primo intero del lato di sopra: y \ge c, e poi
 *     y \le c - 1, cioè gli interi da l'estremo inferiore a c - 1 uno per
 *     uno, oppure y = c - 1 - s con s \in \mathbb{N}_{0} se non c'è un
 *     estremo;
 *   - ORDER, y razionale senza estremo: y = at + s e y = at - s, con s \ge 0
 *     da un lato e s > 0 dall'altro, secondo dove sta at;
 *   - POINT: y = at, e y nel suo insieme senza at;
 *   - RESIDUE: y = M s + r per r da 0 a M - 1, con s dove serve perché
 *     y stia sopra l'estremo inferiore (come in 18o);
 *   - MEMBER: y = P s + o con s intero, dove P = |m / alpha| e o è la
 *     soluzione di alpha y + beta = 0 ridotta tra 0 e P: sono le y per cui
 *     alpha y + beta è un multiplo di m; e le altre, con il loro fatto;
 *   - DIVISOR: y = u s con s intero, e le altre, con il loro fatto. */
static int regions_of(int index, const Split *s, const Formula *body, Region *out) {
    const NumberSet *set = universal[index].numbers;
    int letter = region_letter(body), count = 0;
    Rat fresh = letter ? rat_atom(atom_var(letter)) : rat_int(0);
    NumberSet any = {0}, base = *set;
    any.integers = 1;
    base.holes = 0;
    if (!letter) return 0;
    switch (s->kind) {
    case SPLIT_ORDER:
        if (set->integers) {
            long long c = order_cut(s);
            NumberSet up = *set;
            up.bounded = 1;
            up.low = c;
            up.strict = 0;
            out[count++] = (Region){REGION_SET, numbers_made(up), 0, rat_int(0), {rat_int(0), {0, NULL}}};
            if (set->bounded) {
                for (long long p = set->low + set->strict; p <= c - 1; p++) {
                    if (!numbers_contain(set, frac_int(p))) continue;
                    if (count > MAX_REGION_POINTS) return 0;
                    out[count++] = (Region){REGION_POINT, NULL, 0, rat_int(p), {rat_int(0), {0, NULL}}};
                }
                return count;
            }
            NumberSet down = any;
            down.bounded = 1;
            for (int i = 0; i < set->holes; i++)
                if (frac_cmp(set->hole[i], frac_int(c - 1)) <= 0) down.hole[down.holes++] = frac_add(frac_int(c - 1), frac_neg(set->hole[i]));
            out[count++] = (Region){REGION_VALUE, numbers_made(down), letter, rat_add(rat_int(c - 1), fresh, 1), {rat_int(0), {0, NULL}}};
            return count;
        }
        if (set->bounded) return 0;
        for (int side = 0; side < 2; side++) {
            /* side 0: y = at + s; side 1: y = at - s. at è compreso dal lato
             * upper_closed. */
            NumberSet half = base;
            half.bounded = 1;
            half.low = 0;
            half.strict = side == s->upper_closed;
            for (int i = 0; i < set->holes; i++) {
                Frac moved = frac_add(set->hole[i], frac_neg(s->at));
                if (side) moved = frac_neg(moved);
                if (moved.num >= 0 && half.holes < MAX_HOLES) half.hole[half.holes++] = moved;
            }
            Rat value = rat_add(rat_frac(s->at), fresh, side);
            out[count++] = (Region){REGION_VALUE, numbers_made(half), letter, value, {rat_int(0), {0, NULL}}};
        }
        return count;
    case SPLIT_POINT: {
        NumberSet rest = *set;
        if (rest.holes == MAX_HOLES) return 0;
        rest.hole[rest.holes++] = s->at;
        out[count++] = (Region){REGION_POINT, NULL, 0, rat_frac(s->at), {rat_int(0), {0, NULL}}};
        out[count++] = (Region){REGION_SET, numbers_made(rest), 0, rat_int(0), {rat_int(0), {0, NULL}}};
        return count;
    }
    case SPLIT_RESIDUE:
        for (long long r = 0; r < s->modulus; r++) {
            NumberSet part = any;
            long long first = set->low + set->strict - r, m = s->modulus;
            part.bounded = set->bounded;
            part.low = !set->bounded ? 0 : first >= 0 ? (first + m - 1) / m : -((-first) / m);
            Rat value = rat_add(rat_mul(rat_int(m), fresh), rat_int(r), 0);
            out[count++] = (Region){REGION_VALUE, numbers_made(part), letter, value, {rat_int(0), {0, NULL}}};
        }
        return count;
    case SPLIT_MEMBER: {
        Num m;
        if (!rat_number(s->divisor, &m)) return 0;
        Frac period = frac_div(m.re, s->alpha), offset = frac_neg(frac_div(s->beta, s->alpha));
        if (period.num < 0) period = frac_neg(period);
        offset = frac_add(offset, frac_neg(frac_mul(period, frac_int(frac_floor(frac_div(offset, period))))));
        if (period.num == 1 && period.den == 1 && offset.num == 0) {
            NumberSet whole = base;
            whole.integers = 1;
            out[count++] = (Region){REGION_SET, numbers_made(whole), 0, rat_int(0), {rat_int(0), {0, NULL}}};
        } else {
            Rat value = rat_add(rat_mul(rat_frac(period), fresh), rat_frac(offset), 0);
            out[count++] = (Region){REGION_VALUE, numbers_made(any), letter, value, {rat_int(0), {0, NULL}}};
        }
        /* Il fatto del secondo caso, scritto come "P non divide y - o": dice
         * lo stesso di "m non divide alpha y + beta", e nella forma in cui lo
         * riconosce not_multiple(), che guarda le differenze con y. */
        Rat shifted = rat_add(rat_atom(s->atom), rat_frac(offset), 1);
        out[count++] = (Region){REGION_EXCLUDED, NULL, 0, rat_int(0), {rat_frac(period), shifted.num}};
        return count;
    }
    case SPLIT_DIVISOR:
        out[count++] = (Region){REGION_VALUE, numbers_made(any), letter, rat_mul(s->divisor, fresh), {rat_int(0), {0, NULL}}};
        out[count++] = (Region){REGION_EXCLUDED, NULL, 0, rat_int(0), {s->divisor, rat_atom(s->atom).num}};
        return count;
    }
    return 0;
}

/* Controllo del passo: ogni elemento dell'insieme di y deve stare in uno dei
 * casi, altrimenti la distinzione ne lascerebbe fuori qualcuno. Lo si
 * verifica, come in 18c, sui primi elementi dell'insieme, calcolando: un
 * insieme nuovo lo contiene, un punto è lui, un'espressione a s + b lo dà
 * con s = (y - b)/a nel suo insieme, un fatto "m non divide w" vale con
 * i numeri. La distinzione "u divide y o no", con u un'espressione, è vera
 * per come è fatta, e non ha numeri da calcolare: lì il controllo non c'è.
 * Ritorna 1 se il controllo passa. */
static int regions_cover(int index, const Split *s, const Region *region, int regions) {
    Frac sample[2 * SAMPLE_SIZE], alpha, beta;
    Num w, m;
    if (s->kind == SPLIT_DIVISOR) return 1;
    numbers_sample(universal[index].numbers, sample, 2 * SAMPLE_SIZE);
    for (int i = 0; i < 2 * SAMPLE_SIZE; i++) {
        int covered = 0;
        for (int k = 0; k < regions && !covered && !failure; k++) {
            const Region *r = &region[k];
            if (r->kind == REGION_SET) covered = numbers_contain(r->set, sample[i]);
            else if (r->kind == REGION_POINT) covered = rat_number(r->value, &w) && frac_cmp(w.re, sample[i]) == 0;
            else if (r->kind == REGION_VALUE && rat_affine_in(r->value, atom_var(r->letter), &alpha, &beta))
                covered = numbers_contain(r->set, frac_div(frac_add(sample[i], frac_neg(beta)), alpha));
            else if (r->kind == REGION_EXCLUDED && rat_number(r->excluded.divisor, &m) &&
                     rat_number(poly_substitute(r->excluded.value, s->atom, rat_frac(sample[i])), &w))
                covered = !number_divides(m, w);
        }
        if (failure) return 0;
        if (!covered) return 0;
    }
    return 1;
}

/* Scrive la frase che annuncia la distinzione s sulla variabile name; region
 * sono i suoi casi. */
static void region_intro(int name, const Split *s, const Region *region) {
    Num m;
    switch (s->kind) {
    case SPLIT_ORDER:
        if (region[0].set->integers) {
            long long c = order_cut(s);
            proof_add("\\item Either $%c \\ge %lld$ or $%c \\le %lld$.\n", name, c, name, c - 1);
            return;
        }
        proof_add("\\item Either $%c %s ", name, s->upper_closed ? "\\ge" : ">");
        put_frac(s->at);
        proof_add("$ or $%c %s ", name, s->upper_closed ? "<" : "\\le");
        put_frac(s->at);
        proof_add("$.\n");
        return;
    case SPLIT_POINT:
        proof_add("\\item Either $%c = ", name);
        put_frac(s->at);
        proof_add("$ or $%c \\neq ", name);
        put_frac(s->at);
        proof_add("$.\n");
        return;
    case SPLIT_RESIDUE:
        proof_add("\\item Every integer is $%lld%c + r$ for exactly one integer $%c$ and one $r$ among $0", s->modulus, region[0].letter, region[0].letter);
        for (long long r = 1; r < s->modulus; r++) proof_add(", %lld", r);
        proof_add("$: division by $%lld$ with remainder. So there are $%lld$ cases.\n", s->modulus, s->modulus);
        return;
    case SPLIT_MEMBER: {
        Rat linear = rat_add(rat_mul(rat_frac(s->alpha), rat_atom(s->atom)), rat_frac(s->beta), 0);
        proof_add("\\item Either $");
        put_fraction(linear);
        if (rat_number(s->divisor, &m) && num_equal(m, num_int(1))) {
            proof_add(" \\in \\mathbb{Z}$ or $");
            put_fraction(linear);
            proof_add(" \\notin \\mathbb{Z}$.\n");
        } else {
            proof_add("$ is a multiple of $");
            put_fraction(s->divisor);
            proof_add("$ or it is not.\n");
        }
        return;
    }
    case SPLIT_DIVISOR:
        proof_add("\\item Either $");
        put_fraction(s->divisor);
        proof_add(" \\mid %c$ or $", name);
        put_fraction(s->divisor);
        proof_add(" \\nmid %c$.\n", name);
        return;
    }
}

/* Scrive il titolo del caso r, il numero k della distinzione s sulla
 * variabile name: che cosa vale nel caso e, se y diventa un'espressione in
 * una variabile nuova, quale. */
static void region_heading(int name, const Split *s, const Region *r, int k) {
    Num m;
    proof_add("\\item \\emph{Case $");
    if (r->kind == REGION_POINT) {
        proof_add("%c = ", name);
        put_fraction(r->value);
    } else {
        switch (s->kind) {
        case SPLIT_ORDER:
            if (r->set->integers) proof_add(k == 0 ? "%c \\ge %lld" : "%c \\le %lld", name, order_cut(s) - (k != 0));
            else {
                proof_add("%c %s ", name, k == 0 ? (s->upper_closed ? "\\ge" : ">") : (s->upper_closed ? "<" : "\\le"));
                put_frac(s->at);
            }
            break;
        case SPLIT_POINT:
            proof_add("%c \\neq ", name);
            put_frac(s->at);
            break;
        case SPLIT_RESIDUE:
            proof_add("%c = ", name);
            put_fraction(r->value);
            break;
        case SPLIT_MEMBER: {
            Rat linear = rat_add(rat_mul(rat_frac(s->alpha), rat_atom(s->atom)), rat_frac(s->beta), 0);
            int unit = rat_number(s->divisor, &m) && num_equal(m, num_int(1));
            if (unit) {
                put_fraction(linear);
                proof_add(k == 0 ? " \\in \\mathbb{Z}" : " \\notin \\mathbb{Z}");
            } else {
                put_fraction(s->divisor);
                proof_add(k == 0 ? " \\mid " : " \\nmid ");
                put_fraction(linear);
            }
            break;
        }
        case SPLIT_DIVISOR:
            put_fraction(s->divisor);
            proof_add(k == 0 ? " \\mid %c" : " \\nmid %c", name);
            break;
        }
    }
    proof_add("$}");
    if (r->kind == REGION_VALUE && s->kind != SPLIT_RESIDUE) {
        proof_add(", that is $%c = ", name);
        put_fraction(r->value);
        proof_add("$ with $%c \\in ", r->letter);
        put_numbers(r->set);
        proof_add("$");
    } else if (r->kind == REGION_VALUE) {
        proof_add(", with $%c \\in ", r->letter);
        put_numbers(r->set);
        proof_add("$");
    }
    proof_add(".\n");
}

/* Ciò che va dimostrato in ogni caso di una distinzione: una funzione che lo
 * dimostra, scrivendo, e i suoi dati. Ritorna 1 se ci riesce. */
typedef int (*RegionGoal)(void *data);

/* 18v-2. Dimostra goal, e se non riesce perché manca una distinzione su una
 * delle variabili generiche dal posto from in su, la fa e dimostra goal in
 * ognuno dei casi, che possono chiederne altre fino a MAX_REGION_DEPTH.
 * body serve a scegliere le lettere nuove (regions_of()). Ritorna 1 se ci
 * riesce; se ritorna 0 non lascia testo, e una richiesta su una variabile
 * più esterna resta in attesa per chi l'ha introdotta. */
static int in_regions(RegionGoal prove, void *data, const Formula *body, int from, int depth) {
    Mark mark = mark_here();
    Split older = split_wanted;
    int had = split_pending;
    split_pending = 0;
    int holds = prove(data);
    Split wanted = split_wanted;
    int asked = split_pending;
    split_pending = had;
    split_wanted = older;
    if (failure == CASE_UNDECIDED) failure = NULL;
    if (holds || !asked || failure || search_left <= 0) return holds;

    /* La richiesta è per una variabile più esterna: passa a chi l'ha
     * introdotta, se non ce n'è già una. */
    int index = universal_index(wanted.atom);
    if (index < 0) return 0;
    if (index < from) {
        if (!had) { split_pending = 1; split_wanted = wanted; }
        return 0;
    }
    if (depth >= MAX_REGION_DEPTH) return 0;
    rollback(mark);

    /* I casi, uno per uno. */
    Region region[MAX_CASES + MAX_REGION_POINTS + 2];
    int regions = regions_of(index, &wanted, body, region);
    if (regions < 2 || failure) return 0;
    if (!regions_cover(index, &wanted, region, regions)) {
        if (!failure) unjustified_steps++;
        return 0;
    }
    int name = universal[index].name;
    region_intro(name, &wanted, region);
    region_depth++;
    holds = 1;
    for (int k = 0; k < regions && holds && !failure; k++) {
        const Region *r = &region[k];
        Bound kept = universal[index];
        region_heading(name, &wanted, r, k);
        if (r->kind == REGION_EXCLUDED &&
            !work_reserve((void **)&excluded, &excluded_capacity, (size_t)excluded_count + 1, sizeof *excluded)) { holds = 0; break; }
        if (r->kind == REGION_SET) universal[index].numbers = r->set;
        if (r->kind == REGION_VALUE || r->kind == REGION_POINT) env_push(name, r->value);
        if (r->kind == REGION_VALUE) universal[index] = (Bound){r->letter, r->set};
        if (r->kind == REGION_EXCLUDED) excluded[excluded_count++] = r->excluded;
        proof_add("\\begin{itemize}\n");
        holds = in_regions(prove, data, body, from, depth + 1);
        proof_add("\\end{itemize}\n");
        if (r->kind == REGION_EXCLUDED) excluded_count--;
        if (r->kind == REGION_VALUE || r->kind == REGION_POINT) env_pop();
        universal[index] = kept;
    }
    region_depth--;
    if (!holds) rollback(mark);
    return holds && !failure;
}

/* La condizione da dimostrare in ogni caso di una distinzione chiesta
 * dentro un "per ogni" (18k). */
typedef struct {
    Formula *body;
    int negated;
} Claim;

/* La RegionGoal di un Claim: lo dimostra con establish(). */
static int claim_established(void *data) {
    Claim *claim = data;
    return establish(claim->body, claim->negated);
}

/* 18v-2. Dimostra body, negata se negated, distinguendo i casi che servono
 * sulle variabili generiche dal posto from in su: quelle appena introdotte
 * da un "per ogni". */
int establish_in_regions(Formula *body, int negated, int from) {
    Claim claim = {body, negated};
    return in_regions(claim_established, &claim, body, from, 0);
}

/* 18v-1. Stabilisce il caso di ogni applicazione definita per casi
 * nell'espressione node, dalle più interne: per ognuna, se l'argomento non è
 * un numero, dimostra la condizione di un caso e annota la scelta in
 * case_choice[], scrivendo il ragionamento. Ritorna 1 se ci riesce; se no
 * chiede una distinzione (18v-2) e ritorna 0, e il testo va cancellato da
 * chi chiama. */
static int cases_decided_in(const Node *node) {
    if (!node) return 1;
    if (failure || !cases_decided_in(node->a) || !cases_decided_in(node->b) || !cases_decided_in(node->c)) return 0;
    const Map *map = node->kind == N_APPLY ? map_find(node->name) : NULL;
    if (!map || !map->cases) return 1;
    Rat t = eval(node->a);
    if (failure) return 0;
    if (case_computed(map, t) >= 0) return 1;
    if (failure) return 0;
    for (int i = case_choice_count - 1; i >= 0; i--)
        if (case_choice[i].node == node && rat_same(case_choice[i].argument, t)) return 1;
    if (case_choice_count == MAX_CASE_CHOICES) return 0;

    /* Il primo caso la cui condizione si dimostra. */
    for (int i = 0; i < map->cases && !failure; i++) {
        size_t start = proof_length;
        env_push(map->parameter, t);
        Rat value = eval(map->piece[i].value);
        proof_add("\\item By the definition of $%c$, $%c(", map->name, map->name);
        put_fraction(t);
        proof_add(") = ");
        put_fraction(value);
        proof_add("$:");
        int holds = !failure && case_proved(map->piece[i].when, 0);
        env_pop();
        if (holds) {
            proof_add("\n");
            case_choice[case_choice_count++] = (CaseChoice){node, t, i};
            return 1;
        }
        proof_cut(start);
        if (failure == OUT_OF_MEMORY) return 0;
        failure = NULL;
    }
    split_from_cases(map, t);
    return 0;
}

/* 18v-1. Stabilisce il caso di ogni applicazione definita per casi nelle
 * espressioni della condizione f, che non contiene quantificatori. */
static int cases_decided(const Formula *f) {
    if (!f) return 1;
    if (f->kind == F_NOT || f->kind == F_AND || f->kind == F_OR || f->kind == F_IMPLIES || f->kind == F_IFF)
        return cases_decided(f->a) && cases_decided(f->b);
    return cases_decided_in(f->left) && cases_decided_in(f->right);
}

/* Elenca in list[], a partire dal posto count, le uguaglianze di f (negata
 * se negated) da cui si può ricavare il valore di una variabile, e ritorna il
 * nuovo numero di elementi; list ha MAX_EQUATIONS posti.
 *
 * In una congiunzione ogni uguaglianza deve valere, quindi il valore cercato
 * la soddisfa: è una condizione necessaria. In una disgiunzione basta che
 * valga una parte, quindi un'uguaglianza di una parte non è necessaria; ma
 * risolverla è un modo di rendere vera la condizione ("esiste y con A o B"
 * vale se esiste y con A). In tutti e due i casi il valore trovato è solo
 * una proposta: chi chiama ricontrolla l'intera condizione.
 *
 * Non entra in un "per ogni y" più interno: lì ogni uguaglianza va letta
 * per tutti gli y, e risolverne una darebbe un valore che cambia con y. In
 * un "esiste y" più interno entra, e ne prende le sole uguaglianze in cui y
 * non compare: "esiste y con A e B(y)" chiede A quanto "A, ed esiste y con
 * B(y)". È ciò che serve per \exists p, q\ (p = a + c \land q = b + d),
 * dove il valore di p sta in un'uguaglianza scritta dopo \exists q. */
static int find_equations(Formula *f, int negated, const Formula **list, int count) {
    Junction j;
    if (f->kind == F_NOT) return find_equations(f->a, !negated, list, count);
    if (f->kind == F_EQUAL || f->kind == F_DISTINCT) {
        if ((f->kind == F_EQUAL) != negated && count < MAX_EQUATIONS) list[count++] = f;
        return count;
    }
    if ((f->kind == F_FORALL || f->kind == F_EXISTS) && (f->kind == F_EXISTS) != negated) {
        int found = find_equations(f->a, negated, list, count), kept = count;
        for (int i = count; i < found; i++)
            if (!node_uses_letter(list[i]->left, f->variable) && !node_uses_letter(list[i]->right, f->variable)) list[kept++] = list[i];
        return kept;
    }
    if (!junction(f, negated, &j)) return count;
    return find_equations(j.y, j.ny, list, find_equations(j.x, j.nx, list, count));
}

/* 18i, secondo caso. L'uguaglianza `equation`, richiesta dalla condizione del
 * quantificatore f, ha per numeratore il polinomio num, che non è di primo
 * grado in x. Se num contiene solo x, con coefficienti numerici, i valori
 * possibili di x sono le sue radici, e quelle razionali si trovano tutte
 * (vedi rational_roots()): si prova ciascuna di quelle che stanno
 * nell'insieme. Scrive il ragionamento e ritorna 1 se una funziona.
 *
 * È ciò che permette di trovare x = 41 per x^2 = 1681, che nessun elenco dei
 * "numeri più semplici" (18j) raggiungerebbe. cleared dice se num è stato
 * ottenuto togliendo denominatori. */
static int solve_by_roots(Formula *f, int negated, const Formula *equation, Poly num, int cleared) {
    long long c[MAX_UNIVARIATE + 1], scale;
    Frac root[MAX_UNIVARIATE + 1];
    int degree = poly_coefficients(num, atom_var(f->variable), c, &scale);
    int roots = degree >= 2 ? rational_roots(c, degree, root) : 0;
    if (roots >= 0 && degree >= 2 && !roots_confirmed(num, atom_var(f->variable), root, roots, &f->numbers)) return 0;
    for (int k = 0; k < roots; k++) {
        Mark mark = mark_here();
        if (!numbers_contain(&f->numbers, root[k])) continue;
        proof_add("\\item We look for $%c$ with $", f->variable);
        put_source(equation);
        proof_add("$. %s this equation is $", cleared ? "After clearing denominators," : "Written out,");
        put_poly(num);
        proof_add(" = 0$, whose rational roots are $");
        for (int j = 0; j < roots; j++) {
            if (j) proof_add(",\\ ");
            put_frac(root[j]);
        }
        proof_add("$. Take $%c = ", f->variable);
        put_frac(root[k]);
        proof_add("$, an element of $");
        put_numbers(&f->numbers);
        proof_add("$.\n");

        /* La condizione, con x legata alla radice. */
        choose(f->variable, root[k]);
        env_push(f->variable, rat_frac(root[k]));
        int holds = establish(f->a, negated);
        env_pop();
        if (holds) { witness_keep(f, rat_frac(root[k])); return 1; }
        rollback(mark);
    }
    return 0;
}

/* Prototipo in avanti inevitabile: 18v-3 risolve la stessa equazione caso
 * per caso, chiamando di nuovo solve_with() con il caso scelto. */
static int solve_through_cases(Formula *f, int negated, const Formula *equation);

/* 18i. Prova a dimostrare "esiste x in A tale che ..." risolvendo
 * l'uguaglianza `equation`, una di quelle di find_equations(). f è il nodo
 * del quantificatore e negated il segno con cui va letta la sua condizione.
 * Scrive il ragionamento e ritorna 1 se ci riesce; se ritorna 0 il testo
 * scritto va cancellato da chi chiama.
 *
 * Se l'uguaglianza, tolti i denominatori, è di grado più alto in x, la si
 * passa a solve_by_roots(). Se è di primo grado, cioè alpha x + beta = 0 con
 * alpha e beta senza x, l'unico valore possibile è x = -beta/alpha. Va
 * controllato tutto ciò che questo sottintende: che alpha non si annulli
 * mai, che il valore stia in A, e infine che con quel valore la condizione
 * valga davvero. Quest'ultimo controllo ricalcola tutto da capo, quindi non
 * si fida dei passaggi fatti per ricavare x. */
static int solve_with(Formula *f, int negated, const Formula *equation) {
    int x = atom_var(f->variable);
    Poly num, den, part[2], shown_num, shown_den;
    Num number;
    if (failure) return 0;

    /* L'equazione come alpha x + beta = 0. Qui x non è legata: è un atomo.
     *
     * È un conto fatto per tentativo, senza aver controllato i divisori: con
     * i valori dati alle altre variabili può capitare una divisione per zero.
     * Vuol dire solo che così non si ricava nulla, quindi l'errore si
     * cancella; all'ingresso `failure` era NULL, e non si perde altro. */
    Rat gap = rat_add(eval(equation->left), eval(equation->right), 1);
    if (failure == CASE_UNDECIDED && poly_uses(undecided_argument.num, x)) {
        failure = NULL;
        return solve_through_cases(f, negated, equation);
    }
    if (failure) { failure = NULL; return 0; }
    if (!rat_polynomials(gap, &num, &den)) return 0;
    if (poly_split(num, x, part, 1) != 1) return solve_by_roots(f, negated, equation, num, !poly_is_one(den));
    Poly alpha = part[1], minus_beta = poly_negate(part[0]);
    Rat solution = rat_make(minus_beta, alpha);
    if (!rat_polynomials(solution, &shown_num, &shown_den)) return 0;

    /* Controllo del passo: alpha x - (-beta) deve ridare il numeratore
     * dell'equazione, che il testo sta per riscrivere in quella forma. */
    Poly linear = poly_add(poly_mul(alpha, rat_atom(x).num), minus_beta, 1);
    if (failure) return 0;
    if (!poly_equal(linear, num)) { unjustified_steps++; return 0; }

    proof_add("\\item We look for $%c$ with $", f->variable);
    put_source(equation);
    proof_add("$. %s this equation is $", poly_is_one(den) ? "Written out," : "After clearing denominators,");
    if (!poly_is_one(alpha)) put_factor(alpha);
    proof_add("%c = ", f->variable);
    put_poly(minus_beta);
    proof_add("$.");

    /* Si può dividere per alpha solo se non si annulla mai. */
    if (!poly_is_constant(alpha)) {
        proof_add(" The coefficient of $%c$ is never zero.", f->variable);
        if (!zero_only_where(alpha, NULL)) {
            split_at_zero((Rat){alpha, poly_const(num_int(1))});
            return 0;
        }
    }

    /* Il valore, e la sua appartenenza ad A. */
    proof_add("\n\\item So take $%c = ", f->variable);
    put_ratio(shown_num, shown_den);
    proof_add("$. It has to be an element of $");
    put_numbers(&f->numbers);
    proof_add("$.");
    if (!always_in(solution, &f->numbers)) {
        split_for_membership(solution, &f->numbers);
        return 0;
    }
    proof_add("\n");

    /* La condizione, con x legata al valore trovato. */
    if (rat_number(solution, &number)) choose(f->variable, number.re);
    env_push(f->variable, solution);
    int holds = establish(f->a, negated);
    env_pop();
    if (holds) witness_keep(f, solution);
    return holds;
}

/* Se il caso piece di map è un punto, "x = c" con x la variabile della regola
 * e c un numero, mette c in *point e ritorna 1. */
int case_point(const Map *map, int piece, Frac *point) {
    const Formula *c = map->piece[piece].when;
    Num value;
    if (c->kind != F_EQUAL) return 0;
    const Node *other = c->left->kind == N_VAR && c->left->name == map->parameter ? c->right
                      : c->right->kind == N_VAR && c->right->name == map->parameter ? c->left : NULL;
    if (!other || node_uses_letter(other, map->parameter)) return 0;
    int number = rat_number(eval(other), &value) && value.im.num == 0;
    if (failure) { failure = NULL; return 0; }
    if (number) *point = value.re;
    return number;
}

/* 18v-3. L'uguaglianza `equation`, richiesta dalla condizione dell'"esiste"
 * f, contiene un'applicazione definita per casi il cui argomento dipende
 * dalla variabile x: è quella che ha fatto fallire il conto (undecided_*).
 * Si prova un caso alla volta: se il caso è un punto x = c si prova c; se no
 * l'uguaglianza si risolve (18i) con il valore di quel caso. Il caso è solo
 * un tentativo: scelto il valore, la condizione di f si dimostra da capo, e
 * 18v-1 stabilisce il caso con una dimostrazione. Scrive il ragionamento e
 * ritorna 1 se un caso funziona; se ritorna 0 il testo va cancellato. */
static int solve_through_cases(Formula *f, int negated, const Formula *equation) {
    const Map *map = undecided_map;
    const Node *node = undecided_node;
    Rat argument = undecided_argument;
    int x = atom_var(f->variable);
    if (case_choice_count == MAX_CASE_CHOICES) return 0;
    for (int i = 0; i < map->cases && !failure && search_left > 0; i++) {
        Mark mark = mark_here();
        Frac point;
        int holds;
        if (rat_same(argument, rat_atom(x)) && case_point(map, i, &point)) {
            if (!numbers_contain(&f->numbers, point)) continue;
            proof_add("\\item Case %d of the definition of $%c$ is $%c = ", i + 1, map->name, f->variable);
            put_frac(point);
            proof_add("$: take $%c = ", f->variable);
            put_frac(point);
            proof_add("$, an element of $");
            put_numbers(&f->numbers);
            proof_add("$.\n");
            choose(f->variable, point);
            env_push(f->variable, rat_frac(point));
            holds = establish(f->a, negated);
            env_pop();
            if (holds) witness_keep(f, rat_frac(point));
        } else {
            env_push(map->parameter, argument);
            Rat value = eval(map->piece[i].value);
            proof_add("\\item In case %d of the definition of $%c$, where ", i + 1, map->name);
            put_condition(map->piece[i].when, 0);
            proof_add(", $%c(", map->name);
            put_fraction(argument);
            proof_add(") = ");
            put_fraction(value);
            proof_add("$.\n");
            env_pop();
            case_choice[case_choice_count++] = (CaseChoice){node, argument, i};
            holds = !failure && solve_with(f, negated, equation);
            case_choice_count--;
        }
        if (holds) return 1;
        rollback(mark);
        if (failure == CASE_UNDECIDED) failure = NULL;
    }
    return 0;
}

/* 18i. Prova a dimostrare "esiste x in A tale che ..." risolvendo, una dopo
 * l'altra, le uguaglianze da cui x si può ricavare. Ritorna 1 se una
 * funziona; se ritorna 0 non lascia testo né scelte. */
static int solve_for(Formula *f, int negated) {
    const Formula *equation[MAX_EQUATIONS];
    int count = find_equations(f->a, negated, equation, 0);
    for (int i = 0; i < count && !failure && search_left > 0; i++) {
        Mark mark = mark_here();
        if (solve_with(f, negated, equation[i])) return 1;
        rollback(mark);
    }
    return 0;
}

/* =============================================================================
 * 18.5 LE IPOTESI "ESISTE", CON IL LORO TESTIMONE (18u)
 * ============================================================================
 *
 * A che cosa serve. "Se x - y è un intero e y - z è un intero, allora x - z
 * è un intero" si scrive
 *
 *     ((\exists k \in Z (x - y = k)) \land (\exists j \in Z (y - z = j)))
 *         \implies \exists m \in Z (x - z = m).
 *
 * Le regole viste finora dimostrano una disgiunzione una parte per volta, e
 * qui nessuna parte vale da sola: non è vero che l'ipotesi è sempre falsa,
 * né che x - z è sempre intero. Un matematico direbbe: "sia k l'intero che
 * l'ipotesi fornisce, e j l'altro; allora x - z = k + j". Questa regola fa
 * lo stesso, in tre passi, su una disgiunzione di cui si guardano tutte le
 * parti insieme (un'implicazione "A implica B" è la disgiunzione "non A,
 * oppure B": vedi junction()).
 *
 *   18u-1. Dare un nome. Una parte "per ogni v in A vale P(v)" (ed è così
 *          che si legge un'ipotesi "esiste v in A con H(v)", che nella
 *          disgiunzione compare negata: "per ogni v, non H(v)") diventa
 *          P(v) con v variabile generica. È lecito: se per ogni v vale
 *          "P(v) oppure R", e R non contiene v, allora o R è vera, oppure è
 *          falsa e P(v) vale per ogni v. Serve che v non compaia in R: per
 *          questo la lettera non deve essere usata nelle altre parti.
 *   18u-2. Svolgere. Una parte "s appartiene ad A" è "esiste q in A con
 *          s = q", e "u divide v" è "esiste q intero con v = q u" (17n):
 *          sono le definizioni, e sostituirle non cambia nulla. Così
 *          un'ipotesi a \equiv b \pmod{n}, con n una lettera, riceve anche
 *          lei il nome del suo quoziente. La regola 18r non è toccata:
 *          quando i moduli sono numeri decide lei, provando i resti.
 *   18u-3. Trovare il valore. Resta una parte "esiste m in A con E(m)",
 *          accanto a delle ipotesi H_1 = 0, ..., H_r = 0. Se E è di primo
 *          grado in m, cioè alpha m + beta = 0, si cerca m tra i polinomi
 *          nelle variabili generiche: un polinomio w e dei moltiplicatori
 *          c_i con
 *
 *              alpha w + beta = c_1 H_1 + ... + c_r H_r
 *
 *          come polinomi. È lo stesso sistema lineare della regola 18s, con
 *          in più i coefficienti di w tra le incognite: alpha fa da
 *          "ipotesi" il cui moltiplicatore è -w. Trovato w, lo si lega a m
 *          e si dimostra il resto con le regole di sempre: sarà la 18s a
 *          riscrivere l'identità e a ricontrollarla. Più "esiste" di
 *          seguito si cercano insieme: alpha_1 w_1 + alpha_2 w_2 + beta.
 *
 * Perché w va cercato tra i polinomi nelle sole variabili intere, quando A
 * è un insieme di interi: m = x - z soddisfa l'equazione, ma non si può
 * dimostrare che sia intero; m = k + j sì, perché k e j lo sono (18d). Che
 * il valore stia in A va infatti dimostrato per ogni valore delle variabili
 * generiche, senza usare le ipotesi: è più di quanto servirebbe, ed è ciò
 * che always_in() sa fare.
 *
 * Due parti con la stessa lettera. Una variabile è identificata dalla sua
 * lettera, quindi due ipotesi scritte tutte e due con \exists k non possono
 * ricevere tutte e due il nome k: prima di dare il nome, una viene riscritta
 * con una lettera che lì non è usata (quantifier_renamed()).
 *
 * Perché dare un nome è lecito, e che cosa lo garantisce. 18u-1 allarga la
 * portata di una lettera a tutta la disgiunzione, e un errore qui
 * fonderebbe due numeri in uno: da \exists k (x = 2k) e \exists k (y = 2k)
 * seguirebbe x = y. Il passo è corretto a tre condizioni, ognuna con la sua
 * difesa:
 *
 *   - v non compare nelle altre parti, né tra le variabili in vista
 *     (generiche, legate, applicazioni): letter_is_free() lo controlla su
 *     ogni nodo, quantificato o no (formula_uses_letter());
 *   - dentro la parte, v indica sempre lo stesso numero: formula_check()
 *     vieta di quantificare una lettera dentro se stessa, e le copie che
 *     nascono qui, rinominate o svolte, usano lettere che lì non compaiono;
 *   - la copia rinominata dice la stessa cosa dell'originale: nasce
 *     riscrivendo un testo, e formula_renamed() la confronta nodo per nodo
 *     con l'originale (alfa-equivalenza).
 *
 * Un errore che nessuna delle tre vede resta possibile, per esempio un tipo
 * di nodo nuovo con una lettera che formula_uses_letter() non guarda. Lo
 * fermerebbe la verifica del capitolo 19, che ricalcola l'enunciato com'è
 * scritto, con le sue portate, su valori che soddisfano le ipotesi: due
 * numeri fusi per errore danno una tesi che lì fallisce (x = 0, y = 2).
 *
 * Che cosa non fa. Non si applica dentro una dimostrazione per casi sul
 * resto (18o). Il valore cercato e solo un polinomio: un'ipotesi "per
 * ogni" non viene mai usata su un valore particolare.
 *
 * La verifica indipendente. I valori trovati qui sono espressioni nelle
 * lettere a cui è stato dato un nome, e quelle lettere non esistono fuori da
 * questa dimostrazione: la verifica dell'enunciato non potrebbe calcolarli.
 * Perciò, riuscita la dimostrazione, ciò che è stato annotato nei nodi viene
 * dimenticato (forget_choices()), e i controlli sono due, descritti in testa
 * al capitolo 19:
 *
 *   - l'enunciato com'è scritto, su valori che soddisfano le ipotesi per
 *     costruzione: per \exists k (x = k^2 + 7) si sceglie k e si calcola x.
 *     Se le ipotesi non sono mai risultate vere (meno di MIN_SATISFIED
 *     volte), il verdetto non viene emesso;
 *   - il valore scelto qui, annotato prima di dimenticarlo
 *     (record_witnesses()): dove le ipotesi valgono deve stare nel suo
 *     insieme e rendere vera la condizione. Si calcola con i numeri, senza
 *     l'identità tra polinomi con cui 18s ha giustificato il passo, e una
 *     copia del programma che scriveva w con il segno sbagliato, o non
 *     chiedeva che w fosse intero, è stata fermata così.
 */

/* I valori trovati da 18u-3 nella dimostrazione in corso: i primi
 * record_count (vedi Mark). */
WitnessRecord witness_records[MAX_RECORDS];

/* universal_named e dichiarato con la pila dei legami: la verifica da un
 * valore prima ai testimoni delle ipotesi, poi alle altre variabili. */

/* Prototipo in avanti inevitabile: forget_choices() sta nel capitolo 19, con
 * la verifica a cui serve, e 18u deve chiamarla quando riesce. */
void forget_choices(Formula *f);

/* Elenca in leaf[], a partire dal posto count, le parti della disgiunzione
 * f (negata se negated): scende nelle negazioni e nei connettivi che, con
 * quel segno, sono disgiunzioni, e si ferma su tutto il resto. Ritorna il
 * nuovo numero di parti, o -1 se sono più di MAX_LEAVES. */
static int leaves_collect(Formula *f, int negated, Leaf *leaf, int count) {
    Junction j;
    if (count < 0) return -1;
    if (f->kind == F_NOT) return leaves_collect(f->a, !negated, leaf, count);
    if (junction(f, negated, &j) && !j.conjunction) return leaves_collect(j.y, j.ny, leaf, leaves_collect(j.x, j.nx, leaf, count));
    if (count == MAX_LEAVES) return -1;
    leaf[count] = (Leaf){f, negated};
    return count + 1;
}

/* Ritorna la condizione f con la sua parte `old` sostituita da `by`. I nodi
 * che stanno tra f e old vengono copiati, così f resta com'era; il segno
 * con cui `by` va letta è quello che aveva old, perché i connettivi intorno
 * sono gli stessi. Se l'arena è piena ritorna f, e l'errore è annotato. */
static Formula *leaf_replaced(Formula *f, const Formula *old, Formula *by) {
    if (f == old) return by;
    if (f->kind != F_NOT && f->kind != F_AND && f->kind != F_OR && f->kind != F_IMPLIES) return f;
    Formula *a = leaf_replaced(f->a, old, by), *b = f->b ? leaf_replaced(f->b, old, by) : NULL;
    if (a == f->a && b == f->b) return f;
    Formula *copy = arena_alloc(sizeof *copy);
    if (!copy) return f;
    *copy = *f;
    copy->a = a;
    copy->b = b;
    return copy;
}

/* Ritorna 1 se la lettera può diventare il nome di una variabile che vale
 * per tutta la disgiunzione leaf[0..count), pur essendo scritta solo nella
 * parte own: non deve essere già una variabile generica o legata, né
 * comparire in un'altra parte. Con own = -1 nessuna parte è esclusa. */
static int letter_is_free(const Leaf *leaf, int count, int own, int letter) {
    if (env_lookup(letter) || map_find(letter)) return 0;
    for (int i = 0; i < universal_count; i++)
        if (universal[i].name == letter) return 0;
    for (int i = 0; i < count; i++)
        if (i != own && formula_uses_letter(leaf[i].source, letter)) return 0;
    return 1;
}

/* 18u-2. Ritorna la definizione svolta della condizione f, che è
 * un'appartenenza a un insieme numerico o una divisibilità:
 *
 *     s \in A     diventa   \exists q \in A\ (s = q)
 *     u \mid v    diventa   \exists q \in \mathbb{Z}\ (v = q \cdot u)
 *
 * preceduta da \lnot se f è scritta con \notin o \nmid. q è `letter`, una
 * lettera che l'enunciato non usa in quel punto. Il testo dei nuovi nodi
 * viene scritto qui, perché l'enunciato non lo contiene; ritorna NULL se
 * l'arena è piena. */
static Formula *membership_unfolded(const Formula *f, int letter) {
    int divides = f->kind == F_DIVIDES;

    /* Il testo, composto nel buffer della dimostrazione e poi tolto da lì:
     * si annota dove cadono l'insieme e l'uguaglianza. */
    size_t from = proof_length;
    if (f->swapped) proof_add("\\lnot ");
    size_t quantifier_at = proof_length - from;
    proof_add("\\exists %c \\in ", letter);
    size_t set_at = proof_length - from;
    if (divides) proof_add("\\mathbb{Z}"); else put_numbers(&f->numbers);
    size_t set_end = proof_length - from;
    proof_add("\\ (");
    size_t equation_at = proof_length - from;
    put_node(divides ? f->right : f->left, 0);
    proof_add(" = %c", letter);
    if (divides) { proof_add(" \\cdot "); put_node(f->left, 4); }
    size_t equation_end = proof_length - from;
    proof_add(")");
    size_t length = proof_length - from;
    char *text = arena_alloc(length + 1);
    if (text) memcpy(text, proof_text + from, length + 1);
    proof_cut(from);
    if (!text) return NULL;

    /* I nodi: l'uguaglianza, il quantificatore, la negazione. */
    Node *name = node_new(N_VAR, NULL, NULL);
    name->name = letter;
    Formula *equation = formula_node(F_EQUAL, NULL, NULL, text + equation_at);
    equation->end = text + equation_end;
    equation->left = divides ? f->right : f->left;
    equation->right = divides ? node_new(N_MUL, name, f->left) : name;
    Formula *exists = formula_node(F_EXISTS, equation, NULL, text + quantifier_at);
    exists->end = text + length;
    exists->variable = letter;
    if (divides) exists->numbers.integers = 1; else exists->numbers = f->numbers;
    exists->numbers.start = text + set_at;
    exists->numbers.end = text + set_end;
    if (!f->swapped) return exists;
    Formula *negation = formula_node(F_NOT, exists, NULL, text);
    negation->end = text + length;
    return negation;
}

/* 18y-4. IL NOME DI UN VALORE POSITIVO
 *
 * Un'ipotesi "esiste q in A con E(q)", dove E fissa il valore di q, dice di
 * più quando quel valore è sempre positivo: allora q sta nella parte
 * positiva di A. È un fatto, non una scelta: se E è alpha q + beta = 0, con
 * alpha che non si annulla mai, l'unico q possibile è -beta/alpha, e se
 * questo numero è positivo per ogni valore delle variabili generiche, ogni q
 * che soddisfa E è positivo. Quindi "esiste q in A con E(q)" ed "esiste q
 * nella parte positiva di A con E(q)" dicono la stessa cosa, in tutti e due i
 * versi, e il nome che 18u-1 dà a q può variare nella parte positiva.
 *
 * A che cosa serve. Due casi, con lo stesso ragionamento:
 *
 *   - x y^{-1} \in \mathbb{Q}, tra reali positivi, è "esiste q razionale con
 *     x y^{-1} = q" (18u-2): q = x/y è positivo, quindi q non è zero, e si
 *     può dividere per lui (18y-3): da x y^{-1} = q segue y x^{-1} = 1/q;
 *   - y = a x con x, y naturali e a intero: a = y/x è positivo, quindi a è
 *     un naturale, a >= 1. È ciò che serve all'antisimmetria della
 *     divisibilità (18z): da y = a x e x = b y segue a b = 1, e tra i naturali
 *     questo vuol dire a = b = 1.
 *
 * Si guardano le uguaglianze che E chiede tutte insieme: E stessa, o le
 * parti di una congiunzione. */

/* 18y-4. Se l'insieme a ha una parte positiva diversa da lui, scritta come
 * un insieme dei libri, la mette in *out e ritorna 1: \mathbb{N} per gli
 * interi che arrivano a 1 o sotto, \mathbb{Q}^{+} e \mathbb{R}^{+} per i
 * razionali e i reali senza estremo. Con dei punti tolti ritorna 0. */
static int positive_part(const NumberSet *a, NumberSet *out) {
    static const char *const written[] = {"\\mathbb{N}", "\\mathbb{Q}^{+}", "\\mathbb{R}^{+}"};
    if (a->holes || (a->bounded && (!a->integers || a->low >= 1))) return 0;
    memset(out, 0, sizeof *out);
    out->integers = a->integers;
    out->reals = a->reals;
    out->bounded = 1;
    out->low = a->integers ? 1 : 0;
    out->strict = !a->integers;
    out->start = written[a->integers ? 0 : a->reals ? 2 : 1];
    out->end = out->start + strlen(out->start);
    return 1;
}

/* 18y-4. Dimostra che l'"esiste" q, un'ipotesi, fissa un valore positivo per
 * la sua lettera, come descritto in testa al paragrafo: una delle
 * uguaglianze che la sua condizione chiede è alpha q + beta = 0, con alpha
 * che non si annulla mai e -beta/alpha positivo. Scrive il ragionamento e
 * ritorna 1 se ci riesce; se ritorna 0 non lascia testo. */
static int witness_positive(const Formula *q) {
    const Formula *equation[MAX_EQUATIONS];
    int count = 0, x = atom_var(q->variable);
    Mark mark = mark_here();

    /* Le uguaglianze chieste tutte insieme: la condizione, o le parti di una
     * congiunzione. */
    const Formula *stack[MAX_EQUATIONS], *g;
    int depth = 0;
    stack[depth++] = q->a;
    while (depth && count < MAX_EQUATIONS) {
        g = stack[--depth];
        if (g->kind == F_AND && depth + 2 <= MAX_EQUATIONS) { stack[depth++] = g->b; stack[depth++] = g->a; }
        else if (g->kind == F_EQUAL) equation[count++] = g;
    }
    for (int i = 0; i < count && !failure; i++) {
        Poly num, den, part[2], top, bottom;
        Rat gap = rat_add(eval(equation[i]->left), eval(equation[i]->right), 1);
        if (failure) { failure = NULL; continue; }
        if (!rat_polynomials(gap, &num, &den) || poly_split(num, x, part, 1) != 1) continue;
        Rat value = rat_make(poly_negate(part[0]), part[1]);
        if (!rat_polynomials(value, &top, &bottom)) continue;
        proof_add("\\item In $");
        put_source(q);
        proof_add("$ the equality $");
        put_source(equation[i]);
        proof_add("$ fixes $%c = ", q->variable);
        put_ratio(top, bottom);
        proof_add("$.");
        if (!poly_is_constant(part[1])) proof_add(" The coefficient of $%c$ is never zero:", q->variable);
        int positive = poly_is_constant(part[1]) || zero_only_where(part[1], NULL);
        if (positive) proof_add(" That value is positive, so $%c$ is too.", q->variable);
        positive = positive && signs(top, top, NULL, 0, SIGN_POSITIVE) && (poly_is_one(bottom) || signs(bottom, bottom, NULL, 0, SIGN_POSITIVE));
        if (positive && !failure) { proof_add("\n"); return 1; }
        failure = NULL;
        rollback(mark);
    }
    return 0;
}

/* La lettera name dopo la sostituzione di ogni from[i] con to[i], per i <
 * count; -1 se name è già una delle to[i], che dovevano essere nuove. */
static int letter_renamed(int name, const int *from, const int *to, int count) {
    for (int i = 0; i < count; i++) {
        if (name == from[i]) return to[i];
        if (name == to[i]) return -1;
    }
    return name;
}

/* Ritorna 1 se l'espressione b è a con ogni lettera from[i] scritta to[i]:
 * stessi nodi, stessi numeri, stesse lettere tranne quelle cambiate. */
static int node_renamed(const Node *a, const Node *b, const int *from, const int *to, int count) {
    if (!a || !b) return a == b;
    return a->kind == b->kind && a->value == b->value && a->op == b->op && letter_renamed(a->name, from, to, count) == b->name &&
           node_renamed(a->a, b->a, from, to, count) && node_renamed(a->b, b->b, from, to, count) && node_renamed(a->c, b->c, from, to, count);
}

/* Come node_renamed(), per due condizioni: b deve essere a con le lettere
 * cambiate, nodo per nodo, con gli stessi insiemi.
 *
 * È il controllo del passo di quantifier_renamed(), scritto a parte: là la
 * copia nasce riscrivendo un testo e rileggendolo, e un errore della
 * riscrittura (una lettera tra le graffe di \mathbb{N} cambiata, come è già
 * successo con le definizioni svolte di 17j) darebbe un'altra condizione.
 * Qui si guarda che la copia sia la stessa condizione con le variabili
 * legate chiamate in un altro modo. Basta, perché ogni to[i] è una lettera
 * che in a non compare (letter_renamed() lo pretende), quindi due lettere
 * diverse restano diverse e una variabile non ne cattura un'altra: è ciò che
 * i logici chiamano alfa-equivalenza, e due condizioni alfa-equivalenti sono
 * vere o false insieme. */
static int formula_renamed(const Formula *a, const Formula *b, const int *from, const int *to, int count) {
    if (!a || !b) return a == b;
    return a->kind == b->kind && a->swapped == b->swapped && letter_renamed(a->variable, from, to, count) == b->variable &&
           numbers_equal(&a->numbers, &b->numbers) && node_renamed(a->left, b->left, from, to, count) &&
           node_renamed(a->right, b->right, from, to, count) && formula_renamed(a->a, b->a, from, to, count) &&
           formula_renamed(a->b, b->b, from, to, count);
}

/* 18u-1, quando la lettera è già usata altrove. Ritorna una copia del
 * quantificatore q, parte di posto own della disgiunzione leaf[0..count),
 * in cui ogni sua lettera che compare anche in un'altra parte è cambiata
 * con una che lì non è usata; ritorna NULL se non c'è nulla da cambiare o
 * se non ci riesce.
 *
 * I libri scrivono spesso due ipotesi con la stessa lettera, \exists k\ (a
 * - b = kn) e \exists k\ (b - c = kn): sono due numeri diversi, e per
 * dare un nome a tutti e due uno va chiamato in un altro modo. Cambiare il
 * nome di una variabile legata non cambia ciò che la condizione dice.
 *
 * La copia si ottiene come le definizioni svolte di 17j: si riscrive il
 * testo del quantificatore con la lettera nuova e lo si rilegge, così ogni
 * nodo ha il testo che gli corrisponde. Più lettere dopo lo stesso
 * quantificatore hanno un testo solo, quindi si cambiano insieme, e q deve
 * essere il nodo della prima. Una copia che non risulta la stessa
 * condizione con le lettere cambiate (formula_renamed()) è un passo non
 * giustificato, e non si usa. */
static Formula *quantifier_renamed(const Formula *q, const Leaf *leaf, int count, int own) {
    size_t binders = 0;
    for (const Formula *g = q; g->kind == q->kind && g->start == q->start && g->end == q->end; g = g->a) binders++;
    if (!binders) return NULL;
    char (*fresh)[2] = arena_alloc(binders * sizeof *fresh);
    const char **to = arena_alloc(binders * sizeof *to), *before = syntax_error;
    int *from = arena_alloc(binders * sizeof *from), *letters = arena_alloc(binders * sizeof *letters), changes = 0;
    if (!fresh || !to || !from || !letters) return NULL;

    /* Le lettere scritte dopo il quantificatore: i nodi con lo stesso
     * testo. Si cambiano quelle usate altrove, purché non siano già
     * variabili in vista: allora il nome nuovo non basterebbe. */
    for (const Formula *g = q; g->kind == q->kind && g->start == q->start && g->end == q->end; g = g->a) {
        int taken = 0, letter = 0;
        for (int i = 0; i < count; i++) taken = taken || (i != own && formula_uses_letter(leaf[i].source, g->variable));
        if (!taken) continue;
        for (const char *c = "hjkqrstuvwpgdcbamn"; *c && !letter; c++) {
            int used = !letter_is_free(leaf, count, -1, *c);
            for (int i = 0; i < changes; i++) used = used || fresh[i][0] == *c;
            if (!used) letter = *c;
        }
        if (!letter || !letter_is_free(leaf, 0, -1, g->variable)) return NULL;
        from[changes] = g->variable;
        fresh[changes][0] = (char)letter;
        fresh[changes][1] = 0;  /* Il deposito non e statico: la parola va terminata. */
        to[changes] = fresh[changes];
        letters[changes] = letter;
        changes++;
    }
    if (!changes) return NULL;

    /* Il testo riscritto, e la sua lettura. Un errore di lettura vuol dire
     * solo che la copia non si può fare; una copia letta che dice un'altra
     * cosa, invece, è un errore della riscrittura. */
    draft_length = 0;
    draft_rewrite(q->start, q->end, from, to, changes);
    Formula *copy = unfold();
    int read = !syntax_error;
    syntax_error = before;
    if (read && !formula_renamed(q, copy, from, letters, changes)) { unjustified_steps++; read = 0; }
    return read ? copy : NULL;
}

/* 18u-3, per una sola uguaglianza. Cerca i valori dei `names` "esiste" di
 * quantifier[] che rendono `equation` una conseguenza delle `hypotheses`
 * ipotesi di given[], e con quelli dimostra la disgiunzione f (negata se
 * negated) in cui body prende il posto di quantifier[0]. given[] deve avere
 * altri `names` posti liberi dopo le ipotesi. Scrive il ragionamento e
 * ritorna 1 se ci riesce; se ritorna 0 il testo scritto va cancellato da chi
 * chiama. */
static int witnesses_solve(Formula *f, int negated, Formula **quantifier, int names, Formula *body,
                           const Formula *equation, Poly *given, int hypotheses) {
    Poly num, den, part[2], alpha[MAX_NAMED], multiplier[MAX_LITERALS + MAX_NAMED];
    int need[MAX_LITERALS + MAX_NAMED] = {0};
    Mark mark = mark_here();

    /* L'equazione con le lettere cercate come atomi. È un conto fatto per
     * tentativo: se non riesce vuol dire solo che da qui non si ricava
     * nulla, come in solve_with(). */
    Rat gap = rat_add(eval(equation->left), eval(equation->right), 1);
    if (failure) { failure = NULL; return 0; }
    if (!rat_polynomials(gap, &num, &den)) return 0;

    /* num = beta + alpha_1 m_1 + ... + alpha_r m_r: di primo grado in ogni
     * lettera cercata, e senza prodotti tra due di loro. */
    Poly beta = num;
    for (int j = 0; j < names; j++) {
        if (poly_split(beta, atom_var(quantifier[j]->variable), part, 1) != 1) return 0;
        alpha[j] = part[1];
        beta = part[0];
    }
    for (int j = 0; j < names; j++)
        for (int k = 0; k < names; k++)
            if (poly_uses(alpha[j], atom_var(quantifier[k]->variable))) return 0;

    /* Prima l'equazione com'è, v = -1; poi, se ci sono ipotesi, moltiplicata
     * per una variabile generica v che non può valere zero (vedi "Un fattore
     * che non si annulla" in testa a 18s).
     *
     * 18y-3. Moltiplicata per v si può anche cercare v m al posto di m, se m
     * varia tra i razionali o i reali: allora m = w / v. Serve dove il
     * valore è un reciproco: da x = q y, con q diverso da zero, y = (1/q) x,
     * e 1/q non è un polinomio. Si cerca w con v beta + alpha w nullo dove
     * valgono le ipotesi; dividendo per v, che non è zero, beta + alpha (w /
     * v) lo è anche lui. */
    int fractions = 1;
    for (int j = 0; j < names; j++) fractions = fractions && !quantifier[j]->numbers.integers;
    for (int v = -1; v < (hypotheses ? universal_count : 0) && !failure && search_left > 0; v++)
        for (int divide = 0; divide <= (v >= 0 && fractions) && !failure && search_left > 0; divide++) {
            Poly scale = poly_const(num_int(1));
            if (v >= 0 && numbers_contain(universal[v].numbers, frac_int(0))) continue;
            if (v >= 0) scale = rat_atom(atom_var(universal[v].name)).num;
            Poly target = poly_mul(scale, beta);
            long long least = poly_degree(target);
            for (int j = 0; j < names; j++) {
                given[hypotheses + j] = divide ? alpha[j] : poly_mul(scale, alpha[j]);
                need[hypotheses + j] = quantifier[j]->numbers.integers ? LETTER_INTEGER : quantifier[j]->numbers.reals ? LETTER_REAL : LETTER_RATIONAL;
                if (poly_degree(given[hypotheses + j]) > least) least = poly_degree(given[hypotheses + j]);
            }

            /* Il grado di ciò che si cerca non è noto: si parte dal più basso
             * possibile e si sale di poco, finché il sistema ha una soluzione. */
            int found = 0;
            for (long long top = least; top <= least + 2 && !found && !failure && search_left > 0; top++)
                found = combination(target, given, hypotheses + names, multiplier, top, need);
            if (!found) continue;

            /* Controllo del passo: rifatto il conto con prodotti e somme,
             * scale (beta + alpha_1 w_1 + ...) deve essere la combinazione delle
             * ipotesi che il sistema ha trovato (scale beta + alpha_1 w_1 + ...
             * se si divide). I w_j sono i moltiplicatori degli alpha_j, cambiati
             * di segno. */
            Poly rebuilt = poly_const(num_int(0));
            for (int i = 0; i < hypotheses + names; i++) rebuilt = poly_add(rebuilt, poly_mul(multiplier[i], given[i]), 0);
            if (failure) return 0;
            if (!poly_equal(rebuilt, target)) { unjustified_steps++; continue; }

            /* I valori, e la loro appartenenza agli insiemi. Dividendo per v,
             * prima che v non è zero. */
            Rat value[MAX_NAMED];
            int inside = 1;
            proof_add("\\item We look for $%c", quantifier[0]->variable);
            for (int j = 1; j < names; j++) proof_add(", %c", quantifier[j]->variable);
            proof_add("$ with $");
            put_source(equation);
            proof_add("$%s.", hypotheses ? ", using what is assumed" : "");
            if (divide) {
                proof_add(" We divide by $%c$, which is not zero.", universal[v].name);
                inside = zero_only_where(scale, NULL);
            }
            for (int j = 0; j < names && inside; j++) {
                Poly shown_num, shown_den;
                value[j] = rat_make(poly_negate(multiplier[hypotheses + j]), divide ? scale : poly_const(num_int(1)));
                proof_add(" Take $%c = ", quantifier[j]->variable);
                if (rat_polynomials(value[j], &shown_num, &shown_den)) put_ratio(shown_num, shown_den); else put_poly(value[j].num);
                proof_add("$. It has to be an element of $");
                put_numbers(&quantifier[j]->numbers);
                proof_add("$.");
                inside = always_in(value[j], &quantifier[j]->numbers);
            }
            proof_add("\n");
            if (!inside) { rollback(mark); continue; }

            /* Il resto, con le lettere legate ai valori trovati. */
            for (int j = 0; j < names; j++) {
                Num number;
                if (rat_number(value[j], &number)) choose(quantifier[j]->variable, number.re);
                env_push(quantifier[j]->variable, value[j]);
            }
            int holds = establish(leaf_replaced(f, quantifier[0], body), negated);
            for (int j = 0; j < names; j++) env_pop();
            if (!holds) { rollback(mark); continue; }
            for (int j = 0; j < names; j++) witness_keep(quantifier[j], value[j]);
            return 1;
        }
    return 0;
}

/* Annota in witness_records[] ciò che 18u-3 ha appena affermato. I `names`
 * "esiste" di quantifier[] cominciano la parte own della disgiunzione
 * leaf[0..count), body è la condizione che li segue, da leggere con il segno
 * sign, e i valori scelti sono nei nodi. Ritorna 0, senza annotare nulla, se
 * l'elenco è pieno: allora il valore non va usato, perché nessuno lo
 * ricontrollerebbe.
 *
 * Si copia lo stato della dimostrazione in quel momento: le variabili
 * generiche, prima quelle a cui 18u-1 ha dato il nome di un testimone, e
 * quelle legate a un valore. I valori nei nodi invece non bastano: 18u-1
 * li dimentica (forget_choices()), perché contengono lettere che fuori dalla
 * dimostrazione non esistono. */
static int record_witnesses(const Leaf *leaf, int count, int own, Formula **quantifier, int names, const Formula *body, int sign) {
    if (record_count == MAX_RECORDS) return 0;
    WitnessRecord *r = &witness_records[record_count++];
    r->generics = 0;
    r->generic = arena_alloc(((size_t)universal_count + 1) * sizeof *r->generic);
    if (!r->generic) { record_count--; return 0; }
    for (int named = 1; named >= 0; named--)
        for (int i = 0; i < universal_count; i++)
            if ((int)universal_named[i] == named) r->generic[r->generics++] = universal[i];
    r->bindings = env_count;
    r->binding = arena_alloc(((size_t)env_count + 1) * sizeof *r->binding);
    if (!r->binding) { record_count--; return 0; }
    for (int i = 0; i < env_count; i++) r->binding[i] = *env_at(i);
    r->leaves = 0;
    for (int i = 0; i < count; i++)
        if (i != own) r->leaf[r->leaves++] = leaf[i];
    r->names = names;
    for (int j = 0; j < names; j++) {
        r->quantifier[j] = quantifier[j];
        r->value[j] = quantifier[j]->witness[split_case];
    }
    r->body = body;
    r->sign = sign;
    return 1;
}

/* 18x. IL VALORE DI UN ESPONENTE
 *
 * "Esiste m intero con b = 2^{m} a", accanto all'ipotesi a = 2^{n} b: m sta
 * in un esponente, e l'equazione non è di primo grado in m, quindi 18u-3 non
 * lo trova. Ma gli esponenti si sommano quando le potenze si moltiplicano, e
 * il valore che serve è di solito una combinazione degli esponenti delle
 * ipotesi: qui m = -n; con a = 2^{n} b e b = 2^{k} c, per a = 2^{m} c, m =
 * n + k. La regola prova come valore di un "esiste" tra gli interi, la cui
 * lettera compare solo negli esponenti, le somme n_1 \pm ... \pm n_j delle
 * variabili generiche intere che compaiono negli esponenti delle altre
 * parti, dalle più corte; con ognuna la disgiunzione viene dimostrata da
 * capo, con le regole di sempre. È una ricerca, come 18j: un valore che non
 * porta a una dimostrazione si scarta, e uno che ci porta è giusto perché
 * la dimostrazione c'è. Il valore trovato si annota come quelli di 18u-3, e
 * la verifica del capitolo 19 lo ricontrolla con i numeri. */

/* 18x. Ritorna 1 se la lettera compare nell'espressione node fuori dagli
 * esponenti: come variabile, o nella base di una potenza. */
static int letter_outside_exponents(const Node *node, int letter) {
    if (!node) return 0;
    if (node->kind == N_POW) return letter_outside_exponents(node->a, letter);
    if (node->name == letter && (node->kind == N_VAR || node->kind == N_BIGOP || node->kind == N_SEQ || node->kind == N_APPLY)) return 1;
    return letter_outside_exponents(node->a, letter) || letter_outside_exponents(node->b, letter) || letter_outside_exponents(node->c, letter);
}

/* 18x. Ritorna 1 se nella condizione f la lettera compare, e solo negli
 * esponenti delle potenze. */
int letter_only_in_exponents(const Formula *f, int letter) {
    if (!f) return 1;
    if (letter_outside_exponents(f->left, letter) || letter_outside_exponents(f->right, letter)) return 0;
    return letter_only_in_exponents(f->a, letter) && letter_only_in_exponents(f->b, letter);
}

/* 18x. Aggiunge a letters[], che ne ha *count e posto per MAX_NAMED, le
 * variabili generiche intere che compaiono negli esponenti dell'espressione
 * node, ognuna una volta. inside dice se si è già dentro un esponente. */
static void exponent_letters(const Node *node, int inside, int *letters, int *count) {
    if (!node) return;
    if (inside && node->kind == N_VAR && !env_lookup(node->name)) {
        int who = universal_index(atom_var(node->name)), seen = 0;
        for (int i = 0; i < *count; i++) seen = seen || letters[i] == node->name;
        if (who >= 0 && universal[who].numbers->integers && !seen && *count < MAX_NAMED) letters[(*count)++] = node->name;
    }
    exponent_letters(node->a, inside, letters, count);
    exponent_letters(node->b, inside || node->kind == N_POW, letters, count);
    exponent_letters(node->c, inside, letters, count);
}

/* 18x. Come exponent_letters(), per ogni espressione della condizione f. */
static void formula_exponent_letters(const Formula *f, int *letters, int *count) {
    if (!f) return;
    exponent_letters(f->left, 0, letters, count);
    exponent_letters(f->right, 0, letters, count);
    formula_exponent_letters(f->a, letters, count);
    formula_exponent_letters(f->b, letters, count);
}

/* Fin dove arriva, in valore assoluto, la costante che 18x aggiunge alle
 * combinazioni degli esponenti. */
#define EXPONENT_SHIFT 2

/* 18x. Prova il valore value per l'"esiste" q con cui comincia la parte own
 * della disgiunzione f (negata se negated), le cui parti sono
 * leaf[0..count); body è la condizione di q, da leggere con il segno sign.
 * Ritorna 1 se con quel valore la disgiunzione è dimostrata e il valore
 * annotato per la verifica; 0 se no, senza lasciare testo né scelte; -1 se
 * è dimostrata ma l'elenco delle annotazioni è pieno, e allora il valore non
 * si può usare: nessuno lo ricontrollerebbe. */
static int exponent_try(Formula *f, int negated, const Leaf *leaf, int count, int own, Formula *q, Formula *body, int sign, Rat value) {
    Mark mark = mark_here();
    proof_add("\\item The letter $%c$ appears only in exponents, and exponents add up when powers are multiplied: we try $%c = ", q->variable, q->variable);
    put_poly(value.num);
    proof_add("$. It has to be an element of $");
    put_numbers(&q->numbers);
    proof_add("$.");
    if (!always_in(value, &q->numbers)) { rollback(mark); return 0; }
    proof_add("\n");
    env_push(q->variable, value);
    int holds = establish(leaf_replaced(f, q, body), negated);
    env_pop();
    if (!holds) { rollback(mark); return 0; }
    witness_keep(q, value);
    if (record_witnesses(leaf, count, own, &q, 1, body, sign)) return 1;
    witness_drop(q);
    rollback(mark);
    return -1;
}

/* 18x. Dimostra la disgiunzione f (negata se negated), le cui parti sono
 * leaf[0..count), dando all'"esiste" q con cui comincia la parte own, la cui
 * condizione è body da leggere con il segno sign, il valore di una
 * combinazione degli esponenti delle altre parti (vedi la testa del
 * paragrafo). Scrive il ragionamento e ritorna 1 se ci riesce; se ritorna 0
 * non lascia testo né scelte. */
static int exponent_witness(Formula *f, int negated, const Leaf *leaf, int count, int own, Formula *q, Formula *body, int sign) {
    int letters[MAX_NAMED], found = 0;
    if (!power_letters || !q->numbers.integers || !formula_uses_letter(body, q->variable) || !letter_only_in_exponents(body, q->variable)) return 0;
    for (int i = 0; i < count; i++)
        if (i != own) formula_exponent_letters(leaf[i].source, letters, &found);

    /* Tre giri, dai valori più semplici. Prima le combinazioni: per ogni
     * lettera il segno + o -, oppure niente (cifra 0, 1 o 2 in base 3),
     * dalle più corte. Poi i prodotti di due esponenti, con i due segni:
     * (x^{n})^{m} = x^{n m}, e con y = x^{n} e z = y^{m} il valore per
     * z = x^{k} è k = n m. Infine le combinazioni con una costante piccola,
     * perché con a = 2^{n + 1} b il valore per b = 2^{m + 1} a è m = -n - 2.
     * I prodotti vengono prima delle costanti perché ogni valore provato
     * costa una dimostrazione intera, e le costanti sono le più numerose. */
    int combinations = 1;
    for (int i = 0; i < found; i++) combinations *= 3;
    for (int round = 0; round < 3; round++) {
        if (round == 1) {
            for (int i = 0; i < found; i++)
                for (int j = i; j < found; j++)
                    for (int minus = 0; minus < 2 && !failure && search_left > 0; minus++) {
                        Rat value = rat_mul(rat_atom(atom_var(letters[i])), rat_atom(atom_var(letters[j])));
                        if (minus) value = rat_add(rat_int(0), value, 1);
                        int tried = exponent_try(f, negated, leaf, count, own, q, body, sign, value);
                        if (tried) return tried > 0;
                    }
            continue;
        }
        for (int length = 1; length <= found; length++)
            for (int shift = round ? 1 : 0; shift <= (round ? 2 * EXPONENT_SHIFT : 0); shift++)
                for (int code = 1; code < combinations && !failure && search_left > 0; code++) {
                    Rat value = rat_int(shift % 2 ? (shift + 1) / 2 : -(shift / 2));
                    int used = 0;
                    for (int i = 0, c = code; i < found; i++, c /= 3) {
                        if (c % 3 == 0) continue;
                        value = rat_add(value, rat_atom(atom_var(letters[i])), c % 3 == 2);
                        used++;
                    }
                    if (used != length) continue;
                    int tried = exponent_try(f, negated, leaf, count, own, q, body, sign, value);
                    if (tried) return tried > 0;
                }
    }
    return 0;
}

/* 18u-3. Dimostra la disgiunzione f (negata se negated), le cui parti sono
 * leaf[0..count), cercando il valore degli "esiste" con cui comincia la
 * parte own tra i polinomi nelle variabili generiche, come descritto in
 * testa a 18u. Scrive il ragionamento e ritorna 1 se ci riesce; se ritorna
 * 0 non lascia testo né scelte.
 *
 * Il valore trovato è solo una proposta, come in 18i: l'intera disgiunzione
 * viene poi dimostrata da capo con il valore al posto della lettera. */
static int witnesses_from(Formula *f, int negated, const Leaf *leaf, int count, int own) {
    Formula *quantifier[MAX_NAMED], *body = leaf[own].source;
    const Formula *equation[MAX_EQUATIONS];
    Literal assumed[MAX_LITERALS];
    Poly given[MAX_LITERALS + MAX_NAMED];
    Mark mark = mark_here();
    if (failure) return 0;

    /* Gli "esiste" consecutivi con cui comincia la parte own: sign è il
     * segno con cui va letta la condizione che li segue. */
    int sign = leaf[own].negated, longest = 0;
    while (longest < MAX_NAMED && (body->kind == F_FORALL || body->kind == F_EXISTS) && (body->kind == F_EXISTS) != sign &&
           letter_is_free(leaf, count, own, body->variable)) {
        quantifier[longest++] = body;
        body = body->a;
    }
    if (!longest) return 0;

    /* Le ipotesi: le altre parti che sono un confronto da leggere come
     * "diversi", cioè un'uguaglianza che si può supporre. Il loro polinomio
     * lo calcola clause_polynomials(), che controlla anche le divisioni: le
     * frasi che scrive qui non servono, le riscriverà la regola 18s. Un
     * conto che non riesce vuol dire solo che così non si ricava nulla. */
    int hypotheses = 0, kept = 0;
    for (int i = 0; i < count && hypotheses < MAX_LITERALS; i++) {
        Literal literal[MAX_LITERALS];
        int found = 0;
        if (i != own && gather(leaf[i].source, leaf[i].negated, literal, &found) && found == 1 && !literal[0].equation)
            assumed[hypotheses++] = literal[0];
    }
    int usable = clause_polynomials(assumed, hypotheses);
    rollback(mark);
    if (failure || !usable) { failure = NULL; return 0; }
    for (int i = 0; i < hypotheses; i++)
        if (!poly_is_constant(assumed[i].value)) given[kept++] = assumed[i].value;

    /* Si cercano insieme i valori dei primi `names` "esiste": prima di
     * tutti, poi di meno, perché un'uguaglianza li deve contenere tutti.
     * Ogni uguaglianza richiesta da ciò che li segue può darli. */
    for (int names = longest; names > 0; names--) {
        body = quantifier[names - 1]->a;
        int equations = find_equations(body, sign, equation, 0);
        for (int e = 0; e < equations && !failure && search_left > 0; e++) {
            if (witnesses_solve(f, negated, quantifier, names, body, equation[e], given, kept)) {
                if (record_witnesses(leaf, count, own, quantifier, names, body, sign)) return 1;
                for (int j = 0; j < names; j++) witness_drop(quantifier[j]);
                rollback(mark);
                return 0;
            }
            rollback(mark);
        }
    }

    /* 18x. Un "esiste" la cui lettera sta solo negli esponenti: le
     * combinazioni degli esponenti delle altre parti. */
    return exponent_witness(f, negated, leaf, count, own, quantifier[0], quantifier[0]->a, sign);
}

/* 18u. Dimostra la disgiunzione f (negata se negated) guardandone tutte le
 * parti insieme, con i tre passi descritti in testa a 18u: uno per
 * chiamata, e il resto lo fa establish(), che torna qui finché serve.
 * Scrive il ragionamento e ritorna 1 se ci riesce; se ritorna 0 non lascia
 * testo né scelte. */
static int name_witnesses(Formula *f, int negated) {
    Leaf leaf[MAX_LEAVES];
    Mark mark = mark_here();
    int count = leaves_collect(f, negated, leaf, 0);
    if (count < 0 || failure || split_modulus) return 0;

    /* Senza variabili generiche ogni parte è una condizione su numeri, che
     * non dipende dalle altre: la disgiunzione vale solo se ne vale una da
     * sola, e questo è già stato provato da chi chiama. */
    if (!universal_count) return 0;

    /* 18u-1. Una parte che dice "per ogni v": v diventa generica. I due
     * modi di arrivarci si scrivono in modo diverso: un "per ogni" della
     * tesi introduce v, un "esiste" tra le ipotesi le dà un nome. */
    for (int i = 0; i < count; i++) {
        Formula *q = leaf[i].source;
        if ((q->kind != F_FORALL && q->kind != F_EXISTS) || (q->kind == F_FORALL) == leaf[i].negated) continue;

        /* La lettera è usata anche da un'altra parte: prima la si cambia,
         * e il passo successivo darà il nome alla copia. */
        if (!letter_is_free(leaf, count, i, q->variable)) {
            Formula *renamed = quantifier_renamed(q, leaf, count, i);
            if (!renamed) continue;
            proof_add("\\item The letters bound in $");
            put_source(q);
            proof_add("$ are used elsewhere too: we write it $");
            put_source(renamed);
            proof_add("$, which says the same.\n");
            if (establish(leaf_replaced(f, q, renamed), negated)) return 1;
            rollback(mark);
            return 0;
        }
        /* 18y-4. Il nome di un valore che l'ipotesi fissa, e che è sempre
         * positivo, varia nella parte positiva dell'insieme. L'insieme sta
         * nell'arena: la verifica del capitolo 19 lo rilegge dopo. */
        const NumberSet *named = &q->numbers;
        NumberSet positive, *kept;
        if (q->kind == F_EXISTS && positive_part(&q->numbers, &positive) && (kept = arena_alloc(sizeof *kept)) && witness_positive(q)) {
            *kept = positive;
            named = kept;
        }
        if (q->kind == F_FORALL) {
            proof_add("\\item Let $%c \\in ", q->variable);
            put_numbers(&q->numbers);
            proof_add("$.\n");
        } else {
            proof_add("\\item Suppose that $");
            put_source(q);
            proof_add("$ holds, and call $%c$ such an element of $", q->variable);
            put_numbers(named);
            proof_add("$: from here on $%c$ is fixed, and what follows is proved for every $%c \\in ", q->variable, q->variable);
            put_numbers(named);
            proof_add("$.\n");
        }
        int hypothesis = q->kind == F_EXISTS;
        if (!universal_push((Bound){q->variable, named})) return 0;
        universal_named[universal_count - 1] = (unsigned char)hypothesis;
        int holds = establish(leaf_replaced(f, q, q->a), negated);
        universal_count--;
        universal_named[universal_count] = 0;

        /* I valori annotati dentro f possono contenere v, che fuori da qui
         * non esiste: la verifica ricalcolerà f com'è scritta, e quelli
         * trovati da 18u-3 li ricontrollerà a parte (witness_records[]). */
        if (holds) { hypotheses_named += hypothesis; forget_choices(f); return 1; }
        rollback(mark);
        return 0;
    }

    /* 18u-2. Un'appartenenza o una divisibilità: la sua definizione, con
     * una lettera che qui non è usata. */
    for (int i = 0; i < count; i++) {
        Formula *q = leaf[i].source;
        int letter = 0;
        if (q->kind != F_IN && q->kind != F_DIVIDES) continue;
        for (const char *c = "qhkjtsuvwpgdcba"; *c && !letter; c++)
            if (letter_is_free(leaf, count, -1, *c)) letter = *c;

        Formula *unfolded = letter ? membership_unfolded(q, letter) : NULL;
        if (!unfolded) continue;
        proof_add("\\item By definition, $");
        put_source(q);
        proof_add("$ says that $");
        put_source(unfolded);
        proof_add("$.\n");
        if (establish(leaf_replaced(f, q, unfolded), negated)) return 1;
        rollback(mark);
        return 0;
    }

    /* 18u-3. Un "esiste": il suo valore, cercato usando le altre parti. */
    for (int i = 0; i < count && !failure; i++)
        if (witnesses_from(f, negated, leaf, count, i)) return 1;
    return 0;
}

/* =============================================================================
 * 18.6 ESTABLISH(): LA DIMOSTRAZIONE PER STRUTTURA
 * ============================================================================
 *
 * establish() mette insieme le regole dei capitoli precedenti seguendo la
 * forma della condizione: un'appartenenza (18e) o una divisibilità, un
 * confronto o una disgiunzione di confronti (18g, 18h, 18s), i connettivi
 * (18l, 18u), i quantificatori (18w, 18k, 18n, 18o, 18i, 18j), e prima di
 * establish() la regola dei divisori (18w), che le serve. Qui stanno anche
 * ciò che si dimostra di un'applicazione prima di usarla (18m) e la
 * divisione della tesi nelle sue affermazioni (prove_claims()), che sono i
 * punti di ingresso del capitolo 19.
 */

/* 18w. I DIVISORI DI UN NUMERO: UNA RICERCA FINITA
 *
 * A che cosa serve. "Nessun d diverso da 1 divide sia 2 sia 3" si scrive
 * \forall d \in \mathbb{N}\ \lnot (d \neq 1 \land d \mid 2 \land d \mid 3),
 * e parla di infiniti d; ma per tutti quelli che non dividono 2 la
 * condizione vale da sé, perché la sua parte "d divide 2" è falsa. Restano i
 * divisori di 2, che sono pochi: si provano uno per uno.
 *
 * Il teorema. Se d divide un intero c diverso da zero, allora |d| <= |c|.
 * Infatti c = q d con q intero (17n), e q non è zero perché c non lo è;
 * quindi |q| >= 1 e |c| = |q| |d| >= |d|. I divisori di c stanno dunque tra
 * -|c| e |c|, e si trovano tutti provando quei numeri: il conto è finito e
 * completo.
 *
 * La regola, per una lettera d che varia tra gli interi:
 *
 *   18w-1. "Per ogni d vale P(d)", dove P(d), letta come una disgiunzione,
 *          ha tra le sue parti "d non divide c", con c un numero diverso da
 *          zero (una volta date alle altre lettere i loro valori). Per ogni d
 *          che non divide c quella parte è vera, e con lei P(d); resta da
 *          dimostrare P(d) per i divisori di c che stanno nell'insieme di d,
 *          un caso ciascuno. È così che si legge un'ipotesi "d divide c":
 *          "d \mid c \implies Q" è "d non divide c, oppure Q".
 *   18w-2. "Esiste d con P(d)", dove P(d), letta come una congiunzione, ha
 *          tra le sue parti "d divide c": un d che va bene divide c, e si
 *          provano i divisori di c nell'insieme di d, dal più piccolo in
 *          valore assoluto. È la regola 18j con l'elenco completo dei valori
 *          possibili al posto dei numeri più semplici.
 *
 * Il valore di c deve essere un numero: un divisore di una lettera generica
 * non ha un elenco finito. Fuori dai casi di 18w-1 nulla si dimostra: lì la
 * parte "d non divide c" è vera per definizione, e i casi coprono tutti gli
 * altri d dell'insieme.
 *
 * La verifica indipendente (capitolo 19) ricalcola l'enunciato com'è
 * scritto, con d sul campione, senza usare questa regola. I valori scelti
 * per un "esiste" dentro un caso di 18w-1 cambiano da un caso all'altro, e
 * un nodo ne ricorda uno solo: perciò, riuscita la regola, vengono
 * dimenticati, e la verifica ricalcola quegli "esiste" com'è scritto. */

/* Il più grande |c| di cui 18w elenca i divisori provando i numeri da 1 a
 * |c|: oltre, il conto costerebbe troppo e la regola non si applica. */
#define DIVISOR_SCAN 100000

/* 18w. Se la condizione del quantificatore f, letta con il segno di f
 * (negata se negated), obbliga la variabile a dividere un numero diverso da
 * zero, mette quel numero in *c, la parte che lo dice in *part, e ritorna 1;
 * altrimenti ritorna 0. every dice se il quantificatore, con quel segno, è un
 * "per ogni": allora la parte è "d non divide c" di una disgiunzione (18w-1),
 * altrimenti "d divide c" di una congiunzione (18w-2). */
static int divisor_bound(Formula *f, int negated, int every, long long *c, const Formula **part) {
    Leaf leaf[MAX_LEAVES];

    /* Le parti di una congiunzione sono le negazioni delle parti della
     * disgiunzione negata: in tutti e due i casi si cerca una parte che,
     * con il suo segno, dice "d non divide c". */
    int count = leaves_collect(f->a, every ? negated : !negated, leaf, 0);
    for (int i = 0; i < count; i++) {
        const Formula *q = leaf[i].source;
        Num value;
        if (q->kind != F_DIVIDES || q->swapped == leaf[i].negated) continue;
        if (q->left->kind != N_VAR || q->left->name != f->variable || node_uses_letter(q->right, f->variable)) continue;

        /* c deve essere un intero diverso da zero: un conto che non riesce
         * vuol dire solo che questa parte non dà un elenco. */
        Rat r = eval(q->right);
        int number = !failure && rat_number(r, &value) && value.im.num == 0 && value.re.den == 1 && value.re.num != 0 &&
                     value.re.num >= -DIVISOR_SCAN && value.re.num <= DIVISOR_SCAN;
        failure = NULL;
        if (!number) continue;
        *c = value.re.num < 0 ? -value.re.num : value.re.num;
        *part = q;
        return 1;
    }
    return 0;
}

/* 18w. Dimostra il quantificatore f, negato se negated, quando la sua
 * variabile varia tra gli interi e la sua condizione la obbliga a dividere
 * un numero diverso da zero (divisor_bound()), con i casi descritti in testa
 * al paragrafo. Scrive il ragionamento e ritorna 1 se ci riesce; 0 se la
 * regola non si applica; -1 se si applica ma un caso non riesce. Se non
 * ritorna 1 non lascia testo né scelte.
 *
 * Perché il -1. I divisori sono tutti i valori che contano: un "esiste" il
 * cui valore non si trova tra loro non si trova altrove, perché un valore
 * scritto con le variabili generiche che fosse sempre un divisore di c
 * sarebbe un polinomio con un numero finito di valori su insiemi infiniti,
 * cioè una costante, e le costanti sono già state provate. Lo stesso per un
 * "per ogni" con un caso che non riesce. Chi chiama può quindi smettere di
 * cercare: provare le altre regole costava migliaia di passi, e la ricerca
 * di un controesempio a una proprietà transitiva si fermava prima di
 * arrivarci. */
static int by_divisors(Formula *f, int negated) {
    long long c, divisor[2 * MAX_CASES];
    const Formula *part;
    int every = (f->kind == F_FORALL) != negated, count = 0;
    Mark mark = mark_here();
    if (!f->numbers.integers || failure || !divisor_bound(f, negated, every, &c, &part)) return 0;

    /* I divisori di c nell'insieme della variabile, dal più piccolo in
     * valore assoluto, prima il positivo. Il controllo del passo ricalcola
     * che ognuno divida davvero c, con la divisione di number_divides(). */
    for (long long d = 1; d <= c; d++) {
        if (c % d != 0) continue;
        for (long long v = d; v >= -d; v -= 2 * d) {
            if (!numbers_contain(&f->numbers, frac_int(v))) continue;
            if (count == 2 * MAX_CASES) return 0;
            if (!number_divides(num_int(v), num_int(c))) { unjustified_steps++; return 0; }
            divisor[count++] = v;
        }
    }

    /* 18w-2. "Esiste": i divisori, uno dopo l'altro, come in 18j. */
    if (!every) {
        for (int i = 0; i < count && !failure; i++) {
            proof_add("\\item Since $");
            put_source(part);
            proof_add("$ is required, $%c$ is a divisor of $%lld$. Take $%c = %lld$, an element of $", f->variable, c, f->variable, divisor[i]);
            put_numbers(&f->numbers);
            proof_add("$.\n");
            choose(f->variable, frac_int(divisor[i]));
            env_push(f->variable, rat_int(divisor[i]));
            int holds = establish(f->a, negated);
            env_pop();
            if (holds) { witness_keep(f, rat_int(divisor[i])); return 1; }
            rollback(mark);
        }
        return -1;
    }

    /* 18w-1. "Per ogni": fuori dai divisori la parte "d non divide c" vale;
     * poi un caso per divisore. */
    proof_add("\\item Let $%c \\in ", f->variable);
    put_numbers(&f->numbers);
    proof_add("$. If $");
    put_source(part);
    proof_add("$ fails, the condition holds. Otherwise $%c$ divides $%lld$: then $%lld = q %c$ with $q$ a nonzero integer, so "
              "$|%c| \\le %lld$, and the divisors of $%lld$ in $", f->variable, c, c, f->variable, f->variable, c, c);
    put_numbers(&f->numbers);
    proof_add(count ? "$ are " : "$: there are none, so the condition always holds.\n");
    for (int i = 0; i < count; i++) proof_add("%s$%lld$%s", i ? (i + 1 == count ? " and " : ", ") : "", divisor[i], i + 1 == count ? ".\n" : "");
    for (int i = 0; i < count; i++) {
        proof_add("\\item \\emph{Case $%c = %lld$}.\n\\begin{itemize}\n", f->variable, divisor[i]);
        env_push(f->variable, rat_int(divisor[i]));
        int holds = establish(f->a, negated);
        env_pop();
        proof_add("\\end{itemize}\n");
        if (!holds) { rollback(mark); return -1; }
    }

    /* Le scelte fatte dentro i casi cambiano da un caso all'altro: non sono
     * un controesempio da riportare, e i nodi non le ricordano (vedi la
     * testa del paragrafo). */
    if (chosen_count > mark.chosen) chosen_by_cases = 1;
    forget_choices(f->a);
    return 1;
}

/* Il lavoro di establish(), che ne descrive il contratto, una volta
 * stabiliti i casi delle applicazioni definite per casi. */
static int establish_rules(Formula *f, int negated) {
    Mark mark = mark_here();
    Literal literal[MAX_LITERALS];
    Junction j;
    int count = 0;
    if (failure || search_left <= 0) return 0;
    search_left--;
    if (f->kind == F_NOT) return establish(f->a, !negated);

    /* 18e. Appartenenza a un insieme numerico (17k): l'espressione deve
     * avere un valore, e il valore stare nell'insieme. Che non ci stia si sa
     * dire solo di un numero, guardandolo. */
    if (f->kind == F_IN) {
        Num number;
        int inside = f->swapped == negated;
        proof_add("\\item $");
        put_source(f);
        proof_add("$ %s.", negated ? "fails" : "holds");
        int proved = term_defined(f->left);
        Rat value = eval(f->left);
        if (proved && inside) proved = always_in(value, &f->numbers);
        else if (proved) proved = !failure && rat_number(value, &number) && number.im.num == 0 && !numbers_contain(&f->numbers, number.re);
        if (proved && !inside) {
            proof_add(" Indeed $");
            put_frac(number.re);
            proof_add("$ is not in $");
            put_numbers(&f->numbers);
            proof_add("$.");
        }
        if (proved && !failure) { proof_add("\n"); return 1; }
        rollback(mark);
        return 0;
    }

    /* Divisibilità (17n): "u divide v" si dimostra, per ogni valore delle
     * variabili, quando il quoziente v/u è un polinomio che vale sempre un
     * intero (18d): allora v è u per quell'intero, anche dove u è zero. Che
     * u non divida v si sa dire solo di due numeri. */
    if (f->kind == F_DIVIDES) {
        Poly num, den;
        Num divisor, dividend;
        int divides = f->swapped == negated;
        proof_add("\\item $");
        put_source(f);
        proof_add("$ %s.", negated ? "fails" : "holds");
        int proved = term_defined(f->left) && term_defined(f->right);
        Rat u = eval(f->left), v = eval(f->right);
        if (proved && !failure && rat_number(u, &divisor) && rat_number(v, &dividend)) {
            proved = number_divides(divisor, dividend) == divides;
            if (proved) proof_add(" Computed with the two numbers.");
        } else if (proved && !failure && divides && u.num.count != 0) {
            proof_add(" The quotient is $");
            proved = rat_polynomials(rat_div(v, u), &num, &den) && poly_is_one(den);
            if (proved) { put_poly(num); proof_add("$."); proved = always_integer(num); }
        } else {
            proved = 0;
        }
        if (proved && !failure) { proof_add("\n"); return 1; }
        rollback(mark);
        return 0;
    }

    /* 18g, 18h. Un confronto, o una disgiunzione di confronti. */
    if (gather(f, negated, literal, &count)) {
        /* I polinomi che prove_clause() calcola servono solo a lei: resta il
         * testo che ha scritto. La memoria che ha preso si può ridare, a
         * meno che non sia nata la base di una potenza o l'argomento di
         * un'arcotangente, che restano nelle tabelle degli atomi. Senza
         * questo passo una ricerca lunga riempie l'arena molto prima di
         * finire i tentativi. */
        size_t before = arena_used;
        int polys = base_poly_count, atans = atan_count;
        proof_add("\\item");
        int proved = prove_clause(literal, count);

        /* 18s. Dove 18h non arriva: la tesi come combinazione delle
         * ipotesi. Il testo del primo tentativo si cancella. */
        if (!proved && !failure) {
            rollback(mark);
            proof_add("\\item");
            proved = prove_combination(literal, count);
        }

        /* 18z. Dove non arriva nemmeno 18s: un'ipotesi dà il valore di una
         * variabile, che si sostituisce nel resto. */
        if (!proved && !failure) {
            rollback(mark);
            proof_add("\\item");
            proved = prove_by_substitution(literal, count, MAX_SUBSTITUTIONS);
        }
        /* 18v-2. Un confronto che vale tranne in un punto di una variabile:
         * quel punto, e il resto, sono due casi da distinguere. */
        if (!proved && !failure)
            for (int i = 0; i < count && !split_pending; i++) split_at_zero((Rat){literal[i].value, poly_const(num_int(1))});
        if (polys == base_poly_count && atans == atan_count && failure != OUT_OF_MEMORY) arena_used = before;
        if (proved) { proof_add("\n"); return 1; }
        rollback(mark);

        /* Una disgiunzione di più confronti che prove_clause() non sa
         * trattare insieme può ancora valere per una sola delle sue parti:
         * si prosegue con la regola dei connettivi. Serve solo se tra le
         * parti c'è un "diversi": un "uguali" che vale da solo è già stato
         * riconosciuto (18g), e provarli di nuovo uno per uno consumerebbe i
         * tentativi di chi sta intorno, come la regola 18o. */
        int different = 0;
        for (int i = 0; i < count; i++) different += !literal[i].equation;
        if (count < 2 || !different || failure) return 0;
    }

    /* 18l. Congiunzione: tutte e due le parti. Disgiunzione che non è fatta
     * di soli confronti: una parte basta, e si prova prima l'una poi l'altra. */
    if (junction(f, negated, &j)) {
        if (j.conjunction) {
            if (establish(j.x, j.nx) && establish(j.y, j.ny)) return 1;
            rollback(mark);
            return 0;
        }
        for (int side = 0; side < 2; side++) {
            Formula *part = side ? j.y : j.x;
            int sign = side ? j.ny : j.nx;
            proof_add("\\item It is enough to show that $");
            put_source(part);
            proof_add("$ %s.\n", sign ? "fails" : "holds");
            if (establish(part, sign)) return 1;
            rollback(mark);
        }

        /* 18u. Nessuna delle due parti vale da sola: si guardano tutte
         * insieme, dando un nome a ciò che le ipotesi dicono esistere. I
         * tentativi di questa regola sono contati a parte, come quelli di
         * 18o, e sono pochi: quando non porta a nulla non deve consumare la
         * ricerca di chi sta intorno, che può arrivare qui migliaia di
         * volte, una per ogni numero provato da 18j. Prima di questo conto
         * due enunciati falsi, che venivano smentiti, restavano senza
         * risposta; sono nei test. */
        int outside = search_set_aside();
        int named = name_witnesses(f, negated);
        search_left += outside;
        if (named) return 1;

        /* 18l. Altrimenti, se è "A implica B e C"
         * si dimostrano "A implica B" e "A implica C", che insieme dicono lo
         * stesso: così l'ipotesi A resta accanto a ogni pezzo della tesi,
         * dove le regole 18h e 18s la sanno usare. I due nodi provvisori
         * servono solo a passare le due implicazioni a questa funzione. */
        if (f->kind == F_IMPLIES && !negated && f->b->kind == F_AND) {
            Formula first = *f, second = *f;
            first.b = f->b->a;
            second.b = f->b->b;
            if (establish(&first, 0) && establish(&second, 0)) return 1;
            rollback(mark);
        }
        return 0;
    }

    /* 18l. Equivalenza: le due implicazioni. La sua negazione: una delle due
     * implicazioni non vale. I due nodi provvisori servono solo a passare le
     * implicazioni a questa stessa funzione. */
    if (f->kind == F_IFF) {
        Formula forward = *f, backward = *f;
        forward.kind = backward.kind = F_IMPLIES;
        backward.a = f->b;
        backward.b = f->a;
        if (negated) {
            if (establish(&forward, 1) || establish(&backward, 1)) return 1;
        } else {
            proof_add("\\item ($\\Rightarrow$)\n");
            if (establish(&forward, 0)) {
                proof_add("\\item ($\\Leftarrow$)\n");
                if (establish(&backward, 0)) return 1;
            }
        }
        rollback(mark);
        return 0;
    }
    if (f->kind != F_FORALL && f->kind != F_EXISTS) return 0;

    /* 18w. Una variabile intera che deve dividere un numero: i valori che
     * contano sono i divisori, finiti. Si prova prima delle altre regole,
     * perché quando si applica decide in pochi passi ciò che quelle
     * cercherebbero a lungo. Quando si applica e non riesce, le altre non
     * troverebbero di più (vedi by_divisors()). */
    int divisors = by_divisors(f, negated);
    if (divisors) return divisors > 0;

    /* 18k. "Per ogni": variabili generiche. Più quantificatori di seguito
     * sullo stesso insieme si introducono insieme, come in "siano a, b". */
    if ((f->kind == F_FORALL) != negated) {
        Formula *last = f;
        int outer = universal_count;
        f->modulus = 0;

        /* I legami crescono con la dimostrazione, inclusi i testimoni delle
         * ipotesi; non si assume che basti la profondita del testo letto. */
        proof_add("\\item Let $%c", f->variable);
        if (!universal_push((Bound){f->variable, &f->numbers})) return 0;
        while (last->a->kind == f->kind && numbers_equal(&last->a->numbers, &f->numbers)) {
            last = last->a;
            proof_add(", %c", last->variable);
            if (!universal_push((Bound){last->variable, &last->numbers})) { universal_count = outer; return 0; }
        }
        proof_add(" \\in ");
        put_numbers(&f->numbers);
        proof_add("$");

        /* 17t-2. Le componenti di una coppia: si dice di quale. */
        for (const Formula *g = f, *said = NULL; ; g = g->a) {
            if (g->pair) proof_add(g->complex ? "%s$%c = %c + i%c$" : "%s$%c = (%c, %c)$", said ? " and " : ", with ", g->pair, g->variable, g->a->variable);
            if (g->pair) said = g;
            if (g == last) break;
        }
        proof_add(".\n");
        int holds = establish_in_regions(last->a, negated, outer);
        universal_count = outer;
        if (holds) return 1;

        /* Le due regole che seguono valgono per una variabile sola, intera.
         * Il tentativo diretto può essersi fermato su un conto che con una
         * lettera non si fa, come una somma fino a n: non è un errore
         * dell'enunciato. */
        const NumberSet *set = &f->numbers;
        if (last != f || !set->integers || set->holes || search_left <= 0) { rollback(mark); return 0; }
        failure = NULL;

        /* 18n. Per induzione: un'uguaglianza, su una semiretta di interi,
         * senza altre variabili in gioco. */
        const Formula *body = f->a;
        int sign = negated;
        while (body->kind == F_NOT) { body = body->a; sign = !sign; }
        if (set->bounded && outer == 0 && env_count == 0 && (body->kind == F_EQUAL || body->kind == F_DISTINCT) &&
            (body->kind == F_EQUAL) != sign) {
            rollback(mark);
            if (by_induction(f, body)) return 1;
        }

        /* 18o. Per casi sul resto di una divisione. */
        if (by_remainders(f, negated)) return 1;
        failure = NULL;
        rollback(mark);
        return 0;
    }

    /* 18i. "Esiste": prima risolvendo un'equazione. Un valore scelto in un
     * tentativo precedente, per questo stesso caso, non conta più. */
    witness_drop(f);
    if (solve_for(f, negated)) return 1;
    rollback(mark);

    /* 18u-3. Poi cercando il valore tra i polinomi nelle variabili
     * generiche: qui non ci sono ipotesi, e l'equazione deve diventare
     * un'identità. Trova p = m + n per m a + n a = p a, dove 18i si ferma
     * perché dividerebbe per a, che può essere zero. Anche questi tentativi
     * sono contati a parte, come quelli di 18o. */
    Leaf alone = {f, negated};
    int outside = search_set_aside();
    int polynomial = witnesses_from(f, negated, &alone, 1, 0);
    search_left += outside;
    if (polynomial) return 1;

    /* 18j. Poi provando i numeri più semplici dell'insieme. Il valore è un
     * numero fisso anche se ci sono variabili generiche: va bene quando lo
     * stesso numero serve per tutti i loro valori. */
    Frac sample[SAMPLE_SIZE];
    numbers_sample(&f->numbers, sample, SAMPLE_SIZE);
    for (int i = 0; i < SAMPLE_SIZE && !failure; i++) {
        proof_add("\\item Take $%c = ", f->variable);
        put_frac(sample[i]);
        if (f->pair) proof_add(f->complex ? "$ in $%c = %c + i%c" : "$ in $%c = (%c, %c)", f->pair, f->variable, f->a->variable);
        proof_add("$, an element of $");
        put_numbers(&f->numbers);
        proof_add("$.\n");
        choose(f->variable, sample[i]);
        env_push(f->variable, rat_frac(sample[i]));
        int holds = establish(f->a, negated);
        env_pop();
        if (holds) { witness_keep(f, rat_frac(sample[i])); return 1; }
        rollback(mark);
    }

    /* 18z. Poi le espressioni di primo grado più semplici nelle variabili
     * generiche: "per ogni m c'è un x che m non è un multiplo di x" non ha
     * un x fisso, ma x = 2m va bene per ogni m. Il valore va dimostrato
     * nell'insieme e la condizione con quel valore, come ogni altro: chi
     * cerca propone, la dimostrazione decide. Una variabile intera dà valori
     * interi, una razionale razionali. È anche la regola che prima si
     * chiamava 18v-9 (v, v + 1, v - 1), che questo elenco contiene: "esiste
     * y per cui nessun x dà f(x) = y", con f(x) = a x + b e a, b parametri,
     * vuole y = b + 1. */
    static const int line[][2] = {{1, 0}, {1, 1}, {2, 0}, {1, -1}, {2, 1}, {3, 0}};
    const Formula *equation[MAX_EQUATIONS];

    /* Solo quando nessuna uguaglianza dà il valore, e solo con le variabili
     * di cui la condizione parla, anche attraverso la regola di
     * un'applicazione che calcola (b, nella regola di f): dove 18i ha già
     * un'equazione da risolvere questi tentativi non aggiungono nulla, e
     * dentro più "esiste" annidati costavano migliaia di passi. */
    if (find_equations(f->a, negated, equation, 0)) return 0;
    for (int v = 0; v < universal_count && !failure && search_left > 0; v++) {
        if (env_lookup(universal[v].name) || (f->numbers.integers && !universal[v].numbers->integers) ||
            !formula_mentions(f->a, universal[v].name)) continue;
        for (size_t k = 0; k < sizeof line / sizeof *line && !failure && search_left > 0; k++) {
            Rat value = rat_add(rat_mul(rat_int(line[k][0]), rat_atom(atom_var(universal[v].name))), rat_int(line[k][1]), 0);
            proof_add("\\item Take $%c = ", f->variable);
            put_poly(value.num);
            proof_add("$. It has to be an element of $");
            put_numbers(&f->numbers);
            proof_add("$.");
            if (!always_in(value, &f->numbers)) { rollback(mark); continue; }
            proof_add("\n");
            env_push(f->variable, value);
            int holds = establish(f->a, negated);
            env_pop();
            if (holds) { witness_keep(f, value); return 1; }
            rollback(mark);
        }
    }
    return 0;
}

/* Ritorna 1 se la condizione f contiene un quantificatore. */
static int formula_quantifies(const Formula *f) {
    return f && (f->kind == F_FORALL || f->kind == F_EXISTS || f->kind == F_SOLVE || formula_quantifies(f->a) || formula_quantifies(f->b));
}

/* Ritorna 1 se l'enunciato in corso ha un'applicazione definita per casi. */
static int cases_declared(void) {
    for (int i = 0; i < map_count; i++)
        if (maps[i].cases) return 1;
    return 0;
}

/* Dimostra la condizione f, o la sua negazione se negated, per ogni valore
 * delle variabili generiche e con i valori dati alle altre. Scrive il
 * ragionamento come una serie di \item e ritorna 1 se ci riesce; se ritorna 0
 * non lascia testo né scelte. Le regole sono descritte in testa al capitolo
 * 18.
 *
 * Una condizione senza quantificatori in cui compare un'applicazione
 * definita per casi comincia con la scelta dei casi (18v-1), che vale finché
 * la si dimostra: dopo, le scelte si tolgono, perché parlano di quei valori
 * delle variabili. Un conto che si è fermato su un caso non stabilito non è
 * un errore dell'enunciato: lo si dimentica, e la richiesta di distinguere
 * (18v-2) resta a chi la raccoglie. */
static int establish(Formula *f, int negated) {
    Mark mark = mark_here();
    int choices = case_choice_count;
    int holds = (!cases_declared() || formula_quantifies(f) || cases_decided(f)) && establish_rules(f, negated);
    case_choice_count = choices;
    if (failure == CASE_UNDECIDED) failure = NULL;
    if (!holds) rollback(mark);
    return holds;
}

/* 18v-6. Dimostra, in uno dei casi di una distinzione sulla variabile della
 * regola di map (o senza distinzioni), che la definizione per casi dà un
 * solo valore e che sta nel codominio: un caso vale, il suo valore è
 * definito e sta nel codominio, e ognuno degli altri o non vale o dà lo
 * stesso valore. Scrive il ragionamento e ritorna 1 se ci riesce; se un caso
 * non si sa decidere chiede una distinzione (18v-2).
 *
 * Che nessun caso valga in una parte del dominio non si dimostra: i casi
 * allora non coprono il dominio, e la verifica sul campione lo trova. */
static int cases_hold_here(void *data) {
    const Map *map = data;
    const Rat *bound = env_lookup(map->parameter);
    Rat t = bound ? *bound : rat_atom(atom_var(map->parameter));
    int first = -1, holds = 1;
    env_push(map->parameter, t);

    /* Il primo caso che vale, con il suo valore. */
    for (int i = 0; i < map->cases && first < 0 && !failure; i++) {
        size_t start = proof_length;
        proof_add("\\item Case %d of the definition applies:", i + 1);
        if (case_proved(map->piece[i].when, 0)) first = i;
        else proof_cut(start);
        if (failure == CASE_UNDECIDED) failure = NULL;
    }
    if (first < 0) holds = 0;
    Rat value = holds ? eval(map->piece[first].value) : rat_int(0);
    if (holds) {
        proof_add(" So $%c(", map->name);
        put_fraction(t);
        proof_add(") = ");
        put_fraction(value);
        proof_add("$.");
        holds = term_defined(map->piece[first].value) && always_in(value, &map->codomain);
        proof_add("\n");
    }

    /* Gli altri: non valgono, o danno lo stesso valore. */
    for (int j = 0; j < map->cases && holds && !failure; j++) {
        if (j == first) continue;
        Rat other = eval(map->piece[j].value);
        Rat gap = rat_add(other, value, 1);
        if (!failure && gap.num.count == 0) {
            proof_add("\\item Case %d of the definition gives the same value.\n", j + 1);
            continue;
        }
        if (failure) failure = NULL;
        size_t start = proof_length;
        proof_add("\\item Case %d of the definition does not apply:", j + 1);
        if (case_proved(map->piece[j].when, 1)) { proof_add("\n"); continue; }
        proof_cut(start);
        holds = 0;
    }

    /* Un caso che non si sa decidere: si chiede che cosa distinguere. */
    if (!holds && !failure)
        for (int i = 0; i < map->cases && !split_pending; i++) split_from_condition(map->piece[i].when);
    env_pop();
    return holds && !failure;
}

/* 18v-6. Dimostra che la definizione per casi di map definisce
 * un'applicazione dal dominio al codominio: per ogni x del dominio i casi
 * che valgono danno uno stesso valore, definito e nel codominio. Scrive il
 * ragionamento come un \item e ritorna 1 se ci riesce. È il seguito di 18m
 * per le definizioni per casi. */
static int cases_define(const Map *map) {
    int outer = universal_count;
    proof_add("\\item \\emph{The definition by cases defines a map from $");
    put_numbers(&map->domain);
    proof_add("$ to $");
    put_numbers(&map->codomain);
    proof_add("$.} Let $%c \\in ", map->parameter);
    put_numbers(&map->domain);
    proof_add("$.\n\\begin{itemize}\n");
    if (!universal_push((Bound){map->parameter, &map->domain})) return 0;
    int defined = in_regions(cases_hold_here, (void *)map, NULL, outer, 0);
    universal_count = outer;
    proof_add("\\end{itemize}\n");
    return defined && !failure;
}

/* 18m. Dimostra che la regola di map definisce un'applicazione dal dominio al
 * codominio: per ogni x del dominio il valore esiste, perché nessun divisore
 * si annulla, e appartiene al codominio. Scrive il ragionamento come un \item
 * e ritorna 1 se ci riesce.
 *
 * Senza questo passo le ipotesi dell'enunciato potrebbero non essere
 * soddisfatte da nessuna applicazione, e allora qualunque tesi ne seguirebbe:
 * un verdetto FALSO sarebbe sbagliato, e uno DIMOSTRATO non direbbe nulla. */
int map_defined(const Map *map) {
    Poly num, den;
    if (map->cases) return cases_define(map);
    proof_add("\\item \\emph{The %srule defines %s from $", map->partner ? "first component of the " : map->component ? "second component of the " : "",
              map->binary ? "an operation" : "a map");
    put_numbers(&map->domain);
    if (map->binary) { proof_add(" \\times "); put_numbers(&map->second); }
    proof_add("$ to $");
    put_numbers(&map->codomain);
    proof_add("$.} Let $%c \\in ", map->parameter);
    put_numbers(&map->domain);
    if (map->binary) { proof_add("$ and $%c \\in ", map->parameter2); put_numbers(&map->second); }
    proof_add("$.");

    /* Le variabili della regola sono generiche nel dominio, dopo i
     * parametri dell'enunciato (17s). */
    int outer = universal_count;
    if (!universal_push((Bound){map->parameter, &map->domain})) return 0;
    if (map->binary && !universal_push((Bound){map->parameter2, &map->second})) { universal_count = outer; return 0; }
    int defined = term_defined(map->body);
    Rat value = eval(map->body);
    if (defined && rat_polynomials(value, &num, &den)) {
        proof_add(" The value is $");
        put_ratio(num, den);
        proof_add("$.");
        defined = always_in(value, &map->codomain);
    } else {
        defined = 0;
    }
    universal_count = outer;
    proof_add("\n");
    return defined && !failure;
}

/* Dimostra la tesi f dividendola nelle affermazioni di cui è la congiunzione:
 * ognuna ha il suo titolo, con il testo dell'enunciato, e sotto i suoi passi.
 * Ritorna 1 se le dimostra tutte. */
int prove_claims(Formula *f) {
    if (f->kind == F_AND) return prove_claims(f->a) && prove_claims(f->b);
    proof_add("\\item \\emph{Claim:} $");
    put_source(f);
    proof_add("$.\n\\begin{itemize}\n");
    int holds = establish_in_regions(f, 0, 0);
    proof_add("\\end{itemize}\n");
    return holds;
}

/* =============================================================================
 * 18.7 SOLE CONGRUENZE: TUTTI I RESTI (18r)
 * ============================================================================
 *
 * "5x è congruo a 8 modulo 36 se e solo se x è congruo a 16 modulo 36" parla
 * di tutti gli interi, ma che un intero x soddisfi una congruenza dipende
 * solo dal resto di x nella divisione per il modulo: i resti sono 36, e si
 * provano tutti. Questa regola decide così, vero o falso, ogni enunciato
 * fatto soltanto di condizioni di questo tipo.
 *
 * Il linguaggio. Un enunciato chiuso costruito con connettivi e
 * quantificatori a partire da condizioni "m divide P", dove m è un numero e P
 * un polinomio a coefficienti razionali nelle variabili dell'enunciato. Le
 * variabili variano in insiemi di interi. La condizione si può scrivere in
 * quattro modi: m \mid P, P \equiv Q \pmod{m}, P \in \mathbb{Z}, oppure
 * \exists k \in \mathbb{Z} (L = R) con un'uguaglianza di primo grado in k,
 * a coefficiente numerico: c k + P = 0 dice che -P/c è un intero
 * (names_a_multiple()). In tutti i casi la condizione è "il polinomio Q è
 * un intero", con Q = P/m, P oppure -P/c; scritto Q = N/D con N a
 * coefficienti interi e D il minimo comune
 * multiplo dei denominatori, è "D divide N". Così anche x/2 \equiv 1
 * \pmod{3}, che ha un coefficiente frazionario, riceve il modulo giusto: 6.
 *
 * Perché basta provare i resti. Sia M un multiplo comune dei moduli D.
 *
 *   1. Se x e x' sono interi con lo stesso resto modulo M, cioè x' = x + M t,
 *      allora N(x') - N(x) è multiplo di M per ogni polinomio N a
 *      coefficienti interi: lo è (x + M t)^j - x^j, per la formula del
 *      binomio, e somme e prodotti per interi lo conservano. Vale lo stesso
 *      con più variabili, cambiandone una alla volta. Quindi "D divide N"
 *      vale per x se e solo se vale per x', perché D divide M.
 *   2. Per induzione sulla struttura, la verità di ogni parte dell'enunciato
 *      dipende solo dai resti modulo M delle variabili libere in quella
 *      parte: i connettivi non aggiungono nulla, e per un quantificatore
 *      basta il punto 3.
 *   3. Un insieme di interi della grammatica (tutti gli interi da un certo
 *      punto in su, o tutti, meno un numero finito di punti) contiene interi
 *      di ogni resto modulo M, perché ogni classe di resto è infinita e non
 *      limitata dall'alto. Quindi "per ogni x in A vale P(x)" equivale a "per
 *      ogni resto r tra 0 e M - 1 vale P(r)", e così "esiste".
 *
 * Il conto è finito e completo: M alla d casi, con d quantificatori uno
 * dentro l'altro. Per questo la regola risponde anche FALSO, e quando la
 * domanda è \{x \in \mathbb{Z} \mid c\} elenca i resti buoni.
 *
 * Ciò che non è di questa forma (un'uguaglianza tra variabili, una variabile
 * razionale, un modulo che è una lettera) non la riguarda: lì la verità non
 * è periodica, e l'enunciato resta alle altre regole.
 *
 * La verifica indipendente è nel capitolo 19: lo stesso enunciato viene
 * ricalcolato sugli interi veri di un periodo, con i conti esatti del
 * capitolo 11 al posto dell'aritmetica dei resti. Lì stanno anche il
 * verdetto e le soluzioni (decide_by_residues(), solve_by_residues()), che
 * di quella verifica hanno bisogno.
 */

/* Le condizioni dell'enunciato in corso, e un multiplo comune dei loro
 * moduli: il periodo M. */
Congruence congruences[MAX_CONGRUENCES];
int congruence_count;
long long residue_period;

/* Le variabili intere visibili nel punto dell'enunciato che si sta
 * esaminando, dalla più esterna, e il resto dato a ciascuna. */
int *residue_name;
long long *residue_value;
static size_t residue_name_capacity, residue_value_capacity;
int residue_count;

/* Ritorna 1 se f è un'uguaglianza o una disgiunzione di uguaglianze. */
static int equations_only(const Formula *f) {
    if (f->kind == F_OR) return equations_only(f->a) && equations_only(f->b);
    return f->kind == F_EQUAL;
}

/* Ritorna 1 se f ha la forma "esiste k in Z tale che L = R (oppure L' = R',
 * ...)": è il modo di scrivere "è un multiplo di" senza il simbolo. Che le
 * uguaglianze siano davvero di primo grado in k lo controlla chi le legge. */
int names_a_multiple(const Formula *f) {
    return f->kind == F_EXISTS && f->numbers.integers && !f->numbers.bounded && !f->numbers.holes && equations_only(f->a);
}

/* Registra in congruences[] la condizione "quotient è un numero intero",
 * scritta dal nodo source. Ritorna 1 se ci riesce: quotient deve essere un
 * polinomio a coefficienti razionali nelle variabili intere in vista.
 *
 * Il modulo è il minimo comune multiplo D dei denominatori dei coefficienti,
 * e il dividendo è D per quotient: vedi "Il linguaggio" in testa a 18r. */
static int congruence_add(const Formula *source, Rat quotient) {
    Poly num, den;
    if (failure || congruence_count == MAX_CONGRUENCES || !rat_polynomials(quotient, &num, &den)) return 0;
    if (!poly_is_constant(den) || den.count == 0) return 0;
    Poly q = poly_mul(num, poly_const(num_inv(den.term[0].coef)));

    /* Il modulo; e ogni lettera deve essere una variabile intera in vista. */
    long long modulus = 1;
    for (int i = 0; i < q.count; i++) {
        const Term *t = &q.term[i];
        __int128 multiple = (__int128)modulus / gcd128(modulus, t->coef.re.den) * t->coef.re.den;
        if (t->coef.im.num != 0 || multiple > MAX_PERIOD) return 0;
        modulus = (long long)multiple;
        for (int k = 0; k < t->mono.count; k++) {
            int known = 0;
            for (int v = 0; v < residue_count; v++) known = known || atom_var(residue_name[v]) == t->mono.factor[k].atom;
            if (!known) return 0;
        }
    }
    congruences[congruence_count++] = (Congruence){source, modulus, poly_mul(q, poly_const(num_int(modulus)))};
    return !failure;
}

/* Registra le uguaglianze di e, che stanno sotto "esiste k in Z" con k di
 * nome name: ognuna deve essere c k + P = 0 con c un numero non nullo, e
 * dice che -P/c è un intero. Ritorna 1 se sono tutte di questa forma. */
static int multiples_read(const Formula *e, int name) {
    Poly num, den, part[2];
    if (e->kind == F_OR) return multiples_read(e->a, name) && multiples_read(e->b, name);
    Rat gap = rat_add(eval(e->left), eval(e->right), 1);
    if (failure || !rat_polynomials(gap, &num, &den) || !poly_is_constant(den)) return 0;
    if (poly_split(num, atom_var(name), part, 1) != 1 || !poly_is_constant(part[1])) return 0;
    return congruence_add(e, rat_make(poly_negate(part[0]), part[1]));
}

/* Ritorna 1 se la condizione f appartiene al linguaggio di 18r, e allora ne
 * registra le condizioni in congruences[]. *deepest, che chi chiama mette a
 * zero, riceve il massimo numero di variabili in vista insieme, cioè quanti
 * quantificatori sui resti stanno uno dentro l'altro. Nessuna variabile deve
 * essere legata: i conti si fanno sulle lettere. */
int congruences_read(const Formula *f, int *deepest) {
    Num divisor;
    if (failure) return 0;
    switch (f->kind) {
    case F_NOT:
        return congruences_read(f->a, deepest);
    case F_AND: case F_OR: case F_IMPLIES: case F_IFF:
        return congruences_read(f->a, deepest) && congruences_read(f->b, deepest);
    case F_DIVIDES:
        return rat_number(eval(f->left), &divisor) && !num_is_zero(divisor) && congruence_add(f, rat_div(eval(f->right), eval(f->left)));
    case F_IN:
        /* Solo "è un intero": stare in un insieme con un estremo o con dei
         * punti tolti non dipende dal resto. */
        return f->numbers.integers && !f->numbers.bounded && !f->numbers.holes && congruence_add(f, eval(f->left));
    case F_FORALL: case F_EXISTS: case F_SOLVE: {
        if (names_a_multiple(f)) return multiples_read(f->a, f->variable);
        if (!f->numbers.integers ||
            !work_reserve((void **)&residue_name, &residue_name_capacity, (size_t)residue_count + 1, sizeof *residue_name) ||
            !work_reserve((void **)&residue_value, &residue_value_capacity, (size_t)residue_count + 1, sizeof *residue_value)) return 0;
        residue_name[residue_count++] = f->variable;
        if (residue_count > *deepest) *deepest = residue_count;
        int known = congruences_read(f->a, deepest);
        residue_count--;
        return known;
    }
    default:
        return 0;
    }
}

/* Ritorna 1 se, con i resti dati alle variabili in vista, vale la condizione
 * registrata per il nodo source: il dividendo è multiplo del modulo. I conti
 * si fanno modulo il modulo, quindi con numeri piccoli. */
static int congruence_holds(const Formula *source) {
    const Congruence *c = congruences;
    while (c->source != source) c++;
    __int128 total = 0;
    for (int i = 0; i < c->dividend.count; i++) {
        const Term *t = &c->dividend.term[i];
        __int128 product = t->coef.re.num % c->modulus;
        for (int k = 0; k < t->mono.count; k++) {
            long long value = 0;
            for (int v = 0; v < residue_count; v++)
                if (atom_var(residue_name[v]) == t->mono.factor[k].atom) value = residue_value[v] % c->modulus;
            for (long long e = 0; e < t->mono.factor[k].exp.num; e++) product = product * value % c->modulus;
        }
        total = (total + product) % c->modulus;
    }
    return total == 0;
}

/* 18r. Ritorna 1 se la condizione f, che congruences_read() ha accettato, è
 * vera con i resti dati alle variabili in vista. Un quantificatore prova
 * tutti i resti della sua variabile, da 0 a residue_period - 1. */
int residue_holds(const Formula *f) {
    switch (f->kind) {
    case F_NOT:     return !residue_holds(f->a);
    case F_AND:     return residue_holds(f->a) && residue_holds(f->b);
    case F_OR:      return residue_holds(f->a) || residue_holds(f->b);
    case F_IMPLIES: return !residue_holds(f->a) || residue_holds(f->b);
    case F_IFF:     return residue_holds(f->a) == residue_holds(f->b);
    case F_DIVIDES: case F_IN:
        return congruence_holds(f) != f->swapped;
    case F_EQUAL:   return congruence_holds(f);
    default:        break;
    }

    /* "Esiste k con L = R": una delle uguaglianze, cioè delle condizioni. */
    if (names_a_multiple(f)) return residue_holds(f->a);

    /* Un quantificatore su una variabile intera. */
    int every = f->kind == F_FORALL, holds = every;
    residue_name[residue_count++] = f->variable;
    for (long long r = 0; r < residue_period && holds == every; r++) {
        residue_value[residue_count - 1] = r;
        holds = residue_holds(f->a);
    }
    residue_count--;
    return holds;
}
