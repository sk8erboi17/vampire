/* MODULO engine_logic: insiemi qualsiasi: modelli finiti, istanze,
 * saturazione, e i compiti svolti per Vampire (capitolo 28).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in engine_logic.h, e il
 * resto è static. */
#include "engine_logic.h"
#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"
#include "engine_induction.h"

/* =============================================================================
 * 28. INSIEMI QUALSIASI: MODELLI FINITI, ISTANZE, UGUALI AL POSTO DI UGUALI
 * ============================================================================
 *
 * A che cosa serve. "In un insieme con un'operazione, un elemento neutro a
 * sinistra e uno a destra coincidono" non parla di numeri: l'insieme è
 * qualsiasi, e dell'operazione si sa solo ciò che dicono le ipotesi. Non
 * c'è una regola da sostituire né un conto da fare, e le regole del capitolo
 * 18, che lavorano con i polinomi, non hanno presa. Il linguaggio di questi
 * enunciati è nel paragrafo 17o di parser.c; qui c'è il modo di deciderli,
 * che è fatto di due metà molto diverse.
 *
 * SMENTIRE: I MODELLI FINITI (28a, 28t)
 *
 * L'enunciato afferma qualcosa di ogni insieme e di ogni operazione. Per
 * smentirlo basta un esempio in cui le ipotesi valgono e la tesi no, e un
 * esempio si può cercare tra gli insiemi con uno, due, tre elementi: lì
 * un'operazione è una tabella, le tabelle sono in numero finito, e che un
 * enunciato valga in una tabella si controlla con un conto finito e
 * completo. Un esempio trovato così è un controesempio vero: il verdetto è
 * FALSO, con le tabelle stampate.
 * Quando le tabelle da enumerare sono troppe, 28t traduce la frase in
 * clausole proposizionali e cerca con un piccolo risolutore SAT scritto
 * qui. Le cardinalita crescono senza tetto compilato nel programma, entro
 * budget espliciti di lavoro e memoria. Ogni tabella estratta viene
 * ricalcolata senza usare la traduzione SAT e verificata dal checker.
 *
 * Non trovarne non dimostra nulla. "Ogni applicazione iniettiva di un
 * insieme in sé è suriettiva" vale in ogni insieme finito, e quindi in ogni
 * tabella che si possa provare, ma è falso: n -> n + 1 sui naturali è
 * iniettiva e non raggiunge lo zero. Per questo la ricerca dei modelli fa
 * due sole cose: smentisce, e fa da controllo indipendente di ciò che
 * l'altra metà dimostra. Un enunciato è dichiarato DIMOSTRATO solo se ha
 * una dimostrazione scritta, ricontrollata passo per passo, nessun modello
 * piccolo lo contraddice, e il verificatore indipendente ne accetta il
 * certificato (28f).
 *
 * Il prefisso esaustivo di 28a usa insiemi non vuoti; 28t include anche gli
 * insiemi vuoti. Il verificatore delle dimostrazioni controlla da se tutti
 * i possibili insiemi vuoti, come spiegato sotto.
 *
 * Fa eccezione l'enunciato che chiede un esempio, \exists S\ \exists R
 * \subseteq S \times S\ (...): lì un modello in cui la condizione vale è
 * proprio ciò che si chiede, e trovarlo è una dimostrazione.
 *
 * DIMOSTRARE: ISTANZE E UGUALI AL POSTO DI UGUALI (28b-28e, 28g)
 *
 * Si ragiona per assurdo, come si fa a mano: si suppongono le ipotesi e la
 * negazione della tesi, e si cerca una contraddizione. Tutto ciò che si sa
 * è un elenco di condizioni vere (Known), che cresce con cinque mosse,
 * ognuna una regola di deduzione valida:
 *
 *   28-1. Una parte. Da "A e B" seguono A e B; da "A oppure B", saputo che
 *         A è falsa, segue B.
 *   28-2. Un nome. Da "esiste x in S con P(x)" si prende un tale elemento e
 *         gli si dà un nome nuovo, c: vale P(c). È l'unico modo in cui
 *         nasce un elemento, insieme all'applicare un simbolo a elementi
 *         che ci sono già: per questo ciò che si dimostra vale anche se
 *         qualche insieme è vuoto, e il verificatore lo ricontrolla (28f).
 *   28-3. Un'istanza. Da "per ogni x in S vale P(x)", e da un elemento t di
 *         S, segue P(t).
 *   28-4. Uguali al posto di uguali. Le uguaglianze note s = t dividono gli
 *         elementi in classi; se a = a' e b = b' allora f(a, b) = f(a', b')
 *         (chiusura per congruenza). Vale anche per le parti e le
 *         relazioni: se x sta in X e x = y, allora y sta in X.
 *   28-5. Due casi. Se di "A oppure B" non si sa quale valga, si prova che
 *         la contraddizione arriva in tutti e due i casi.
 *
 * 28-2 e 28-3 valgono anche per le parti (17u di parser.c): da "esiste una
 * parte X di S con P(X)" nasce una parte con un nome nuovo, e da "per ogni
 * parte X di S vale P(X)" segue P(D) per ogni parte D di S che si sa
 * nominare, anche una definita da una regola, "D = \{x \in S \mid c(x)\}"
 * (28j). Quali parti provare, e come, lo dice 28k.
 *
 * La contraddizione è un'uguaglianza che dovrebbe essere falsa (si sa
 * s diverso da t, e s e t sono finiti nella stessa classe), oppure una
 * disgiunzione di cui tutte le parti sono false.
 *
 * Quali istanze. Le regole dicono che cosa è lecito, non che cosa conviene:
 * le istanze possibili sono infinite. Se ne provano di quattro tipi, per un
 * numero fisso di giri:
 *
 *   - sugli elementi che hanno un nome (quelli dichiarati, quelli della
 *     tesi, quelli nati da 28-2), tutte;
 *   - quelle che riscrivono un elemento presente: un termine della
 *     condizione che contiene tutte le sue variabili corrisponde a un
 *     elemento che c'è già. È ciò che fa chi applica l'associatività a
 *     (a b) c perché ce l'ha davanti;
 *   - sugli altri elementi presenti, solo quelle che non introducono
 *     elementi nuovi e contengono un confronto già deciso: sono quelle da
 *     cui 28-1 può trarre subito qualcosa;
 *   - per un "per ogni t" con t = f(u) nel corpo, sugli elementi presenti
 *     scritti come f(u): è "f(x) sta in f(X)" (28l).
 *
 * La definizione di una parte (28j) non si prova su tutti gli elementi con
 * un nome, ma dove la parte compare: "c \in D" chiede che si svolga.
 *
 * Quando le istanze scelte dalla forma non bastano, l'affermazione si
 * riprova con quelle scelte dal significato (28r): dagli elementi di cui si
 * parla si costruisce un modello candidato, il più piccolo che ciò che si
 * sa permette, e di ogni "per ogni" si prova l'istanza che vi è falsa. È la
 * "model-based quantifier instantiation" dei dimostratori SMT.
 *
 * Quali casi. Prima di distinguere i casi della prima disgiunzione in
 * attesa (28-5), si cerca tra le disgiunzioni in attesa una con un caso che
 * si chiude con i soli giri di istanze: allora l'altro caso segue, e la
 * distinzione non conta tra quelle una dentro l'altra (28l). È il lemma che
 * si dimostra per assurdo a metà di una dimostrazione.
 *
 * Non trovare la contraddizione vuol dire NON DIMOSTRATO, mai FALSO: la
 * ricerca non è completa.
 *
 * LA DIMOSTRAZIONE SCRITTA E IL SUO CONTROLLO (28e)
 *
 * Trovata la contraddizione, si risale da lì a ciò che è servito, e solo
 * quello viene scritto, un passo per riga. Ogni passo scritto viene
 * ricontrollato con un metodo diverso da quello che l'ha trovato:
 *
 *   - una catena di uguaglianze s = u = ... = t viene riletta anello per
 *     anello: ogni termine deve ottenersi dal precedente sostituendo, in un
 *     solo punto, un membro di un'uguaglianza già scritta con l'altro
 *     (rewrites()). La ricerca usa classi e rappresentanti; questo
 *     controllo guarda solo come sono scritti i termini.
 *   - un passo "da (p), poiché A vale e B no, segue C" viene ricontrollato
 *     con una tabella di verità: in ogni modo di dare vero o falso alle
 *     condizioni elementari di (p), se (p) è vera e A e B hanno il valore
 *     detto, allora C è vera (follows()).
 *
 * Poi, a dimostrazione finita, che i casi scritti siano tutti: le foglie,
 * con i loro casi, devono coprire ogni distinzione che fanno (28p). Se un
 * controllo fallisce la dimostrazione non viene emessa, e unjustified_steps
 * lo registra.
 *
 * IL CERTIFICATO (28f)
 *
 * Il controllo di 28e legge le tabelle della ricerca: due testimoni che
 * leggono lo stesso giornale. Per questo ogni verdetto del capitolo va anche
 * a checker.c, che non usa nulla di questo file (capitolo 11 di checker.c):
 *
 *   - un modello trovato da 28a, controesempio o esempio, va con le sue
 *     tabelle, e il verificatore vi ricalcola l'enunciato con il suo
 *     valutatore;
 *   - una dimostrazione va con i soli dati che la ricerca ha trovato: per
 *     ogni affermazione un caso, con i nomi (28-2), le istanze (28-3) e le
 *     parti definite (28j) che servono alle contraddizioni dei suoi rami.
 *     Le parti, le uguaglianze e
 *     i casi (28-1, 28-4, 28-5) il verificatore li ritrova da sé, provando
 *     tutti i valori delle condizioni elementari con la sua chiusura per
 *     congruenza, e lo rifà per ogni scelta degli insiemi vuoti: così che la
 *     dimostrazione valga anche se un insieme è vuoto diventa un conto, e non
 *     resta un argomento ("non inventa elementi").
 *
 * DIMOSTRATO e FALSO vogliono il certificato accettato: uno respinto è un
 * errore del programma, conta in unjustified_steps, e il verdetto diventa
 * NON DIMOSTRATO. Se il verificatore non sa controllare una dimostrazione
 * (troppe condizioni elementari) il verdetto resta, e dice perché il
 * certificato manca. Un modello invece è un conto per intero, che il motore
 * ha già fatto con limiti più stretti: se il verificatore non lo sa rifare,
 * il verdetto non c'è.
 *
 * LA NOTAZIONE DEI LIBRI (28h)
 *
 * Gli enunciati scritti con gli insiemi, f(X) = f(Y), R = \{(x, x) \mid x
 * \in S\}, arrivano qui già svolti nelle condizioni sugli elementi (17p,
 * 17q in parser.c): il capitolo non conosce altro linguaggio. Lo svolgimento
 * è una riscrittura, e prima di tutto si ricontrolla: 28h calcola su molti
 * modelli finiti l'enunciato com'è scritto, senza sostituire nulla, e quello
 * svolto, e vuole lo stesso valore. Il certificato è dell'enunciato svolto:
 * il verificatore non legge la notazione dei libri, come non legge il
 * LaTeX.
 *
 * LE PARTI E LE APPLICAZIONI COME OGGETTI (28m, 28n, 28o)
 *
 * Con \mathcal{P}(S) e T^{S} come insiemi di oggetti (17v in parser.c)
 * cambiano tre cose. I modelli finiti danno a questi insiemi le parti e le
 * applicazioni vere, con la loro tabella (28m): un controesempio è ancora un
 * controesempio vero. Le dimostrazioni hanno in più, tra le ipotesi, le
 * leggi delle parti, l'estensionalità e alcune comprensioni (28n), e il
 * verificatore controlla da sé che lo siano. E poiché qui le istanze
 * crescono in fretta, quando la ricerca di sempre non basta la si ripete
 * guardando avanti prima di distinguere i casi e scegliendo le istanze con
 * più cura, e un'affermazione che non segue tutta insieme si prova a pezzi
 * (28o); se non basta ancora, le istanze le sceglie il modello candidato
 * (28r). Tutto questo cambia solo quali dimostrazioni si trovano: ogni passo
 * scritto è ricontrollato come sempre, e il certificato pure.
 *
 * Un enunciato che parla solo dei numeri che scrive, con relazioni date
 * dall'elenco delle loro coppie (17v), ha un solo modello, con i numeri
 * tutti diversi: lì il calcolo decide, come per un esempio, e il verdetto
 * DIMOSTRATO viene da quel conto, con il certificato del modello.
 *
 * L'EQUIPOTENZA (28q)
 *
 * A \sim B (17w in parser.c) vuol dire che c'è una biiezione da A a B: è un
 * "esiste" su due applicazioni, una l'inversa dell'altra, e il capitolo lo
 * usa con le sue due regole. Vera, dà un nome alla biiezione e alla sua
 * inversa, come 28-2. Falsa, ha per istanza due applicazioni costruite,
 * come 28-3: un testimone, fatto da una grammatica piccola e limitata con le
 * biiezioni con un nome e la forma degli insiemi (l'immagine delle parti, f
 * \mapsto \beta \circ f \circ \alpha^{-1} sulle applicazioni, le componenti di
 * un prodotto, scambiate o no), con una definizione per ogni applicazione
 * nuova; che siano una l'inversa dell'altra lo deve mostrare la
 * dimostrazione, con le definizioni e l'estensionalità (28n). Il numero
 * degli elementi non entra mai in una dimostrazione: solo nei modelli
 * finiti, dove A \sim B è "tanti elementi quanti". Il certificato porta i
 * nomi, le definizioni e il testimone, e il verificatore controlla da sé la
 * forma di ogni definizione (11j di checker.c).
 *
 * CHE COSA NON C'È
 *
 * Applicazioni da costruire (\exists f \in S^{S} dentro l'enunciato) fuori
 * da un'equipotenza, ipotesi su tutte le applicazioni quando T^{S} non è un
 * insieme di oggetti dell'enunciato, applicazioni definite per casi o come
 * inverse (servirebbero comprensioni di applicazioni più larghe di quella con
 * due valori di 28s: le definizioni di 28q nascono solo per un testimone), il
 * quoziente (\exists T\ \exists f), potenze x^{n} con n numero: il lettore le
 * respinge, dicendo quale. Le parti costruite con più di un passo, come
 * f(f^{-1}(\{c\})) o \{a, b\}, non vengono provate (28k): un enunciato che
 * ne ha bisogno resta NON DIMOSTRATO. Dell'equipotenza (28q)
 * mancano le biiezioni che la grammatica non costruisce (\mathcal{P}(S) \sim
 * \{0, 1\}^{S}, l'associatività dei prodotti), i passi w3 e w4 uno dentro
 * l'altro, come \mathcal{P}(\mathcal{P}(S)) \sim \mathcal{P}(\mathcal{P}(T)),
 * le cui identità chiederebbero un lemma con l'estensionalità a metà della
 * dimostrazione, che la ricerca non fa; e nel lettore gli esponenti che sono
 * un prodotto o un'unione, S^{T \times V} e S^{T \cup V} (17w), e i lati di
 * tre componenti. Il numero degli elementi, |S|, non c'è (capitolo 20).
 *
 * Il modello candidato di 28r sceglie le istanze, non i casi: le
 * distinzioni restano quelle di refute(), sulla prima disgiunzione in
 * attesa, e una dimostrazione che ne chiede molte, una dentro l'altra, non
 * si trova. Le sue dimostrazioni sono lunghe: ogni caso riscrive le righe
 * da cui parte, e il certificato porta insieme le istanze di tutti i casi,
 * che il verificatore deve ridistinguere da sé. Una delle sue dimostrazioni
 * (la transitività dell'ordine f(S) \subsetneq g(S) di order_relations.tex)
 * ha più casi di quanti il verificatore sappia provare entro il suo limite:
 * il verdetto resta, e dice che il certificato manca. Si potrebbe dare al
 * verificatore la struttura dei casi, come voci del certificato.
 *
 * I modelli finiti dimostrano solo un esempio; un enunciato "per ogni" lo
 * dimostrano le istanze. Una dimostrazione dai soli modelli sarebbe lecita
 * nella classe di Bernays, Schönfinkel e Ramsey (gli "esiste" della
 * negazione, messa in forma prenessa, tutti prima dei "per ogni", e nessuna
 * applicazione che riporti un insieme in un insieme da cui si parte, così
 * che i termini chiusi siano finiti): lì un controesempio, se c'è, ne ha uno
 * con al più tanti elementi quanti sono gli "esiste". Non è usata: andrebbe
 * riconosciuta la classe, scritto il limite, e certificato il conto su tutti
 * i modelli fino a quel limite, che il verificatore oggi non fa; le
 * dimostrazioni per istanze hanno già il loro certificato. Fuori da quella
 * classe è proprio dove i modelli ingannano: "un'applicazione iniettiva di
 * un insieme in sé è suriettiva" vale in ogni modello finito ed è falso.
 */

/* 28a. I MODELLI FINITI */

/* Una coordinata della ricerca dei modelli: la grandezza di un insieme.
 * Si contano elementi; minimum non è mai una grandezza massima. */
typedef struct {
    size_t size;     /* Quanti elementi ha l'insieme nel modello in corso. */
    size_t minimum;  /* Quanti ne deve avere almeno, per la formula e per i tipi (model_minimums()). */
    size_t extra;    /* Stato dell'enumeratore: size = minimum + extra, dove è indirizzabile. */
} ModelDimension;

/* Un'interpretazione finita dell'enunciato in corso: quanti elementi ha
 * ogni insieme, e la tabella di ogni simbolo dichiarato. Gli elementi
 * dell'insieme di posto i sono i numeri da 0 a dimension[i].size - 1.
 *
 * La tabella di un simbolo dà il suo valore per ogni scelta degli
 * argomenti: alla cella a + b * (elementi del primo insieme) c'è il valore
 * in (a, b), che è un elemento del codominio, oppure 0 o 1 per una parte o
 * una relazione. Un elemento con un nome ha la sola cella 0. Le tabelle dei
 * simboli di struttura degli insiemi di parti e di applicazioni non si
 * scelgono: le fissa model_structure() (28m).
 *
 * Il modello possiede coordinate e tabelle. Gli indici di insieme e di
 * simbolo sono quelli del problema corrente; la pulizia usa soltanto le
 * capacità e le lunghezze possedute, non i contatori del parser. */
typedef struct {
    ModelDimension *dimension;      /* Coordinate possedute, indicizzate per insieme. */
    size_t dimension_capacity;      /* Celle allocate nel vettore dimension. */
    size_t **table;                 /* Tabelle possedute, una per simbolo, NULL senza celle. */
    unsigned char **part;           /* Contesti temporanei presi in prestito dai quantificatori su parti. */
    size_t symbols;                 /* Numero di celle allocate in table e part, indipendente dal parser. */
    size_t bytes;                    /* Byte di coordinate, puntatori e tabelle posseduti. */
    int limited;                     /* Ultima allocazione interrotta per risorse, non per dominio vuoto. */
} Model;

/* Libera solo le tabelle; le coordinate restano valide per il tentativo
 * successivo della stessa enumerazione. Anche la loro memoria e contata. */
static void model_tables_clear(Model *m) {
    if (m->table) for (size_t i = 0; i < m->symbols; i++) free(m->table[i]);
    free(m->table); free(m->part); m->table = NULL; m->part = NULL; m->symbols = 0;
    m->bytes = m->dimension_capacity*sizeof *m->dimension;
}

/* Dimensiona le coordinate entro il budget dei modelli. Una crescita
 * conserva le cardinalita, azzera le celle nuove e non pubblica memoria
 * parziale. Risorse finite fermano questa ricerca, non altre dimostrazioni. */
static int model_dimensions(Model *m) {
    size_t need=(size_t)sort_count,unit=sizeof *m->dimension;
    if (m->bytes>model_memory_limit || need>model_memory_limit/unit) { m->limited=1;return 0; }
    if (need<=m->dimension_capacity) return 1;
    size_t cap=m->dimension_capacity?m->dimension_capacity:16;
    while (cap<need) {
        if (cap>(size_t)-1/2) { cap=need;break; }
        cap*=2;
    }
    size_t other=m->bytes-m->dimension_capacity*unit;
    if (cap>(model_memory_limit-other)/unit) cap=need;
    if (cap>(model_memory_limit-other)/unit) { m->limited=1;return 0; }
    ModelDimension *data=realloc(m->dimension,cap*unit);
    if (!data) { m->limited=1;return 0; }
    memset(data+m->dimension_capacity,0,(cap-m->dimension_capacity)*unit);
    m->dimension=data;m->dimension_capacity=cap;m->bytes=other+cap*unit;
    return 1;
}

/* Libera tutto cio che il modello possiede, senza dipendere dai contatori
 * del parser che possono gia appartenere all'enunciato successivo. */
static void model_clear(Model *m) {
    model_tables_clear(m);
    free(m->dimension);m->dimension=NULL;m->dimension_capacity=0;m->bytes=0;
}

/* Moltiplica dimensioni solo se il risultato e indirizzabile. */
static int model_product(size_t a, size_t b, size_t *out) {
    if (a && b > (size_t)-1 / a) return 0;
    *out = a * b;
    return 1;
}

/* 28i. LE PARTI LEGATE NEI MODELLI
 *
 * (Sta qui, dentro 28a, perché i modelli la usano; la lettera è venuta dopo
 * le altre.)
 *
 * Un quantificatore su parti (17u), "per ogni parte X di S", in un modello
 * finito si calcola come uno su elementi: le parti di un insieme di n
 * elementi sono 2^n, e si provano tutte. Una parte e un vettore di n byte, con
 * il byte x acceso se l'elemento x sta nella parte. La parte legata non ha una
 * tabella sua (model_cells() le dà zero celle, così la ricerca dei
 * modelli non la sceglie): il suo valore è in Model.part, come quello di
 * una variabile in value[]. */

/* Ritorna il valore della cella (a, b) della tabella del simbolo symbol nel
 * modello m (b conta solo con due argomenti): per una parte legata, 1 se a
 * sta nella parte che le dà Model.part. */
static size_t model_cell(const Model *m, int symbol, size_t a, size_t b) {
    if (symbol_bound[symbol]) return m->part[symbol][a];
    size_t cell = symbols[symbol].arity ? a : 0;
    if (symbols[symbol].arity == 2) cell += b * m->dimension[symbols[symbol].domain[0]].size;
    return m->table[symbol][cell];
}

/* Ritorna il valore dell'elemento e nel modello m, con ogni variabile al
 * valore che ha in value[]; per una parte o una relazione applicata, 1 se
 * vale. */
static size_t model_element(const Model *m, const Elem *e, const size_t *value) {
    if (e->symbol < 0) return value[e->slot];
    size_t a = e->arg[0] ? model_element(m, e->arg[0], value) : 0, b = e->arg[1] ? model_element(m, e->arg[1], value) : 0;
    return model_cell(m, e->symbol, a, b);
}

/* Quanti elementi i quantificatori hanno provato da quando model_search()
 * ha cominciato. Con molti quantificatori uno dentro l'altro il conto su un
 * solo modello cresce come una potenza: venti "per ogni" su tre elementi
 * sono miliardi di prove. Oltre model_step_limit model_holds() smette di
 * calcolare, e chi la chiama deve buttare via la sua risposta. */
static long long model_steps;

/* Ritorna 1 se il conto sui modelli in corso è arrivato in fondo. Dopo un
 * conto interrotto il valore ritornato da model_holds() o da book_holds()
 * non vuol dire nulla, nemmeno quando è "vero": una negazione rovescia lo
 * zero di un quantificatore interrotto. Chi usa quel valore lo chiede qui. */
static int model_steps_complete(void) { return model_steps <= model_step_limit; }

/* Il motivo, se la ricerca SAT ha trovato un modello che poi non si è
 * potuto ricalcolare entro model_step_limit; altrimenti NULL. Un modello
 * così non è un controesempio, ma il verdetto deve dire che cosa è mancato:
 * non la ricerca, il budget del ricalcolo. Lo azzera prove_abstract(). */
static const char *model_unconfirmed;

/* 28i. Il calcolo di una condizione in un modello: model_holds() per le
 * condizioni svolte, book_holds() (28h) per quelle scritte come nei libri. */
typedef int (*ModelHolds)(const Model *m, const Sentence *s, size_t *value);

/* 28i. Ritorna 1 se il quantificatore su parti s (S_FORALL_PART o
 * S_EXISTS_PART) vale nel modello m, con le variabili ai valori di value[],
 * calcolando la sua condizione con holds. Prova le parti dalla vuota,
 * contandole in model_steps, e rimette Model.part com'era. Lo stesso
 * simbolo può essere legato da due quantificatori uno dentro l'altro (le
 * copie di 17q): per questo il valore di fuori si salva e si rimette. */
static int model_part_quantifier(const Model *m, const Sentence *s, size_t *value, ModelHolds holds) {
    int every = s->kind == S_FORALL_PART, result = every;
    size_t n = m->dimension[symbols[s->part].domain[0]].size;
    if (n > model_memory_limit) { model_steps = model_step_limit + 1LL; return 0; }
    unsigned char *saved = m->part[s->part], *bits = calloc(n ? n : 1, 1);
    if (!bits) { model_steps = model_step_limit + 1LL; return 0; }
    m->part[s->part] = bits;
    for (;;) {
        if (++model_steps > model_step_limit) break;
        if (holds(m, s->a, value) != every) { result = !every; break; }
        size_t bit = 0;
        while (bit < n && bits[bit]) bits[bit++] = 0;
        if (bit == n) break;
        bits[bit] = 1;
    }
    m->part[s->part] = saved;
    free(bits);
    return result;
}

/* 17w. Ritorna 1 se i due lati dell'equipotenza s hanno nel modello m lo
 * stesso numero di elementi: un lato è un insieme o il prodotto di due, e ne
 * ha il prodotto delle grandezze.
 *
 * Perché basta contare. Tra due insiemi finiti c'è una biiezione se e solo
 * se hanno lo stesso numero di elementi: se ne hanno n tutti e due, li si
 * numera da 0 a n - 1, e l'elemento numero i dell'uno va nell'elemento
 * numero i dell'altro; se c'è una biiezione, ogni elemento dell'uno ne ha
 * uno solo dell'altro e viceversa, quindi sono tanti quanti (è il principio
 * dei cassetti, letto nei due versi). È un fatto sugli insiemi finiti dei
 * modelli: le dimostrazioni non lo usano mai (28q). */
static int model_equipotent(const Model *m, const Sentence *s) {
    size_t size[2] = {1, 1};
    for (int k = 0; k < 2; k++)
        for (int i = 0; i < s->sides[k]; i++)
            if (!model_product(size[k], m->dimension[slot_data[s->side_slot[k][i]].sort].size, &size[k])) {
                model_steps = model_step_limit + 1LL;
                return 0;
            }
    return size[0] == size[1];
}

/* Ritorna 1 se la condizione s vale nel modello m, con le variabili libere
 * ai valori di value[]. È un conto finito e completo: ogni quantificatore
 * prova tutti gli elementi del suo insieme. value[] viene usato anche per
 * le variabili che s lega. Se model_steps supera model_step_limit la
 * risposta non vuol dire nulla. */
static int model_holds(const Model *m, const Sentence *s, size_t *value) {
    switch (s->kind) {
    case S_TRUE:
        return 1;
    case S_EQUIPOTENT:
        return model_equipotent(m, s);
    case S_EQUAL:
        return model_element(m, s->left, value) == model_element(m, s->right, value);
    case S_HOLDS:
        return model_element(m, s->left, value);
    case S_NOT:
        return !model_holds(m, s->a, value);
    case S_AND:
        return model_holds(m, s->a, value) && model_holds(m, s->b, value);
    case S_OR:
        return model_holds(m, s->a, value) || model_holds(m, s->b, value);
    case S_IMPLIES:
        return !model_holds(m, s->a, value) || model_holds(m, s->b, value);
    case S_IFF:
        return model_holds(m, s->a, value) == model_holds(m, s->b, value);
    case S_FORALL_PART: case S_EXISTS_PART:
        return model_part_quantifier(m, s, value, model_holds);
    case S_FORALL: case S_EXISTS:
        break;
    case S_MEMBER: case S_INCLUDED: case S_SAME: case S_UNIQUE: case S_COUNT:
        /* La notazione dei libri non arriva qui: lo svolgimento (17q) la
         * toglie, e book_holds() (28h) la calcola a parte. */
        return 0;
    }
    int every = s->kind == S_FORALL;
    for (size_t x = 0; x < m->dimension[slot_data[s->slot].sort].size; x++) {
        if (++model_steps > model_step_limit) return 0;
        value[s->slot] = x;
        if (model_holds(m, s->a, value) != every) return !every;
    }
    return every;
}

/* Ritorna quanti valori può prendere una cella della tabella del simbolo
 * symbol nel modello m, e mette in *cells quante celle ha la tabella. Una
 * parte legata (28i) ha zero celle: nessuno ne sceglie la tabella. */
static size_t model_cells(const Model *m, int symbol, size_t *cells) {
    const Symbol *s = &symbols[symbol];
    *cells = 1;
    for (int i = 0; i < s->arity; i++)
        if (!model_product(*cells, m->dimension[s->domain[i]].size, cells)) { *cells = (size_t)-1; return 0; }
    if (symbol_bound[symbol]) { *cells = 0; return 1; }
    return s->range == TRUTH ? 2 : m->dimension[s->range].size;
}

/* Alloca tabelle azzerate delle cardinalita correnti. Celle e valori non
 * hanno un tetto prefissato; overflow, budget o malloc fallita danno 0.
 * Una funzione con dominio non vuoto e codominio vuoto non esiste. */
static int model_allocate(Model *m) {
    model_tables_clear(m);
    m->limited = 0;
    if (!model_dimensions(m)) return 0;
    size_t pointers;
    if (!model_product((size_t)symbol_count, sizeof *m->table + sizeof *m->part, &pointers) || pointers > model_memory_limit-m->bytes) {
        m->limited = 1; return 0;
    }
    if (symbol_count) {
        m->symbols = (size_t)symbol_count;
        m->table = calloc(m->symbols, sizeof *m->table);
        m->part = calloc(m->symbols, sizeof *m->part);
        if (!m->table || !m->part) { m->limited = 1; model_tables_clear(m); return 0; }
    }
    m->bytes += pointers;
    for (int s = 0; s < symbol_count; s++) {
        size_t cells, bytes, values = model_cells(m, s, &cells);
        if (cells && !values && cells != (size_t)-1) { model_tables_clear(m); return 0; }
        if (!model_product(cells, sizeof(size_t), &bytes) || bytes > model_memory_limit - m->bytes) {
            m->limited = 1; model_tables_clear(m); return 0;
        }
        if (bytes) m->table[s] = calloc(bytes, 1);
        if (bytes && !m->table[s]) { m->limited = 1; model_tables_clear(m); return 0; }
        m->bytes += bytes;
    }
    return 1;
}

/* 28m. GLI INSIEMI DI PARTI E DI APPLICAZIONI NEI MODELLI
 *
 * (Sta qui, dopo 28a, perché ne completa i modelli; la lettera è venuta
 * dopo le altre.)
 *
 * Un enunciato che prende \mathcal{P}(S) o T^{S} come insieme di oggetti
 * (17v in parser.c) parla delle parti e delle applicazioni vere: un suo
 * modello non può dare a \mathcal{P}(S) elementi qualsiasi, perché un
 * controesempio in cui \mathcal{P}(S) non contiene tutte le parti di S non
 * smentirebbe nulla. Per questo in un modello la grandezza di questi insiemi
 * e la tabella del loro simbolo di struttura non si scelgono, si calcolano:
 *
 *   - \mathcal{P}(S), con S di n elementi, ha 2^n elementi: l'elemento k è
 *     la parte degli i con il bit i di k uguale a 1. Ogni parte di S ha un
 *     solo k, quindi questo è proprio l'insieme delle parti.
 *   - T^{S}, con S di n elementi e T di m, ha m^n elementi: l'elemento k è
 *     l'applicazione che manda i nella cifra i di k scritto in base m (la
 *     cifra 0 è quella delle unità). Ogni applicazione ha un solo k.
 *
 * È la stessa numerazione del verificatore (ck_derived_sort() in
 * checker.c), che la rifà da sé: le tabelle degli altri simboli nominano gli
 * elementi con quei numeri. Il prefisso esaustivo usa MAX_MODEL_SIZE,
 * MAX_MODEL_OBJECTS e MAX_MODEL_CELLS per restare breve; la ricerca SAT
 * successiva non li usa. Entrambe hanno le stesse tabelle dinamiche. */

/* Ritorna 1 se la tabella del simbolo di posto s è fissata dalla struttura
 * di un insieme, e non va scelta: il simbolo di struttura di un insieme di
 * parti o di applicazioni, o un numero scritto come elemento (17v). */
static int symbol_fixed(int s) { return symbol_structure(s) >= 0 || symbols[s].name >= NUMERAL_NAMES; }

/* 17v. Ritorna quale dei numeri dell'insieme di posto sort è il simbolo s:
 * 0 per il primo nell'elenco dei simboli, 1 per il secondo, e così via. È
 * l'elemento che lo rappresenta nei modelli, dove i numeri sono gli
 * elementi 0, 1, ... del loro insieme. */
static int numeral_position(int sort, int s) {
    int position = 0;
    for (int i = 0; i < s; i++) position += symbols[i].name >= NUMERAL_NAMES && symbols[i].range == sort;
    return position;
}

/* Completa le cardinalita degli insiemi derivati. Le potenze sono quelle
 * della definizione: si fermano se non sono indirizzabili, senza enumerare
 * una potenza enorme. model_allocate controlla poi il budget di memoria. */
static int model_derived_sizes(Model *m) {
    for (int i = 0; i < sort_count; i++) {
        if (sort_data[i].kind == SORT_PLAIN) continue;
        if (sort_data[i].kind == SORT_NUMBERS) {
            m->dimension[i].size = 0;
            for (int s = 0; s < symbol_count; s++) m->dimension[i].size += symbols[s].name >= NUMERAL_NAMES && symbols[s].range == i;
            continue;
        }
        size_t values = sort_data[i].kind == SORT_PARTS ? 2 : m->dimension[sort_data[i].target].size, size = 1;
        size_t power = m->dimension[sort_data[i].base].size;
        /* L'esponenziazione binaria evita un ciclo lungo anche per 0^n e 1^n. */
        for (; power; power /= 2) {
            if ((power & 1) && !model_product(size, values, &size)) return 0;
            if (power > 1 && !model_product(values, values, &values)) return 0;
        }
        m->dimension[i].size = size;
    }
    return 1;
}

/* Le cifre in base base scelgono solo le grandezze degli insiemi arbitrari
 * del prefisso esaustivo; gli altri non consumano cifre. Ritorna la somma,
 * o -2 fuori dal prefisso. I limiti non riguardano il successivo SAT. */
static int model_sizes_at(Model *m, int code, int base) {
    if (!model_dimensions(m)) return -2;
    int sum = 0;
    for (int i = 0; i < sort_count; i++) {
        if (sort_data[i].kind == SORT_PLAIN) {
            sum += (int)(m->dimension[i].size=1+code%base);code/=base;
        }
    }
    if (!model_derived_sizes(m)) return -2;
    for (int i = 0; i < sort_count; i++)
        if (sort_data[i].kind != SORT_PLAIN && m->dimension[i].size > MAX_MODEL_OBJECTS) return -2;
    for (int s = 0; s < symbol_count; s++) {
        size_t cells;
        model_cells(m, s, &cells);
        if (cells > MAX_MODEL_CELLS) return -2;
    }
    return sum;
}

/* Le grandezze della ricerca esaustiva (28a), nella sua base usuale. La
 * ricerca SAT sceglie direttamente le cardinalita, senza una base fissa. */
static int model_sizes(Model *m, int code) {
    return model_sizes_at(m, code, MAX_MODEL_SIZE);
}

/* Riempie in m le tabelle dei simboli di struttura, con la numerazione
 * descritta in testa al paragrafo. Le grandezze devono essere già date
 * (model_sizes()). */
static void model_structure(Model *m) {
    /* 17v. Ogni numero scritto è un elemento diverso del suo insieme. */
    for (int s = 0; s < symbol_count; s++)
        if (symbols[s].name >= NUMERAL_NAMES) m->table[s][0] = (size_t)numeral_position(symbols[s].range, s);
    for (int i = 0; i < sort_count; i++) {
        if (sort_data[i].kind == SORT_PLAIN || sort_data[i].kind == SORT_NUMBERS) continue;
        size_t *cell = m->table[sort_data[i].symbol];
        size_t base = m->dimension[sort_data[i].base].size;
        for (size_t x = 0; x < m->dimension[i].size; x++)
            for (size_t a = 0, rest = x; a < base; a++) {
                /* Le parti: la cella di (a, x) dice se a sta nella parte x.
                 * Le applicazioni: quella di (x, a) è il valore di x in a. */
                if (sort_data[i].kind == SORT_PARTS) { cell[a + x * base] = (size_t)(x >> a & 1); continue; }
                cell[x + a * m->dimension[i].size] = (rest % m->dimension[sort_data[i].target].size);
                rest /= m->dimension[sort_data[i].target].size;
            }
    }
}

/* Quanti insiemi qualsiasi ha l'enunciato in corso: gli altri sono insiemi
 * di parti o di applicazioni, la cui grandezza non si sceglie. */
static int plain_sorts(void) {
    int count = 0;
    for (int i = 0; i < sort_count; i++) count += sort_data[i].kind == SORT_PLAIN;
    return count;
}

/* Prima composizione di total negli insiemi arbitrari: tutto nell'ultima
 * coordinata, zero nelle altre. Non usa una pila proporzionale ai tipi. */
static int model_composition_start(Model *m,size_t total) {
    int last=-1;
    for (int i=0;i<sort_count;i++) if (sort_data[i].kind==SORT_PLAIN) {
        m->dimension[i].extra=0;last=i;
    }
    if (last>=0) m->dimension[last].extra=total;
    return last>=0 || !total;
}

/* Composizione successiva, in ordine lessicografico. La coda non nulla
 * cede un elemento alla coordinata precedente; quelle attraversate sono
 * azzerate. La somma resta total, quindi l'incremento non puo traboccare.
 * Ogni composizione appare una volta, senza codificare base^sort_count. */
static int model_composition_next(Model *m) {
    int last=sort_count-1;
    while (last>=0 && sort_data[last].kind!=SORT_PLAIN) last--;
    if (last<0) return 0;
    size_t tail=m->dimension[last].extra;
    for (int i=last-1;i>=0;i--) if (sort_data[i].kind==SORT_PLAIN) {
        if (tail) {
            m->dimension[i].extra++;m->dimension[last].extra=tail-1;return 1;
        }
        tail=m->dimension[i].extra;m->dimension[i].extra=0;
    }
    return 0;
}

/* Materializza i valori della composizione e le cardinalita derivate.
 * maximum>0 delimita soltanto il campione indipendente dei libri: ripete
 * i vincoli del prefisso esaustivo. SAT chiama con zero e non li usa. */
static int model_composition_values(Model *m,size_t maximum) {
    for (int i=0;i<sort_count;i++) if (sort_data[i].kind==SORT_PLAIN) {
        ModelDimension *d=&m->dimension[i];
        if (d->extra>(size_t)-1-d->minimum) return 0;
        d->size=d->minimum+d->extra;
        if (maximum && d->size>maximum) return 0;
    }
    if (!model_derived_sizes(m)) return 0;
    for (int i=0;i<sort_count;i++) {
        if (m->dimension[i].size<m->dimension[i].minimum) return 0;
        if (maximum && sort_data[i].kind!=SORT_PLAIN && m->dimension[i].size>MAX_MODEL_OBJECTS) return 0;
    }
    if (maximum) for (int f=0;f<symbol_count;f++) {
        size_t cells;model_cells(m,f,&cells);
        if (cells>MAX_MODEL_CELLS) return 0;
    }
    return 1;
}

/* Ambiente riutilizzabile dei valutatori finiti. Il vettore possiede le
 * celle e cresce con gli slot della formula, non con la cardinalita degli
 * insiemi. Le valutazioni sono sequenziali e non creano slot: il puntatore
 * resta valido fino alla prossima chiamata a model_variables(). */
static size_t *model_values;
static size_t model_values_capacity;

/* Prepara valori iniziali zero per tutti gli slot correnti. Un errore di
 * allocazione non puo essere ignorato da una strategia successiva. */
static size_t *model_variables(void) {
    if (!work_reserve((void **)&model_values, &model_values_capacity, (size_t)slot_count, sizeof *model_values)) return NULL;
    if (slot_count) memset(model_values, 0, (size_t)slot_count * sizeof *model_values);
    return model_values;
}

/* Cerca un modello in cui la condizione root vale (wanted = 1) o non vale
 * (wanted = 0), tra quelli in cui ogni insieme ha da 1 a MAX_MODEL_SIZE
 * elementi, dai più piccoli. Se lo trova lo lascia in *m e ritorna 1.
 *
 * Non sempre li prova tutti: una scelta delle grandezze con più di
 * MAX_MODELS tabelle viene saltata, e dopo MAX_MODEL_WORK tabelle in tutto,
 * o model_step_limit elementi provati dai quantificatori, la ricerca si
 * ferma. In *tried mette quante tabelle ha provato, e in
 * *bound il più grande k per cui ha provato tutti i modelli con insiemi di
 * al più k elementi: è ciò che il verdetto può dire di aver controllato. */
static int model_search(const Sentence *root, int wanted, Model *m, long long *tried, int *bound) {
    size_t *value = model_variables();
    int codes = 1, complete[MAX_MODEL_CODES] = {0}, plain = plain_sorts();
    *tried = 0;
    *bound = 0;
    if (work_allocation_failed) return 0;
    model_steps = 0;
    if (!model_dimensions(m)) return 0;
    /* Questa strategia deve completare tutte le configurazioni per
     * certificare bound. Quando non entrano nella sua quota, passa a SAT;
     * non tronca un prodotto e non inventa un prefisso completato. */
    for (int i=0;i<plain;i++) {
        if (codes>MAX_MODEL_CODES/MAX_MODEL_SIZE) return 0;
        codes*=MAX_MODEL_SIZE;
    }

    /* Le grandezze, per numero totale di elementi degli insiemi qualsiasi:
     * code le elenca tutte, e a ogni giro si tengono quelle con quel totale.
     * Gli insiemi di parti e di applicazioni hanno la grandezza che segue
     * (28m). */
    for (int total = plain; sort_count && total <= plain * MAX_MODEL_SIZE && *tried < MAX_MODEL_WORK; total++) {
        for (int code = 0; code < codes && *tried < MAX_MODEL_WORK; code++) {
            if (model_sizes(m, code) != total) continue;

            /* Quante tabelle: il prodotto, su tutte le celle, dei valori
             * possibili. */
            double count = 1;
            for (int s = 0; s < symbol_count && count <= MAX_MODELS; s++) {
                size_t cells, values = model_cells(m, s, &cells);
                for (size_t c = 0; c < cells && count <= MAX_MODELS && !symbol_fixed(s); c++) count *= values;
            }
            if (count > MAX_MODELS) continue;

            /* Tutte le tabelle, come un contachilometri: si parte da tutte
             * le celle a zero e si aumenta la prima che può crescere,
             * azzerando quelle prima di lei. Quelle fissate dalla struttura
             * non cambiano. */
            if (!model_allocate(m)) continue;
            model_structure(m);
            for (int more = 1; more && *tried < MAX_MODEL_WORK; ) {
                /* Una risposta ottenuta a conto interrotto non conta, e la
                 * ricerca finisce lì: *tried è già oltre il suo limite. */
                int holds = model_holds(m, root, value);
                if (!model_steps_complete()) { *tried = MAX_MODEL_WORK; break; }
                ++*tried;
                if (holds == wanted) return 1;
                more = 0;
                for (int s = 0; s < symbol_count && !more; s++) {
                    if (symbol_fixed(s)) continue;
                    size_t cells, values = model_cells(m, s, &cells);
                    for (size_t c = 0; c < cells && !more; c++) {
                        if (++m->table[s][c] < values) more = 1; else m->table[s][c] = 0;
                    }
                }
                if (!more) complete[code] = 1;
            }
        }
    }

    /* Il piu grande k con tutte le grandezze fino a k provate per intero.
     * Ogni codice indica una scelta degli insiemi arbitrari: anche una
     * costruzione derivata troppo grande resta una scelta non completata. */
    for (int k = 1; k <= MAX_MODEL_SIZE; k++) {
        int all = 1;
        for (int code = 0; code < codes; code++) {
            int inside=1,rest=code;
            for (int i=0;i<sort_count;i++) if (sort_data[i].kind==SORT_PLAIN) {
                inside=inside && 1+rest%MAX_MODEL_SIZE<=k;rest/=MAX_MODEL_SIZE;
            }
            if (inside && !complete[code]) all = 0;
        }
        if (!all) break;
        *bound = k;
    }
    return 0;
}

/* 28t. MODELLI FINITI CON SAT
 *
 * Una casella f(a,b)=c e una variabile booleana. Una clausola impone che
 * ogni casella abbia almeno un valore, e le clausole a coppie che non ne
 * abbia due. Un termine composto ha un vettore di valori con lo stesso
 * vincolo; se i suoi argomenti valgono a,b, prende il valore della casella
 * (a,b). I quantificatori diventano congiunzioni o disgiunzioni finite.
 * Per i connettivi si introduce un nome con clausole equivalenti (Tseitin),
 * evitando di distribuire le disgiunzioni sulle congiunzioni.
 *
 * E la riduzione MACE a SAT: Claessen e Sorensson, "New techniques that
 * improve MACE-style finite model finding" (2003), e Reger, Suda e
 * Voronkov, "Finding finite models in multi-sorted first-order logic"
 * (2016), https://arxiv.org/abs/1604.08040. Qui si riscrive l'idea, non il
 * codice. Il piccolo risolutore usa clausole osservate, propagazione unitaria
 * e apprendimento del primo punto di implicazione unico (CDCL): risolve i
 * conflitti con le ragioni delle assegnazioni fino a una sola assegnazione
 * del livello corrente. La clausola cosi ottenuta segue dalle precedenti.
 *
 * SAT cerca soltanto. Anche una risposta sbagliata del risolutore non e una
 * dimostrazione: si estraggono le tabelle, model_holds() ricalcola la frase,
 * e 28f consegna il modello al verificatore indipendente. UNSAT e i limiti
 * di risorse non dimostrano mai un enunciato universale. Dopo il prefisso
 * esaustivo, le cardinalita crescono senza tetto; depositi, tabelle e testo
 * crescono sullo heap entro budget espliciti. Anche il checker usa indici
 * size_t e tabelle dinamiche, non un limite equivalente nascosto.
 */

/* Un letterale SAT e un indice con segno; la memoria necessaria per una
 * variabile esaurisce lo spazio indirizzabile prima dell'indice stesso. */
typedef ptrdiff_t SatLiteral;

/* Una clausola: first/count individuano i letterali nel deposito; next
 * collega i due osservatori nelle liste watch. Zero termina ogni lista. */
typedef struct {
    size_t first, count, next[2];
} SatClause;

/* Una variabile proposizionale: value e phase valgono -1,0,1; depth e il
 * livello di assegnazione, reason la clausola+1 (zero per una decisione).
 * seen serve all'analisi del conflitto, activity guida soltanto la ricerca. */
typedef struct {
    signed char value, phase;
    unsigned char seen;
    size_t depth, reason;
    unsigned long long activity;
} SatVariable;

/* Un valore finito: literal[v] significa "vale v". known=(size_t)-1
 * indica un vettore variabile, altrimenti il valore costante, rappresentato
 * senza allocare un vettore. symbol/arg/next condividono applicazioni e
 * costanti nella hash; symbol=-1 esclude una voce dalla condivisione.
 * literal e posseduto dalla voce, gli argomenti sono indici di altre voci. */
typedef struct {
    size_t size, known, arg[2], next;
    int symbol;
    SatLiteral *literal;
} SatTerm;

/* Metadati SAT di un insieme. named conta le costanti dichiarate, seen
 * quelle gia codificate; ordered_map e la sola mappa S->S ordinata per
 * simmetria, -1 se assente. Le celle sono possedute dallo stato SAT. */
typedef struct { size_t named,seen;int ordered_map; } SatSort;

/* Una ricerca possiede tutti i depositi, ognuno con capacita dinamica.
 * I contatori indicano le voci valide; i suffissi _cap le celle allocate.
 * var e term partono da 1; la variabile 1 e vera. trail contiene le
 * assegnazioni, limit[d] l'inizio del livello d, qhead la prima da propagare.
 * watch contiene 2*clausola+osservatore+1; hash contiene indici di term.
 * table associa ogni cella del modello al suo vettore; slots tiene gli
 * elementi legati. broken significa risorse finite, inconsistent conflitto.
 * bytes comprende le tabelle del modello e tutte le allocazioni SAT;
 * budget/work limitano il lavoro, mai la cardinalita di un insieme.
 * memory_limit, se non nullo, permette alla saturazione di condividere il
 * proprio budget con il SAT; zero conserva quello dei modelli finiti. */
typedef struct {
    size_t variables, clauses, literals, terms, level, assigned, qhead;
    int broken, inconsistent, memory_limited;
    unsigned long long work, budget;
    size_t bytes, memory_limit;
    SatVariable *var;
    SatClause *clause;
    SatLiteral *literal, *trail, *learned;
    size_t *watch, *limit, *hash;
    SatTerm *term;
    size_t var_cap, clause_cap, literal_cap, trail_cap, learned_cap;
    size_t watch_cap, limit_cap, term_cap, hash_cap;
    size_t **table, *slots;
    size_t table_cap, slots_cap;
    SatSort *sort;
    size_t sort_cap;
} SatState;

/* Registra lavoro prima di eseguirlo; un budget esaurito non e UNSAT. */
static int sat_spend(SatState *s, unsigned long long count) {
    unsigned long long budget = s->budget ? s->budget : model_work_limit;
    if (s->broken || s->work > budget || count > budget - s->work) { s->broken = 1; return 0; }
    s->work += count;
    return 1;
}

/* Riserva un deposito geometrico, conservando dati e proprieta anche se
 * realloc fallisce. Le celle nuove sono azzerate; nessuna capacita massima
 * e compilata nel programma. bytes contabilizza solo allocazioni riuscite. */
static int sat_reserve(SatState *s, void **data, size_t *capacity, size_t need, size_t unit) {
    if (s->broken) return 0;
    if (need <= *capacity) return 1;
    size_t cap = *capacity ? *capacity : 16, bytes, old;
    while (cap < need) {
        if (cap > (size_t)-1 / 2) { cap = need; break; }
        cap *= 2;
    }
    size_t limit = s->memory_limit ? s->memory_limit : model_memory_limit;
    if (!model_product(cap, unit, &bytes) || !model_product(*capacity, unit, &old) ||
        s->bytes > limit || bytes - old > limit - s->bytes) {
        s->broken = s->memory_limited = 1; return 0;
    }
    void *p = realloc(*data, bytes);
    if (!p) { s->broken = s->memory_limited = 1; return 0; }
    memset((unsigned char *)p + old, 0, bytes - old);
    *data = p; *capacity = cap; s->bytes += bytes - old;
    return 1;
}

/* Libera ogni deposito della ricerca, comprese le tabelle di indici e i
 * vettori di valori posseduti dai termini. Puo seguire una crescita fallita. */
static void sat_clear(SatState *s) {
    for (size_t i = 1; i <= s->terms; i++) free(s->term[i].literal);
    for (size_t i = 0; i < s->table_cap; i++) free(s->table[i]);
    free(s->table);
    free(s->sort);
    free(s->var); free(s->clause); free(s->literal); free(s->trail);
    free(s->learned); free(s->watch); free(s->limit); free(s->hash); free(s->term); free(s->slots);
    memset(s, 0, sizeof *s);
}

/* Valore assoluto di un letterale prodotto dal risolutore, mai PTRDIFF_MIN. */
static size_t sat_index(SatLiteral l) { return (size_t)(l > 0 ? l : -l); }

/* Il posto nella lista osservata del letterale non nullo l. */
static size_t sat_watch_index(SatLiteral l) { return 2 * (sat_index(l) - 1) + (l < 0); }

/* Il valore del letterale l: 1 vero, -1 falso, 0 non assegnato. */
static int sat_value(const SatState *s, SatLiteral l) { return l > 0 ? s->var[l].value : -s->var[-l].value; }

/* Crea una variabile e riserva insieme i depositi indicizzati da essa.
 * In caso di risorse finite ritorna la costante vera e pone broken: nessun
 * chiamante puo usare quel valore come un modello accettato. */
static SatLiteral sat_variable(SatState *s) {
    size_t v = s->variables + 1;
    if (!sat_spend(s, 1) || v > (size_t)PTRDIFF_MAX || v > ((size_t)-1 - 2) / 2 ||
        !sat_reserve(s, (void **)&s->var, &s->var_cap, v + 2, sizeof *s->var) ||
        !sat_reserve(s, (void **)&s->watch, &s->watch_cap, 2 * v, sizeof *s->watch) ||
        !sat_reserve(s, (void **)&s->trail, &s->trail_cap, v + 2, sizeof *s->trail) ||
        !sat_reserve(s, (void **)&s->learned, &s->learned_cap, v + 2, sizeof *s->learned) ||
        !sat_reserve(s, (void **)&s->limit, &s->limit_cap, v + 2, sizeof *s->limit)) {
        s->broken = 1; return 1;
    }
    s->variables = v;
    s->var[v].phase = -1;
    return (SatLiteral)v;
}

/* Assegna l con la ragione data (zero: decisione), se non era gia falso.
 * Non alloca memoria: propagazione e analisi possono conservare puntatori. */
static int sat_assign(SatState *s, SatLiteral l, size_t reason) {
    if (s->broken) return 0;
    if (sat_value(s, l)) return sat_value(s, l) > 0;
    size_t v = sat_index(l);
    s->var[v].value = s->var[v].phase = l > 0 ? 1 : -1;
    s->var[v].depth = s->level;
    s->var[v].reason = reason;
    s->trail[s->assigned++] = l;
    return 1;
}

/* Aggiunge una clausola togliendo duplicati e falso; una tautologia non
 * serve. Ritorna clausola+1, o zero se non scrive. Le unitarie si assegnano
 * subito; le altre osservano i primi due posti. Il deposito dei letterali
 * puo spostarsi, quindi l'input non deve puntarvi dentro. */
static size_t sat_clause(SatState *s, const SatLiteral *literal, size_t count) {
    if (s->broken || s->inconsistent) return 0;
    if (!sat_spend(s, count + 1)) return 0;
    if (!count) { s->inconsistent = 1; return 0; }
    if (count > (size_t)-1 - s->literals || s->clauses > ((size_t)-1 - 2) / 2 ||
        !sat_reserve(s, (void **)&s->literal, &s->literal_cap, s->literals + count, sizeof *s->literal) ||
        !sat_reserve(s, (void **)&s->clause, &s->clause_cap, s->clauses + 1, sizeof *s->clause)) {
        s->broken = 1; return 0;
    }
    size_t first = s->literals, used = 0;
    for (size_t i = 0; i < count; i++) {
        SatLiteral l = literal[i];
        int repeated = 0;
        if (l == 1) return 0;
        if (l == -1) continue;
        for (size_t j = 0; j < used; j++) {
            if (!sat_spend(s, 1)) return 0;
            if (s->literal[first + j] == -l) return 0;
            repeated |= s->literal[first + j] == l;
        }
        if (!repeated) s->literal[first + used++] = l;
    }
    if (!used) { s->inconsistent = 1; return 0; }
    size_t c = s->clauses++;
    s->clause[c] = (SatClause){first, used, {0, 0}};
    s->literals += used;
    for (size_t i = 0; i < used; i++) s->var[sat_index(s->literal[first + i])].activity++;
    if (used == 1) {
        if (!sat_assign(s, s->literal[first], c + 1)) s->inconsistent = 1;
    } else for (size_t w = 0; w < 2; w++) {
        size_t at = sat_watch_index(s->literal[first + w]);
        s->clause[c].next[w] = s->watch[at];
        s->watch[at] = 2 * c + w + 1;
    }
    return c + 1;
}

/* Propaga solo gli osservatori diventati falsi: un sostituto evita di
 * esaminare la clausola alle altre assegnazioni. Senza sostituto, l'altro
 * osservato e obbligato. Ritorna clausola+1 per un conflitto, zero altrimenti. */
static size_t sat_propagate(SatState *s) {
    while (s->qhead < s->assigned && !s->broken) {
        SatLiteral false_literal = -s->trail[s->qhead++];
        size_t *link = &s->watch[sat_watch_index(false_literal)];
        while (*link) {
            if (!sat_spend(s, 1)) return 0;
            size_t edge = *link - 1, c = edge / 2, w = edge % 2;
            SatClause *clause = &s->clause[c];
            SatLiteral *v = s->literal + clause->first, other = v[1 - w];
            if (sat_value(s, other) > 0) { link = &clause->next[w]; continue; }
            size_t k = 2;
            while (k < clause->count && sat_value(s, v[k]) < 0) {
                if (!sat_spend(s, 1)) return 0;
                k++;
            }
            if (k < clause->count) {
                SatLiteral replacement = v[k];
                size_t at = sat_watch_index(replacement);
                v[k] = v[w]; v[w] = replacement;
                *link = clause->next[w]; clause->next[w] = s->watch[at]; s->watch[at] = edge + 1;
                continue;
            }
            if (!sat_assign(s, other, c + 1)) return c + 1;
            link = &clause->next[w];
        }
    }
    return 0;
}

/* Cancella le assegnazioni dopo il livello indicato; conserva fasi e
 * propagazioni precedenti, che non dipendono dalle decisioni cancellate. */
static void sat_backtrack(SatState *s, size_t level) {
    size_t keep = s->limit[level + 1];
    while (s->assigned > keep) s->var[sat_index(s->trail[--s->assigned])].value = 0;
    s->qhead = s->assigned; s->level = level;
}

/* Decide la CNF: 1 SAT, -1 UNSAT, 0 risorse finite. Risolve un conflitto
 * all'indietro con le sue ragioni fino al primo punto di implicazione unico
 * (un solo letterale al livello corrente). La clausola cosi ottenuta segue
 * dalle precedenti e diventa unitaria al livello degli altri letterali. */
static int sat_solve(SatState *s) {
    unsigned long long bump = 32, conflicts = 0;
    if (s->broken) return 0;
    if (s->inconsistent) return -1;
    for (;;) {
        size_t conflict = sat_propagate(s);
        if (s->broken) return 0;
        if (conflict) {
            if (!s->level) return -1;
            size_t count = 1, pending = 0, at = s->assigned;
            SatLiteral pivot = 0;
            do {
                SatClause *clause = &s->clause[conflict - 1];
                for (size_t i = 0; i < clause->count; i++) {
                    if (!sat_spend(s, 1)) return 0;
                    SatLiteral l = s->literal[clause->first + i];
                    size_t v = sat_index(l);
                    if (v == sat_index(pivot) || s->var[v].seen || !s->var[v].depth) continue;
                    s->var[v].seen = 1; s->var[v].activity += bump;
                    if (s->var[v].depth == s->level) pending++;
                    else s->learned[count++] = l;
                }
                do { pivot = s->trail[--at]; } while (!s->var[sat_index(pivot)].seen);
                s->var[sat_index(pivot)].seen = 0; pending--;
                conflict = s->var[sat_index(pivot)].reason;
            } while (pending && conflict);
            if (pending) { s->broken = 1; return 0; }
            s->learned[0] = -pivot;
            size_t level = 0;
            for (size_t i = 1; i < count; i++) {
                size_t v = sat_index(s->learned[i]);
                s->var[v].seen = 0;
                if (s->var[v].depth > level) level = s->var[v].depth;
            }
            sat_backtrack(s, level);
            size_t reason = sat_clause(s, s->learned, count);
            if (s->broken) return 0;
            if (s->inconsistent || !sat_assign(s, s->learned[0], reason)) return -1;
            if (++conflicts % 128 == 0) {
                bump *= 2;
                if (bump > (1ULL << 40)) {
                    for (size_t v = 2; v <= s->variables; v++) s->var[v].activity /= 2;
                    bump /= 2;
                }
            }
            continue;
        }
        size_t choose = 0;
        for (size_t v = 2; v <= s->variables; v++) {
            if (!sat_spend(s, 1)) return 0;
            if (!s->var[v].value && (!choose || s->var[v].activity > s->var[choose].activity)) choose = v;
        }
        if (!choose) return 1;
        s->limit[++s->level] = s->assigned;
        sat_assign(s, s->var[choose].phase > 0 ? (SatLiteral)choose : -(SatLiteral)choose, 0);
    }
}

/* Nome equivalente ad a e b; le clausole sono q=>a, q=>b, (a e b)=>q. */
static SatLiteral sat_and(SatState *s, SatLiteral a, SatLiteral b) {
    if (s->broken) return -1;
    if (a == b || b == 1) return a;
    if (a == 1) return b;
    if (a == -1 || b == -1 || a == -b) return -1;
    SatLiteral q = sat_variable(s);
    sat_clause(s, (SatLiteral[]){-q, a}, 2);
    sat_clause(s, (SatLiteral[]){-q, b}, 2);
    sat_clause(s, (SatLiteral[]){q, -a, -b}, 3);
    return q;
}

/* La disgiunzione, con De Morgan. */
static SatLiteral sat_or(SatState *s, SatLiteral a, SatLiteral b) { return -sat_and(s, -a, -b); }

/* Hash di una costante o applicazione: l'overflow unsigned e intenzionale
 * e cambia soltanto il contenitore, mai l'identita controllata dei termini. */
static size_t sat_term_hash(int symbol, size_t a, size_t b) {
    return (size_t)(unsigned)(symbol + 2) * 1009u + a * 9176u + b * 6361u;
}

/* Aggiunge un termine vuoto e allarga la hash. I puntatori a term possono
 * spostarsi: chi chiama conserva indici, non indirizzi, durante una crescita. */
static size_t sat_term(SatState *s, size_t size, size_t known) {
    if (!sat_spend(s, 1) || !size || s->terms > ((size_t)-1 - 4) / 2 ||
        !sat_reserve(s, (void **)&s->term, &s->term_cap, s->terms + 2, sizeof *s->term)) {
        s->broken = 1; return 0;
    }
    size_t old = s->hash_cap;
    if (!sat_reserve(s, (void **)&s->hash, &s->hash_cap, 2 * (s->terms + 2), sizeof *s->hash)) return 0;
    if (old != s->hash_cap) {
        memset(s->hash, 0, s->hash_cap * sizeof *s->hash);
        for (size_t i = 1; i <= s->terms; i++) if (s->term[i].symbol != -1) {
            SatTerm *t = &s->term[i];
            size_t at = sat_term_hash(t->symbol, t->arg[0], t->arg[1]) % s->hash_cap;
            t->next = s->hash[at]; s->hash[at] = i;
        }
    }
    size_t id = ++s->terms;
    s->term[id] = (SatTerm){.size=size, .known=known, .symbol=-1};
    return id;
}

/* Legge un letterale di valore, anche dalle costanti senza vettore. */
static SatLiteral sat_at(const SatState *s, size_t id, size_t value) {
    const SatTerm *t = &s->term[id];
    return t->known != (size_t)-1 ? (t->known == value ? 1 : -1) : t->literal[value];
}

/* Crea un vettore one-hot. Il vincolo "al piu uno" usa una catena di
 * prefissi: p_i significa che un valore precedente e vero; p_i e v_i non
 * possono essere veri insieme. Costo lineare, senza le coppie quadratiche.
 * L'ultima clausola impone almeno un valore; due valori usano un solo bit. */
static size_t sat_vector(SatState *s, size_t size) {
    size_t id = sat_term(s, size, size == 1 ? 0 : (size_t)-1);
    if (!id || size == 1) return id;
    size_t cap = 0;
    if (!sat_reserve(s, (void **)&s->term[id].literal, &cap, size, sizeof(SatLiteral))) return id;
    SatLiteral *literal = s->term[id].literal;
    if (size == 2) { literal[1] = sat_variable(s); literal[0] = -literal[1]; return id; }
    for (size_t v = 0; v < size && !s->broken; v++) literal[v] = sat_variable(s);
    sat_clause(s, literal, size);
    SatLiteral prefix = literal[0];
    for (size_t v = 1; v < size && !s->broken; v++) {
        sat_clause(s, (SatLiteral[]){-prefix, -literal[v]}, 2);
        if (v + 1 < size) prefix = sat_or(s, prefix, literal[v]);
    }
    return id;
}

/* Condivide il valore costante (size,value), senza allocare size letterali. */
static size_t sat_constant(SatState *s, size_t size, size_t value) {
    if (s->broken) return 0;
    if (!size || value >= size) { s->broken = 1; return 0; }
    if (s->hash_cap) {
        size_t at = sat_term_hash(-2, size, value) % s->hash_cap;
        for (size_t i = s->hash[at]; i; i = s->term[i].next)
            if (s->term[i].symbol == -2 && s->term[i].arg[0] == size && s->term[i].arg[1] == value) return i;
    }
    size_t id = sat_term(s, size, value);
    if (!id) return 0;
    SatTerm *t = &s->term[id]; t->symbol = -2; t->arg[0] = size; t->arg[1] = value;
    size_t at = sat_term_hash(-2, size, value) % s->hash_cap;
    t->next = s->hash[at]; s->hash[at] = id;
    return id;
}

/* Il vettore booleano equivalente al letterale, senza nuove variabili. */
static size_t sat_boolean(SatState *s, SatLiteral literal) {
    if (literal == 1 || literal == -1) return sat_constant(s, 2, literal == 1);
    size_t id = sat_term(s, 2, (size_t)-1), cap = 0;
    if (!id || !sat_reserve(s, (void **)&s->term[id].literal, &cap, 2, sizeof(SatLiteral))) return 0;
    s->term[id].literal[0] = -literal; s->term[id].literal[1] = literal;
    return id;
}

/* Traduce un'applicazione. Argomenti fissati selezionano una cella;
 * altrimenti ogni combinazione implica il valore di quella cella. La hash
 * condivide i termini composti. Le parti legate hanno vettori separati. */
static size_t sat_application(SatState *s, const Model *m, int symbol, size_t a, size_t b) {
    if (s->broken) return 0;
    const Symbol *f = &symbols[symbol];
    if (symbol_bound[symbol]) {
        SatLiteral truth = -1;
        for (size_t v = 0; v < m->dimension[f->domain[0]].size && !s->broken; v++)
            if (m->part[symbol][v]) truth = sat_or(s, truth, sat_at(s, a, v));
        return sat_boolean(s, truth);
    }
    size_t av = a ? s->term[a].known : 0, bv = b ? s->term[b].known : 0;
    if (av != (size_t)-1 && bv != (size_t)-1) return s->table[symbol][av + bv * (a ? m->dimension[f->domain[0]].size : 1)];
    size_t at = sat_term_hash(symbol, a, b) % s->hash_cap;
    for (size_t i = s->hash[at]; i; i = s->term[i].next)
        if (s->term[i].symbol == symbol && s->term[i].arg[0] == a && s->term[i].arg[1] == b) return i;
    size_t size = f->range == TRUTH ? 2 : m->dimension[f->range].size, id = sat_vector(s, size);
    if (s->broken) return 0;
    /* sat_vector puo aver spostato sia term sia hash. */
    SatTerm *out = &s->term[id];
    at = sat_term_hash(symbol, a, b) % s->hash_cap;
    out->symbol = symbol; out->arg[0] = a; out->arg[1] = b; out->next = s->hash[at]; s->hash[at] = id;
    size_t na = a ? m->dimension[f->domain[0]].size : 1, nb = b ? m->dimension[f->domain[1]].size : 1;
    for (size_t y = 0; y < nb && !s->broken; y++)
        for (size_t x = 0; x < na && !s->broken; x++) {
            SatLiteral la = a ? sat_at(s, a, x) : 1, lb = b ? sat_at(s, b, y) : 1;
            if (la == -1 || lb == -1) continue;
            size_t cell = s->table[symbol][x + y * na];
            for (size_t v = 0; v < size && !s->broken; v++)
                sat_clause(s, (SatLiteral[]){-la, -lb, -sat_at(s, cell, v), sat_at(s, id, v)}, 4);
        }
    return id;
}

/* Il vettore di un termine con i legami correnti. */
static size_t sat_element(SatState *s, const Model *m, const Elem *e) {
    if (s->broken) return 0;
    if (e->symbol < 0) return sat_constant(s, m->dimension[slot_data[e->slot].sort].size, s->slots[e->slot]);
    size_t a = e->arg[0] ? sat_element(s, m, e->arg[0]) : 0;
    size_t b = e->arg[1] ? sat_element(s, m, e->arg[1]) : 0;
    return sat_application(s, m, e->symbol, a, b);
}

/* Due vettori one-hot sono uguali se hanno lo stesso valore. Con un lato
 * costante basta un letterale; altrimenti ogni valore impone l'equivalenza. */
static SatLiteral sat_equal(SatState *s, size_t a, size_t b) {
    if (s->broken) return -1;
    if (a == b) return 1;
    size_t x = s->term[a].known, y = s->term[b].known;
    if (x != (size_t)-1) return sat_at(s, b, x);
    if (y != (size_t)-1) return sat_at(s, a, y);
    SatLiteral q = sat_variable(s);
    for (size_t v = 0; v < s->term[a].size && !s->broken; v++) {
        sat_clause(s, (SatLiteral[]){-q, -sat_at(s, a, v), sat_at(s, b, v)}, 3);
        sat_clause(s, (SatLiteral[]){q, -sat_at(s, a, v), -sat_at(s, b, v)}, 3);
    }
    return q;
}

/* Traduce i connettivi con Tseitin e i quantificatori con congiunzioni o
 * disgiunzioni finite. Gli insiemi vuoti danno le identita vere/falso; le
 * parti si enumerano con un vettore binario, senza shift di lunghezza n. */
static SatLiteral sat_sentence(SatState *s, const Model *m, const Sentence *f) {
    if (!sat_spend(s, 1)) return -1;
    SatLiteral a, b;
    switch (f->kind) {
    case S_TRUE: return 1;
    case S_EQUIPOTENT: {
        int equal = model_equipotent(m, f);
        if (!model_steps_complete()) s->broken = 1;
        return equal ? 1 : -1;
    }
    case S_EQUAL: {
        size_t left = sat_element(s, m, f->left), right = sat_element(s, m, f->right);
        return sat_equal(s, left, right);
    }
    case S_HOLDS: {
        size_t id = sat_element(s, m, f->left);
        return s->broken ? -1 : sat_at(s, id, 1);
    }
    case S_NOT: return -sat_sentence(s, m, f->a);
    case S_AND: case S_OR: case S_IMPLIES: case S_IFF:
        a = sat_sentence(s, m, f->a); b = sat_sentence(s, m, f->b);
        if (f->kind == S_AND) return sat_and(s, a, b);
        if (f->kind == S_OR) return sat_or(s, a, b);
        if (f->kind == S_IMPLIES) return sat_or(s, -a, b);
        return sat_or(s, sat_and(s, a, b), sat_and(s, -a, -b));
    case S_FORALL: case S_EXISTS: {
        int every = f->kind == S_FORALL;
        SatLiteral result = every ? 1 : -1;
        size_t saved = s->slots[f->slot];
        for (size_t x = 0; x < m->dimension[slot_data[f->slot].sort].size && !s->broken; x++) {
            s->slots[f->slot] = x; a = sat_sentence(s, m, f->a);
            result = every ? sat_and(s, result, a) : sat_or(s, result, a);
        }
        s->slots[f->slot] = saved;
        return result;
    }
    case S_FORALL_PART: case S_EXISTS_PART: {
        int every = f->kind == S_FORALL_PART;
        SatLiteral result = every ? 1 : -1;
        size_t n = m->dimension[symbols[f->part].domain[0]].size, cap = 0;
        unsigned char *saved = m->part[f->part], *bits = NULL;
        if (!sat_reserve(s, (void **)&bits, &cap, n ? n : 1, 1)) return -1;
        m->part[f->part] = bits;
        for (;;) {
            a = sat_sentence(s, m, f->a);
            result = every ? sat_and(s, result, a) : sat_or(s, result, a);
            if (s->broken || result == (every ? -1 : 1)) break;
            size_t bit = 0;
            while (bit < n && bits[bit]) bits[bit++] = 0;
            if (bit == n) break;
            bits[bit] = 1;
        }
        m->part[f->part] = saved; free(bits); s->bytes -= cap;
        return result;
    }
    case S_MEMBER: case S_INCLUDED: case S_SAME: case S_UNIQUE: case S_COUNT:
        s->broken = 1; return -1;
    }
    s->broken = 1; return -1;
}

/* Cerca un modello delle dimensioni correnti, spendendo il budget rimasto.
 * I dati estratti sono ricalcolati per intero, prima del successivo controllo
 * indipendente nel certificato. UNSAT e risorse finite ritornano entrambi 0. */
static int model_sat(const Sentence *root, int wanted, Model *m, unsigned long long *work) {
    if (*work >= model_work_limit) return 0;
    ++*work;
    if (!model_allocate(m)) { if (m->limited) *work = model_work_limit; return 0; }
    SatState s = {.bytes=m->bytes, .budget=model_work_limit - *work};
    if (!s.budget) return 0;
    sat_reserve(&s, (void **)&s.slots, &s.slots_cap, (size_t)slot_count, sizeof *s.slots);
    sat_variable(&s); sat_assign(&s, 1, 0);
    model_steps = 0;
    model_structure(m);
    sat_reserve(&s,(void **)&s.sort,&s.sort_cap,(size_t)sort_count,sizeof *s.sort);
    for (int i=0;i<sort_count && !s.broken;i++) s.sort[i].ordered_map=-1;
    for (int f = 0; f < symbol_count && !s.broken; f++) {
        int sort = symbols[f].range;
        if (sort < 0 || sort >= sort_count || sort_data[sort].kind != SORT_PLAIN || symbol_fixed(f) || symbol_bound[f]) continue;
        if (!symbols[f].arity) s.sort[sort].named++;
        if (symbols[f].arity == 1 && symbols[f].domain[0] == sort && s.sort[sort].ordered_map < 0) s.sort[sort].ordered_map = f;
    }
    sat_reserve(&s, (void **)&s.table, &s.table_cap, (size_t)symbol_count, sizeof *s.table);
    for (int f = 0; f < symbol_count && !s.broken; f++) {
        if (symbol_bound[f]) continue;
        size_t cells, values = model_cells(m, f, &cells), cap = 0;
        if (!sat_reserve(&s, (void **)&s.table[f], &cap, cells ? cells : 1, sizeof(size_t))) break;
        for (size_t c = 0; c < cells && !s.broken; c++) {
            size_t id = symbol_fixed(f) ? sat_constant(&s, values, m->table[f][c]) : sat_vector(&s, values);
            if (s.broken) break;
            s.table[f][c] = id;
            if (s.term[id].known == (size_t)-1)
                for (size_t v = 0; v < values; v++) s.var[sat_index(sat_at(&s, id, v))].phase = 1;
        }
        /* Rottura generale delle simmetrie. Numera prima gli elementi con
         * un nome, nell'ordine in cui appaiono: il j-esimo nome vale al piu
         * j, anche se due nomi coincidono. Poi visita una sola mappa S->S,
         * in ordine di argomento, dando a ogni elemento nuovo il prossimo
         * numero libero. Dopo i nomi e i argomenti, f(i) vale al piu k+i,
         * con k=max(1,numero dei nomi). Se non ci sono nomi si parte da un
         * elemento arbitrario. Ogni modello ammette questa rinumerazione;
         * non si ordina una seconda mappa, che potrebbe contraddirla. */
        int sort = symbols[f].range;
        if (!s.broken && sort >= 0 && sort < sort_count && sort_data[sort].kind == SORT_PLAIN) {
            if (!symbols[f].arity) {
                size_t last = s.sort[sort].seen++;
                for (size_t v = last + 1; v < values && !s.broken; v++) {
                    SatLiteral excluded = -sat_at(&s, s.table[f][0], v);
                    sat_clause(&s, &excluded, 1);
                }
            } else if (s.sort[sort].ordered_map == f) {
                size_t seed = s.sort[sort].named ? s.sort[sort].named : 1;
                for (size_t c = 0; c < cells && c < values && seed < values - c && !s.broken; c++)
                    for (size_t v = seed + c + 1; v < values && !s.broken; v++) {
                        SatLiteral excluded = -sat_at(&s, s.table[f][c], v);
                        sat_clause(&s, &excluded, 1);
                    }
            }
        }
    }
    SatLiteral truth = sat_sentence(&s, m, root);
    sat_clause(&s, (SatLiteral[]){wanted ? truth : -truth}, 1);
    int found = sat_solve(&s) == 1;
    if (found) {
        for (int f = 0; f < symbol_count && found; f++) {
            if (symbol_fixed(f) || symbol_bound[f]) continue;
            size_t cells; model_cells(m, f, &cells);
            for (size_t c = 0; c < cells; c++) {
                size_t id = s.table[f][c], value = 0;
                while (value < s.term[id].size && sat_value(&s, sat_at(&s, id, value)) <= 0) value++;
                if (value == s.term[id].size) { found = 0; break; }
                m->table[f][c] = value;
            }
        }
        size_t *value = s.slots;
        model_steps = 0;
        int confirmed = found && model_holds(m, root, value) == wanted;
        if (!confirmed && model_steps_complete()) unjustified_steps++;
        if (found && !model_steps_complete())
            model_unconfirmed = "trovato un modello candidato, ma ricalcolarvi l'enunciato supera il budget dei passi (--model-steps): non conta come controesempio";
        found = confirmed && model_steps_complete();
    }
    *work += s.work;

    /* Anche un modello che non si riesce a ricalcolare ferma la ricerca: i
     * modelli più grandi costerebbero di più, e il budget che manca è
     * quello dei passi, non quello della ricerca. */
    if (s.memory_limited || (!found && model_unconfirmed)) *work = model_work_limit;
    sat_clear(&s);
    return found;
}

/* Consuma visite delle coordinate e dei tipi senza overflow del contatore.
 * Un budget esaurito non e una risposta di UNSAT. */
static int model_visit(unsigned long long *work,unsigned long long count) {
    if (*work>model_work_limit || count>model_work_limit-*work) { *work=model_work_limit;return 0; }
    *work+=count;return 1;
}

/* Se la polarita richiede un testimone ordinario, il suo insieme non e
 * vuoto. Congiunzioni vere e disgiunzioni false obbligano entrambi i lati;
 * un'implicazione falsa obbliga premessa vera e conclusione falsa. Le altre
 * alternative non sono assunte. Un testimone di una parte non obbliga il
 * suo insieme base: anche l'insieme vuoto ha una parte. */
static int model_required_sorts(Model *m,const Sentence *s,int wanted,unsigned long long *work) {
    if (!s || !model_visit(work,1)) return s==NULL;
    if (s->kind==S_NOT) return model_required_sorts(m,s->a,!wanted,work);
    if ((s->kind==S_AND && wanted) || (s->kind==S_OR && !wanted))
        return model_required_sorts(m,s->a,wanted,work) && model_required_sorts(m,s->b,wanted,work);
    if (s->kind==S_IMPLIES && !wanted)
        return model_required_sorts(m,s->a,1,work) && model_required_sorts(m,s->b,0,work);
    if ((s->kind==S_EXISTS && wanted) || (s->kind==S_FORALL && !wanted)) {
        m->dimension[slot_data[s->slot].sort].minimum=1;
        return model_required_sorts(m,s->a,wanted,work);
    }
    if ((s->kind==S_EXISTS_PART && wanted) || (s->kind==S_FORALL_PART && !wanted))
        return model_required_sorts(m,s->a,wanted,work);
    return 1;
}

/* Limiti inferiori logicamente necessari, non scelte euristiche. Una
 * costante esige un valore; una funzione con argomenti in insiemi non
 * vuoti esige un codominio non vuoto. Il punto fisso propaga solo queste
 * implicazioni. Saltare cardinalita inferiori non perde alcun modello. */
static int model_minimums(Model *m,const Sentence *root,int wanted,unsigned long long *work) {
    if (!model_dimensions(m)) return 0;
    for (int i=0;i<sort_count;i++) {
        if (!model_visit(work,1)) return 0;
        m->dimension[i].minimum=sort_data[i].kind==SORT_PARTS || sort_data[i].kind==SORT_NUMBERS;
    }
    if (!model_required_sorts(m,root,wanted,work)) return 0;
    for (int changed=1;changed;) {
        changed=0;
        for (int f=0;f<symbol_count;f++) {
            if (!model_visit(work,1)) return 0;
            const Symbol *symbol=&symbols[f];
            if (symbol->range==TRUTH || m->dimension[symbol->range].minimum) continue;
            int nonempty=1;
            for (int a=0;a<symbol->arity;a++) nonempty &= m->dimension[symbol->domain[a]].minimum>0;
            if (nonempty) { m->dimension[symbol->range].minimum=1;changed=1; }
        }
    }
    return 1;
}

/* Enumera le composizioni dell'eccesso total oltre i limiti inferiori.
 * Per ogni totale sono finitissime, e ogni vettore ammissibile viene
 * raggiunto. Visite, modelli scartati e coordinata finale consumano lavoro;
 * nessuna ricorsione o potenza codifica il numero degli insiemi. */
static int model_sat_total(const Sentence *root,int wanted,Model *m,size_t total,
                           unsigned long long *work,int bound) {
    if (!model_dimensions(m) || !model_composition_start(m,total)) return 0;
    do {
        if (!model_visit(work,(unsigned long long)sort_count+1)) return 0;
        if (!model_composition_values(m,0)) continue;
        int small=bound>0;
        for (int i=0;i<sort_count;i++)
            if (sort_data[i].kind==SORT_PLAIN && (!m->dimension[i].size || m->dimension[i].size>(size_t)bound)) small=0;
        if (!small && model_sat(root,wanted,m,work)) return 1;
    } while (*work<model_work_limit && model_composition_next(m));
    return 0;
}

/* Prosegue dopo il prefisso esaustivo, senza una cardinalita o un numero
 * di tentativi massimi. Il budget totale di lavoro/memoria e esplicito e
 * configurabile; esaurirlo non autorizza un verdetto matematico positivo. */
static int model_sat_search(const Sentence *root, int wanted, Model *m, long long *tried, int bound) {
    unsigned long long work = 0;
    if (!model_minimums(m,root,wanted,&work)) return 0;
    for (size_t total = 0; work < model_work_limit; total++) {
        if (model_sat_total(root, wanted, m, total, &work, bound)) { ++*tried; return 1; }
        if (!plain_sorts() || total == (size_t)-1) break;
    }
    return 0;
}

/* Ritorna il numero che il pedice index scrive: index stesso, o 0 per
 * ZERO_INDEX (17v). */
static int index_digits(int index) { return index == ZERO_INDEX ? 0 : index; }

/* Scrive il nome del simbolo di posto symbol: la lettera, o il comando
 * LaTeX, con il pedice se c'è. */
static void put_symbol(int symbol) {
    const Symbol *s = &symbols[symbol];
    if (s->name >= NUMERAL_NAMES) { proof_add("%d", s->name - NUMERAL_NAMES); return; }
    if (s->name < 0) { proof_add(sort_data[symbol_structure(symbol)].kind == SORT_PARTS ? "\\in" : "\\operatorname{ev}"); return; }
    if (s->name >= RELATION_NAMES) proof_add("\\%s", relation_commands[s->name - RELATION_NAMES]);
    else if (s->name >= GREEK_NAMES) proof_add("\\%s", greek_letters[s->name - GREEK_NAMES]);
    else if (s->name >= OPERATION_NAMES) proof_add("\\%s", operation_symbols[s->name - OPERATION_NAMES]);
    else proof_add("%c", s->name);
    if (s->index <= LETTER_INDEX) proof_add("_{%c}", LETTER_INDEX - s->index);
    else if (s->index) proof_add("_{%d}", index_digits(s->index));
}

/* Scrive il nome dell'insieme di posto sort: la lettera, o (17v)
 * \mathcal{P}(S) e T^{S}. */
static void put_sort(int sort) {
    if (sort_data[sort].kind == SORT_PLAIN) {
        proof_add("%c", sort_data[sort].name);
        if (sort_data[sort].index) proof_add("_{%d}", sort_data[sort].index);  /* 17w */
        return;
    }
    if (sort_data[sort].kind == SORT_NUMBERS) {
        /* 17v. I numeri che l'enunciato scrive. */
        proof_add("\\{");
        for (int s = 0, written = 0; s < symbol_count; s++)
            if (symbols[s].name >= NUMERAL_NAMES && symbols[s].range == sort) { if (written++) proof_add(", "); put_symbol(s); }
        proof_add("\\}");
        return;
    }
    if (sort_data[sort].kind == SORT_PARTS) { proof_add("\\mathcal{P}("); put_sort(sort_data[sort].base); proof_add(")"); return; }
    put_sort(sort_data[sort].target);
    proof_add("^{");
    put_sort(sort_data[sort].base);
    proof_add("}");
}

/* Scrive l'elemento numero x dell'insieme di posto sort in un modello: la
 * minuscola della lettera dell'insieme, con il numero per pedice. Così gli
 * elementi di due insiemi diversi non si confondono. Un elemento di un
 * insieme di parti si scrive come la parte che è, \{s_{0}, s_{2}\}; uno di
 * un insieme di applicazioni con i suoi valori, (s_{0} \mapsto t_{1}, ...),
 * con la numerazione di 28m. */
static void put_model_element(const Model *m, int sort, size_t x) {
    if (sort_data[sort].kind == SORT_PLAIN && sort_data[sort].index) { proof_add("%c_{%d,%zu}", tolower(sort_data[sort].name), sort_data[sort].index, x); return; }  /* 17w */
    if (sort_data[sort].kind == SORT_PLAIN) { proof_add("%c_{%zu}", tolower(sort_data[sort].name), x); return; }
    if (sort_data[sort].kind == SORT_NUMBERS) {
        /* 17v. Il numero che l'elemento x rappresenta. */
        for (int s = 0; s < symbol_count; s++)
            if (symbols[s].name >= NUMERAL_NAMES && symbols[s].range == sort && (size_t)numeral_position(sort, s) == x) put_symbol(s);
        return;
    }
    proof_add(sort_data[sort].kind == SORT_PARTS ? "\\{" : "(");
    for (size_t a = 0, written = 0, rest = x; a < m->dimension[sort_data[sort].base].size; a++) {
        if (sort_data[sort].kind == SORT_PARTS && !(x >> a & 1)) continue;
        if (written++) proof_add(", ");
        put_model_element(m, sort_data[sort].base, a);
        if (sort_data[sort].kind == SORT_PARTS) continue;
        proof_add(" \\mapsto ");
        put_model_element(m, sort_data[sort].target, rest % m->dimension[sort_data[sort].target].size);
        rest /= m->dimension[sort_data[sort].target].size;
    }
    proof_add(sort_data[sort].kind == SORT_PARTS ? "\\}" : ")");
}

/* Scrive il modello m: gli insiemi, poi ogni simbolo dichiarato con la sua
 * tabella. Una parte e una relazione si scrivono come l'insieme degli
 * elementi, o delle coppie, per cui valgono. Gli insiemi di parti e di
 * applicazioni (17v) sono quelli veri: non si elencano, e il loro simbolo
 * di struttura non ha una tabella da dire. */
static void put_model(const Model *m) {
    for (int i = 0, written = 0; i < sort_count; i++) {
        /* 17v. I numeri scritti sono i soli elementi del loro insieme. */
        if (sort_data[i].kind == SORT_NUMBERS) { proof_add("%s$", written++ ? ", " : ""); put_sort(i); proof_add("$"); }
        if (sort_data[i].kind != SORT_PLAIN) continue;
        proof_add("%s$", written++ ? ", " : "");
        put_sort(i);
        proof_add(" = \\{");
        for (size_t x = 0; x < m->dimension[i].size; x++) { if (x) proof_add(", "); put_model_element(m, i, x); }
        proof_add("\\}$");
    }
    for (int s = 0; s < symbol_count; s++) {
        if (symbol_fixed(s)) continue;
        const Symbol *symbol = &symbols[s];
        size_t cells, first = m->dimension[symbol->arity ? symbol->domain[0] : 0].size, written = 0;
        if (symbol_bound[s]) continue;  /* una parte legata (28i) non ha tabella */
        model_cells(m, s, &cells);
        proof_add("; $");
        /* Una funzione con dominio vuoto e il grafico vuoto: la sua
         * dichiarazione va mostrata anche quando non ci sono celle. */
        if (!cells && symbol->range != TRUTH) { put_symbol(s); proof_add(" = \\emptyset$"); continue; }
        if (symbol->range == TRUTH) { put_symbol(s); proof_add(" = \\{"); }
        for (size_t c = 0; c < cells; c++) {
            if (symbol->range == TRUTH && !m->table[s][c]) continue;
            if (written++) proof_add(", ");

            /* Gli argomenti, come li si scrive nell'enunciato. */
            int infix = symbol->name >= OPERATION_NAMES && symbol->name < GREEK_NAMES;
            if (symbol->range != TRUTH && !infix) put_symbol(s);
            if (symbol->arity && !infix) proof_add(symbol->arity == 2 || symbol->range != TRUTH ? "(" : "");
            if (symbol->arity) put_model_element(m, symbol->domain[0], c % first);
            if (infix) { proof_add(" "); put_symbol(s); proof_add(" "); }
            else if (symbol->arity == 2) proof_add(", ");
            if (symbol->arity == 2) put_model_element(m, symbol->domain[1], c / first);
            if (symbol->arity && !infix) proof_add(symbol->arity == 2 || symbol->range != TRUTH ? ")" : "");
            if (symbol->range != TRUTH) { proof_add(" = "); put_model_element(m, symbol->range, m->table[s][c]); }
        }
        if (symbol->range == TRUTH) proof_add(written ? "\\}" : "\\} = \\emptyset");
        proof_add("$");
    }
}

/* 28h. LA NOTAZIONE DEI LIBRI, RICONTROLLATA SUI MODELLI
 *
 * (Sta qui, subito dopo 28a, perché usa i suoi modelli; la lettera è venuta
 * dopo le altre.)
 *
 * Il paragrafo 17q svolge la notazione dei libri sostituendo, sull'albero:
 * f(X) = f(Y) diventa "per ogni t, esiste u in X con f(u) = t se e solo se
 * ...". Un errore lì farebbe dimostrare un altro enunciato, e ogni controllo
 * successivo, compreso il certificato, lo confermerebbe, perché tutti
 * guardano l'enunciato svolto. Per questo l'enunciato com'è scritto si
 * calcola anche per un'altra strada, su molti modelli finiti, e deve dare
 * lo stesso valore di quello svolto.
 *
 * L'altra strada non sostituisce nulla. Per sapere se il membro t sta in
 * \{(x, y) \mid c\} prova ogni valore di x e di y e guarda se uno dà proprio
 * t e rende vera c, come dice la definizione ("esiste (x, y) uguale a t per
 * cui vale c"); per un'immagine prova ogni elemento del dominio; per
 * un'uguaglianza tra insiemi prova ogni membro possibile; per "esiste un
 * solo x" conta. Le lettere legate prendono i loro valori in value[], come
 * quelle dei quantificatori: è un ambiente, e una lettera non può prendere
 * il posto di un'altra. Le due strade hanno in comune solo l'albero letto e
 * le tabelle dei simboli.
 *
 * I modelli sono quelli di 28a: per ogni scelta delle grandezze degli
 * insiemi, dalla più piccola, tutte le tabelle se sono poche, altrimenti un
 * campione preso a caso con un seme fisso, fino a MAX_CHECK_MODELS modelli o
 * al limite di model_step_limit. Non dimostra che le due strade coincidano
 * sempre, e non serve: è il controllo contro gli errori dello svolgimento,
 * e un errore di sostituzione cambia l'enunciato quasi sempre già in un
 * modello di due o tre elementi.
 */

static int book_holds(const Model *m, const Sentence *s, size_t *value);

/* Ritorna 1 se il membro t[], di set->arity componenti già calcolate, sta
 * nell'insieme set del modello m, con le variabili libere ai valori di
 * value[]. Calcola dalla definizione, senza sostituire nulla (vedi la testa
 * del paragrafo); value[] viene usato anche per le lettere che set lega, e
 * rimesso com'era. */
static int book_member(const Model *m, const size_t *t, const SetTerm *set, size_t *value) {
    int found = 0;
    size_t saved[MAX_ARITY], arg;
    switch (set->kind) {
    case ST_SYMBOL:
        return model_cell(m, set->symbol, t[0], set->arity == 2 ? t[1] : 0);
    case ST_SECTION:
        return model_cell(m, set->symbol, t[0], model_element(m, set->item[0], value));
    case ST_SORT:
        return 1;
    case ST_EMPTY:
        return 0;
    case ST_LIST:
        for (int i = 0; i < set->items && !found; i++) found = t[0] == model_element(m, set->item[i], value);
        return found;
    case ST_BUILDER: {
        /* Ogni valore delle lettere dello schema, come un contachilometri:
         * t sta nell'insieme se uno di loro dà t e rende vera la condizione. */
        int possible = 1;
        for (int i = 0; i < set->bounds; i++) {
            saved[i] = value[set->bound[i]]; value[set->bound[i]] = 0;
            possible = possible && m->dimension[slot_data[set->bound[i]].sort].size != 0;
        }
        for (int more = possible; more && !found; ) {
            if (++model_steps > model_step_limit) break;
            int same = 1;
            for (int i = 0; i < set->arity && same; i++) same = value[set->item[i]->slot] == t[i];
            found = same && book_holds(m, set->condition, value);
            more = 0;
            for (int i = 0; i < set->bounds && !more; i++) {
                if (++value[set->bound[i]] < m->dimension[slot_data[set->bound[i]].sort].size) more = 1; else value[set->bound[i]] = 0;
            }
        }
        for (int i = 0; i < set->bounds; i++) value[set->bound[i]] = saved[i];
        return found;
    }
    case ST_IMAGE: case ST_PREIMAGE: {
        /* f(x) è la cella di x; per un elemento di T^{S} (17v), la cella di
         * (f, x) del simbolo di struttura. */
        size_t map = set->items ? model_element(m, set->item[0], value) : 0;
        int sort = symbols[set->symbol].domain[set->items];
        if (set->kind == ST_PREIMAGE) {
            arg = set->items ? model_cell(m, set->symbol, map, t[0]) : model_cell(m, set->symbol, t[0], 0);
            return book_member(m, &arg, set->a, value);
        }
        for (arg = 0; arg < m->dimension[sort].size && !found; arg++)
            found = (set->items ? model_cell(m, set->symbol, map, arg) : model_cell(m, set->symbol, arg, 0)) == t[0] && book_member(m, &arg, set->a, value);
        return found;
    }
    case ST_PART:
        /* 17v. La cella di (t, X) dell'appartenenza. */
        return model_cell(m, set->symbol, t[0], model_element(m, set->item[0], value));
    case ST_TUPLES:
        /* 17v. Uno dei membri dell'elenco, componente per componente. */
        for (int k = 0; k < set->items && !found; k++) {
            found = 1;
            for (int i = 0; i < set->arity && found; i++) found = model_element(m, set->tuple[k * set->arity + i], value) == t[i];
        }
        return found;
    case ST_REPLACE: {
        /* 17v. Ogni valore delle lettere nuove, come un contachilometri: t
         * sta nell'insieme se uno di loro rende vera la condizione e dà t,
         * come elemento o come la parte con gli stessi elementi di a. */
        int possible = 1;
        for (int i = 0; i < set->bounds; i++) {
            saved[i] = value[set->bound[i]]; value[set->bound[i]] = 0;
            possible = possible && m->dimension[slot_data[set->bound[i]].sort].size != 0;
        }
        for (int more = possible; more && !found; ) {
            if (++model_steps > model_step_limit) break;
            if (book_holds(m, set->condition, value)) {
                if (set->items) {
                    found = model_element(m, set->item[0], value) == t[0];
                } else {
                    found = 1;
                    for (arg = 0; arg < m->dimension[sort_data[set->sort[0]].base].size && found; arg++)
                        found = (int)model_cell(m, set->symbol, arg, t[0]) == book_member(m, &arg, set->a, value);
                }
            }
            more = 0;
            for (int i = 0; i < set->bounds && !more; i++) {
                if (++value[set->bound[i]] < m->dimension[slot_data[set->bound[i]].sort].size) more = 1; else value[set->bound[i]] = 0;
            }
        }
        for (int i = 0; i < set->bounds; i++) value[set->bound[i]] = saved[i];
        return found;
    }
    case ST_DESCRIBE: {
        /* 17v. Ogni parte Z con gli stessi elementi dell'insieme a (nei
         * modelli ce n'è una sola, 28m) dà t \in b. */
        int z = set->bound[0], sort = slot_data[z].sort, result = 1;
        saved[0] = value[z];
        for (size_t x = 0; x < m->dimension[sort].size && result; x++) {
            int same = 1;
            for (arg = 0; arg < m->dimension[sort_data[sort].base].size && same; arg++)
                same = (int)model_cell(m, sort_data[sort].symbol, arg, x) == book_member(m, &arg, set->a, value);
            if (!same) continue;
            value[z] = x;
            result = book_member(m, t, set->b, value);
        }
        value[z] = saved[0];
        return result;
    }
    case ST_POWERSET:
        /* 17v. Ogni elemento della parte t sta in a. */
        for (arg = 0; arg < m->dimension[sort_data[set->sort[0]].base].size; arg++)
            if (model_cell(m, set->symbol, arg, t[0]) && !book_member(m, &arg, set->a, value)) return 0;
        return 1;
    case ST_UNION:
        return book_member(m, t, set->a, value) || book_member(m, t, set->b, value);
    case ST_INTER:
        return book_member(m, t, set->a, value) && book_member(m, t, set->b, value);
    case ST_DIFF:
        return book_member(m, t, set->a, value) && !book_member(m, t, set->b, value);
    case ST_SYMDIFF:
        return book_member(m, t, set->a, value) != book_member(m, t, set->b, value);
    case ST_BIG_UNION: case ST_BIG_INTER: {
        /* Ogni valore dell'indice, nel suo insieme o nella sua parte. */
        int index = set->bound[0], every = set->kind == ST_BIG_INTER, result = every;
        saved[0] = value[index];
        for (size_t i = 0; i < m->dimension[slot_data[index].sort].size && result == every; i++) {
            if (set->symbol >= 0 && !model_cell(m, set->symbol, i, 0)) continue;
            if (set->b && !book_member(m, &i, set->b, value)) continue;
            value[index] = i;
            if (book_member(m, t, set->a, value) != every) result = !every;
        }
        value[index] = saved[0];
        return result;
    }
    }
    return 0;
}

/* Passa dal membro possibile t[] di set al successivo: le scelte delle
 * componenti nei loro insiemi, in ordine, a partire da quella con tutti
 * zeri. Ritorna 0, con t[] di nuovo a zero, quando sono finite. */
static int book_next(const Model *m, const SetTerm *set, size_t *t) {
    for (int i = 0; i < set->arity; i++) {
        if (++t[i] < m->dimension[set->sort[i]].size) return 1;
        t[i] = 0;
    }
    return 0;
}

/* Ritorna 1 se, per ogni membro possibile t (ogni scelta delle componenti
 * nei loro insiemi), "t sta in set" e "t sta in other" valgono come chiede
 * how: 0 per "il primo implica il secondo", 1 per "hanno lo stesso valore".
 * Con how = 2 ritorna 1 se c'è un t che sta in other e non in set. */
static int book_compare(const Model *m, const SetTerm *set, const SetTerm *other, int how, size_t *value) {
    size_t t[MAX_ARITY] = {0};
    for (int i = 0; i < set->arity; i++) if (!m->dimension[set->sort[i]].size) return how != 2;
    for (;;) {
        if (++model_steps > model_step_limit) return 0;
        int in_set = book_member(m, t, set, value), in_other = book_member(m, t, other, value);
        if (how == 0 && in_set && !in_other) return 0;
        if (how == 1 && in_set != in_other) return 0;
        if (how == 2 && in_other && !in_set) return 1;
        if (!book_next(m, set, t)) return how != 2;
    }
}

/* Ritorna 1 se la condizione s, scritta come nei libri (17p), vale nel
 * modello m, con le variabili libere ai valori di value[]. È model_holds()
 * per le condizioni di 17o, con in più i nodi di 17p calcolati dalla loro
 * definizione. Se model_steps supera model_step_limit la risposta non vuol
 * dire nulla. */
static int book_holds(const Model *m, const Sentence *s, size_t *value) {
    size_t t[MAX_ARITY];
    int count = 0, every;
    switch (s->kind) {
    case S_TRUE:    return 1;
    case S_EQUIPOTENT: return model_equipotent(m, s);
    case S_EQUAL:   return model_element(m, s->left, value) == model_element(m, s->right, value);
    case S_HOLDS:   return model_element(m, s->left, value);
    case S_NOT:     return !book_holds(m, s->a, value);
    case S_AND:     return book_holds(m, s->a, value) && book_holds(m, s->b, value);
    case S_OR:      return book_holds(m, s->a, value) || book_holds(m, s->b, value);
    case S_IMPLIES: return !book_holds(m, s->a, value) || book_holds(m, s->b, value);
    case S_IFF:     return book_holds(m, s->a, value) == book_holds(m, s->b, value);
    case S_MEMBER:
        for (int i = 0; i < s->items; i++) t[i] = model_element(m, s->item[i], value);
        return book_member(m, t, s->set, value);
    case S_INCLUDED:
        return book_compare(m, s->set, s->other, 0, value) && (!s->proper || book_compare(m, s->set, s->other, 2, value));
    case S_SAME:
        return book_compare(m, s->set, s->other, 1, value);
    case S_FORALL_PART: case S_EXISTS_PART:
        return model_part_quantifier(m, s, value, book_holds);
    case S_UNIQUE:
        /* Si contano gli elementi per cui vale. */
        for (size_t x = 0; x < m->dimension[slot_data[s->slot].sort].size && count < 2; x++) {
            if (++model_steps > model_step_limit) return 0;
            value[s->slot] = x;
            count += book_holds(m, s->a, value);
        }
        return count == 1;
    case S_COUNT: {
        /* 17x. Si contano i membri, uno per uno, fra tutti i possibili: è
         * la definizione, senza le variabili e le coppie dello svolgimento. */
        long long members = 0;
        memset(t, 0, sizeof t);
        for (int i = 0; i < s->set->arity; i++) if (!m->dimension[s->set->sort[i]].size) return s->least == 0;
        do {
            if (++model_steps > model_step_limit) return 0;
            members += book_member(m, t, s->set, value);
        } while (book_next(m, s->set, t));
        return members >= s->least && (s->most < 0 || members <= s->most);
    }
    case S_FORALL: case S_EXISTS:
        break;
    }
    every = s->kind == S_FORALL;
    for (size_t x = 0; x < m->dimension[slot_data[s->slot].sort].size; x++) {
        if (++model_steps > model_step_limit) return 0;
        value[s->slot] = x;
        if (book_holds(m, s->a, value) != every) return !every;
    }
    return every;
}

/* Dà alle tabelle di m valori presi a caso, con il generatore che parte da
 * *state: lo stesso seme dà gli stessi modelli, quindi lo stesso verdetto. */
static void book_random_tables(Model *m, unsigned *state) {
    for (int s = 0; s < symbol_count; s++) {
        if (symbol_fixed(s)) continue;
        size_t cells, values = model_cells(m, s, &cells);
        for (size_t c = 0; c < cells; c++) {
            *state ^= *state << 13;
            *state ^= *state >> 17;
            *state ^= *state << 5;
            m->table[s][c] = (*state % values);
        }
    }
}

/* Confronta l'enunciato com'è scritto, written, calcolato da book_holds(),
 * con quello svolto, unfolded, calcolato da model_holds(), sui modelli
 * descritti in testa al paragrafo. Ritorna quanti modelli ha confrontato, o
 * -1 se in uno i due valori sono diversi. */
static long long book_check(const Sentence *written, const Sentence *unfolded) {
    Model m={0};
    size_t *value=model_variables();
    if (work_allocation_failed || !model_dimensions(&m)) { model_clear(&m);return 0; }
    for (int i=0;i<sort_count;i++) m.dimension[i].minimum=sort_data[i].kind==SORT_PLAIN;
    unsigned state=2463534242u;
    unsigned long long visits=0,cost=(unsigned long long)sort_count+1;
    long long compared=0;
    model_steps=0;

    /* Le composizioni visitano direttamente i totali possibili: non
     * calcolano 4^sort_count e non attraversano codici di insiemi derivati.
     * La quota conta anche configurazioni scartate e scansioni dei tipi. */
    size_t last;
    if (!model_product((size_t)plain_sorts(),MAX_MODEL_SIZE-1,&last)) goto finished;
    for (size_t total=0;total<=last;total++) {
        model_composition_start(&m,total);
        do {
            if (cost>MAX_MODEL_WORK-visits) goto finished;
            visits+=cost;
            if (!model_composition_values(&m,MAX_MODEL_SIZE)) continue;

            /* Tutte le tabelle se sono al piu 256, altrimenti 256 a caso.
             * I simboli di struttura non si scelgono. La valutazione del
             * testo scritto resta indipendente da quella dello svolto. */
            double count=1;
            for (int f=0;f<symbol_count && count<=256;f++) {
                size_t cells,values=model_cells(&m,f,&cells);
                for (size_t c=0;c<cells && count<=256 && !symbol_fixed(f);c++) count*=values;
            }
            if (!model_allocate(&m)) continue;
            model_structure(&m);
            for (int tried=0,more=1;more;tried++) {
                if (count>256) book_random_tables(&m,&state);
                int book=book_holds(&m,written,value),plain=model_holds(&m,unfolded,value);
                if (!model_steps_complete()) goto finished;
                if (book!=plain) { model_clear(&m);return -1; }
                if (++compared>=MAX_CHECK_MODELS) goto finished;
                more=0;
                if (count>256) { more=tried+1<256;continue; }
                for (int f=0;f<symbol_count && !more;f++) {
                    if (symbol_fixed(f)) continue;
                    size_t cells,values=model_cells(&m,f,&cells);
                    for (size_t c=0;c<cells && !more;c++) {
                        if (++m.table[f][c]<values) more=1;else m.table[f][c]=0;
                    }
                }
            }
            model_tables_clear(&m);
        } while (model_composition_next(&m));
    }
finished:
    model_clear(&m);
    return compared;
}

/* Scrive nella dimostrazione che la notazione degli insiemi è stata svolta,
 * e su quanti modelli lo svolgimento è stato ricontrollato: compared, che è
 * 0 se non c'era nulla da svolgere, e allora non scrive nulla. */
static void put_unfolding_note(long long compared) {
    if (!compared) return;
    proof_add(" The notation of sets (sets of elements or of pairs given by a rule, images and preimages, equalities and "
              "inclusions between sets, numbers of elements) is read as the conditions on elements it stands for, and that is the statement "
              "written above; the statement as written and that one take the same value in each of the %lld finite models "
              "tried.", compared);
}

/* 28b. GLI ELEMENTI DI CUI SI PARLA */

/* Un elemento nominato in una dimostrazione: un simbolo applicato ad altri
 * elementi, già in tabella. Due scritture uguali sono lo stesso posto della
 * tabella, quindi "scritti allo stesso modo" si controlla confrontando due
 * numeri. Il posto 0 è riservato a "vero", il valore di una parte o di una
 * relazione che vale: così x \in X è l'uguaglianza X(x) = vero, e le regole
 * sulle uguaglianze servono anche per le appartenenze. */
typedef struct {
    int symbol;    /* posto in symbols[]; -1 per "vero", senza troncamenti a 16 bit */
    short arg[2];  /* gli argomenti, posti in questa tabella; -1 dove mancano */
} Ground;

/* La tabella degli elementi. È una sola per tutti i rami della ricerca: un
 * ramo ne usa i primi now->grounds posti, e chi torna a un ramo precedente
 * riusa i posti dopo. */
static Ground ground[MAX_GROUND];

/* Una sostituzione finita delle variabili astratte con elementi presenti.
 * count e il numero di celle possedute nell'arena, data i valori (indici
 * di ground, oppure -1 per una variabile non sostituita). Le celle oltre
 * count valgono sempre -1: gli assiomi possono creare slot dopo una copia.
 * I Known conservano copie immutabili; solo i vettori temporanei di una
 * ricerca vengono modificati. La durata e quella dell'arena della prova. */
typedef struct { int count; short *data; } SlotValues;

/* La sostituzione vuota vale per qualsiasi numero di variabili. */
#define SLOT_VALUES_EMPTY ((SlotValues){0})

/* Legge una sostituzione, compresi i posti creati dopo il suo snapshot. */
static inline int slot_values_get(SlotValues values, int slot) {
    return slot >= 0 && slot < values.count ? values.data[slot] : -1;
}

/* Copia source in un vettore temporaneo gia dimensionato per tutti gli
 * slot correnti. Il suffisso non presente nello snapshot resta non legato;
 * nessuna cella del Known da cui proviene la copia viene modificata. */
static void slot_values_load(SlotValues target, SlotValues source) {
    if (target.count < source.count) {
        work_allocation_failed = 1; fail(OUT_OF_MEMORY); return;
    }
    if (source.count) memcpy(target.data, source.data, (size_t)source.count * sizeof *source.data);
    for (int i = source.count; i < target.count; i++) target.data[i] = -1;
}

/* Crea una copia indipendente con spazio per tutti gli slot correnti.
 * La copia vuota non alloca. Ogni chiamante controlla il fallimento prima
 * di scrivere: un vettore parziale non puo diventare una deduzione. */
static SlotValues slot_values_copy(SlotValues source) {
    int count = slot_count > source.count ? slot_count : source.count;
    if (!count) return SLOT_VALUES_EMPTY;
    short *data = work_arena_array((size_t)count, sizeof *data);
    if (!data) return SLOT_VALUES_EMPTY;
    SlotValues copy = {count, data};
    slot_values_load(copy, source);
    return copy;
}

/* Ciò che si sa in un ramo: una condizione dell'enunciato, con il segno con
 * cui è vera e con un elemento al posto di ogni variabile libera. Come ci
 * si è arrivati lo dicono origin e parent: serve a scrivere la
 * dimostrazione e a ricontrollarla. */
typedef enum {
    K_GIVEN,     /* un'ipotesi dell'enunciato */
    K_DENIED,    /* la tesi, supposta falsa */
    K_PART,      /* 28-1: segue da parent, date le condizioni già decise */
    K_INSTANCE,  /* 28-3: parent, un "per ogni", su degli elementi */
    K_NAMED,     /* 28-2: parent, un "esiste", su un elemento con un nome nuovo */
    K_CASE,      /* 28-5: uno dei due casi lasciati aperti da parent */
    K_DEFINED,   /* 28j: la definizione di una parte nuova, data da una regola */
    K_BIJECTION, /* 28q: parent è un'equipotenza; vera, le identità di una
                    biiezione nuova e della sua inversa (28q-1); falsa, la
                    loro negazione per due applicazioni costruite (28q-2) */
    K_MAPDEF     /* 28q: la definizione di un'applicazione nuova (d1-d3) */
} Origin;

/* A che punto è una condizione nota. */
typedef enum {
    K_NEW,      /* appena aggiunta: va ancora guardata */
    K_DONE,     /* usata: è un fatto, oppure le sue conseguenze sono in elenco */
    K_WAITING,  /* una disgiunzione di cui non si sa ancora quale parte valga */
    K_RULE      /* un "per ogni": dà un'istanza per ogni elemento */
} Stage;

/* Una condizione nota (vedi Origin). Se è un confronto tra due elementi è un
 * "fatto", e left e right dicono quali: uguali se negated è 0, diversi se è
 * 1. Per un'appartenenza right è 0, "vero".
 *
 * Invariante: source non è una negazione (le negazioni sono nel segno), e
 * parent, quando c'è, viene prima nell'elenco. Sostituzioni e parti sono
 * snapshot nell'arena: copiarli in un ramo non introduce memoria mutabile
 * condivisa, e nessun prefisso di quantificatori viene troncato. */
typedef struct {
    const Sentence *source;  /* la condizione, com'è nell'enunciato */
    signed char negated;     /* 1 se è vera la sua negazione */
    signed char origin;      /* un Origin */
    signed char stage;       /* uno Stage */
    short parent;            /* da quale condizione viene; -1 se da nessuna */
    short left, right;       /* fatto: i due elementi; -1 altrimenti */
    int stamp;               /* numero d'ordine: vedi Branch.clock */
    SlotValues value;       /* snapshot immutabile delle sostituzioni */
    int parts;              /* numero di simboli nella copia immutabile part */
    const int *part;      /* 28j: per un'istanza di un "per ogni parte", la
                                parte al posto di ogni parte legata, dalla più
                                esterna; per un nome dato a una parte (K_NAMED)
                                o per una definizione (K_DEFINED), in part[0]
                                la parte nuova. 28q: per K_BIJECTION le
                                applicazioni delle identità, prima le
                                componenti di quella da A a B, poi quelle
                                dell'inversa; per K_MAPDEF, in part[0]
                                l'applicazione definita. Posti in symbols[];
                                nell'arena della prova; NULL se parts = 0 */
} Known;

/* Un ramo della ricerca: tutto ciò che si sa dopo certe scelte di casi.
 *
 * Le uguaglianze note sono tenute in due modi. rep[] dà per ogni elemento
 * il rappresentante della sua classe: due elementi sono uguali, per ciò che
 * si sa, quando hanno lo stesso rappresentante. up[] e why[] ricordano
 * perché: formano una foresta in cui ogni arco t - up[t] è un'uguaglianza
 * tra i due elementi, nota come fatto (why = il suo posto in known[])
 * oppure ottenuta sostituendo uguali negli argomenti (why = CONGRUENT). Due
 * elementi della stessa classe sono collegati da un solo cammino, che non
 * cambia più: gli archi si aggiungono solo tra classi diverse. Quel cammino
 * è la catena di uguaglianze da scrivere.
 *
 * clock numera le condizioni nell'ordine in cui vengono aggiunte: un passo
 * della dimostrazione può usare solo ciò che ha un numero più basso del
 * suo. */
typedef struct {
    Known known[MAX_KNOWN];
    int knowns;
    short rep[MAX_GROUND], up[MAX_GROUND], why[MAX_GROUND];
    short different[MAX_DIFFERENT];  /* i fatti "diversi", posti in known[] */
    int differents;
    int grounds;                     /* elementi in uso nella tabella */
    int symbols;                     /* simboli in uso, compresi i nomi nuovi */
    int clock;
} Branch;

/* Valore di Branch.why per un arco che non è un fatto: i due elementi sono
 * uguali perché hanno lo stesso simbolo e argomenti uguali (28-4). */
#define CONGRUENT (-1)

/* I rami, uno per profondità (una distinzione di casi, una scelta di parti
 * di 28k o un caso provato da 28l ne aggiungono uno), e quello in cui si sta
 * lavorando. */
static Branch branch[MAX_BRANCHES];
static Branch *now;

/* 1 se la ricerca si è fermata perché una tabella è piena: allora non aver
 * trovato una dimostrazione non dice nulla. */
static int exhausted;

/* Come si è chiuso l'ultimo ramo: il fatto "diversi" i cui due elementi sono
 * risultati uguali, oppure la disgiunzione di cui ogni parte è falsa. Uno
 * solo dei due non è -1. */
static int clash_fact, clash_choice;

/* Tabelle per ritrovare un elemento senza scorrere tutto l'elenco: per
 * scrittura (exact) e, tra una chiusura e l'altra, per classi degli
 * argomenti (classes). Contengono posti di ground[], o -1. */
static short exact[4 * MAX_GROUND], classes[4 * MAX_GROUND];

/* Ritorna il posto da cui cominciare a cercare, in una delle due tabelle,
 * il simbolo symbol applicato ad a e b. */
static unsigned ground_hash(int symbol, int a, int b) {
    return ((unsigned)symbol * 31u + (unsigned)(a + 1)) * 2053u + (unsigned)(b + 1);
}

/* Modi di cercare un elemento (vedi ground_lookup()). */
typedef enum { G_EXACT, G_CREATE, G_CLASS } Lookup;

/* Ritorna il posto dell'elemento "symbol applicato ad a e b", o -1.
 *
 *   G_EXACT:  quello scritto proprio così, se è in tabella;
 *   G_CREATE: come sopra, e se manca lo aggiunge (se la tabella è piena
 *             annota exhausted e ritorna -1);
 *   G_CLASS:  uno qualsiasi in tabella i cui argomenti siano uguali ad a e
 *             b per ciò che si sa. Vale solo subito dopo closure(). */
static int ground_lookup(int symbol, int a, int b, Lookup mode) {
    unsigned size = sizeof exact / sizeof *exact;
    if (mode == G_CLASS && a >= 0) {
        int ra = now->rep[a], rb = b >= 0 ? now->rep[b] : -1;
        for (unsigned h = ground_hash(symbol, ra, rb) % size; classes[h] >= 0; h = (h + 1) % size) {
            const Ground *g = &ground[classes[h]];
            if (g->symbol == symbol && now->rep[g->arg[0]] == ra && (g->arg[1] >= 0 ? now->rep[g->arg[1]] : -1) == rb) return classes[h];
        }
        return -1;
    }
    unsigned h = ground_hash(symbol, a, b) % size;
    for (; exact[h] >= 0; h = (h + 1) % size) {
        const Ground *g = &ground[exact[h]];
        if (g->symbol == symbol && g->arg[0] == a && g->arg[1] == b) return exact[h];
    }
    if (mode != G_CREATE) return -1;
    if (now->grounds == MAX_GROUND) { exhausted = 1; return -1; }

    /* Un elemento nuovo: da solo nella sua classe. */
    int id = now->grounds++;
    ground[id] = (Ground){symbol, {(short)a, (short)b}};
    now->rep[id] = (short)id;
    now->up[id] = -1;
    exact[h] = (short)id;
    return id;
}

/* Rifà la tabella exact per gli elementi del ramo corrente: va chiamata
 * quando si cambia ramo, perché i posti dopo now->grounds non valgono più. */
static void ground_reindex(void) {
    unsigned size = sizeof exact / sizeof *exact;
    memset(exact, -1, sizeof exact);
    for (int id = 0; id < now->grounds; id++) {
        unsigned h = ground_hash(ground[id].symbol, ground[id].arg[0], ground[id].arg[1]) % size;
        while (exact[h] >= 0) h = (h + 1) % size;
        exact[h] = (short)id;
    }
}

/* Ritorna il posto dell'elemento che e indica quando ogni variabile vale
 * l'elemento di value[]; -1 se manca dalla tabella, -2 se e contiene una
 * variabile non ancora sostituita. mode è G_EXACT o G_CREATE, come in
 * ground_lookup(). */
static int elem_ground(const Elem *e, SlotValues value, Lookup mode) {
    int arg[2] = {-1, -1};
    if (e->symbol < 0) return slot_values_get(value, e->slot) >= 0 ? slot_values_get(value, e->slot) : -2;
    for (int i = 0; i < 2 && e->arg[i]; i++) {
        arg[i] = elem_ground(e->arg[i], value, mode);
        if (arg[i] < 0) return arg[i];
    }

    return ground_lookup(e->symbol, arg[0], arg[1], mode);
}

/* Scrive l'elemento di posto id. tight chiede le parentesi intorno a
 * un'operazione scritta tra i suoi operandi. */
static void put_ground(int id, int tight) {
    const Ground *g = &ground[id];
    if (g->symbol < 0) { proof_add("\\top"); return; }
    int name = symbols[g->symbol].name;
    if (symbol_structure(g->symbol) >= 0) {
        /* 17v. L'applicazione di un elemento di T^{S}, f(x). */
        put_ground(g->arg[0], 1);
        proof_add("\\left(");
        put_ground(g->arg[1], 0);
        proof_add("\\right)");
        return;
    }
    if (name >= OPERATION_NAMES && name < GREEK_NAMES) {
        if (tight) proof_add("\\left(");
        put_ground(g->arg[0], 1);
        proof_add(" ");
        put_symbol(g->symbol);
        proof_add(" ");
        put_ground(g->arg[1], 1);
        if (tight) proof_add("\\right)");
        return;
    }
    put_symbol(g->symbol);
    if (g->arg[0] < 0) return;
    proof_add("\\left(");
    put_ground(g->arg[0], 0);
    if (g->arg[1] >= 0) { proof_add(", "); put_ground(g->arg[1], 0); }
    proof_add("\\right)");
}

/* Scrive il nome della variabile di posto slot: la lettera, con il pedice se
 * c'è. */
static void put_slot(int slot) {
    proof_add("%c", slot_data[slot].letter);
    if (slot_data[slot].index) proof_add("_{%d}", index_digits(slot_data[slot].index));
}

/* Scrive l'elemento e, con gli elementi di value[] al posto delle variabili
 * sostituite e la lettera per le altre. */
static void put_elem(const Elem *e, SlotValues value, int tight) {
    if (e->symbol < 0) {
        if (slot_values_get(value, e->slot) >= 0) put_ground(slot_values_get(value, e->slot), tight); else put_slot(e->slot);
        return;
    }
    int name = symbols[e->symbol].name;
    if (symbol_structure(e->symbol) >= 0) {
        /* 17v. L'applicazione di un elemento di T^{S}, f(x). */
        put_elem(e->arg[0], value, 1);
        proof_add("\\left(");
        put_elem(e->arg[1], value, 0);
        proof_add("\\right)");
        return;
    }
    if (name >= OPERATION_NAMES && name < GREEK_NAMES) {
        if (tight) proof_add("\\left(");
        put_elem(e->arg[0], value, 1);
        proof_add(" ");
        put_symbol(e->symbol);
        proof_add(" ");
        put_elem(e->arg[1], value, 1);
        if (tight) proof_add("\\right)");
        return;
    }
    put_symbol(e->symbol);
    if (!e->arg[0]) return;
    proof_add("\\left(");
    put_elem(e->arg[0], value, 0);
    if (e->arg[1]) { proof_add(", "); put_elem(e->arg[1], value, 0); }
    proof_add("\\right)");
}

/* 17w. Scrive il lato k dell'equipotenza s: un insieme, o il prodotto di
 * due. */
static void put_equipotent_side(const Sentence *s, int k) {
    for (int i = 0; i < s->sides[k]; i++) {
        if (i) proof_add(" \\times ");
        put_sort(slot_data[s->side_slot[k][i]].sort);
    }
}

/* Scrive la condizione s, negata se negated, con gli elementi di value[] al
 * posto delle variabili sostituite. tight chiede le parentesi intorno a ciò
 * che non è un confronto. */
static void put_sentence(const Sentence *s, int negated, SlotValues value, int tight) {
    static const char *const connective[] = {[S_AND] = "\\land", [S_OR] = "\\lor", [S_IMPLIES] = "\\implies", [S_IFF] = "\\iff"};
    switch (s->kind) {
    case S_TRUE:
        proof_add(negated ? "\\bot" : "\\top");
        return;
    case S_EQUIPOTENT:
        put_equipotent_side(s, 0);
        proof_add(negated ? " \\not\\sim " : " \\sim ");
        put_equipotent_side(s, 1);
        return;
    case S_NOT:
        put_sentence(s->a, !negated, value, tight);
        return;
    case S_EQUAL:
        put_elem(s->left, value, 0);
        proof_add(negated ? " \\neq " : " = ");
        put_elem(s->right, value, 0);
        return;
    case S_HOLDS:
        /* Una parte: x \in X. Una relazione: (x, y) \in R. Una famiglia di
         * parti (17p): x \in X_{i}. */
        if (symbols[s->left->symbol].family) {
            put_elem(s->left->arg[0], value, 0);
            proof_add(negated ? " \\notin " : " \\in ");
            put_symbol(s->left->symbol);
            proof_add("_{");
            put_elem(s->left->arg[1], value, 0);
            proof_add("}");
            return;
        }
        if (symbol_structure(s->left->symbol) >= 0) {
            /* 17v. L'appartenenza a un elemento di \mathcal{P}(S): t \in X. */
            put_elem(s->left->arg[0], value, 0);
            proof_add(negated ? " \\notin " : " \\in ");
            put_elem(s->left->arg[1], value, 0);
            return;
        }
        if (symbols[s->left->symbol].name >= RELATION_NAMES) {
            /* 17v. Una relazione scritta con un comando: x \le y. */
            if (negated) proof_add("\\lnot (");
            put_elem(s->left->arg[0], value, 0);
            proof_add(" ");
            put_symbol(s->left->symbol);
            proof_add(" ");
            put_elem(s->left->arg[1], value, 0);
            if (negated) proof_add(")");
            return;
        }
        if (s->left->arg[1]) proof_add("(");
        put_elem(s->left->arg[0], value, 0);
        if (s->left->arg[1]) { proof_add(", "); put_elem(s->left->arg[1], value, 0); proof_add(")"); }
        proof_add(negated ? " \\notin " : " \\in ");
        put_symbol(s->left->symbol);
        return;
    case S_AND: case S_OR: case S_IMPLIES: case S_IFF:
        if (negated) proof_add("\\lnot ");
        if (negated || tight) proof_add("(");
        put_sentence(s->a, 0, value, 1);
        proof_add(" %s ", connective[s->kind]);
        put_sentence(s->b, 0, value, 1);
        if (negated || tight) proof_add(")");
        return;
    case S_FORALL: case S_EXISTS:
        proof_add("%s\\%s ", negated ? "\\lnot " : "", s->kind == S_FORALL ? "forall" : "exists");
        put_slot(s->slot);
        proof_add(" \\in ");
        put_sort(slot_data[s->slot].sort);
        proof_add("\\ (");
        put_sentence(s->a, 0, value, 0);
        proof_add(")");
        return;
    case S_FORALL_PART: case S_EXISTS_PART:
        proof_add("%s\\%s ", negated ? "\\lnot " : "", s->kind == S_FORALL_PART ? "forall" : "exists");
        put_symbol(s->part);
        proof_add(" \\subseteq ");
        put_sort(symbols[s->part].domain[0]);
        proof_add("\\ (");
        put_sentence(s->a, 0, value, 0);
        proof_add(")");
        return;
    case S_MEMBER: case S_INCLUDED: case S_SAME: case S_UNIQUE: case S_COUNT:
        /* Non arrivano qui: lo svolgimento (17q) li toglie. */
        return;
    }
}

/* 28c. CIÒ CHE SI SA: UGUAGLIANZE, CLASSI, CATENE */

/* 28-4. Annota che gli elementi a e b, di classi diverse, sono uguali, per
 * la ragione reason: un fatto, o CONGRUENT. Le due classi diventano una, e
 * nella foresta nasce l'arco a - b.
 *
 * Perché l'arco possa partire da a, a deve essere la radice del suo albero:
 * prima si rovesciano gli archi da a alla vecchia radice, che restano le
 * stesse uguaglianze lette nell'altro verso. */
static void classes_join(int a, int b, int reason) {
    int node = a, above = now->up[a], why = now->why[a];
    while (above >= 0) {
        int next = now->up[above], next_why = now->why[above];
        now->up[above] = (short)node;
        now->why[above] = (short)why;
        node = above;
        above = next;
        why = next_why;
    }
    now->up[a] = (short)b;
    now->why[a] = (short)reason;
    for (int from = now->rep[a], to = now->rep[b], id = 0; id < now->grounds; id++)
        if (now->rep[id] == from) now->rep[id] = (short)to;
}

/* 28-4. Chiusura per congruenza: finché due elementi hanno lo stesso
 * simbolo e argomenti uguali per ciò che si sa, ma stanno in classi
 * diverse, li unisce. Al ritorno la tabella `classes` è aggiornata.
 *
 * A ogni giro la tabella viene rifatta: ogni elemento vi entra con la
 * "firma" data dal simbolo e dalle classi degli argomenti, e se la firma
 * c'è già i due elementi sono uguali. Un'unione cambia le classi, quindi le
 * firme, e il giro ricomincia. */
static void closure(void) {
    unsigned size = sizeof classes / sizeof *classes;
    for (int changed = 1; changed; ) {
        changed = 0;
        memset(classes, -1, sizeof classes);
        for (int id = 1; id < now->grounds && !changed; id++) {
            const Ground *g = &ground[id];
            if (g->arg[0] < 0) continue;
            int found = ground_lookup(g->symbol, g->arg[0], g->arg[1], G_CLASS);
            if (found >= 0 && now->rep[found] != now->rep[id]) { classes_join(id, found, CONGRUENT); changed = 1; }
            if (found >= 0) continue;
            unsigned h = ground_hash(g->symbol, now->rep[g->arg[0]], g->arg[1] >= 0 ? now->rep[g->arg[1]] : -1) % size;
            while (classes[h] >= 0) h = (h + 1) % size;
            classes[h] = (short)id;
        }
    }
}

/* Ritorna il posto in known[] di un fatto "diversi" tra la classe di a e
 * quella di b, o -1 se non se ne conosce nessuno. */
static int different_fact(int a, int b) {
    for (int i = 0; i < now->differents; i++) {
        const Known *k = &now->known[now->different[i]];
        int l = now->rep[k->left], r = now->rep[k->right];
        if ((l == now->rep[a] && r == now->rep[b]) || (l == now->rep[b] && r == now->rep[a])) return now->different[i];
    }
    return -1;
}

/* Mette in node[] il cammino nella foresta dall'elemento a all'elemento b,
 * estremi compresi, e ritorna quanti archi ha; -1 se a e b non sono
 * collegati o se il cammino ha più di max archi.
 *
 * Si sale da a fino alla radice, poi da b finché si incontra il cammino di
 * a: quello è il punto in cui i due si congiungono. */
static int forest_path(int a, int b, short *node, int max) {
    short from_a[MAX_GROUND], from_b[MAX_CHAIN + 1];
    int count_a = 0, count_b = 0, meet = -1;
    for (int t = a; t >= 0; t = now->up[t]) from_a[count_a++] = (short)t;
    for (int t = b; t >= 0 && meet < 0; t = now->up[t]) {
        for (int i = 0; i < count_a && meet < 0; i++)
            if (from_a[i] == t) meet = i;
        if (meet < 0) { if (count_b == max) return -1; from_b[count_b++] = (short)t; }
    }
    if (meet < 0 || meet + count_b > max) return -1;
    for (int i = 0; i <= meet; i++) node[i] = from_a[i];
    for (int i = 0; i < count_b; i++) node[meet + 1 + i] = from_b[count_b - 1 - i];
    return meet + count_b;
}

/* Una catena di uguaglianze t_0 = t_1 = ... = t_n: ogni anello cambia un
 * solo punto del termine, usando un fatto. */
typedef struct {
    int links;                  /* n */
    short term[MAX_CHAIN + 1];  /* t_0, ..., t_n: posti in ground[] */
    short fact[MAX_CHAIN];      /* fact[i] giustifica t_i = t_{i+1}: posto in known[] */
} Chain;

/* Allunga la catena c, che finisce con l'elemento a, fino all'elemento b,
 * seguendo il cammino della foresta. Ritorna 0 se a e b non sono collegati
 * o se la catena diventa troppo lunga.
 *
 * Un arco che è un fatto è un anello. Un arco di congruenza, tra f(a1, a2)
 * e f(b1, b2), si svolge: prima la catena da a1 a b1 dentro f(_, a2), poi
 * quella da a2 a b2 dentro f(b1, _). I termini intermedi possono non
 * essere in tabella, e vengono aggiunti: servono solo a essere scritti. */
static int chain_extend(Chain *c, int a, int b) {
    short node[MAX_CHAIN + 1];
    int edges = forest_path(a, b, node, MAX_CHAIN);
    if (edges < 0) return 0;
    for (int i = 0; i < edges; i++) {
        int low = now->up[node[i]] == node[i + 1] ? node[i] : node[i + 1], reason = now->why[low];
        if (reason != CONGRUENT) {
            if (c->links == MAX_CHAIN) return 0;
            c->fact[c->links++] = (short)reason;
            c->term[c->links] = node[i + 1];
            continue;
        }

        /* Un argomento per volta: inner è la catena tra i due argomenti,
         * e ogni suo anello diventa un anello tra due applicazioni. */
        const Ground from = ground[node[i]], to = ground[node[i + 1]];
        for (int side = 0; side < 2 && from.arg[side] >= 0; side++) {
            Chain inner = {0, {from.arg[side]}, {0}};
            if (!chain_extend(&inner, from.arg[side], to.arg[side])) return 0;
            for (int j = 0; j < inner.links; j++) {
                int step = side ? ground_lookup(from.symbol, to.arg[0], inner.term[j + 1], G_CREATE)
                                : ground_lookup(from.symbol, inner.term[j + 1], from.arg[1], G_CREATE);
                if (step < 0 || c->links == MAX_CHAIN) return 0;
                c->fact[c->links++] = inner.fact[j];
                c->term[c->links] = (short)step;
            }
        }
    }
    return 1;
}

/* Controllo di un anello, indipendente dalle classi: ritorna 1 se
 * l'elemento v si ottiene dall'elemento u sostituendo, in un solo punto, l
 * con r oppure r con l. Guarda solo come i due elementi sono scritti: o
 * sono proprio l e r, oppure hanno lo stesso simbolo, un argomento identico
 * e l'altro che si ottiene allo stesso modo. */
static int rewrites(int u, int v, int l, int r) {
    if ((u == l && v == r) || (u == r && v == l)) return 1;
    const Ground *a = &ground[u], *b = &ground[v];
    if (a->symbol != b->symbol || a->arg[0] < 0) return 0;
    int first = a->arg[0] == b->arg[0], second = a->arg[1] == b->arg[1];
    if (first == second) return 0;
    return first ? rewrites(a->arg[1], b->arg[1], l, r) : rewrites(a->arg[0], b->arg[0], l, r);
}

/* Mette in *c la catena di uguaglianze dall'elemento a all'elemento b
 * fatta solo di fatti con numero d'ordine minore di stamp, e la
 * ricontrolla anello per anello con rewrites(). Ritorna 1 se la catena
 * esiste e supera il controllo; 0 se a e b non risultavano uguali a quel
 * punto. Un anello che non supera il controllo è un errore del programma:
 * lo registra unjustified_steps. */
static int chain_between(Chain *c, int a, int b, int stamp) {
    c->links = 0;
    c->term[0] = (short)a;
    if (now->rep[a] != now->rep[b] || !chain_extend(c, a, b)) return 0;
    for (int i = 0; i < c->links; i++) {
        const Known *fact = &now->known[c->fact[i]];
        if (fact->stamp >= stamp) return 0;
        if (fact->negated || fact->left < 0 || !rewrites(c->term[i], c->term[i + 1], fact->left, fact->right)) { unjustified_steps++; return 0; }
    }
    return 1;
}

/* 28d. LA RICERCA */

/* Aggiunge all'elenco del ramo la condizione source, vera con il segno
 * negated e con gli elementi di value[] al posto delle variabili, arrivata
 * da parent nel modo origin. Ritorna il suo posto, o -1 se l'elenco è
 * pieno. Le negazioni in testa passano nel segno. */
static int known_add(const Sentence *source, int negated, SlotValues value, Origin origin, int parent) {
    if (work_allocation_failed) { exhausted = 1; return -1; }
    while (source->kind == S_NOT) { source = source->a; negated = !negated; }
    if (now->knowns == MAX_KNOWN) { exhausted = 1; return -1; }
    Known *k = &now->known[now->knowns];
    k->source = source;
    k->negated = (signed char)negated;
    k->origin = (signed char)origin;
    k->stage = K_NEW;
    k->parent = (short)parent;
    k->left = k->right = -1;
    k->stamp = now->clock++;
    k->value = slot_values_copy(value);
    if (work_allocation_failed) { exhausted = 1; return -1; }
    k->parts = 0;
    k->part = NULL;
    return now->knowns++;
}

/* Conserva nel passo at una copia immutabile dei count simboli scelti.
 * at indica un Known valido e count e non negativo.
 * I rami possono condividere la copia: un tentativo nuovo non la modifica.
 * Ritorna zero e interrompe la ricerca se manca la memoria per la copia. */
static int known_parts(int at, const int *part, int count) {
    int *copy = work_arena_array((size_t)count, sizeof *copy);
    if (count && !copy) { exhausted = 1; return 0; }
    if (count) memcpy(copy, part, (size_t)count * sizeof *copy);
    now->known[at].parts = count;
    now->known[at].part = copy;
    return 1;
}

/* Come si legge un connettivo tenuto conto del segno: le due parti con il
 * loro segno, e se insieme fanno una congiunzione o una disgiunzione. Sono
 * le stesse leggi di junction() (capitolo 18), per quest'altro albero. */
typedef struct {
    int conjunction;       /* 1 congiunzione, 0 disgiunzione */
    const Sentence *x, *y; /* le due parti */
    int nx, ny;            /* 1 se la parte va presa negata */
} Parts;

/* Se s è una congiunzione, una disgiunzione o un'implicazione mette in *p
 * il modo di leggerla, negata se negated, e ritorna 1. */
static int sentence_parts(const Sentence *s, int negated, Parts *p) {
    if (s->kind != S_AND && s->kind != S_OR && s->kind != S_IMPLIES) return 0;
    *p = (Parts){(s->kind == S_AND) != negated, s->a, s->b, s->kind == S_IMPLIES ? !negated : negated, negated};
    return 1;
}

/* Mette in tabella gli elementi nominati dai confronti di s che non stanno
 * sotto un quantificatore: così truth() li trova, e la chiusura per
 * congruenza li confronta con gli altri. */
static void sentence_ground(const Sentence *s, SlotValues value) {
    if (s->kind == S_FORALL || s->kind == S_EXISTS || s->kind == S_FORALL_PART || s->kind == S_EXISTS_PART || s->kind == S_TRUE ||
        s->kind == S_EQUIPOTENT)
        return;
    if (s->kind == S_EQUAL || s->kind == S_HOLDS) {
        elem_ground(s->left, value, G_CREATE);
        if (s->right) elem_ground(s->right, value, G_CREATE);
        return;
    }
    sentence_ground(s->a, value);
    if (s->b) sentence_ground(s->b, value);
}

/* Ritorna ciò che si sa della condizione s, negata se negated, con gli
 * elementi di value[] al posto delle variabili: 1 se è vera, 0 se è falsa,
 * -1 se non si sa. Un confronto è vero se i due elementi sono nella stessa
 * classe, falso se si sa che sono diversi; i connettivi seguono le tavole
 * di verità, dove "non si sa" resta tale a meno che l'altra parte decida;
 * di un quantificatore non si sa mai nulla. Va chiamata dopo closure(). */
static int truth(const Sentence *s, int negated, SlotValues value) {
    int a, b, known = -1;
    switch (s->kind) {
    case S_TRUE:
        known = 1;
        break;
    case S_NOT:
        return truth(s->a, !negated, value);
    case S_EQUAL: case S_HOLDS:
        a = elem_ground(s->left, value, G_EXACT);
        b = s->kind == S_EQUAL ? elem_ground(s->right, value, G_EXACT) : 0;
        if (a >= 0 && b >= 0) known = now->rep[a] == now->rep[b] ? 1 : different_fact(a, b) >= 0 ? 0 : -1;
        break;
    case S_AND:
        a = truth(s->a, 0, value);
        b = truth(s->b, 0, value);
        known = (a == 0 || b == 0) ? 0 : (a == 1 && b == 1) ? 1 : -1;
        break;
    case S_OR: case S_IMPLIES:
        a = truth(s->a, s->kind == S_IMPLIES, value);
        b = truth(s->b, 0, value);
        known = (a == 1 || b == 1) ? 1 : (a == 0 && b == 0) ? 0 : -1;
        break;
    case S_IFF:
        a = truth(s->a, 0, value);
        b = truth(s->b, 0, value);
        if (a >= 0 && b >= 0) known = a == b;
        break;
    case S_FORALL: case S_EXISTS: case S_FORALL_PART: case S_EXISTS_PART: case S_EQUIPOTENT:
    case S_MEMBER: case S_INCLUDED: case S_SAME: case S_UNIQUE: case S_COUNT:  /* questi non arrivano qui (17q) */
        break;
    }
    return known < 0 ? -1 : known != negated;
}

/* I nomi dati da 28-2, per il certificato (28f). Il posto di un nome in
 * symbols[] si riusa da un ramo all'altro, quindi il nome si riconosce dal
 * suo numero d'ordine, name_serial[], che non si ripete nella dimostrazione
 * di un'affermazione: names_given ne conta i nomi. name_known[] è il posto
 * in known[] della condizione K_NAMED che il nome ha aperto. */
static int *name_serial, *name_known;
static size_t name_serial_capacity, name_known_capacity;
static int names_given;

/* 28r-3. La generazione di ogni simbolo: 0 per quelli dichiarati e per i
 * nomi che l'enunciato dà senza istanze, 1 più la più alta degli elementi
 * dell'istanza per un nome nato dentro un'istanza. Si scrive quando il nome
 * nasce, e vale per quel nome solo (il posto si riusa da un ramo all'altro:
 * lo si riscrive). */
static unsigned char *symbol_generation;
static size_t symbol_generation_capacity;

/* 28r-3. Ritorna la generazione dell'elemento presente id: la più alta dei
 * simboli che lo scrivono. */
static int ground_generation(int id) {
    const Ground *g = &ground[id];
    int generation = g->symbol >= 0 ? symbol_generation[g->symbol] : 0;
    for (int i = 0; i < 2 && g->arg[i] >= 0; i++) {
        int inner = ground_generation(g->arg[i]);
        if (inner > generation) generation = inner;
    }
    return generation;
}

/* 28r-3. Ritorna la generazione del nome che nasce dalla condizione nota k,
 * un "esiste": la più alta degli elementi al posto delle sue variabili, più
 * 1 se k viene, attraverso le sue parti, da un'istanza; al più 255. */
static int known_generation(const Known *k) {
    int generation = 0, instance = 0;
    for (int v = 0; v < k->value.count; v++) {
        int inner = slot_values_get(k->value, v) > 0 ? ground_generation(slot_values_get(k->value, v)) : 0;
        if (inner > generation) generation = inner;
    }
    for (const Known *p = k; !instance && p; p = p->parent >= 0 ? &now->known[p->parent] : NULL) instance = p->origin == K_INSTANCE;
    generation += instance;
    return generation > 255 ? 255 : generation;
}

/* 28n. Da quale legge delle parti viene una condizione nota (known_law()):
 * da nessuna, dall'estensionalità o da una comprensione. */
typedef enum { LAW_NONE, LAW_EXTENSIONALITY, LAW_COMPREHENSION } Law;
static int known_law(int i);

/* 28n. symbol_law[s] è 1 se il nome di posto s è nato da una legge delle
 * parti: una parte data da una comprensione, o un elemento che distingue
 * due parti. */
static unsigned char *symbol_law;
static size_t symbol_law_capacity;
/* Quanti simboli ha letto l'enunciato: gli altri sono nomi dati dalla
 * dimostrazione (28-2, e le parti di 28j). */
static int declared_symbols;

/* Dimensiona i metadati dei simboli della ricerca. Il parser possiede le
 * dichiarazioni, il motore questi dati delle dimostrazioni: nessuno dei
 * due conosce i vettori dell'altro. Tutti i riferimenti restano indici.
 * Una crescita parziale conserva i dati e segnala soltanto risorse finite. */
static int proof_symbols_reserve(size_t need) {
    if (!work_reserve((void **)&name_serial, &name_serial_capacity, need, sizeof *name_serial) ||
        !work_reserve((void **)&name_known, &name_known_capacity, need, sizeof *name_known) ||
        !work_reserve((void **)&symbol_generation, &symbol_generation_capacity, need, sizeof *symbol_generation) ||
        !work_reserve((void **)&symbol_law, &symbol_law_capacity, need, sizeof *symbol_law)) {
        exhausted = 1; return 0;
    }
    return 1;
}

/* Registra un nome del motore dopo aver riservato anche i suoi metadati.
 * Ritorna l'indice nuovo, o -1 senza pubblicare un nome incompleto. */
static int proof_symbol_append(Symbol symbol) {
    if (!proof_symbols_reserve((size_t)symbol_count + 1)) return -1;
    int id = symbol_append(symbol);
    if (id < 0) exhausted = 1;
    return id;
}

/* 28j. LE PARTI NELLA RICERCA: NOMI, COPIE, DEFINIZIONI
 *
 * (Sta qui, dentro 28d, perché known_open() la usa; la lettera è venuta
 * dopo le altre.)
 *
 * Un quantificatore su parti (17u) si usa come uno su elementi, con una
 * parte al posto di un elemento:
 *
 *   - 28-2 per le parti. Da "esiste una parte X di S con P(X)" si prende una
 *     tale parte e le si dà un nome nuovo, X_1: vale P(X_1).
 *   - 28-3 per le parti. Da "per ogni parte X di S vale P(X)", e da una
 *     parte D di S, segue P(D). Quali D provare lo dice 28k.
 *
 * Una parte D si sa nominare quando è un simbolo: una parte dichiarata, una
 * nata da 28-2, oppure una DEFINITA da una regola, "sia D = \{x \in S \mid
 * c(x)\}", con c fatta di ciò che c'è già. Una definizione è un passo
 * valido: per l'assioma di separazione, per ogni insieme S e ogni condizione
 * c c'è la parte degli x di S per cui c vale (vuota, se non vale per
 * nessuno; e se S è vuoto c'è comunque, ed è vuota). D è un nome nuovo, e di
 * lei si sa solo "per ogni x di S, x \in D se e solo se c(x)" (K_DEFINED):
 * nulla di ciò che si sapeva prima cambia. Anche una parte di un insieme
 * vuoto esiste, quindi una parte, nominata o definita, non chiede mai che
 * un insieme abbia elementi; è c che può nominarne uno, come \{a\}, e allora
 * la definizione vale solo dove a c'è (lo controlla il verificatore, 11g).
 *
 * P(D) è P(X) con D al posto di X: una copia dell'albero (sentence_rename()),
 * nell'arena come l'enunciato. Da lì in poi una condizione nota che viene da
 * una copia è come le altre: si apre, si istanzia, si scrive e si
 * ricontrolla allo stesso modo. Il controllo di 28e rilegge ogni copia con
 * sentence_renamed(), che confronta i due alberi nodo per nodo senza
 * ricostruirli: un controllo diverso da chi ha fatto la copia. */

/* Ritorna 1 se s è un quantificatore su parti. */
static int part_quantifier(const Sentence *s) { return s->kind == S_FORALL_PART || s->kind == S_EXISTS_PART; }

/* Ritorna l'elemento e con il simbolo to al posto di from; dove nulla
 * cambia, e stesso. */
static Elem *elem_rename(Elem *e, int from, int to) {
    if (e->symbol < 0) return e;
    Elem *a = e->arg[0] ? elem_rename(e->arg[0], from, to) : NULL, *b = e->arg[1] ? elem_rename(e->arg[1], from, to) : NULL;
    if (e->symbol != from && a == e->arg[0] && b == e->arg[1]) return e;
    return elem_new(e->symbol == from ? to : e->symbol, 0, a, b);
}

/* Ritorna la condizione s con la parte to al posto della parte legata
 * from: ogni from applicato a qualcosa diventa to applicato alla stessa
 * cosa. Un quantificatore interno che lega di nuovo from (le copie di 17q
 * possono farlo) la nasconde, e lì non cambia nulla. Dove nulla cambia si
 * riusa s; se l'arena è piena annota exhausted.
 *
 * Perché i cast: i nodi sono nell'arena, scrivibili, e l'albero letto non
 * cambia mai; una copia ne condivide i pezzi che restano uguali. */
static const Sentence *sentence_rename(const Sentence *s, int from, int to) {
    if (part_quantifier(s) && s->part == from) return s;
    Elem *left = s->left ? elem_rename(s->left, from, to) : NULL, *right = s->right ? elem_rename(s->right, from, to) : NULL;
    const Sentence *a = s->a ? sentence_rename(s->a, from, to) : NULL, *b = s->b ? sentence_rename(s->b, from, to) : NULL;
    if (left == s->left && right == s->right && a == s->a && b == s->b) return s;
    Sentence *copy = arena_alloc(sizeof *copy);
    if (!copy) { exhausted = 1; return s; }
    *copy = *s;
    copy->left = left;
    copy->right = right;
    copy->a = (Sentence *)a;
    copy->b = (Sentence *)b;
    return copy;
}

/* Il simbolo che deve stare in una copia al posto di symbol: to[i] se
 * symbol è from[i], per qualche i < count; altrimenti lui stesso. */
static int renamed_symbol(int symbol, const int *from, const int *to, int count) {
    for (int i = 0; i < count; i++)
        if (from[i] == symbol) return to[i];
    return symbol;
}

/* Ritorna 1 se l'elemento e è scritto come original con to[i] al posto di
 * from[i], per ogni i < count (con count = 0: scritto allo stesso modo). */
static int elem_renamed(const Elem *e, const Elem *original, const int *from, const int *to, int count) {
    if (!e || !original) return e == original;
    if (e->symbol < 0 || original->symbol < 0) return e->symbol == original->symbol && e->slot == original->slot;
    return e->symbol == renamed_symbol(original->symbol, from, to, count) && elem_renamed(e->arg[0], original->arg[0], from, to, count) &&
           elem_renamed(e->arg[1], original->arg[1], from, to, count);
}

/* Ritorna 1 se la condizione s è scritta come original con to[i] al posto
 * della parte legata from[i], per ogni i < count: il controllo di una copia
 * fatta da sentence_rename(), che guarda solo come sono scritti i due
 * alberi. Sotto un quantificatore che lega di nuovo from[i], from[i] resta
 * com'è. Con count = 0 dice se i due alberi sono scritti allo stesso modo.
 * Una copia temporanea fallita segnala failure e ritorna zero. */
static int sentence_renamed(const Sentence *s, const Sentence *original, const int *from, const int *to, int count) {
    if (!s || !original) return s == original;
    if (s->kind != original->kind || s->slot != original->slot || s->part != original->part) return 0;
    if (!elem_renamed(s->left, original->left, from, to, count) || !elem_renamed(s->right, original->right, from, to, count)) return 0;

    /* Solo un quantificatore che nasconde un nome richiede una mappa nuova.
     * Negli altri nodi si condividono i vettori del chiamante, senza copie. */
    int hidden = 0;
    if (part_quantifier(original))
        for (int i = 0; i < count; i++) hidden |= original->part == from[i];
    if (!hidden)
        return sentence_renamed(s->a, original->a, from, to, count) && sentence_renamed(s->b, original->b, from, to, count);
    int *inner = NULL; size_t capacity = 0;
    if (!work_reserve((void **)&inner, &capacity, 2 * (size_t)count, sizeof *inner)) return 0;
    int used = 0;
    for (int i = 0; i < count; i++) if (original->part != from[i]) {
        inner[used] = from[i]; inner[count + used++] = to[i];
    }
    int same = sentence_renamed(s->a, original->a, inner, inner + count, used) &&
               sentence_renamed(s->b, original->b, inner, inner + count, used);
    free(inner);
    return same;
}

/* Ritorna 1 se il simbolo symbol compare nell'elemento e. */
static int elem_mentions(const Elem *e, int symbol) {
    return e && (e->symbol == symbol || elem_mentions(e->arg[0], symbol) || elem_mentions(e->arg[1], symbol));
}

/* Ritorna 1 se il simbolo symbol compare nella condizione s. */
static int sentence_mentions(const Sentence *s, int symbol) {
    return s && (elem_mentions(s->left, symbol) || elem_mentions(s->right, symbol) || sentence_mentions(s->a, symbol) ||
                 sentence_mentions(s->b, symbol));
}

/* Ritorna 1 se il simbolo di posto symbol è una parte che si può mettere al
 * posto di una parte legata di sort: una parte dell'insieme sort, non
 * legata, non una famiglia. */
static int part_of(int symbol, int sort) {
    if (symbol < 0 || symbol >= symbol_count) return 0;
    const Symbol *s = &symbols[symbol];
    return !symbol_bound[symbol] && s->arity == 1 && s->range == TRUTH && !s->family && s->domain[0] == sort;
}

/* Registra una parte nuova dell'insieme sort, che si chiama con la lettera
 * letter e il primo pedice da first in su che nessun simbolo abbia, e le dà
 * il numero d'ordine dei nomi (28f). Ritorna il suo posto in symbols[], o -1
 * se non c'è più posto (e annota exhausted). */
static int part_symbol_new(int letter, int sort, int first) {
    Symbol part = {letter, first, 1, {sort, 0}, TRUTH, 0, 0};
    while (symbol_find(part.name, part.index) >= 0) {
        if (part.index == INT_MAX) { exhausted = 1; return -1; }
        part.index++;
    }
    int id = proof_symbol_append(part);
    if (id < 0) return -1;
    symbol_law[id] = 0;
    symbol_generation[id] = 1;
    name_serial[id] = ++names_given;
    name_known[id] = -1;
    return id;
}

/* 28-2 per una parte: dalla condizione nota di posto i, "esiste una parte X
 * di S con P(X)" (o "non per ogni parte X di S vale P(X)"), dà alla parte un
 * nome nuovo, la lettera di X con il primo pedice libero, e aggiunge P del
 * nome con il segno della condizione. */
static void part_name(int i) {
    const Sentence *s = now->known[i].source;
    int part = part_symbol_new(symbols[s->part].name, symbols[s->part].domain[0], 0);
    if (part < 0) return;
    int named = known_add(sentence_rename(s->a, s->part, part), now->known[i].negated, now->known[i].value, K_NAMED, i);
    if (named < 0) return;
    int chosen = part;
    if (!known_parts(named, &chosen, 1)) return;
    name_known[part] = named;
}

/* 28q. L'EQUIPOTENZA: BIIEZIONI CON UN NOME, BIIEZIONI COSTRUITE
 *
 * (Sta qui, dentro 28d, perché known_open() e instantiate() la usano; la
 * lettera è venuta dopo le altre. La seconda metà, la grammatica dei
 * testimoni, sta più avanti, accanto alle istanze.)
 *
 * A \sim B (17w di parser.c) vuol dire che c'è una biiezione da A a B. Il
 * capitolo la usa nella forma "ci sono \varphi \colon A \to B e \psi \colon
 * B \to A, una l'inversa dell'altra":
 *
 *     D(\varphi, \psi) =  \forall x \in A\ (\psi(\varphi(x)) = x)
 *                         \land \forall y \in B\ (\varphi(\psi(y)) = y).
 *
 * Le due forme sono equivalenti, e senza l'assioma della scelta. Se \varphi è
 * una biiezione, per ogni y di B c'è uno e un solo x con \varphi(x) = y (uno
 * perché \varphi è suriettiva, uno solo perché è iniettiva): \psi(y) è quel
 * x, una descrizione e non una scelta, e D vale. Viceversa da D: se
 * \varphi(a) = \varphi(b) allora a = \psi(\varphi(a)) = \psi(\varphi(b)) = b,
 * e ogni y è \varphi(\psi(y)). Con un lato prodotto, A = A_{1} \times A_{2},
 * x è una coppia e \psi(\varphi(x)) = x vale componente per componente; una
 * applicazione verso un prodotto sono le sue due componenti, ognuna di due
 * argomenti se parte da un prodotto (17w).
 *
 * L'equipotenza è dunque un "esiste" su due applicazioni, e il capitolo la
 * usa con le due regole di sempre:
 *
 *   28q-1. Un nome. Da A \sim B vera nel ramo nascono due applicazioni nuove,
 *          \varphi_{k} e \psi_{k}, e vale D(\varphi_{k}, \psi_{k}): è 28-2 per
 *          una biiezione. I nomi sono nuovi, quindi nulla di ciò che si
 *          sapeva cambia.
 *   28q-2. Un'istanza. Da A \sim B falsa, cioè "per ogni \varphi e \psi, non
 *          D(\varphi, \psi)", segue \lnot D(\gamma, \delta) per due
 *          applicazioni \gamma e \delta che ci sono: è 28-3. Le si costruisce
 *          con la grammatica dei testimoni (più avanti), dando un nome a
 *          ognuna con la sua DEFINIZIONE (K_MAPDEF), in una di tre forme:
 *
 *     d1. \gamma(x) = t, con t un termine in cui \gamma non compare;
 *     d2. \gamma(X) parte di C: \forall y \in C\ (y \in \gamma(X) \iff c), con c
 *         una condizione in cui \gamma non compare;
 *     d3. \gamma(f) applicazione da E: \forall y \in E, e per \gamma(f)(y) una
 *         delle tre forme, ricorsivamente.
 *
 * Una definizione è un passo valido. Per ogni valore degli argomenti c'è
 * uno e un solo oggetto che la soddisfa: il valore di t; la parte \{y \in C
 * \mid c\}, che sta in \mathcal{P}(C) perché lì ci sono tutte le parti; la
 * applicazione che a ogni y dà l'oggetto della forma interna, che sta in
 * C^{E} perché lì ci sono tutte le applicazioni. Uno solo, perché due parti
 * con gli stessi elementi, e due applicazioni con gli stessi valori, sono la
 * stessa (28n). Quindi l'applicazione \gamma esiste, senza scegliere nulla,
 * e il suo nome è nuovo: come per le parti definite (28j), darglielo non
 * cambia nulla di ciò che si sapeva. Il verificatore controlla da sé la forma
 * di ogni definizione (11j di checker.c).
 *
 * Che \gamma e \delta siano una l'inversa dell'altra non lo si suppone mai: è
 * ciò che la dimostrazione deve ottenere, per assurdo, dalle definizioni,
 * dalle identità delle biiezioni con un nome e dall'estensionalità (28n),
 * con le istanze di sempre. Le istanze di una definizione si prendono dove
 * l'applicazione definita compare (instance_mapdef()), come per le parti di
 * 28j. Il numero degli elementi non entra mai: nessuna regola dice che
 * equipotenti vuol dire "con tanti elementi quanti"; lo dicono solo i
 * modelli finiti, dove è un conto (model_equipotent()).
 *
 * Le variabili delle identità sono quelle del nodo (17w); quelle delle
 * definizioni, due per insieme, nascono una volta per enunciato
 * (bijection_prepare()): una definizione è una condizione chiusa, e due
 * condizioni chiuse possono legare la stessa variabile senza confondersi. */

/* 28q. Ritorna il quantificatore kind sulla variabile di posto slot davanti a
 * body. I nodi costruiti qui e dalle leggi delle parti (28n) non hanno
 * testo nell'enunciato: start ed end sono vuoti, e non si stampano mai come
 * testo. */
static Sentence *axiom_bind(SentenceKind kind, int slot, Sentence *body) {
    Sentence *s = sentence_new(kind, body, NULL, "");
    s->end = s->start;
    s->slot = slot;
    return s;
}

/* 28q. Ritorna la condizione kind tra gli elementi left e right:
 * un'uguaglianza (S_EQUAL), o l'appartenenza (S_HOLDS) del simbolo symbol
 * applicato a left e right. */
static Sentence *axiom_atom(SentenceKind kind, int symbol, Elem *left, Elem *right) {
    Sentence *s = sentence_new(kind, NULL, NULL, "");
    s->end = s->start;
    s->left = kind == S_HOLDS ? elem_new(symbol, 0, left, right) : left;
    s->right = kind == S_HOLDS ? NULL : right;
    return s;
}

/* 28q. Ritorna il connettivo kind tra a e b, senza semplificare nulla: la
 * forma è quella che il verificatore riconosce. */
static Sentence *axiom_join(SentenceKind kind, Sentence *a, Sentence *b) {
    Sentence *s = sentence_new(kind, a, b, "");
    s->end = s->start;
    return s;
}

/* 28q. Ritorna la variabile di posto slot, come elemento. */
static Elem *slot_elem(int slot) { return elem_new(-1, slot, NULL, NULL); }

/* 28q. Ritorna il simbolo di posto symbol applicato ai primi count elementi
 * di arg[] (count da 0 a 2). */
static Elem *map_apply(int symbol, Elem *const *arg, int count) {
    return elem_new(symbol, 0, count > 0 ? arg[0] : NULL, count > 1 ? arg[1] : NULL);
}

/* 28q. Ritorna l'insieme della componente i del lato k dell'equipotenza e. */
static int side_sort(const Sentence *e, int k, int i) { return slot_data[e->side_slot[k][i]].sort; }

/* 28q. Ritorna il nome interno della lettera greca word (greek_letters[],
 * 17o). */
static int greek_name(const char *word) {
    for (size_t i = 0; i < sizeof greek_letters / sizeof *greek_letters; i++)
        if (strcmp(greek_letters[i], word) == 0) return GREEK_NAMES + (int)i;
    return GREEK_NAMES;
}

/* 28q. Registra un'applicazione nuova, di nome la lettera greca word con il
 * primo pedice da 1 in su che nessun simbolo abbia, con arity argomenti
 * negli insiemi domain[] e il valore nell'insieme range; le dà il numero
 * d'ordine dei nomi (28f). Ritorna il suo posto in symbols[], o -1 se non c'è
 * più posto (e annota exhausted). */
static int map_symbol_new(const char *word, int arity, const int *domain, int range) {
    Symbol map = {greek_name(word), 1, arity, {arity > 0 ? domain[0] : 0, arity > 1 ? domain[1] : 0}, range, 0, 0};
    while (symbol_find(map.name, map.index) >= 0) {
        if (map.index == INT_MAX) { exhausted = 1; return -1; }
        map.index++;
    }
    int id = proof_symbol_append(map);
    if (id < 0) return -1;
    symbol_law[id] = 0;
    symbol_generation[id] = 0;
    name_serial[id] = ++names_given;
    name_known[id] = -1;
    return id;
}

/* 28q. Ritorna le identità D dell'equipotenza e (vedi la testa del
 * paragrafo) per le applicazioni di map[]: in map[0..n) le componenti di
 * quella da A a B, in map[n..n+m) quelle dell'inversa, con m e n le
 * componenti dei lati A e B. La forma, che il verificatore costruisce allo
 * stesso modo (ck_identities() in checker.c), è
 *
 *     (\forall x_{1} \forall x_{2}\ (\psi_{1}(\varphi(x)) = x_{1} \land \psi_{2}(\varphi(x)) = x_{2}))
 *     \land (\forall y_{1} ... )
 *
 * con le variabili del nodo, la più esterna per prima, e \varphi(x) scritto
 * come le n componenti \varphi_{j}(x_{1}, x_{2}). Con una componente sola
 * l'uguaglianza è una, senza congiunzione. */
static Sentence *equipotent_identities(const Sentence *e, const int *map) {
    Sentence *half[2];
    for (int k = 0; k < 2; k++) {
        /* Per k = 0: le variabili di A, e \psi dopo \varphi; per k = 1 quelle
         * di B, e \varphi dopo \psi. */
        int m = e->sides[k], n = e->sides[1 - k];
        const int *first = k ? map + e->sides[1] : map, *second = k ? map : map + e->sides[1];
        Elem *x[2], *inner[2];
        Sentence *body = NULL;
        for (int i = 0; i < m; i++) x[i] = slot_elem(e->side_slot[k][i]);
        for (int j = 0; j < n; j++) inner[j] = map_apply(first[j], x, m);
        for (int i = 0; i < m; i++) {
            Sentence *equal = axiom_atom(S_EQUAL, -1, map_apply(second[i], inner, n), x[i]);
            body = body ? axiom_join(S_AND, body, equal) : equal;
        }
        for (int i = m - 1; i >= 0; i--) body = axiom_bind(S_FORALL, e->side_slot[k][i], body);
        half[k] = body;
    }
    return axiom_join(S_AND, half[0], half[1]);
}

/* 28q. Gli insiemi della componente j delle applicazioni delle identità di
 * e, nell'ordine di map[] in equipotent_identities(): mette quelli degli
 * argomenti in domain[] e ne ritorna quanti sono, quello del valore in
 * *range. */
static int identity_map_sorts(const Sentence *e, int j, int *domain, int *range) {
    int forward = j < e->sides[1], from = forward ? 0 : 1;
    *range = forward ? side_sort(e, 1, j) : side_sort(e, 0, j - e->sides[1]);
    for (int a = 0; a < e->sides[from]; a++) domain[a] = side_sort(e, from, a);
    return e->sides[from];
}

/* 28q-1. Dalla condizione nota di posto i, l'equipotenza vera A \sim B, dà
 * un nome alla biiezione da A a B, \varphi, e alla sua inversa, \psi (una
 * applicazione per componente), e aggiunge le loro identità. */
static void bijection_name(int i) {
    const Sentence *e = now->known[i].source;
    int map[4];
    int count = e->sides[0] + e->sides[1];
    for (int j = 0; j < count; j++) {
        int domain[2], range, arity = identity_map_sorts(e, j, domain, &range);
        map[j] = map_symbol_new(j < e->sides[1] ? "varphi" : "psi", arity, domain, range);
        if (map[j] < 0) return;
    }
    int named = known_add(equipotent_identities(e, map), 0, now->known[i].value, K_BIJECTION, i);
    if (named < 0) return;
    if (!known_parts(named, map, count)) return;
    for (int j = 0; j < count; j++) name_known[map[j]] = named;
}

/* Guarda per la prima volta la condizione nota di posto i, e ne trae ciò
 * che non richiede scelte: un fatto entra tra le uguaglianze o tra i
 * "diversi"; di una congiunzione si aggiungono le due parti (28-1); un
 * "esiste" riceve un nome (28-2); una disgiunzione e un "per ogni" restano
 * in attesa. */
static void known_open(int i) {
    Known *k = &now->known[i];
    const Sentence *s = k->source;
    Parts p;
    k->stage = K_DONE;
    switch (s->kind) {
    case S_TRUE: case S_NOT:
        return;
    case S_EQUAL: case S_HOLDS:
        k->left = (short)elem_ground(s->left, k->value, G_CREATE);
        k->right = (short)(s->kind == S_EQUAL ? elem_ground(s->right, k->value, G_CREATE) : 0);
        if (k->left < 0 || k->right < 0) { k->left = k->right = -1; exhausted = 1; return; }
        if (k->negated && now->differents < MAX_DIFFERENT) now->different[now->differents++] = (short)i;
        else if (k->negated) exhausted = 1;
        else if (now->rep[k->left] != now->rep[k->right]) classes_join(k->left, k->right, i);
        return;
    case S_AND: case S_OR: case S_IMPLIES: case S_IFF:
        if (sentence_parts(s, k->negated, &p) && p.conjunction) {
            known_add(p.x, p.nx, k->value, K_PART, i);
            known_add(p.y, p.ny, k->value, K_PART, i);
            return;
        }
        sentence_ground(s, k->value);
        k->stage = K_WAITING;
        return;
    case S_FORALL_PART: case S_EXISTS_PART:
        /* 28j. Un "per ogni parte" aspetta le sue parti (28k); un "esiste
         * una parte" dà un nome. */
        if ((s->kind == S_FORALL_PART) != k->negated) k->stage = K_RULE;
        else part_name(i);
        return;
    case S_EQUIPOTENT:
        /* 28q. Vera, una biiezione con un nome (28q-1); falsa, è un "per
         * ogni" su due applicazioni, che aspetta il suo testimone (28q-2). */
        if (k->negated) k->stage = K_RULE;
        else bijection_name(i);
        return;
    case S_FORALL: case S_EXISTS:
        break;
    case S_MEMBER: case S_INCLUDED: case S_SAME: case S_UNIQUE: case S_COUNT:
        /* Non arrivano qui: lo svolgimento (17q) li toglie. */
        return;
    }
    if ((s->kind == S_FORALL) != k->negated) { k->stage = K_RULE; return; }

    /* 28-2. Un nome nuovo: la lettera della variabile, con il primo pedice
     * che non sia già di un altro simbolo. */
    Symbol name = {slot_data[s->slot].letter, 0, 0, {0, 0}, slot_data[s->slot].sort, 0, 0};
    SlotValues value = SLOT_VALUES_EMPTY;
    while (symbol_find(name.name, name.index) >= 0) {
        if (name.index == INT_MAX) { exhausted = 1; return; }
        name.index++;
    }
    int id = proof_symbol_append(name);
    if (id < 0) return;
    symbol_law[id] = known_law(i) != LAW_NONE;
    symbol_generation[id] = (unsigned char)known_generation(k);
    name_serial[id] = ++names_given;
    name_known[id] = -1;
    value = slot_values_copy(k->value);
    if (work_allocation_failed) { exhausted = 1; return; }
    value.data[s->slot] = (short)ground_lookup(id, -1, -1, G_CREATE);
    if (slot_values_get(value, s->slot) >= 0) name_known[id] = known_add(s->a, k->negated, value, K_NAMED, i);
}

/* 28-1. Riguarda la disgiunzione in attesa di posto i alla luce di ciò che
 * si sa adesso. Se una parte è vera non c'è altro da trarne; se una è
 * falsa, vale l'altra, che entra in elenco; se lo sono tutte e due il ramo
 * si chiude, e clash_choice lo annota. Un "se e solo se" si tratta allo
 * stesso modo: saputa una parte, l'altra è decisa. Ritorna 1 se ha
 * aggiunto qualcosa o chiuso il ramo. */
static int known_decide(int i) {
    Known *k = &now->known[i];
    const Sentence *s = k->source;
    Parts p;
    if (s->kind == S_IFF) {
        int a = truth(s->a, 0, k->value), b = truth(s->b, 0, k->value);
        if (a < 0 && b < 0) return 0;
        k->stage = K_DONE;
        if (a >= 0 && b >= 0) {
            if ((a == b) != k->negated) return 0;
            clash_choice = i;
        } else if (a >= 0) {
            known_add(s->b, a ? k->negated : !k->negated, k->value, K_PART, i);
        } else {
            known_add(s->a, b ? k->negated : !k->negated, k->value, K_PART, i);
        }
        return 1;
    }
    sentence_parts(s, k->negated, &p);
    int x = truth(p.x, p.nx, k->value), y = truth(p.y, p.ny, k->value);
    if (x != 0 && y != 0 && x != 1 && y != 1) return 0;
    k->stage = K_DONE;
    if (x == 1 || y == 1) return 0;
    if (x == 0 && y == 0) clash_choice = i;
    else if (x == 0) known_add(p.y, p.ny, k->value, K_PART, i);
    else known_add(p.x, p.nx, k->value, K_PART, i);
    return 1;
}

/* Trae da ciò che si sa tutto ciò che non richiede istanze né scelte:
 * apre le condizioni nuove, chiude per congruenza, riguarda le disgiunzioni
 * in attesa, finché nulla cambia. Ritorna 1 se il ramo si è chiuso con una
 * contraddizione, annotata in clash_fact o clash_choice. */
static int settle(void) {
    clash_fact = clash_choice = -1;
    for (int changed = 1; changed && !exhausted; ) {
        changed = 0;
        for (int i = 0; i < now->knowns && !exhausted; i++) {
            if (now->known[i].stage != K_NEW) continue;
            known_open(i);
            changed = 1;

            /* Il falso, una disgiunzione senza parti (lo svolgimento lo
             * lascia, per esempio, per un'immagine dell'insieme vuoto): il
             * ramo è chiuso. */
            if (now->known[i].source->kind == S_TRUE && now->known[i].negated) { clash_choice = i; return 1; }
        }
        closure();

        /* Una contraddizione: due elementi che si sanno diversi sono finiti
         * nella stessa classe. */
        for (int i = 0; i < now->differents; i++) {
            const Known *k = &now->known[now->different[i]];
            if (now->rep[k->left] == now->rep[k->right]) { clash_fact = now->different[i]; return 1; }
        }
        for (int i = 0; i < now->knowns && !exhausted; i++) {
            if (now->known[i].stage != K_WAITING || !known_decide(i)) continue;
            if (clash_choice >= 0) return 1;
            changed = 1;
        }
    }
    return 0;
}

/* Un "per ogni" noto, pronto per le sue istanze (28-3): le variabili dei
 * "per ogni" consecutivi con cui la condizione comincia, e ciò che li
 * segue. */
typedef struct {
    int known;             /* il suo posto in known[] */
    const int *slot;       /* variabili dalla piu esterna, prestito dal chiamante */
    int slots;             /* numero di variabili nel vettore slot */
    SlotSet all;     /* le stesse, come bit: il bit i è la variabile di posto i */
    const Sentence *body;  /* la condizione che segue i "per ogni" */
    int negated;           /* il segno con cui è vera */
} Rule;

/* Aggiunge all'elenco l'istanza di rule con gli elementi di value[] al
 * posto delle sue variabili, se non c'è già: due istanze su elementi uguali
 * per ciò che si sa sono la stessa. Ritorna 1 se l'ha aggiunta. */
static int instance_add(const Rule *rule, SlotValues value) {
    if (work_allocation_failed) return 0;
    for (int j = 0; j < rule->slots; j++)
        if (slot_values_get(value, rule->slot[j]) < 0) return 0;
    for (int i = rule->known + 1; i < now->knowns; i++) {
        const Known *k = &now->known[i];
        int same = k->parent == rule->known && k->origin == K_INSTANCE;
        for (int j = 0; j < rule->slots && same; j++) {
            int a = slot_values_get(k->value, rule->slot[j]), b = slot_values_get(value, rule->slot[j]);
            same = a >= 0 && now->rep[a] == now->rep[b];
        }
        if (same) return 0;
    }
    return known_add(rule->body, rule->negated, value, K_INSTANCE, rule->known) >= 0;
}

/* Ritorna le variabili che compaiono nell'elemento e, come bit. */
static SlotSet elem_slots(const Elem *e) {
    if (!e) return SLOT_EMPTY;
    if (e->symbol < 0) return slot_set_single(e->slot);
    return slot_set_union(elem_slots(e->arg[0]), elem_slots(e->arg[1]));
}

/* Confronto di uno schema con gli elementi presenti. Cerca ogni modo di
 * dare un elemento alle variabili ancora libere in value[] così che ogni
 * schema pattern[i], per i < count, diventi uguale, per ciò che si sa,
 * all'elemento target[i]; per ogni modo trovato aggiunge l'istanza di rule,
 * e ritorna quante ne ha aggiunte. I due elenchi hanno MAX_PATTERN posti e
 * vengono usati come pila: uno schema così annidato da riempirla non viene
 * confrontato.
 *
 * Una variabile libera prende l'elemento che ha di fronte; una già fissata
 * deve essergli uguale. Un simbolo applicato deve trovare, nella classe di
 * ciò che ha di fronte, un elemento con lo stesso simbolo: ce ne possono
 * essere più d'uno, e si provano tutti. È così che (x \perp y) \perp z
 * trova e \perp c quando si sa che e = b \perp a: x = b, y = a, z = c. */
static int instance_match(const Rule *rule, const Elem **pattern, short *target, int count, SlotValues value) {
    if (count == 0) return instance_add(rule, value);
    const Elem *p = pattern[count - 1];
    int facing = target[count - 1], made = 0;
    if (p->symbol < 0) {
        int fixed = slot_values_get(value, p->slot);
        if (fixed >= 0) return now->rep[fixed] == now->rep[facing] ? instance_match(rule, pattern, target, count - 1, value) : 0;
        value.data[p->slot] = (short)facing;
        made = instance_match(rule, pattern, target, count - 1, value);
        value.data[p->slot] = -1;
        return made;
    }
    for (int id = 1; id < now->grounds && !exhausted && count < MAX_PATTERN; id++) {
        if (now->rep[id] != now->rep[facing] || ground[id].symbol != p->symbol) continue;
        int next = count - 1;
        for (int i = 0; i < 2 && p->arg[i]; i++) { pattern[next] = p->arg[i]; target[next++] = ground[id].arg[i]; }
        made += instance_match(rule, pattern, target, next, value);
    }
    pattern[count - 1] = p;
    target[count - 1] = (short)facing;
    return made;
}

/* 28-3, le istanze che riscrivono un elemento presente. Per ogni elemento
 * scritto nella condizione s (fuori dai quantificatori più interni) che sia
 * un simbolo applicato e contenga tutte le variabili di rule, cerca gli
 * elementi presenti che gli corrispondono e aggiunge quelle istanze.
 * Ritorna quante ne ha aggiunte. */
static int instance_rewrite_elem(const Rule *rule, const Elem *e) {
    const Elem *pattern[MAX_PATTERN];
    short target[MAX_PATTERN];
    SlotValues value = SLOT_VALUES_EMPTY;
    int made = 0;
    if (e->symbol < 0) return 0;
    for (int i = 0; i < 2 && e->arg[i]; i++) made += instance_rewrite_elem(rule, e->arg[i]);
    if (!e->arg[0] || symbols[e->symbol].range == TRUTH || !slot_set_includes(elem_slots(e), rule->all)) return made;
    value = slot_values_copy(now->known[rule->known].value);
    if (work_allocation_failed) return 0;
    for (int id = 1, last = now->grounds; id < last && !exhausted; id++) {
        if (ground[id].symbol != e->symbol) continue;
        int count = 0;
        slot_values_load(value, now->known[rule->known].value);
        for (int i = 0; i < 2 && e->arg[i]; i++) { pattern[count] = e->arg[i]; target[count++] = ground[id].arg[i]; }
        made += instance_match(rule, pattern, target, count, value);
    }
    return made;
}

/* Come instance_rewrite_elem(), per tutti gli elementi dei confronti di s. */
static int instance_rewrite(const Rule *rule, const Sentence *s) {
    if (s->kind == S_FORALL || s->kind == S_EXISTS || part_quantifier(s) || s->kind == S_TRUE || s->kind == S_EQUIPOTENT) return 0;
    if (s->kind == S_EQUAL || s->kind == S_HOLDS) return instance_rewrite_elem(rule, s->left) + (s->right ? instance_rewrite_elem(rule, s->right) : 0);
    return instance_rewrite(rule, s->a) + (s->b ? instance_rewrite(rule, s->b) : 0);
}

/* Esamina, senza aggiungere nulla, l'elemento e di un'istanza che si pensa
 * di fare, con gli elementi di value[] al posto delle variabili. Ritorna il
 * posto di un elemento uguale a lui per ciò che si sa, o un numero negativo
 * se non c'è; annota in *missing se l'istanza introdurrebbe un elemento
 * nuovo. Un elemento con un nome c'è sempre: l'enunciato lo dà. */
static int instance_elem(const Elem *e, SlotValues value, int *missing) {
    int arg[2] = {-1, -1};
    if (e->symbol < 0) return slot_values_get(value, e->slot) >= 0 ? slot_values_get(value, e->slot) : -2;
    for (int i = 0; i < 2 && e->arg[i]; i++) {
        arg[i] = instance_elem(e->arg[i], value, missing);
        if (arg[i] < 0) return arg[i];
    }
    int found = ground_lookup(e->symbol, arg[0], arg[1], arg[0] < 0 ? G_CREATE : G_CLASS);
    if (found < 0 && symbols[e->symbol].range != TRUTH) *missing = 1;
    return found;
}

/* Come instance_elem(), per tutti i confronti della condizione s che non
 * stanno sotto un quantificatore; annota in più in *decided se di uno di
 * quei confronti si sa già se è vero o falso. */
static void instance_survey(const Sentence *s, SlotValues value, int *missing, int *decided) {
    if (s->kind == S_FORALL || s->kind == S_EXISTS || part_quantifier(s) || s->kind == S_TRUE || s->kind == S_EQUIPOTENT) return;
    if (s->kind == S_EQUAL || s->kind == S_HOLDS) {
        int a = instance_elem(s->left, value, missing), b = s->kind == S_EQUAL ? instance_elem(s->right, value, missing) : 0;
        if (a >= 0 && b >= 0 && (now->rep[a] == now->rep[b] || different_fact(a, b) >= 0)) *decided = 1;
        return;
    }
    instance_survey(s->a, value, missing, decided);
    if (s->b) instance_survey(s->b, value, missing, decided);
}

/* 28o. Con split_lookahead (le prove di ripiego) le istanze sugli elementi
 * con un nome di un "per ogni" di due o più variabili, P_1 \implies P_2
 * \implies ... \implies C, sono tante quante le coppie di nomi, e quasi
 * tutte non servono. Si tengono quelle in cui nessuna premessa P_i si sa
 * falsa (allora l'istanza è vera senza dire nulla) e al più una non si sa:
 * le altre aspettano che se ne sappia di più. Ritorna 1 se l'istanza di
 * rule con gli elementi di value[] è da tenere. */
static int split_lookahead;
static int instance_guarded(const Rule *rule, SlotValues value) {
    int unknown = 0;
    if (rule->negated) return 1;
    for (const Sentence *s = rule->body; s->kind == S_IMPLIES; s = s->b) {
        int known = truth(s->a, 0, value);
        if (known == 0) return 0;
        unknown += known < 0;
    }
    return unknown <= 1;
}

/* 28-3, le istanze per scelta degli elementi. Prova ogni scelta di un
 * elemento per ciascuna variabile di rule, uno per classe: con named = 1
 * tra i soli elementi con un nome, e le prende tutte; con named = 0 tra
 * tutti, e prende quelle che non introducono elementi nuovi e contengono un
 * confronto già deciso. Se le scelte sono troppe non ne prova nessuna.
 * Ritorna quante istanze ha aggiunto. */
static int instance_choices(const Rule *rule, int named) {
    /* Depositi sullo heap riusati fra i giri; nessun Known ne conserva un
     * indirizzo. La routine non richiama ricorsivamente questa ricerca. */
    static short *candidate;
    static int *index;
    static size_t candidate_capacity, index_capacity;
    size_t sorts = (size_t)sort_count;
    if (!work_reserve((void **)&candidate, &candidate_capacity, (size_t)now->grounds, sizeof *candidate) ||
        !work_reserve((void **)&index, &index_capacity, 2 * sorts + (size_t)rule->slots, sizeof *index)) {
        exhausted = 1; return 0;
    }
    int *first = index, *candidates = index + sorts, *pick = index + 2 * sorts;
    int made = 0, law = known_law(rule->known), used = 0;
    for (int sort = 0; sort < sort_count; sort++) first[sort] = -1;
    for (int j = 0; j < rule->slots; j++) first[slot_data[rule->slot[j]].sort] = 0;

    /* Le variabili dello stesso insieme condividono gli stessi candidati.
     * Ogni elemento entra in una sola lista: la memoria non e il prodotto
     * del numero di quantificatori per quello degli elementi presenti. */
    for (int sort = 0; sort < sort_count; sort++) {
        if (first[sort] < 0) continue;
        first[sort] = used; candidates[sort] = 0;
        for (int id = 1; id < now->grounds; id++) {
            if (symbols[ground[id].symbol].range != sort || (named && ground[id].arg[0] >= 0)) continue;
            if (law == LAW_COMPREHENSION && symbol_law[ground[id].symbol]) continue;
            int fresh = 1;
            for (int c = first[sort]; c < used && fresh; c++) fresh = now->rep[candidate[c]] != now->rep[id];
            if (fresh) { candidate[used++] = (short)id; candidates[sort]++; }
        }
    }
    long long choices = 1;
    for (int j = 0; j < rule->slots && choices <= MAX_TUPLES; j++) {
        pick[j] = 0;
        choices *= candidates[slot_data[rule->slot[j]].sort];
    }
    if (choices == 0 || choices > (named ? MAX_FREE_TUPLES : MAX_TUPLES)) return 0;

    SlotValues value;
    value = slot_values_copy(now->known[rule->known].value);
    if (work_allocation_failed) return 0;

    /* Ogni scelta, come un contachilometri. */
    for (int more = 1; more && !exhausted; ) {
        int missing = 0, decided = 0;
        slot_values_load(value, now->known[rule->known].value);
        for (int j = 0; j < rule->slots; j++) {
            int sort = slot_data[rule->slot[j]].sort;
            value.data[rule->slot[j]] = candidate[first[sort] + pick[j]];
        }
        if (!named) instance_survey(rule->body, value, &missing, &decided);
        int kept = !split_lookahead || rule->slots < 2 || instance_guarded(rule, value);
        if (kept && (named || (!missing && decided))) made += instance_add(rule, value);
        more = 0;
        for (int j = 0; j < rule->slots && !more; j++) {
            if (++pick[j] < candidates[slot_data[rule->slot[j]].sort]) more = 1; else pick[j] = 0;
        }
    }
    return made;
}

/* 28l. LE DIMOSTRAZIONI PIÙ LUNGHE: ISTANZE SUGGERITE, CASI CHE SI
 * CHIUDONO SUBITO
 *
 * (Sta qui, dentro 28d, perché le istanze servono a instantiate(); i casi
 * sono più avanti, con cheap_split(), prima di refute(). La lettera è venuta
 * dopo le altre.)
 *
 * Le dimostrazioni con le immagini e le controimmagini svolte sono più
 * lunghe delle altre del capitolo, e chiedono due cose che 28-3 e 28-5 da
 * sole non fanno.
 *
 * Le istanze suggerite da un'uguaglianza.
 * "f(X) \subseteq f(Y)" svolto è "per ogni t di T, se esiste u in X con
 * f(u) = t, allora esiste v in Y con f(v) = t". Chi lo usa sa che x sta in X
 * e prende t = f(x): "f(x) sta in f(X), quindi in f(Y)". Nessuna delle istanze
 * di 28-3 lo fa: f(x) non ha un nome, e nel corpo, fuori dai quantificatori
 * interni, non c'è un confronto che l'istanza decida. Ma il corpo dice quali
 * valori di t contano: t è il valore di f, f(u) = t. Per un "per ogni" su una
 * sola variabile t, ogni uguaglianza del corpo, anche sotto i quantificatori
 * interni, tra t e un simbolo applicato P suggerisce t := G per ogni elemento
 * presente G scritto come P (stessi simboli; al posto delle variabili di P,
 * qualsiasi cosa). Le istanze sono vere comunque (28-3); la regola dice solo
 * quali provare, al più MAX_FREE_TUPLES per giro, e non introduce elementi:
 * G c'è già.
 *
 * I casi che si chiudono subito. Un'istanza come "t \in f(X \cap Y) se e
 * solo se t \in f(X) \cap f(Y)" su un t che non c'entra è una disgiunzione
 * in attesa come quella che serve; distinguendo i casi della prima (28-5),
 * le distinzioni una dentro l'altra (MAX_SPLITS) finiscono su quelle che
 * non c'entrano. Spesso però uno dei due casi di una disgiunzione si chiude
 * con i soli giri di istanze: allora vale l'altro, ed è un passo che non
 * apre davvero due strade. cheap_split() cerca, tra le prime MAX_PROBES
 * disgiunzioni in attesa, una così, ne chiude il caso (la sua dimostrazione
 * scritta è quella di un caso, ricontrollata come le altre) e continua
 * nell'altro senza contarla tra le distinzioni. Se nessuna ha un caso così,
 * si torna a 28-5. La profondità dei rami resta limitata da MAX_BRANCHES. */

/* Ritorna 1 se l'elemento presente id è scritto come lo schema p: gli stessi
 * simboli negli stessi posti, e qualsiasi cosa al posto delle variabili. */
static int ground_fits(int id, const Elem *p) {
    if (p->symbol < 0) return 1;
    const Ground *g = &ground[id];
    if (g->symbol != p->symbol) return 0;
    for (int i = 0; i < 2 && p->arg[i]; i++)
        if (g->arg[i] < 0 || !ground_fits(g->arg[i], p->arg[i])) return 0;
    return 1;
}

/* Aggiunge le istanze del "per ogni" rule, su una sola variabile, suggerite
 * dalle uguaglianze della condizione s tra la variabile e un simbolo
 * applicato (vedi sopra). Ritorna quante ne ha aggiunte; *budget è quante
 * ne può ancora aggiungere. */
static int instance_trigger(const Rule *rule, const Sentence *s, int *budget) {
    if (!s) return 0;
    int made = instance_trigger(rule, s->a, budget) + instance_trigger(rule, s->b, budget), slot = rule->slot[0];
    if (s->kind != S_EQUAL) return made;
    for (int side = 0; side < 2; side++) {
        const Elem *bare = side ? s->right : s->left, *pattern = side ? s->left : s->right;
        if (bare->symbol >= 0 || bare->slot != slot || pattern->symbol < 0 || slot_set_intersects(elem_slots(pattern), rule->all)) continue;
        SlotValues value = slot_values_copy(now->known[rule->known].value);
        if (work_allocation_failed) return made;
        for (int id = 1, last = now->grounds; id < last && *budget > 0 && !exhausted; id++) {
            if (!ground_fits(id, pattern)) continue;
            slot_values_load(value, now->known[rule->known].value);
            value.data[slot] = (short)id;
            if (instance_add(rule, value)) { made++; --*budget; }
        }
    }
    return made;
}

/* 28j. Le istanze della definizione di una parte D (rule, la sua condizione
 * K_DEFINED, "per ogni x, x \in D se e solo se c(x)"): una per ogni elemento
 * e di cui si parla come membro di D, cioè con D(e) presente. È come si usa
 * una definizione a mano, dove serve: provarla su tutti gli elementi con un
 * nome riempirebbe il ramo di equivalenze "s \in D se e solo se s = a" su
 * elementi che non c'entrano, che la distinzione dei casi (28-5) prenderebbe
 * per prime. Ritorna quante istanze ha aggiunto. */
static int instance_definition(const Rule *rule) {
    int part = now->known[rule->known].part[0], made = 0;
    SlotValues value;
    value = slot_values_copy(now->known[rule->known].value);
    if (work_allocation_failed) return 0;
    for (int id = 1, last = now->grounds; id < last && !exhausted; id++) {
        if (ground[id].symbol != part) continue;
        slot_values_load(value, now->known[rule->known].value);
        value.data[rule->slot[0]] = ground[id].arg[0];
        made += instance_add(rule, value);
    }
    return made;
}

/* 28q. LA GRAMMATICA DEI TESTIMONI
 *
 * (La seconda metà di 28q: sta qui, accanto alle istanze, perché il
 * testimone di 28q-2 è un'istanza.)
 *
 * Un testimone di A \sim B si costruisce con ciò che c'è: le biiezioni con un
 * nome tra due insiemi (28q-1) e la forma degli insiemi. Un termine della
 * grammatica è una biiezione da un insieme U a un insieme V:
 *
 *   w1. l'identità, se U = V;
 *   w2. un passo da U a un insieme W, seguito da un termine da W a V. Il
 *       passo è una biiezione con un nome, \varphi_{k} da U o \psi_{k}
 *       all'indietro, oppure uno di w3 e w4;
 *   w3. U = \mathcal{P}(U'), W = \mathcal{P}(W'), e un termine \beta da U' a
 *       W': l'immagine X \mapsto \beta(X), definita con d2 come y \in \gamma(X)
 *       \iff \beta^{-1}(y) \in X, e l'inversa Y \mapsto \beta^{-1}(Y), y \in
 *       \delta(Y) \iff \beta(y) \in Y;
 *   w4. U = U_{2}^{U_{1}}, W = W_{2}^{W_{1}}, e due termini, \alpha da U_{1} a
 *       W_{1} e \beta da U_{2} a W_{2}: f \mapsto \beta \circ f \circ
 *       \alpha^{-1}, definita con d3 come \gamma(f)(y) = \beta(f(\alpha^{-1}(y))),
 *       e l'inversa F \mapsto \beta^{-1} \circ F \circ \alpha.
 *
 * I lati. Con una componente, un termine da A a B. Con due, da A_{1} \times
 * A_{2} a B_{1} \times B_{2}, o componente per componente, (x_{1}, x_{2})
 * \mapsto (\beta_{1}(x_{1}), \beta_{2}(x_{2})), o scambiando, (x_{1}, x_{2})
 * \mapsto (\beta_{1}(x_{2}), \beta_{2}(x_{1})), e l'inversa allo stesso modo:
 * le componenti sono applicazioni di due argomenti, definite con d1. Un
 * termine fatto di un solo passo è già una coppia di applicazioni; ogni
 * altro si scrive con d1, \gamma(x) = \beta(x).
 *
 * Perché i termini sono pochi. Un passo w2 non torna mai su un insieme già
 * toccato, quindi una composizione ha al più tanti passi quanti sono gli
 * insiemi, e w3 e w4 scendono negli insiemi su cui U è costruito, che
 * vengono prima di lui (sort_derived() in parser.c). I termini sono quindi
 * in numero finito; se ne tengono al più MAX_WITNESSES, dai più corti (il
 * numero dei passi, compresi quelli dentro w3 e w4), e la ricerca li prova
 * in quest'ordine, uno per tentativo (claim_attempts()). Il certificato porta
 * quello che ha funzionato, con le sue definizioni.
 *
 * Pochi i termini, non i cammini. Per trovarli la ricerca prova ogni
 * insieme non ancora toccato come passo successivo, e a ogni passo w3 o w4
 * riparte dagli insiemi su cui è costruito con nessuno toccato: con n
 * insiemi costruiti uno sull'altro i cammini crescono come un fattoriale.
 * S^{S^{\ldots}} \sim S visita 241 volte bij_terms() con 4 esponenti,
 * 39.061 con 6, 13 milioni con 8; con 10 (63 caratteri) lavorava un'ora e
 * venticinque minuti per un NON DIMOSTRATO. Gli enunciati dei libri ne
 * chiedono una dozzina. Per questo le visite si contano, e oltre
 * MAX_BIJ_VISITS la ricerca dei termini si ferma con quelli che ha: il ramo
 * è segnato come interrotto (exhausted), e il verdetto lo dice. Un termine
 * trovato resta un termine giusto: è la dimostrazione, con il suo
 * certificato, a controllare che sia una biiezione.
 *
 * La grammatica non conosce l'enunciato: solo gli insiemi e le biiezioni con
 * un nome nel ramo. Che cosa non costruisce: una biiezione che non è fatta
 * così, come \mathcal{P}(S) \sim \{0, 1\}^{S} o S \times (T \times V) \sim (S
 * \times T) \times V, e i passi con una biiezione con un nome tra prodotti,
 * da un'ipotesi S \times T \sim V. Lì l'enunciato resta NON DIMOSTRATO. */

/* 28q. Un termine della grammatica: una biiezione da from a to, scritta con
 * una delle regole w1-w4. Un passo w2 porta in next il termine che lo
 * segue. I termini vivono in bij[], rifatto per ogni testimone. */
typedef enum { BIJ_SAME, BIJ_NAMED, BIJ_PARTS, BIJ_MAPS } BijKind;
typedef struct {
    BijKind kind;           /* w1, w2 con un nome, w3, w4 */
    int from, to;           /* gli insiemi di partenza e di arrivo */
    int forward, backward;  /* BIJ_NAMED: la biiezione con un nome e la sua inversa, scambiate per un passo
                               all'indietro; BIJ_PARTS, BIJ_MAPS: le applicazioni definite, -1 finché il termine
                               non è scritto (bij_write()). Posti in symbols[] */
    int inner[2];           /* BIJ_PARTS: il termine tra le basi; BIJ_MAPS: quello tra gli insiemi di partenza,
                               poi quello tra gli insiemi d'arrivo. Posti in bij[]; -1 dove non servono */
    int next;               /* il termine da to in poi (w2), o -1 */
    int size;               /* i passi, compresi quelli dentro w3 e w4 */
} Bij;
static Bij bij[MAX_BIJ];
static int bij_count;

/* 28q. Le variabili delle definizioni: due per insieme, nate una volta per
 * enunciato da bijection_prepare(); bij_ready è 0 se non ci sono. */
static int (*bij_slot)[2],bij_ready;
static size_t bij_slot_capacity;

/* 28q. Quale testimone provare, dal più corto (0), e quanti se ne sono
 * trovati al più in un ramo: li usa claim_attempts(). */
static int witness_choice, witness_options;

/* 28q. Le visite di bij_terms() per l'equipotenza in corso: le azzera
 * bijection_witness(), e oltre MAX_BIJ_VISITS la ricerca si ferma. */
static long bij_visits;

/* 28q. Ritorna il posto in bij[] di una copia di b, o -1 se non c'è posto. */
static int bij_new(Bij b) {
    if (bij_count == MAX_BIJ) return -1;
    bij[bij_count] = b;
    return bij_count++;
}

/* 28q. Mette il termine t nella lista list[0..*count), ordinata dal più
 * corto, se ci sta tra i primi max; a parità di passi dopo quelli che ci
 * sono già. */
static void bij_keep(int *list, int *count, int max, int t) {
    if (t < 0) return;
    int at = *count;
    while (at > 0 && bij[list[at - 1]].size > bij[t].size) at--;
    if (at >= max) return;
    if (*count < max) ++*count;
    for (int i = *count - 1; i > at; i--) list[i] = list[i - 1];
    list[at] = t;
}

static int bij_terms(int from, int to, SlotSet visited, int *list, int max);

/* 28q. Mette in list[] i passi da from all'insieme step (w2 con un nome, w3,
 * w4), al più max, dai più corti. */
static void bij_steps(int from, int step, int *list, int *count, int max) {
    /* w2: le biiezioni con un nome tra due insiemi, nei due versi. */
    for (int i = 0; i < now->knowns; i++) {
        const Known *k = &now->known[i];
        if (k->origin != K_BIJECTION || k->negated) continue;
        const Sentence *e = now->known[k->parent].source;
        if (e->sides[0] != 1 || e->sides[1] != 1) continue;
        int a = side_sort(e, 0, 0), b = side_sort(e, 1, 0);
        if (a == from && b == step) bij_keep(list, count, max, bij_new((Bij){BIJ_NAMED, from, step, k->part[0], k->part[1], {-1, -1}, -1, 1}));
        if (b == from && a == step) bij_keep(list, count, max, bij_new((Bij){BIJ_NAMED, from, step, k->part[1], k->part[0], {-1, -1}, -1, 1}));
    }

    /* w3 e w4: termini tra gli insiemi su cui sono costruiti. */
    int a[MAX_WITNESSES], b[MAX_WITNESSES], na = 0, nb = 1;
    if (sort_data[from].kind != sort_data[step].kind || (sort_data[from].kind != SORT_PARTS && sort_data[from].kind != SORT_MAPS)) return;
    na = bij_terms(sort_data[from].base, sort_data[step].base, SLOT_EMPTY, a, max);
    if (sort_data[from].kind == SORT_MAPS) nb = bij_terms(sort_data[from].target, sort_data[step].target, SLOT_EMPTY, b, max);
    for (int i = 0; i < na; i++)
        for (int j = 0; j < nb; j++) {
            Bij made = {BIJ_PARTS, from, step, -1, -1, {a[i], -1}, -1, 1 + bij[a[i]].size};
            if (sort_data[from].kind == SORT_MAPS) { made.kind = BIJ_MAPS; made.inner[1] = b[j]; made.size += bij[b[j]].size; }
            bij_keep(list, count, max, bij_new(made));
        }
}

/* 28q. Mette in list[] i termini da from a to che non passano per gli
 * insiemi di visited (indice i: l'insieme di posto i), al più max, dai più
 * corti, e ritorna quanti sono. Finito il budget delle visite non ne cerca
 * altri, e annota che la ricerca è stata interrotta. */
static int bij_terms(int from, int to, SlotSet visited, int *list, int max) {
    int count = 0;
    if (++bij_visits > MAX_BIJ_VISITS) { exhausted = 1; return 0; }
    if (from == to) bij_keep(list, &count, max, bij_new((Bij){BIJ_SAME, from, to, -1, -1, {-1, -1}, -1, 0}));
    visited=slot_set_with(visited,from);
    for (int step = 0; step < sort_count; step++) {
        int first[MAX_WITNESSES], rest[MAX_WITNESSES], steps = 0, rests;
        if (slot_set_contains(visited,step)) continue;
        bij_steps(from, step, first, &steps, max);
        if (!steps) continue;
        rests = bij_terms(step, to, visited, rest, max);
        for (int i = 0; i < steps; i++)
            for (int j = 0; j < rests; j++) {
                Bij made = bij[first[i]];
                if (bij[rest[j]].kind != BIJ_SAME) { made.next = rest[j]; made.size += bij[rest[j]].size; }
                bij_keep(list, &count, max, bij_new(made));
            }
    }
    return count;
}

/* 28q. Ritorna l'elemento x mandato dal termine t, o dal suo inverso se
 * back: la scrittura come termine, con le applicazioni di ogni passo al loro
 * posto. Il termine deve essere scritto (bij_write()). L'inverso di una
 * composizione fa i passi dall'ultimo, ognuno all'indietro. */
static Elem *bij_apply(int t, Elem *x, int back) {
    if (t < 0) return x;
    const Bij *b = &bij[t];
    if (!back) return bij_apply(b->next, b->kind == BIJ_SAME ? x : elem_new(b->forward, 0, x, NULL), 0);
    Elem *rest = bij_apply(b->next, x, 1);
    return b->kind == BIJ_SAME ? rest : elem_new(b->backward, 0, rest, NULL);
}

/* 28q. Aggiunge al ramo la definizione spec dell'applicazione nuova map
 * (K_MAPDEF), e ritorna 0 se non c'è posto. */
static int mapdef_add(Sentence *spec, int map) {
    SlotValues nothing = SLOT_VALUES_EMPTY;

    int i = known_add(spec, 0, nothing, K_MAPDEF, -1);
    if (i < 0) return 0;
    int chosen = map;
    if (!known_parts(i, &chosen, 1)) return 0;
    name_known[map] = i;
    return 1;
}

/* 28q. Dà le loro applicazioni, con le definizioni, ai passi w3 e w4 del
 * termine t e di quelli dentro e dopo di lui, dai più interni (vedi la
 * testa del paragrafo per le forme). Ritorna 0 se non c'è stato posto. */
static int bij_write(int t) {
    if (t < 0) return 1;
    Bij *b = &bij[t];
    int defined = b->kind == BIJ_PARTS || b->kind == BIJ_MAPS;
    if (defined && b->forward >= 0) return 1;  /* già scritto */
    if (!bij_write(b->inner[0]) || !bij_write(b->inner[1]) || !bij_write(b->next)) return 0;
    if (!defined) return 1;
    int forward = map_symbol_new("gamma", 1, &b->from, b->to), backward = map_symbol_new("delta", 1, &b->to, b->from);
    if (forward < 0 || backward < 0) return 0;
    b->forward = forward;
    b->backward = backward;
    for (int side = 0; side < 2; side++) {
        /* side 0: \gamma da from a to; side 1: \delta da to a from. */
        int map = side ? backward : forward, arg = side ? b->to : b->from, value = side ? b->from : b->to, base = sort_data[value].base;
        Elem *object = slot_elem(bij_slot[arg][0]), *y = slot_elem(bij_slot[base][0]), *image = elem_new(map, 0, object, NULL);
        Sentence *spec;
        if (b->kind == BIJ_PARTS) {
            /* d2: y \in \gamma(X) \iff \beta^{-1}(y) \in X; y \in \delta(Y) \iff \beta(y) \in Y. */
            spec = axiom_join(S_IFF, axiom_atom(S_HOLDS, sort_data[value].symbol, y, image), axiom_atom(S_HOLDS, sort_data[arg].symbol, bij_apply(b->inner[0], y, !side), object));
        } else {
            /* d3: \gamma(f)(y) = \beta(f(\alpha^{-1}(y))); \delta(F)(y) = \beta^{-1}(F(\alpha(y))). */
            Elem *inside = elem_new(sort_data[arg].symbol, 0, object, bij_apply(b->inner[0], y, !side));
            spec = axiom_atom(S_EQUAL, -1, elem_new(sort_data[value].symbol, 0, image, y), bij_apply(b->inner[1], inside, side));
        }
        if (!mapdef_add(axiom_bind(S_FORALL, bij_slot[arg][0], axiom_bind(S_FORALL, bij_slot[base][0], spec)), map)) return 0;
    }
    return 1;
}

/* 28q. Un testimone di un'equipotenza, prima di essere scritto con le sue
 * definizioni: per ogni componente j del lato B il termine term[j] (un posto
 * in bij[]; -1 per la seconda di un lato con una sola componente), che parte
 * dalla componente swap ? 1 - j : j del lato A; size è la somma dei passi,
 * che dà l'ordine in cui i testimoni si provano. */
typedef struct {
    int term[2], swap, size;
} Witness;

/* 28q-2. L'istanza della condizione nota di posto r, l'equipotenza falsa A
 * \sim B: costruisce con la grammatica i testimoni, prende quello di numero
 * witness_choice (dal più corto), ne scrive le definizioni e aggiunge
 * \lnot D(\gamma, \delta). Una sola volta per ramo. Ritorna 1 se l'ha
 * aggiunta. */
static int bijection_witness(int r) {
    const Sentence *e = now->known[r].source;
    Witness found[2 * MAX_WITNESSES * MAX_WITNESSES], chosen;
    int count = 0, m = e->sides[0], n = e->sides[1];
    for (int i = r + 1; i < now->knowns; i++)
        if (now->known[i].parent == r && now->known[i].origin == K_BIJECTION) return 0;
    if (!bij_ready || m != n) return 0;

    /* I testimoni: per ogni modo di accoppiare le componenti, un termine per
     * componente; in ordine di passi, a parità prima senza scambio. */
    bij_count = 0;
    bij_visits = 0;
    for (int swap = 0; swap < m; swap++) {
        int list[2][MAX_WITNESSES], length[2];
        for (int j = 0; j < n; j++) length[j] = bij_terms(side_sort(e, 0, swap ? 1 - j : j), side_sort(e, 1, j), SLOT_EMPTY, list[j], MAX_WITNESSES);
        for (int a = 0; a < length[0]; a++)
            for (int b = 0; b < (n == 2 ? length[1] : 1); b++) {
                Witness w = {{list[0][a], n == 2 ? list[1][b] : -1}, swap, bij[list[0][a]].size + (n == 2 ? bij[list[1][b]].size : 0)};
                int at = count++;
                while (at > 0 && found[at - 1].size > w.size) { found[at] = found[at - 1]; at--; }
                found[at] = w;
            }
    }
    if (count > MAX_WITNESSES) count = MAX_WITNESSES;
    if (count > witness_options) witness_options = count;
    if (witness_choice >= count) return 0;
    chosen = found[witness_choice];

    /* Le applicazioni: quelle di un solo passo con un nome, w3 o w4 se il
     * lato ha una componente; altrimenti nuove, definite con d1. */
    int map[4];
    for (int j = 0; j < n; j++)
        if (!bij_write(chosen.term[j])) return 0;
    const Bij *only = &bij[chosen.term[0]];
    if (m == 1 && only->kind != BIJ_SAME && only->next < 0) {
        map[0] = only->forward;
        map[1] = only->backward;
    } else {
        int domain[2], range;
        for (int j = 0; j < n + m; j++) {
            int arity = identity_map_sorts(e, j, domain, &range);
            if ((map[j] = map_symbol_new(j < n ? "gamma" : "delta", arity, domain, range)) < 0) return 0;
        }
        for (int j = 0; j < n + m; j++) {
            /* \gamma_{j}(x) = \beta_{j}(x_{i}), con i la componente da cui parte
             * \beta_{j}; \delta_{i}(y) = \beta_{j}^{-1}(y_{j}). */
            int forward = j < n, at = forward ? j : j - n, from = forward ? 0 : 1, count_args = e->sides[from];
            int term = forward ? j : (chosen.swap ? 1 - at : at), source = forward ? (chosen.swap ? 1 - j : j) : term;
            Elem *x[2];
            for (int a = 0; a < count_args; a++) x[a] = slot_elem(bij_slot[side_sort(e, from, a)][a]);
            Sentence *spec = axiom_atom(S_EQUAL, -1, map_apply(map[j], x, count_args), bij_apply(chosen.term[term], x[source], !forward));
            for (int a = count_args - 1; a >= 0; a--) spec = axiom_bind(S_FORALL, bij_slot[side_sort(e, from, a)][a], spec);
            if (!mapdef_add(spec, map[j])) return 0;
        }
    }
    int instance = known_add(equipotent_identities(e, map), 1, now->known[r].value, K_BIJECTION, r);
    if (instance < 0) return 0;
    return known_parts(instance, map, n + m);
}

/* 28q. Le istanze della definizione di un'applicazione (rule, una
 * condizione K_MAPDEF): una per ogni elemento presente scritto come la sua
 * forma, \gamma(x), y \in \gamma(X) o \gamma(f)(y), con al posto delle variabili
 * ciò che vi compare. Come per le parti di 28j, la definizione si usa dove
 * l'applicazione compare. Ritorna quante istanze ha aggiunto. */
static int instance_mapdef(const Rule *rule) {
    const Elem *shape = rule->body->kind == S_IFF ? rule->body->a->left : rule->body->left, *pattern[MAX_PATTERN];
    short target[MAX_PATTERN];
    SlotValues value = SLOT_VALUES_EMPTY;
    int made = 0;
    value = slot_values_copy(now->known[rule->known].value);
    if (work_allocation_failed) return 0;
    for (int id = 1, last = now->grounds; id < last && !exhausted; id++) {
        if (ground[id].symbol != shape->symbol) continue;
        int count = 0;
        slot_values_load(value, now->known[rule->known].value);
        for (int i = 0; i < 2 && shape->arg[i]; i++) { pattern[count] = shape->arg[i]; target[count++] = ground[id].arg[i]; }
        made += instance_match(rule, pattern, target, count, value);
    }
    return made;
}

/* 28q. Ritorna 1 se nella condizione s c'è un'equipotenza. */
static int sentence_has_equipotence(const Sentence *s) {
    return s && (s->kind == S_EQUIPOTENT || sentence_has_equipotence(s->a) || sentence_has_equipotence(s->b));
}

/* 28q. Prepara le variabili delle definizioni, due per insieme, se
 * l'enunciato root ha un'equipotenza. Un errore di risorse interrompe la
 * preparazione; una rinuncia lessicale non contamina la prova successiva. */
static void bijection_prepare(const Sentence *root) {
    const char *before = syntax_error;
    bij_ready = 0;
    if (!sentence_has_equipotence(root)) return;
    if (!work_reserve((void **)&bij_slot,&bij_slot_capacity,(size_t)sort_count,sizeof *bij_slot)) return;
    for (int i=0;i<sort_count && syntax_error==before && !work_allocation_failed;i++)
        for (int j=0;j<2 && syntax_error==before && !work_allocation_failed;j++) bij_slot[i][j]=unfold_slot(i);
    bij_ready=syntax_error==before && !work_allocation_failed;
    syntax_error = before;
}

/* 28r. LE ISTANZE SCELTE DA UN MODELLO CANDIDATO
 *
 * (Sta qui, dentro 28d, accanto alle altre istanze; la lettera è venuta dopo
 * le altre.)
 *
 * A che cosa serve. Le istanze di 28-3 si scelgono dalla forma: tutte sui
 * nomi, quelle che riscrivono un elemento presente, quelle che decidono un
 * confronto. Nelle dimostrazioni sulle famiglie di parti (una partizione
 * comune, la controimmagine di una partizione) e sugli ordini tra parti o
 * tra applicazioni le scelte per forma sono migliaia, e quella giusta
 * arriva quando le tabelle sono già piene, oppure non arriva mai: per "ogni
 * elemento a di S sta in un pezzo di F*" serve l'ipotesi "ogni t di T sta in
 * un pezzo di F" con t = f(a), un elemento di cui nessuno parla ancora. Qui
 * le istanze si scelgono dal significato, con un modello.
 *
 * Il modello candidato di un ramo. Gli elementi di ogni insieme sono le
 * classi degli elementi presenti (gli uguali per ciò che si sa sono uno
 * solo); un simbolo applicato vale l'elemento presente scritto così, se c'è,
 * altrimenti un valore "altro", diverso da tutti gli elementi presenti e
 * uguale solo a se stesso; due classi diverse sono elementi diversi; una
 * parte o una relazione vale solo dove si sa che vale. È il modello più
 * piccolo che le uguaglianze e le appartenenze note permettono, e i
 * quantificatori vi si calcolano provando gli elementi presenti: un conto
 * finito. È la tecnica dei dimostratori SMT detta MBQI, "model-based
 * quantifier instantiation" (Ge e de Moura, 2009).
 *
 * La regola. Un "per ogni" noto che nel modello candidato è falso in
 * qualche elemento a dice che il modello non va: l'istanza su a è vera
 * (28-3, come ogni istanza) e nel modello è falsa, quindi aggiungerla
 * costringe il ramo a cambiare. Porta una contraddizione, o un fatto nuovo
 * (il modello cresce), o un "esiste" a cui dare un nome (nasce un elemento),
 * o una disgiunzione da distinguere. Le istanze vere nel modello non dicono
 * nulla di nuovo su di lui, e si lasciano. Così "ogni t di T sta in un pezzo
 * di F", su t = f(a), nel modello è falsa perché i pezzi presenti sono
 * nessuno: l'istanza dà un pezzo nuovo, quello che serve. Per ogni "per ogni"
 * si prende, a ogni giro, la prima istanza falsa sugli elementi in ordine
 * di età: una sola, come fanno i dimostratori SMT, perché ognuna cambia il
 * modello e le altre vanno ricalcolate su quello nuovo.
 *
 * Tre aggiunte, ognuna con il suo perché.
 *
 *   28r-1. Un insieme senza elementi presenti, in cui un'applicazione
 *          dichiarata manda un elemento presente a: si aggiunge f(a). Il
 *          modello deve dare un valore a f(a), e un valore è un elemento:
 *          senza, i "per ogni" su quell'insieme non avrebbero dove provarsi.
 *          f(a) c'è: f è un'applicazione e a un elemento del suo dominio.
 *   28r-2. L'estensionalità di 28n resta come in 28n, provata solo dove un
 *          confronto è già deciso. Nel modello candidato due parti con gli
 *          stessi elementi presenti sembrano uguali in tutto ciò che si
 *          prova, e l'estensionalità sembrerebbe falsa su quasi tutte le
 *          coppie: le sue istanze, che servono solo a distinguere i casi,
 *          riempirebbero i rami.
 *   28r-3. La generazione. Un elemento nato da un "esiste" dentro
 *          un'istanza ha generazione 1 più la più alta degli elementi
 *          dell'istanza; quelli dichiarati e quelli a cui dà un nome
 *          l'enunciato stesso, senza istanze, hanno generazione 0. Il modello
 *          candidato prova solo gli elementi fino a una generazione data.
 *          Senza, un'ipotesi come "ogni x è in relazione con qualche a"
 *          darebbe un elemento nuovo da ogni elemento, e quello un altro, in
 *          una catena senza fine. Le generazioni ammesse crescono come in
 *          una ricerca ad approfondimento progressivo: prima 2, poi 4
 *          (model_generations[]).
 *
 * Quando. Sono le ultime prove di claim_attempts(), dopo quelle di sempre e
 * di 28o: le affermazioni che quelle dimostrano non cambiano, né nella
 * dimostrazione scritta né nel certificato. Il modello cambia solo quali
 * istanze si provano: ognuna è un'istanza di 28-3, scritta, ricontrollata
 * da 28e e portata nel certificato (28f) come le altre, e il verificatore la
 * rilegge senza sapere da dove viene. Le distinzioni di casi, le scelte di
 * parti (28k) e i casi che si chiudono subito (28l) restano quelli di
 * refute(). Il modello candidato non decide mai nulla da solo: non è un
 * controesempio (non tiene conto delle disgiunzioni in attesa, e i suoi
 * insiemi sono solo gli elementi nominati), e non trovarvi istanze false
 * vuol dire solo che la ricerca si ferma. */

/* 1 durante le prove di questo paragrafo: instantiate() sceglie le istanze
 * con il modello candidato. */
static int model_guided;

/* Il valore, nel modello candidato, di un simbolo applicato che non è
 * presente: "altro", diverso da ogni posto di ground[]. */
#define CANDIDATE_ELSE (-3)

/* Le generazioni ammesse nelle prove successive (28r-3), e quella ammessa
 * nella prova in corso. */
static const int model_generations[] = {2, 4};
static int generation_limit;

/* Il modello candidato del ramo in corso: per ogni insieme, un elemento
 * presente per ogni classe (il più vecchio, posto in ground[]), in ordine di
 * età, e quanti sono. Lo rifà candidate_prepare(). candidate_steps conta i
 * passi del calcolo, fino a MAX_CANDIDATE_STEPS per giro di istanze. */
static short (*candidate_domain)[MAX_GROUND];
static int *candidate_size;
static size_t candidate_domain_capacity,candidate_size_capacity;
static long long candidate_steps;

/* Ritorna il valore dell'elemento e nel modello candidato, con le variabili
 * agli elementi di value[]: il rappresentante della sua classe, oppure
 * CANDIDATE_ELSE se e è un simbolo applicato che non è presente (anche
 * perché non lo è un suo argomento). Una parte o una relazione applicata
 * vale la classe di "vero" quando si sa che vale. Va chiamata dopo
 * closure(), come ground_lookup() con G_CLASS. */
static int candidate_term(const Elem *e, SlotValues value) {
    int arg[2] = {-1, -1};
    if (e->symbol < 0) return slot_values_get(value, e->slot) >= 0 ? now->rep[slot_values_get(value, e->slot)] : CANDIDATE_ELSE;
    for (int i = 0; i < 2 && e->arg[i]; i++) {
        arg[i] = candidate_term(e->arg[i], value);
        if (arg[i] == CANDIDATE_ELSE) return CANDIDATE_ELSE;
    }
    int found = ground_lookup(e->symbol, arg[0], arg[1], arg[0] < 0 ? G_EXACT : G_CLASS);
    return found >= 0 ? now->rep[found] : CANDIDATE_ELSE;
}

/* Ritorna il valore della condizione s nel modello candidato, con le
 * variabili libere agli elementi di value[]: 1 vera, 0 falsa, -1 se non si
 * calcola. Non si calcolano i quantificatori su parti di 17u (le loro parti
 * le sceglie 28k), né nulla oltre MAX_CANDIDATE_STEPS passi; un connettivo
 * con una parte che non si calcola vale -1, a meno che l'altra lo decida.
 * value[] viene usato anche per le variabili che s lega, e rimesso com'era. */
static int candidate_holds(const Sentence *s, SlotValues value) {
    int a, b = -1;
    if (++candidate_steps > MAX_CANDIDATE_STEPS) return -1;
    switch (s->kind) {
    case S_TRUE:
        return 1;
    case S_NOT:
        a = candidate_holds(s->a, value);
        return a < 0 ? a : !a;
    case S_EQUAL:
        /* Due "altro" sono lo stesso valore, e nessuno dei due è un
         * elemento presente. */
        return candidate_term(s->left, value) == candidate_term(s->right, value);
    case S_HOLDS:
        return candidate_term(s->left, value) == now->rep[0];
    case S_AND:
        if ((a = candidate_holds(s->a, value)) == 0 || (b = candidate_holds(s->b, value)) == 0) return 0;
        return a == 1 && b == 1 ? 1 : -1;
    case S_OR: case S_IMPLIES:
        a = candidate_holds(s->a, value);
        if (s->kind == S_IMPLIES && a >= 0) a = !a;
        if (a == 1 || (b = candidate_holds(s->b, value)) == 1) return 1;
        return a == 0 && b == 0 ? 0 : -1;
    case S_IFF:
        a = candidate_holds(s->a, value);
        b = candidate_holds(s->b, value);
        return a < 0 || b < 0 ? -1 : a == b;
    case S_FORALL: case S_EXISTS: {
        /* Ogni elemento del modello, finché uno decide. */
        int sort = slot_data[s->slot].sort, every = s->kind == S_FORALL, result = every;
        short saved = slot_values_get(value, s->slot);
        for (int i = 0; i < candidate_size[sort] && result != !every; i++) {
            value.data[s->slot] = candidate_domain[sort][i];
            int v = candidate_holds(s->a, value);
            if (v < 0) result = -1;
            else if (v != every) result = !every;
        }
        value.data[s->slot] = saved;
        return result;
    }
    case S_FORALL_PART: case S_EXISTS_PART: case S_EQUIPOTENT:
        /* Le parti di 17u le sceglie 28k, le biiezioni di un'equipotenza 28q. */
    case S_MEMBER: case S_INCLUDED: case S_SAME: case S_UNIQUE: case S_COUNT:  /* questi non arrivano qui (17q) */
        break;
    }
    return -1;
}

/* Rifà il modello candidato del ramo in corso (candidate_domain[]): per ogni
 * insieme, il più vecchio degli elementi presenti di ogni classe la cui
 * generazione non supera generation_limit (28r-3). */
static void candidate_prepare(void) {
    for (int i = 0; i < sort_count; i++) candidate_size[i] = 0;
    for (int id = 1; id < now->grounds; id++) {
        int sort = symbols[ground[id].symbol].range, fresh = 1;
        if (sort == TRUTH || ground_generation(id) > generation_limit) continue;
        for (int c = 0; c < candidate_size[sort] && fresh; c++) fresh = now->rep[candidate_domain[sort][c]] != now->rep[id];
        if (fresh) candidate_domain[sort][candidate_size[sort]++] = (short)id;
    }
}

/* 28r-1. Aggiunge f(a) per ogni applicazione dichiarata f, di un
 * argomento, che va in un insieme senza elementi nel modello candidato, con
 * a il primo elemento del modello nel suo dominio. Ritorna quanti elementi
 * ha aggiunto; se qualcuno, rifà la chiusura e il modello. */
static int candidate_complete(void) {
    int made = 0;
    for (int f = 0; f < declared_symbols; f++) {
        const Symbol *map = &symbols[f];
        if (map->arity != 1 || map->range == TRUTH || symbol_bound[f] || symbol_structure(f) >= 0) continue;
        if (candidate_size[map->range] > 0 || candidate_size[map->domain[0]] == 0) continue;
        made += ground_lookup(f, candidate_domain[map->domain[0]][0], -1, G_CREATE) >= 0;
    }
    if (made) {
        closure();
        candidate_prepare();
    }
    return made;
}

/* Aggiunge la prima istanza del "per ogni" rule che è falsa nel modello
 * candidato, provando le scelte degli elementi del modello come un
 * contachilometri; se le scelte sono più di MAX_TUPLES non ne prova
 * nessuna. Ritorna 1 se l'ha aggiunta. Un'istanza falsa che c'è già (una
 * disgiunzione in attesa) non conta, e si passa alla scelta successiva. */
static int instance_model(const Rule *rule) {
    static int *pick;
    static size_t capacity;
    if (!work_reserve((void **)&pick, &capacity, (size_t)rule->slots, sizeof *pick)) { exhausted = 1; return 0; }
    long long tuples = 1;
    SlotValues value = SLOT_VALUES_EMPTY;
    /* Un prodotto interrotto al budget evita overflow con molte variabili.
     * Un dominio vuoto, anche dopo il prefisso gia grande, da zero istanze. */
    for (int j = 0; j < rule->slots; j++) {
        int size = candidate_size[slot_data[rule->slot[j]].sort];
        if (!size) return 0;
        if (tuples <= MAX_TUPLES) tuples *= size;
        pick[j] = 0;
    }
    if (!tuples || tuples > MAX_TUPLES) return 0;
    value = slot_values_copy(now->known[rule->known].value);
    if (work_allocation_failed) return 0;
    for (int more = 1; more && !exhausted && candidate_steps <= MAX_CANDIDATE_STEPS; ) {
        for (int j = 0; j < rule->slots; j++) value.data[rule->slot[j]] = candidate_domain[slot_data[rule->slot[j]].sort][pick[j]];

        /* Falsa: il valore opposto al segno con cui il corpo è noto. */
        if (candidate_holds(rule->body, value) == rule->negated && instance_add(rule, value)) return 1;
        more = 0;
        for (int j = 0; j < rule->slots && !more; j++) {
            if (++pick[j] < candidate_size[slot_data[rule->slot[j]].sort]) more = 1; else pick[j] = 0;
        }
    }
    return 0;
}

/* 28-3. Aggiunge le istanze dei "per ogni" noti che vale la pena provare,
 * come descritto in testa al capitolo ("Quali istanze"), e ritorna quante
 * ne ha aggiunte. Va chiamata dopo settle(), con le classi aggiornate: le
 * istanze aggiunte non vengono aperte qui, quindi le classi non cambiano
 * mentre si cerca. Le definizioni di 28j hanno le loro (instance_definition()),
 * più quelle che decidono un confronto. Con model_guided le istanze sono
 * quelle di 28r, scelte con il modello candidato. */
static int instantiate(void) {
    int made = 0, before = now->knowns;
    int *slot = NULL; size_t capacity = 0;

    /* 28r. Il modello candidato, con gli elementi che gli mancano (28r-1). */
    if (model_guided) {
        candidate_steps = 0;
        candidate_prepare();
        made += candidate_complete();
    }
    for (int r = 0; r < before && !exhausted; r++) {
        /* Un "per ogni parte" ha le sue istanze in 28k; un'equipotenza
         * falsa il suo testimone (28q-2). */
        if (now->known[r].stage != K_RULE || part_quantifier(now->known[r].source)) continue;
        if (now->known[r].source->kind == S_EQUIPOTENT) { made += bijection_witness(r); continue; }
        Rule rule = {.known=r, .all=SLOT_EMPTY, .body=now->known[r].source, .negated=now->known[r].negated};
        for (const Sentence *q = rule.body; (q->kind == S_FORALL || q->kind == S_EXISTS) && (q->kind == S_FORALL) != rule.negated; q = q->a)
            rule.slots++;
        if (!work_reserve((void **)&slot, &capacity, (size_t)rule.slots, sizeof *slot)) { exhausted = 1; break; }
        rule.slot = slot;
        int at = 0;
        while ((rule.body->kind == S_FORALL || rule.body->kind == S_EXISTS) &&
               (rule.body->kind == S_FORALL) != rule.negated) {
            rule.all = slot_set_with(rule.all, rule.body->slot);
            slot[at++] = rule.body->slot;
            rule.body = rule.body->a;
        }

        /* 28r. Una definizione di 28j o di 28q anche dove la sua parte o la
         * sua applicazione compare, l'estensionalità come in 28n (28r-2), il
         * resto dal modello. */
        if (model_guided) {
            if (now->known[r].origin == K_DEFINED) made += instance_definition(&rule);
            if (now->known[r].origin == K_MAPDEF) made += instance_mapdef(&rule);
            made += known_law(r) == LAW_EXTENSIONALITY ? instance_choices(&rule, 0) : instance_model(&rule);
            continue;
        }
        if (now->known[r].origin == K_DEFINED) {
            made += instance_definition(&rule) + instance_choices(&rule, 0);
            continue;
        }
        if (now->known[r].origin == K_MAPDEF) {
            made += instance_mapdef(&rule);
            continue;
        }

        /* 28n. L'estensionalità solo dove un confronto è già deciso (X \neq
         * Y noto), la comprensione solo sui nomi con cui si comincia: vedi
         * "Quali istanze delle leggi" in testa a 28n. */
        int law = known_law(r), budget = MAX_FREE_TUPLES;
        if (law != LAW_EXTENSIONALITY) made += instance_choices(&rule, 1);
        if (!law) made += instance_rewrite(&rule, rule.body);
        if (law != LAW_COMPREHENSION) made += instance_choices(&rule, 0);
        if (!law && rule.slots == 1) made += instance_trigger(&rule, rule.body, &budget);
    }
    free(slot);
    return made;
}

/* 28e. LA DIMOSTRAZIONE SCRITTA, E IL SUO CONTROLLO */

/* Perché un confronto tra due elementi ha un certo valore: è vero per una
 * catena di uguaglianze tra i due, oppure è falso perché due catene li
 * portano ai due elementi di un fatto "diversi". */
typedef struct {
    int value;       /* 1 vero, 0 falso, -1 non si sa */
    Chain chain[2];  /* vero: chain[0] va da un elemento all'altro. Falso: le
                        due catene, dai due elementi a quelli di `against` */
    int against;     /* falso: il fatto "diversi", posto in known[] */
} Reason;

/* Ricostruisce in *reason ciò che si sapeva del confronto s, con gli
 * elementi di value[] al posto delle variabili, usando solo i fatti con
 * numero d'ordine minore di stamp. Ogni catena trovata è già stata
 * ricontrollata anello per anello (chain_between()). */
static void literal_reason(const Sentence *s, SlotValues value, int stamp, Reason *reason) {
    int a = elem_ground(s->left, value, G_EXACT), b = s->kind == S_EQUAL ? elem_ground(s->right, value, G_EXACT) : 0;
    reason->value = -1;
    if (a < 0 || b < 0) return;
    if (chain_between(&reason->chain[0], a, b, stamp)) { reason->value = 1; return; }
    for (int i = 0; i < now->differents; i++) {
        const Known *d = &now->known[now->different[i]];
        if (d->stamp >= stamp) continue;
        for (int swap = 0; swap < 2; swap++) {
            if (!chain_between(&reason->chain[0], a, swap ? d->right : d->left, stamp) ||
                !chain_between(&reason->chain[1], b, swap ? d->left : d->right, stamp)) continue;
            reason->value = 0;
            reason->against = now->different[i];
            return;
        }
    }
}

/* Un passo 28-1 riletto per essere scritto e ricontrollato: le condizioni
 * elementari della premessa, con il valore di quelle che servono, e i fatti
 * su cui quei valori poggiano. Una condizione elementare è ciò che i
 * connettivi collegano: un confronto, un quantificatore, una dichiarazione. */
typedef struct {
    const Sentence *atom[MAX_PROP_ATOMS];
    int value[MAX_PROP_ATOMS];  /* 1, 0, oppure -1: non serve o non si sa */
    int atoms;
    short used[(2 * MAX_CHAIN + 1) * MAX_PROP_ATOMS];
    int uses;
} Deduction;

/* Elenca in d le condizioni elementari di s. Ritorna 0 se sono troppe. */
static int deduction_atoms(const Sentence *s, Deduction *d) {
    if (s->kind == S_NOT) return deduction_atoms(s->a, d);
    if (s->kind == S_AND || s->kind == S_OR || s->kind == S_IMPLIES || s->kind == S_IFF) return deduction_atoms(s->a, d) && deduction_atoms(s->b, d);
    if (d->atoms == MAX_PROP_ATOMS) return 0;
    d->atom[d->atoms++] = s;
    return 1;
}

/* Ritorna il valore di s quando la condizione elementare di posto i vale
 * vero se il bit i di bits è 1, falso altrimenti. */
static int deduction_value(const Sentence *s, const Deduction *d, unsigned bits) {
    switch (s->kind) {
    case S_NOT: return !deduction_value(s->a, d, bits);
    case S_AND: return deduction_value(s->a, d, bits) && deduction_value(s->b, d, bits);
    case S_OR: return deduction_value(s->a, d, bits) || deduction_value(s->b, d, bits);
    case S_IMPLIES: return !deduction_value(s->a, d, bits) || deduction_value(s->b, d, bits);
    case S_IFF: return deduction_value(s->a, d, bits) == deduction_value(s->b, d, bits);
    default: break;
    }
    for (int i = 0; i < d->atoms; i++)
        if (d->atom[i] == s) return bits >> i & 1;
    return 0;
}

/* Controllo di un passo con la tabella di verità: ritorna 1 se, in ogni
 * modo di dare vero o falso alle condizioni elementari che rispetta i
 * valori noti di d, quando premise è vera lo è anche conclusion (negata se
 * negated). Con conclusion NULL chiede che premise non sia mai vera: è una
 * contraddizione. Le condizioni di cui non si sa nulla sono lasciate
 * libere, quindi il passo è valido qualunque cosa valgano. */
static int deduction_follows(const Known *premise, const Sentence *conclusion, int negated, const Deduction *d) {
    for (unsigned bits = 0; bits < 1u << d->atoms; bits++) {
        int respects = 1;
        for (int i = 0; i < d->atoms && respects; i++) respects = d->value[i] < 0 || (int)(bits >> i & 1) == d->value[i];
        if (!respects || deduction_value(premise->source, d, bits) == premise->negated) continue;
        if (!conclusion || deduction_value(conclusion, d, bits) == negated) return 0;
    }
    return 1;
}

/* Rilegge il passo che dalla condizione nota di posto premise trae
 * conclusion (negata se negated; NULL per una contraddizione), fatto quando
 * il numero d'ordine era stamp. Riempie *d con le sole condizioni
 * elementari che servono e con i fatti su cui poggiano, e ritorna 1 se il
 * passo supera il controllo della tabella di verità. Se non lo supera è un
 * errore del programma, che unjustified_steps registra; se le condizioni
 * elementari sono troppe per la tabella il passo non si può controllare, e
 * la risposta è 0 senza che sia un errore.
 *
 * "Che servono": si parte da tutte quelle di cui si sapeva il valore, e si
 * prova a dimenticarle una per volta; quelle senza cui il passo regge
 * ancora non vengono scritte. */
static int deduction_read(int premise, const Sentence *conclusion, int negated, int stamp, Deduction *d) {
    const Known *p = &now->known[premise];
    Reason reason;
    d->atoms = d->uses = 0;
    if (!deduction_atoms(p->source, d)) return 0;
    for (int i = 0; i < d->atoms; i++) {
        d->value[i] = d->atom[i]->kind == S_TRUE ? 1 : -1;
        if (d->atom[i]->kind != S_EQUAL && d->atom[i]->kind != S_HOLDS) continue;
        literal_reason(d->atom[i], p->value, stamp, &reason);
        d->value[i] = reason.value;
    }
    if (!deduction_follows(p, conclusion, negated, d)) { unjustified_steps++; return 0; }
    for (int i = 0; i < d->atoms; i++) {
        int kept = d->value[i];
        if (kept < 0 || d->atom[i]->kind == S_TRUE) continue;
        d->value[i] = -1;
        if (!deduction_follows(p, conclusion, negated, d)) d->value[i] = kept;
    }

    /* I fatti usati dalle condizioni rimaste. */
    for (int i = 0; i < d->atoms; i++) {
        if (d->value[i] < 0 || d->atom[i]->kind == S_TRUE) continue;
        literal_reason(d->atom[i], p->value, stamp, &reason);
        for (int c = 0; c < (reason.value ? 1 : 2); c++)
            for (int j = 0; j < reason.chain[c].links; j++) d->used[d->uses++] = reason.chain[c].fact[j];
        if (!reason.value) d->used[d->uses++] = (short)reason.against;
    }
    return 1;
}

/* Le condizioni note che servono alla contraddizione del ramo, e il numero
 * con cui ognuna è citata nella dimostrazione scritta. */
static char needed[MAX_KNOWN];
static short label[MAX_KNOWN];

/* Scrive il riferimento alla condizione nota di posto i: (H3) per la terza
 * ipotesi, che è la condizione di posto 2, e il suo numero per le altre. */
static void put_label(int i) {
    if (now->known[i].origin == K_GIVEN) proof_add("(H%d)", i + 1); else proof_add("(%d)", label[i]);
}

/* Scrive ", by (3), (5)" con i riferimenti ai fatti delle catene di reason
 * e, se il confronto è falso, al fatto "diversi". Ogni fatto una volta. */
static void put_reason_labels(const Reason *reason) {
    short seen[2 * MAX_CHAIN + 1];
    int count = 0;
    for (int c = 0; c < (reason->value ? 1 : 2); c++)
        for (int j = 0; j < reason->chain[c].links; j++) seen[count++] = reason->chain[c].fact[j];
    if (!reason->value) seen[count++] = (short)reason->against;
    for (int i = 0, written = 0; i < count; i++) {
        int repeated = 0;
        for (int j = 0; j < i; j++) repeated = repeated || seen[j] == seen[i];
        if (repeated) continue;
        proof_add(written++ ? ", " : " by ");
        put_label(seen[i]);
    }
}

/* Scrive perché il confronto s ha il valore che reason dice: la catena di
 * uguaglianze, se è un'uguaglianza vera con più di un anello, altrimenti
 * il confronto stesso; poi i fatti usati. */
static void put_reason(const Sentence *s, SlotValues value, const Reason *reason) {
    const Chain *c = &reason->chain[0];
    proof_add("$");
    if (reason->value && s->kind == S_EQUAL && c->links > 1) {
        for (int i = 0; i <= c->links; i++) { if (i) proof_add(" = "); put_ground(c->term[i], 0); }
    } else {
        put_sentence(s, !reason->value, value, 0);
    }
    proof_add("$");
    put_reason_labels(reason);
}

/* Ritorna 1 se la condizione nota k è proprio `written`, letta con il
 * segno negated: le negazioni in testa a written passano nel segno, come
 * fa known_add(). */
static int known_is(const Known *k, const Sentence *written, int negated) {
    while (written->kind == S_NOT) { written = written->a; negated = !negated; }
    return k->source == written && k->negated == negated;
}

/* 28j. Ritorna 1 se l'elemento e non ha variabili libere fuori da bound (il
 * bit i per la variabile di posto i). Il bitset cresce anche per le
 * variabili nuove introdotte dalle definizioni di 28q. */
static int elem_closed(const Elem *e, SlotSet bound) {
    if (!e) return 1;
    if (e->symbol < 0) return slot_set_contains(bound, e->slot);
    return elem_closed(e->arg[0], bound) && elem_closed(e->arg[1], bound);
}

/* 28j. Ritorna 1 se la condizione s non ha variabili libere fuori da bound. */
static int sentence_closed(const Sentence *s, SlotSet bound) {
    if (!s) return 1;
    if (s->kind == S_FORALL || s->kind == S_EXISTS) bound = slot_set_with(bound, s->slot);
    return elem_closed(s->left, bound) && elem_closed(s->right, bound) && sentence_closed(s->a, bound) && sentence_closed(s->b, bound);
}

/* 28j. Controlla la definizione di posto i: è "per ogni x di S, x \in D se
 * e solo se c", chiusa, con D una parte di S nuova, che c non nomina e
 * nessuna condizione nota prima di questa nomina. Ritorna 1 se regge. */
static int definition_derived(int i) {
    const Known *k = &now->known[i];
    const Sentence *s = k->source;
    if (k->parts != 1) return 0;
    int part = k->part[0];
    if (k->negated || s->kind != S_FORALL || s->a->kind != S_IFF || s->a->a->kind != S_HOLDS || !sentence_closed(s, SLOT_EMPTY)) return 0;
    const Elem *member = s->a->a->left;
    if (member->symbol != part || part < declared_symbols || !part_of(part, slot_data[s->slot].sort) || member->arg[0]->symbol >= 0 ||
        member->arg[0]->slot != s->slot || sentence_mentions(s->a->b, part))
        return 0;
    for (int j = 0; j < i; j++)
        if (sentence_mentions(now->known[j].source, part)) return 0;
    return 1;
}

/* 28q. Ritorna 1 se nell'elemento presente id compare il simbolo symbol. */
static int ground_mentions(int id, int symbol) {
    if (id < 0) return 0;
    const Ground *g = &ground[id];
    return g->symbol == symbol || ground_mentions(g->arg[0], symbol) || ground_mentions(g->arg[1], symbol);
}

/* 28q. Ritorna 1 se il simbolo symbol compare in una delle condizioni note
 * prima di quella di posto i: nella condizione, o negli elementi al posto
 * delle sue variabili. */
static int mentioned_before(int i, int symbol) {
    for (int j = 0; j < i; j++) {
        const Known *k = &now->known[j];
        if (sentence_mentions(k->source, symbol)) return 1;
        for (int v = 0; v < k->value.count; v++)
            if (slot_values_get(k->value, v) > 0 && ground_mentions(slot_values_get(k->value, v), symbol)) return 1;
    }
    return 0;
}

/* 28q. Ritorna 1 se t è la variabile di posto slot. */
static int is_variable(const Elem *t, int slot) { return t && t->symbol < 0 && t->slot == slot; }

/* 28q. Ritorna 1 se l'elemento e sta nell'insieme sort (TRUTH per una parte
 * o una relazione applicata), con ogni simbolo applicato a tanti argomenti
 * quanti ne chiede, ognuno nel suo insieme. Il lettore lo controlla per ciò
 * che legge (elem_expect()); le identità e le definizioni di 28q le
 * costruisce il motore, e questo è il loro controllo. */
static int elem_typed(const Elem *e, int sort) {
    if (!e) return 0;
    if (e->symbol < 0) return slot_data[e->slot].sort == sort;
    const Symbol *s = &symbols[e->symbol];
    if (s->range != sort) return 0;
    for (int a = 0; a < 2; a++)
        if ((a < s->arity) != (e->arg[a] != NULL) || (a < s->arity && !elem_typed(e->arg[a], s->domain[a]))) return 0;
    return 1;
}

/* 28q. Come elem_typed(), per ogni confronto della condizione s: i due
 * membri di un'uguaglianza nello stesso insieme, un'appartenenza che vale
 * vero o falso. */
static int sentence_typed(const Sentence *s) {
    if (!s) return 1;
    if (s->kind == S_EQUAL) return elem_typed(s->left, elem_sort(s->left)) && elem_typed(s->right, elem_sort(s->left));
    if (s->kind == S_HOLDS) return elem_typed(s->left, TRUTH);
    return sentence_typed(s->a) && sentence_typed(s->b);
}

/* 28q. Controlla, leggendo l'albero, che s sia scritta come le identità D
 * dell'equipotenza e per le applicazioni di map[] (la forma è in testa a
 * equipotent_identities()): per ogni lato i "per ogni" sulle sue variabili,
 * poi un'uguaglianza per componente, ognuna con l'applicazione giusta
 * applicata alle altre e alle variabili nel loro ordine. Ritorna 1 se
 * regge. */
static int identities_written(const Sentence *s, const Sentence *e, const int *map) {
    if (s->kind != S_AND) return 0;
    for (int k = 0; k < 2; k++) {
        const Sentence *q = k ? s->b : s->a;
        int m = e->sides[k], n = e->sides[1 - k];
        const int *first = k ? map + e->sides[1] : map, *second = k ? map : map + e->sides[1];
        for (int i = 0; i < m; i++, q = q->a)
            if (q->kind != S_FORALL || q->slot != e->side_slot[k][i]) return 0;
        if (m == 2 && q->kind != S_AND) return 0;
        for (int i = 0; i < m; i++) {
            const Sentence *equal = m == 2 ? (i ? q->b : q->a) : q;
            if (equal->kind != S_EQUAL || !is_variable(equal->right, e->side_slot[k][i]) || equal->left->symbol != second[i]) return 0;
            for (int j = 0; j < 2; j++) {
                const Elem *inner = equal->left->arg[j];
                if ((j < n) != (inner != NULL)) return 0;
                if (j >= n) continue;
                if (inner->symbol != first[j]) return 0;
                for (int a = 0; a < 2; a++)
                    if ((a < m) != (inner->arg[a] != NULL) || (a < m && !is_variable(inner->arg[a], e->side_slot[k][a]))) return 0;
            }
        }
    }
    return 1;
}

/* 28q. Controlla la condizione nota di posto i, che viene dall'equipotenza
 * parent (K_BIJECTION): ha il suo segno, ed è D per le applicazioni di
 * k->part[], ognuna con gli insiemi giusti. Da un'equipotenza vera (28q-1)
 * le applicazioni sono nuove: nate dopo l'enunciato, tutte diverse, e mai
 * nominate prima. Da una falsa (28q-2) devono esserci già: dichiarate, o con
 * il loro nome o la loro definizione prima di questa condizione. Ritorna 1
 * se regge. */
static int bijection_derived(int i) {
    const Known *k = &now->known[i], *p = &now->known[k->parent];
    const Sentence *e = p->source;
    if (e->kind != S_EQUIPOTENT || k->negated != p->negated) return 0;
    if (k->parts != e->sides[0] + e->sides[1]) return 0;
    for (int j = 0; j < k->parts; j++) {
        int map = k->part[j], domain[2], range, arity = identity_map_sorts(e, j, domain, &range);
        if (map < 0 || map >= symbol_count) return 0;
        const Symbol *s = &symbols[map];
        if (s->arity != arity || s->range != range || s->family || symbol_bound[map] || symbol_structure(map) >= 0) return 0;
        for (int a = 0; a < arity; a++)
            if (s->domain[a] != domain[a]) return 0;
        for (int other = 0; other < j && !p->negated; other++)
            if (k->part[other] == map) return 0;
        if (!p->negated && (map < declared_symbols || mentioned_before(i, map))) return 0;
        if (p->negated && map >= declared_symbols && (name_known[map] < 0 || name_known[map] >= i)) return 0;
    }
    return identities_written(k->source, e, k->part) && sentence_typed(k->source);
}

/* 28q. Ritorna 1 se spec, sotto i "per ogni" sulle variabili di bound, è
 * una forma d1-d3 (testa di 28q) che definisce l'oggetto value dell'insieme
 * sort, senza nominare map in ciò che gli dà il valore. La variabile di d2 e
 * d3 è nuova: non è tra quelle di bound. */
static int spec_defines(const Sentence *spec, Elem *value, int sort, int map, SlotSet bound) {
    if (spec->kind == S_EQUAL) return elem_renamed(spec->left, value, NULL, NULL, 0) && !elem_mentions(spec->right, map);
    if (spec->kind != S_FORALL || slot_set_contains(bound, spec->slot) || (sort_data[sort].kind != SORT_PARTS && sort_data[sort].kind != SORT_MAPS) ||
        slot_data[spec->slot].sort != sort_data[sort].base)
        return 0;
    Elem *y = slot_elem(spec->slot);
    const Sentence *body = spec->a;
    bound = slot_set_with(bound, spec->slot);
    if (sort_data[sort].kind == SORT_MAPS) return spec_defines(body, elem_new(sort_data[sort].symbol, 0, value, y), sort_data[sort].target, map, bound);
    return body->kind == S_IFF && body->a->kind == S_HOLDS && elem_renamed(body->a->left, elem_new(sort_data[sort].symbol, 0, y, value), NULL, NULL, 0) &&
           !sentence_mentions(body->b, map);
}

/* 28q. Controlla la definizione di posto i (K_MAPDEF): chiusa, per
 * un'applicazione nuova k->part[0] mai nominata prima, con i "per ogni" sui
 * suoi argomenti, ognuno nel suo insieme, e poi una forma d1-d3. Ritorna 1
 * se regge. */
static int mapdef_derived(int i) {
    const Known *k = &now->known[i];
    const Sentence *s = k->source;
    if (k->parts != 1) return 0;
    int map = k->part[0];
    if (k->negated || map < declared_symbols || map >= symbol_count || !sentence_closed(s, SLOT_EMPTY) || !sentence_typed(s) || mentioned_before(i, map)) return 0;
    const Symbol *f = &symbols[map];
    if (f->range == TRUTH || f->family || symbol_bound[map] || f->arity < 1) return 0;
    Elem *arg[2];
    SlotSet bound = SLOT_EMPTY;
    for (int a = 0; a < f->arity; a++, s = s->a) {
        if (s->kind != S_FORALL || slot_data[s->slot].sort != f->domain[a] || slot_set_contains(bound, s->slot)) return 0;
        bound = slot_set_with(bound, s->slot);
        arg[a] = slot_elem(s->slot);
    }
    return spec_defines(s, map_apply(map, arg, f->arity), f->range, map, bound);
}

/* 28j. Controlla che la condizione nota k venga dal "per ogni parte" p con
 * le parti di k->part[] al posto delle parti legate in testa a p: ognuna una
 * parte del suo insieme con un nome, e k il corpo di p con loro al posto
 * delle legate, riletto da sentence_renamed(). Ritorna 1 se regge. */
static int part_instance_derived(const Known *k, const Known *p) {
    const Sentence *body = p->source;
    int count = 0, negated = p->negated, valid = 1;
    for (const Sentence *q = body; part_quantifier(q) && (q->kind == S_FORALL_PART) != p->negated; q = q->a) count++;
    if (!count || count != k->parts) return 0;
    int *from = NULL; size_t capacity = 0;
    if (!work_reserve((void **)&from, &capacity, (size_t)count, sizeof *from)) return 0;
    for (int j = 0; j < count; j++, body = body->a) {
        valid &= part_of(k->part[j], symbols[body->part].domain[0]);
        from[j] = body->part;
    }
    while (body->kind == S_NOT) { body = body->a; negated = !negated; }
    valid = valid && k->negated == negated && sentence_renamed(k->source, body, from, k->part, count);
    free(from);
    return valid;
}

/* 28j. Controlla che la condizione nota di posto i venga dall'"esiste una
 * parte" (o dal "non per ogni parte") p, con al posto della parte legata
 * una parte nuova, k->part[0], che nessuna condizione nota prima di questa
 * nomina. Ritorna 1 se regge. */
static int part_name_derived(int i, const Known *p) {
    const Known *k = &now->known[i];
    const Sentence *body = p->source->a;
    if (k->parts != 1) return 0;
    int from = p->source->part, to = k->part[0];
    int negated = p->negated;
    if ((p->source->kind == S_EXISTS_PART) == p->negated || to < declared_symbols || !part_of(to, symbols[from].domain[0])) return 0;
    for (int j = 0; j < i; j++)
        if (sentence_mentions(now->known[j].source, to)) return 0;
    while (body->kind == S_NOT) { body = body->a; negated = !negated; }
    return k->negated == negated && sentence_renamed(k->source, body, &from, &to, 1);
}

/* 28r. Ritorna 1 se l'elemento presente id è scritto bene: ogni argomento
 * sta nell'insieme che il suo simbolo chiede, fino in fondo. Il controllo di
 * un'istanza lo vuole per ogni elemento che sostituisce: chi ha costruito
 * l'elemento, compresi gli f(a) aggiunti dal modello candidato (28r-1), non
 * conta. */
static int ground_sorted(int id) {
    const Ground *g = &ground[id];
    const Symbol *s = &symbols[g->symbol];
    for (int i = 0; i < 2; i++) {
        if ((i < s->arity) != (g->arg[i] >= 0)) return 0;
        if (i < s->arity && (g->arg[i] < 1 || symbols[ground[g->arg[i]].symbol].range != s->domain[i] || !ground_sorted(g->arg[i]))) return 0;
    }
    return 1;
}

/* Controlla che la condizione nota di posto i, che non è un passo 28-1,
 * venga davvero da parent nel modo che origin dice: è un controllo sulla
 * forma, fatto rileggendo l'albero dell'enunciato. Ritorna 1 se regge. */
static int known_derived(int i) {
    const Known *k = &now->known[i], *p = &now->known[k->parent];
    const Sentence *body = p->source;
    Parts parts;
    switch (k->origin) {
    case K_INSTANCE:
        if (part_quantifier(body)) return part_instance_derived(k, p);

        /* Il corpo dei "per ogni" con cui parent comincia, con un elemento
         * del suo insieme al posto di ogni variabile. */
        while ((body->kind == S_FORALL || body->kind == S_EXISTS) && (body->kind == S_FORALL) != p->negated) {
            int id = slot_values_get(k->value, body->slot);
            if (id < 1 || symbols[ground[id].symbol].range != slot_data[body->slot].sort || !ground_sorted(id)) return 0;
            body = body->a;
        }
        return body != p->source && known_is(k, body, p->negated);
    case K_NAMED:
        /* parent è un "esiste", e il nome è nuovo: nessuna condizione nota
         * prima di questa lo usa. */
        if (part_quantifier(body)) return part_name_derived(i, p);
        if ((body->kind != S_FORALL && body->kind != S_EXISTS) || (body->kind == S_EXISTS) == p->negated) return 0;
        if (slot_values_get(k->value, body->slot) < 1 || ground[slot_values_get(k->value, body->slot)].arg[0] >= 0) return 0;
        for (int j = 0; j < i; j++)
            for (int v = 0; v < slot_count; v++)
                if (slot_values_get(now->known[j].value, v) == slot_values_get(k->value, body->slot)) return 0;
        return known_is(k, body->a, p->negated);
    case K_CASE:
        /* Uno dei due casi di una disgiunzione. Per un "se e solo se" il
         * caso è una scelta per il primo lato, e per il secondo il valore
         * che ne segue: lo stesso se l'equivalenza è vera, l'opposto se è
         * negata. Il primo lato è la condizione nota subito prima. */
        if (body->kind == S_IFF) {
            const Known *first = &now->known[i > 0 ? i - 1 : 0];
            if (known_is(k, body->a, 0) || known_is(k, body->a, 1)) return 1;
            return i > 0 && first->parent == k->parent && first->origin == K_CASE &&
                   (known_is(first, body->a, 0) || known_is(first, body->a, 1)) &&
                   known_is(k, body->b, known_is(first, body->a, 1) != p->negated);
        }
        return sentence_parts(body, p->negated, &parts) && !parts.conjunction &&
               (known_is(k, parts.x, parts.nx) || known_is(k, parts.y, parts.ny));
    case K_BIJECTION:
        return bijection_derived(i);
    default:
        return 1;
    }
}

/* 28j. Segna in needed[] le condizioni che hanno dato un nome (28-2) o una
 * definizione (K_DEFINED) ai simboli che l'elemento e nomina: chi legge la
 * dimostrazione deve averli visti nascere. */
static void need_names_elem(const Elem *e) {
    if (!e) return;
    if (e->symbol >= declared_symbols && name_known[e->symbol] >= 0) needed[name_known[e->symbol]] = 1;
    need_names_elem(e->arg[0]);
    need_names_elem(e->arg[1]);
}

/* 28j. Come need_names_elem(), per tutti gli elementi della condizione s. */
static void need_names(const Sentence *s) {
    if (!s) return;
    need_names_elem(s->left);
    need_names_elem(s->right);
    need_names(s->a);
    need_names(s->b);
}

/* 28j. Come need_names_elem(), per i nomi dentro l'elemento presente id: un
 * elemento con un nome usato in un'istanza va presentato anche se nessun
 * fatto su di lui serve, e con lui la catena da cui è nato. */
static void need_ground_names(int id) {
    const Ground *g = &ground[id];
    if (g->symbol >= declared_symbols && name_known[g->symbol] >= 0) needed[name_known[g->symbol]] = 1;
    for (int i = 0; i < 2 && g->arg[i] >= 0; i++) need_ground_names(g->arg[i]);
}

/* 28p. I CASI SCRITTI SONO TUTTI
 *
 * (Sta qui, accanto a leaf_write() che scrive i casi; la lettera è venuta
 * dopo le altre.)
 *
 * Ogni passo scritto si ricontrolla da solo (28e): una catena di
 * uguaglianze anello per anello, una deduzione con la sua tabella di verità,
 * un caso con la disgiunzione da cui viene. Ma "per ogni passo" non basta a
 * dire che la dimostrazione è completa: una distinzione di casi in cui un
 * caso non è scritto ha tutti i passi giusti e non dimostra nulla. Il
 * certificato non se ne accorge sempre, perché il verificatore ritrova da
 * sé i casi che non chiedono istanze (11e di checker.c): l'esperimento di
 * un motore bugiardo che non scriveva il caso già chiuso di 28o è passato
 * senza che nessun test lo vedesse. Per questo, a dimostrazione finita, si
 * controlla anche la forma dei casi.
 *
 * Di ogni ramo chiuso e scritto (una foglia) si annota il cammino: la
 * successione dei casi in cui sta, ognuno come la disgiunzione da cui viene
 * (il suo posto tra le cose note, uguale in tutti i rami che la ereditano) e
 * la parte scelta. Le foglie coprono tutto se, partendo dal cammino vuoto,
 * in ogni punto o c'è una foglia che si ferma lì (il ramo è chiuso senza
 * altri casi), oppure tutte le foglie che proseguono distinguono la stessa
 * disgiunzione, con le sue due parti, e da ognuna le foglie coprono tutto a
 * loro volta. È la regola della dimostrazione per casi: da "A oppure B", da
 * A una contraddizione e da B una contraddizione, segue la contraddizione;
 * la disgiunzione è tra le righe del caso (la sua riga "there are two
 * cases" la cita), ed è ricontrollata come le altre. Se la copertura manca
 * il programma ha sbagliato: unjustified_steps lo conta, e l'affermazione
 * non è dimostrata. */

/* Un passo del cammino di una foglia: la disgiunzione di posto parent tra
 * le cose note, e la parte scelta, come il primo caso che ne viene (source
 * con il segno negated; per un "se e solo se" il primo lato). */
typedef struct {
    short parent;
    const Sentence *source;
    signed char negated;
} CaseStep;

/* Il cammino di una foglia scritta: i suoi casi, dal più esterno. */
typedef struct {
    CaseStep step[MAX_CASE_STEPS];
    int steps;
} CasePath;

/* I cammini delle foglie scritte per l'affermazione in corso; 1 in
 * case_overflow se una non ci stava, e allora la copertura non si può dire. */
static CasePath case_path[MAX_CASE_LEAVES];
static int case_paths, case_overflow;

/* Annota il cammino del ramo corrente, appena chiuso e scritto. */
static void case_path_record(void) {
    if (case_paths == MAX_CASE_LEAVES) { case_overflow = 1; return; }
    CasePath *p = &case_path[case_paths++];
    p->steps = 0;
    for (int i = 0; i < now->knowns; i++) {
        const Known *k = &now->known[i];
        int first = k->origin == K_CASE;
        for (int j = 0; j < p->steps && first; j++) first = p->step[j].parent != k->parent;
        if (!first) continue;
        if (p->steps == MAX_CASE_STEPS) { case_overflow = 1; return; }
        p->step[p->steps++] = (CaseStep){k->parent, k->source, k->negated};
    }
}

/* Ritorna 1 se due passi scelgono la stessa parte della stessa
 * disgiunzione. */
static int case_step_same(const CaseStep *a, const CaseStep *b) {
    return a->parent == b->parent && a->source == b->source && a->negated == b->negated;
}

/* Ritorna 1 se le foglie di posto leaf[0..count), che hanno i primi depth
 * passi uguali, coprono tutti i casi da lì in giù (vedi la testa del
 * paragrafo). */
static int case_paths_cover(const CasePath *paths, const int *leaf, int count, int depth) {
    int side[MAX_CASE_LEAVES], sides = 0, other[MAX_CASE_LEAVES], others = 0;
    if (count == 0) return 0;
    for (int i = 0; i < count; i++)
        if (paths[leaf[i]].steps == depth) return 1;

    /* Tutte proseguono: la stessa disgiunzione, divisa nelle sue due parti. */
    const CaseStep *first = &paths[leaf[0]].step[depth];
    for (int i = 0; i < count; i++) {
        const CaseStep *s = &paths[leaf[i]].step[depth];
        if (s->parent != first->parent) return 0;
        if (case_step_same(s, first)) side[sides++] = leaf[i];
        else if (!others || case_step_same(s, &paths[other[0]].step[depth])) other[others++] = leaf[i];
        else return 0;
    }
    return others > 0 && case_paths_cover(paths, side, sides, depth + 1) && case_paths_cover(paths, other, others, depth + 1);
}

/* Ritorna 1 se le foglie scritte per l'affermazione in corso coprono tutti
 * i loro casi. */
static int case_paths_complete(void) {
    int leaf[MAX_CASE_LEAVES];
    for (int i = 0; i < case_paths; i++) leaf[i] = i;
    return !case_overflow && case_paths_cover(case_path, leaf, case_paths, 0);
}

/* Scrive la dimostrazione del ramo che si è appena chiuso: le sole
 * condizioni note che servono alla contraddizione, una per riga, e la
 * contraddizione. `leaf` è il numero del caso, 0 se non ci sono casi.
 * Ritorna 1 se ogni passo scritto ha superato il suo controllo; se ritorna
 * 0 il testo scritto va cancellato da chi chiama. Annota il cammino dei
 * casi della foglia (28p). */
static int leaf_write(int leaf) {
    static Deduction d;
    static Reason reason;
    memset(needed, 0, sizeof needed);

    /* Da dove nasce la contraddizione: un fatto "diversi" tra due elementi
     * uguali, o una disgiunzione senza parti vere. */
    if (clash_fact >= 0) {
        const Known *f = &now->known[clash_fact];
        if (!chain_between(&reason.chain[0], f->left, f->right, INT_MAX)) return 0;
        needed[clash_fact] = 1;
        for (int j = 0; j < reason.chain[0].links; j++) needed[reason.chain[0].fact[j]] = 1;
    } else {
        if (!deduction_read(clash_choice, NULL, 0, INT_MAX, &d)) return 0;
        needed[clash_choice] = 1;
        for (int j = 0; j < d.uses; j++) needed[d.used[j]] = 1;
    }

    /* All'indietro: ciò che serve a ciò che serve. Una condizione viene
     * sempre dopo quelle da cui dipende, quindi basta un passaggio. Ogni
     * passo viene ricontrollato qui, prima di scrivere qualcosa. */
    for (int i = now->knowns - 1; i >= 0; i--) {
        const Known *k = &now->known[i];
        if (!needed[i]) continue;

        /* 28j. Le parti scelte, e i nomi che la condizione nomina (in una
         * copia o in una definizione), vanno presentati prima di usarli. */
        need_names(k->source);
        for (int v = 0; v < slot_count; v++)
            if (slot_values_get(k->value, v) > 0) need_ground_names(slot_values_get(k->value, v));
        for (int j = 0; j < k->parts; j++)
            if (k->part[j] >= declared_symbols && name_known[k->part[j]] >= 0) needed[name_known[k->part[j]]] = 1;
        if ((k->origin == K_DEFINED && !definition_derived(i)) || (k->origin == K_MAPDEF && !mapdef_derived(i))) {
            if (!work_allocation_failed) unjustified_steps++;
            return 0;
        }
        if (k->parent < 0) continue;
        needed[k->parent] = 1;
        if (k->origin != K_PART) {
            if (!known_derived(i)) {
                /* Un controllo interrotto per memoria non e una deduzione
                 * falsa: il fallimento persistente scarta comunque la prova. */
                if (!work_allocation_failed) unjustified_steps++;
                return 0;
            }
            continue;
        }
        if (!deduction_read(k->parent, k->source, k->negated, k->stamp, &d)) return 0;
        for (int j = 0; j < d.uses; j++) needed[d.used[j]] = 1;
    }

    /* Le righe. */
    int number = 0;
    if (leaf) proof_add("\\item \\emph{Case %d.}\n\\begin{enumerate}\n", leaf);
    else proof_add("\\item \\emph{Suppose not.}\n\\begin{enumerate}\n");
    for (int i = 0; i < now->knowns; i++) {
        const Known *k = &now->known[i];
        if (!needed[i] || k->origin == K_GIVEN) continue;
        label[i] = (short)++number;
        proof_add("\\item ");
        if (k->origin == K_DENIED) {
            proof_add("Suppose that the claim fails");
        } else if (k->origin == K_INSTANCE) {
            proof_add("By ");
            put_label(k->parent);
            proof_add(" with");
            const Known *p = &now->known[k->parent];
            int written = 0;
            for (const Sentence *q = p->source; (q->kind == S_FORALL || q->kind == S_EXISTS) && (q->kind == S_FORALL) != p->negated; q = q->a) {
                proof_add("%s $", written++ ? "," : "");
                put_slot(q->slot);
                proof_add(" := ");
                put_ground(slot_values_get(k->value, q->slot), 0);
                proof_add("$");
            }

            /* 28j. Le parti scelte per le parti legate. */
            const Sentence *q = p->source;
            for (int j = 0; j < k->parts && part_quantifier(q); j++, q = q->a) {
                proof_add("%s $", written++ ? "," : "");
                put_symbol(q->part);
                proof_add(" := ");
                put_symbol(k->part[j]);
                proof_add("$");
            }
        } else if (k->origin == K_NAMED) {
            /* Un "esiste" vero dà l'elemento; un "per ogni" falso dà un
             * elemento per cui non vale. Lo stesso per una parte (28j). */
            const Sentence *q = now->known[k->parent].source;
            int some = q->kind == S_EXISTS || q->kind == S_EXISTS_PART, part = part_quantifier(q);
            proof_add("By ");
            put_label(k->parent);
            if (some) proof_add(" there is such %s of $", part ? "a part" : "an element");
            else proof_add(" some %s of $", part ? "part" : "element");
            put_sort(part ? symbols[q->part].domain[0] : slot_data[q->slot].sort);
            proof_add(some ? "$; call it $" : "$ makes it fail; call it $");
            if (part) put_symbol(k->part[0]); else put_ground(slot_values_get(k->value, q->slot), 0);
            proof_add("$. For it");
        } else if (k->origin == K_DEFINED) {
            /* 28j. La parte nuova, con la sua regola. */
            const Sentence *definition = k->source;
            SlotValues nothing = SLOT_VALUES_EMPTY;

            proof_add("Consider the part $");
            put_symbol(k->part[0]);
            proof_add(" = \\{");
            put_slot(definition->slot);
            proof_add(" \\in ");
            put_sort(slot_data[definition->slot].sort);
            proof_add(" \\mid ");
            put_sentence(definition->a->b, 0, nothing, 0);
            proof_add("\\}$ of $");
            put_sort(slot_data[definition->slot].sort);
            proof_add("$");
        } else if (k->origin == K_BIJECTION) {
            /* 28q-1: la biiezione con un nome; 28q-2: il testimone. */
            const Sentence *e = now->known[k->parent].source;
            int n = e->sides[1], m = e->sides[0];
            proof_add("By ");
            put_label(k->parent);
            proof_add(k->negated ? ", no map from $" : " there is a bijection from $");
            put_equipotent_side(e, 0);
            proof_add("$ to $");
            put_equipotent_side(e, 1);
            proof_add(k->negated ? "$ has an inverse; in particular not $" : "$; call it $");
            for (int j = 0; j < n; j++) { if (j) proof_add(", "); put_symbol(k->part[j]); }
            proof_add(k->negated ? "$, with $" : "$, and its inverse $");
            for (int j = 0; j < m; j++) { if (j) proof_add(", "); put_symbol(k->part[n + j]); }
            proof_add(k->negated ? "$ as inverse" : "$. For them");
        } else if (k->origin == K_MAPDEF) {
            /* 28q: un'applicazione nuova, con la sua definizione. */
            const Symbol *f = &symbols[k->part[0]];
            proof_add("Consider the map $");
            put_symbol(k->part[0]);
            proof_add(" \\colon ");
            for (int a = 0; a < f->arity; a++) { if (a) proof_add(" \\times "); put_sort(f->domain[a]); }
            proof_add(" \\to ");
            put_sort(f->range);
            proof_add("$ defined by");
        } else if (k->origin == K_CASE) {
            proof_add("By ");
            put_label(k->parent);
            proof_add(" there are two cases. In this one");
        } else {
            /* 28-1: la premessa, e ciò che di lei si sa già. */
            deduction_read(k->parent, k->source, k->negated, k->stamp, &d);
            proof_add("From ");
            put_label(k->parent);
            for (int a = 0, written = 0; a < d.atoms; a++) {
                if (d.value[a] < 0 || d.atom[a]->kind == S_TRUE) continue;
                literal_reason(d.atom[a], now->known[k->parent].value, k->stamp, &reason);
                proof_add(written++ ? " and " : ", since ");
                put_reason(d.atom[a], now->known[k->parent].value, &reason);
            }
        }
        proof_add(": $");
        put_sentence(k->source, k->negated, k->value, 0);
        proof_add("$.\n");
    }

    /* La contraddizione. */
    proof_add("\\item This is a contradiction: ");
    if (clash_fact >= 0) {
        const Known *f = &now->known[clash_fact];
        reason.value = 1;
        chain_between(&reason.chain[0], f->left, f->right, INT_MAX);
        put_reason(f->source, f->value, &reason);
        proof_add(", against ");
        put_label(clash_fact);
    } else {
        deduction_read(clash_choice, NULL, 0, INT_MAX, &d);
        put_label(clash_choice);
        proof_add(" cannot hold");
        for (int a = 0, written = 0; a < d.atoms; a++) {
            if (d.value[a] < 0 || d.atom[a]->kind == S_TRUE) continue;
            literal_reason(d.atom[a], now->known[clash_choice].value, INT_MAX, &reason);
            proof_add(written++ ? " and " : ", since ");
            put_reason(d.atom[a], now->known[clash_choice].value, &reason);
        }
    }
    proof_add(".\n\\end{enumerate}\n");
    if (!exhausted) case_path_record();
    return !exhausted;
}

/* 28f. IL CERTIFICATO
 *
 * Il controllo di 28e è del programma su se stesso: legge le tabelle della
 * ricerca. Il certificato porta la dimostrazione a checker.c, che non usa
 * nulla di questo file (capitolo 11 di checker.c). Per un modello trovato da
 * 28a porta gli insiemi, con i loro elementi, e la tabella di ogni simbolo:
 * il verificatore vi calcola l'enunciato da capo. Per una dimostrazione
 * porta, per ogni affermazione della tesi, un caso "case (not C)" con i soli
 * dati che la ricerca ha trovato: i nomi dati (28-2, voce witness) e le
 * istanze (28-3, voce instance) che servono alle contraddizioni dei rami. Il
 * resto, le parti (28-1), le uguaglianze (28-4) e i casi (28-5), il
 * verificatore lo ritrova da sé, provando tutti i valori delle condizioni
 * elementari, e così controlla anche che la dimostrazione valga quando un
 * insieme è vuoto.
 *
 * I nomi del certificato. Un nome dato da 28-2 si scrive con la lettera e il
 * suo numero d'ordine, x_3: due rami diversi possono dare due nomi diversi
 * allo stesso posto di symbols[], e nel certificato, dove i rami di
 * un'affermazione stanno insieme, devono restare distinti. I simboli
 * dichiarati si scrivono senza _ (R_{1} diventa R1), e le variabili legate
 * con la loro lettera, quindi non si confondono con i nomi. */

/* name_written[n] è 1 se la voce witness del nome di numero d'ordine n è
 * già nel certificato dell'affermazione in corso. */
static unsigned char name_written[MAX_NAMES_GIVEN + 1];

/* Scrive un'etichetta univoca dell'insieme. I nomi arbitrari conservano
 * lettera e pedice; quelli derivati hanno un prefisso con underscore e
 * l'indice del tipo, distinto dai nomi arbitrari. Concatenare gli alberi
 * non basta: mappe parti(P)->S e P->parti(S) darebbero entrambe MPPS.
 * Il significato resta nei dati parts/maps, mai nell'etichetta. */
static void cert_sort(int sort) {
    if (sort_data[sort].kind == SORT_PLAIN) {
        cert_add("%c", sort_data[sort].name);
        if (sort_data[sort].index) cert_add("%d", sort_data[sort].index);  /* 17w */
        return;
    }
    if (sort_data[sort].kind == SORT_NUMBERS) { cert_add("Num"); return; }
    cert_add("%c_%d",sort_data[sort].kind==SORT_PARTS?'P':'M',sort);
}

/* Scrive nel certificato il nome del simbolo di posto symbol. Un simbolo
 * di struttura (17v) si chiama in o ap seguito dal nome del suo insieme. */
static void cert_symbol(int symbol) {
    const Symbol *s = &symbols[symbol];
    if (symbol_structure(symbol) >= 0) {
        cert_add(sort_data[symbol_structure(symbol)].kind == SORT_PARTS ? "in" : "ap");
        cert_sort(symbol_structure(symbol));
        return;
    }
    /* 17v. Un numero scritto come elemento si chiama num seguito dal numero.
     * Si chiamava n1, come nel certificato si scrive la variabile n_{1}: con
     * \forall n_{1} in vista, "n1" nella condizione diventava la variabile,
     * e il certificato parlava di un altro enunciato. Nessun altro nome
     * comincia per "num": una lettera sola, o un comando (lettere greche,
     * operazioni, relazioni), poi un pedice.
     * Warning: se aggiungi un comando che si chiama num, cambia questo nome. */
    if (s->name >= NUMERAL_NAMES) { cert_add("num%d", s->name - NUMERAL_NAMES); return; }
    if (symbol >= declared_symbols && s->name >= GREEK_NAMES) { cert_add("%s_%d", greek_letters[s->name - GREEK_NAMES], name_serial[symbol]); return; }  /* 28q */
    if (symbol >= declared_symbols) { cert_add("%c_%d", s->name, name_serial[symbol]); return; }
    if (s->name >= RELATION_NAMES) cert_add("%s", relation_commands[s->name - RELATION_NAMES]);
    else if (s->name >= GREEK_NAMES) cert_add("%s", greek_letters[s->name - GREEK_NAMES]);
    else if (s->name >= OPERATION_NAMES) cert_add("%s", operation_symbols[s->name - OPERATION_NAMES]);
    else cert_add("%c", s->name);
    if (s->index <= LETTER_INDEX) cert_add("%c", LETTER_INDEX - s->index);
    else if (s->index) cert_add("%d", index_digits(s->index));
}

/* Scrive nel certificato l'elemento di posto id: (f a), o il nome. */
static void cert_ground(int id) {
    const Ground *g = &ground[id];
    if (g->symbol < 0) { certificate_broken = 1; return; }
    if (g->arg[0] >= 0) cert_add("(");
    cert_symbol(g->symbol);
    for (int i = 0; i < 2 && g->arg[i] >= 0; i++) { cert_add(" "); cert_ground(g->arg[i]); }
    if (g->arg[0] >= 0) cert_add(")");
}

/* Scrive nel certificato il nome della variabile di posto slot: la
 * lettera, seguita dal pedice se c'è (x_{1} diventa x1). Non si confonde con
 * un simbolo: il lettore (17o, 17p) non lega mai una lettera che è il nome di
 * un simbolo in vista, e i nomi dati da 28-2 hanno il trattino basso. */
static void cert_slot(int slot) {
    cert_add("%c", slot_data[slot].letter);
    if (slot_data[slot].index) cert_add("%d", index_digits(slot_data[slot].index));
}

/* Scrive nel certificato l'elemento e, con gli elementi di value[] al posto
 * delle variabili sostituite. Una parte o una relazione applicata, (X a),
 * è nella notazione del verificatore anche la condizione che valga. */
static void cert_elem(const Elem *e, SlotValues value) {
    if (e->symbol < 0) {
        if (slot_values_get(value, e->slot) >= 0) cert_ground(slot_values_get(value, e->slot)); else cert_slot(e->slot);
        return;
    }
    if (e->arg[0]) cert_add("(");
    cert_symbol(e->symbol);
    for (int i = 0; i < 2 && e->arg[i]; i++) { cert_add(" "); cert_elem(e->arg[i], value); }
    if (e->arg[0]) cert_add(")");
}

/* Scrive nel certificato la condizione s, con gli elementi di value[] al
 * posto delle variabili sostituite. Una dichiarazione è "true": i simboli
 * dichiarati sono nelle voci symbol. */
static void cert_sentence(const Sentence *s, SlotValues value) {
    static const char *const word[] = {[S_NOT] = "not", [S_AND] = "and", [S_OR] = "or", [S_IMPLIES] = "implies", [S_IFF] = "iff"};
    switch (s->kind) {
    case S_TRUE:
        cert_add("true");
        return;
    case S_EQUIPOTENT:
        /* 17w. (equipotent A B), con un lato prodotto tra parentesi: (S T). */
        cert_add("(equipotent");
        for (int k = 0; k < 2; k++) {
            cert_add(s->sides[k] == 2 ? " (" : " ");
            for (int i = 0; i < s->sides[k]; i++) { if (i) cert_add(" "); cert_sort(slot_data[s->side_slot[k][i]].sort); }
            if (s->sides[k] == 2) cert_add(")");
        }
        cert_add(")");
        return;
    case S_EQUAL:
        cert_add("(= ");
        cert_elem(s->left, value);
        cert_add(" ");
        cert_elem(s->right, value);
        cert_add(")");
        return;
    case S_HOLDS:
        cert_elem(s->left, value);
        return;
    case S_FORALL: case S_EXISTS:
        cert_add("(%s ", s->kind == S_FORALL ? "forall" : "exists");
        cert_slot(s->slot);
        cert_add(" ");
        cert_sort(slot_data[s->slot].sort);
        cert_add(" ");
        cert_sentence(s->a, value);
        cert_add(")");
        return;
    case S_FORALL_PART: case S_EXISTS_PART:
        /* 28j. La parte legata si scrive con il suo nome, come una variabile
         * (11g di checker.c). */
        cert_add("(%s ", s->kind == S_FORALL_PART ? "forallpart" : "existspart");
        cert_symbol(s->part);
        cert_add(" ");
        cert_sort(symbols[s->part].domain[0]);
        cert_add(" ");
        cert_sentence(s->a, value);
        cert_add(")");
        return;
    case S_MEMBER: case S_INCLUDED: case S_SAME: case S_UNIQUE: case S_COUNT:
        /* Non arrivano qui (17q); se arrivassero, il certificato non le sa
         * dire. */
        certificate_broken = 1;
        return;
    default:
        cert_add("(%s ", word[s->kind]);
        cert_sentence(s->a, value);
        if (s->b) { cert_add(" "); cert_sentence(s->b, value); }
        cert_add(")");
        return;
    }
}

/* Scrive l'inizio del certificato dell'enunciato root: il tipo, gli
 * insiemi (con il numero di elementi del modello m, se c'è), i simboli
 * dichiarati, l'enunciato. */
static void cert_abstract_head(const char *kind, const Sentence *root, const Model *m) {
    SlotValues nothing = SLOT_VALUES_EMPTY;

    certificate_length = 0;
    certificate_broken = 0;
    cert_add("certificate %s\n", kind);
    for (int i = 0; i < sort_count; i++) {
        /* 17v. Un insieme di parti o di applicazioni dice di che cosa è
         * fatto, e il nome del suo simbolo di struttura: la grandezza e la
         * tabella il verificatore le calcola da sé. */
        cert_add("sort ");
        cert_sort(i);
        if (sort_data[i].kind == SORT_NUMBERS) {
            /* 17v. I numeri scritti, nel loro ordine (numeral_position()). */
            cert_add(" numbers");
            for (int s = 0; s < declared_symbols; s++)
                if (symbols[s].name >= NUMERAL_NAMES && symbols[s].range == i) { cert_add(" "); cert_symbol(s); }
        } else if (sort_data[i].kind != SORT_PLAIN) {
            cert_add(sort_data[i].kind == SORT_PARTS ? " parts " : " maps ");
            cert_sort(sort_data[i].base);
            if (sort_data[i].kind == SORT_MAPS) { cert_add(" "); cert_sort(sort_data[i].target); }
            cert_add(" ");
            cert_symbol(sort_data[i].symbol);
        } else if (m) {
            cert_add(" %zu", m->dimension[i].size);
        }
        cert_add("\n");
    }
    /* Warning: se cambia l'ordine delle dichiarazioni implicite o esplicite,
     * aggiorna anche la numerazione della clausificazione in sp_prepare(). */
    for (int s = 0; s < declared_symbols; s++) {
        if (symbol_fixed(s) || symbol_bound[s]) continue;  /* fissato da 17v, o una parte legata (17u): non è dichiarato */
        cert_add("symbol ");
        cert_symbol(s);
        for (int i = 0; i < symbols[s].arity; i++) { cert_add(" "); cert_sort(symbols[s].domain[i]); }
        if (symbols[s].range == TRUTH) cert_add(" bool");
        else { cert_add(" "); cert_sort(symbols[s].range); }
        cert_add("\n");
    }
    cert_add("statement ");
    cert_sentence(root, nothing);
    cert_add("\n");
}

static void cert_witness(int symbol);

/* Scrive, se non ci sono già, le voci witness dei nomi che compaiono
 * nell'elemento di posto id. */
static void cert_names_in(int id) {
    const Ground *g = &ground[id];
    if (g->symbol >= declared_symbols) cert_witness(g->symbol);
    for (int i = 0; i < 2 && g->arg[i] >= 0; i++) cert_names_in(g->arg[i]);
}

/* 28j. Come cert_names_in(), per i nomi che compaiono nell'elemento e: i
 * suoi simboli (una copia o una definizione ne hanno di dati dalla
 * dimostrazione) e gli elementi di value[] al posto delle sue variabili. */
static void cert_names_in_elem(const Elem *e, SlotValues value) {
    if (!e) return;
    if (e->symbol < 0) {
        if (slot_values_get(value, e->slot) >= 0) cert_names_in(slot_values_get(value, e->slot));
        return;
    }
    if (e->symbol >= declared_symbols) cert_witness(e->symbol);
    cert_names_in_elem(e->arg[0], value);
    cert_names_in_elem(e->arg[1], value);
}

/* 28j. Come cert_names_in_elem(), per tutti gli elementi della condizione s. */
static void cert_names_in_sentence(const Sentence *s, SlotValues value) {
    if (!s) return;
    cert_names_in_elem(s->left, value);
    cert_names_in_elem(s->right, value);
    cert_names_in_sentence(s->a, value);
    cert_names_in_sentence(s->b, value);
}

/* Scrive la voce del nome di posto symbol, se non c'è già, preceduta dalle
 * voci dei nomi che usa. Per un nome dato da 28-2 è la voce witness: la
 * condizione "esiste" (o "per ogni", negata) da cui è nato. Per una parte
 * definita (28j) è la voce part: "part D x S c", la parte degli x di S per
 * cui vale c. */
static void cert_witness(int symbol) {
    int serial = name_serial[symbol];
    if (serial > MAX_NAMES_GIVEN || name_known[symbol] < 0) { certificate_broken = 1; return; }
    if (name_written[serial]) return;
    name_written[serial] = 1;
    const Known *named = &now->known[name_known[symbol]];
    if (named->origin == K_MAPDEF) {
        /* 28q. "define NOME A1 [A2] B C": l'applicazione con i suoi insiemi e
         * la sua definizione, dopo le voci dei nomi che usa. */
        const Symbol *f = &symbols[symbol];
        cert_names_in_sentence(named->source, named->value);
        cert_add("define ");
        cert_symbol(symbol);
        for (int a = 0; a < f->arity; a++) { cert_add(" "); cert_sort(f->domain[a]); }
        cert_add(" ");
        cert_sort(f->range);
        cert_add(" ");
        cert_sentence(named->source, named->value);
        cert_add("\n");
        return;
    }
    if (named->origin == K_BIJECTION) {
        /* 28q-1. "witness (equipotent A B) phi... psi...": i nomi di tutte le
         * applicazioni della biiezione, in una voce. */
        const Sentence *e = now->known[named->parent].source;
        cert_add("witness ");
        cert_sentence(e, named->value);
        for (int j = 0; j < e->sides[0] + e->sides[1]; j++) {
            if (name_serial[named->part[j]] <= MAX_NAMES_GIVEN) name_written[name_serial[named->part[j]]] = 1;
            cert_add(" ");
            cert_symbol(named->part[j]);
        }
        cert_add("\n");
        return;
    }
    if (named->origin == K_DEFINED) {
        const Sentence *definition = named->source;
        cert_names_in_sentence(definition->a->b, named->value);
        cert_add("part ");
        cert_symbol(symbol);
        cert_add(" ");
        cert_slot(definition->slot);
        cert_add(" ");
        cert_sort(slot_data[definition->slot].sort);
        cert_add(" ");
        cert_sentence(definition->a->b, named->value);
        cert_add("\n");
        return;
    }
    const Known *p = &now->known[named->parent];
    for (int v = 0; v < slot_count; v++)
        if (slot_values_get(p->value, v) >= 0) cert_names_in(slot_values_get(p->value, v));
    cert_names_in_sentence(p->source, p->value);
    cert_add("witness ");
    cert_sentence(p->source, p->value);
    cert_add(" ");
    cert_symbol(symbol);
    cert_add("\n");
}

/* Scrive nel certificato le voci del ramo appena chiuso: i nomi e le
 * istanze tra le condizioni che servono alla sua contraddizione (needed[],
 * riempito da leaf_write()), nell'ordine in cui sono nate. Un'istanza
 * nomina la condizione da cui viene e un elemento per ognuno dei
 * quantificatori che ha tolto. */
static void cert_leaf(void) {
    for (int i = 0; i < now->knowns; i++) {
        const Known *k = &now->known[i];
        if (!needed[i] || (k->origin != K_INSTANCE && k->origin != K_NAMED && k->origin != K_DEFINED && k->origin != K_MAPDEF && k->origin != K_BIJECTION))
            continue;
        if (k->origin == K_DEFINED || k->origin == K_MAPDEF || (k->origin == K_BIJECTION && !k->negated)) { cert_witness(k->part[0]); continue; }
        if (k->origin == K_BIJECTION) {
            /* 28q-2. "instance (equipotent A B) gamma... delta...", dopo le
             * definizioni delle applicazioni. */
            const Sentence *e = now->known[k->parent].source;
            int count = e->sides[0] + e->sides[1];
            for (int j = 0; j < count; j++)
                if (k->part[j] >= declared_symbols) cert_witness(k->part[j]);
            cert_add("instance ");
            cert_sentence(e, k->value);
            for (int j = 0; j < count; j++) { cert_add(" "); cert_symbol(k->part[j]); }
            cert_add("\n");
            continue;
        }
        const Known *p = &now->known[k->parent];
        if (k->origin == K_NAMED) {
            cert_witness(part_quantifier(p->source) ? k->part[0] : ground[slot_values_get(k->value, p->source->slot)].symbol);
            continue;
        }
        for (int v = 0; v < slot_count; v++)
            if (slot_values_get(k->value, v) >= 0) cert_names_in(slot_values_get(k->value, v));
        cert_names_in_sentence(p->source, p->value);
        for (int j = 0; j < k->parts; j++)
            if (k->part[j] >= declared_symbols) cert_witness(k->part[j]);
        cert_add("instance ");
        cert_sentence(p->source, p->value);
        for (const Sentence *q = p->source; (q->kind == S_FORALL || q->kind == S_EXISTS) && slot_values_get(k->value, q->slot) >= 0; q = q->a) {
            cert_add(" ");
            cert_ground(slot_values_get(k->value, q->slot));
        }

        /* 28j. Per un "per ogni parte", i nomi delle parti scelte. */
        const Sentence *q = p->source;
        for (int j = 0; j < k->parts && part_quantifier(q); j++, q = q->a) {
            cert_add(" ");
            cert_symbol(k->part[j]);
        }
        cert_add("\n");
    }
}

/* Dà al verificatore il certificato appena scritto, e ne riporta la
 * risposta in verdict. Accettato: il verdetto porta il certificato.
 * Respinto: è un errore del programma, unjustified_steps lo conta.
 * Respinto, non controllabile o incompleto: il verdetto diventa sempre
 * NON DIMOSTRATO. Questo linguaggio copre l'enunciato: esaurire le risorse
 * del verificatore non equivale ad averne ottenuto l'accettazione. */
static Verdict abstract_certified(Verdict verdict) {
    const char *text = certificate_text, *why = "è più lungo di quanto il programma sappia scrivere";
    CkAnswer answer = certificate_broken ? CK_UNSUPPORTED : ck_check(&text, &why, checker_steps());
    if (answer == CK_ACCEPTED) {
        verdict.certificate = certificate_text;
        return verdict;
    }
    snprintf(certificate_problem, sizeof certificate_problem, "il verificatore indipendente %s il certificato: %s",
             answer == CK_REJECTED ? "ha respinto" : "non sa controllare", why);
    verdict.reason = certificate_problem;
    if (answer == CK_REJECTED) unjustified_steps++;
    verdict.outcome = NOT_PROVED;
    verdict.proof = verdict.detail = verdict.certificate = NULL;
    return verdict;
}

/* 28n. LE LEGGI DELLE PARTI E DELLE APPLICAZIONI
 *
 * Un enunciato che prende \mathcal{P}(S) o T^{S} come insieme di oggetti
 * (17v) usa ciò che una parte e un'applicazione sono, e che le ipotesi non
 * dicono: due parti con gli stessi elementi sono la stessa parte, e ogni
 * condizione dà la parte degli elementi che la soddisfano. Le dimostrazioni
 * dei libri lo usano senza dirlo ("sia Y = S \setminus \{x\}"); qui sono
 * delle condizioni in più, gli assiomi, scritte come ogni altra e aggiunte
 * alle ipotesi. Sono vere per le parti e le applicazioni vere, e sono le
 * uniche cose che le distinguono da un insieme qualsiasi:
 *
 *   28n-1. Estensionalità delle parti. \forall X, Y \in \mathcal{P}(S)\
 *          ((\forall t \in S\ (t \in X \iff t \in Y)) \implies X = Y): una
 *          parte è l'insieme dei suoi elementi, e niente altro.
 *   28n-2. Estensionalità delle applicazioni. \forall f, g \in T^{S}\
 *          ((\forall x \in S\ (f(x) = g(x))) \implies f = g): un'applicazione
 *          è la tabella dei suoi valori.
 *   28n-3. Comprensione. Per una condizione P(t), con t in S e dei
 *          parametri: per ogni scelta dei parametri esiste Z \in
 *          \mathcal{P}(S) con \forall t \in S\ (t \in Z \iff P(t)). È la
 *          parte \{t \in S \mid P(t)\}, che esiste per qualunque P: è un
 *          sottoinsieme di S, e \mathcal{P}(S) li contiene tutti.
 *
 * Quali comprensioni. Le condizioni P sono infinite, e la ricerca ne prova
 * poche: la parte vuota (P falsa), tutto S (P vera) e le parti di un solo
 * elemento, \{a\} (P è t = a, con a parametro). Sono le parti di cui
 * parlano le dimostrazioni a mano di questi enunciati: "S stesso non è
 * un'immagine", "\{a\} e S contengono tutti e due a". Non è una ricerca
 * completa, e non deve esserlo: come per le istanze (28-3), non trovare una
 * dimostrazione vuol dire NON DIMOSTRATO. Per le applicazioni c'è una legge
 * in più, che dà quelle con due valori (28s).
 *
 * Il verificatore non si fida: riceve gli assiomi nel certificato, una voce
 * axiom per ognuno, e controlla da sé che ognuno abbia la forma di 28n-1,
 * 28n-2, 28n-3 o 28s-1, su un insieme di parti o di applicazioni dichiarato
 * (11h e 11k in checker.c). Un assioma di forma diversa è respinto: non si può far
 * passare un'ipotesi in più per una legge. I modelli finiti (28a, 28m)
 * hanno le parti e le applicazioni vere, dove gli assiomi valgono: un
 * controesempio trovato lì è un controesempio vero. */

/* Gli assiomi dell'enunciato in corso, aggiunti alle sue ipotesi, e la
 * legge di cui ognuno è un caso. */
static const Sentence *axioms[MAX_AXIOMS];
static Law axiom_law[MAX_AXIOMS];
static int axiom_count;

/* Ritorna la legge da cui viene la condizione nota di posto i: quella
 * dell'assioma, se è un assioma o una sua istanza; LAW_NONE altrimenti. */
static int known_law(int i) {
    const Known *k = &now->known[i];
    if (k->origin == K_INSTANCE || k->origin == K_PART) return known_law(k->parent);
    if (k->origin != K_GIVEN) return LAW_NONE;
    for (int a = 0; a < axiom_count; a++)
        if (axioms[a] == k->source) return axiom_law[a];
    return LAW_NONE;
}

/* Ritorna una variabile nuova dell'insieme sort, come elemento, e mette il
 * suo posto in *slot. */
static Elem *axiom_variable(int sort, int *slot) {
    *slot = unfold_slot(sort);
    return elem_new(-1, *slot, NULL, NULL);
}

/* Aggiunge l'assioma a, caso della legge law, se c'è posto; altrimenti lo
 * lascia fuori, e la ricerca ha una legge in meno. */
static void axiom_add(const Sentence *a, Law law) {
    if (axiom_count == MAX_AXIOMS || syntax_error) return;
    axiom_law[axiom_count] = law;
    axioms[axiom_count++] = a;
}

/* 28n-1 e 28n-2. L'estensionalità dell'insieme di posto sort, di parti o
 * di applicazioni. */
static void axiom_extensionality(int sort) {
    int x, y, t, symbol = sort_data[sort].symbol;
    Elem *a = axiom_variable(sort, &x), *b = axiom_variable(sort, &y), *point = axiom_variable(sort_data[sort].base, &t);
    Sentence *same = sort_data[sort].kind == SORT_PARTS
                         ? axiom_join(S_IFF, axiom_atom(S_HOLDS, symbol, point, a), axiom_atom(S_HOLDS, symbol, point, b))
                         : axiom_atom(S_EQUAL, -1, elem_new(symbol, 0, a, point), elem_new(symbol, 0, b, point));
    Sentence *law = axiom_join(S_IMPLIES, axiom_bind(S_FORALL, t, same), axiom_atom(S_EQUAL, -1, a, b));
    axiom_add(axiom_bind(S_FORALL, x, axiom_bind(S_FORALL, y, law)), LAW_EXTENSIONALITY);
}

/* 28n-3. La comprensione della parte \{t \in S \mid P(t)\} di
 * \mathcal{P}(S), insieme di posto sort: kind 0 per la parte vuota (P
 * falsa), 1 per tutto S (P vera), 2 per \{a\} (P è t = a, con a
 * parametro). */
static void axiom_part(int sort, int kind) {
    int z, t, a = -1, symbol = sort_data[sort].symbol;
    Elem *part = axiom_variable(sort, &z), *point = axiom_variable(sort_data[sort].base, &t);
    Sentence *condition = axiom_join(S_TRUE, NULL, NULL);
    if (kind == 0) condition = axiom_join(S_NOT, condition, NULL);
    if (kind == 2) condition = axiom_atom(S_EQUAL, -1, point, axiom_variable(sort_data[sort].base, &a));
    Sentence *law = axiom_bind(S_EXISTS, z, axiom_bind(S_FORALL, t, axiom_join(S_IFF, axiom_atom(S_HOLDS, symbol, point, part), condition)));
    axiom_add(kind == 2 ? axiom_bind(S_FORALL, a, law) : law, LAW_COMPREHENSION);
}

static void sentence_free(const Sentence *s, SlotSet bound, SlotSet *free);

/* Aggiunge a *free, come bit, le variabili dell'elemento e che non sono in
 * bound, cioè non legate dentro l'insieme di cui e fa parte. */
static void elem_free(const Elem *e, SlotSet bound, SlotSet *free) {
    if (!e) return;
    if (e->symbol < 0) { if (!slot_set_contains(bound, e->slot)) *free = slot_set_with(*free, e->slot); return; }
    elem_free(e->arg[0], bound, free);
    elem_free(e->arg[1], bound, free);
}

/* Come elem_free(), per un insieme scritto come nei libri: le lettere di
 * una regola, l'indice di un'unione e la parte di una descrizione sono
 * legate dentro di lui. */
static void set_term_free(const SetTerm *t, SlotSet bound, SlotSet *free) {
    if (!t) return;
    for (int i = 0; i < t->bounds; i++) bound = slot_set_with(bound, t->bound[i]);
    for (int i = 0; i < t->items; i++) elem_free(t->item[i], bound, free);
    set_term_free(t->a, bound, free);
    set_term_free(t->b, bound, free);
    if (t->condition) sentence_free(t->condition, bound, free);
}

/* Come elem_free(), per una condizione. */
static void sentence_free(const Sentence *s, SlotSet bound, SlotSet *free) {
    if (!s) return;
    if (s->kind == S_FORALL || s->kind == S_EXISTS || s->kind == S_UNIQUE) bound = slot_set_with(bound, s->slot);
    elem_free(s->left, bound, free);
    elem_free(s->right, bound, free);
    for (int i = 0; i < s->items; i++) elem_free(s->item[i], bound, free);
    set_term_free(s->set, bound, free);
    set_term_free(s->other, bound, free);
    sentence_free(s->a, bound, free);
    sentence_free(s->b, bound, free);
}

/* 28n-3. La comprensione dell'insieme e, che l'enunciato scrive come una
 * parte (part_template[] in 17v): per ogni valore delle sue lettere libere,
 * esiste la parte Z con \forall t\ (t \in Z \iff t \in e). La condizione
 * t \in e è svolta come in 17q, con lettere nuove al posto di quelle
 * libere, così l'assioma non condivide variabili con l'enunciato. */
static void axiom_template(const SetTerm *e) {
    int sort = sort_derived_find(SORT_PARTS, e->sort[0], -1), z, t, count = 0, original_slots = slot_count;
    SlotSet free = SLOT_EMPTY;
    if (sort < 0) return;
    set_term_free(e, SLOT_EMPTY, &free);
    int *slot = work_arena_array((size_t)original_slots, sizeof *slot);
    if (work_allocation_failed) return;
    for (int v = 0; v < original_slots; v++)
        if (slot_set_contains(free, v)) {
            /* Creare la variabile puo riallocare unfold_to; prima il valore,
             * poi si cerca la cella di destinazione. */
            Elem *replacement = axiom_variable(slot_data[v].sort, &slot[count]);
            unfold_to[v] = replacement;
            count++;
        }
    Elem *part = axiom_variable(sort, &z), *point = axiom_variable(e->sort[0], &t);
    Sentence *from = axiom_join(S_TRUE, NULL, NULL);
    unfold_copying++;
    Sentence *condition = unfold_member(&point, e, from);
    unfold_copying--;
    if (unfold_capacity) memset(unfold_to, 0, unfold_capacity * sizeof *unfold_to);
    Sentence *law = axiom_bind(S_EXISTS, z, axiom_bind(S_FORALL, t, axiom_join(S_IFF, axiom_atom(S_HOLDS, sort_data[sort].symbol, point, part), condition)));
    while (count > 0) law = axiom_bind(S_FORALL, slot[--count], law);
    axiom_add(law, LAW_COMPREHENSION);
}

/* 28s. LE APPLICAZIONI CON DUE VALORI
 *
 * (Sta qui, accanto alle leggi di 28n di cui è una in più; la lettera è
 * venuta dopo le altre.)
 *
 * Le comprensioni di 28n danno delle parti: la vuota, tutto S, \{a\}. Per le
 * applicazioni come oggetti, T^{S}, non ce n'era nessuna, e una
 * dimostrazione che chiede di costruire un'applicazione non si trovava:
 * "se l'ordine punto per punto su S^{S} è totale, S ha un solo elemento" si
 * dimostra a mano prendendo, per a \neq b, le applicazioni che mandano a in
 * a e il resto in b, e a in b e il resto in a, e guardando che non sono
 * confrontabili. La legge che le dà è
 *
 *   28s-1. Per ogni p di S e ogni u, v di T esiste h in T^{S} con h(x) = u
 *          se x = p e h(x) = v altrimenti.
 *
 * È vera: la regola dà a ogni x di S un valore solo, in T, quindi
 * un'applicazione da S a T, e T^{S} le contiene tutte; se S è vuoto non c'è
 * nessun p, se T lo è nessun u, e la legge non dice nulla. Con u = v dà le
 * applicazioni costanti. Perché questa e non altre: sono le applicazioni che
 * si scrivono con i soli elementi che hanno un nome, come \{a\} per le parti,
 * ed è un passo solo; le applicazioni date da una formula qualsiasi sarebbero
 * infinite, come le parti, e la legge diventerebbe una ricerca. Entra tra le
 * comprensioni (LAW_COMPREHENSION), che le prove usano solo quando le altre
 * non bastano (claim_attempts()), e il verificatore la riconosce dalla sua
 * forma, lettera per lettera (11k in checker.c). */

/* 28s-1. Aggiunge agli assiomi la legge delle applicazioni con due valori
 * dell'insieme di posto sort, di applicazioni da S a T, nella forma che il
 * verificatore riconosce: \forall p \in S\ \forall u, v \in T\ \exists h \in
 * T^{S}\ \forall x \in S\ ((x = p \implies h(x) = u) \land (x \neq p
 * \implies h(x) = v)). */
static void axiom_map_point(int sort) {
    int p, u, v, h, x, symbol = sort_data[sort].symbol;
    Elem *point = axiom_variable(sort_data[sort].base, &p), *first = axiom_variable(sort_data[sort].target, &u), *other = axiom_variable(sort_data[sort].target, &v);
    Elem *map = axiom_variable(sort, &h), *at = axiom_variable(sort_data[sort].base, &x);
    Sentence *here = axiom_atom(S_EQUAL, -1, at, point);
    Sentence *body = axiom_join(S_AND, axiom_join(S_IMPLIES, here, axiom_atom(S_EQUAL, -1, elem_new(symbol, 0, map, at), first)),
                                axiom_join(S_IMPLIES, axiom_join(S_NOT, here, NULL), axiom_atom(S_EQUAL, -1, elem_new(symbol, 0, map, at), other)));
    Sentence *law = axiom_bind(S_EXISTS, h, axiom_bind(S_FORALL, x, body));
    axiom_add(axiom_bind(S_FORALL, p, axiom_bind(S_FORALL, u, axiom_bind(S_FORALL, v, law))), LAW_COMPREHENSION);
}

/* Prepara gli assiomi dell'enunciato in corso: per ogni insieme di parti
 * l'estensionalità e le comprensioni descritte in testa al paragrafo, per
 * ogni insieme di applicazioni l'estensionalità e la legge di 28s; poi le
 * comprensioni degli insiemi che l'enunciato scrive come parti, tranne
 * quelli che le prime già danno (\emptyset, tutto S). Usa posti nuovi per
 * le variabili, dopo quelli dello svolgimento. */
static void axioms_prepare(void) {
    axiom_count = 0;
    for (int i = 0; i < sort_count; i++)
        /* I numeri elencati non sono insiemi di oggetti con un simbolo
         * di struttura: non hanno un'appartenenza o un'applicazione da
         * rendere estensionale. Trattarli come mappe userebbe sort_symbol=-1. */
        if (sort_data[i].kind == SORT_PARTS || sort_data[i].kind == SORT_MAPS) axiom_extensionality(i);
    for (int i = 0; i < sort_count; i++)
        for (int kind = 0; kind < 3 && sort_data[i].kind == SORT_PARTS; kind++) axiom_part(i, kind);
    for (int i = 0; i < sort_count; i++)
        if (sort_data[i].kind == SORT_MAPS) axiom_map_point(i);
    for (int i = 0; i < part_template_count; i++)
        if (part_template[i]->kind != ST_EMPTY && part_template[i]->kind != ST_SORT) axiom_template(part_template[i]);
}

/* Quanti dei primi assiomi sono estensionalità: axioms_prepare() le mette
 * prima delle comprensioni. */
static int axioms_extensional(void) {
    int count = 0;
    while (count < axiom_count && axiom_law[count] == LAW_EXTENSIONALITY) count++;
    return count;
}

/* Scrive nel certificato una voce axiom per ogni assioma (28f, 11h in
 * checker.c). */
static void cert_axioms(void) {
    SlotValues nothing = SLOT_VALUES_EMPTY;

    for (int i = 0; i < axiom_count; i++) {
        cert_add("axiom ");
        cert_sentence(axioms[i], nothing);
        cert_add("\n");
    }
}

/* 28g. I RAMI, LE AFFERMAZIONI, IL VERDETTO */

/* Quanti rami sono stati chiusi finora nella dimostrazione in corso: serve
 * a numerare i casi. */
static int leaves_closed;

/* Quanti giri di istanze (28-3) un ramo fa prima di distinguere dei casi
 * (28-5): MAX_ROUNDS, o di meno nelle prove di 28n. */
static int rounds_before_split = MAX_ROUNDS;

/* Copia nel ramo di profondità depth + 1 quello di profondità depth, con
 * i suoi elementi e i suoi nomi, e ci si sposta. Delle tabelle si copia
 * solo la parte in uso: il resto non vale nulla. */
static void branch_copy(int depth) {
    const Branch *from = &branch[depth];
    Branch *to = &branch[depth + 1];
    branch[depth].symbols = symbol_count;
    memcpy(to->known, from->known, sizeof *from->known * (size_t)from->knowns);
    memcpy(to->rep, from->rep, sizeof *from->rep * (size_t)from->grounds);
    memcpy(to->up, from->up, sizeof *from->up * (size_t)from->grounds);
    memcpy(to->why, from->why, sizeof *from->why * (size_t)from->grounds);
    memcpy(to->different, from->different, sizeof *from->different * (size_t)from->differents);
    to->knowns = from->knowns;
    to->differents = from->differents;
    to->grounds = from->grounds;
    to->symbols = from->symbols;
    to->clock = from->clock;
    now = to;
    ground_reindex();
}

/* 28k. QUALI PARTI PROVARE
 *
 * Le parti di S sono infinite quando S lo è, e anche quando è finito sono
 * troppe per provarle tutte: come per gli elementi (28-3, "Quali istanze"),
 * le regole dicono che cosa è lecito, non che cosa conviene. Si fa come a
 * mano: per smentire "f è iniettiva" con l'ipotesi "per ogni X, Y,
 * f(X) \subseteq f(Y) implica X \subseteq Y" si prendono X = \{a\} e Y =
 * \{b\}, con a e b gli elementi che f manda nello stesso punto; per avere
 * f(X) = Z si prende X = f^{-1}(Z). Le parti provate per una parte legata
 * di S sono quelle che si scrivono con un solo passo da ciò che il ramo ha
 * già:
 *
 *   - le parti di S che hanno un nome (dichiarate, o nate da 28-2);
 *   - \{a\}, per ogni elemento a di S con un nome (dichiarato, o nato da
 *     28-2), uno per classe di elementi uguali;
 *   - \emptyset e S;
 *   - f^{-1}(\{c\}) e f^{-1}(P), per ogni applicazione f da S a T, ogni c di T
 *     con un nome e ogni parte P di T con un nome;
 *   - f(P), per ogni applicazione f a valori in S e ogni parte P con un nome
 *     del suo dominio;
 *   - S \setminus P, per ogni parte P di S con un nome.
 *
 * Perché questo limite: sono le costruzioni che si fanno partendo dagli
 * oggetti dell'enunciato senza inventarne di nuovi, e un passo solo, perché
 * le parti costruite da parti costruite crescerebbero senza fine (f(f^{-1}(f(
 * ...)))). Le dimostrazioni dei libri sulle immagini e le controimmagini
 * stanno quasi tutte qui dentro.
 *
 * Come si provano. Aggiungere tutte le istanze insieme, come per gli
 * elementi, non funziona: un'istanza come "f(X) \subseteq f(Y) implica X
 * \subseteq Y" è un'implicazione tra due "per ogni", che si usa solo
 * distinguendo i casi (28-5), e i casi di trenta istanze inutili
 * esaurirebbero la profondità prima di arrivare a quella giusta. Si prova
 * invece una scelta per volta, come chi cerca l'esempio giusto: per un
 * "per ogni parte" del ramo e una scelta delle sue parti, una copia del ramo
 * con le definizioni delle parti e l'istanza; se la copia si chiude, il ramo
 * è chiuso, altrimenti si butta la copia, con ciò che ha scritto, e si prova
 * la scelta successiva. Non è una distinzione di casi: basta che una scelta
 * riesca, perché ciò che si aggiunge è vero comunque.
 *
 * Le scelte vengono prima dei casi, così un'istanza vale in tutti i casi che
 * seguono; se nessuna basta si distinguono i casi, e in ognuno si può
 * scegliere di nuovo, perché casi diversi possono volere parti diverse. Una
 * scelta dentro l'altra al più MAX_PART_CHOICES volte in un ramo, e al più
 * MAX_PART_ATTEMPTS scelte per un'affermazione: oltre, NON DIMOSTRATO. Non
 * trovare la scelta giusta non vuol dire mai FALSO. */

/* Una parte da provare per una parte legata (vedi sopra), prima di
 * averla: come si scrive con ciò che c'è. */
typedef enum {
    P_SYMBOL,          /* una parte con un nome: part */
    P_SINGLE,          /* \{element\} */
    P_EMPTY,           /* \emptyset */
    P_WHOLE,           /* l'insieme sort, tutto */
    P_POINT_PREIMAGE,  /* map^{-1}(\{element\}) */
    P_PREIMAGE,        /* map^{-1}(part) */
    P_IMAGE,           /* map(part) */
    P_COMPLEMENT       /* sort \setminus part */
} PartKind;

/* Una parte dell'insieme sort da provare (PartKind dice quale). I
 * simboli sono posti in symbols[]: element un elemento con un nome, map
 * un'applicazione di un argomento, part una parte con un nome; -1 dove non
 * servono. */
typedef struct {
    PartKind kind;
    int sort, part, map, element;
} PartCandidate;

/* Le variabili delle definizioni (28j): per ogni insieme, la x di "\{x \in
 * S \mid ...\}" e la u di un'immagine, "esiste u con f(u) = x". Si creano la
 * prima volta che servono, con una lettera che l'enunciato non usa; -1
 * finché mancano. Tutte le definizioni le condividono: ognuna è una
 * condizione chiusa, che le lega. */
static int (*definition_slot)[2];
static size_t definition_slot_capacity;

/* Dimensiona i depositi della sola ricerca legacy per istanze. Sono
 * separati dai modelli e da Sp, che non devono pagarne le cache. */
static int instance_sorts_reserve(void) {
    size_t need=(size_t)sort_count;
    return work_reserve((void **)&candidate_domain,&candidate_domain_capacity,need,sizeof *candidate_domain) &&
           work_reserve((void **)&candidate_size,&candidate_size_capacity,need,sizeof *candidate_size) &&
           work_reserve((void **)&definition_slot,&definition_slot_capacity,need,sizeof *definition_slot);
}

/* Ritorna la variabile which (0 per x, 1 per u) delle definizioni di parti
 * di sort, o -1 (annotando exhausted) se le variabili o le lettere sono
 * finite. */
static int definition_variable(int sort, int which) {
    if (definition_slot[sort][which] < 0) {
        int slot = slot_new(fresh_letter(), 0, sort);
        if (slot < 0 || syntax_error) { syntax_error = NULL; exhausted = 1; return -1; }
        definition_slot[sort][which] = slot;
    }
    return definition_slot[sort][which];
}

/* Ritorna 1 se il simbolo symbol è un nome dato da 28-2 (o dichiarato) e non
 * una parte definita: solo da questi si costruiscono altre parti. */
static int part_named(int symbol) {
    return symbol < declared_symbols || (name_known[symbol] >= 0 && now->known[name_known[symbol]].origin == K_NAMED);
}

/* Mette in element[] gli elementi di sort con un nome nel ramo corrente,
 * uno per classe di elementi uguali, e ritorna quanti sono. */
static int named_elements(int sort, int *element) {
    static int *rep; static size_t capacity;
    size_t need = (size_t)(symbol_count < now->grounds ? symbol_count : now->grounds);
    if (!work_reserve((void **)&rep, &capacity, need, sizeof *rep)) { exhausted = 1; return 0; }
    int count = 0;
    for (int s = 0; s < symbol_count; s++) {
        int id = symbols[s].arity == 0 && symbols[s].range == sort ? ground_lookup(s, -1, -1, G_EXACT) : -1, fresh = id >= 0;
        for (int i = 0; i < count && fresh; i++) fresh = rep[i] != now->rep[id];
        if (!fresh) continue;
        rep[count] = now->rep[id];
        element[count++] = s;
    }
    return count;
}

/* Mette in out[] le parti di sort da provare, nell'ordine della testa del
 * paragrafo, al più MAX_PART_CANDIDATES, e ritorna quante sono. */
static int part_candidates(int sort, PartCandidate *out) {
    static int *element; static size_t capacity;
    size_t need = (size_t)(symbol_count < now->grounds ? symbol_count : now->grounds);
    if (!work_reserve((void **)&element, &capacity, need, sizeof *element)) { exhausted = 1; return 0; }
    int count = 0, elements;
#define CANDIDATE(...) do { if (count < MAX_PART_CANDIDATES) out[count++] = (PartCandidate){__VA_ARGS__}; } while (0)
    for (int s = 0; s < symbol_count; s++)
        if (part_of(s, sort) && part_named(s)) CANDIDATE(P_SYMBOL, sort, s, -1, -1);
    elements = named_elements(sort, element);
    for (int i = 0; i < elements; i++) CANDIDATE(P_SINGLE, sort, -1, -1, element[i]);
    CANDIDATE(P_EMPTY, sort, -1, -1, -1);
    CANDIDATE(P_WHOLE, sort, -1, -1, -1);

    /* Un passo da ciò che ha un nome: controimmagini, immagini,
     * complementari. Le applicazioni sono quelle dichiarate, di un
     * argomento. */
    for (int f = 0; f < declared_symbols; f++) {
        const Symbol *map = &symbols[f];
        if (map->arity != 1 || map->range == TRUTH || symbol_bound[f]) continue;
        if (map->domain[0] == sort) {
            elements = named_elements(map->range, element);
            for (int i = 0; i < elements; i++) CANDIDATE(P_POINT_PREIMAGE, sort, -1, f, element[i]);
            for (int s = 0; s < symbol_count; s++)
                if (part_of(s, map->range) && part_named(s)) CANDIDATE(P_PREIMAGE, sort, s, f, -1);
        }
        if (map->range == sort)
            for (int s = 0; s < symbol_count; s++)
                if (part_of(s, map->domain[0]) && part_named(s)) CANDIDATE(P_IMAGE, sort, s, f, -1);
    }
    for (int s = 0; s < symbol_count; s++)
        if (part_of(s, sort) && part_named(s)) CANDIDATE(P_COMPLEMENT, sort, s, -1, -1);
#undef CANDIDATE
    return count;
}

/* Ritorna la regola della parte candidate, la condizione c di "\{x \in S
 * \mid c\}", con la variabile x di posto x; NULL se mancano le variabili. */
static Sentence *candidate_rule(const PartCandidate *c, int x) {
    Elem *element = elem_new(-1, x, NULL, NULL), *named = c->element >= 0 ? elem_new(c->element, 0, NULL, NULL) : NULL;
    Sentence *s, *member;
    switch (c->kind) {
    case P_SINGLE:
        s = sentence_new(S_EQUAL, NULL, NULL, NULL);
        s->left = element;
        s->right = named;
        return s;
    case P_EMPTY:
        return sentence_new(S_NOT, sentence_new(S_TRUE, NULL, NULL, NULL), NULL, NULL);
    case P_POINT_PREIMAGE:
        s = sentence_new(S_EQUAL, NULL, NULL, NULL);
        s->left = elem_new(c->map, 0, element, NULL);
        s->right = named;
        return s;
    case P_PREIMAGE:
        s = sentence_new(S_HOLDS, NULL, NULL, NULL);
        s->left = elem_new(c->part, 0, elem_new(c->map, 0, element, NULL), NULL);
        return s;
    case P_IMAGE: {
        /* Esiste u nel dominio, in part, con map(u) = x. */
        int u = definition_variable(symbols[c->map].domain[0], 1);
        if (u < 0) return NULL;
        Elem *argument = elem_new(-1, u, NULL, NULL);
        member = sentence_new(S_HOLDS, NULL, NULL, NULL);
        member->left = elem_new(c->part, 0, argument, NULL);
        s = sentence_new(S_EQUAL, NULL, NULL, NULL);
        s->left = elem_new(c->map, 0, argument, NULL);
        s->right = element;
        s = sentence_new(S_EXISTS, sentence_new(S_AND, member, s, NULL), NULL, NULL);
        s->slot = u;
        return s;
    }
    case P_COMPLEMENT:
        member = sentence_new(S_HOLDS, NULL, NULL, NULL);
        member->left = elem_new(c->part, 0, element, NULL);
        return sentence_new(S_NOT, member, NULL, NULL);
    default:
        return sentence_new(S_TRUE, NULL, NULL, NULL);
    }
}

/* Dà nel ramo corrente un nome alla parte candidate, che non è P_SYMBOL: se
 * una parte con la stessa regola è già definita la riusa, altrimenti
 * registra una parte nuova, con la lettera letter e un pedice, e la sua
 * definizione "per ogni x di S, x sta nella parte se e solo se c(x)"
 * (K_DEFINED, 28j). Ritorna il simbolo, o -1. */
static int part_define(const PartCandidate *candidate, int letter) {
    SlotValues nothing = SLOT_VALUES_EMPTY;
    int x = definition_variable(candidate->sort, 0);
    Sentence *rule = x >= 0 ? candidate_rule(candidate, x) : NULL;
    if (!rule || exhausted) return -1;

    /* La stessa regola sulla stessa variabile, quindi parte dello stesso
     * insieme: \emptyset di S e \emptyset di T hanno la stessa regola, ma
     * sono parti diverse (un errore di questo genere è stato trovato così). */
    for (int i = 0; i < now->knowns; i++)
        if (now->known[i].origin == K_DEFINED && now->known[i].source->slot == x && sentence_renamed(now->known[i].source->a->b, rule, NULL, NULL, 0))
            return now->known[i].part[0];
    int part = part_symbol_new(letter, candidate->sort, 1);
    if (part < 0) return -1;
    Sentence *member = sentence_new(S_HOLDS, NULL, NULL, NULL);
    member->left = elem_new(part, 0, elem_new(-1, x, NULL, NULL), NULL);
    Sentence *definition = sentence_new(S_FORALL, sentence_new(S_IFF, member, rule, NULL), NULL, NULL);
    definition->slot = x;

    int at = known_add(definition, 0, nothing, K_DEFINED, -1);
    if (at < 0) return -1;
    int chosen = part;
    if (!known_parts(at, &chosen, 1)) return -1;
    name_known[part] = at;
    return part;
}

static int refute(int depth, int splits, int choices);

/* Le scelte provate finora per l'affermazione in corso, e 1 se una scelta,
 * o una prova di 28l, si è fermata a un limite del programma (exhausted):
 * allora non aver trovato la dimostrazione non dice nulla. */
static int part_attempts, part_interrupted;

/* Quante scelte di parti una dentro l'altra sono ammesse in un ramo nella
 * ricerca in corso: da 1 a MAX_PART_CHOICES (vedi abstract_claim()). */
static int part_limit;

/* Il punto a cui torna un tentativo non riuscito (una scelta di parti, 28k,
 * o una prova di 28l): quanto erano lunghi la dimostrazione scritta e il
 * certificato, la memoria usata, i rami chiusi, i nomi dati e le loro voci
 * già scritte, i simboli. */
typedef struct {
    size_t proof, certificate, arena;
    int leaves, names, broken, symbols, cases;  /* cases (28p): i cammini delle foglie scritte */
    unsigned char written[MAX_NAMES_GIVEN + 1];
} SearchMark;

/* Annota in *mark il punto in cui si trova la ricerca. */
static void search_mark(SearchMark *mark) {
    *mark = (SearchMark){proof_length, certificate_length, arena_used, leaves_closed, names_given, certificate_broken, symbol_count, case_paths, {0}};
    memcpy(mark->written, name_written, sizeof name_written);
}

/* Riporta la ricerca al punto mark, sul ramo di profondità depth: ciò che il
 * tentativo ha scritto e dato si dimentica. Un tentativo fermato a un limite
 * lo annota in part_interrupted, e non ferma gli altri. */
static void search_back(const SearchMark *mark, int depth) {
    proof_cut(mark->proof);
    certificate_length = mark->certificate;
    certificate_text[mark->certificate] = 0;
    certificate_broken = mark->broken;
    arena_used = mark->arena;
    leaves_closed = mark->leaves;
    names_given = mark->names;
    case_paths = mark->cases;
    memcpy(name_written, mark->written, sizeof name_written);
    symbol_count = mark->symbols;
    now = &branch[depth];
    ground_reindex();
    if (exhausted) { part_interrupted = 1; exhausted = 0; }
}

/* Prova a chiudere il ramo di profondità depth con una scelta di parti per
 * uno dei suoi "per ogni parte" (vedi la testa del paragrafo); splits e
 * choices sono le distinzioni di casi e le scelte già fatte sopra di lui.
 * Ritorna 1 se una scelta chiude il ramo, con la dimostrazione e le voci del
 * certificato di quella sola; 0 se nessuna, e allora non lascia nulla:
 * testo, certificato, nomi, memoria e il ramo tornano come erano. */
static int part_choose(int depth, int splits, int choices) {
    PartCandidate *candidate = NULL;
    int *names = NULL;
    int *index = NULL, closed = 0;
    size_t candidate_capacity = 0, name_capacity = 0, index_capacity = 0;
    Branch *here = &branch[depth];
    for (int r = 0; r < here->knowns; r++) {
        const Known *rule = &here->known[r];
        if (rule->stage != K_RULE || !part_quantifier(rule->source)) continue;

        /* Le parti legate in testa alla regola, e le parti da provare per
         * ognuna. I temporanei appartengono a questa chiamata: una scelta
         * ricorsiva puo crescere senza spostare i vettori del suo genitore. */
        const Sentence *body = rule->source;
        int parts = 0, more = 1;
        for (const Sentence *q = body; part_quantifier(q) && (q->kind == S_FORALL_PART) != rule->negated; q = q->a) parts++;
        if (!work_reserve((void **)&candidate, &candidate_capacity, (size_t)parts * MAX_PART_CANDIDATES, sizeof *candidate) ||
            !work_reserve((void **)&names, &name_capacity, 2 * (size_t)parts, sizeof *names) ||
            !work_reserve((void **)&index, &index_capacity, 2 * (size_t)parts, sizeof *index)) {
            exhausted = 1; goto done;
        }
        int *bound = names, *chosen = names + parts;
        int *candidates = index, *pick = index + parts;
        for (int j = 0; j < parts; j++, body = body->a) {
            bound[j] = body->part;
            candidates[j] = part_candidates(symbols[body->part].domain[0], candidate + (size_t)j * MAX_PART_CANDIDATES);
            pick[j] = 0;
            more = more && candidates[j] > 0;
        }

        /* Ogni scelta, come un contachilometri. */
        for (; more; ) {
            SearchMark mark;
            if (part_attempts++ >= MAX_PART_ATTEMPTS || failure) goto done;
            search_mark(&mark);

            /* La copia del ramo, con le definizioni delle parti scelte e
             * l'istanza, se non c'è già. */
            int fresh = 1;
            branch_copy(depth);
            for (int j = 0; j < parts && fresh; j++) {
                const PartCandidate *c = &candidate[(size_t)j * MAX_PART_CANDIDATES + (size_t)pick[j]];
                chosen[j] = c->kind == P_SYMBOL ? c->part : part_define(c, symbols[bound[j]].name);
                fresh = chosen[j] >= 0;
            }
            for (int i = r + 1; i < now->knowns && fresh; i++)
                fresh = now->known[i].parent != r || now->known[i].parts != parts ||
                        memcmp(now->known[i].part, chosen, sizeof *chosen * (size_t)parts) != 0;
            if (fresh) {
                const Sentence *instance = body;
                for (int j = 0; j < parts; j++) instance = sentence_rename(instance, bound[j], chosen[j]);
                int at = known_add(instance, rule->negated, rule->value, K_INSTANCE, r);
                if (at >= 0 && known_parts(at, chosen, parts)) {
                    if (!exhausted && refute(depth + 1, splits, choices + 1)) { closed = 1; goto done; }
                }
            }

            /* Non è bastata: si torna com'era, e alla scelta successiva. */
            search_back(&mark, depth);
            more = 0;
            for (int j = 0; j < parts && !more; j++) {
                if (++pick[j] < candidates[j]) more = 1; else pick[j] = 0;
            }
        }
    }
done:
    free(candidate); free(names); free(index);
    return closed;
}

/* 28-5. Aggiunge alle cose note del ramo in corso il caso side della
 * disgiunzione in attesa di posto open, che non resta più in attesa. */
static void case_continue(int open, int side) {
    Known *k = &now->known[open];
    Parts parts;
    k->stage = K_DONE;
    if (k->source->kind == S_IFF) {
        /* "A se e solo se B": o tutte e due vere, o tutte e due false; se è
         * negato, una vera e l'altra falsa. Il caso fissa A, e con lei B. */
        known_add(k->source->a, side, k->value, K_CASE, open);
        known_add(k->source->b, side != k->negated, k->value, K_CASE, open);
    } else if (sentence_parts(k->source, k->negated, &parts)) {
        known_add(side ? parts.y : parts.x, side ? parts.ny : parts.nx, k->value, K_CASE, open);
    }
}

/* 28-5. Apre il caso side della disgiunzione in attesa di posto open: una
 * copia del ramo di profondità depth (branch_copy()), con quel caso in più
 * tra le cose note. */
static void case_open(int depth, int open, int side) {
    branch_copy(depth);
    case_continue(open, side);
}

/* 28o. LA SCELTA DEL CASO
 *
 * (Sta qui, accanto a 28-5 che serve; la lettera è venuta dopo le altre.)
 *
 * 28-5 distingue i casi della prima disgiunzione in attesa, dopo
 * MAX_ROUNDS giri di istanze. Con le parti e le applicazioni come oggetti
 * le istanze crescono in fretta (un elemento dà una parte che lo contiene,
 * la parte un elemento che contiene, e così via), e le tabelle si riempiono
 * prima della fine dei giri; e le disgiunzioni in attesa sono decine, con la
 * prima che spesso non serve. Con split_lookahead acceso, dopo ogni giro si
 * guarda avanti: per le disgiunzioni in attesa più recenti (al più
 * MAX_LOOKAHEAD) si apre ognuno dei due casi e si vede se si chiude da solo,
 * con ciò che segue senza istanze (settle()). Se una ha un caso che si
 * chiude, si distinguono subito i suoi casi, preferendo quella con tutti e
 * due chiusi; altrimenti si va avanti come prima. È la regola del
 * "letterale che fallisce" dei dimostratori: un caso che si chiude subito
 * costa una riga, e l'altro sa una cosa in più. Le prove non lasciano nulla:
 * i casi aperti sono copie, e i nomi dati lì si tolgono. Cambia solo
 * l'ordine della ricerca, non ciò che una dimostrazione trovata dice: ogni
 * suo passo è ricontrollato come sempre (28e). Le stesse prove scelgono le
 * istanze con più cura (instance_guarded(), in 28-3, dove split_lookahead è
 * dichiarata). */

/* Ritorna la disgiunzione in attesa del ramo di profondità depth con un
 * caso che si chiude da solo, scelta come in testa al paragrafo, o -1; in
 * *closing mette quale caso si chiude, 0 o 1, oppure 2 se si chiudono tutti
 * e due. */
static int split_choice(int depth, int *closing) {
    int best = -1, probes = 0, saved = exhausted;
    for (int i = branch[depth].knowns - 1; i >= 0 && probes < MAX_LOOKAHEAD; i--) {
        if (branch[depth].known[i].stage != K_WAITING) continue;
        int closed[2];
        probes++;
        for (int side = 0; side < 2; side++) {
            case_open(depth, i, side);
            closed[side] = settle() && !exhausted;
            exhausted = saved;
            symbol_count = branch[depth].symbols;
        }
        if (closed[0] && closed[1]) { best = i; *closing = 2; break; }
        if ((closed[0] || closed[1]) && best < 0) { best = i; *closing = closed[1]; }
    }
    now = &branch[depth];
    ground_reindex();
    return best;
}

/* 28l. Il valore di splits con cui refute() fa solo i suoi giri di istanze,
 * senza casi né scelte: è la prova di un caso. */
#define PROBE (MAX_SPLITS + 1)

/* 28l. Cerca, tra le prime MAX_PROBES disgiunzioni in attesa del ramo di
 * profondità depth, una con un caso che si chiude con i soli giri di
 * istanze; se la trova, chiude quel caso e poi l'altro, con le stesse
 * distinzioni di casi (splits) e scelte (choices) che restano al ramo.
 * Ritorna 1 se il ramo si è chiuso così; 0 se nessuna disgiunzione ha un
 * caso così, e allora non lascia nulla; -1 se ce n'era una ma l'altro caso
 * non si è chiuso: allora nemmeno il ramo si chiuderebbe (l'altro caso sa
 * tutto ciò che sa il ramo, e una cosa in più), e non lascia nulla. */
static int cheap_split(int depth, int splits, int choices) {
    static SearchMark mark[MAX_BRANCHES];
    Branch *here = &branch[depth];
    for (int open = 0, probes = 0; open < here->knowns && probes < MAX_PROBES && !failure; open++) {
        if (here->known[open].stage != K_WAITING) continue;
        probes++;
        for (int side = 0; side < 2; side++) {
            search_mark(&mark[depth]);
            case_open(depth, open, side);
            if (!refute(depth + 1, PROBE, choices)) { search_back(&mark[depth], depth); continue; }
            now = here;
            symbol_count = here->symbols;
            case_open(depth, open, !side);
            if (refute(depth + 1, splits, choices)) return 1;
            search_back(&mark[depth], depth);
            return -1;
        }
    }
    return 0;
}

/* Cerca una contraddizione in ogni continuazione del ramo di profondità
 * depth, e scrive la dimostrazione di ogni ramo che chiude. Ritorna 1 se li
 * chiude tutti, e allora ciò che il ramo suppone è impossibile. splits e
 * choices sono le distinzioni di casi e le scelte di parti (28k) fatte
 * sopra di lui; con splits uguale a PROBE fa solo i giri di istanze (28l).
 *
 * Prima ciò che segue senza scelte e le istanze, per un numero fisso di
 * giri (rounds_before_split). Se non basta, una disgiunzione con un caso che
 * si chiude subito (28l), che non conta tra le distinzioni di casi; poi una
 * scelta di parti (28k); poi 28-5: la prima disgiunzione in attesa dà due
 * casi, ognuno una copia del ramo con una parte in più tra le cose note, e
 * devono chiudersi tutti e due.
 *
 * 28o. Con split_lookahead, dopo ogni giro: se una disgiunzione ha i due
 * casi che si chiudono con ciò che segue senza istanze, si distinguono, e
 * il ramo è chiuso senza contarla tra le distinzioni; se ne ha uno, quello
 * si scrive subito, chiuso, e il ramo va avanti con l'altro caso tra le
 * cose note, senza scendere di profondità. */
static int refute(int depth, int splits, int choices) {
    int open = -1, closing = 0;
    now = &branch[depth];
    for (int round = 0; !exhausted; round++) {
        if (settle()) {
            /* Il ramo è chiuso: la sua dimostrazione scritta, e le sue voci
             * del certificato. */
            if (!leaf_write(splits || leaves_closed ? ++leaves_closed : 0)) return 0;
            cert_leaf();
            return 1;
        }

        /* 28o. Un caso che si chiude da solo vale più di altre istanze. */
        if (split_lookahead && splits != PROBE && depth + 1 < MAX_BRANCHES && (open = split_choice(depth, &closing)) >= 0) {
            if (closing == 2) break;
            case_open(depth, open, closing);
            if (!settle() || !leaf_write(++leaves_closed)) return 0;
            cert_leaf();
            now = &branch[depth];
            symbol_count = now->symbols;
            ground_reindex();
            case_continue(open, !closing);
            open = -1;
            round--;
            continue;
        }
        if (round == rounds_before_split || !instantiate()) break;
    }
    if (exhausted || splits == PROBE || depth + 1 == MAX_BRANCHES) return 0;
    if (open < 0) {
        int cheap = cheap_split(depth, splits, choices);
        if (cheap) return cheap > 0;
        if (choices < part_limit && part_choose(depth, splits, choices)) return 1;
    }
    for (int i = 0; i < now->knowns && open < 0; i++)
        if (now->known[i].stage == K_WAITING) open = i;
    if (exhausted || open < 0 || (splits == MAX_SPLITS && closing != 2)) return 0;
    for (int side = 0; side < 2; side++) {
        /* Il caso: una copia del ramo, con i suoi elementi e i suoi nomi. */
        case_open(depth, open, side);
        if (!refute(depth + 1, splits + (closing != 2), choices)) return 0;
        now = &branch[depth];
        symbol_count = now->symbols;
    }
    return 1;
}

/* Ritorna 1 se dalle ipotesi, le condizioni di hypothesis[0..hypotheses),
 * segue claim: lo dimostra per assurdo, e scrive la dimostrazione. Se
 * ritorna 0 non lascia testo.
 *
 * 28k. La ricerca si fa con al più una scelta di parti per ramo, poi, se non
 * basta e qualche scelta c'è stata, da capo con due: così una scelta in più
 * non viene provata prima di una distinzione di casi che basterebbe, e la
 * dimostrazione non si porta dietro parti che non servono. */
static int abstract_claim(const Sentence **hypothesis, int hypotheses, const Sentence *claim) {
    SlotValues nothing = SLOT_VALUES_EMPTY;
    size_t start = proof_length, certificate_start = certificate_length, arena_start = arena_used;
    int declared = symbol_count, proved = 0, certificate_was_broken = certificate_broken;

    for (part_limit = 1; part_limit <= MAX_PART_CHOICES && !proved && !exhausted; part_limit++) {
        proof_cut(start);
        certificate_length = certificate_start;
        certificate_text[certificate_start] = 0;
        arena_used = arena_start;
        symbol_count = declared;

        /* Il ramo di partenza: "vero" al posto 0, gli elementi con un nome
         * che l'enunciato dichiara, le ipotesi, la tesi negata.
         *
         * Perché gli elementi dichiarati subito. Un elemento entra nella
         * tabella quando lo nomina un fatto; ma u, dichiarato con u \in S,
         * può comparire solo sotto un quantificatore, come in f(u) \in
         * f(\{u\}), e allora nessuna istanza lo proverebbe. Metterlo in
         * tabella è lecito: u è un elemento di S, e un'istanza su u è
         * un'istanza su un termine chiuso fatto di simboli dichiarati, che il
         * verificatore accetta (11d, 11f di checker.c). */
        now = &branch[0];
        now->knowns = now->differents = now->clock = 0;
        now->grounds = 0;
        memset(exact, -1, sizeof exact);
        ground_lookup(-1, -1, -1, G_CREATE);
        for (int s = 0; s < declared; s++)
            if (symbols[s].arity == 0) ground_lookup(s, -1, -1, G_CREATE);
        for (int i = 0; i < hypotheses; i++) known_add(hypothesis[i], 0, nothing, K_GIVEN, -1);
        known_add(claim, 1, nothing, K_DENIED, -1);

        proof_add("\\item \\emph{Claim:} $");
        put_sentence(claim, 0, nothing, 0);
        proof_add("$.\n\\begin{itemize}\n");
        leaves_closed = 0;

        /* Nel certificato, un caso per l'affermazione: la si suppone falsa.
         * I nomi ripartono da capo, come nel verificatore. */
        cert_add("case (not ");
        cert_sentence(claim, nothing);
        cert_add(")\n");
        names_given = 0;
        memset(name_written, 0, sizeof name_written);
        part_attempts = 0;
        case_paths = case_overflow = 0;
        proved = refute(0, 0, 0);
        proof_add("\\end{itemize}\n");

        /* 28p. I casi scritti devono coprire tutto: se non lo fanno, il
         * programma ha sbagliato, e l'affermazione non è dimostrata. */
        if (proved && !case_paths_complete()) {
            unjustified_steps++;
            proved = 0;
            break;
        }
        if (!part_attempts) break;
    }

    /* I nomi dati durante la dimostrazione valgono solo per lei. Se non
     * riesce, il suo caso esce anche dal certificato (28n: la si può
     * riprovare con più leggi). */
    symbol_count = declared;
    if (!proved) {
        proof_cut(start);
        certificate_length = certificate_start;
        certificate_text[certificate_start] = 0;
        certificate_broken = certificate_was_broken;
    }
    return proved;
}

/* Ritorna 1 se l'affermazione claim segue dalle ipotesi hypothesis[]: le
 * prime first_pass sono le ipotesi dell'enunciato e le estensionalità
 * (28n), le altre, fino a hypotheses, le comprensioni. Prova come
 * abstract_claim(), con le sole prime; poi (28o) guardando avanti e
 * distinguendo i casi dopo LOOKAHEAD_ROUNDS giri, prima che le istanze
 * riempiano le tabelle; poi, se ci sono, anche con le comprensioni. */
static int claim_passes(const Sentence **hypothesis, int hypotheses, int first_pass, const Sentence *claim) {
    int first = first_pass < hypotheses ? first_pass : hypotheses;
    int proved = abstract_claim(hypothesis, first, claim);
    for (int pass = 1; !proved && pass < 3; pass++) {
        if (pass == 2 && first_pass >= hypotheses) break;
        exhausted = 0;
        split_lookahead = 1;
        rounds_before_split = LOOKAHEAD_ROUNDS;
        proved = abstract_claim(hypothesis, pass == 1 ? first : hypotheses, claim);
        split_lookahead = 0;
        rounds_before_split = MAX_ROUNDS;
    }
    return proved;
}

/* 28r. Come claim_passes(), con le istanze scelte dal modello candidato: per
 * ogni generazione di model_generations[], prima senza e poi con le
 * comprensioni, e MODEL_ROUNDS giri prima di distinguere i casi, perché ogni
 * giro aggiunge una sola istanza per "per ogni", e una catena di istanze che
 * dipendono l'una dall'altra chiede un giro per anello. */
static int model_passes(const Sentence **hypothesis, int hypotheses, int first_pass, const Sentence *claim) {
    int first = first_pass < hypotheses ? first_pass : hypotheses, proved = 0;
    for (size_t g = 0; !proved && g < sizeof model_generations / sizeof *model_generations; g++)
        for (int all = 0; all < 2 && !proved && (!all || first < hypotheses); all++) {
            exhausted = 0;
            model_guided = 1;
            generation_limit = model_generations[g];
            rounds_before_split = MODEL_ROUNDS;
            proved = abstract_claim(hypothesis, all ? hypotheses : first, claim);
            model_guided = 0;
            rounds_before_split = MAX_ROUNDS;
        }
    return proved;
}

/* Come claim_passes(), e (28q) con un testimone per volta per le
 * equipotenze da dimostrare: dal più corto, finché la dimostrazione riesce o
 * i testimoni finiscono. Senza equipotenze witness_options resta 0, e il
 * giro è uno solo. Infine (28r) model_passes(), con il primo testimone: le
 * istanze scelte dal modello vengono dopo tutte le altre prove, così ciò che
 * quelle dimostrano non cambia. */
static int claim_attempts(const Sentence **hypothesis, int hypotheses, int first_pass, const Sentence *claim) {
    int proved = 0;
    witness_options = 0;
    for (witness_choice = 0; !proved && (witness_choice == 0 || witness_choice < witness_options); witness_choice++) {
        if (witness_choice) exhausted = 0;
        proved = claim_passes(hypothesis, hypotheses, first_pass, claim);
    }

    /* Un testimone che ha dentro un passo w3 o w4 sotto un'altra applicazione
     * (un prodotto, una composizione) chiede le identità di quel passo a metà
     * della dimostrazione, con l'estensionalità, e quindi più giri di istanze
     * prima di distinguere i casi: un ultimo tentativo con il doppio, per
     * ogni testimone. */
    for (witness_choice = 0; !proved && witness_choice < witness_options; witness_choice++) {
        exhausted = 0;
        rounds_before_split = 2 * MAX_ROUNDS;
        proved = abstract_claim(hypothesis, first_pass < hypotheses ? first_pass : hypotheses, claim);
        rounds_before_split = MAX_ROUNDS;
    }
    witness_choice = 0;
    if (!proved) proved = model_passes(hypothesis, hypotheses, first_pass, claim);
    return proved;
}
/* 28o. Un'affermazione che non si dimostra tutta insieme si prova a pezzi,
 * ognuno come un'affermazione a sé: un'equivalenza A \iff B nei due versi,
 * A \implies B e B \implies A; A \implies (B \land C) come A \implies B e A
 * \implies C. L'affermazione segue dai pezzi per le sole leggi della logica,
 * e il verificatore, che ritrova i connettivi da sé (11e in checker.c), lo
 * ricontrolla. Ritorna 1 se ogni pezzo è dimostrato; un pezzo che non si
 * dimostra si divide ancora, se si può. */
static int claim_halves(const Sentence **hypothesis, int hypotheses, int first_pass, const Sentence *claim) {
    const Sentence *x, *y;
    if (claim->kind == S_IFF) {
        x = axiom_join(S_IMPLIES, claim->a, claim->b);
        y = axiom_join(S_IMPLIES, claim->b, claim->a);
    } else if (claim->kind == S_IMPLIES && claim->b->kind == S_AND) {
        x = axiom_join(S_IMPLIES, claim->a, claim->b->a);
        y = axiom_join(S_IMPLIES, claim->a, claim->b->b);
    } else {
        return 0;
    }
    return (claim_attempts(hypothesis, hypotheses, first_pass, x) || claim_halves(hypothesis, hypotheses, first_pass, x)) &&
           (claim_attempts(hypothesis, hypotheses, first_pass, y) || claim_halves(hypothesis, hypotheses, first_pass, y));
}

/* Aggiunge a list[], dal posto count, le condizioni di cui s è la
 * congiunzione, saltando le dichiarazioni; ritorna il nuovo numero, al più
 * max. */
static int conjuncts(const Sentence *s, const Sentence **list, int count, int max) {
    if (s->kind == S_AND) return conjuncts(s->b, list, conjuncts(s->a, list, count, max), max);
    if (s->kind != S_TRUE && count < max) list[count++] = s;
    return count;
}

/* Il testo di un modello, per il verdetto in una riga: una copia posseduta
 * qui, riusata tra gli enunciati e valida fino al modello successivo. */
static char *model_text;
static size_t model_text_capacity;  /* Byte posseduti in model_text. */

/* Consegna un modello gia trovato: ricalcola ipotesi, tesi e notazione
 * scritta, poi scrive il documento e il certificato indipendente. La stessa
 * uscita serve alle due quote di ricerca; una ricerca precedente puo aver
 * lasciato una dimostrazione incompleta, che qui viene svuotata. */
static Verdict abstract_model_result(Verdict verdict, const Sentence *written, const Sentence *root,
                                     const Model *model, long long compared) {
    size_t *value = model_variables();
    if (work_allocation_failed) { verdict.outcome = NOT_PROVED; verdict.reason = OUT_OF_MEMORY; return verdict; }
    proof_reset();

    /* Il modello trovato viene ricalcolato pezzo per pezzo: ipotesi
     * vere e tesi falsa, e non solo "l'implicazione è falsa". Con la
     * notazione dei libri, anche l'enunciato com'è scritto (28h). */
    model_steps = 0;
    int confirmed = abstract_example ? model_holds(model, root, value)
                  : root->kind == S_IMPLIES ? model_holds(model, root->a, value) && !model_holds(model, root->b, value)
                  : !model_holds(model, root, value);
    if (written != root) confirmed = confirmed && book_holds(model, written, value) == abstract_example;

    /* Un conto interrotto non conferma nulla, nemmeno quando il suo valore
     * è quello atteso: per un controesempio "non vale" è anche ciò che
     * ritorna un quantificatore fermato a metà. */
    if (!model_steps_complete()) {
        verdict.outcome = NOT_PROVED;
        verdict.reason = "il modello trovato non si è potuto ricalcolare entro il budget dei passi (--model-steps)";
        return verdict;
    }
    if (!confirmed) {
        unjustified_steps++;
        verdict.outcome = NOT_PROVED;
        verdict.reason = "la verifica indipendente non conferma il modello trovato";
        return verdict;
    }
    proof_add(abstract_example ? "\\textbf{Proof.} An example: " : "\\textbf{The statement is false.} A counterexample: ");
    proof_growable = 1;
    size_t from = proof_length;
    put_model(model);
    if (proof_broken) { verdict.outcome = NOT_PROVED; verdict.reason = "memoria esaurita scrivendo il modello"; return verdict; }
    /* Una copia intera: il testo di un modello cresce con i suoi insiemi,
     * e troncato a metà di una formula non si legge più (con 130 insiemi la
     * riga del verdetto finiva in "$S_{120} = \{"). La dimostrazione scritta
     * continua a crescere e può spostarsi: non si può puntare lì dentro. */
    size_t model_length = proof_length - from;
    if (!work_reserve((void **)&model_text, &model_text_capacity, model_length + 1, 1)) {
        verdict.outcome = NOT_PROVED; verdict.reason = OUT_OF_MEMORY; return verdict;
    }
    memcpy(model_text, proof_text + from, model_length);
    model_text[model_length] = 0;
    proof_add(abstract_example ? ". Computing with these tables, the condition holds." : ". Computing with these tables, the hypotheses hold and the conclusion fails.");
    put_unfolding_note(compared);
    if (abstract_example) proof_add(" $\\Box$");
    verdict.outcome = abstract_example ? PROVED : REFUTED;
    verdict.method = "con un esempio";
    verdict.detail = abstract_example ? NULL : model_text;
    verdict.proof = proof_text;

    /* Il certificato: il modello, in cui il verificatore ricalcola
     * l'enunciato con il suo valutatore. Se non lo sa ricalcolare (un
     * modello troppo grande per lui) il modello resta senza conferma, e
     * il verdetto non c'è: required = 1. */
    cert_abstract_head(abstract_example ? "example" : "counterexample", root, model);
    for (int s = 0; s < symbol_count; s++) {
        size_t cells;
        if (symbol_fixed(s) || symbol_bound[s]) continue;  /* fissato (28m), o una parte legata (28i): non ha tabella */
        model_cells(model, s, &cells);
        cert_add("table ");
        cert_symbol(s);
        for (size_t c = 0; c < cells; c++) cert_add(" %zu", model->table[s][c]);
        cert_add("\n");
    }
    cert_add("end\n");
    return abstract_certified(verdict);

}

/* Una quota di lavoro del model finding. Il limite di cardinalita resta
 * assente: cambiare quota modifica soltanto quanta ricerca si esegue prima
 * di dare tempo alla dimostrazione. Il programma ha uno stato singolo. */
static int model_sat_slice(const Sentence *root, int wanted, Model *model, long long *tried, int bound,
                           unsigned long long allowance) {
    if (!allowance) return 0;
    unsigned long long saved = model_work_limit;
    model_work_limit = allowance;
    int found = model_sat_search(root, wanted, model, tried, bound);
    model_work_limit = saved;
    return found;
}

/* 28u. SATURAZIONE: CLAUSOLE DA FARE E CLAUSOLE GIA ELABORATE
 *
 * Si nega l'enunciato e lo si traduce nel primo ordine non tipato, con un
 * predicato per ogni dominio: gli insiemi possono essere vuoti. Skolem
 * conserva le dipendenze dagli universali e i nomi di Tseitin conservano
 * tutte le variabili libere. Il checker ricostruisce la traduzione con un
 * lettore e strutture indipendenti; nessuna sua funzione cerca per noi.
 *
 * Una clausola scelta dalla coda viene combinata con quelle elaborate:
 * risoluzione, risoluzione dell'uguaglianza, fattorizzazione e superposizione.
 * I genitori hanno sempre variabili distinte prima dell'unificazione.
 * L'occurs-check impedisce sostituzioni cicliche: x=f(x) non ha un
 * unificatore tra termini finiti. Ogni deduzione conserva genitori,
 * posizioni e sostituzione simultanea completamente risolta.
 *
 * KBO con tutti i pesi uguali a uno orienta le riscritture; una clausola
 * sussunta e ridondante. La scelta alterna peso ed eta: ogni quinto turno
 * prende la piu vecchia, quindi una clausola persistente non resta esclusa
 * perche continuano a nascerne di leggere. Esaurire risorse o saturare senza
 * il vuoto non prova la tesi. Solo il vuoto ricontrollato la dimostra.
 *
 * SInE sceglie prima le clausole attivate dai simboli meno comuni della
 * tesi, poi allarga la tolleranza. Il portafoglio limita questi tentativi
 * per lavoro e tempo CPU; l'ultimo riattiva tutte le clausole. Le clausole
 * sospese conservano indice e contenuto: il checker ricostruisce sempre
 * l'enunciato originale, non una tesi riscritta dal selettore. Riprendere
 * dopo una quota richiede di rimettere in coda anche le clausole elaborate:
 * l'ultima inferenza puo essere stata interrotta a meta.
 *
 * AVATAR separa componenti a variabili disgiunte e introduce nomi per le
 * loro chiusure universali. Il SAT sceglie quali richiedere; le assunzioni
 * restano guardie nelle clausole complete. Una contraddizione condizionale
 * diventa un vincolo booleano che esclude il ramo. Prima di cambiare ramo
 * si rilegge il modello contro tutte le clausole SAT. Una risposta UNSAT
 * richiede un replay RUP: propagazione sotto le assunzioni opposte alla
 * clausola appresa, poi risoluzione all'indietro delle ragioni del conflitto.
 * Il checker riceve solo definizioni, partizioni e risoluzioni esplicite.
 * SAT, replay e clausole condividono i budget di lavoro e memoria; una
 * quota locale lascia al ciclo ordinario le trasformazioni gia valide.
 *
 * I principi universali su parti vengono istanziati con comprensioni
 * {x in S | L(x)}, da proprieta letterali ricavate dai controesempi ground.
 * Questo permette di usare principi induttivi forniti come ipotesi: non
 * attribuisce a un insieme arbitrario la semantica standard dei naturali.
 * Le istanze hanno contesti copiati, nomi freschi e gruppi di clausole
 * ricostruiti dal checker. Una clausificazione direzionale della NNF e
 * l'eliminazione booleana dei nomi tecnici limitano i passaggi ausiliari;
 * tutte le semplificazioni conservano risoluzioni esplicite. Non si assume
 * mai vera la proprieta scelta per la comprensione.
 *
 * Riferimenti: Kovacs e Voronkov, First-Order Theorem Proving and Vampire
 * (2013); Sternagel e Thiemann, Formalizing Knuth-Bendix Orders and
 * Knuth-Bendix Completion (2013); Hoder e Voronkov, Sine Qua Non for Large
 * Theory Reasoning (2011), selezione applicata qui alle clausole e ai soli
 * simboli originali, non ai nomi tecnici della traduzione; Voronkov,
 * AVATAR (2014); Plaisted e Greenbaum, A Structure-Preserving Clause Form
 * Translation (1986); Reger e Voronkov, Induction in Saturation-Based
 * Proof Search (2019). Si implementano
 * le regole, senza codice o risolutori esterni.
 */

/* Un blocco stabile di memoria della ricerca. next concatena i blocchi,
 * used/capacity contano byte del payload allineato. Nessun blocco si sposta.
 * I temporanei si riusano fra inferenze; le deduzioni vivono fino al termine. */
typedef struct SpBlock SpBlock;
struct SpBlock {
    SpBlock *next;
    size_t used, capacity;
    _Alignas(16) unsigned char data[];
};

/* Un'arena possiede tutti i blocchi a partire da first; current e quello
 * da cui continuare. Solo l'arena dei temporanei viene azzerata. */
typedef struct { SpBlock *first, *current; } SpArena;

/* Un simbolo della traduzione: arity conta gli argomenti; predicate
 * distingue un atomo da una funzione. component vale indice AVATAR piu
 * uno, zero negli altri casi. Il numero e quello nel certificato. */
typedef struct { int arity, predicate, component; } SpSymbol;

/* Un termine condiviso, con argomenti contigui in argument. weight e il
 * numero di occorrenze di simboli e variabili, per KBO e la scelta in coda.
 * Un riferimento positivo indica un termine; -1-v la variabile v; zero
 * l'assenza di un termine, usata per i predicati e le costanti logiche. */
typedef struct { int symbol, first, count; unsigned long long weight; } SpTerm;

/* Un atomo eventualmente negato. right!=0 indica un'uguaglianza; altrimenti
 * left e un predicato, oppure zero per vero. negative appartiene a {0,1}. */
typedef struct { int left, right, negative; } SpLiteral;

/* Una sostituzione esplicita nel certificato: variable e il nome prima
 * della normalizzazione, term la sua immagine gia completamente risolta. */
typedef struct { int variable, term; } SpBinding;

/* Regole del calcolo: INPUT viene ricostruita dal checker; COMPONENT e
 * COMPLEMENT sono definizioni conservative, SPLIT astrae una partizione,
 * COMPREHEND ricostruisce un'istanza universale su parti.
 * Le altre sono le inferenze esplicite del primo ordine.
 * Warning: una nuova regola richiede l'aggiornamento di sp_write(). */
typedef enum { SP_INPUT, SP_RESOLVE, SP_REFLEX, SP_FACTOR, SP_SUPER, SP_EQUAL_FACTOR,
               SP_COMPONENT, SP_COMPLEMENT, SP_SPLIT, SP_COMPREHEND } SpRule;

/* Un gruppo dello split: component identifica la chiusura universale,
 * negative il complemento ground. literal ha count indici nel genitore;
 * dopo sp_keep e posseduto dall'arena persistente della deduzione. */
typedef struct { int component, negative, count; const int *literal; } SpGroup;

/* Dati sufficienti a ricontrollare una deduzione. p/q e lp/lq identificano
 * genitori e letterali; flip/otherflip scelgono i versi delle uguaglianze;
 * side/position individuano il sotto-termine in visita preorder. binding
 * ha bindings immagini simultanee, possedute dall'arena della clausola.
 * groups/group descrivono soltanto SPLIT; per le due definizioni p e
 * invece l'indice della componente e non un genitore. Per COMPREHEND p
 * identifica l'istanza, senza genitori fra le clausole della ricerca. */
typedef struct {
    SpRule rule;
    int p, lp, q, lq, flip, otherflip, side, position;
    int bindings;
    const SpBinding *binding;
    int groups;
    const SpGroup *group;
} SpStep;

/* Stato di una clausola nella ricerca. Cancellarla dalla ricerca conserva
 * la deduzione nel deposito, perche puo essere genitore di una prova.
 * HELD sospende un'ipotesi di SInE, LOCKED una clausola le cui guardie
 * non sono attive nel modello SAT. BOOLEAN e affidata alla ricerca SAT. */
typedef enum { SP_PENDING, SP_ACTIVE, SP_DELETED, SP_HELD, SP_LOCKED, SP_BOOLEAN } SpStage;

/* Indice sparso di SInE, posseduto dall'arena persistente della ricerca.
 * first[i..i+1] delimita in symbol i simboli originali distinti della
 * clausola iniziale i; reverse[j..j+1] delimita in clause le clausole che
 * contengono il simbolo j. frequency conta clausole, non occorrenze di un
 * termine; minimum[i] e la frequenza minima nei simboli della clausola,
 * zero se non ne ha. Entrambi gli indici occupano spazio lineare nei dati. */
typedef struct {
    size_t *first, *reverse, *frequency, *minimum;
    int *symbol, *clause;
} SpSine;

/* Una clausola immutabile quanto a letterali e deduzione. count e il numero
 * di letterali, variables quello dei nomi normalizzati; literal e posseduto
 * dall'arena. signature filtra solo confronti impossibili di sussunzione,
 * weight ordina la coda. stage e l'unico campo modificato dalla ricerca. */
typedef struct {
    int count, variables;
    const SpLiteral *literal;
    SpStep step;
    SpStage stage;
    unsigned long long signature, weight;
} SpClause;

/* Una componente universalmente chiusa e il suo nome proposizionale.
 * key possiede letterali nell'arena persistente; symbol e fresco e senza
 * argomenti, atom il riferimento al suo termine condiviso (zero durante
 * una costruzione interrotta). forward/reverse sono clausole di definizione, -1 se una quota
 * ne ha interrotto la costruzione. value conserva il modello SAT fra due
 * chiamate CDCL: non dipende dalle assegnazioni temporanee del risolutore. */
typedef struct { SpClause key; int symbol, atom, forward, reverse, value; } SpComponent;

/* Una parte definita nel contesto di lettura: literal ha il solo parametro
 * v0 e definisce {x in sort | literal(x)}. left=0 indica un posto non legato
 * a una comprensione. I termini sono condivisi nel deposito della ricerca. */
typedef struct { SpLiteral literal; int sort; } SpProperty;

/* Una formula con quantificatore su parti, rinviata fino alle istanze.
 * source appartiene all'albero del parser; name e il suo nome nella NNF,
 * positive la polarita e every l'ammissibilita delle istanze universali.
 * binding ha slot_count celle, property declared_symbols celle; universals
 * ha universal parametri. Le copie appartengono all'arena persistente. */
typedef struct {
    const Sentence *source;
    SpLiteral name;
    int positive, every, universal;
    const int *binding, *universals;
    const SpProperty *property;
} SpSchema;

/* Un'istanza universale eseguita nella ricerca: schema identifica la
 * formula, property la comprensione canonica. first..past delimita tutte
 * le clausole ricostruite da quel comando nel certificato, incluse quelle
 * ridondanti. complete distingue il comando intero da un prefisso terminale;
 * symbol_first..symbol_past delimita i simboli freschi introdotti dal corpo.
 * Il deposito della ricerca possiede la voce e i suoi termini. */
typedef struct {
    int schema, first, past, complete;
    int symbol_first, symbol_past;
    SpLiteral property;
} SpExpansion;

/* Un comando che introduce simboli dopo la clausificazione iniziale.
 * kind e COMPONENT o COMPREHEND; index individua la voce corrispondente.
 * L'ordine posseduto dal vettore e quello della firma del certificato. */
typedef struct { SpRule kind; int index; } SpIntroduction;

/* Una coppia di termini ancora da unificare o confrontare. Gli elementi
 * della pila sono valori: una crescita non lascia puntatori pendenti. */
typedef struct { int a, b; } SpPair;

/* Un bilancio delle occorrenze per la condizione sulle variabili di KBO:
 * variable e un nome, balance e occorrenze nel primo meno nel secondo. */
typedef struct { int variable; long long balance; } SpBalance;

/* Stato posseduto da una ricerca. I suffissi _cap sono capacita sullo heap;
 * i contatori delimitano le celle valide. term/argument/hash condividono i
 * termini, symbol i simboli, clause le deduzioni; heap sceglie il peso e
 * age scorre gli indici per eta. input_symbol/original_symbol traducono i
 * simboli del parser nell'ordine dell'intestazione e viceversa; inputs conta
 * le dichiarazioni effettivamente emesse. binding e universals servono al parsing
 * dell'albero, non a interpretare un modello finito.
 * variables numera gli universali introdotti, universal conta quelli attivi;
 * initial delimita le clausole iniziali, empty e il posto del vuoto o -1.
 * unsupported segnala un nodo fuori dal primo ordine. rounds conta le scelte.
 *
 * sub e la sostituzione dell'unificazione; match e quella del confronto a
 * senso unico. todo/occurs sono pile iterative, trail permette di tornare
 * indietro nella sussunzione. path/path_count descrivono il cammino al punto
 * di superposizione. sub_count/match_count delimitano le mappe; trails,
 * todos, occurrences e balances contano le rispettive celle valide.
 * balance serve solo a KBO. storage possiede
 * clausole e certificati, scratch i temporanei riusati. bytes/work contano
 * memoria reale e visite; limited significa soltanto ricerca incompleta. */
typedef struct {
    int terms, args, symbols, clauses, variables, universal, heap_count, age;
    int initial, empty, limited, unsupported, inputs;
    unsigned long long work, rounds;
    size_t bytes;
    SpTerm *term;
    int *argument, *hash, *binding, *universals, *heap;
    int *input_symbol, *original_symbol;
    SpSymbol *symbol;
    SpClause *clause;
    int *sub, *match, *trail, *occurs, *path;
    int path_count;
    SpPair *todo;
    SpBalance *balance;
    size_t term_cap, argument_cap, hash_cap, binding_cap, universal_cap, heap_cap;
    size_t input_cap, original_cap;
    size_t symbol_cap, clause_cap, sub_cap, match_cap, trail_cap, occurs_cap, todo_cap, balance_cap, path_cap;
    int sub_count, match_count, trails, todos, occurrences, balances;
    SpSine sine;                 /* incidenze immutabili delle clausole iniziali */
    unsigned long long quota;    /* fine della quota di lavoro, zero per il budget globale */
    clock_t started, cpu_quota;  /* inizio e durata massima CPU del tentativo; zero senza timer */
    int resumable;              /* limited dipende dalla quota locale, non da memoria o budget globale */
    unsigned age_interval;      /* una scelta per eta ogni age_interval turni; zero mantiene cinque */
    int strategy;               /* zero diretto, 1/2 SInE, 3 AVATAR, 4 tutte le ipotesi */
    SpComponent *component;     /* componenti possedute, identificate anche nei simboli */
    int components;
    size_t component_cap;
    SatState sat;              /* SAT delle componenti, con budget condivisi */
    int avatar;                /* abilita la gestione dei rami SAT in questo tentativo */
    int avatar_dirty;          /* nuove componenti o clausole booleane richiedono un nuovo modello */
    int split_cursor, sat_cursor;/* primi indici di clausole ancora da suddividere o inviare al SAT */
    int replaying;             /* conserva i passi RUP senza euristiche o reinvio al SAT */
    unsigned sat_models;       /* modelli SAT effettivamente controllati, per la diagnostica */
    int *sat_proof;            /* clausola FO piu uno per ciascuna clausola SAT; zero richiede replay */
    size_t sat_proof_cap;
    signed char *rup_value;    /* assegnazioni temporanee del replay, indicizzate per componente */
    int *rup_reason, *rup_trail;/* ragioni FO piu uno e ordine delle propagazioni; zero e un'assunzione */
    size_t rup_value_cap, rup_reason_cap, rup_trail_cap;
    SpProperty *property;       /* parti definite, indicizzate per simbolo originale del parser */
    size_t property_cap;
    SpSchema *schema;           /* formule quantificate astratte, possedute dalla ricerca */
    SpExpansion *expansion;     /* gruppi di clausole delle istanze, in ordine cronologico */
    int schemas, expansions;
    size_t schema_cap, expansion_cap;
    SpIntroduction *introduction;/* ordine comune dei nomi SAT e delle istanze */
    int introductions;
    size_t introduction_cap;
    int comprehension;          /* abilita le istanze nei tentativi AVATAR e ordinario finale */
    int forward;                /* clausificazione direzionale in forma normale negativa */
    int emitting;               /* espansione piu uno durante la sua clausificazione, zero altrimenti */
    int seed_schema;            /* prossima formula a cui proporre le parti vuota e intera */
    int eliminate_expansion;    /* prossima istanza da semplificare per eliminazione booleana */
    int eliminate_symbol;       /* prossimo simbolo nell'intervallo dell'istanza corrente */
    int *unit;                  /* clausole unitarie disponibili, anche universalmente quantificate */
    int units, unit_cursor;     /* numero di unitarie e prossimo indice da semplificare */
    size_t unit_cap;
    SpArena storage, scratch;
} SpState;

/* Byte ancora disponibili a entrambi i motori. La sottrazione separata
 * evita overflow anche quando un limite viene ridotto fra due tentativi. */
static size_t sp_memory_left(const SpState *s) {
    if (s->bytes > saturation_memory_limit || s->sat.bytes > saturation_memory_limit - s->bytes) return 0;
    return saturation_memory_limit - s->bytes - s->sat.bytes;
}

/* Registra lavoro effettivo prima di visitare un nodo o tentare un passo.
 * Le quote locali interrompono con le stesse cautele di quelle globali,
 * ma il portafoglio puo riprendere lo stato. Il tempo CPU guida soltanto
 * la ricerca: non decide alcuna proposizione matematica. */
static int sp_visit(SpState *s) {
    if (s->limited || s->unsupported) return 0;
    if (s->work >= saturation_work_limit) { s->limited = 1; return 0; }
    if (s->quota && s->work >= s->quota) { s->limited = s->resumable = 1; return 0; }
    if (s->cpu_quota && s->work % 1024 == 0) {
        clock_t current = clock();
        if (s->started != (clock_t)-1 && current != (clock_t)-1 && current >= s->started && current - s->started >= s->cpu_quota) {
            s->limited = s->resumable = 1; return 0;
        }
    }
    s->work++;
    return 1;
}

/* Cresce un deposito, senza perdere i vecchi dati e contabilizzando i byte
 * effettivamente allocati. Non usa il fallimento globale delle altre
 * strategie: una ricerca interrotta puo lasciare spazio a un'altra. */
static int sp_reserve(SpState *s, void **data, size_t *capacity, size_t need, size_t unit) {
    if (s->limited || s->unsupported) return 0;
    if (need <= *capacity) return 1;
    size_t count = *capacity ? *capacity : 16;
    while (count < need) {
        if (count > (size_t)-1 / 2) { count = need; break; }
        count *= 2;
    }
    if (count > (size_t)-1 / unit || (count - *capacity) * unit > sp_memory_left(s)) { s->limited = 1; return 0; }
    void *next = realloc(*data, count * unit);
    if (!next) { s->limited = 1; return 0; }
    memset((unsigned char *)next + *capacity * unit, 0, (count - *capacity) * unit);
    s->bytes += (count - *capacity) * unit;
    *data = next; *capacity = count;
    return 1;
}

/* Prende memoria stabile, allineata, da un'arena della ricerca. Il budget
 * comprende i blocchi interi e i loro metadati, anche se non ancora pieni. */
static void *sp_allocate(SpState *s, SpArena *a, size_t count, size_t unit) {
    if (!count || s->limited || s->unsupported) return NULL;
    if (count > ((size_t)-1 - 15) / unit) { s->limited = 1; return NULL; }
    size_t need = (count * unit + 15) & ~(size_t)15;
    SpBlock *b = a->current;
    while (b && need > b->capacity - b->used) b = b->next;
    if (!b) {
        size_t capacity = need > 16384 ? need : 16384;
        if (capacity > (size_t)-1 - sizeof *b || sizeof *b + capacity > sp_memory_left(s)) { s->limited = 1; return NULL; }
        b = malloc(sizeof *b + capacity);
        if (!b) { s->limited = 1; return NULL; }
        *b = (SpBlock){.capacity=capacity};
        if (!a->first) a->first = b;
        else {
            SpBlock *last = a->current ? a->current : a->first;
            while (last->next) last = last->next;
            last->next = b;
        }
        s->bytes += sizeof *b + capacity;
    }
    a->current = b;
    void *data = b->data + b->used; b->used += need;
    return data;
}

/* Ricomincia i temporanei tra due inferenze. Nessun termine o clausola
 * conservato puo possedere un puntatore a quest'arena. */
static void sp_scratch_reset(SpState *s) {
    for (SpBlock *b = s->scratch.first; b; b = b->next) b->used = 0;
    s->scratch.current = s->scratch.first;
}

/* Libera tutto lo stato, anche dopo un'allocazione incompleta. */
static void sp_clear(SpState *s) {
    free(s->term); free(s->argument); free(s->hash); free(s->binding); free(s->universals);
    free(s->input_symbol); free(s->original_symbol);
    free(s->heap); free(s->symbol); free(s->clause); free(s->sub); free(s->match);
    free(s->trail); free(s->occurs); free(s->todo); free(s->balance); free(s->path);
    free(s->component); free(s->sat_proof); free(s->rup_value); free(s->rup_reason); free(s->rup_trail);
    free(s->property); free(s->schema); free(s->expansion);
    free(s->introduction);
    free(s->unit);
    sat_clear(&s->sat);
    SpArena *arenas[2] = {&s->storage, &s->scratch};
    for (int i = 0; i < 2; i++) for (SpBlock *b = arenas[i]->first; b;) {
        SpBlock *next = b->next; free(b); b = next;
    }
    memset(s, 0, sizeof *s);
}

/* Introduce un simbolo nel medesimo ordine dichiarativo del protocollo. */
static int sp_symbol(SpState *s, int arity, int predicate) {
    if (s->symbols == INT_MAX || !sp_reserve(s, (void **)&s->symbol, &s->symbol_cap, (size_t)s->symbols + 1, sizeof *s->symbol)) {
        s->limited = 1; return 0;
    }
    int id = s->symbols++;
    s->symbol[id] = (SpSymbol){.arity=arity, .predicate=predicate};
    return id;
}

/* Hash dei figli gia condivisi. Una collisione richiede comunque il
 * confronto esatto del simbolo e dell'intero vettore degli argomenti. */
static unsigned long long sp_term_hash(int symbol, const int *args, int count) {
    unsigned long long h = 1469598103934665603ULL ^ (unsigned)symbol;
    for (int i = 0; i < count; i++) h = (h ^ (unsigned)args[i]) * 1099511628211ULL;
    return h;
}

/* Peso di un riferimento: le variabili pesano uno, zero non e un termine. */
static unsigned long long sp_term_weight(const SpState *s, int t) {
    return t < 0 ? 1 : t ? s->term[t].weight : 0;
}

/* Condivide una costruzione finita. Il vettore input non deve puntare
 * dentro argument, che puo spostarsi; i chiamanti usano frame o scratch. */
static int sp_term(SpState *s, int symbol, const int *args) {
    if (!sp_visit(s)) return 0;
    int count = s->symbol[symbol].arity;
    if (!s->hash_cap || (size_t)s->terms + 1 >= s->hash_cap / 2) {
        size_t old = s->hash_cap;
        if (old > (size_t)-1 / 2 || !sp_reserve(s, (void **)&s->hash, &s->hash_cap, old ? 2 * old : 32, sizeof *s->hash)) {
            s->limited = 1; return 0;
        }
        memset(s->hash, 0, s->hash_cap * sizeof *s->hash);
        for (int id = 1; id <= s->terms; id++) {
            SpTerm t = s->term[id];
            size_t k = sp_term_hash(t.symbol, t.count ? s->argument + t.first : NULL, t.count) % s->hash_cap;
            while (s->hash[k]) k = (k + 1) % s->hash_cap;
            s->hash[k] = id;
        }
    }
    size_t h = sp_term_hash(symbol, args, count) % s->hash_cap;
    for (; s->hash[h]; h = (h + 1) % s->hash_cap) {
        if (!sp_visit(s)) return 0;
        int id = s->hash[h]; SpTerm t = s->term[id];
        if (t.symbol == symbol && (!count || memcmp(s->argument + t.first, args, (size_t)count * sizeof *args) == 0)) return id;
    }
    if (s->terms == INT_MAX || count > INT_MAX - s->args) { s->limited = 1; return 0; }
    if (!sp_reserve(s, (void **)&s->term, &s->term_cap, (size_t)s->terms + 2, sizeof *s->term) ||
        !sp_reserve(s, (void **)&s->argument, &s->argument_cap, (size_t)s->args + (size_t)count, sizeof *s->argument)) return 0;
    unsigned long long weight = 1;
    for (int i = 0; i < count; i++) {
        unsigned long long w = sp_term_weight(s, args[i]);
        if (w > ULLONG_MAX - weight) { s->limited = 1; return 0; }
        weight += w;
    }
    int id = ++s->terms;
    s->term[id] = (SpTerm){symbol, s->args, count, weight};
    if (count) memcpy(s->argument + s->args, args, (size_t)count * sizeof *args);
    s->args += count; s->hash[h] = id;
    return id;
}

/* Segue le sostituzioni dell'unificazione, che l'occurs-check tiene acicliche. */
static int sp_deref(const SpState *s, int t) {
    while (t < 0 && -1 - t < s->sub_count && s->sub[-1 - t]) t = s->sub[-1 - t];
    return t;
}

/* Aggiunge un confronto alla pila iterativa condivisa dalle operazioni di
 * unificazione e matching; il chiamante azzera todos prima di usarla. */
static int sp_pair_push(SpState *s, int a, int b) {
    if (s->todos == INT_MAX || !sp_reserve(s, (void **)&s->todo, &s->todo_cap, (size_t)s->todos + 1, sizeof *s->todo)) {
        s->limited = 1; return 0;
    }
    s->todo[s->todos++] = (SpPair){a, b};
    return 1;
}

/* Cerca una variabile in un termine dereferenziato, senza usare la pila C.
 * Se x compare in t, x=t richiederebbe un termine infinito e va rifiutata. */
static int sp_occurs(SpState *s, int variable, int term) {
    s->occurrences = 0;
    if (!sp_reserve(s, (void **)&s->occurs, &s->occurs_cap, 1, sizeof *s->occurs)) return 1;
    s->occurs[s->occurrences++] = term;
    while (s->occurrences && sp_visit(s)) {
        int t = sp_deref(s, s->occurs[--s->occurrences]);
        if (t == variable) return 1;
        if (t <= 0) continue;
        SpTerm n = s->term[t];
        if (n.count > INT_MAX - s->occurrences ||
            !sp_reserve(s, (void **)&s->occurs, &s->occurs_cap, (size_t)s->occurrences + (size_t)n.count, sizeof *s->occurs)) {
            s->limited = 1; return 1;
        }
        for (int i = 0; i < n.count; i++) s->occurs[s->occurrences++] = s->argument[n.first + i];
    }
    return s->limited;
}

/* Unificazione di Robinson con occurs-check. Il contesto sub gia presente
 * si estende; un fallimento lo lascia sporco, e il chiamante lo reinizializza
 * prima di un altro tentativo. Nessuna equazione sui reali entra qui. */
static int sp_unify(SpState *s, int left, int right) {
    s->todos = 0;
    sp_pair_push(s, left, right);
    while (s->todos && sp_visit(s)) {
        SpPair pair = s->todo[--s->todos];
        int a = sp_deref(s, pair.a), b = sp_deref(s, pair.b);
        if (a == b) continue;
        if (a < 0 || b < 0) {
            if (a >= 0) { int t = a; a = b; b = t; }
            if (-1 - a >= s->sub_count || sp_occurs(s, a, b)) return 0;
            s->sub[-1 - a] = b;
        } else {
            if (!a || !b || s->term[a].symbol != s->term[b].symbol) return 0;
            SpTerm x = s->term[a], y = s->term[b];
            for (int i = 0; i < x.count; i++) sp_pair_push(s, s->argument[x.first + i], s->argument[y.first + i]);
        }
    }
    return !s->limited && !s->unsupported;
}

/* Inizia un'unificazione con i nomi dei due genitori gia separati. */
static int sp_unify_start(SpState *s, int count) {
    s->sub_count = count;
    if (!sp_reserve(s, (void **)&s->sub, &s->sub_cap, (size_t)count, sizeof *s->sub)) return 0;
    if (count) memset(s->sub, 0, (size_t)count * sizeof *s->sub);
    return 1;
}

/* Applica una sostituzione risolta ai termini del genitore traslato di
 * offset. Gli zeri della mappa lasciano i nomi liberi; le immagini di sub
 * sono dereferenziate ricorsivamente solo quando recursive vale uno. */
static int sp_apply(SpState *s, int t, int offset, const int *sub, int count, int recursive) {
    if (!t || !sp_visit(s)) return 0;
    if (t < 0) {
        long long v = -1LL - t + offset;
        if (v >= INT_MAX) { s->limited = 1; return 0; }
        if (v < count && sub[v]) return recursive ? sp_apply(s, sub[v], 0, sub, count, 1) : sub[v];
        return -(int)v - 1;
    }
    SpTerm n = s->term[t];
    int *args = sp_allocate(s, &s->scratch, (size_t)n.count, sizeof *args);
    if (n.count && !args) return 0;
    for (int i = 0; i < n.count; i++) args[i] = sp_apply(s, s->argument[n.first + i], offset, sub, count, recursive);
    return sp_term(s, n.symbol, args);
}

/* Confronto a senso unico: solo le variabili dello schema possono cambiare.
 * I nomi del termine bersaglio sono traslati e quindi non possono essere
 * scambiati con quelli dello schema. trail conserva i nuovi legami. */
static int sp_match(SpState *s, int pattern, int target) {
    s->todos = 0;
    sp_pair_push(s, pattern, target);
    while (s->todos && sp_visit(s)) {
        SpPair p = s->todo[--s->todos];
        if (p.a == p.b) continue;
        if (p.a < 0) {
            int v = -p.a - 1;
            if (v >= s->match_count) return 0;
            if (s->match[v]) { if (s->match[v] != p.b) return 0; }
            else {
                if (!sp_reserve(s, (void **)&s->trail, &s->trail_cap, (size_t)s->trails + 1, sizeof *s->trail)) return 0;
                s->match[v] = p.b; s->trail[s->trails++] = v;
            }
        } else {
            if (!p.a || p.b <= 0 || s->term[p.a].symbol != s->term[p.b].symbol) return 0;
            SpTerm a = s->term[p.a], b = s->term[p.b];
            for (int i = 0; i < a.count; i++) sp_pair_push(s, s->argument[a.first + i], s->argument[b.first + i]);
        }
    }
    return !s->limited;
}

/* Ricomincia un confronto di schemi, oppure torna al punto segnato prima
 * di provare un diverso abbinamento di letterali. */
static int sp_match_start(SpState *s, int count) {
    s->match_count = count; s->trails = 0;
    if (!sp_reserve(s, (void **)&s->match, &s->match_cap, (size_t)count, sizeof *s->match)) return 0;
    if (count) memset(s->match, 0, (size_t)count * sizeof *s->match);
    return 1;
}

/* Cancella soltanto i legami aggiunti dopo mark. */
static void sp_match_back(SpState *s, int mark) {
    while (s->trails > mark) s->match[s->trail[--s->trails]] = 0;
}

/* Accumula il multinsieme delle variabili di t col segno dato. La visita
 * conta occorrenze, non soli nodi del DAG: f(x,x) contiene x due volte. */
static void sp_balance(SpState *s, int t, int sign) {
    if (!t || !sp_visit(s)) return;
    if (t < 0) {
        int i = 0;
        while (i < s->balances && s->balance[i].variable != t) i++;
        if (i == s->balances) {
            if (!sp_reserve(s, (void **)&s->balance, &s->balance_cap, (size_t)i + 1, sizeof *s->balance)) return;
            s->balance[s->balances++] = (SpBalance){t, 0};
        }
        if ((sign > 0 && s->balance[i].balance == LLONG_MAX) ||
            (sign < 0 && s->balance[i].balance == LLONG_MIN)) { s->limited = 1; return; }
        s->balance[i].balance += sign;
        return;
    }
    SpTerm n = s->term[t];
    for (int i = 0; i < n.count; i++) sp_balance(s, s->argument[n.first + i], sign);
}

/* KBO stretto, con peso uno per ogni simbolo e variabile e precedenza
 * crescente dei simboli. Prima si impone occ_s(x)>=occ_t(x) per ogni x;
 * poi decide il peso, a parita la precedenza o il primo figlio diverso.
 * I pesi positivi e la condizione sulle variabili rendono l'ordine ben
 * fondato e stabile per sostituzioni: riscrivere nel verso maggiore->minore
 * non puo creare un ciclo. Termini aperti possono restare incomparabili. */
static int sp_greater(SpState *s, int a, int b) {
    if (a == b || !a || !b || !sp_visit(s)) return 0;
    s->balances = 0; sp_balance(s, a, 1); sp_balance(s, b, -1);
    for (int i = 0; i < s->balances; i++) if (s->balance[i].balance < 0) return 0;
    unsigned long long x = sp_term_weight(s, a), y = sp_term_weight(s, b);
    if (x != y) return x > y;
    if (a < 0 || b < 0) return 0;
    SpTerm u = s->term[a], v = s->term[b];
    if (u.symbol != v.symbol) return u.symbol > v.symbol;
    for (int i = 0; i < u.count; i++) {
        int l = s->argument[u.first + i], r = s->argument[v.first + i];
        if (l != r) return sp_greater(s, l, r);
    }
    return 0;
}

/* Mappa temporanea della normalizzazione: old e il riferimento negativo
 * originale, fresh quello assegnato per prima occorrenza. Le celle sono
 * nello scratch e nessuna clausola conservata ne possiede il puntatore. */
typedef struct { int old, fresh; } SpName;

/* Un contesto di rinomina, condiviso solo dalla ricorsione corrente.
 * count/capacity delimitano i nomi, name puo cambiare indirizzo crescendo. */
typedef struct { int count; size_t capacity; SpName *name; } SpNames;

/* Rinomina le variabili per prima occorrenza, condividendo nuovamente i
 * termini costruiti. Non usa il valore numerico dei nomi come capacita. */
static int sp_rename(SpState *s, int t, SpNames *names) {
    if (!t || !sp_visit(s)) return 0;
    if (t < 0) {
        for (int i = 0; i < names->count; i++) if (names->name[i].old == t) return names->name[i].fresh;
        if ((size_t)names->count == names->capacity) {
            size_t cap = names->capacity ? 2 * names->capacity : 16;
            SpName *next = sp_allocate(s, &s->scratch, cap, sizeof *next);
            if (!next) return 0;
            if (names->count) memcpy(next, names->name, (size_t)names->count * sizeof *next);
            names->name = next; names->capacity = cap;
        }
        if (names->count == INT_MAX) { s->limited = 1; return 0; }
        int fresh = -1 - names->count;
        names->name[names->count++] = (SpName){t, fresh};
        return fresh;
    }
    SpTerm n = s->term[t];
    int *args = sp_allocate(s, &s->scratch, (size_t)n.count, sizeof *args);
    if (n.count && !args) return 0;
    for (int i = 0; i < n.count; i++) args[i] = sp_rename(s, s->argument[n.first + i], names);
    return sp_term(s, n.symbol, args);
}

/* Stesso atomo, ammettendo la simmetria dell'uguaglianza. Il segno viene
 * confrontato dal chiamante, cosi si riconoscono anche i complementari. */
static int sp_same_atom(SpLiteral a, SpLiteral b) {
    return (a.left == b.left && a.right == b.right) ||
           (a.right && b.right && a.left == b.right && a.right == b.left);
}

/* Copia e normalizza: falso si elimina, i duplicati identici si contraggono.
 * L'ordine dei letterali e il verso delle uguaglianze restano quelli della
 * regola, perche sono dati del certificato. La firma usa solo simboli che
 * una sostituzione non puo cambiare, quindi non scarta una sussunzione vera. */
static SpClause sp_normal(SpState *s, const SpLiteral *literal, int count) {
    SpClause c = {0}; SpNames names = {0};
    SpLiteral *out = sp_allocate(s, &s->scratch, (size_t)count, sizeof *out);
    if (count && !out) return c;
    for (int i = 0; i < count && sp_visit(s); i++) {
        SpLiteral l = literal[i];
        if (!l.left && l.negative) continue;
        l.left = sp_rename(s, l.left, &names); l.right = sp_rename(s, l.right, &names);
        /* Una quota puo fermare soltanto il secondo membro di t=t:
         * quel prefisso non e un predicato e non va indicizzato come tale. */
        if (s->limited || s->unsupported) break;
        int repeated = 0;
        for (int j = 0; j < c.count; j++)
            repeated |= out[j].left == l.left && out[j].right == l.right && out[j].negative == l.negative;
        if (repeated) continue;
        out[c.count++] = l;
        unsigned key = !l.left ? 0 : l.right ? 2u + (unsigned)l.negative
                       : 4u + 2u * (unsigned)s->term[l.left].symbol + (unsigned)l.negative;
        c.signature |= 1ULL << (key % 64);
        unsigned long long weight = sp_term_weight(s, l.left), right = sp_term_weight(s, l.right);
        if (right > ULLONG_MAX - weight) { s->limited = 1; return c; }
        weight += right;
        if (weight == ULLONG_MAX || weight + 1 > ULLONG_MAX - c.weight) { s->limited = 1; return c; }
        c.weight += weight + 1;
    }
    c.literal = out; c.variables = names.count;
    return c;
}

/* Una tautologia e vera per ogni interpretazione: vero, t=t, oppure due
 * atomi identici con segni opposti. Non basta che siano unificabili. */
static int sp_tautology(const SpClause *c) {
    for (int i = 0; i < c->count; i++) {
        SpLiteral l = c->literal[i];
        if ((!l.left || (l.right && l.left == l.right)) && !l.negative) return 1;
        for (int j = 0; j < i; j++)
            if (l.negative != c->literal[j].negative && sp_same_atom(l, c->literal[j])) return 1;
    }
    return 0;
}

/* Trasla e istanzia i letterali di una clausola, senza modificarla. Le
 * immagini devono gia essere simultanee, come quelle scritte al checker. */
static SpLiteral *sp_instance(SpState *s, SpClause c, int offset, const int *sub, int count, int recursive) {
    SpLiteral *literal = sp_allocate(s, &s->scratch, (size_t)c.count, sizeof *literal);
    if (c.count && !literal) return NULL;
    for (int i = 0; i < c.count; i++) {
        literal[i] = c.literal[i];
        literal[i].left = sp_apply(s, literal[i].left, offset, sub, count, recursive);
        literal[i].right = sp_apply(s, literal[i].right, offset, sub, count, recursive);
    }
    return literal;
}

/* Un livello del confronto fra clausole: choice e il prossimo letterale e
 * verso da provare, mark delimita i legami presenti prima di quel livello. */
typedef struct { size_t choice; int mark; } SpMatchFrame;

/* C sussume D se esiste una sostituzione theta con C theta contenuta in D.
 * I nomi di D restano fissi e distinti da quelli di C. Un successo rende D
 * ridondante: ogni interpretazione che soddisfa C soddisfa anche D. Il
 * backtracking e iterativo e il budget conta ogni abbinamento tentato. */
static int sp_subsumes(SpState *s, SpClause c, SpClause d) {
    if (c.signature & ~d.signature) return 0;
    if (!c.count) return 1;
    if (!d.count || !sp_match_start(s, c.variables)) return 0;
    int offset = c.variables > 64 ? c.variables : 64;
    SpLiteral *target = sp_instance(s, d, offset, NULL, 0, 0);
    SpMatchFrame *frame = sp_allocate(s, &s->scratch, (size_t)c.count, sizeof *frame);
    if (!target || !frame) return 0;
    int level = 0; frame[0] = (SpMatchFrame){0};
    while (level >= 0 && sp_visit(s)) {
        SpMatchFrame *f = &frame[level];
        sp_match_back(s, f->mark);
        if (f->choice == 2 * (size_t)d.count) { level--; continue; }
        size_t choice = f->choice++;
        SpLiteral a = c.literal[level], b = target[choice / 2];
        int flip = (int)(choice % 2);
        if (a.negative != b.negative || !!a.right != !!b.right || (flip && !a.right)) continue;
        int x = flip ? b.right : b.left, y = flip ? b.left : b.right;
        if (!sp_match(s, a.left, x) || (a.right && !sp_match(s, a.right, y))) continue;
        if (++level == c.count) return 1;
        frame[level] = (SpMatchFrame){.mark=s->trails};
    }
    return 0;
}

/* Ordine della coda per peso, con eta come spareggio deterministico. */
static int sp_before(const SpState *s, int a, int b) {
    return s->clause[a].weight < s->clause[b].weight ||
           (s->clause[a].weight == s->clause[b].weight && a < b);
}

/* Aggiunge una clausola alla coda a priorita. Le voci cancellate vengono
 * scartate quando arrivano in testa, senza spostare le altre clausole. */
static void sp_enqueue(SpState *s, int id) {
    if (!sp_reserve(s, (void **)&s->heap, &s->heap_cap, (size_t)s->heap_count + 1, sizeof *s->heap)) return;
    size_t at = (size_t)s->heap_count++;
    while (at && sp_before(s, id, s->heap[(at - 1) / 2])) {
        s->heap[at] = s->heap[(at - 1) / 2]; at = (at - 1) / 2;
    }
    s->heap[at] = id;
}

/* Toglie il minimo dall'heap, anche se gia elaborato per eta o cancellato. */
static int sp_pop(SpState *s) {
    if (!s->heap_count) return -1;
    int result = s->heap[0], last = s->heap[--s->heap_count];
    size_t at = 0, count = (size_t)s->heap_count;
    while (2 * at + 1 < count) {
        size_t child = 2 * at + 1;
        if (child + 1 < count && sp_before(s, s->heap[child + 1], s->heap[child])) child++;
        if (!sp_before(s, s->heap[child], last)) break;
        s->heap[at] = s->heap[child]; at = child;
    }
    if (count) s->heap[at] = last;
    return result;
}

/* Una scelta per eta ogni age_interval turni, cinque di default. Con
 * risorse illimitate ogni clausola persistente viene prima o poi scelta. */
static int sp_select(SpState *s) {
    unsigned interval = s->age_interval ? s->age_interval : 5;
    if (s->rounds++ % interval == interval - 1) {
        while (s->age < s->clauses && s->clause[s->age].stage != SP_PENDING && sp_visit(s)) s->age++;
        if (s->age < s->clauses) return s->age++;
    }
    for (int id; (id = sp_pop(s)) >= 0 && sp_visit(s);)
        if (s->clause[id].stage == SP_PENDING) return id;
    return -1;
}

/* Restituisce componente piu uno per una guardia, zero per un letterale
 * ordinario. Il ruolo resta esplicito anche fra simboli di nuove istanze. */
static int sp_guard(const SpState *s, SpLiteral l) {
    if (l.right || l.left <= 0) return 0;
    int symbol = s->term[l.left].symbol;
    return s->symbol[symbol].component;
}

/* Le guardie sono disgiunti della clausola completa: la parte FO e
 * richiesta soltanto quando tutte sono false. Le clausole solo booleane
 * vanno al SAT, anche se il modello corrente gia le soddisfa. */
static SpStage sp_available(const SpState *s, SpClause c) {
    if (!s->avatar || !c.count) return SP_PENDING;
    int ordinary = 0, active = 1;
    for (int i = 0; i < c.count; i++) {
        int guard = sp_guard(s, c.literal[i]);
        if (!guard) ordinary = 1;
        else if (s->component[guard - 1].value * (c.literal[i].negative ? -1 : 1) >= 0) active = 0;
    }
    return !ordinary ? SP_BOOLEAN : active ? SP_PENDING : SP_LOCKED;
}

/* Salva una clausola e, se derivata, la sua sostituzione. I temporanei sono
 * copiati prima di tornare al chiamante. Le clausole iniziali conservano
 * sempre il proprio indice, comprese quelle ridondanti; il checker le
 * ricostruisce senza conoscere le euristiche della ricerca. replaced e il
 * bersaglio di una riscrittura, oppure -1: non puo sussumere la propria
 * sostituta per poi essere cancellato senza conservarne nessuna.
 * Le definizioni mantengono anch'esse un indice; il replay conserva ogni
 * risolvente. Gruppi, posizioni e sostituzioni vengono copiati nell'arena. */
static int sp_keep(SpState *s, const SpLiteral *literal, int count, SpStep step, int replaced) {
    SpClause c = sp_normal(s, literal, count);
    if (s->limited || s->unsupported) return -1;
    int trivial = sp_tautology(&c), retained = step.rule == SP_INPUT || step.rule == SP_COMPONENT || step.rule == SP_COMPLEMENT || step.rule == SP_COMPREHEND;
    if (!retained && trivial) return -1;
    if (!retained && !s->replaying) for (int i = 0; i < s->clauses && sp_visit(s); i++)
        if (i != replaced && s->clause[i].stage != SP_DELETED && s->clause[i].stage != SP_HELD &&
            s->clause[i].stage != SP_LOCKED && sp_subsumes(s, s->clause[i], c)) return -1;
    if (s->clauses == INT_MAX) { s->limited = 1; return -1; }
    if (!sp_reserve(s, (void **)&s->clause, &s->clause_cap, (size_t)s->clauses + 1, sizeof *s->clause)) return -1;
    SpLiteral *saved = sp_allocate(s, &s->storage, (size_t)c.count, sizeof *saved);
    SpBinding *bindings = sp_allocate(s, &s->storage, (size_t)step.bindings, sizeof *bindings);
    if ((c.count && !saved) || (step.bindings && !bindings) || s->limited) return -1;
    if (c.count) memcpy(saved, c.literal, (size_t)c.count * sizeof *saved);
    if (step.bindings) memcpy(bindings, step.binding, (size_t)step.bindings * sizeof *bindings);
    SpGroup *groups = sp_allocate(s, &s->storage, (size_t)step.groups, sizeof *groups);
    if (step.groups && !groups) return -1;
    for (int i = 0; i < step.groups; i++) {
        groups[i] = step.group[i];
        int *indices = sp_allocate(s, &s->storage, (size_t)groups[i].count, sizeof *indices);
        if (!indices) return -1;
        memcpy(indices, groups[i].literal, (size_t)groups[i].count * sizeof *indices);
        groups[i].literal = indices;
    }
    c.literal = saved; c.step = step; c.step.binding = bindings;
    c.step.group = groups;
    c.stage = trivial ? SP_DELETED : sp_available(s, c);
    int id = s->clauses++;
    s->clause[id] = c;
    if (!c.count) s->empty = id;
    if (c.stage == SP_PENDING) sp_enqueue(s, id);
    if (s->avatar && c.stage == SP_BOOLEAN && !s->replaying) s->avatar_dirty = 1;
    if (!retained && !s->replaying && c.count) for (int i = 0; i < id && sp_visit(s); i++)
        if (s->clause[i].stage != SP_DELETED && sp_subsumes(s, c, s->clause[i])) s->clause[i].stage = SP_DELETED;
    return s->limited ? -1 : id;
}

/* Scrive una delle clausole di Tseitin, di al piu tre letterali. */
static void sp_emit(SpState *s, SpLiteral a, SpLiteral b, SpLiteral c, int count) {
    SpLiteral literal[3] = {a, b, c};
    SpStep step = {.rule=s->emitting ? SP_COMPREHEND : SP_INPUT, .p=s->emitting ? s->emitting - 1 : 0};
    sp_keep(s, literal, count, step, -1);
}

/* Il complemento di un letterale conserva il suo atomo. */
static SpLiteral sp_not(SpLiteral l) { l.negative = !l.negative; return l; }

/* Raccoglie nomi distinti in un vettore sparso nello scratch. Anche indici
 * lontani non richiedono memoria per tutte le posizioni intermedie. */
static void sp_free_variables(SpState *s, int t, SpNames *names) {
    if (!t || !sp_visit(s)) return;
    if (t < 0) { sp_rename(s, t, names); return; }
    SpTerm n = s->term[t];
    for (int i = 0; i < n.count; i++) sp_free_variables(s, s->argument[n.first + i], names);
}

/* Ordine dei nomi liberi, indipendente dall'ordine in cui sono stati letti. */
static int sp_name_order(const void *a, const void *b) {
    int x = ((const SpName *)a)->old, y = ((const SpName *)b)->old;
    return (y > x) - (y < x);
}

/* La riflessivita rende t=t vero per ogni interpretazione. Ridurre questo
 * atomo prima di nominare una sottoformula evita nomi per costanti logiche. */
static SpLiteral sp_constant_literal(SpLiteral l) {
    return l.right && l.left == l.right ? (SpLiteral){0, 0, l.negative} : l;
}

/* Introduce q(vars) equivalente ad a AND b, oppure a OR b. Le tre
 * implicazioni garantiscono entrambi i versi, anche sotto una negazione.
 * Con forward basta q=>F: i nomi interni della NNF compaiono positivamente.
 * Ogni modello di F si estende assegnando q=F, mentre q vero impone F.
 * E la trasformazione di Plaisted e Greenbaum; i membri di comprensioni
 * usati sotto negazione mantengono invece entrambi i versi.
 * I parametri sono tutte e sole le variabili libere, in ordine crescente. */
static SpLiteral sp_connect(SpState *s, SpLiteral a, SpLiteral b, int conjunction) {
    if (s->forward) { a = sp_constant_literal(a); b = sp_constant_literal(b); }
    if (!a.left) return a.negative == conjunction ? a : b;
    if (!b.left) return b.negative == conjunction ? b : a;
    SpNames names = {0};
    sp_free_variables(s, a.left, &names); sp_free_variables(s, a.right, &names);
    sp_free_variables(s, b.left, &names); sp_free_variables(s, b.right, &names);
    if (names.count) qsort(names.name, (size_t)names.count, sizeof *names.name, sp_name_order);
    int *args = sp_allocate(s, &s->scratch, (size_t)names.count, sizeof *args);
    if (names.count && !args) return (SpLiteral){0};
    for (int i = 0; i < names.count; i++) args[i] = names.name[i].old;
    SpLiteral q = {sp_term(s, sp_symbol(s, names.count, 1), args), 0, 0};
    if (conjunction) {
        sp_emit(s, sp_not(q), a, a, 2); sp_emit(s, sp_not(q), b, b, 2);
        if (!s->forward) sp_emit(s, q, sp_not(a), sp_not(b), 3);
    } else {
        if (!s->forward) { sp_emit(s, q, sp_not(a), a, 2); sp_emit(s, q, sp_not(b), b, 2); }
        sp_emit(s, sp_not(q), a, b, 3);
    }
    return q;
}

/* Legge un termine dell'albero originale nell'ambiente dei quantificatori.
 * Gli elementi legati sono slot, non nomi testuali: non puo esserci cattura. */
static int sp_input_term(SpState *s, const Elem *e) {
    if (!sp_visit(s)) return 0;
    if (e->symbol < 0) {
        if (e->slot < 0 || e->slot >= slot_count || !s->binding[e->slot]) { s->unsupported = 1; return 0; }
        return s->binding[e->slot];
    }
    if (e->symbol >= declared_symbols || s->input_symbol[e->symbol] < 0) { s->unsupported = 1; return 0; }
    int args[2];
    for (int i = 0; i < symbols[e->symbol].arity; i++) args[i] = sp_input_term(s, e->arg[i]);
    return sp_term(s, s->input_symbol[e->symbol], args);
}

/* Sostituisce tutte le occorrenze strutturali di from con to. L'immagine
 * non viene attraversata: si usa sia per astrarre un termine ground in
 * v0, sia per applicare la proprieta a un argomento senza cattura. */
static int sp_replace_term(SpState *s, int term, int from, int to) {
    if (!term || !sp_visit(s)) return 0;
    if (term == from) return to;
    if (term < 0) return term;
    SpTerm n = s->term[term];
    int *args = sp_allocate(s, &s->scratch, (size_t)n.count, sizeof *args);
    if (n.count && !args) return 0;
    for (int i = 0; i < n.count; i++) args[i] = sp_replace_term(s, s->argument[n.first + i], from, to);
    return sp_term(s, n.symbol, args);
}

/* Rinomina una formula quantificata su parti conservandone l'ambiente.
 * Il nome denota la formula nella polarita della NNF. Lasciarlo inizialmente
 * libero indebolisce i vincoli; le istanze universali verranno aggiunte
 * durante la ricerca. Le parti non diventano elementi del dominio comune. */
static SpLiteral sp_schema(SpState *s, const Sentence *n, int positive) {
    SpLiteral none = {0, 0, 1};
    if (s->schemas == INT_MAX || !sp_reserve(s, (void **)&s->schema, &s->schema_cap,
            (size_t)s->schemas + 1, sizeof *s->schema)) { s->limited = 1; return none; }
    int *binding = sp_allocate(s, &s->storage, (size_t)slot_count, sizeof *binding);
    int *universals = sp_allocate(s, &s->storage, (size_t)s->universal, sizeof *universals);
    SpProperty *property = sp_allocate(s, &s->storage, (size_t)declared_symbols, sizeof *property);
    if (s->limited) return none;
    if (slot_count) memcpy(binding, s->binding, (size_t)slot_count * sizeof *binding);
    if (s->universal) memcpy(universals, s->universals, (size_t)s->universal * sizeof *universals);
    if (declared_symbols) memcpy(property, s->property, (size_t)declared_symbols * sizeof *property);
    int symbol = sp_symbol(s, s->universal, 1);
    SpLiteral name = {sp_term(s, symbol, universals), 0, 0};
    if (!s->limited) s->schema[s->schemas++] = (SpSchema){.source=n, .name=name,
        .positive=positive, .every=(n->kind == S_FORALL_PART) == positive, .universal=s->universal,
        .binding=binding, .universals=universals, .property=property};
    return name;
}

/* L'appartenenza a una parte definita da L e D_S(t) AND L(t). Il parametro
 * v0 viene sostituito una sola volta; gli altri termini restano chiusi. */
static SpLiteral sp_property_member(SpState *s, const Elem *e) {
    SpLiteral none = {0, 0, 1};
    if (e->symbol < 0 || e->symbol >= declared_symbols || !s->property[e->symbol].literal.left) {
        s->unsupported = 1; return none;
    }
    SpProperty p = s->property[e->symbol];
    int value = sp_input_term(s, e->arg[0]);
    SpLiteral l = p.literal;
    l.left = sp_replace_term(s, l.left, -1, value); l.right = sp_replace_term(s, l.right, -1, value);
    SpLiteral domain = {sp_term(s, s->inputs + p.sort, &value), 0, 0};
    if (s->forward) l = sp_constant_literal(l);
    int forward = s->forward; s->forward = 0;
    SpLiteral member = sp_connect(s, domain, l, 1);
    s->forward = forward;
    return member;
}

/* NNF, Skolem e Tseitin sull'albero. positive indica la polarita richiesta.
 * Un quantificatore su S diventa un quantificatore del dominio comune con
 * il vincolo D_S: lo Skolem di un esiste non impone mai D_S incondizionatamente.
 * Le parti quantificate ricevono un'astrazione e successive istanze di
 * comprensione; l'equipotenza conserva le proprie strategie. */
static SpLiteral sp_formula(SpState *s, const Sentence *n, int positive) {
    SpLiteral constant = {0, 0, !positive}, a, b;
    if (!sp_visit(s)) return constant;
    switch (n->kind) {
    case S_TRUE: return constant;
    case S_EQUAL: case S_HOLDS:
        if (n->kind == S_HOLDS && n->left->symbol >= 0 && n->left->symbol < declared_symbols && symbol_bound[n->left->symbol]) {
            a = sp_property_member(s, n->left); return positive ? a : sp_not(a);
        }
        return (SpLiteral){sp_input_term(s, n->left), n->right ? sp_input_term(s, n->right) : 0, !positive};
    case S_NOT: return sp_formula(s, n->a, !positive);
    case S_AND: case S_OR: case S_IMPLIES:
        a = sp_formula(s, n->a, n->kind == S_IMPLIES ? !positive : positive);
        if (s->forward) {
            a = sp_constant_literal(a);
            if (!a.left && a.negative == ((n->kind == S_AND) == positive)) return a;
        }
        b = sp_formula(s, n->b, positive);
        return sp_connect(s, a, b, (n->kind == S_AND) == positive);
    case S_IFF:
        a = sp_formula(s, n->a, 0); b = sp_formula(s, n->b, positive);
        a = sp_connect(s, a, b, 0);
        b = sp_formula(s, n->a, 1);
        return sp_connect(s, a, sp_connect(s, b, sp_formula(s, n->b, !positive), 0), 1);
    case S_FORALL: case S_EXISTS: {
        int every = (n->kind == S_FORALL) == positive;
        if (s->variables == INT_MAX || !sp_reserve(s, (void **)&s->universals, &s->universal_cap, (size_t)s->universal + 1, sizeof *s->universals)) {
            s->limited = 1; return constant;
        }
        int value = every ? -1 - s->variables++ : sp_term(s, sp_symbol(s, s->universal, 0), s->universals);
        int saved = s->binding[n->slot]; s->binding[n->slot] = value;
        if (every) s->universals[s->universal++] = value;
        a = (SpLiteral){sp_term(s, s->inputs + slot_data[n->slot].sort, &value), 0, every};
        b = sp_formula(s, n->a, positive);
        if (every) s->universal--;
        s->binding[n->slot] = saved;
        return sp_connect(s, a, b, !every);
    }
    case S_FORALL_PART: case S_EXISTS_PART: return sp_schema(s, n, positive);
    case S_EQUIPOTENT: {
        /* 11m-e di checker.c, che spiega perché è lecito: una proposizione
         * nuova e, due funzioni nuove, e le quattro clausole "e implica che
         * le due funzioni si disfano a vicenda tra A e B"; al posto
         * dell'equipotenza, e. Stessi simboli e stesse clausole del
         * verificatore, nello stesso ordine: i numeri devono coincidere.
         * Così un'equipotenza si può usare in una refutazione, non
         * dimostrare. La saturazione di questo capitolo non arriva qui
         * (sp_supported_formula() rifiuta l'equipotenza, che ha le sue
         * strategie): ci arriva la consegna delle clausole a Vampire. */
        if (n->sides[0] != 1 || n->sides[1] != 1) { s->unsupported = 1; return constant; }
        int from = s->inputs + slot_data[n->side_slot[0][0]].sort, to = s->inputs + slot_data[n->side_slot[1][0]].sort;
        int name = sp_symbol(s, 0, 1), there = sp_symbol(s, 1, 0), back = sp_symbol(s, 1, 0);
        if (s->limited) return constant;
        int proposition = sp_term(s, name, NULL), x = -1;
        int image = sp_term(s, there, &x), returned = sp_term(s, back, &image);
        int preimage = sp_term(s, back, &x), again = sp_term(s, there, &preimage);
        SpLiteral unless = {proposition, 0, 1};
        sp_emit(s, unless, (SpLiteral){sp_term(s, from, &x), 0, 1}, (SpLiteral){sp_term(s, to, &image), 0, 0}, 3);
        sp_emit(s, unless, (SpLiteral){sp_term(s, from, &x), 0, 1}, (SpLiteral){returned, x, 0}, 3);
        sp_emit(s, unless, (SpLiteral){sp_term(s, to, &x), 0, 1}, (SpLiteral){sp_term(s, from, &preimage), 0, 0}, 3);
        sp_emit(s, unless, (SpLiteral){sp_term(s, to, &x), 0, 1}, (SpLiteral){again, x, 0}, 3);
        return (SpLiteral){proposition, 0, !positive};
    }
    default: s->unsupported = 1; return constant;
    }
}

/* Introduce un simbolo originale nella numerazione del certificato.
 * input_symbol traduce i posti del parser; original_symbol e la mappa
 * inversa, usata nelle clausole di chiusura e nel testo della prova. */
static void sp_input_symbol(SpState *s, int original) {
    if (original < 0 || original >= declared_symbols) { s->unsupported = 1; return; }
    if (s->input_symbol[original] >= 0) return;
    if (!sp_reserve(s, (void **)&s->original_symbol, &s->original_cap, (size_t)s->inputs + 1, sizeof *s->original_symbol)) return;
    int id = sp_symbol(s, symbols[original].arity, symbols[original].range == TRUTH);
    if (s->limited) return;
    s->input_symbol[original] = id; s->original_symbol[s->inputs++] = original;
}

/* Clausifica la negazione dell'enunciato e le leggi fornite. Le sole
 * funzioni dichiarate ricevono clausole di chiusura sui domini; per
 * predicati e simboli di Skolem non si inventano vincoli ulteriori. */
static int sp_prepare(SpState *s, const Sentence *root, const Sentence *const *laws, int count) {
    s->empty = -1;
    for (int i = 0; i < declared_symbols; i++) if (symbol_bound[i]) s->forward = 1;
    if (!sp_reserve(s, (void **)&s->binding, &s->binding_cap, (size_t)slot_count, sizeof *s->binding)) return 0;
    if (!sp_reserve(s, (void **)&s->property, &s->property_cap, (size_t)declared_symbols, sizeof *s->property)) return 0;
    if (!sp_reserve(s, (void **)&s->input_symbol, &s->input_cap, (size_t)declared_symbols, sizeof *s->input_symbol)) return 0;
    for (int i = 0; i < declared_symbols; i++) s->input_symbol[i] = -1;
    /* Warning: questo ordine e quello scritto da cert_abstract_head: prima
     * i simboli impliciti nelle sort, poi le dichiarazioni esplicite. Il
     * parser puo aver incontrato una funzione prima di un insieme di parti. */
    for (int i = 0; i < sort_count; i++) {
        if (sort_data[i].kind == SORT_NUMBERS) {
            for (int f = 0; f < declared_symbols; f++)
                if (symbols[f].name >= NUMERAL_NAMES && symbols[f].range == i) sp_input_symbol(s, f);
        } else if (sort_data[i].kind != SORT_PLAIN) sp_input_symbol(s, sort_data[i].symbol);
    }
    for (int i = 0; i < declared_symbols; i++)
        if (!symbol_fixed(i) && !symbol_bound[i]) sp_input_symbol(s, i);
    for (int i = 0; i < sort_count; i++) sp_symbol(s, 1, 1);
    for (int i = 0; i < s->inputs && sp_visit(s); i++) {
        const Symbol *f = &symbols[s->original_symbol[i]];
        if (f->range == TRUTH) continue;
        int vars[2] = {-1, -2}, value = sp_term(s, i, vars);
        SpLiteral c[3];
        c[0] = (SpLiteral){sp_term(s, s->inputs + f->range, &value), 0, 0};
        for (int j = 0; j < f->arity; j++) c[j + 1] = (SpLiteral){sp_term(s, s->inputs + f->domain[j], &vars[j]), 0, 1};
        sp_keep(s, c, f->arity + 1, (SpStep){.rule=SP_INPUT}, -1);
    }
    SpLiteral l = sp_formula(s, root, 0); sp_emit(s, l, l, l, 1);
    for (int i = 0; i < count && sp_visit(s); i++) { l = sp_formula(s, laws[i], 1); sp_emit(s, l, l, l, 1); }
    s->initial = s->clauses;
    return !s->limited && !s->unsupported;
}

/* Confronta chiavi canoniche senza permutare i letterali: lo stesso ordine
 * verra scritto nel certificato e ricostruito indipendentemente. */
static int sp_component_equal(SpState *s, SpClause a, SpClause b) {
    if (a.count != b.count) return 0;
    for (int i = 0; i < a.count && sp_visit(s); i++)
        if (a.literal[i].left != b.literal[i].left || a.literal[i].right != b.literal[i].right || a.literal[i].negative != b.literal[i].negative) return 0;
    return !s->limited;
}

/* Condivide una chiusura universale e conserva le sue definizioni.
 * Solo un singolo letterale ground puo usare il complemento della stessa
 * proposizione. Una quota puo lasciare una definizione incompleta, ma non
 * permette di cancellare il genitore dello split che la richiedeva. */
static int sp_component(SpState *s, SpClause key) {
    for (int i = 0; i < s->components && sp_visit(s); i++)
        if (sp_component_equal(s, key, s->component[i].key)) return i;
    if (s->limited) return -1;
    if (s->components == INT_MAX || key.count == INT_MAX ||
        !sp_reserve(s, (void **)&s->component, &s->component_cap, (size_t)s->components + 1, sizeof *s->component)) {
        s->limited = 1; return -1;
    }
    if (s->introductions == INT_MAX || !sp_reserve(s, (void **)&s->introduction, &s->introduction_cap,
            (size_t)s->introductions + 1, sizeof *s->introduction)) { s->limited = 1; return -1; }
    SpLiteral *copy = sp_allocate(s, &s->storage, (size_t)key.count, sizeof *copy);
    if (!copy) return -1;
    memcpy(copy, key.literal, (size_t)key.count * sizeof *copy); key.literal = copy;
    int symbol = sp_symbol(s, 0, 1);
    if (s->limited) return -1;
    int id = s->components++;
    s->component[id] = (SpComponent){.key=key, .symbol=symbol, .forward=-1, .reverse=-1};
    s->symbol[symbol].component = id + 1;
    s->introduction[s->introductions++] = (SpIntroduction){SP_COMPONENT, id};
    int atom = sp_term(s, symbol, NULL);
    s->component[id].atom = atom; s->avatar_dirty = 1;
    SpLiteral *definition = sp_allocate(s, &s->scratch, (size_t)key.count + 1, sizeof *definition);
    if (!definition || s->limited) return -1;
    memcpy(definition, copy, (size_t)key.count * sizeof *definition);
    definition[key.count] = (SpLiteral){atom, 0, 1};
    s->component[id].forward = sp_keep(s, definition, key.count + 1, (SpStep){.rule=SP_COMPONENT, .p=id}, -1);
    if (!key.variables && key.count == 1 && !s->limited) {
        SpLiteral opposite[] = {sp_not(copy[0]), {atom, 0, 0}};
        s->component[id].reverse = sp_keep(s, opposite, 2, (SpStep){.rule=SP_COMPLEMENT, .p=id}, -1);
    }
    return s->limited ? -1 : id;
}

/* Radice di una classe di letterali connessi da variabili condivise.
 * La compressione dei cammini non cambia la partizione matematica. */
static int sp_group_root(SpState *s, int *parent, int i) {
    int root = i;
    while (parent[root] != root && sp_visit(s)) root = parent[root];
    while (parent[i] != i && sp_visit(s)) { int next = parent[i]; parent[i] = root; i = next; }
    return root;
}

/* Collega due letterali quando vi compare la stessa variabile. owner ha
 * una cella per nome normalizzato e vale -1 prima della prima occorrenza. */
static void sp_group_variables(SpState *s, int term, int literal, int *parent, int *owner) {
    if (!term || !sp_visit(s)) return;
    if (term < 0) {
        int v = -term - 1;
        if (owner[v] < 0) owner[v] = literal;
        else {
            int a = sp_group_root(s, parent, literal), b = sp_group_root(s, parent, owner[v]);
            parent[b] = a;
        }
        return;
    }
    SpTerm n = s->term[term];
    for (int i = 0; i < n.count; i++) sp_group_variables(s, s->argument[n.first + i], literal, parent, owner);
}

/* Trova le componenti connesse dei letterali ordinari e scrive uno split
 * controllabile. I letterali ground sono componenti singole; le guardie
 * gia presenti non partecipano alla connessione e restano nel risultato.
 * Le definizioni non vengono suddivise di nuovo. Ritorna senza cambiare
 * il genitore quando rimane una sola componente con variabili. */
static void sp_split(SpState *s, int p) {
    SpClause a = s->clause[p];
    if (!a.count || a.stage == SP_DELETED || a.stage == SP_HELD || a.stage == SP_BOOLEAN ||
        a.step.rule == SP_COMPONENT || a.step.rule == SP_COMPLEMENT) return;
    /* La strategia con istanze propaga direttamente i fatti unitari:
     * astrarli di nuovo li nasconderebbe dietro guardie senza offrire una
     * scelta fra rami. Le disgiunzioni restano affidate allo split. */
    if (s->comprehension && a.count == 1) return;
    sp_scratch_reset(s);
    int *parent = sp_allocate(s, &s->scratch, (size_t)a.count, sizeof *parent);
    int *owner = sp_allocate(s, &s->scratch, (size_t)a.variables, sizeof *owner);
    int *which = sp_allocate(s, &s->scratch, (size_t)a.count, sizeof *which);
    if (!parent || !which || (a.variables && !owner)) return;
    for (int i = 0; i < a.count; i++) { parent[i] = i; which[i] = -1; }
    for (int i = 0; i < a.variables; i++) owner[i] = -1;
    for (int i = 0; i < a.count && sp_visit(s); i++) if (!sp_guard(s, a.literal[i])) {
        sp_group_variables(s, a.literal[i].left, i, parent, owner);
        sp_group_variables(s, a.literal[i].right, i, parent, owner);
    }
    int groups = 0;
    for (int i = 0; i < a.count && sp_visit(s); i++) if (!sp_guard(s, a.literal[i])) {
        int root = sp_group_root(s, parent, i);
        parent[i] = root;
        if (which[root] < 0) which[root] = groups++;
    }
    if (s->limited || !groups || (groups == 1 && a.variables)) return;
    SpGroup *part = sp_allocate(s, &s->scratch, (size_t)groups, sizeof *part);
    int *used = sp_allocate(s, &s->scratch, (size_t)groups, sizeof *used);
    SpLiteral *out = sp_allocate(s, &s->scratch, (size_t)a.count, sizeof *out);
    if (!part || !used || !out) return;
    memset(part, 0, (size_t)groups * sizeof *part); memset(used, 0, (size_t)groups * sizeof *used);
    /* Le radici sono gia definitive. Una nuova visita con quota durante
     * il conteggio potrebbe fermarsi su un nodo interno, privo di gruppo:
     * usare soltanto le radici congelate evita un indice -1. */
    for (int i = 0; i < a.count; i++) if (!sp_guard(s, a.literal[i])) part[which[parent[i]]].count++;
    for (int i = 0; i < groups; i++) {
        part[i].literal = sp_allocate(s, &s->scratch, (size_t)part[i].count, sizeof *part[i].literal);
        if (!part[i].literal) return;
    }
    for (int i = 0; i < a.count; i++) if (!sp_guard(s, a.literal[i])) {
        int group = which[parent[i]];
        ((int *)part[group].literal)[used[group]++] = i;
    }
    for (int i = 0; i < groups && sp_visit(s); i++) {
        SpLiteral *literal = sp_allocate(s, &s->scratch, (size_t)part[i].count, sizeof *literal);
        if (!literal) return;
        for (int j = 0; j < part[i].count; j++) literal[j] = a.literal[part[i].literal[j]];
        SpClause key = sp_normal(s, literal, part[i].count);
        /* Anche in una clausola con variabili, un singolo gruppo ground
         * condivide la chiave positiva con il suo letterale opposto. */
        if (!key.variables && key.count == 1 && key.literal[0].negative) {
            part[i].negative = 1; literal[0].negative = 0; key = sp_normal(s, literal, 1);
        }
        int id = sp_component(s, key);
        if (id < 0) return;
        part[i].component = id;
        out[i] = (SpLiteral){s->component[id].atom, 0, part[i].negative};
    }
    int count = groups;
    for (int i = 0; i < a.count; i++) if (sp_guard(s, a.literal[i])) out[count++] = a.literal[i];
    if (s->limited) return;
    sp_keep(s, out, count, (SpStep){.rule=SP_SPLIT, .p=p, .groups=groups, .group=part}, -1);
    if (!s->limited) s->clause[p].stage = SP_DELETED;
}

/* Istanzia una formula universale su parti con una proprieta letterale.
 * Tutte le clausole emesse restano indicizzate, perche il checker ricrea
 * l'intero gruppo. Nessuna verita della proprieta viene assunta. L'istanza
 * puo introdurre altre formule quantificate, con le proprie copie di contesto.
 * Una quota interrompe onestamente il tentativo finale: un gruppo parziale
 * non viene esportato. Ritorna uno anche per un'istanza gia presente. */
static int sp_comprehend(SpState *s, int id, SpLiteral literal) {
    if (!sp_visit(s)) return 0;
    if (s->emitting || id < 0 || id >= s->schemas || !s->schema[id].every) {
        s->unsupported = 1; return 0;
    }
    SpClause property = sp_normal(s, &literal, 1);
    if (s->limited) return 0;
    if (property.count != 1 || property.variables > 1 || !property.literal[0].left) { s->unsupported = 1; return 0; }
    literal = property.literal[0];
    for (int i = 0; i < s->expansions && sp_visit(s); i++) {
        SpExpansion old = s->expansion[i];
        if (old.schema == id && old.property.left == literal.left && old.property.right == literal.right && old.property.negative == literal.negative) {
            if (!old.complete) { s->limited = 1; s->resumable = 0; return 0; }
            return 1;
        }
    }
    if (s->limited) return 0;
    if (s->expansions == INT_MAX || !sp_reserve(s, (void **)&s->expansion, &s->expansion_cap,
            (size_t)s->expansions + 1, sizeof *s->expansion)) { s->limited = 1; return 0; }
    if (s->introductions == INT_MAX || !sp_reserve(s, (void **)&s->introduction, &s->introduction_cap,
            (size_t)s->introductions + 1, sizeof *s->introduction)) { s->limited = 1; return 0; }
    SpSchema schema = s->schema[id];
    if (!sp_reserve(s, (void **)&s->universals, &s->universal_cap, (size_t)schema.universal, sizeof *s->universals)) return 0;
    if (slot_count) memcpy(s->binding, schema.binding, (size_t)slot_count * sizeof *s->binding);
    if (declared_symbols) memcpy(s->property, schema.property, (size_t)declared_symbols * sizeof *s->property);
    if (schema.universal) memcpy(s->universals, schema.universals, (size_t)schema.universal * sizeof *s->universals);
    s->universal = schema.universal;
    int part = schema.source->part;
    s->property[part] = (SpProperty){literal, symbols[part].domain[0]};
    int expansion = s->expansions++;
    s->expansion[expansion] = (SpExpansion){.schema=id, .first=s->clauses, .past=s->clauses, .symbol_first=s->symbols, .property=literal};
    s->introduction[s->introductions++] = (SpIntroduction){SP_COMPREHEND, expansion};
    s->emitting = expansion + 1;
    /* Una quota locale puo fermare la strategia, ma non lascia un comando
     * a meta. Il budget globale e la memoria restano sempre vincolanti. */
    unsigned long long quota = s->quota; clock_t cpu_quota = s->cpu_quota;
    s->quota = 0; s->cpu_quota = 0;
    SpLiteral result = sp_formula(s, schema.source->a, schema.positive);
    sp_emit(s, sp_not(schema.name), result, result, 2);
    s->quota = quota; s->cpu_quota = cpu_quota;
    s->emitting = 0;
    s->expansion[expansion].past = s->clauses;
    s->expansion[expansion].symbol_past = s->symbols;
    s->expansion[expansion].complete = !s->limited && !s->unsupported;
    if (!s->expansion[expansion].complete) s->resumable = 0;
    s->universal = 0;
    if (slot_count) memset(s->binding, 0, (size_t)slot_count * sizeof *s->binding);
    if (declared_symbols) memset(s->property, 0, (size_t)declared_symbols * sizeof *s->property);
    return !s->limited && !s->unsupported;
}

/* Le parti vuota e intera sono comprensioni valide anche senza elementi
 * nominati. Si propone una sola formula per turno; le formule annidate
 * entrano nella stessa agenda dinamica, senza un limite di profondita.
 * Le proprieta x=x e x!=x sono dati generali, non casi di un esercizio. */
static void sp_seed_comprehensions(SpState *s) {
    while (s->seed_schema < s->schemas && sp_visit(s)) {
        int id = s->seed_schema++;
        if (!s->schema[id].every) continue;
        sp_scratch_reset(s);
        if (sp_comprehend(s, id, (SpLiteral){-1, -1, 0})) sp_comprehend(s, id, (SpLiteral){-1, -1, 1});
        return;
    }
}

/* Una proprieta proposta deve avere solo il parametro da astrarre.
 * Qui il controllo di groundness e sintattico, senza assegnazioni a caso. */
static int sp_ground_term(SpState *s, int term) {
    if (!term) return 1;
    if (!sp_visit(s) || term < 0) return 0;
    SpTerm n = s->term[term];
    for (int i = 0; i < n.count; i++) if (!sp_ground_term(s, s->argument[n.first + i])) return 0;
    return 1;
}

/* Una proprieta gia proposta copre i suoi casi particolari. Il matching
 * separa i due parametri: P(s(x)) non richiede un'altra istanza induttiva
 * quando P(x) e gia nell'agenda. E solo una selezione della ricerca, non
 * una prova di P(x); il checker riceve sempre le istanze effettive. */
static int sp_property_covered(SpState *s, int schema, SpLiteral property) {
    for (int i = 0; i < s->expansions && sp_visit(s); i++) {
        SpExpansion e = s->expansion[i]; SpLiteral old = e.property;
        if (e.schema != schema || old.negative != property.negative || !!old.right != !!property.right) continue;
        for (int flip = 0; flip < (old.right ? 2 : 1) && sp_visit(s); flip++) {
            sp_scratch_reset(s);
            if (!sp_match_start(s, 1)) return 0;
            /* Ogni proprieta ha al piu v0: v1 separa il candidato dalla
             * variabile sostituibile della proprieta gia proposta. */
            int left = sp_apply(s, flip ? property.right : property.left, 1, NULL, 0, 0);
            int right = sp_apply(s, flip ? property.left : property.right, 1, NULL, 0, 0);
            if (sp_match(s, old.left, left) && (!old.right || sp_match(s, old.right, right))) return 1;
        }
    }
    return 0;
}

/* Dalla clausola selezionata L[t] si propone la proprieta complementare
 * NOT L[x]. Le sottoespressioni piu piccole vengono prima: per f(a)!=a
 * la scelta a produce f(x)=x. Si applica la stessa operazione strutturale
 * alle costanti del letterale, senza riconoscere un teorema o un costruttore.
 * Questa e la selezione leggera su unita ground di Reger e Voronkov:
 * applicare subito tutte le proprieta di ogni clausola moltiplicherebbe
 * i corpi prima di poter lavorare sull'obiettivo induttivo corrente. */
static void sp_propose_term(SpState *s, SpLiteral literal, int term) {
    if (term <= 0 || !sp_visit(s)) return;
    SpTerm n = s->term[term];
    for (int i = 0; i < n.count && !s->limited; i++) sp_propose_term(s, literal, s->argument[n.first + i]);
    if (n.count || s->symbol[n.symbol].predicate || s->limited || s->unsupported) return;
    sp_scratch_reset(s);
    SpLiteral property = sp_not(literal);
    property.left = sp_replace_term(s, property.left, term, -1);
    property.right = sp_replace_term(s, property.right, term, -1);
    int schemas = s->schemas;
    for (int i = 0; i < schemas && sp_visit(s); i++) if (s->schema[i].every) {
        if (sp_property_covered(s, i, property)) continue;
        if (!sp_comprehend(s, i, property)) return;
    }
}

/* I predicati tecnici di domini e Tseitin guidano la saturazione, ma non
 * sono nuovi obiettivi induttivi. Si considerano uguaglianze e predicati
 * originali ground; il budget globale limita i tentativi, non un tetto
 * compilato al numero di proprieta o istanze. */
static void sp_propose_comprehensions(SpState *s, int id) {
    if (!s->schemas) return;
    SpClause c = s->clause[id];
    int ordinary = 0;
    for (int i = 0; i < c.count; i++) ordinary += !sp_guard(s, c.literal[i]);
    if (ordinary != 1) return;
    for (int i = 0; i < c.count && sp_visit(s); i++) {
        SpLiteral l = c.literal[i];
        if (sp_guard(s, l)) continue;
        /* Nel ramo SAT si anticipano i controesempi negativi: dai fatti
         * gia veri non si generano subito proprieta complementari. Il
         * tentativo ordinario finale considera entrambi i segni. */
        if (s->avatar && !l.negative) continue;
        if (!l.left || (!l.right && (l.left < 0 || s->term[l.left].symbol >= s->inputs))) continue;
        if (!sp_ground_term(s, l.left) || !sp_ground_term(s, l.right)) continue;
        sp_propose_term(s, l, l.left); sp_propose_term(s, l, l.right);
    }
}

/* Congela le immagini di una sostituzione. Risolvere qui tutte le catene
 * permette al checker di applicarla una sola volta, simultaneamente. */
static SpStep sp_snapshot(SpState *s, SpStep step, const int *sub, int count, int recursive) {
    int bindings = 0;
    for (int v = 0; v < count; v++) bindings += sub[v] != 0;
    SpBinding *saved = sp_allocate(s, &s->scratch, (size_t)bindings, sizeof *saved);
    if (bindings && !saved) return step;
    step.binding = saved; step.bindings = 0;
    for (int v = 0; v < count && sp_visit(s); v++) if (sub[v]) {
        int term = sp_apply(s, sub[v], 0, sub, count, recursive);
        if (term != -v - 1) saved[step.bindings++] = (SpBinding){v, term};
    }
    return step;
}

/* Dimensiona il contesto dei genitori separati. Il prefisso storico 64
 * mantiene leggibili i primi certificati, senza essere un limite. */
static int sp_context(SpState *s, int p, int q, int *offset) {
    *offset = s->clause[p].variables > 64 ? s->clause[p].variables : 64;
    if (s->clause[q].variables > INT_MAX - *offset) { s->limited = 1; return 0; }
    return *offset + s->clause[q].variables;
}

/* Conserva il risultato di una risoluzione o fattorizzazione. omit_a e
 * omit_b sono i letterali cancellati, -1 se nessuno; b puo essere vuota.
 * extra aggiunge, se richiesto, l'ineguaglianza della fattorizzazione equazionale. */
static void sp_combination(SpState *s, SpStep step, SpClause a, int omit_a,
                           SpClause b, int omit_b, int offset, const SpLiteral *extra) {
    if (b.count > INT_MAX - a.count - 1) { s->limited = 1; return; }
    int capacity = a.count + b.count + 1, used = 0;
    SpLiteral *out = sp_allocate(s, &s->scratch, (size_t)capacity, sizeof *out);
    SpLiteral *x = sp_instance(s, a, 0, s->sub, s->sub_count, 1);
    SpLiteral *y = sp_instance(s, b, offset, s->sub, s->sub_count, 1);
    if (!out || (a.count && !x) || (b.count && !y)) return;
    for (int i = 0; i < a.count; i++) if (i != omit_a) out[used++] = x[i];
    for (int i = 0; i < b.count; i++) if (i != omit_b) out[used++] = y[i];
    if (extra) out[used++] = *extra;
    step = sp_snapshot(s, step, s->sub, s->sub_count, 1);
    sp_keep(s, out, used, step, -1);
}

/* La selezione vale 1 se sono presenti letterali negativi ordinari, 2
 * per una clausola composta soltanto da domini, zero negli altri casi.
 * Le guardie AVATAR non partecipano alla scelta dei letterali FO. */
static int sp_resolution_selection(const SpState *s, SpClause c) {
    int negative = 0, domains = s->inputs != 0;
    for (int i = 0; i < c.count; i++) {
        SpLiteral l = c.literal[i];
        if (s->avatar && sp_guard(s, l)) continue;
        negative |= l.negative;
        if (l.right || l.left <= 0) domains = 0;
        else {
            int symbol = s->term[l.left].symbol;
            domains &= symbol >= s->inputs && symbol < s->inputs + sort_count;
        }
    }
    return domains ? 2 : negative;
}

/* Si privilegiano i negativi, ma le clausole dei domini usano il massimo
 * KBO. In D(f(x)) OR NOT D(x) il massimo e D(f(x)): si risponde cosi a
 * richieste su un termine gia presente, invece di generare D(f^n(a)) per
 * tutti i termini possibili. Nessun vincolo di dominio viene cancellato.
 * La selezione decide soltanto quali risoluzioni valide tentare. */
static int sp_resolution_literal(SpState *s, SpClause c, int index, int selection) {
    SpLiteral l = c.literal[index];
    if (s->avatar && sp_guard(s, l)) return 0;
    if (selection != 2) return !selection || l.negative;
    for (int i = 0; i < c.count && sp_visit(s); i++)
        if ((!s->avatar || !sp_guard(s, c.literal[i])) && sp_greater(s, c.literal[i].left, l.left)) return 0;
    return !s->limited;
}

/* Risoluzione binaria: da C o A e D o non B, se A e B si unificano,
 * segue (C o D) sigma. Per le uguaglianze si provano entrambi i versi.
 * Non si identificano le variabili dei genitori prima dell'unificazione. */
static void sp_resolve(SpState *s, int p, int q) {
    SpClause a = s->clause[p], b = s->clause[q];
    int selection_a = sp_resolution_selection(s, a), selection_b = sp_resolution_selection(s, b);
    int offset, count = sp_context(s, p, q, &offset);
    for (int i = 0; i < a.count && s->empty < 0 && sp_visit(s); i++)
        for (int j = 0; j < b.count && s->empty < 0 && sp_visit(s); j++) {
            SpLiteral x = a.literal[i], y = b.literal[j];
            if (!sp_resolution_literal(s, a, i, selection_a) || !sp_resolution_literal(s, b, j, selection_b)) continue;
            if (x.negative == y.negative || !!x.right != !!y.right || !x.left || !y.left) continue;
            for (int flip = 0; flip < (x.right ? 2 : 1) && s->empty < 0 && sp_visit(s); flip++) {
                sp_scratch_reset(s);
                if (!sp_unify_start(s, count)) return;
                int left = sp_apply(s, flip ? y.right : y.left, offset, NULL, 0, 0);
                int right = sp_apply(s, flip ? y.left : y.right, offset, NULL, 0, 0);
                if (!sp_unify(s, x.left, left) || (x.right && !sp_unify(s, x.right, right))) continue;
                sp_combination(s, (SpStep){.rule=SP_RESOLVE, .p=p, .lp=i, .q=q, .lq=j}, a, i, b, j, offset, NULL);
            }
        }
}

/* Trova un letterale proposizionale esatto, oppure restituisce -1.
 * I duplicati sono gia contratti dalla normalizzazione delle clausole. */
static int sp_proposition(SpClause c, int atom, int negative) {
    for (int i = 0; i < c.count; i++)
        if (!c.literal[i].right && c.literal[i].left == atom && c.literal[i].negative == negative) return i;
    return -1;
}

/* Elimina un nome tecnico senza argomenti con Davis-Putnam: da tutte le
 * coppie C OR q, D OR NOT q conserva C OR D, poi ritira le clausole con q.
 * Ogni risolvente ha una risoluzione esplicita, ricontrollabile dal checker.
 * Teacher: un modello dei risolventi si estende scegliendo q vero se un C
 * e falso, falso se un D e falso; entrambe le richieste non possono esserci
 * insieme, perche falsificherebbero C OR D. L'argomento vale anche quando
 * C e D sono universalmente quantificate, separandone prima le variabili.
 * Se una quota interrompe le coppie, i genitori restano nella ricerca.
 * Non si eliminano nomi di parti o componenti, che altre istanze possono
 * riutilizzare. Nessun predicato con argomenti viene trattato da Booleano. */
static void sp_eliminate_comprehensions(SpState *s) {
    while (s->eliminate_expansion < s->expansions && s->empty < 0 && sp_visit(s)) {
        SpExpansion e = s->expansion[s->eliminate_expansion];
        if (s->eliminate_symbol < e.symbol_first) s->eliminate_symbol = e.symbol_first;
        if (s->eliminate_symbol >= e.symbol_past) {
            s->eliminate_expansion++; s->eliminate_symbol = 0; continue;
        }
        int symbol = s->eliminate_symbol, protected = 0;
        if (!s->symbol[symbol].predicate || s->symbol[symbol].arity || s->symbol[symbol].component) {
            s->eliminate_symbol++; continue;
        }
        int atom = sp_term(s, symbol, NULL);
        for (int i = 0; i < s->schemas && sp_visit(s); i++) protected |= s->schema[i].name.left == atom;
        for (int i = 0; i < s->components && sp_visit(s); i++)
            protected |= sp_proposition(s->component[i].key, atom, 0) >= 0 || sp_proposition(s->component[i].key, atom, 1) >= 0;
        if (s->limited) return;
        if (protected) { s->eliminate_symbol++; continue; }
        int last = s->clauses;
        for (int p = 0; p < last && s->empty < 0 && sp_visit(s); p++) {
            if (s->clause[p].stage == SP_DELETED) continue;
            SpClause a = s->clause[p]; int x = sp_proposition(a, atom, 0);
            if (x < 0) continue;
            for (int q = 0; q < last && s->empty < 0 && sp_visit(s); q++) {
                if (s->clause[q].stage == SP_DELETED) continue;
                SpClause b = s->clause[q]; int y = sp_proposition(b, atom, 1);
                if (y < 0) continue;
                sp_scratch_reset(s);
                int offset, count = sp_context(s, p, q, &offset);
                if (!sp_unify_start(s, count)) return;
                sp_combination(s, (SpStep){.rule=SP_RESOLVE, .p=p, .lp=x, .q=q, .lq=y}, a, x, b, y, offset, NULL);
            }
        }
        if (s->limited) return;
        for (int i = 0; i < last && sp_visit(s); i++)
            if (sp_proposition(s->clause[i], atom, 0) >= 0 || sp_proposition(s->clause[i], atom, 1) >= 0) s->clause[i].stage = SP_DELETED;
        if (s->limited) return;
        s->eliminate_symbol++;
    }
}

/* Inferenze a un genitore. l!=r si cancella quando l e r si unificano.
 * Due atomi dello stesso segno si contraggono con un unificatore comune.
 * Dalle uguaglianze l=r o u=v, con l sigma=u sigma, segue invece
 * (resto o u=v o r!=v) sigma: e la fattorizzazione equazionale. */
static void sp_unary(SpState *s, int p) {
    SpClause a = s->clause[p], none = {0};
    for (int i = 0; i < a.count && s->empty < 0 && sp_visit(s); i++) {
        SpLiteral x = a.literal[i];
        if (s->avatar && sp_guard(s, x)) continue;
        if (x.negative && x.right) {
            sp_scratch_reset(s);
            if (sp_unify_start(s, a.variables) && sp_unify(s, x.left, x.right))
                sp_combination(s, (SpStep){.rule=SP_REFLEX, .p=p, .lp=i}, a, i, none, -1, 0, NULL);
        }
        for (int j = 0; j < a.count && s->empty < 0 && sp_visit(s); j++) {
            if (j == i) continue;
            SpLiteral y = a.literal[j];
            if (s->avatar && sp_guard(s, y)) continue;
            if (j > i && x.negative == y.negative && !!x.right == !!y.right) {
                for (int flip = 0; flip < (x.right ? 2 : 1) && s->empty < 0 && sp_visit(s); flip++) {
                    sp_scratch_reset(s);
                    if (!sp_unify_start(s, a.variables)) return;
                    if (!sp_unify(s, x.left, flip ? y.right : y.left) ||
                        (x.right && !sp_unify(s, x.right, flip ? y.left : y.right))) continue;
                    sp_combination(s, (SpStep){.rule=SP_FACTOR, .p=p, .lp=i, .lq=j}, a, i, none, -1, 0, NULL);
                }
            }
            /* Per la fattorizzazione equazionale si conserva ciascuna
             * delle due uguaglianze a turno: i residui non sono lo stesso
             * insieme sintattico di letterali, a differenza della fattorizzazione. */
            if (!x.negative && !y.negative && x.right && y.right)
                for (int flip = 0; flip < 2 && s->empty < 0 && sp_visit(s); flip++)
                    for (int other = 0; other < 2 && s->empty < 0 && sp_visit(s); other++) {
                        sp_scratch_reset(s);
                        if (!sp_unify_start(s, a.variables) ||
                            !sp_unify(s, flip ? x.right : x.left, other ? y.right : y.left)) continue;
                        SpLiteral extra = {sp_apply(s, flip ? x.left : x.right, 0, s->sub, s->sub_count, 1),
                                           sp_apply(s, other ? y.left : y.right, 0, s->sub, s->sub_count, 1), 1};
                        sp_combination(s, (SpStep){.rule=SP_EQUAL_FACTOR, .p=p, .lp=i, .lq=j, .flip=flip, .otherflip=other},
                                       a, i, none, -1, 0, &extra);
                    }
        }
    }
}

/* Trova una posizione preorder del termine originale e ne conserva il
 * cammino di figli in path. I pesi esatti consentono di saltare sottoalberi
 * senza visitarli; il cammino resta valido anche se si unificano variabili. */
static int sp_path(SpState *s, int term, unsigned long long position) {
    s->path_count = 0;
    while (position && term > 0 && sp_visit(s)) {
        SpTerm n = s->term[term]; position--;
        int found = 0;
        for (int i = 0; i < n.count; i++) {
            int child = s->argument[n.first + i]; unsigned long long weight = sp_term_weight(s, child);
            if (position >= weight) { position -= weight; continue; }
            if (!sp_reserve(s, (void **)&s->path, &s->path_cap, (size_t)s->path_count + 1, sizeof *s->path)) return 0;
            s->path[s->path_count++] = i; term = child; found = 1; break;
        }
        if (!found) return 0;
    }
    return position ? 0 : term;
}

/* Sostituisce sul cammino scelto e calcola la posizione DOPO sigma. Le
 * immagini delle variabili che precedono il punto possono avere piu nodi:
 * usare la vecchia posizione sarebbe un certificato sbagliato. */
static int sp_rewrite(SpState *s, int term, int depth, int offset, const int *sub, int count, int recursive,
                      int replacement, unsigned long long before, int *position) {
    if (!sp_visit(s)) return 0;
    if (depth == s->path_count) {
        if (before >= INT_MAX) { s->limited = 1; return 0; }
        *position = (int)before;
        return replacement;
    }
    if (term <= 0) { s->limited = 1; return 0; }
    SpTerm n = s->term[term];
    int *args = sp_allocate(s, &s->scratch, (size_t)n.count, sizeof *args);
    if (n.count && !args) return 0;
    before++;
    for (int i = 0; i < n.count; i++) {
        int child = s->argument[n.first + i];
        if (i == s->path[depth]) args[i] = sp_rewrite(s, child, depth + 1, offset, sub, count, recursive, replacement, before, position);
        else args[i] = sp_apply(s, child, offset, sub, count, recursive);
        if (i < s->path[depth]) {
            unsigned long long weight = sp_term_weight(s, args[i]);
            if (weight > ULLONG_MAX - before) { s->limited = 1; return 0; }
            before += weight;
        }
    }
    return sp_term(s, n.symbol, args);
}

/* Costruisce una superposizione valida dopo matching o unificazione. La
 * posizione originale e descritta da path, la sostituzione dal chiamante.
 * Il punto non e mai una variabile ne la radice di un predicato. */
static void sp_super_result(SpState *s, SpStep step, int offset, const int *sub, int count, int recursive) {
    SpClause a = s->clause[step.p], b = s->clause[step.q];
    SpLiteral source = a.literal[step.lp], target = b.literal[step.lq];
    int lhs = sp_apply(s, step.flip ? source.right : source.left, 0, sub, count, recursive);
    int rhs = sp_apply(s, step.flip ? source.left : source.right, 0, sub, count, recursive);
    if (lhs == rhs || sp_greater(s, rhs, lhs)) return;
    int raw = step.side ? target.right : target.left;
    int other = step.side ? target.left : target.right;
    int entire = sp_apply(s, raw, offset, sub, count, recursive);
    if (target.right && sp_greater(s, sp_apply(s, other, offset, sub, count, recursive), entire)) return;
    int result = sp_rewrite(s, raw, 0, offset, sub, count, recursive, rhs, 0, &step.position);
    SpLiteral *x = sp_instance(s, a, 0, sub, count, recursive), *y = sp_instance(s, b, offset, sub, count, recursive);
    if ((a.count && !x) || (b.count && !y) || s->limited) return;
    if (step.side) y[step.lq].right = result; else y[step.lq].left = result;
    if (b.count > INT_MAX - a.count) { s->limited = 1; return; }
    SpLiteral *out = sp_allocate(s, &s->scratch, (size_t)(a.count + b.count), sizeof *out);
    if (!out) return;
    int used = 0;
    for (int i = 0; i < a.count; i++) if (i != step.lp) out[used++] = x[i];
    for (int i = 0; i < b.count; i++) out[used++] = y[i];
    step = sp_snapshot(s, step, sub, count, recursive);
    sp_keep(s, out, used, step, -1);
}

/* Superposizioni fra due clausole, comprese quelle di una clausola con una
 * propria copia rinominata. Si esclude il verso strettamente crescente
 * dopo sigma, ma si conservano i termini incomparabili e tutti i letterali:
 * il calcolo contiene quindi le inferenze della superposizione ordinata. */
static void sp_superpose(SpState *s, int p, int q) {
    SpClause a = s->clause[p], b = s->clause[q];
    int offset, count = sp_context(s, p, q, &offset);
    for (int i = 0; i < a.count && s->empty < 0 && sp_visit(s); i++) {
        SpLiteral source = a.literal[i];
        if (source.negative || !source.right) continue;
        for (int flip = 0; flip < 2 && s->empty < 0 && sp_visit(s); flip++) {
            int lhs = flip ? source.right : source.left;
            if (lhs < 0) continue;
            for (int j = 0; j < b.count && s->empty < 0 && sp_visit(s); j++)
                for (int side = 0; side < (b.literal[j].right ? 2 : 1) && s->empty < 0 && sp_visit(s); side++) {
                    int raw = side ? b.literal[j].right : b.literal[j].left;
                    unsigned long long size = sp_term_weight(s, raw), first = b.literal[j].right ? 0 : 1;
                    for (unsigned long long pos = first; pos < size && s->empty < 0 && sp_visit(s); pos++) {
                        sp_scratch_reset(s);
                        int at = sp_path(s, raw, pos);
                        if (at <= 0 || !sp_unify_start(s, count)) continue;
                        int target = sp_apply(s, at, offset, NULL, 0, 0);
                        if (!sp_unify(s, lhs, target)) continue;
                        sp_super_result(s, (SpStep){.rule=SP_SUPER, .p=p, .lp=i, .q=q, .lq=j, .flip=flip, .side=side},
                                        offset, s->sub, s->sub_count, 1);
                    }
                }
        }
    }
}

/* Riscrive una clausola con una singola uguaglianza universale orientata.
 * Si usa matching: la clausola bersaglio non viene istanziata. La nuova
 * clausola e equivalente alla precedente in presenza dell'uguaglianza;
 * anche se gia sussunta, rende ridondante il vecchio bersaglio. */
static int sp_demodulate(SpState *s, int p, int q) {
    SpClause a = s->clause[p], b = s->clause[q];
    if (p == q || a.count != 1 || a.literal[0].negative || !a.literal[0].right) return 0;
    SpLiteral l = a.literal[0];
    int flip;
    if (sp_greater(s, l.left, l.right)) flip = 0;
    else if (sp_greater(s, l.right, l.left)) flip = 1;
    else return 0;
    int lhs = flip ? l.right : l.left, offset, count = sp_context(s, p, q, &offset);
    (void)count;
    for (int j = 0; j < b.count && sp_visit(s); j++)
        for (int side = 0; side < (b.literal[j].right ? 2 : 1) && sp_visit(s); side++) {
            int raw = side ? b.literal[j].right : b.literal[j].left;
            unsigned long long size = sp_term_weight(s, raw), first = b.literal[j].right ? 0 : 1;
            for (unsigned long long pos = first; pos < size && sp_visit(s); pos++) {
                sp_scratch_reset(s);
                int at = sp_path(s, raw, pos);
                if (at <= 0 || !sp_match_start(s, a.variables)) continue;
                if (!sp_match(s, lhs, sp_apply(s, at, offset, NULL, 0, 0))) continue;
                /* La demodulazione puo agire anche nel membro minore di
                 * un'uguaglianza: e una riscrittura, non una restrizione
                 * necessaria al calcolo della superposizione. */
                SpClause original = s->clause[q];
                SpLiteral *target = sp_instance(s, original, offset, s->match, s->match_count, 0);
                int rhs = sp_apply(s, flip ? l.left : l.right, 0, s->match, s->match_count, 0), position;
                int rewritten = sp_rewrite(s, raw, 0, offset, s->match, s->match_count, 0, rhs, 0, &position);
                if (!target || s->limited) return 0;
                if (side) target[j].right = rewritten; else target[j].left = rewritten;
                SpStep step = {.rule=SP_SUPER, .p=p, .lp=0, .q=q, .lq=j, .flip=flip, .side=side, .position=position};
                step = sp_snapshot(s, step, s->match, s->match_count, 0);
                sp_keep(s, target, original.count, step, q);
                if (s->limited) return 0;
                s->clause[q].stage = SP_DELETED;
                return 1;
            }
        }
    return 0;
}

/* Ricomincia la coda con le clausole scelte e ogni deduzione conservata.
 * Non si rianima una clausola eliminata per tautologia o sussunzione.
 * Anche gli ACTIVE tornano PENDING: una quota puo avere fermato le loro
 * inferenze prima di esaurirle. L'eta riparte da zero senza perdere equita.
 * selected=NULL riattiva tutte le ipotesi. keep_active e ammesso solo
 * quando il modello SAT precedente viene esteso senza cambiarne i valori;
 * conserva allora anche l'eta e l'agenda unitaria. Ritorna quante sono sospese;
 * con limited la coda e incompleta e il chiamante non deve usarla. */
static int sp_requeue_mode(SpState *s, const unsigned char *selected, int keep_active) {
    int held = 0;
    s->heap_count = 0;
    if (!keep_active) {
        s->age = 0; s->rounds = 0;
        s->units = s->unit_cursor = 0;
    }
    for (int i = 0; i < s->clauses && sp_visit(s); i++) {
        if (s->clause[i].stage == SP_DELETED) continue;
        int keep = i >= s->initial || !selected || selected[i];
        SpStage stage = keep ? sp_available(s, s->clause[i]) : SP_HELD;
        if (keep_active && stage == SP_PENDING && s->clause[i].stage == SP_ACTIVE) stage = SP_ACTIVE;
        s->clause[i].stage = stage;
        if (s->clause[i].stage == SP_PENDING) sp_enqueue(s, i);
        if (!keep) held++;
    }
    return held;
}

/* Una strategia nuova riprende anche le inferenze eventualmente interrotte
 * dal tentativo precedente. Nessuna clausola elaborata resta esclusa. */
static int sp_requeue(SpState *s, const unsigned char *selected) {
    return sp_requeue_mode(s, selected, 0);
}

/* Converte una guardia nel letterale del SAT. La variabile SAT uno e la
 * costante vera; le componenti occupano consecutivamente i posti da due. */
static SatLiteral sp_boolean(const SpState *s, SpLiteral l) {
    SatLiteral v = (SatLiteral)sp_guard(s, l) + 1;
    return l.negative ? -v : v;
}

/* Risoluzione proposizionale esplicita per il replay. Il pivot e l'indice
 * della componente, non una decisione del SAT. Entrambi i genitori sono
 * clausole complete gia giustificate; nessuna unificazione e necessaria. */
static int sp_boolean_resolve(SpState *s, int p, int q, int pivot) {
    SpClause a = s->clause[p], b = s->clause[q];
    int x = -1, y = -1;
    for (int i = 0; i < a.count; i++) if (sp_guard(s, a.literal[i]) == pivot + 1) x = i;
    for (int i = 0; i < b.count; i++) if (sp_guard(s, b.literal[i]) == pivot + 1) y = i;
    if (x < 0 || y < 0 || a.literal[x].negative == b.literal[y].negative || b.count > INT_MAX - a.count) return -1;
    sp_scratch_reset(s);
    SpLiteral *out = sp_allocate(s, &s->scratch, (size_t)a.count + (size_t)b.count, sizeof *out);
    if (!out) return -1;
    int count = 0;
    for (int i = 0; i < a.count; i++) if (i != x) out[count++] = a.literal[i];
    for (int i = 0; i < b.count; i++) if (i != y) out[count++] = b.literal[i];
    return sp_keep(s, out, count, (SpStep){.rule=SP_RESOLVE, .p=p, .lp=x, .q=q, .lq=y}, -1);
}

/* Ricostruisce una clausola appresa con RUP: si assumono falsi i suoi
 * letterali e si propagano soltanto clausole precedenti, gia giustificate.
 * Un conflitto si risolve all'indietro con le ragioni delle propagazioni;
 * restano soltanto negazioni delle assunzioni. La sottoclausola risultante
 * e quindi una conseguenza per risoluzione, anche se piu forte del target.
 * target vuoto richiede una contraddizione senza assunzioni.
 * Ritorna la clausola FO ricostruita, -1 se non riesce: UNSAT non basta. */
static int sp_rup(SpState *s, const SatLiteral *target, size_t count, size_t before) {
    memset(s->rup_value, 0, (size_t)s->components * sizeof *s->rup_value);
    memset(s->rup_reason, 0, (size_t)s->components * sizeof *s->rup_reason);
    for (size_t i = 0; i < count && sp_visit(s); i++) {
        size_t v = sat_index(target[i]);
        if (v < 2 || v - 2 >= (size_t)s->components) return -1;
        int value = target[i] < 0 ? 1 : -1;
        if (s->rup_value[v - 2] && s->rup_value[v - 2] != value) return -1;
        s->rup_value[v - 2] = (signed char)value;
    }
    int assigned = 0, conflict = -1, changed = 1;
    while (changed && conflict < 0 && !s->limited) {
        changed = 0;
        for (size_t j = 0; j < before && conflict < 0 && sp_visit(s); j++) {
            if (!s->sat_proof[j]) return -1;
            int id = s->sat_proof[j] - 1;
            SpClause c = s->clause[id];
            int unknown = 0, unit = -1, value = 0, satisfied = 0;
            for (int i = 0; i < c.count && sp_visit(s); i++) {
                int v = sp_guard(s, c.literal[i]) - 1;
                if (v < 0) return -1;
                int truth = s->rup_value[v] * (c.literal[i].negative ? -1 : 1);
                if (truth > 0) { satisfied = 1; break; }
                if (!truth) { unknown++; unit = v; value = c.literal[i].negative ? -1 : 1; }
            }
            if (satisfied) continue;
            if (!unknown) conflict = id;
            else if (unknown == 1) {
                s->rup_value[unit] = (signed char)value; s->rup_reason[unit] = id + 1;
                s->rup_trail[assigned++] = unit; changed = 1;
            }
        }
    }
    if (conflict < 0 || s->limited) return -1;
    while (assigned && sp_visit(s)) {
        int v = s->rup_trail[--assigned], used = 0;
        SpClause c = s->clause[conflict];
        for (int i = 0; i < c.count; i++) used |= sp_guard(s, c.literal[i]) == v + 1;
        if (used) {
            conflict = sp_boolean_resolve(s, conflict, s->rup_reason[v] - 1, v);
            if (conflict < 0) return -1;
        }
    }
    /* Il controllo finale impedisce che un replay incompleto venga usato
     * come ragione della clausola appresa o della clausola vuota. */
    SpClause result = s->clause[conflict];
    for (int i = 0; i < result.count && sp_visit(s); i++) {
        int present = 0;
        for (size_t j = 0; j < count && sp_visit(s); j++) present |= sp_boolean(s, result.literal[i]) == target[j];
        if (!present) return -1;
    }
    return s->limited ? -1 : conflict;
}

/* Traduce tutte le clausole apprese del CDCL in risoluzioni esplicite,
 * rispettandone l'ordine, poi ricostruisce il conflitto finale. Il replay
 * conserva esattamente i propri risultati, senza sussunzioni euristiche
 * e senza inviarli di nuovo al SAT. Una mancata ricostruzione e UNKNOWN. */
static int sp_avatar_replay(SpState *s) {
    size_t n = (size_t)s->components;
    if (!n) return 0;
    if (!sp_reserve(s, (void **)&s->rup_value, &s->rup_value_cap, n, sizeof *s->rup_value) ||
        !sp_reserve(s, (void **)&s->rup_reason, &s->rup_reason_cap, n, sizeof *s->rup_reason) ||
        !sp_reserve(s, (void **)&s->rup_trail, &s->rup_trail_cap, n, sizeof *s->rup_trail)) return 0;
    s->replaying = 1;
    int ok = 1;
    for (size_t i = 0; i < s->sat.clauses && ok && s->empty < 0 && sp_visit(s); i++) if (!s->sat_proof[i]) {
        SatClause c = s->sat.clause[i];
        int id = sp_rup(s, s->sat.literal + c.first, c.count, i);
        if (id < 0) ok = 0; else s->sat_proof[i] = id + 1;
    }
    if (ok && s->empty < 0 && !s->limited) ok = sp_rup(s, NULL, 0, s->sat.clauses) >= 0;
    s->replaying = 0;
    return ok && s->empty >= 0 && !s->limited;
}

/* Prima di ogni operazione SAT assegna il lavoro e la memoria ancora
 * disponibili a entrambi i motori. before permette di addebitare soltanto
 * il lavoro nuovo; nessun contatore viene azzerato fra due modelli SAT. */
static int sp_sat_begin(SpState *s, unsigned long long *before) {
    if (!sp_visit(s)) return 0;
    unsigned long long end = saturation_work_limit;
    if (s->quota && s->quota < end) end = s->quota;
    if (s->work >= end) { sp_visit(s); return 0; }
    if (!sp_memory_left(s) || end - s->work > ULLONG_MAX - s->sat.work) { s->limited = 1; return 0; }
    s->sat.memory_limit = s->sat.bytes + sp_memory_left(s);
    s->sat.budget = s->sat.work + end - s->work;
    *before = s->sat.work;
    return 1;
}

/* Registra il costo dell'operazione e traduce il limite locale del SAT
 * in una quota riprendibile soltanto quando non manca memoria e il budget
 * globale consente ancora la strategia successiva. */
static int sp_sat_end(SpState *s, unsigned long long before) {
    s->work += s->sat.work - before;
    if (s->sat.broken) {
        s->limited = 1;
        s->resumable = !s->sat.memory_limited && s->work < saturation_work_limit && s->quota && s->quota < saturation_work_limit;
    }
    return !s->limited;
}

/* Aggiunge nuove componenti e vincoli al livello zero, poi chiede un
 * modello SAT. Il vecchio modello FO resta copiato nelle componenti mentre
 * il CDCL cancella decisioni e propaga. Un modello viene riletto contro
 * tutte le clausole SAT prima di attivare le clausole FO del nuovo ramo.
 * UNSAT richiede invece il replay delle risoluzioni fino al vuoto. */
static int sp_avatar_update(SpState *s) {
    int last = s->clauses;
    while (s->split_cursor < last && sp_visit(s)) {
        sp_split(s, s->split_cursor);
        if (s->limited) return 0;
        s->split_cursor++;
    }
    if (s->limited || !s->avatar_dirty) return !s->limited;
    unsigned long long before;
    if (!sp_sat_begin(s, &before)) return 0;
    SatState *b = &s->sat;
    b->inconsistent = 0;
    for (size_t v = 1; v <= b->variables && sat_spend(b, 1); v++) { b->var[v].value = 0; b->var[v].seen = 0; }
    b->assigned = b->qhead = b->level = 0;
    while (b->variables < (size_t)s->components + 1 && !b->broken) sat_variable(b);
    if (!b->broken) sat_assign(b, 1, 0);
    for (size_t i = 0; i < b->clauses && sat_spend(b, 1); i++) {
        SatClause c = b->clause[i];
        if (c.count == 1 && !sat_assign(b, b->literal[c.first], i + 1)) b->inconsistent = 1;
    }
    if (!sp_sat_end(s, before)) return 0;
    last = s->clauses;
    for (; s->sat_cursor < last && sp_visit(s); s->sat_cursor++) {
        int id = s->sat_cursor; SpClause c = s->clause[id];
        if (c.stage == SP_DELETED || sp_available(s, c) != SP_BOOLEAN) continue;
        sp_scratch_reset(s);
        SatLiteral *literal = sp_allocate(s, &s->scratch, (size_t)c.count, sizeof *literal);
        if (!literal) return 0;
        for (int i = 0; i < c.count; i++) literal[i] = sp_boolean(s, c.literal[i]);
        if (!sp_sat_begin(s, &before)) return 0;
        size_t added = sat_clause(b, literal, (size_t)c.count);
        if (!sp_sat_end(s, before)) return 0;
        if (!sp_reserve(s, (void **)&s->sat_proof, &s->sat_proof_cap, b->clauses, sizeof *s->sat_proof)) return 0;
        if (added) s->sat_proof[added - 1] = id + 1;
    }
    if (!sp_sat_begin(s, &before)) return 0;
    int result = sat_solve(b);
    if (!sp_sat_end(s, before)) return 0;
    if (!sp_reserve(s, (void **)&s->sat_proof, &s->sat_proof_cap, b->clauses, sizeof *s->sat_proof)) return 0;
    if (result < 0) return sp_avatar_replay(s);
    if (!result) return 0;
    for (size_t i = 0; i < b->clauses && sp_visit(s); i++) {
        SatClause c = b->clause[i]; int satisfied = 0;
        for (size_t j = 0; j < c.count && sp_visit(s); j++) satisfied |= sat_value(b, b->literal[c.first + j]) > 0;
        if (!satisfied) return 0;
    }
    if (s->limited) return 0;
    int changed = 0;
    for (int i = 0; i < s->components; i++) {
        int value = b->var[(size_t)i + 2].value;
        if (!value) return 0;
        changed |= s->component[i].value && s->component[i].value != value;
        s->component[i].value = value;
    }
    s->sat_models++; s->avatar_dirty = 0;
    /* Un'estensione del medesimo modello non cambia le inferenze gia
     * esaurite. Riattivarle a ogni nuovo nome darebbe sempre precedenza
     * ai fatti vecchi e affamerebbe le clausole delle istanze. Il ciclo
     * marca invece PENDING la singola clausola interrotta da un vincolo.
     * Se cambia una decisione esistente si riesamina l'intero ramo. */
    int age = s->age; unsigned long long rounds = s->rounds;
    sp_requeue_mode(s, NULL, !changed);
    s->age = age; s->rounds = rounds;
    /* Un contenuto FO unitario del ramo puo avere guardie nel testo della
     * clausola. Proporlo subito evita che la coda dei nomi tecnici rinvii
     * l'obiettivo induttivo; la proprieta resta solo un candidato, non un
     * fatto del ramo. I corpi nuovi verranno suddivisi al giro successivo. */
    if (s->comprehension && !s->limited) {
        int clauses = s->clauses, expansions = s->expansions;
        for (int i = 0; i < clauses && sp_visit(s); i++) if (s->clause[i].stage == SP_PENDING)
            sp_propose_comprehensions(s, i);
        if (s->expansions != expansions) s->avatar_dirty = 1;
    }
    return !s->limited;
}

/* Individua l'unico letterale FO di una clausola, oppure restituisce -1.
 * In AVATAR le altre posizioni possono essere guardie ground; fuori da
 * AVATAR occorre una clausola unitaria nel senso ordinario. */
static int sp_unit_literal(const SpState *s, SpClause c) {
    int at = -1;
    for (int i = 0; i < c.count; i++) if (!s->avatar || !sp_guard(s, c.literal[i])) {
        if (at >= 0) return -1;
        at = i;
    }
    return at;
}

/* Cancella un letterale complementare a un'istanza di una clausola unitaria.
 * Il matching istanzia soltanto l'unita; il bersaglio resta universale sulle
 * sue variabili, rinominate a parte. Risoluzione e sostituzione esplicite
 * giustificano la riduzione. Le guardie dell'unita restano nel risultato:
 * il bersaglio si elimina soltanto se gia le contiene tutte, altrimenti
 * il risolvente vale sotto ipotesi piu forti e non puo sostituirlo. */
static int sp_unit_resolve(SpState *s, int target, int unit) {
    SpClause c = s->clause[target], a = s->clause[unit];
    int at = sp_unit_literal(s, a);
    if (at < 0) return 0;
    SpLiteral u = a.literal[at];
    int redundant = 1;
    for (int i = 0; i < a.count; i++) if (i != at) {
        int present = 0;
        for (int j = 0; j < c.count; j++)
            present |= a.literal[i].negative == c.literal[j].negative && sp_same_atom(a.literal[i], c.literal[j]);
        redundant &= present;
    }
    int offset;
    sp_context(s, unit, target, &offset);
    for (int i = 0; i < c.count && sp_visit(s); i++) {
        SpLiteral l = c.literal[i];
        if (u.negative == l.negative || !!u.right != !!l.right) continue;
        for (int flip = 0; flip < (u.right ? 2 : 1) && sp_visit(s); flip++) {
            sp_scratch_reset(s);
            if (!sp_match_start(s, s->clause[unit].variables)) return 0;
            int left = sp_apply(s, flip ? l.right : l.left, offset, NULL, 0, 0);
            int right = sp_apply(s, flip ? l.left : l.right, offset, NULL, 0, 0);
            if (!sp_match(s, u.left, left) || (u.right && !sp_match(s, u.right, right))) continue;
            SpLiteral *instance = sp_instance(s, c, offset, s->match, s->match_count, 0);
            SpLiteral *source = sp_instance(s, a, 0, s->match, s->match_count, 0);
            if (a.count > INT_MAX - c.count) { s->limited = 1; return 0; }
            SpLiteral *out = sp_allocate(s, &s->scratch, (size_t)a.count + (size_t)c.count, sizeof *out);
            if (!instance || !source || !out) return 0;
            int count = 0;
            for (int j = 0; j < a.count; j++) if (j != at) out[count++] = source[j];
            for (int j = 0; j < c.count; j++) if (j != i) out[count++] = instance[j];
            SpStep step = {.rule=SP_RESOLVE, .p=unit, .lp=at, .q=target, .lq=i};
            step = sp_snapshot(s, step, s->match, s->match_count, 0);
            sp_keep(s, out, count, step, -1);
            if (s->limited) return 0;
            if (redundant) s->clause[target].stage = SP_DELETED;
            return redundant;
        }
    }
    return 0;
}

/* Propagazione unitaria per le clausole nuove delle istanze. Si conserva
 * la prova di ogni riduzione, inclusi i nomi di Tseitin: altrimenti i corpi
 * delle comprensioni si moltiplicherebbero prima di usare base e passo.
 * L'agenda visita ogni clausola nuova; una nuova unita raggiunge anche le
 * clausole precedenti. Un turno visita soltanto il prefisso presente al
 * suo inizio: D(a), D(x)=>D(f(x)) genererebbero altrimenti D(f^n(a)) senza
 * mai lasciare lavorare il ciclo given-clause. Le nuove unita restano
 * nell'agenda del turno successivo, senza un tetto al numero di istanze.
 * Fuori da AVATAR le guardie sono disgiunti ordinari. */
static void sp_unit_propagate(SpState *s) {
    int last = s->clauses;
    while (s->unit_cursor < last && s->empty < 0 && sp_visit(s)) {
        int id = s->unit_cursor++;
        SpClause c = s->clause[id];
        if (c.stage == SP_DELETED || c.stage == SP_HELD || c.stage == SP_LOCKED) continue;
        if (c.stage == SP_BOOLEAN) continue;
        int at = sp_unit_literal(s, c);
        if (at >= 0) {
            int duplicate = 0;
            for (int i = 0; i < s->units && sp_visit(s); i++) {
                SpClause old = s->clause[s->unit[i]];
                if (old.count != c.count || old.variables != c.variables) continue;
                int same = 1;
                for (int j = 0; j < c.count; j++) {
                    int present = 0;
                    for (int k = 0; k < old.count; k++)
                        present |= old.literal[k].negative == c.literal[j].negative && sp_same_atom(old.literal[k], c.literal[j]);
                    same &= present;
                }
                duplicate |= same;
            }
            if (duplicate) { s->clause[id].stage = SP_DELETED; continue; }
            if (s->units == INT_MAX || !sp_reserve(s, (void **)&s->unit, &s->unit_cap, (size_t)s->units + 1, sizeof *s->unit)) {
                s->limited = 1; return;
            }
            s->unit[s->units++] = id;
            for (int i = 0; i < id && s->empty < 0 && sp_visit(s); i++)
                if (s->clause[i].stage != SP_DELETED && s->clause[i].stage != SP_HELD && s->clause[i].stage != SP_LOCKED) sp_unit_resolve(s, i, id);
        } else for (int i = 0; i < s->units && s->empty < 0 && sp_visit(s); i++)
            if (sp_unit_resolve(s, id, s->unit[i])) break;
    }
}

/* Il ciclo given-clause. Le semplificazioni conservano le loro deduzioni;
 * i genitori elaborati restano indirizzabili anche quando diventano
 * ridondanti. Una coda vuota senza contraddizione restituisce sconosciuto. */
static int sp_search(SpState *s) {
    if (s->expansions && !s->expansion[s->expansions - 1].complete) { s->limited = 1; s->resumable = 0; return 0; }
    while (s->empty < 0 && sp_visit(s)) {
        if (s->comprehension) {
            sp_seed_comprehensions(s);
            if (s->empty >= 0 || s->limited) break;
            sp_eliminate_comprehensions(s);
            if (s->empty >= 0 || s->limited) break;
            sp_unit_propagate(s);
            if (s->empty >= 0 || s->limited) break;
        }
        if (s->avatar && (!sp_avatar_update(s) || s->empty >= 0)) break;
        if (s->avatar && s->avatar_dirty) continue;
        int given = sp_select(s);
        if (s->limited) break;
        if (given < 0) {
            if (s->comprehension && s->seed_schema < s->schemas) continue;
            break;
        }
        int last = s->clauses, redundant = 0;
        sp_scratch_reset(s);
        for (int i = 0; i < last && !redundant && sp_visit(s); i++)
            if (s->clause[i].stage == SP_ACTIVE && sp_subsumes(s, s->clause[i], s->clause[given])) redundant = 1;
        if (redundant) { s->clause[given].stage = SP_DELETED; continue; }
        for (int i = 0; i < last && !redundant && sp_visit(s); i++)
            if (s->clause[i].stage == SP_ACTIVE) redundant = sp_demodulate(s, i, given);
        if (redundant) continue;
        s->clause[given].stage = SP_ACTIVE;
        if (s->comprehension) sp_propose_comprehensions(s, given);
        sp_unary(s, given);
        if (s->avatar && s->avatar_dirty) {
            if (s->clause[given].stage == SP_ACTIVE) s->clause[given].stage = SP_PENDING;
            continue;
        }
        for (int i = 0; i < last && s->empty < 0 && s->clause[given].stage == SP_ACTIVE && sp_visit(s); i++) {
            if (s->clause[i].stage != SP_ACTIVE) continue;
            sp_resolve(s, given, i);
            if (s->avatar && s->avatar_dirty) break;
            if (s->empty < 0) sp_superpose(s, given, i);
            if (s->avatar && s->avatar_dirty) break;
            if (i != given && s->empty < 0) sp_superpose(s, i, given);
            if (s->avatar && s->avatar_dirty) break;
        }
        /* Una nuova regola unitaria riscrive anche clausole gia in coda o
         * elaborate: le versioni nuove torneranno nella coda equa. */
        for (int i = 0; i < last && s->empty < 0 && (!s->avatar || !s->avatar_dirty) && sp_visit(s); i++)
            if (i != given && s->clause[i].stage != SP_DELETED &&
                s->clause[i].stage != SP_HELD && s->clause[i].stage != SP_LOCKED) sp_demodulate(s, given, i);
        if (s->avatar && s->avatar_dirty && s->clause[given].stage == SP_ACTIVE) s->clause[given].stage = SP_PENDING;
    }
    return s->empty >= 0 && !s->limited && !s->unsupported;
}

/* Conta o raccoglie i simboli originali distinti di un termine. stamp e
 * l'indice della clausola piu uno, seen evita di contare ripetizioni.
 * frequency e list possono essere NULL: i due passaggi condividono la
 * stessa visita, ma il primo conta e il secondo scrive lo spazio esatto. */
static void sp_sine_term(SpState *s, int term, int stamp, int *seen,
                          size_t *frequency, int *list, size_t *used) {
    if (term <= 0 || !sp_visit(s)) return;
    SpTerm t = s->term[term];
    if (t.symbol < s->inputs && seen[t.symbol] != stamp) {
        seen[t.symbol] = stamp;
        if (*used == (size_t)-1) { s->limited = 1; return; }
        if (frequency) frequency[t.symbol]++;
        if (list) list[*used] = t.symbol;
        (*used)++;
    }
    for (int i = 0; i < t.count; i++) sp_sine_term(s, s->argument[t.first + i], stamp, seen, frequency, list, used);
}

/* Costruisce le incidenze in due passaggi. Ogni simbolo e contato una sola
 * volta per clausola, anche in f(f(x)); Skolem, domini e Tseitin non
 * collegano ipotesi altrimenti distinte soltanto perche sono nomi tecnici.
 * Nessuna clausola viene cambiata, omessa dal deposito o rinumerata.
 * Richiede una clausificazione completa; ritorna uno per l'indice completo,
 * zero se le risorse non sono bastate a costruirlo. */
static int sp_sine_prepare(SpState *s) {
    if (s->limited || s->unsupported) return 0;
    SpSine *g = &s->sine;
    g->first = sp_allocate(s, &s->storage, (size_t)s->initial + 1, sizeof *g->first);
    g->reverse = sp_allocate(s, &s->storage, (size_t)s->inputs + 1, sizeof *g->reverse);
    g->frequency = sp_allocate(s, &s->storage, (size_t)s->inputs, sizeof *g->frequency);
    g->minimum = sp_allocate(s, &s->storage, (size_t)s->initial, sizeof *g->minimum);
    int *seen = sp_allocate(s, &s->scratch, (size_t)s->inputs, sizeof *seen);
    if (s->limited) return 0;
    if (s->inputs) { memset(seen, 0, (size_t)s->inputs * sizeof *seen); memset(g->frequency, 0, (size_t)s->inputs * sizeof *g->frequency); }
    g->first[0] = 0;
    for (int i = 0; i < s->initial && sp_visit(s); i++) {
        size_t used = 0;
        SpClause c = s->clause[i];
        for (int j = 0; j < c.count; j++) {
            sp_sine_term(s, c.literal[j].left, i + 1, seen, g->frequency, NULL, &used);
            sp_sine_term(s, c.literal[j].right, i + 1, seen, g->frequency, NULL, &used);
        }
        if (used > (size_t)-1 - g->first[i]) { s->limited = 1; return 0; }
        g->first[i + 1] = g->first[i] + used;
    }
    if (s->limited) return 0;
    size_t edges = g->first[s->initial];
    g->symbol = sp_allocate(s, &s->storage, edges, sizeof *g->symbol);
    g->clause = sp_allocate(s, &s->storage, edges, sizeof *g->clause);
    size_t *next = sp_allocate(s, &s->scratch, (size_t)s->inputs, sizeof *next);
    if (s->limited) return 0;
    g->reverse[0] = 0;
    for (int i = 0; i < s->inputs; i++) { g->reverse[i + 1] = g->reverse[i] + g->frequency[i]; next[i] = g->reverse[i]; seen[i] = 0; }
    for (int i = 0; i < s->initial && sp_visit(s); i++) {
        size_t used = 0, minimum = (size_t)-1;
        SpClause c = s->clause[i];
        int *list = edges ? g->symbol + g->first[i] : NULL;
        for (int j = 0; j < c.count; j++) {
            sp_sine_term(s, c.literal[j].left, i + 1, seen, NULL, list, &used);
            sp_sine_term(s, c.literal[j].right, i + 1, seen, NULL, list, &used);
        }
        for (size_t j = 0; j < used && sp_visit(s); j++) {
            int symbol = list[j];
            if (g->frequency[symbol] < minimum) minimum = g->frequency[symbol];
            g->clause[next[symbol]++] = i;
        }
        g->minimum[i] = used ? minimum : 0;
    }
    return !s->limited;
}

/* Segna i simboli originali di un elemento della tesi, traducendo i posti
 * del parser nell'ordine del certificato. Le variabili non sono simboli. */
static void sp_sine_goal_term(SpState *s, const Elem *e, unsigned char *goal) {
    if (!e || !sp_visit(s)) return;
    if (e->symbol >= 0 && e->symbol < declared_symbols && s->input_symbol[e->symbol] >= 0)
        goal[s->input_symbol[e->symbol]] = 1;
    sp_sine_goal_term(s, e->arg[0], goal); sp_sine_goal_term(s, e->arg[1], goal);
}

/* La tesi fornisce i simboli inizialmente rilevanti; le ipotesi non li
 * diventano soltanto perche sono scritte nell'enunciato da dimostrare. */
static void sp_sine_goal(SpState *s, const Sentence *n, unsigned char *goal) {
    if (!n || !sp_visit(s)) return;
    sp_sine_goal_term(s, n->left, goal); sp_sine_goal_term(s, n->right, goal);
    sp_sine_goal(s, n->a, goal); sp_sine_goal(s, n->b, goal);
}

/* Chiusura dei trigger di SInE. Un simbolo rilevante s attiva C se la sua
 * frequenza non supera tolerance volte il minimo di C; C rende rilevanti
 * tutti i suoi simboli. Le clausole senza simboli originali sono tenute.
 * Si visitano liste inverse, non tutte le clausole per ogni nuovo simbolo.
 * Richiede sp_sine_prepare riuscita. selected ha initial celle e viene
 * riempito; tolerance deve essere >0. Ritorna uno se la chiusura e completa,
 * zero con limited se le risorse non sono bastate. */
static int sp_sine_select(SpState *s, const unsigned char *goal, unsigned tolerance, unsigned char *selected) {
    if (s->limited || s->unsupported) return 0;
    const SpSine *g = &s->sine;
    int *queue = sp_allocate(s, &s->scratch, (size_t)s->inputs, sizeof *queue);
    unsigned char *relevant = sp_allocate(s, &s->scratch, (size_t)s->inputs, 1);
    if (s->limited) return 0;
    int count = 0;
    for (int i = 0; i < s->inputs; i++) { relevant[i] = goal[i]; if (goal[i]) queue[count++] = i; }
    for (int i = 0; i < s->initial; i++) selected[i] = g->minimum[i] == 0;
    for (int at = 0; at < count && sp_visit(s); at++) {
        int symbol = queue[at];
        for (size_t j = g->reverse[symbol]; j < g->reverse[symbol + 1] && sp_visit(s); j++) {
            int clause = g->clause[j]; size_t minimum = g->minimum[clause];
            if (selected[clause] || (minimum <= (size_t)-1 / tolerance && g->frequency[symbol] > tolerance * minimum)) continue;
            selected[clause] = 1;
            for (size_t k = g->first[clause]; k < g->first[clause + 1] && sp_visit(s); k++) {
                int next = g->symbol[k];
                if (!relevant[next]) { relevant[next] = 1; queue[count++] = next; }
            }
        }
    }
    return !s->limited;
}

/* Portafoglio in ordine: SInE stretto, SInE con tolleranza due e maggiore
 * frequenza delle scelte per eta, AVATAR, infine il ciclo ordinario con
 * tutte le ipotesi. AVATAR ha meta del lavoro rimasto e un secondo CPU;
 * le sue definizioni e clausole conservano validita nella ripartenza.
 * Ogni tentativo filtrato ha al piu un ottavo del lavoro rimasto e un
 * quarto di secondo CPU; con formule su parti usa un trentaduesimo,
 * perche i filtri FO non ne generano ancora le istanze. L'ultimo usa
 * il budget globale. Una firma vuota o un insieme gia
 * ristretto al massimo non richiedono ricerche filtrate ridondanti.
 * s contiene la clausificazione completa di root. Ritorna uno soltanto
 * per una refutazione, zero per una ricerca incompleta; tutti i passi
 * continuano a riferirsi alle clausole originali. */
static int sp_portfolio(SpState *s, const Sentence *root) {
    if (s->limited || s->unsupported) return 0;
    if (s->empty >= 0 || !s->inputs) { s->comprehension = s->schemas != 0; return sp_search(s); }
    sp_scratch_reset(s);
    if (!sp_sine_prepare(s)) return 0;
    unsigned char *goal = sp_allocate(s, &s->storage, (size_t)s->inputs, 1);
    if (!goal) return 0;
    memset(goal, 0, (size_t)s->inputs);
    sp_sine_goal(s, root->kind == S_IMPLIES ? root->b : root, goal);
    if (s->limited) return 0;
    for (int phase = 1; phase <= 4; phase++) {
        s->strategy = phase;
        s->quota = 0; s->cpu_quota = 0;
        s->avatar = phase == 3;
        s->comprehension = phase >= 3 && s->schemas != 0;
        if (phase == 3) s->avatar_dirty = 1;
        if (phase == 4) sat_clear(&s->sat);
        sp_scratch_reset(s);
        unsigned char *selected = NULL;
        if (phase < 3) {
            selected = sp_allocate(s, &s->scratch, (size_t)s->initial, 1);
            if (s->initial && !selected) return 0;
            if (!sp_sine_select(s, goal, (unsigned)phase, selected)) return 0;
        }
        int held = sp_requeue(s, selected);
        if (s->limited) return 0;
        if (phase < 3) {
            unsigned long long share = (saturation_work_limit - s->work) / (s->schemas ? 32 : 8);
            if (!held || !share) continue;
            s->quota = s->work + share;
            s->started = clock(); s->cpu_quota = CLOCKS_PER_SEC / 4 ? CLOCKS_PER_SEC / 4 : 1;
        } else if (phase == 3) {
            unsigned long long share = (saturation_work_limit - s->work) / 2;
            if (!share) continue;
            s->quota = s->work + share;
            s->started = clock(); s->cpu_quota = CLOCKS_PER_SEC;
        }
        s->age_interval = phase == 2 ? 2 : 5;
        if (sp_search(s)) { s->quota = 0; s->cpu_quota = 0; return 1; }
        if (s->limited && !s->resumable) return 0;
        s->limited = s->resumable = 0;
    }
    s->quota = 0; s->cpu_quota = 0;
    return 0;
}

/* Scrive un termine nel protocollo indipendente. I simboli sono numeri
 * della traduzione, non posti nella tabella di termini del motore. */
static void sp_cert_term(const SpState *s, int t) {
    if (t < 0) { cert_add("(v %d)", -t - 1); return; }
    SpTerm n = s->term[t];
    cert_add("(f %d", n.symbol);
    for (int i = 0; i < n.count; i++) { cert_add(" "); sp_cert_term(s, s->argument[n.first + i]); }
    cert_add(")");
}

/* Scrive la clausola normalizzata che il checker deve ritrovare esattamente. */
static void sp_cert_clause(const SpState *s, SpClause c) {
    cert_add("(clause");
    for (int i = 0; i < c.count; i++) {
        SpLiteral l = c.literal[i];
        if (!l.left) cert_add(l.negative ? " (false)" : " (true)");
        else {
            cert_add(" (%s ", l.right ? l.negative ? "ne" : "eq" : l.negative ? "neg" : "pos");
            sp_cert_term(s, l.left);
            if (l.right) { cert_add(" "); sp_cert_term(s, l.right); }
            cert_add(")");
        }
    }
    cert_add(")");
}

/* Nomi matematici dei simboli introdotti: D per i domini, k per Skolem,
 * P per le sottoformule. I simboli dichiarati conservano la loro scrittura. */
static void sp_put_term(const SpState *s, int t) {
    if (t < 0) { proof_add("x_{%d}", -t - 1); return; }
    SpTerm n = s->term[t];
    if (n.symbol < s->inputs) put_symbol(s->original_symbol[n.symbol]);
    else if (s->symbol[n.symbol].component) proof_add("b_{%d}", s->symbol[n.symbol].component - 1);
    else if (n.symbol < s->inputs + sort_count) proof_add("D_{%d}", n.symbol - s->inputs);
    else proof_add("%s_{%d}", s->symbol[n.symbol].predicate ? "P" : "k", n.symbol);
    if (n.count) proof_add("(");
    for (int i = 0; i < n.count; i++) { if (i) proof_add(","); sp_put_term(s, s->argument[n.first + i]); }
    if (n.count) proof_add(")");
}

/* Rende una disgiunzione come formula; la clausola vuota e il falso. */
static void sp_put_clause(const SpState *s, SpClause c) {
    if (!c.count) { proof_add("\\bot"); return; }
    for (int i = 0; i < c.count; i++) {
        SpLiteral l = c.literal[i];
        if (i) proof_add(" \\lor ");
        if (!l.left) proof_add(l.negative ? "\\bot" : "\\top");
        else {
            if (!l.right && l.negative) proof_add("\\lnot ");
            sp_put_term(s, l.left);
            if (l.right) { proof_add(l.negative ? " \\ne " : " = "); sp_put_term(s, l.right); }
        }
    }
}

/* Scrive gli antenati del vuoto e tutti i comandi che introducono nomi.
 * I comandi mantengono la firma e gli indici anche quando la loro prima
 * clausola non e fra gli antenati. Le clausole iniziali mantengono
 * i loro indici; gli altri passi vengono rinumerati dopo quelle iniziali,
 * cosi omettere ricerche inutilizzate non cambia un riferimento del checker. */
static void sp_write(SpState *s, const Sentence *root, const Sentence *const *laws, int law_count, long long compared) {
    if (s->empty < 0 || (s->expansions && !s->expansion[s->expansions - 1].complete)) { s->limited = 1; return; }
    sp_scratch_reset(s);
    unsigned char *needed = sp_allocate(s, &s->scratch, (size_t)s->clauses, 1);
    int *number = sp_allocate(s, &s->scratch, (size_t)s->clauses, sizeof *number);
    if (!needed || !number) return;
    memset(needed, 0, (size_t)s->clauses);
    needed[s->empty] = 1;
    for (int i = s->empty; i >= s->initial; i--) if (needed[i]) {
        SpStep step = s->clause[i].step;
        if (step.rule == SP_COMPONENT || step.rule == SP_COMPLEMENT || step.rule == SP_COMPREHEND) continue;
        needed[step.p] = 1;
        if (step.rule == SP_RESOLVE || step.rule == SP_SUPER) needed[step.q] = 1;
    }
    int count = s->initial;
    for (int i = 0; i < s->clauses; i++) number[i] = i < s->initial ? i : -1;
    /* I comandi non dipendono da genitori FO: le proprieta sono formule,
     * non fatti assunti. Si possono anticipare ai passi conservando il
     * loro ordine comune, necessario per simboli e formule annidate. */
    for (int i = 0; i < s->introductions; i++) {
        SpIntroduction event = s->introduction[i];
        if (event.kind == SP_COMPONENT) {
            SpComponent c = s->component[event.index];
            if (count > INT_MAX - 2) { s->limited = 1; return; }
            if (c.forward >= 0) number[c.forward] = count;
            count++;
            if (!c.key.variables && c.key.count == 1) {
                if (c.reverse >= 0) number[c.reverse] = count;
                count++;
            }
        } else {
            SpExpansion e = s->expansion[event.index];
            if (!e.complete || e.past - e.first > INT_MAX - count) { s->limited = 1; return; }
            for (int j = e.first; j < e.past; j++) number[j] = count++;
        }
    }
    for (int i = s->initial; i < s->clauses; i++) if (needed[i] && s->clause[i].step.rule != SP_COMPONENT &&
            s->clause[i].step.rule != SP_COMPLEMENT && s->clause[i].step.rule != SP_COMPREHEND) {
        if (count == INT_MAX) { s->limited = 1; return; }
        number[i] = count++;
    }
    cert_abstract_head("saturation", root, NULL);
    for (int i = 0; i < law_count; i++) { cert_add("axiom "); cert_sentence(laws[i], SLOT_VALUES_EMPTY); cert_add("\n"); }
    cert_add(s->forward ? "clausify forward\n" : "clausify\n");
    proof_reset(); proof_growable = 1;
    proof_add("\\textbf{Proof.} By contradiction and saturation. Each domain predicate $D_i$ denotes membership in its set. "
              "Negation normal form, Skolem functions with their universal parameters, and predicates for subformulas give clauses; "
              "all free variables of each clause are universal and are renamed apart before an inference. "
              "The initial clauses used below and every derived step are:\n\\begin{itemize}\n");
    for (int i = 0; i < s->introductions; i++) {
        SpIntroduction event = s->introduction[i];
        if (event.kind == SP_COMPONENT) {
            SpComponent c = s->component[event.index];
            cert_add("component "); sp_cert_clause(s, c.key); cert_add("\n");
            if (!c.key.variables && c.key.count == 1) cert_add("complement %d\n", event.index);
            proof_add("\\item Define $b_{%d}\\iff ", event.index);
            for (int j = 0; j < c.key.variables; j++) proof_add("\\forall x_{%d}\\ ", j);
            proof_add("("); sp_put_clause(s, c.key); proof_add(")$.\n");
        } else {
            SpExpansion e = s->expansion[event.index];
            SpClause property = {.count=1, .literal=&e.property};
            cert_add("comprehend %d ", e.schema); sp_cert_clause(s, property); cert_add("\n");
            proof_add("\\item Instantiate the universal part formula $ ");
            SpSchema schema = s->schema[e.schema];
            put_sentence(schema.source, !schema.positive, SLOT_VALUES_EMPTY, 0);
            proof_add("$ with $\\{x_0\\in "); put_sort(symbols[schema.source->part].domain[0]);
            proof_add("\\mid "); sp_put_clause(s, property); proof_add("\\}$.\n");
        }
    }
    static const char *const rule[] = {"input", "resolve", "reflex", "factor", "super", "equalfactor", "component", "complement", "split", "comprehend"};
    static const char *const description[] = {"clausification", "resolution", "equality resolution", "factoring", "superposition", "equality factoring", "component definition", "ground complement", "variable-disjoint splitting", "comprehension instantiation"};
    for (int i = 0; i < s->clauses; i++) {
        SpClause c = s->clause[i]; SpStep step = c.step;
        if (!needed[i]) continue;
        proof_add("\\item $(C_{%d})\\quad ", number[i]); sp_put_clause(s, c); proof_add("$.");
        if (i < s->initial) { proof_add(" By clausification.\n"); continue; }
        if (step.rule == SP_COMPONENT || step.rule == SP_COMPLEMENT) { proof_add(" By %s.\n", description[step.rule]); continue; }
        if (step.rule == SP_COMPREHEND) { proof_add(" By comprehension and clausification.\n"); continue; }
        proof_add(" By %s from $(C_{%d})$", description[step.rule], number[step.p]);
        if (step.rule == SP_RESOLVE || step.rule == SP_SUPER) proof_add(" and $(C_{%d})$", number[step.q]);
        if (step.bindings) {
            proof_add(", with $");
            for (int j = 0; j < step.bindings; j++) {
                if (j) proof_add(",\\ ");
                proof_add("x_{%d}\\mapsto ", step.binding[j].variable); sp_put_term(s, step.binding[j].term);
            }
            proof_add("$");
        }
        proof_add(".\n");
        if (step.rule == SP_SPLIT) {
            cert_add("step split %d (groups", number[step.p]);
            for (int j = 0; j < step.groups; j++) {
                SpGroup g = step.group[j];
                cert_add(" (%d %d", g.component, g.negative);
                for (int k = 0; k < g.count; k++) cert_add(" %d", g.literal[k]);
                cert_add(")");
            }
            cert_add(") "); sp_cert_clause(s, c); cert_add("\n");
            continue;
        }
        cert_add("step %s %d %d", rule[step.rule], number[step.p], step.lp);
        if (step.rule == SP_RESOLVE) cert_add(" %d %d", number[step.q], step.lq);
        else if (step.rule == SP_SUPER) cert_add(" %d %d %d %d %d", step.flip, number[step.q], step.lq, step.side, step.position);
        else if (step.rule == SP_FACTOR) cert_add(" %d", step.lq);
        else if (step.rule == SP_EQUAL_FACTOR) cert_add(" %d %d %d", step.flip, step.lq, step.otherflip);
        cert_add(" (subst");
        for (int j = 0; j < step.bindings; j++) {
            cert_add(" (%d ", step.binding[j].variable); sp_cert_term(s, step.binding[j].term); cert_add(")");
        }
        cert_add(") "); sp_cert_clause(s, c); cert_add("\n");
    }
    cert_add("end\n");
    proof_add("\\end{itemize}\nThe empty clause is a contradiction. Every inference and the initial clausification "
              "are checked independently by the certificate verifier.");
    put_unfolding_note(compared); proof_add(" $\\Box$");
}

/* Nodi trattati dalla saturazione: primo ordine e astrazioni dei
 * quantificatori su parti con istanze di comprensione. Una parte non viene
 * confusa con un elemento; l'equipotenza conserva la propria strategia. */
static int sp_supported_formula(const Sentence *root) {
    switch (root->kind) {
    case S_TRUE: case S_EQUAL: case S_HOLDS: return 1;
    case S_NOT: case S_FORALL: case S_EXISTS: case S_FORALL_PART: case S_EXISTS_PART: return sp_supported_formula(root->a);
    case S_AND: case S_OR: case S_IMPLIES: case S_IFF: return sp_supported_formula(root->a) && sp_supported_formula(root->b);
    default: return 0;
    }
}

/* Dentro Vampire (LOGIC_CLAUSES). Nodi che la traduzione in clausole sa
 * scrivere per chi cerca la refutazione altrove: quelli di
 * sp_supported_formula() e in più l'equipotenza tra due insiemi (non tra
 * prodotti), che tra le clausole si può usare e non dimostrare (11m-e di
 * checker.c). La saturazione di questo capitolo continua a non
 * incontrarla: per l'equipotenza ha i testimoni di 28q, che la sanno anche
 * dimostrare, e vengono prima. */
static int sp_handed_formula(const Sentence *root) {
    switch (root->kind) {
    case S_TRUE: case S_EQUAL: case S_HOLDS: return 1;
    case S_EQUIPOTENT: return root->sides[0] == 1 && root->sides[1] == 1;
    case S_NOT: case S_FORALL: case S_EXISTS: case S_FORALL_PART: case S_EXISTS_PART: return sp_handed_formula(root->a);
    case S_AND: case S_OR: case S_IMPLIES: case S_IFF: return sp_handed_formula(root->a) && sp_handed_formula(root->b);
    default: return 0;
    }
}

/* Cerca una refutazione e la consegna soltanto attraverso ck_check.
 * Ritorna uno se e arrivata al controllo di un certificato, compreso un
 * eventuale rifiuto che deve restare visibile come errore del motore.
 * Zero significa ricerca incompleta: le altre strategie possono proseguire. */
static int saturation_attempt(const Sentence *root, const Sentence *const *laws, int law_count,
                               long long compared, Verdict *verdict) {
    if (!sp_supported_formula(root)) return 0;
    SpState state = {0};
    if (!sp_prepare(&state, root, laws, law_count) || !sp_portfolio(&state, root)) { sp_clear(&state); return 0; }
    /* Se il vuoto e gia nella negazione della tesi, non servono leggi
     * aggiuntive dopo di esso: si riscrive la sola refutazione della tesi. */
    if (state.empty < state.initial && state.empty + 1 < state.initial) {
        sp_clear(&state);
        if (!sp_prepare(&state, root, NULL, 0) || !sp_portfolio(&state, root)) { sp_clear(&state); return 0; }
        law_count = 0;
    }
    sp_write(&state, root, laws, law_count, compared);
    if (state.limited || proof_broken) { sp_clear(&state); return 0; }
    verdict->outcome = PROVED;
    verdict->method = "per saturazione di clausole";
    verdict->proof = proof_text;
    *verdict = abstract_certified(*verdict);
    sp_clear(&state);
    return 1;
}

/* Dentro Vampire (LOGIC_CLAUSES, più sotto). Aggiunge alle clausole
 * iniziali di s le istanze delle formule universali su parti che si possono
 * proporre senza cercare, perché chi cercherà la refutazione, Vampire, non
 * sa scegliere una parte: per lui una formula su parti senza istanze è un
 * nome senza vincoli (11m di checker.c).
 *
 *   - La parte vuota e la parte intera, per ogni formula
 *     (sp_seed_comprehensions()), comprese le formule che nascono dentro
 *     un'istanza.
 *   - Per ogni letterale chiuso L[c] delle clausole iniziali, scritto con i
 *     simboli dell'enunciato, e ogni costante c che vi compare, la proprietà
 *     complementare "non L[x]" (sp_propose_term()). È la scelta che 28u fa
 *     sulle clausole unitarie mentre satura; qui la saturazione viene dopo
 *     e la fa un altro, quindi si guardano tutti i letterali iniziali: tra
 *     loro c'è la tesi negata, con le sue costanti di Skolem, ed è lei che
 *     dice quale parte serve (per "f(y) = y per ogni y" con un principio di
 *     induzione tra le ipotesi, la parte degli x con f(x) = x).
 *
 * Nessuna di queste istanze è un'ipotesi in più: ognuna è "la formula vale
 * per ogni parte, quindi per questa", e il verificatore la ricostruisce da
 * sé dalla riga comprehend. Ritorna 0 se un'istanza è rimasta a metà (il
 * budget di lavoro, o una forma che la traduzione non sa): chi chiama deve
 * allora ripartire dalle sole clausole iniziali, perché un gruppo parziale
 * non si consegna. */
static int sp_static_comprehensions(SpState *s) {
    int initial = s->clauses;
    while (s->seed_schema < s->schemas && !s->limited && !s->unsupported) sp_seed_comprehensions(s);
    for (int i = 0; i < initial && !s->limited && !s->unsupported; i++) {
        /* La clausola si rilegge a ogni letterale: un'istanza aggiunge
         * clausole, e il deposito può essersi spostato. */
        for (int j = 0; j < s->clause[i].count && !s->limited && !s->unsupported; j++) {
            SpLiteral l = s->clause[i].literal[j];
            if (sp_guard(s, l)) continue;
            if (!l.left || (!l.right && (l.left < 0 || s->term[l.left].symbol >= s->inputs))) continue;
            if (!sp_ground_term(s, l.left) || !sp_ground_term(s, l.right)) continue;
            sp_propose_term(s, l, l.left);
            sp_propose_term(s, l, l.right);
        }
    }
    while (s->seed_schema < s->schemas && !s->limited && !s->unsupported) sp_seed_comprehensions(s);
    return !s->limited && !s->unsupported;
}

int logic_task = LOGIC_DECIDE;
const char *const LOGIC_HANDED_OVER = "la ricerca è consegnata al dimostratore che ospita il motore";

/* Il modello ricevuto per LOGIC_ADOPT_MODEL, preso in prestito da chi
 * chiama: una grandezza per insieme, nell'ordine delle voci sort
 * dell'enunciato consegnato, e una tabella per simbolo dichiarato,
 * nell'ordine delle voci symbol, con le celle nell'ordine dei modelli di
 * questo capitolo (il primo argomento cambia più in fretta). */
const size_t *adopted_sizes;
const size_t *const *adopted_tables;
const size_t *adopted_cells;   /* quante celle ha ogni tabella */
int adopted_sorts, adopted_symbols;

/* Carica in m il modello ricevuto. Ritorna 0 se non è un'interpretazione
 * dei simboli dell'enunciato in corso: un numero diverso di insiemi o di
 * tabelle, una tabella con un numero di celle diverso da quello che le
 * grandezze chiedono, un valore fuori dal suo insieme, un'applicazione da
 * un insieme con elementi a uno vuoto. Nulla di ciò che arriva è creduto:
 * chi chiama ricalcola poi l'enunciato nel modello (abstract_model_result()).
 * Le grandezze degli insiemi di parti e di applicazioni e le tabelle dei
 * loro simboli di struttura non si ricevono: si calcolano (28m). */
static int model_adopt(Model *m) {
    if (adopted_sorts != sort_count || !model_dimensions(m)) return 0;
    for (int i = 0; i < sort_count; i++) m->dimension[i].size = sort_data[i].kind == SORT_PLAIN ? adopted_sizes[i] : 0;
    if (!model_derived_sizes(m) || !model_allocate(m)) return 0;
    model_structure(m);

    /* Le tabelle, nell'ordine in cui cert_abstract_head() dichiara i simboli. */
    int given = 0;
    for (int s = 0; s < symbol_count; s++) {
        if (symbol_fixed(s) || symbol_bound[s]) continue;
        size_t cells, values = model_cells(m, s, &cells);
        if (given >= adopted_symbols || adopted_cells[given] != cells) return 0;
        for (size_t c = 0; c < cells; c++) {
            if (adopted_tables[given][c] >= values) return 0;
            m->table[s][c] = adopted_tables[given][c];
        }
        given++;
    }
    return given == adopted_symbols;
}

/* Decide l'enunciato su insiemi qualsiasi scritto in formula e ne ritorna
 * il verdetto, come descritto in testa al capitolo: prima i modelli finiti,
 * che possono smentirlo (o, se chiede un esempio, dimostrarlo); poi la
 * dimostrazione per assurdo di ogni affermazione della tesi. In tutti e due
 * i casi il verdetto vale solo con il certificato accettato (28f).
 *
 * Svuota l'arena: i risultati di chiamate precedenti non sono più validi. */
Verdict prove_abstract(const char *formula) {
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, "con istanze delle ipotesi e uguali al posto di uguali", NULL, NULL};
    static Model model;
    const Sentence *hypothesis[MAX_KNOWN / 8], *claim[MAX_KNOWN / 8];
    SlotValues nothing = SLOT_VALUES_EMPTY;
    long long tried;
    int bound;

    /* Ripartenza da zero e parsing. Il modello precedente non serve piu. */
    model_clear(&model);
    model_unconfirmed = NULL;
    proof_reset();
    arena_used = arena_keep;
    failure = NULL;
    syntax_error = NULL;
    cursor = formula;
    next_token();
    const Sentence *written = abstract_statement();

    /* L'arena piena viene prima di un errore di sintassi: il lettore,
     * fermato a metà, può averne annotato uno che non c'è ("manca la
     * parentesi chiusa"). Ed è una risorsa finita, non un enunciato che non
     * si sa leggere: NON DIMOSTRATO, come per la pila. */
    if (failure == OUT_OF_MEMORY) { verdict.outcome = NOT_PROVED; verdict.reason = OUT_OF_MEMORY; return verdict; }
    if (syntax_error || failure) { verdict.reason = syntax_error ? syntax_error : failure; return verdict; }

    declared_symbols = symbol_count;
    if (!proof_symbols_reserve((size_t)symbol_count)) { verdict.reason = OUT_OF_MEMORY; return verdict; }
    if (symbol_count) memset(symbol_generation, 0, (size_t)symbol_count * sizeof *symbol_generation);
    if (symbol_count) memset(symbol_law, 0, (size_t)symbol_count * sizeof *symbol_law);

    /* 17q, 28h. La notazione dei libri, se c'è, si svolge; e lo svolgimento
     * si ricontrolla sui modelli finiti prima di ragionare sull'enunciato
     * svolto. Se non è d'accordo con l'enunciato scritto è un errore del
     * programma: nessun verdetto. */
    const Sentence *root = written;
    long long compared = 0;
    if (sentence_has_book_notation(written)) {
        root = abstract_unfold(written);

        /* Anche l'arena piena: lo svolgimento raddoppia l'enunciato a ogni
         * \exists!, e con 22 uno dentro l'altro la riempie. L'albero
         * incompleto non va calcolato sui modelli. */
        if (failure == OUT_OF_MEMORY) { verdict.outcome = NOT_PROVED; verdict.reason = OUT_OF_MEMORY; return verdict; }
        if (syntax_error || failure) { verdict.reason = syntax_error ? syntax_error : failure; return verdict; }
        compared = book_check(written, root);
        if (compared < 0) {
            unjustified_steps++;
            verdict.outcome = NOT_PROVED;
            verdict.reason = "lo svolgimento della notazione degli insiemi, ricalcolato sui modelli finiti, non dà lo stesso enunciato";
            return verdict;
        }
        if (compared == 0) {
            verdict.outcome = NOT_PROVED;
            verdict.reason = "lo svolgimento della notazione degli insiemi non si è potuto ricontrollare: l'enunciato è troppo lungo da calcolare anche sul modello più piccolo";
            return verdict;
        }
    }

    /* La consegna (vedi "Dentro Vampire", sopra prove_abstract()). L'enunciato
     * è letto e il suo svolgimento ricontrollato: da qui in poi comincerebbe
     * la ricerca, che dentro Vampire non è di questo capitolo. Se la
     * notazione dei certificati non sa dire l'enunciato (certificate_broken)
     * non si consegna nulla, e chi chiama ripiega sul capitolo com'è. */
    int only_written_numbers = !plain_sorts() && !abstract_example;
    for (int s = 0; s < symbol_count && only_written_numbers; s++) only_written_numbers = symbol_fixed(s);
    if (logic_task == LOGIC_HAND_OVER && !only_written_numbers) {
        /* Le leggi (28n), preparate come le prepara più sotto la ricerca
         * di questo capitolo: se le lettere per scriverle non bastano, si
         * consegna l'enunciato senza. */
        const char *before_laws = syntax_error;
        axioms_prepare();
        if (syntax_error != before_laws) { axiom_count = 0; syntax_error = before_laws; }
        cert_abstract_head(abstract_example ? "example" : "counterexample", root, NULL);
        cert_axioms();
        verdict.outcome = NOT_PROVED;
        verdict.reason = LOGIC_HANDED_OVER;
        verdict.detail = certificate_broken ? NULL : certificate_text;
        return verdict;
    }

    /* Le clausole della saturazione (vedi sopra prove_abstract()). Ciò che
     * si consegna è l'inizio di un certificato saturation, fino alla riga
     * clausify compresa, seguito da due elenchi che del certificato non
     * fanno parte e che chi riceve stacca: i simboli della traduzione
     * (quanti argomenti, e se è un predicato), nell'ordine dei loro numeri,
     * e le clausole iniziali, nell'ordine dei loro indici. Sono gli stessi
     * numeri e gli stessi indici che il verificatore ricostruisce: lo
     * garantisce sp_prepare(), su cui poggiano già i certificati di 28u. */
    if (logic_task == LOGIC_CLAUSES) {
        verdict.outcome = NOT_PROVED;
        if (!sp_handed_formula(root)) {
            verdict.reason = "l'enunciato non ha una traduzione in clausole";
            return verdict;
        }
        /* Chi chiede un esempio di E è smentito da una prova che E non
         * vale in nessuna interpretazione, cioè da una prova di "non E".
         * Il certificato saturation refuta la negazione del suo enunciato:
         * con l'enunciato "non E" le clausole da cui parte sono quelle di
         * E, ed è proprio E che Vampire ha refutato. Chi riceve deve
         * leggere il certificato per ciò che dice: che l'esempio non c'è. */
        const Sentence *claimed = abstract_example ? axiom_join(S_NOT, (Sentence *)root, NULL) : root;
        const char *before_laws = syntax_error;
        axioms_prepare();
        if (syntax_error != before_laws) { axiom_count = 0; syntax_error = before_laws; }
        SpState clauses = {0};
        int prepared = sp_prepare(&clauses, claimed, axioms, axiom_count);
        /* Le istanze delle formule su parti; se una resta a metà si riparte
         * dalle sole clausole iniziali (sp_static_comprehensions()). */
        if (prepared && clauses.schemas && !sp_static_comprehensions(&clauses)) {
            sp_clear(&clauses);
            clauses = (SpState){0};
            prepared = sp_prepare(&clauses, claimed, axioms, axiom_count);
        }
        if (!prepared) {
            sp_clear(&clauses);
            verdict.reason = "la traduzione in clausole non è riuscita entro i limiti di memoria e di lavoro";
            return verdict;
        }
        cert_abstract_head("saturation", claimed, NULL);
        cert_axioms();
        cert_add(clauses.forward ? "clausify forward\n" : "clausify\n");
        /* Le righe comprehend, nell'ordine in cui le istanze sono nate: il
         * verificatore ne ricostruisce clausole e simboli nello stesso
         * ordine, in coda a quelli iniziali. */
        for (int i = 0; i < clauses.introductions; i++) {
            SpExpansion e = clauses.expansion[clauses.introduction[i].index];
            SpClause property = {.count=1, .literal=&e.property};
            cert_add("comprehend %d ", e.schema); sp_cert_clause(&clauses, property); cert_add("\n");
        }
        cert_add("symbols %d\n", clauses.symbols);
        for (int i = 0; i < clauses.symbols; i++) cert_add("%d %d\n", clauses.symbol[i].arity, clauses.symbol[i].predicate);
        cert_add("clauses %d\n", clauses.clauses);
        for (int i = 0; i < clauses.clauses; i++) { sp_cert_clause(&clauses, clauses.clause[i]); cert_add("\n"); }
        sp_clear(&clauses);
        verdict.reason = LOGIC_HANDED_OVER;
        verdict.detail = certificate_broken ? NULL : certificate_text;
        return verdict;
    }

    /* Il modello trovato da Vampire, da qui in poi un modello di questo
     * capitolo: abstract_model_result() lo ricalcola e lo certifica, o dice
     * che non conferma. */
    if (logic_task == LOGIC_ADOPT_MODEL) {
        if (!model_adopt(&model)) {
            verdict.outcome = NOT_PROVED;
            verdict.reason = "il modello ricevuto non è un'interpretazione dei simboli dell'enunciato";
            return verdict;
        }
        return abstract_model_result(verdict, written, root, &model, compared);
    }

    /* 28a. I modelli finiti. Per chi chiede un esempio, uno in cui la
     * condizione vale; per gli altri, uno in cui non vale. */
    int model_symbols = symbol_count;
    int found = model_search(root, abstract_example, &model, &tried, &bound);
    /* Prima una quota breve, poi la dimostrazione, infine il budget
     * rimasto. Un universale vero non consuma tutto il model finding prima
     * che le sue ipotesi siano usate. Le richieste di esempio usano subito
     * il budget intero, perche li la ricerca e tutto il procedimento. */
    unsigned long long first_work = abstract_example ? model_work_limit : model_work_limit / 16;
    if (!first_work) first_work = 1;
    unsigned long long remaining_work = model_work_limit - first_work;
    /* (Dentro Vampire, LOGIC_CERTIFY: il SAT dei modelli non si fa, qui e
     * più sotto. L'enunciato è già dimostrato; vedi sopra prove_abstract().) */
    if (!found && logic_task != LOGIC_CERTIFY) found = model_sat_slice(root, abstract_example, &model, &tried, bound, first_work);
    if (found) return abstract_model_result(verdict, written, root, &model, compared);
    verdict.outcome = NOT_PROVED;

    /* 17v, 28m. Un enunciato che parla solo dei numeri che scrive, con
     * relazioni date dall'elenco delle loro coppie, non ha nulla da scegliere:
     * i suoi insiemi sono quei numeri, tutti diversi, e ogni simbolo ha la
     * sua tabella. Ha un solo modello, e quello che vi si calcola è il suo
     * valore. Un conto finito e completo: se il modello non lo smentisce
     * (sopra), l'enunciato vale. Il verificatore rifà il conto sullo stesso
     * modello (11b e 11i in checker.c). */
    int concrete = !plain_sorts() && !abstract_example;
    for (int s = 0; s < symbol_count && concrete; s++) concrete = symbol_fixed(s);
    if (concrete && model_search(root, 1, &model, &tried, &bound)) {
        size_t *value = model_variables();
        if (work_allocation_failed) { verdict.reason = OUT_OF_MEMORY; return verdict; }
        model_steps = 0;
        int holds = model_holds(&model, root, value) && (written == root || book_holds(&model, written, value));
        if (!model_steps_complete()) {
            verdict.reason = "il conto sui numeri dell'enunciato supera il budget dei passi (--model-steps)";
            return verdict;
        }
        if (!holds) {
            unjustified_steps++;
            verdict.reason = "la verifica indipendente non conferma il conto sui numeri dell'enunciato";
            return verdict;
        }
        proof_add("\\textbf{Proof.} The statement speaks only of the numbers it writes, which are distinct and are all its elements, "
                  "and every set in it is given by the list of its members: there is nothing to choose, and computing with them "
                  "the statement holds.");
        put_unfolding_note(compared);
        proof_add(" $\\Box$");
        verdict.outcome = PROVED;
        verdict.method = "con un conto sui numeri dell'enunciato";
        verdict.proof = proof_text;
        cert_abstract_head("example", root, &model);
        cert_add("end\n");
        return abstract_certified(verdict);
    }
    if (abstract_example) {
        verdict.reason = model_unconfirmed ? model_unconfirmed : "nessun esempio trovato entro il budget di ricerca dei modelli: può essercene uno";
        return verdict;
    }

    /* 28u. La prova per clausole e controllata senza un campione finito:
     * puo quindi precedere la cautela che resta per la ricerca per istanze. */
    /* 28n. Le leggi delle parti e delle applicazioni, dopo le ipotesi:
     * anche loro sono condizioni vere, e il certificato le porta. Se le
     * lettere per scriverle non bastano, la ricerca va avanti senza. */
    const char *before_axioms = syntax_error;
    axioms_prepare();
    if (syntax_error != before_axioms) { axiom_count = 0; syntax_error = before_axioms; }
    bijection_prepare(root);
    if (saturation_attempt(root, axioms, axiom_count, compared, &verdict)) return verdict;
    proof_reset();

    /* Senza il controllo indipendente non si dimostra: se nemmeno i modelli
     * con un elemento per insieme sono stati provati tutti, ci si ferma. */
    if (bound < 1) {
        symbol_count = model_symbols;
        if (logic_task != LOGIC_CERTIFY && model_sat_slice(root, 0, &model, &tried, bound, remaining_work))
            return abstract_model_result(verdict, written, root, &model, compared);
        verdict.reason = model_unconfirmed ? model_unconfirmed : "i modelli con pochi elementi sono troppi per provarli: manca il controllo indipendente";
        return verdict;
    }

    /* 28b-28g. La dimostrazione: ipotesi e tesi, un'affermazione per
     * volta. */
    const Sentence *thesis = root->kind == S_IMPLIES ? root->b : root;
    int hypotheses = root->kind == S_IMPLIES ? conjuncts(root->a, hypothesis, 0, MAX_KNOWN / 8) : 0;
    int claims = conjuncts(thesis, claim, 0, MAX_KNOWN / 8), proved = 1;
    exhausted = part_interrupted = 0;
    if (!instance_sorts_reserve()) { verdict.reason=OUT_OF_MEMORY;return verdict; }
    memset(definition_slot,-1,(size_t)sort_count*sizeof *definition_slot);
    cert_abstract_head("structure", root, NULL);

    int given = hypotheses;
    for (int i = 0; i < axiom_count && hypotheses < MAX_KNOWN / 8; i++) hypothesis[hypotheses++] = axioms[i];
    cert_axioms();
    proof_add("\\textbf{Proof.} By contradiction: we suppose that the hypotheses hold and that a claim fails.");
    for (int i = 0; i < hypotheses; i++) {
        if (i == given) proof_add("%s Since every set of parts or of maps here is the set of all of them, these hold too:", given ? "." : "");
        proof_add("%s (H%d) $", i == given ? "" : i ? "," : " The hypotheses:", i + 1);
        put_sentence(hypothesis[i], 0, nothing, 0);
        proof_add("$");
    }
    proof_add("%s\n\\begin{itemize}\n", hypotheses ? "." : "");
    /* 28n. Ogni affermazione prima con le sole estensionalità, che non
     * fanno nascere elementi, poi, se non basta, con le comprensioni: le
     * parti in più servono a poche dimostrazioni e rallentano le altre. Gli
     * assiomi sono in coda alle ipotesi, le estensionalità per prime, quindi
     * la prima prova usa un pezzo iniziale dell'elenco, con gli stessi
     * numeri (H1), (H2), ... */
    int first_pass = given + axioms_extensional();
    for (int i = 0; i < claims && proved && !failure; i++)
        proved = claim_attempts(hypothesis, hypotheses, first_pass, claim[i]) || (!failure && claim_halves(hypothesis, hypotheses, first_pass, claim[i]));
    /* Nessuna dimostrazione trovata: la quota residua riprende il model
     * finding prima di emettere un esito sconosciuto. Anche dopo una ricerca
     * interrotta, un modello completo resta controllabile da solo. */
    if (!proved || failure) {
        symbol_count = model_symbols;
        if (logic_task != LOGIC_CERTIFY && model_sat_slice(root, 0, &model, &tried, bound, remaining_work))
            return abstract_model_result(verdict, written, root, &model, compared);
    }
    if (failure) {
        /* La memoria è finita durante la ricerca (le copie di 28j): ciò che
         * è stato scritto dopo non vale nulla. */
        verdict.reason = failure;
        return verdict;
    }
    if (!proved) {
        verdict.reason = model_unconfirmed ? model_unconfirmed
                       : exhausted || part_interrupted ? "la ricerca è stata interrotta: troppi elementi o troppe istanze senza arrivare a una dimostrazione"
                                   : "nessun controesempio trovato entro il budget dei modelli; le istanze provate non bastano a dimostrarlo";
        return verdict;
    }
    proof_add("\\end{itemize}\nIndependent check: no choice of nonempty sets with at most $%d$ element%s each, and of tables for what is declared, "
              "contradicts the statement (%lld were tried).", bound, bound == 1 ? "" : "s", tried);
    put_unfolding_note(compared);
    proof_add(" $\\Box$");

    /* Una dimostrazione troncata non è scritta: proof_add() si ferma a
     * PROOF_BYTES, e ciò che manca può essere un caso intero. Le
     * dimostrazioni di 28r sono le più lunghe del capitolo, e l'hanno
     * mostrato. */
    if (proof_length >= PROOF_BYTES - 1) {
        verdict.reason = "la dimostrazione trovata è più lunga di quanto il programma sappia scrivere";
        return verdict;
    }
    verdict.outcome = PROVED;
    verdict.proof = proof_text;

    /* Il certificato: i casi scritti da abstract_claim(), con i nomi e le
     * istanze dei rami (28f). */
    cert_add("end\n");
    return abstract_certified(verdict);
}
