/* MODULO engine_sets: relazioni tra insiemi: decisione per regioni, verifica
 * indipendente, dimostrazione scritta (capitoli 15-16).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in engine_sets.h, e il
 * resto è static. */
#include "engine_sets.h"
#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"
#include "engine_induction.h"

/* =============================================================================
 * 15. INSIEMI: DECISIONE PER REGIONI
 * ============================================================================
 *
 * Come si decide un enunciato che deve valere per ogni scelta degli insiemi.
 *
 * Regioni. Dati k insiemi, ogni elemento sta in esattamente una delle 2^k
 * regioni del diagramma di Venn: una regione è la scelta, per ciascun insieme,
 * tra "ci sta" e "non ci sta". Una regione è il numero i cui bit dicono a
 * quali insiemi appartiene: con S di indice 0 e T di indice 1, la regione 1 è
 * "in S e non in T".
 *
 * Il fatto su cui si regge tutto: se un oggetto appartiene o no a
 * un'espressione dipende solo dalle regioni che tocca.
 *
 *   15a. Un elemento x: da quale regione lo contiene. x sta in A unito B se
 *        sta in A o in B, e così via.
 *   15b. Un insieme X: da quali regioni incontra. X sta nell'insieme delle
 *        parti di A se X è contenuto in A, cioè se ogni regione che X incontra
 *        sta in A; sta in {vuoto} se non ne incontra nessuna.
 *   15c. Una coppia (x, y): dalle regioni di x e di y. Sta in A per B se x sta
 *        in A e y sta in B.
 *
 * Configurazioni. Per insiemi dati, alcune regioni contengono elementi e altre
 * sono vuote: questa è la "configurazione". Un'uguaglianza o un'inclusione tra
 * due espressioni fallisce quando esiste un oggetto che sta in una sola delle
 * due (per l'inclusione: nella prima e non nella seconda), e un tale oggetto
 * esiste quando le regioni che tocca sono tutte non vuote. Quindi ogni
 * relazione ha un elenco di "supporti", insiemi di regioni, e fallisce
 * esattamente nelle configurazioni che contengono per intero un supporto.
 *
 * Decisione. La verità di tutto l'enunciato dipende allora solo dalla
 * configurazione. Le configurazioni sono 2^(2^k), ognuna è realizzata da
 * qualche scelta degli insiemi (un elemento per ogni regione non vuota), e
 * ogni scelta degli insiemi ne realizza una. L'enunciato vale per ogni scelta
 * degli insiemi se e solo se vale in tutte le configurazioni: si provano
 * tutte. Con al più 4 insiemi sono al più 65536.
 *
 * Il metodo decide davvero, in entrambi i sensi: un enunciato che fallisce in
 * una configurazione è falso, e la configurazione dà un controesempio.
 *
 * Il quantificatore "esiste un insieme V". Non si può trattare V come gli
 * altri insiemi, perché V va scelto, non è arbitrario. Due casi:
 *
 *   15d. "Esiste V" è un'ipotesi (sta a sinistra di un'implicazione). Dire
 *        "se esiste V con una certa proprietà allora C" equivale a dire "per
 *        ogni V, se V ha la proprietà allora C": V diventa un insieme
 *        arbitrario come gli altri.
 *   15e. "Esiste V" è una tesi. Si cerca un V esplicito costruito dagli altri
 *        insiemi, cioè un'unione di loro regioni: si provano tutte. Trovarlo
 *        dimostra l'esistenza. Non trovarlo non prova nulla, perché V potrebbe
 *        dover dividere una regione: allora si passa a 15f.
 *   15f. Più quantificatori, o in un'altra posizione, o un V che 15e non
 *        trova. Non basta più sapere quali regioni sono vuote: si contano i
 *        loro elementi, fino a un numero che dipende da quanti quantificatori
 *        stanno uno dentro l'altro. È descritto più sotto, con il suo teorema.
 */

/* Ritorna 1 se l'oggetto descritto da u e v appartiene all'espressione n.
 * Il significato di u e v dipende dal tipo di n (vedi 15a, 15b, 15c):
 *
 *   insieme di elementi:    u è la regione dell'elemento;
 *   collezione di insiemi:  u ha un bit per ogni regione che l'insieme incontra;
 *   insieme di coppie:      u e v sono le regioni delle due componenti. */
static int member(const SetNode *n, unsigned u, unsigned v) {
    switch (n->kind) {
    case SET_VAR:        return (u >> n->var) & 1;
    case SET_ONLY_EMPTY: return u == 0;
    case SET_POWER:
        for (unsigned region = 0; u >> region; region++)
            if (((u >> region) & 1) && !member(n->a, region, 0)) return 0;
        return 1;
    case SET_PRODUCT:    return member(n->a, u, 0) && member(n->b, v, 0);
    case SET_UNION:      return member(n->a, u, v) || member(n->b, u, v);
    case SET_INTER:      return member(n->a, u, v) && member(n->b, u, v);
    case SET_DIFF:       return member(n->a, u, v) && !member(n->b, u, v);
    case SET_SYMDIFF:    return member(n->a, u, v) != member(n->b, u, v);
    default:             return 0;  /* SET_EMPTY */
    }
}

/* Confronto per qsort: prima le configurazioni con meno regioni. */
static int by_size(const void *a, const void *b) {
    return __builtin_popcount(*(const unsigned *)a) - __builtin_popcount(*(const unsigned *)b);
}

/* Riempie support e supports della relazione n con i supporti minimi: gli
 * insiemi di regioni, nessuno contenuto in un altro, tali che la relazione
 * fallisce esattamente quando le regioni di uno di essi sono tutte non vuote.
 *
 * Si esaminano tutti gli oggetti del tipo giusto: le regioni per gli elementi,
 * gli insiemi di regioni per gli insiemi, le coppie di regioni per le coppie.
 * Ogni oggetto che distingue i due membri dà un supporto: le regioni che
 * tocca. Bastano i minimi, perché una configurazione che ne contiene uno più
 * grande contiene anche il più piccolo. */
static void relation_supports(SetNode *n) {
    SetType type = set_join(n->a->type, n->b->type);
    unsigned regions = 1u << set_var_count;
    unsigned long long objects = type == TY_FAMILY ? 1ull << regions
                               : type == TY_PAIRS ? (unsigned long long)regions * regions : regions;
    unsigned *found = arena_alloc((size_t)objects * sizeof(unsigned));
    if (!found) return;

    /* Tutti gli oggetti che distinguono i due membri. */
    int count = 0;
    for (unsigned long long object = 0; object < objects; object++) {
        unsigned u = type == TY_PAIRS ? (unsigned)(object / regions) : (unsigned)object;
        unsigned v = type == TY_PAIRS ? (unsigned)(object % regions) : 0;
        int left = member(n->a, u, v), right = member(n->b, u, v);
        if (n->kind == SET_SUBSET ? !(left && !right) : left == right) continue;
        found[count++] = type == TY_FAMILY ? u : type == TY_PAIRS ? (1u << u) | (1u << v) : 1u << u;
    }

    /* Dal più piccolo al più grande, si tiene un supporto solo se non ne
     * contiene uno già tenuto. */
    qsort(found, (size_t)count, sizeof(unsigned), by_size);
    int kept = 0;
    for (int i = 0; i < count; i++) {
        int redundant = 0;
        for (int j = 0; j < kept && !redundant; j++)
            if ((found[j] & ~found[i]) == 0) redundant = 1;
        if (!redundant) found[kept++] = found[i];
    }
    n->support = found;
    n->supports = kept;
}

/* Calcola i supporti di tutte le relazioni del sotto-albero. */
static void set_prepare(SetNode *n) {
    if (!n) return;
    if (n->kind == SET_EQ || n->kind == SET_SUBSET || n->kind == SET_NEQ) { relation_supports(n); return; }
    set_prepare(n->a);
    set_prepare(n->b);
}

/* Ritorna 1 se la formula n è vera nella configurazione in cui le regioni non
 * vuote sono quelle dei bit di nonempty. Il quantificatore si limita a
 * valutare il proprio corpo: come viene trattato il suo insieme lo decide chi
 * sceglie le configurazioni (vedi 15d e 15e). */
static int set_holds(const SetNode *n, unsigned nonempty) {
    switch (n->kind) {
    case SET_EQ: case SET_SUBSET: case SET_NEQ: {
        int fails = 0;
        for (int i = 0; i < n->supports && !fails; i++)
            if ((n->support[i] & ~nonempty) == 0) fails = 1;
        return n->kind == SET_NEQ ? fails : !fails;
    }
    case SET_AND:     return set_holds(n->a, nonempty) && set_holds(n->b, nonempty);
    case SET_OR:      return set_holds(n->a, nonempty) || set_holds(n->b, nonempty);
    case SET_IMPLIES: return !set_holds(n->a, nonempty) || set_holds(n->b, nonempty);
    case SET_IFF:     return set_holds(n->a, nonempty) == set_holds(n->b, nonempty);
    case SET_NOT:     return !set_holds(n->a, nonempty);
    default:          return set_holds(n->a, nonempty);  /* SET_EXISTS */
    }
}

/* Ritorna 1 se n è vera in ogni configurazione le cui regioni non vuote stanno
 * tra quelle di allowed. Altrimenti ritorna 0 e mette in *failing, tra le
 * configurazioni in cui n è falsa, una con il minor numero di regioni non
 * vuote: darà il controesempio più piccolo. */
static int set_valid(const SetNode *n, unsigned allowed, unsigned *failing) {
    int valid = 1;

    /* Tutti i sottoinsiemi di allowed: (p - 1) & allowed è il successivo in
     * ordine decrescente, e dopo lo zero il giro è finito. */
    for (unsigned p = allowed;; p = (p - 1) & allowed) {
        if (!set_holds(n, p) && (valid || __builtin_popcount(p) < __builtin_popcount(*failing))) {
            valid = 0;
            *failing = p;
        }
        if (p == 0) break;
    }
    return valid;
}

/* Ritorna le regioni compatibili con la scelta, per l'insieme di indice var,
 * di un'unione di regioni degli altri insiemi (caso 15e). mask ha un bit per
 * ogni regione degli altri insiemi: 1 se quella regione fa parte dell'insieme.
 * Una regione di tutti gli insiemi è compatibile se il suo bit var coincide
 * con quanto mask dice della regione che resta togliendo quel bit. */
static unsigned witness_regions(int var, unsigned mask) {
    unsigned allowed = 0;
    for (unsigned region = 0; region < (1u << set_var_count); region++) {
        unsigned low = region & ((1u << var) - 1), high = region >> (var + 1);
        unsigned others = low | (high << var);
        if (((region >> var) & 1) == ((mask >> others) & 1)) allowed |= 1u << region;
    }
    return allowed;
}

/* 15f. Quantificatori in ogni posizione: contare gli elementi delle regioni.
 *
 * "Se S non è vuoto esistono due parti di S, non vuote, senza elementi in
 * comune" è falso: se S ha un elemento solo non si può. Per deciderlo non
 * basta sapere quali regioni sono vuote: conta quanti elementi hanno. Ma non
 * serve contarli tutti.
 *
 * Teorema. Sia P una condizione sugli insiemi con al più q quantificatori
 * "esiste un insieme" uno dentro l'altro. Se due scelte degli insiemi liberi
 * danno a ogni regione lo stesso numero di elementi, oppure tutte e due
 * almeno 2^q, allora P vale per l'una se e solo se vale per l'altra.
 *
 * Dimostrazione, per induzione su q. Con q = 0 la verità di P dipende solo
 * da quali regioni sono vuote (capitolo 15, "Configurazioni"), e 2^0 = 1 è
 * proprio "almeno un elemento". Sia ora P = "esiste X tale che R", con R di
 * profondità q - 1, e X un insieme che funziona per la prima scelta. X
 * divide ogni regione, di c elementi, in due: a dentro X e c - a fuori. La
 * regione corrispondente della seconda scelta ha c' elementi, con c' = c
 * oppure c e c' tutti e due almeno 2^q. La si divide così: se c' = c allo
 * stesso modo; altrimenti, se a < 2^(q-1) si mettono a elementi dentro (ne
 * restano fuori almeno 2^(q-1), come nella prima); se c - a < 2^(q-1) se ne
 * lasciano fuori c - a; se nessuno dei due, almeno 2^(q-1) da ogni parte,
 * che si può perché c' è almeno 2^q. Le regioni nuove hanno allora gli stessi
 * numeri di elementi, o tutte e due almeno 2^(q-1): per ipotesi induttiva R
 * vale anche per la seconda scelta. I connettivi non cambiano nulla.
 *
 * Quindi basta dare a ogni regione degli insiemi liberi un numero di
 * elementi tra 0 e 2^q, dove 2^q vuol dire "almeno", e per ogni "esiste X"
 * provare ogni modo di dividere le regioni: è un conto finito e completo,
 * che decide in tutti e due i sensi.
 *
 * Gli oggetti fuori da tutti gli insiemi. Di oggetti ce n'è quanti se ne
 * vuole, e un insieme quantificato può prenderne; ma nessun insieme li
 * prende tutti: l'insieme di tutti gli oggetti non esiste. Per questo la
 * regione 0, quella degli oggetti che non stanno in nessun insieme, è
 * sempre "almeno" quanto serve, e quando un "esiste X" la divide ne resta
 * fuori sempre altrettanto. Una versione che la trattava come le altre
 * regioni lasciava a X la possibilità di prenderla tutta, e così
 * dimostrava "esiste V tale che ogni W è contenuto in V".
 *
 * Il conto cresce in fretta, e ha un tetto (MAX_COUNT_CASES): oltre, la
 * risposta è NON DIMOSTRATO.
 */

/* Ritorna quanti "esiste un insieme" stanno uno dentro l'altro in n, al più. */
static int set_depth(const SetNode *n) {
    if (!n) return 0;
    int a = set_depth(n->a), b = set_depth(n->b), deepest = a > b ? a : b;
    return n->kind == SET_EXISTS ? deepest + 1 : deepest;
}

/* Ritorna le lettere che in n compaiono libere, un bit per indice; bound sono
 * quelle legate da un quantificatore più esterno. */
static unsigned set_free_letters(const SetNode *n, unsigned bound) {
    if (!n) return 0;
    if (n->kind == SET_VAR) return (1u << n->var) & ~bound;
    if (n->kind == SET_EXISTS) bound |= 1u << n->var;
    return set_free_letters(n->a, bound) | set_free_letters(n->b, bound);
}

/* Quante valutazioni può ancora fare il conto in corso; sotto zero è stato
 * interrotto, e le sue risposte non valgono. */
static _Thread_local long long count_budget;

static int counts_hold(const SetNode *n, const unsigned char *count);

/* 15f, un "esiste X". exists è il nodo, bit la lettera X, cap = 2^d con d
 * la profondità della condizione sotto il quantificatore. count[] sono i
 * numeri di elementi delle regioni scelti finora: quelle prima di `region`
 * sono già divise tra dentro e fuori X, le altre no. Ritorna 1 se c'è un
 * modo di dividere le regioni da `region` in poi che rende vera la
 * condizione.
 *
 * Una regione di m elementi si divide in a dentro e m - a fuori, e dei due
 * numeri conta solo ciò che sta sotto cap: cap vuol dire "almeno cap". Se m
 * è 2 cap, cioè "almeno 2 cap", le divisioni possibili sono tutte le coppie
 * in cui una delle due parti è "almeno cap". */
static int split_holds(const SetNode *exists, unsigned bit, int cap, unsigned char *count, unsigned region) {
    unsigned regions = 1u << set_var_count;
    while (region < regions && (region & bit)) region++;
    if (region == regions) return counts_hold(exists->a, count);

    int whole = count[region], found = 0;
    if (whole < 2 * cap) {
        /* Un numero preciso di elementi: a dentro, gli altri fuori. */
        for (int a = 0; a <= whole && !found && count_budget >= 0; a++) {
            count[region | bit] = (unsigned char)(a < cap ? a : cap);
            count[region] = (unsigned char)(whole - a < cap ? whole - a : cap);
            found = split_holds(exists, bit, cap, count, region + 1);
        }
    } else {
        /* "Almeno 2 cap" elementi. Della regione 0 ne restano fuori sempre
         * "almeno cap": non si esaurisce (vedi sopra). */
        for (int inside = 0; inside <= cap && !found; inside++) {
            for (int outside = inside == cap && region != 0 ? 0 : cap; outside <= cap && !found && count_budget >= 0; outside++) {
                count[region | bit] = (unsigned char)inside;
                count[region] = (unsigned char)outside;
                found = split_holds(exists, bit, cap, count, region + 1);
            }
        }
    }
    count[region] = (unsigned char)whole;
    count[region | bit] = 0;
    return found;
}

/* 15f. Ritorna 1 se la condizione n è vera quando la regione r ha count[r]
 * elementi, dove un numero pari a 2^d o più, con d la profondità di n, vuol
 * dire "almeno 2^d". */
static int counts_hold(const SetNode *n, const unsigned char *count) {
    switch (n->kind) {
    case SET_AND:     return counts_hold(n->a, count) && counts_hold(n->b, count);
    case SET_OR:      return counts_hold(n->a, count) || counts_hold(n->b, count);
    case SET_IMPLIES: return !counts_hold(n->a, count) || counts_hold(n->b, count);
    case SET_IFF:     return counts_hold(n->a, count) == counts_hold(n->b, count);
    case SET_NOT:     return !counts_hold(n->a, count);
    case SET_EXISTS:  break;
    default: {
        /* Una relazione: conta solo quali regioni non sono vuote. */
        unsigned nonempty = 0;
        for (unsigned r = 0; r < (1u << set_var_count); r++)
            if (count[r]) nonempty |= 1u << r;
        if (--count_budget < 0) return 0;
        return set_holds(n, nonempty);
    }
    }

    /* "Esiste X": chi era X fuori da qui non conta più, quindi le regioni
     * tornano intere; poi ognuna viene divisa in tutti i modi. */
    unsigned char inner[1u << MAX_SET_VARS];
    unsigned bit = 1u << n->var;
    int cap = 1 << set_depth(n->a);
    for (unsigned r = 0; r < (1u << set_var_count); r++) {
        int whole = r & bit ? 0 : count[r] + count[r | bit];
        inner[r] = (unsigned char)(whole > 2 * cap || r == 0 ? 2 * cap : whole);
    }
    return split_holds(n, bit, cap, inner, 0);
}

/* 15f. Decide se root vale per ogni scelta degli insiemi liberi, provando
 * per le loro regioni ogni numero di elementi da 0 a 2^q. Ritorna 1 se
 * vale; 0 se no, e allora count[] contiene i numeri di elementi di una
 * scelta in cui non vale; -1 se il conto è stato interrotto. */
static int counts_valid(const SetNode *root, unsigned char *count) {
    unsigned regions = 1u << set_var_count, free_letters = set_free_letters(root, 0);
    int top = 1 << set_depth(root);
    count_budget = MAX_COUNT_CASES;
    memset(count, 0, regions);
    count[0] = (unsigned char)top;
    for (;;) {
        int holds = counts_hold(root, count);
        if (count_budget < 0) return -1;
        if (!holds) return 0;

        /* La scelta successiva, come un contachilometri sulle regioni fatte
         * di soli insiemi liberi. */
        unsigned r = 1;
        for (; r < regions; r++) {
            if (r & ~free_letters) continue;
            if (count[r] < top) { count[r]++; break; }
            count[r] = 0;
        }
        if (r == regions) return 1;
    }
}

/* =============================================================================
 * 16. INSIEMI: VERIFICA INDIPENDENTE E DIMOSTRAZIONE SCRITTA
 * ============================================================================
 *
 * Verifica indipendente. Il capitolo 15 ragiona per regioni. Qui lo stesso
 * enunciato viene ricontrollato in un modo che non ne dipende: si prende un
 * universo piccolo, {1, ..., N}, si assegnano agli insiemi tutti i suoi
 * sottoinsiemi in tutti i modi possibili, e ogni espressione viene calcolata
 * davvero, come insieme. Se i due metodi non sono d'accordo, il verdetto non
 * viene emesso.
 *
 * Non è una seconda dimostrazione: N è piccolo. È un controllo contro gli
 * errori del programma, che è ciò a cui serve.
 *
 * Dimostrazione scritta. Il testo è in LaTeX. La forma preferita è quella
 * discorsiva dei libri: "sia x un elemento del primo insieme; allora... quindi
 * x sta nel secondo; viceversa...". La costruisce chase(), con i passi da 16d
 * a 16g, quando l'enunciato parla di insiemi di elementi o di coppie.
 *
 * Ogni fatto che quel testo afferma viene ricontrollato prima di essere
 * scritto, con un metodo che non usa le regole di chase(): è il controllo
 * 16h.
 *
 * Quando quella forma non si applica (insiemi delle parti, ipotesi "non
 * vuoto", quantificatori) o richiederebbe troppi casi, il testo segue invece
 * il ragionamento per regioni del capitolo 15, in una di tre forme:
 *
 *   16a. Una sola relazione tra insiemi di elementi o di coppie: la tabella di
 *        appartenenza, con una riga per ogni caso.
 *   16b. Un'equivalenza o un'implicazione tra condizioni: per ciascuna, in
 *        quali configurazioni fallisce; il confronto dei due elenchi conclude.
 *   16c. Ogni altro enunciato: per ogni relazione le configurazioni in cui
 *        fallisce, e l'esame di tutte le configurazioni.
 *
 * Anche questi testi affermano dei fatti: le righe di una tabella, gli elenchi
 * di configurazioni, l'insieme scelto per un "esiste". Ognuno viene
 * ricalcolato con gli insiemi veri prima di essere scritto: è il controllo
 * 16i.
 */

/* Ritorna il valore dell'espressione n quando gli insiemi valgono value[],
 * sottoinsiemi di un universo di size elementi. Il risultato è una maschera:
 *
 *   insieme di elementi:    il bit e dice se l'elemento e ne fa parte;
 *   collezione di insiemi:  il bit X dice se l'insieme di maschera X ne fa
 *                           parte;
 *   insieme di coppie:      il bit x * size + y dice se (x, y) ne fa parte.
 *
 * In tutti e tre i casi unione, intersezione e differenza sono le operazioni
 * sui bit. size non deve superare 5, perché le maschere abbiano 32 bit. */
static unsigned concrete(const SetNode *n, unsigned *value, int size) {
    unsigned a = n->a ? concrete(n->a, value, size) : 0, b = n->b ? concrete(n->b, value, size) : 0;
    unsigned result = 0;
    switch (n->kind) {
    case SET_VAR:        return value[n->var];
    case SET_ONLY_EMPTY: return 1u;  /* l'insieme vuoto ha maschera 0 */
    case SET_POWER:
        for (unsigned x = 0; x < (1u << size); x++)
            if ((x & ~a) == 0) result |= 1u << x;
        return result;
    case SET_PRODUCT:
        for (int x = 0; x < size; x++)
            for (int y = 0; y < size; y++)
                if (((a >> x) & 1) && ((b >> y) & 1)) result |= 1u << (x * size + y);
        return result;
    case SET_UNION:      return a | b;
    case SET_INTER:      return a & b;
    case SET_DIFF:       return a & ~b;
    case SET_SYMDIFF:    return a ^ b;
    case SET_APPLY: {
        /* 17r: la regola di f, con la sua lettera che vale a. È il calcolo
         * dell'enunciato com'è scritto, per il controllo dello svolgimento:
         * value[] deve avere MAX_SET_LETTERS posti. */
        const PartRule *rule = &part_rules[n->var];
        unsigned saved = value[rule->param[0]];
        value[rule->param[0]] = a;
        result = concrete(rule->rule, value, size);
        value[rule->param[0]] = saved;
        return result;
    }
    default:             return 0;  /* SET_EMPTY */
    }
}

/* Ritorna 1 se la formula n è vera quando gli insiemi valgono value[],
 * sottoinsiemi di un universo di size elementi. Il quantificatore prova
 * davvero tutti i sottoinsiemi, scrivendo in value[] l'insieme in esame.
 *
 * Per un "esiste X" l'universo ha un elemento in più di quello in cui stanno
 * gli insiemi scelti prima, e così per ogni quantificatore più interno: è
 * il modo di dire, con un universo finito, che fuori da qualunque insieme
 * resta sempre qualche oggetto (vedi 15f). Con un universo fisso l'insieme
 * di tutti gli elementi esisteva, e questo controllo confermava "esiste V
 * tale che ogni W è contenuto in V". */
static int concrete_holds(const SetNode *n, unsigned *value, int size) {
    switch (n->kind) {
    case SET_EQ:      return concrete(n->a, value, size) == concrete(n->b, value, size);
    case SET_NEQ:     return concrete(n->a, value, size) != concrete(n->b, value, size);
    case SET_SUBSET:  return (concrete(n->a, value, size) & ~concrete(n->b, value, size)) == 0;
    case SET_AND:     return concrete_holds(n->a, value, size) && concrete_holds(n->b, value, size);
    case SET_OR:      return concrete_holds(n->a, value, size) || concrete_holds(n->b, value, size);
    case SET_IMPLIES: return !concrete_holds(n->a, value, size) || concrete_holds(n->b, value, size);
    case SET_IFF:     return concrete_holds(n->a, value, size) == concrete_holds(n->b, value, size);
    case SET_NOT:     return !concrete_holds(n->a, value, size);
    case SET_PAIR_IN: {
        /* 17r: A e B sono parti dell'insieme della relazione, e la regola
         * vale con le sue lettere che valgono A e B (vedi SET_APPLY in
         * concrete()). */
        const PartRule *rule = &part_rules[n->var];
        unsigned first = concrete(n->a, value, size), second = concrete(n->b, value, size), base = value[rule->base];
        if ((first & ~base) || (second & ~base)) return 0;
        unsigned saved[2] = {value[rule->param[0]], value[rule->param[1]]};
        value[rule->param[0]] = first;
        value[rule->param[1]] = second;
        int holds = concrete_holds(rule->rule, value, size);
        value[rule->param[0]] = saved[0];
        value[rule->param[1]] = saved[1];
        return holds;
    }
    default:          /* SET_EXISTS */
        for (unsigned candidate = 0; candidate < (1u << (size + 1)); candidate++) {
            value[n->var] = candidate;
            if (concrete_holds(n->a, value, size + 1)) return 1;
        }
        return 0;
    }
}

/* Ritorna 1 se root è vera per ogni assegnazione di sottoinsiemi di un
 * universo di size elementi agli insiemi dell'enunciato. bound è l'indice
 * dell'insieme legato da un quantificatore, o -1: quello non si assegna qui. */
static int concrete_valid(const SetNode *root, int bound, int size) {
    unsigned value[MAX_SET_VARS] = {0};
    for (;;) {
        if (!concrete_holds(root, value, size)) return 0;

        /* Assegnazione successiva, come un contachilometri: si incrementa il
         * primo insieme, e quando ha fatto il giro si passa al seguente. */
        int i = 0;
        for (; i < set_var_count; i++) {
            if (i == bound) continue;
            if (++value[i] < (1u << size)) break;
            value[i] = 0;
        }
        if (i == set_var_count) return 1;
    }
}

/* Costruisce gli insiemi che realizzano la configurazione nonempty, con un
 * elemento per ogni regione non vuota: li mette in value[] come maschere su un
 * universo di *size elementi. */
static void configuration_sets(unsigned nonempty, unsigned *value, int *size) {
    *size = 0;
    for (int i = 0; i < set_var_count; i++) value[i] = 0;
    for (unsigned region = 0; nonempty >> region; region++) {
        if (!((nonempty >> region) & 1)) continue;
        for (int i = 0; i < set_var_count; i++)
            if ((region >> i) & 1) value[i] |= 1u << *size;
        (*size)++;
    }
}

/* 16i. Controllo di un fatto delle forme 16b e 16c: "la condizione n fallisce
 * esattamente nelle configurazioni che contengono una di quelle di list".
 * Gli elenchi nascono dal conto per regioni del capitolo 15; qui, per ogni
 * configurazione contenuta in allowed, si costruiscono gli insiemi veri e si
 * calcola la condizione con concrete_holds(), che delle regioni non sa nulla.
 * Si provano le configurazioni con al più 5 regioni non vuote, perché gli
 * insiemi concreti hanno al più 5 elementi.
 *
 * Con holds diverso da zero il fatto è "vale esattamente", come per una
 * relazione "diverso da". Ritorna 1 se il fatto è confermato; altrimenti
 * annota il passo come non giustificato e ritorna 0. */
static int list_confirmed(const SetNode *n, unsigned allowed, const unsigned *list, int count, int holds) {
    for (unsigned p = allowed;; p = (p - 1) & allowed) {
        if (__builtin_popcount(p) <= 5) {
            unsigned value[MAX_SET_VARS];
            int size, listed = 0;
            for (int i = 0; i < count; i++)
                if ((list[i] & ~p) == 0) listed = 1;
            configuration_sets(p, value, &size);
            if ((concrete_holds(n, value, size) != 0) != (holds ? listed : !listed)) { unjustified_steps++; return 0; }
        }
        if (p == 0) break;
    }
    return 1;
}

/* Aggiunge alla dimostrazione l'espressione o la formula n, in LaTeX. Un
 * operando viene messo tra parentesi quando è a sua volta un'operazione dello
 * stesso livello: tra insiemi sotto un'operazione tra insiemi, tra condizioni
 * sotto un connettivo. */
static void put_set(const SetNode *n) {
    static const char *const symbol[] = {
        [SET_UNION] = "\\cup", [SET_INTER] = "\\cap", [SET_DIFF] = "\\setminus", [SET_SYMDIFF] = "\\triangle",
        [SET_PRODUCT] = "\\times", [SET_EQ] = "=", [SET_SUBSET] = "\\subseteq", [SET_NEQ] = "\\neq",
        [SET_AND] = "\\land", [SET_OR] = "\\lor", [SET_IMPLIES] = "\\implies", [SET_IFF] = "\\iff",
    };
    switch (n->kind) {
    case SET_VAR:        proof_add("%c", set_var_name[n->var]); return;
    case SET_EMPTY:      proof_add("\\emptyset"); return;
    case SET_ONLY_EMPTY: proof_add("\\{\\emptyset\\}"); return;
    case SET_POWER:      proof_add("\\mathcal{P}("); put_set(n->a); proof_add(")"); return;
    case SET_NOT:        proof_add("\\lnot ("); put_set(n->a); proof_add(")"); return;
    case SET_EXISTS:     proof_add("\\exists %c\\,(", set_var_name[n->var]); put_set(n->a); proof_add(")"); return;
    default:             break;
    }

    /* Operatori binari. */
    int logical = n->kind >= SET_AND;
    for (int side = 0; side < 2; side++) {
        const SetNode *operand = side ? n->b : n->a;
        int nested = logical ? operand->kind >= SET_AND && operand->kind != SET_NOT && operand->kind != SET_EXISTS
                             : operand->kind >= SET_UNION && operand->kind <= SET_PRODUCT && n->kind <= SET_PRODUCT;
        if (side) proof_add(" %s ", symbol[n->kind]);
        if (nested) proof_add("(");
        put_set(operand);
        if (nested) proof_add(")");
    }
}

/* Aggiunge alla dimostrazione il nome di una regione, per esempio
 * S \cap T^{c} per "in S e non in T". */
static void put_region(unsigned region) {
    for (int i = 0; i < set_var_count; i++)
        proof_add("%s%c%s", i ? " \\cap " : "", set_var_name[i], ((region >> i) & 1) ? "" : "^{c}");
}

/* Aggiunge alla dimostrazione la descrizione delle configurazioni di list, da
 * leggere dopo "fails exactly": ogni elemento è un insieme di regioni che
 * devono essere tutte non vuote. */
static void put_configurations(const unsigned *list, int count) {
    if (count == 0) { proof_add("in no case"); return; }
    if (list[0] == 0) { proof_add("in every case"); return; }

    /* Il caso più comune: basta una regione non vuota. */
    int single = 1;
    for (int i = 0; i < count; i++)
        if (__builtin_popcount(list[i]) != 1) single = 0;
    if (single && count <= MAX_CONFIGS) {
        proof_add(count == 1 ? "when the region " : "when at least one of the regions ");
        for (int i = 0; i < count; i++) {
            proof_add("%s$", i ? ", " : "");
            put_region((unsigned)__builtin_ctz(list[i]));
            proof_add("$");
        }
        proof_add(" is non-empty");
        return;
    }

    /* In generale: più regioni non vuote insieme. */
    for (int i = 0; i < count && i < MAX_CONFIGS; i++) {
        int size = __builtin_popcount(list[i]), first = 1;
        proof_add("%swhen the region%s ", i ? "; or " : "", size == 1 ? "" : "s");
        for (unsigned region = 0; list[i] >> region; region++) {
            if (!((list[i] >> region) & 1)) continue;
            proof_add("%s$", first ? "" : " and ");
            put_region(region);
            proof_add("$");
            first = 0;
        }
        proof_add(size == 1 ? " is non-empty" : size == 2 ? " are both non-empty" : " are all non-empty");
    }
    if (count > MAX_CONFIGS) proof_add("; or in %d further situations of the same kind", count - MAX_CONFIGS);
}

/* Ritorna 1 se nel sotto-albero c'è una relazione tra oggetti di tipo type. */
static int set_relates(const SetNode *n, SetType type) {
    if (!n) return 0;
    if (n->kind == SET_EQ || n->kind == SET_SUBSET || n->kind == SET_NEQ) {
        SetType operands = set_join(n->a->type, n->b->type);
        return operands == type || (type == TY_SET && operands == TY_ANY);
    }
    return set_relates(n->a, type) || set_relates(n->b, type);
}

/* Aggiunge alla dimostrazione la premessa comune alle forme 16b e 16c: cosa
 * sono le regioni e perché una relazione fallisce in certe configurazioni. Si
 * citano solo i tipi di oggetto presenti nell'enunciato root. */
static void put_regions_preamble(const SetNode *root) {
    proof_add("The sets ");
    for (int i = 0; i < set_var_count; i++) proof_add("%s$%c$", i ? ", " : "", set_var_name[i]);
    proof_add(" divide all elements into regions: a region is fixed by saying, for each of these sets, whether an "
              "element belongs to it. We write $A^{c}$ for ``not in $A$'', so that for instance $");
    put_region(1);
    proof_add("$ is the region of the elements that lie in $%c$ and in none of the other sets. ", set_var_name[0]);
    if (set_relates(root, TY_SET))
        proof_add("Whether an element belongs to a set built from them depends only on its region; so an inclusion "
                  "$A \\subseteq B$ fails exactly when some region contained in $A$ but not in $B$ is non-empty, and "
                  "an equality $A = B$ fails exactly when some region contained in only one of $A$, $B$ is non-empty. ");
    if (set_relates(root, TY_FAMILY))
        proof_add("A set $X$ belongs to $\\mathcal{P}(A)$ exactly when every region that $X$ meets is contained in "
                  "$A$, and to $\\{\\emptyset\\}$ exactly when $X$ meets no region; so whether $X$ belongs to a "
                  "collection of sets depends only on the regions it meets, and two such collections differ exactly "
                  "when some set, with one element in each of certain regions and no other element, lies in only one "
                  "of them. This requires those regions to be all non-empty. ");
    if (set_relates(root, TY_PAIRS))
        proof_add("A pair $(x, y)$ belongs to $A \\times B$ exactly when $x \\in A$ and $y \\in B$; so whether it "
                  "belongs to a set of pairs depends only on the regions of $x$ and of $y$, and two sets of pairs "
                  "differ exactly when some pair lies in only one of them, which requires the regions of its two "
                  "components to be non-empty. ");
    proof_add("\n\n");
}

/* Aggiunge alla dimostrazione un elenco con, per ogni relazione del
 * sotto-albero, le configurazioni in cui fallisce (forma 16c). */
static void put_relation_items(const SetNode *n) {
    if (!n) return;
    if (n->kind == SET_EQ || n->kind == SET_SUBSET || n->kind == SET_NEQ) {
        proof_add("\\item $");
        put_set(n);
        proof_add(n->kind == SET_NEQ ? "$ holds exactly " : "$ fails exactly ");
        put_configurations(n->support, n->supports);
        proof_add(".\n");
        return;
    }
    put_relation_items(n->a);
    put_relation_items(n->b);
}

/* Ritorna 1 se la formula è fatta solo di uguaglianze e inclusioni unite da
 * "e" e "o". Una formula così, se fallisce in una configurazione, fallisce in
 * ogni configurazione con più regioni non vuote: per descriverla bastano le
 * configurazioni minime in cui fallisce. */
static int set_is_monotone(const SetNode *n) {
    if (n->kind == SET_EQ || n->kind == SET_SUBSET) return 1;
    return (n->kind == SET_AND || n->kind == SET_OR) && set_is_monotone(n->a) && set_is_monotone(n->b);
}

/* Mette in out le configurazioni minime, tra quelle contenute in allowed, in
 * cui la formula monotona n fallisce, dalla più piccola alla più grande, e ne
 * ritorna il numero; -1 se sono più di max. Una configurazione è minima se
 * togliendole una qualsiasi regione la formula torna vera. */
static int minimal_failures(const SetNode *n, unsigned allowed, unsigned *out, int max) {
    int count = 0;
    for (unsigned p = allowed;; p = (p - 1) & allowed) {
        int minimal = !set_holds(n, p);
        for (unsigned region = 0; minimal && p >> region; region++)
            if (((p >> region) & 1) && !set_holds(n, p & ~(1u << region))) minimal = 0;
        if (minimal) {
            if (count == max) return -1;
            out[count++] = p;
        }
        if (p == 0) break;
    }
    qsort(out, (size_t)count, sizeof(unsigned), by_size);
    return count;
}

/* Raccoglie in *firsts e *seconds le lettere che nel sotto-albero compaiono
 * nel primo e nel secondo fattore di un prodotto cartesiano: sono quelle a cui
 * possono appartenere le componenti x e y di una coppia. into è il mucchio a
 * cui va la lettera corrente, o NULL fuori da un prodotto. */
static void product_factors(const SetNode *n, unsigned *firsts, unsigned *seconds, unsigned *into) {
    if (!n) return;
    if (n->kind == SET_VAR && into) *into |= 1u << n->var;
    if (n->kind == SET_PRODUCT) {
        product_factors(n->a, firsts, seconds, firsts);
        product_factors(n->b, firsts, seconds, seconds);
        return;
    }
    product_factors(n->a, firsts, seconds, into);
    product_factors(n->b, firsts, seconds, into);
}

/* Forma 16a: se root è una sola relazione tra insiemi di elementi o di coppie
 * scrive la dimostrazione con la tabella di appartenenza e ritorna 1;
 * altrimenti non scrive nulla e ritorna 0.
 *
 * Per gli insiemi di elementi le colonne sono "x appartiene a S" per ogni
 * insieme S. Per le coppie (x, y) sono "x appartiene a S" per gli insiemi che
 * compaiono come primo fattore di un prodotto e "y appartiene a T" per quelli
 * che compaiono come secondo. */
static int put_table_proof(const SetNode *root) {
    if (root->kind != SET_EQ && root->kind != SET_SUBSET) return 0;
    SetType type = set_join(root->a->type, root->b->type);
    unsigned firsts = (1u << set_var_count) - 1, seconds = 0;
    if (type == TY_PAIRS) {
        firsts = 0;
        product_factors(root, &firsts, &seconds, NULL);
    } else if (type != TY_SET && type != TY_ANY) {
        return 0;
    }
    int columns = __builtin_popcount(firsts) + __builtin_popcount(seconds);
    if (columns > 4) return 0;
    size_t start = proof_length;

    /* Premessa. */
    const char *object = type == TY_PAIRS ? "$(x, y)$" : "$x$";
    proof_add("\\textbf{Proof.} Let %s be an arbitrary %s. Each row of the table is one possible combination of the "
              "memberships in its first columns ($1$ = belongs, $0$ = does not belong); the last two columns say, "
              "by the definitions of the operations, whether %s belongs to each side.\n\n",
              object, type == TY_PAIRS ? "pair" : "element", object);

    /* Intestazione. */
    proof_add("\\begin{center}\\begin{tabular}{");
    for (int i = 0; i < columns; i++) proof_add("c");
    proof_add("|cc}\n");
    for (int i = 0; i < set_var_count; i++)
        if ((firsts >> i) & 1) proof_add("$x \\in %c$ & ", set_var_name[i]);
    for (int i = 0; i < set_var_count; i++)
        if ((seconds >> i) & 1) proof_add("$y \\in %c$ & ", set_var_name[i]);
    proof_add("$");
    put_set(root->a);
    proof_add("$ & $");
    put_set(root->b);
    proof_add("$ \\\\ \\hline\n");

    /* Una riga per ogni combinazione: u e v sono le regioni di x e di y. */
    for (unsigned u = 0; u < (1u << set_var_count); u++) {
        if (u & ~firsts) continue;
        for (unsigned v = 0; v < (1u << set_var_count); v++) {
            if (v & ~seconds) continue;
            for (int i = 0; i < set_var_count; i++)
                if ((firsts >> i) & 1) proof_add("%u & ", (u >> i) & 1);
            for (int i = 0; i < set_var_count; i++)
                if ((seconds >> i) & 1) proof_add("%u & ", (v >> i) & 1);
            int left = member(root->a, u, v), right = member(root->b, u, v);
            proof_add("%d & %d \\\\\n", left, right);

            /* 16i. Controllo della riga. Le due colonne si ricalcolano con
             * gli insiemi veri: un universo di due elementi, x (il numero 0)
             * e y (il numero 1), messi negli insiemi che la riga dice. Per
             * gli insiemi di elementi si guarda x, cioè il bit 0; per quelli
             * di coppie la coppia (x, y), cioè il bit 0 * 2 + 1. E la riga
             * deve essere compatibile con ciò che la conclusione dirà di
             * tutte: colonne uguali, oppure la prima non oltre la seconda. */
            unsigned value[MAX_SET_VARS], bit = type == TY_PAIRS ? 2u : 1u;
            for (int i = 0; i < set_var_count; i++) value[i] = ((u >> i) & 1) | (((v >> i) & 1) << 1);
            int agrees = ((concrete(root->a, value, 2) & bit) != 0) == left && ((concrete(root->b, value, 2) & bit) != 0) == right;
            if (!agrees || (root->kind == SET_EQ ? left != right : left && !right)) {
                unjustified_steps++;
                proof_length = start;
                proof_text[start] = 0;
                return 0;
            }
        }
    }
    proof_add("\\end{tabular}\\end{center}\n\n");

    /* Conclusione. */
    if (root->kind == SET_EQ)
        proof_add("The last two columns are equal in every row, so the two sides have the same elements. $\\Box$");
    else
        proof_add("In every row where the first of the last two columns is $1$, the second is $1$ as well, so every "
                  "element of the left-hand side belongs to the right-hand side. $\\Box$");
    return 1;
}

/* Forma 16b: se root è un'equivalenza o un'implicazione tra condizioni
 * monotone, eventualmente sotto ipotesi che sono inclusioni o uguaglianze tra
 * insiemi di elementi, scrive la dimostrazione per confronto delle
 * configurazioni e ritorna 1; altrimenti non scrive nulla e ritorna 0.
 *
 * Le ipotesi di quel tipo dicono solo che certe regioni sono vuote: le si
 * toglie dalle regioni ammesse e si ragiona sulle altre. */
static int put_comparison_proof(const SetNode *root) {
    const SetNode *hypothesis = NULL, *core = root;
    unsigned all = (1u << (1u << set_var_count)) - 1, allowed = all;
    if (set_var_count == 5) return 0;

    /* Ipotesi, se ci sono: la parte sinistra di un'implicazione esterna. */
    if (root->kind == SET_IMPLIES && (root->b->kind == SET_IFF || root->b->kind == SET_IMPLIES)) {
        unsigned empty[MAX_CONFIGS];
        hypothesis = root->a;
        core = root->b;
        if (!set_is_monotone(hypothesis)) return 0;
        int count = minimal_failures(hypothesis, all, empty, MAX_CONFIGS);
        if (count < 0 || !list_confirmed(hypothesis, all, empty, count, 0)) return 0;
        for (int i = 0; i < count; i++) {
            if (__builtin_popcount(empty[i]) != 1) return 0;
            allowed &= ~empty[i];
        }
    }
    if ((core->kind != SET_IFF && core->kind != SET_IMPLIES) || !set_is_monotone(core->a) || !set_is_monotone(core->b))
        return 0;

    /* Le configurazioni minime in cui ciascuna delle due condizioni fallisce. */
    unsigned left[MAX_CONFIGS], right[MAX_CONFIGS];
    int lefts = minimal_failures(core->a, allowed, left, MAX_CONFIGS);
    int rights = minimal_failures(core->b, allowed, right, MAX_CONFIGS);
    if (lefts < 0 || rights < 0) return 0;

    /* 16i. I due elenchi, ricontrollati con gli insiemi veri, e ciò che il
     * testo dirà del loro confronto: ogni configurazione minima in cui la
     * seconda condizione fallisce ne contiene una in cui fallisce la prima
     * e, per un'equivalenza, anche il viceversa. */
    if (!list_confirmed(core->a, allowed, left, lefts, 0) || !list_confirmed(core->b, allowed, right, rights, 0)) return 0;
    for (int way = 0; way < (core->kind == SET_IFF ? 2 : 1); way++) {
        const unsigned *weak = way ? left : right, *strong = way ? right : left;
        int weaks = way ? lefts : rights, strongs = way ? rights : lefts;
        for (int i = 0; i < weaks; i++) {
            int contains = 0;
            for (int j = 0; j < strongs; j++)
                if ((strong[j] & ~weak[i]) == 0) contains = 1;
            if (!contains) { unjustified_steps++; return 0; }
        }
    }

    proof_add("\\textbf{Proof.} ");
    put_regions_preamble(root);
    if (hypothesis) {
        unsigned empty = all & ~allowed;
        proof_add("By the hypothesis $");
        put_set(hypothesis);
        proof_add("$, ");
        if (empty) {
            int first = 1;
            for (unsigned region = 0; empty >> region; region++) {
                if (!((empty >> region) & 1)) continue;
                proof_add("%s$", first ? "the following regions are empty: " : ", ");
                put_region(region);
                proof_add("$");
                first = 0;
            }
            proof_add("; only the remaining regions are considered below. ");
        } else {
            proof_add("no region is forced to be empty. ");
        }
    }

    if (core->kind == SET_IFF) {
        /* Le due condizioni falliscono nelle stesse configurazioni: gli
         * elenchi coincidono, e se ne stampa uno. */
        proof_add("Each of the two conditions $");
        put_set(core->a);
        proof_add("$ and $");
        put_set(core->b);
        proof_add("$ fails exactly ");
        put_configurations(left, lefts);
        proof_add(". Hence one holds if and only if the other does. $\\Box$");
    } else {
        proof_add("The condition $");
        put_set(core->a);
        proof_add("$ fails exactly ");
        put_configurations(left, lefts);
        proof_add("; the condition $");
        put_set(core->b);
        proof_add("$ fails exactly ");
        put_configurations(right, rights);
        proof_add(". Every situation in which the second fails is one in which the first fails as well; hence the "
                  "first implies the second. $\\Box$");
    }
    return 1;
}

/* 16i. Ritorna 1 se per ogni relazione del sotto-albero l'elenco delle
 * configurazioni in cui fallisce (o vale, se è "diverso da"), che la forma
 * 16c sta per scrivere, è confermato da list_confirmed(). */
static int relations_confirmed(const SetNode *n) {
    if (!n) return 1;
    if (n->kind == SET_EQ || n->kind == SET_SUBSET || n->kind == SET_NEQ)
        return list_confirmed(n, (1u << (1u << set_var_count)) - 1, n->support, n->supports, n->kind == SET_NEQ);
    return relations_confirmed(n->a) && relations_confirmed(n->b);
}

/* Forma 16c: scrive la dimostrazione generica di root. witness, se non è
 * NULL, è il quantificatore per cui è stato trovato l'insieme esplicito
 * unione delle regioni di mask (vedi 15e). Ritorna 0, senza scrivere nulla,
 * se un elenco che starebbe per scrivere non supera il controllo 16i. */
static int put_general_proof(const SetNode *root, const SetNode *witness, unsigned mask) {
    int single = root->kind == SET_EQ || root->kind == SET_SUBSET;
    if (!single && !relations_confirmed(root)) return 0;
    proof_add("\\textbf{Proof.} ");
    put_regions_preamble(root);

    /* Una sola relazione, tra collezioni di insiemi o tra insiemi di coppie:
     * non ci sono condizioni da combinare, si confrontano i due membri su
     * tutti gli oggetti possibili. */
    if (single) {
        unsigned regions = 1u << set_var_count;
        if (set_relates(root, TY_FAMILY))
            proof_add("There are $%u$ ways of choosing which regions a set $X$ meets. In each of them, ", 1u << regions);
        else
            proof_add("There are $%u$ ways of choosing the regions of $x$ and of $y$ for a pair $(x, y)$. In each of them, ", regions * regions);
        proof_add(root->kind == SET_EQ ? "it belongs to the left-hand side exactly when it belongs to the right-hand side. "
                                         "Hence the two sides have the same elements. $\\Box$"
                                       : "if it belongs to the left-hand side then it belongs to the right-hand side. "
                                         "Hence the left-hand side is contained in the right-hand side. $\\Box$");
        return 1;
    }
    proof_add("For the conditions in the statement this gives:\n\\begin{itemize}\n");
    put_relation_items(root);
    proof_add("\\end{itemize}\n");

    if (witness) {
        /* L'insieme scelto, scritto come unione di regioni degli altri. */
        proof_add("For the set $%c$ whose existence is claimed we take $%c = ", set_var_name[witness->var], set_var_name[witness->var]);
        int first = 1;
        for (unsigned others = 0; mask >> others; others++) {
            if (!((mask >> others) & 1)) continue;
            unsigned low = others & ((1u << witness->var) - 1), high = others >> witness->var;
            unsigned region = low | (high << (witness->var + 1));
            proof_add("%s(", first ? "" : " \\cup ");
            for (int i = 0, printed = 0; i < set_var_count; i++) {
                if (i == witness->var) continue;
                proof_add("%s%c%s", printed++ ? " \\cap " : "", set_var_name[i], ((region >> i) & 1) ? "" : "^{c}");
            }
            proof_add(")");
            first = 0;
        }
        proof_add("%s$; where $%c$ instead appears in a hypothesis, it is an arbitrary set and counts as one more "
                  "set dividing the elements into regions. ", first ? "\\emptyset" : "", set_var_name[witness->var]);
    }
    proof_add("The statement is a logical combination of these conditions, so its truth depends only on which "
              "regions are empty. It was checked in each of the possible cases, and it holds in all of them. $\\Box$");
    return 1;
}

/* Un fatto su un punto: sta (sign = 1) o non sta (sign = 0) in node. Per un
 * insieme di elementi coord dice di quale componente si parla, 0 per x e 1 per
 * y; per un insieme di coppie il punto è la coppia (x, y) e coord non conta. */
typedef struct {
    const SetNode *node;
    int coord, sign;
} Fact;

/* Lo stato di una dimostrazione "per inseguimento degli elementi": ciò che si
 * sa del punto in esame e ciò che resta da sviluppare.
 *
 * Di ogni lettera si sa se x (indice 0) o y (indice 1) le appartiene: il bit
 * della lettera in known dice se lo si sa, quello in truth cosa si sa.
 * pending sono i fatti affermati ma non ancora scomposti. list_start serve a
 * sapere se l'elenco di passaggi in corso è ancora vuoto. */
typedef struct {
    unsigned known[2], truth[2];
    Fact pending[24];
    int pendings;
    size_t list_start;  /* lunghezza del testo quando è iniziato l'elenco di passaggi in corso */
    unsigned long long alive[4];  /* 16h: i mondi ancora possibili, un bit per mondo */
} Chase;

/* Passi ancora concessi: se si esauriscono la dimostrazione discorsiva viene
 * abbandonata, per non scrivere pagine di casi. Un valore negativo dice che
 * va abbandonata comunque. */
static _Thread_local int chase_budget;

/* Le ipotesi utilizzabili durante un inseguimento, come inclusioni: ogni
 * punto di hypothesis_sub[i] sta in hypothesis_sup[i]. */
static _Thread_local const SetNode *hypothesis_sub[16], *hypothesis_sup[16];
static _Thread_local int hypotheses;

/* Le lettere su cui ha senso distinguere due casi, per x e per y. */
static _Thread_local unsigned chase_letters[2];

/* Quanti casi sono aperti uno dentro l'altro. Ogni caso è un elenco rientrato
 * nel documento, e LaTeX ne ammette quattro annidati: oltre il terzo livello
 * di casi la dimostrazione discorsiva viene abbandonata. */
static _Thread_local int chase_depth;

/* 16h. Controllo di ogni passo.
 *
 * chase() ricava i fatti con le sue regole: scompone, usa le ipotesi, apre
 * casi. Qui gli stessi fatti vengono ricontrollati senza regole, per forza
 * bruta. Un "mondo" è un modo completo di dire a quali insiemi appartengono x
 * e y: due regioni, u per x e v per y. Con al più quattro insiemi i mondi sono
 * al più 16 * 16 = 256, e il mondo (u, v) ha il numero 16 u + v.
 *
 * Ogni ramo della dimostrazione porta con sé l'elenco dei mondi ancora
 * possibili, Chase.alive: all'inizio quelli che rispettano le ipotesi; ogni
 * volta che il testo assume qualcosa ("sia x in ...", "caso x in T") si
 * tolgono i mondi in cui non vale. Allora:
 *
 *   - un fatto che il testo afferma come conseguenza deve valere in tutti i
 *     mondi rimasti;
 *   - "questo caso non può presentarsi" richiede che non ne sia rimasto
 *     nessuno;
 *   - quando si distinguono due casi, ogni mondo rimasto deve stare in uno
 *     dei due.
 *
 * Se un controllo fallisce la dimostrazione discorsiva viene abbandonata,
 * come quando i passi concessi finiscono, e il contatore unjustified_steps
 * sale: il verdetto non cambia, perché è già stato stabilito in altro modo,
 * ma quel testo non viene scritto. */

/* Ritorna 1 se nel mondo (u, v) il fatto è vero. */
static int fact_in_world(Fact fact, unsigned u, unsigned v) {
    int inside = fact.node->type == TY_PAIRS ? member(fact.node, u, v) : member(fact.node, fact.coord ? v : u, 0);
    return inside == fact.sign;
}

/* Ritorna 1 se il mondo numero w è ancora possibile nel ramo c. */
static int world_alive(const Chase *c, unsigned w) { return (c->alive[w / 64] >> (w % 64)) & 1; }

/* Da qui in poi il ramo c assume il fatto: toglie i mondi in cui non vale. */
static void worlds_assume(Chase *c, Fact fact) {
    for (unsigned w = 0; w < 256; w++)
        if (!fact_in_world(fact, w >> 4, w & 15)) c->alive[w / 64] &= ~(1ULL << (w % 64));
}

/* Annota che un passo non ha superato il controllo e fa abbandonare la
 * dimostrazione discorsiva. Ritorna 0, per comodità di chi chiama. */
static int step_unjustified(void) {
    unjustified_steps++;
    chase_budget = -1;
    return 0;
}

/* Ritorna 1 se il fatto vale in tutti i mondi possibili nel ramo c; altrimenti
 * annota il passo come non giustificato e ritorna 0. */
static int worlds_entail(const Chase *c, Fact fact) {
    for (unsigned w = 0; w < 256; w++)
        if (world_alive(c, w) && !fact_in_world(fact, w >> 4, w & 15)) return step_unjustified();
    return 1;
}

/* Ritorna 1 se nel ramo c non è rimasto nessun mondo possibile; altrimenti
 * annota il passo come non giustificato e ritorna 0. */
static int worlds_none(const Chase *c) {
    return (c->alive[0] | c->alive[1] | c->alive[2] | c->alive[3]) == 0 ? 1 : step_unjustified();
}

/* Aggiunge un fatto da sviluppare. */
static void chase_push(Chase *c, const SetNode *node, int coord, int sign) {
    if (c->pendings == (int)(sizeof c->pending / sizeof *c->pending)) { chase_budget = -1; return; }
    c->pending[c->pendings++] = (Fact){node, coord, sign};
}

/* Ritorna 1 se da ciò che si sa segue che il punto sta in n, 0 se segue che
 * non ci sta, -1 se non si può ancora dire. */
static int chase_value(const SetNode *n, int coord, const Chase *c) {
    if (n->kind == SET_VAR) return ((c->known[coord] >> n->var) & 1) ? (int)((c->truth[coord] >> n->var) & 1) : -1;
    if (n->kind == SET_EMPTY) return 0;
    int a = chase_value(n->a, n->kind == SET_PRODUCT ? 0 : coord, c);
    int b = chase_value(n->b, n->kind == SET_PRODUCT ? 1 : coord, c);
    switch (n->kind) {
    case SET_UNION:   return a == 1 || b == 1 ? 1 : a == 0 && b == 0 ? 0 : -1;
    case SET_DIFF:    return a == 0 || b == 1 ? 0 : a == 1 && b == 0 ? 1 : -1;
    case SET_SYMDIFF: return a < 0 || b < 0 ? -1 : a != b;
    default:          return a == 0 || b == 0 ? 0 : a == 1 && b == 1 ? 1 : -1;  /* intersezione, prodotto */
    }
}

/* Aggiunge alla dimostrazione il fatto "il punto sta / non sta in n". */
static void put_fact(const SetNode *n, int coord, int sign) {
    proof_add("$%s %s ", n->type == TY_PAIRS ? "(x, y)" : coord ? "y" : "x", sign ? "\\in" : "\\notin");
    put_set(n);
    proof_add("$");
}

/* Aggiunge alla dimostrazione la giustificazione di ciò che chase_value()
 * dice di n: per ogni operazione, quali fatti sui suoi operandi la decidono,
 * partendo dalle più interne. Per esempio "As x in S and x not in T,
 * x in S \ T". Delle lettere non c'è nulla da giustificare. */
static void chase_explain(const SetNode *n, int coord, const Chase *c) {
    if (n->kind == SET_VAR || n->kind == SET_EMPTY) return;
    int ca = n->kind == SET_PRODUCT ? 0 : coord, cb = n->kind == SET_PRODUCT ? 1 : coord;
    int a = chase_value(n->a, ca, c), b = chase_value(n->b, cb, c), sign = chase_value(n, coord, c);

    /* Quali operandi servono: uno solo quando basta a decidere. */
    int use_a = 1, use_b = 1;
    if (n->kind == SET_UNION && sign) { use_a = a == 1; use_b = !use_a; }
    if ((n->kind == SET_INTER || n->kind == SET_PRODUCT) && !sign) { use_a = a == 0; use_b = !use_a; }
    if (n->kind == SET_DIFF && !sign) { use_a = a == 0; use_b = !use_a; }

    if (use_a) chase_explain(n->a, ca, c);
    if (use_b) chase_explain(n->b, cb, c);

    /* 16h. I fatti citati e quello che se ne ricava devono essere veri in
     * tutti i mondi possibili. */
    if ((use_a && !worlds_entail(c, (Fact){n->a, ca, a})) || (use_b && !worlds_entail(c, (Fact){n->b, cb, b})) ||
        !worlds_entail(c, (Fact){n, coord, sign}))
        return;
    proof_add("\\item As ");
    if (use_a) put_fact(n->a, ca, a);
    if (use_a && use_b) proof_add(" and ");
    if (use_b) put_fact(n->b, cb, b);
    proof_add(", ");
    put_fact(n, coord, sign);
    proof_add(".\n");
}

/* Prosegue la dimostrazione che il punto, di cui si sa quanto è in c, sta in
 * goal, scrivendone il testo. Ritorna 1 se ogni caso si chiude, 0 se la
 * dimostrazione va abbandonata.
 *
 * È il modo in cui queste dimostrazioni si scrivono a mano:
 *
 *   16d. Si scompongono i fatti noti con le definizioni: "x sta in A meno B"
 *        dà "x sta in A" e "x non sta in B". Quando la definizione lascia due
 *        possibilità, come per "x sta in A unito B", si distinguono due casi.
 *   16e. Se ormai si sa che il punto sta in goal, lo si giustifica e il caso è
 *        chiuso.
 *   16f. Altrimenti si usa un'ipotesi A contenuto in B: se il punto sta in A
 *        allora sta in B, e se non sta in B allora non sta in A.
 *   16g. Se nessuna ipotesi dice qualcosa di nuovo, si distinguono due casi
 *        secondo che x stia o no in una lettera di cui non si sa ancora nulla.
 *
 * Un caso si chiude anche quando ciò che si sa è contraddittorio: non può
 * presentarsi. Ogni passo aggiunge un'informazione su un numero finito di
 * lettere, quindi il procedimento termina. */
static int chase(Chase c, const SetNode *goal) {
    if (--chase_budget < 0) return 0;

    /* 16d. Scomposizione dei fatti in attesa. Si prende per primo il fatto
     * più semplice: una lettera, poi un fatto già deciso da ciò che si sa, poi
     * uno che si scompone senza casi. Così i casi si aprono solo quando sono
     * inevitabili, e spesso ciò che si è appreso nel frattempo li rende
     * inutili. */
    while (c.pendings > 0) {
        int pick = 0, best = -1;
        for (int i = 0; i < c.pendings; i++) {
            const SetNode *m = c.pending[i].node;
            int sign = c.pending[i].sign, rank = 0;
            if (m->kind == SET_VAR) rank = 3;
            else if (chase_value(m, c.pending[i].coord, &c) >= 0) rank = 2;
            else if (sign ? m->kind == SET_INTER || m->kind == SET_PRODUCT || m->kind == SET_DIFF : m->kind == SET_UNION) rank = 1;
            if (rank >= best) { best = rank; pick = i; }
        }
        Fact fact = c.pending[pick];
        c.pending[pick] = c.pending[--c.pendings];
        const SetNode *n = fact.node;
        int now = chase_value(n, fact.coord, &c);
        if (now == fact.sign) continue;
        if (now >= 0) {
            /* Ciò che si sa dice il contrario: il caso non può presentarsi. */
            if (!worlds_none(&c)) return 0;
            if (n->kind == SET_EMPTY) {
                proof_add("\\item But no element belongs to $\\emptyset$, so this case cannot occur.\n");
                return 1;
            }
            chase_explain(n, fact.coord, &c);
            proof_add("\\item This contradicts ");
            put_fact(n, fact.coord, fact.sign);
            proof_add(", so this case cannot occur.\n");
            return 1;
        }
        if (n->kind == SET_VAR) {
            c.known[fact.coord] |= 1u << n->var;
            if (fact.sign) c.truth[fact.coord] |= 1u << n->var;
            continue;
        }

        /* Le due possibilità che la definizione lascia aperte, ognuna fatta
         * di uno o due fatti sugli operandi; se è una sola, i suoi fatti
         * valgono insieme. */
        int ca = n->kind == SET_PRODUCT ? 0 : fact.coord, cb = n->kind == SET_PRODUCT ? 1 : fact.coord;
        Fact option[2][2];
        int size[2] = {0, 0}, options = 2;
        if ((fact.sign && (n->kind == SET_INTER || n->kind == SET_PRODUCT || n->kind == SET_DIFF)) ||
            (!fact.sign && n->kind == SET_UNION)) {
            options = 1;
            option[0][size[0]++] = (Fact){n->a, ca, fact.sign};
            option[0][size[0]++] = (Fact){n->b, cb, n->kind == SET_DIFF ? 0 : fact.sign};
        } else if (n->kind == SET_SYMDIFF) {
            option[0][size[0]++] = (Fact){n->a, ca, 1};
            option[0][size[0]++] = (Fact){n->b, cb, !fact.sign};
            option[1][size[1]++] = (Fact){n->a, ca, 0};
            option[1][size[1]++] = (Fact){n->b, cb, fact.sign};
        } else {
            option[0][size[0]++] = (Fact){n->a, ca, fact.sign};
            option[1][size[1]++] = (Fact){n->b, cb, n->kind == SET_DIFF ? 1 : fact.sign};
        }

        /* Una possibilità già smentita da ciò che si sa non va considerata. */
        int open[2] = {0, 0}, opens = 0;
        for (int i = 0; i < options; i++) {
            open[i] = 1;
            for (int j = 0; j < size[i]; j++)
                if (chase_value(option[i][j].node, option[i][j].coord, &c) == !option[i][j].sign) open[i] = 0;
            opens += open[i];
        }
        if (opens == 0) {
            if (!worlds_none(&c)) return 0;
            proof_add("\\item But ");
            put_fact(n, fact.coord, fact.sign);
            proof_add(" is impossible here, so this case cannot occur.\n");
            return 1;
        }
        if (opens == 1) {
            int only = open[0] ? 0 : 1;
            for (int j = 0; j < size[only]; j++)
                if (!worlds_entail(&c, option[only][j])) return 0;
            proof_add("\\item Then ");
            for (int j = 0; j < size[only]; j++) {
                if (j) proof_add(" and ");
                put_fact(option[only][j].node, option[only][j].coord, option[only][j].sign);
                chase_push(&c, option[only][j].node, option[only][j].coord, option[only][j].sign);
            }
            proof_add(".\n");
            continue;
        }

        /* Due casi, ognuno proseguito per conto suo in un elenco rientrato. */
        if (chase_depth == 3) return 0;

        /* 16h. I due casi devono coprire tutti i mondi possibili. */
        for (unsigned w = 0; w < 256; w++) {
            int covered = 0;
            for (int i = 0; i < 2 && !covered; i++) {
                covered = 1;
                for (int j = 0; j < size[i]; j++)
                    if (!fact_in_world(option[i][j], w >> 4, w & 15)) covered = 0;
            }
            if (world_alive(&c, w) && !covered) return step_unjustified();
        }
        proof_add("\\item Two cases are possible.\n");
        for (int i = 0; i < 2; i++) {
            Chase branch = c;
            proof_add("\\item \\emph{Case} ");
            for (int j = 0; j < size[i]; j++) {
                if (j) proof_add(" and ");
                put_fact(option[i][j].node, option[i][j].coord, option[i][j].sign);
                chase_push(&branch, option[i][j].node, option[i][j].coord, option[i][j].sign);
                worlds_assume(&branch, option[i][j]);
            }
            proof_add(":\n\\begin{itemize}\n");
            branch.list_start = proof_length;
            chase_depth++;
            int closed = chase(branch, goal);
            chase_depth--;
            if (!closed) return 0;
            proof_add("\\end{itemize}\n");
        }
        return 1;
    }

    /* 16e. La tesi è raggiunta. Se non c'è nulla da giustificare, perché la
     * tesi è tra i fatti già noti, e l'elenco dei passaggi è ancora vuoto, la
     * si enuncia comunque: in LaTeX un elenco non può restare senza voci. */
    if (chase_value(goal, 0, &c) == 1) {
        chase_explain(goal, 0, &c);
        if (!worlds_entail(&c, (Fact){goal, 0, 1})) return 0;
        if (proof_length == c.list_start) {
            proof_add("\\item So ");
            put_fact(goal, 0, 1);
            proof_add(".\n");
        }
        return 1;
    }

    /* 16f. Un'ipotesi che aggiunge un fatto nuovo. */
    for (int i = 0; i < hypotheses; i++) {
        const SetNode *sub = hypothesis_sub[i], *sup = hypothesis_sup[i];
        int inside = chase_value(sub, 0, &c), above = chase_value(sup, 0, &c);
        int forward = inside == 1 && above != 1, backward = above == 0 && inside != 0;
        if (!forward && !backward) continue;
        chase_explain(forward ? sub : sup, 0, &c);
        if (!worlds_entail(&c, (Fact){forward ? sup : sub, 0, forward})) return 0;
        proof_add("\\item Since $");
        put_set(sub);
        proof_add(" \\subseteq ");
        put_set(sup);
        proof_add("$ by assumption, ");
        put_fact(forward ? sup : sub, 0, forward);
        proof_add(".\n");
        chase_push(&c, forward ? sup : sub, 0, forward);
        return chase(c, goal);
    }

    /* 16g. Due casi su una lettera di cui non si sa ancora nulla. */
    for (int coord = 0; coord < 2; coord++)
        for (int var = 0; var < set_var_count; var++) {
            if (!((chase_letters[coord] >> var) & 1) || ((c.known[coord] >> var) & 1)) continue;
            if (chase_depth == 3) return 0;
            proof_add("\\item Two cases are possible.\n");
            for (int sign = 1; sign >= 0; sign--) {
                Chase branch = c;
                SetNode letter = {SET_VAR, TY_SET, var, NULL, NULL, NULL, 0};
                branch.known[coord] |= 1u << var;
                if (sign) branch.truth[coord] |= 1u << var;
                worlds_assume(&branch, (Fact){&letter, coord, sign});
                proof_add("\\item \\emph{Case} $%s %s %c$:\n\\begin{itemize}\n",
                          coord ? "y" : "x", sign ? "\\in" : "\\notin", set_var_name[var]);
                branch.list_start = proof_length;
                chase_depth++;
                int closed = chase(branch, goal);
                chase_depth--;
                if (!closed) return 0;
                proof_add("\\end{itemize}\n");
            }
            return 1;
        }
    return 0;
}

/* Ritorna le lettere che compaiono nel sotto-albero, un bit per lettera. */
static unsigned set_letters(const SetNode *n) {
    if (!n) return 0;
    return (n->kind == SET_VAR ? 1u << n->var : 0) | set_letters(n->a) | set_letters(n->b);
}

/* Scrive la dimostrazione che ogni punto di sub sta in sup, con le ipotesi
 * correnti. Ritorna 0 se va abbandonata. L'insieme vuoto è contenuto in ogni
 * insieme, e in quel caso non c'è nulla da scrivere. converse diverso da zero
 * fa cominciare il testo con "Conversely": è la seconda metà di
 * un'uguaglianza. */
static int narrate_inclusion(const SetNode *sub, const SetNode *sup, int converse) {
    if (sub->kind == SET_EMPTY) return 1;
    int pairs = sub->type == TY_PAIRS || sup->type == TY_PAIRS;
    Chase start = {0};

    /* Le lettere su cui distinguere i casi: per le coppie quelle dei primi e
     * dei secondi fattori, per gli elementi quelle dei due membri e delle
     * ipotesi. */
    chase_letters[0] = chase_letters[1] = 0;
    if (pairs) {
        product_factors(sub, &chase_letters[0], &chase_letters[1], NULL);
        product_factors(sup, &chase_letters[0], &chase_letters[1], NULL);
    } else {
        chase_letters[0] = set_letters(sub) | set_letters(sup);
        for (int i = 0; i < hypotheses; i++) chase_letters[0] |= set_letters(hypothesis_sub[i]) | set_letters(hypothesis_sup[i]);
    }

    proof_add("%s $%s \\in ", sup->kind == SET_EMPTY ? (converse ? "Conversely, suppose that" : "Suppose that")
                                                       : (converse ? "Conversely, let" : "Let"), pairs ? "(x, y)" : "x");
    put_set(sub);
    proof_add("$.\n\\begin{itemize}\n");
    start.list_start = proof_length;
    chase_push(&start, sub, 0, 1);

    /* 16h. I mondi possibili all'inizio: quelli che rispettano le ipotesi,
     * ristretti poi a quelli in cui il punto sta in sub. */
    unsigned regions = 1u << set_var_count;
    for (unsigned u = 0; u < regions; u++)
        for (unsigned v = 0; v < regions; v++) {
            int possible = 1;
            for (int i = 0; i < hypotheses; i++)
                if (fact_in_world((Fact){hypothesis_sub[i], 0, 1}, u, v) && !fact_in_world((Fact){hypothesis_sup[i], 0, 1}, u, v))
                    possible = 0;
            if (possible) start.alive[(16 * u + v) / 64] |= 1ULL << ((16 * u + v) % 64);
        }
    worlds_assume(&start, (Fact){sub, 0, 1});
    if (!chase(start, sup)) return 0;
    proof_add("\\end{itemize}\n");
    if (sup->kind == SET_EMPTY) {
        proof_add("So there is no such element.\n\n");
    } else {
        proof_add("Hence $");
        put_set(sub);
        proof_add(" \\subseteq ");
        put_set(sup);
        proof_add("$.\n\n");
    }
    return 1;
}

/* Scrive la dimostrazione di tutte le relazioni della congiunzione n: di ogni
 * inclusione direttamente, di ogni uguaglianza con le due inclusioni. */
static int narrate_goals(const SetNode *n) {
    if (n->kind == SET_AND) return narrate_goals(n->a) && narrate_goals(n->b);
    if (!narrate_inclusion(n->a, n->b, 0)) return 0;
    if (n->kind == SET_SUBSET) return 1;
    if (!narrate_inclusion(n->b, n->a, n->a->kind != SET_EMPTY)) return 0;
    proof_add("Therefore $");
    put_set(n);
    proof_add("$.\n\n");
    return 1;
}

/* Aggiunge alle ipotesi le relazioni della congiunzione n: un'inclusione così
 * com'è, un'uguaglianza come due inclusioni. */
static void add_hypotheses(const SetNode *n) {
    if (n->kind == SET_AND) { add_hypotheses(n->a); add_hypotheses(n->b); return; }
    for (int way = 0; way < (n->kind == SET_EQ ? 2 : 1) && hypotheses < 16; way++) {
        hypothesis_sub[hypotheses] = way ? n->b : n->a;
        hypothesis_sup[hypotheses++] = way ? n->a : n->b;
    }
}

/* Ritorna 1 se n è una congiunzione di inclusioni e uguaglianze tra insiemi di
 * elementi; con pairs diverso da zero sono ammessi anche gli insiemi di
 * coppie. */
static int set_is_plain(const SetNode *n, int pairs) {
    if (n->kind == SET_AND) return set_is_plain(n->a, pairs) && set_is_plain(n->b, pairs);
    if (n->kind != SET_EQ && n->kind != SET_SUBSET) return 0;
    SetType type = set_join(n->a->type, n->b->type);
    return type == TY_SET || type == TY_ANY || (pairs && type == TY_PAIRS);
}

/* Forma discorsiva, quella preferita: se root è un'inclusione o
 * un'uguaglianza, oppure un'implicazione o un'equivalenza tra condizioni di
 * quel tipo (anche sotto ipotesi dello stesso tipo), scrive la dimostrazione
 * per inseguimento degli elementi e ritorna 1. Altrimenti, o se i casi da
 * distinguere sono troppi, non lascia nulla e ritorna 0.
 *
 * Con delle ipotesi sono ammessi solo insiemi di elementi: le ipotesi vengono
 * applicate al punto x, non a una coppia. */
static int put_narrative_proof(const SetNode *root) {
    const SetNode *given = NULL, *core = root;
    if (root->kind == SET_IMPLIES) { given = root->a; core = root->b; }
    int equivalence = core->kind == SET_IFF;
    if (given && !set_is_plain(given, 0)) return 0;
    if (equivalence ? !set_is_plain(core->a, 0) || !set_is_plain(core->b, 0) : !set_is_plain(core, !given)) return 0;

    hypotheses = 0;
    chase_budget = 300;
    chase_depth = 0;
    proof_add("\\textbf{Proof.} ");
    if (given) {
        add_hypotheses(given);
        proof_add("Assume $");
        put_set(given);
        proof_add("$.\n\n");
    }
    int complete;
    if (!equivalence) {
        complete = narrate_goals(core);
    } else {
        /* Le due implicazioni, ognuna con il proprio lato come ipotesi. */
        int kept = hypotheses;
        add_hypotheses(core->a);
        proof_add("\\smallskip ($\\Rightarrow$) Assume that $");
        put_set(core->a);
        proof_add("$.\n\n");
        complete = narrate_goals(core->b);
        hypotheses = kept;
        add_hypotheses(core->b);
        proof_add("\\smallskip ($\\Leftarrow$) Conversely, assume that $");
        put_set(core->b);
        proof_add("$.\n\n");
        complete = complete && narrate_goals(core->a);
    }
    if (!complete || chase_budget < 0) { proof_reset(); return 0; }
    proof_add("\\hfill $\\Box$");
    return 1;
}

/* Il controesempio di un enunciato falso, come testo: vale fino al verdetto
 * successivo. */
static _Thread_local char counterexample_text[256];

/* Scrive in counterexample_text gli insiemi value[], sottoinsiemi di un
 * universo di size elementi, per esempio "S = {1, 2}, T = {}". Riporta solo
 * le lettere il cui indice ha il bit in listed. */
static void sets_describe(const unsigned *value, int size, unsigned listed) {
    size_t length = 0;
    counterexample_text[0] = 0;
    for (int i = 0; i < set_var_count; i++) {
        if (!((listed >> i) & 1)) continue;
        length += (size_t)snprintf(counterexample_text + length, sizeof counterexample_text - length,
                                   "%s%c = {", length ? ", " : "", set_var_name[i]);
        for (int e = 0, printed = 0; e < size && length < sizeof counterexample_text; e++)
            if ((value[i] >> e) & 1)
                length += (size_t)snprintf(counterexample_text + length, sizeof counterexample_text - length,
                                           "%s%d", printed++ ? ", " : "", e + 1);
        if (length < sizeof counterexample_text)
            length += (size_t)snprintf(counterexample_text + length, sizeof counterexample_text - length, "}");
    }
}

/* Scrive nella dimostrazione che l'enunciato è falso, con gli stessi insiemi
 * di sets_describe() come controesempio. */
static void put_counterexample(const unsigned *value, int size, unsigned listed) {
    proof_add("The statement is false. Counterexample: $");
    for (int i = 0, printed = 0; i < set_var_count; i++) {
        if (!((listed >> i) & 1)) continue;
        proof_add("%s%c = ", printed++ ? ",\\ " : "", set_var_name[i]);
        if (!value[i]) { proof_add("\\emptyset"); continue; }
        proof_add("\\{");
        for (int e = 0, listed_elements = 0; e < size; e++)
            if ((value[i] >> e) & 1) proof_add("%s%d", listed_elements++ ? ", " : "", e + 1);
        proof_add("\\}");
    }
    proof_add("$.");
}

/* Costruisce con configuration_sets() gli insiemi che realizzano la
 * configurazione nonempty e ne scrive la descrizione in counterexample_text.
 * bound, se non è -1, è l'indice di un insieme da non riportare. */
static void counterexample(unsigned nonempty, int bound, unsigned *value, int *size) {
    configuration_sets(nonempty, value, size);
    sets_describe(value, *size, bound < 0 ? ~0u : ~(1u << bound));
}

/* 16i. Controllo dell'insieme scelto per un "esiste" (15e): l'unione delle
 * regioni di mask, per la lettera del quantificatore exists. Per ogni scelta
 * degli altri insiemi tra i sottoinsiemi di un universo di size elementi si
 * costruisce davvero quell'insieme e si calcola la condizione del
 * quantificatore; se other non è NULL basta che valga quando vale other.
 * Ritorna 1 se regge sempre; altrimenti annota il passo come non giustificato
 * e ritorna 0. */
static int witness_confirmed(const SetNode *exists, const SetNode *other, unsigned mask, int size) {
    unsigned value[MAX_SET_VARS] = {0};
    for (;;) {
        /* Un elemento sta nell'insieme scelto se la sua regione rispetto agli
         * altri insiemi è una di quelle di mask. In quella regione gli altri
         * insiemi occupano i bit in ordine, saltando la lettera di exists. */
        value[exists->var] = 0;
        for (int e = 0; e < size; e++) {
            unsigned region = 0;
            for (int i = 0, place = 0; i < set_var_count; i++)
                if (i != exists->var) region |= ((value[i] >> e) & 1) << place++;
            if ((mask >> region) & 1) value[exists->var] |= 1u << e;
        }
        if ((!other || concrete_holds(other, value, size)) && !concrete_holds(exists->a, value, size)) {
            unjustified_steps++;
            return 0;
        }

        /* Assegnazione successiva degli altri insiemi, come in
         * concrete_valid(). */
        int i = 0;
        for (; i < set_var_count; i++) {
            if (i == exists->var) continue;
            if (++value[i] < (1u << size)) break;
            value[i] = 0;
        }
        if (i == set_var_count) return 1;
    }
}

/* Scrive l'enunciato sugli insiemi n nella notazione dei certificati
 * (capitolo 10 di checker.c): la parola davanti, e tutte le parentesi. Un
 * "esiste un insieme" non ha scrittura.
 *
 * Warning: se aggiungi un tipo di nodo, aggiungi qui la sua parola, e la
 * parola al verificatore; altrimenti l'enunciato resta senza certificato. */
static void cert_set(const SetNode *n) {
    static const char *const word[] = {
        [SET_EMPTY] = "empty", [SET_ONLY_EMPTY] = "onlyempty", [SET_POWER] = "power",
        [SET_UNION] = "union", [SET_INTER] = "inter", [SET_DIFF] = "diff", [SET_SYMDIFF] = "symdiff", [SET_PRODUCT] = "times",
        [SET_EQ] = "=", [SET_SUBSET] = "subset", [SET_NEQ] = "neq",
        [SET_AND] = "and", [SET_OR] = "or", [SET_IMPLIES] = "implies", [SET_IFF] = "iff", [SET_NOT] = "not",
    };
    if (n->kind == SET_VAR) { cert_letter(set_var_name[n->var]); return; }
    if (n->kind == SET_EXISTS) { certificate_broken = 1; return; }
    cert_add("(%s", word[n->kind]);
    if (n->a) { cert_add(" "); cert_set(n->a); }
    if (n->b) { cert_add(" "); cert_set(n->b); }
    cert_add(")");
}

/* Verifica indipendente di 15f. Ritorna 1 se root è vera per ogni scelta
 * degli insiemi liberi, quelli con il bit in free_letters, tra i
 * sottoinsiemi dei primi `inner` elementi di un universo di `size` elementi:
 * ogni espressione viene calcolata davvero, come insieme, e ogni "esiste un
 * insieme" prova tutti i sottoinsiemi di un universo che cresce di un
 * elemento a ogni quantificatore (concrete_holds()). Gli elementi oltre i
 * primi `inner` stanno fuori da ogni insieme libero: sono gli oggetti di cui
 * 15f dice che ce n'è quanti se ne vuole. */
static int concrete_valid_freely(const SetNode *root, unsigned free_letters, int inner, int size) {
    unsigned value[MAX_SET_VARS] = {0};
    for (;;) {
        if (!concrete_holds(root, value, size)) return 0;

        /* Assegnazione successiva dei soli insiemi liberi, come in
         * concrete_valid(). Gli altri li riscrive chi li quantifica. */
        int i = 0;
        for (; i < set_var_count; i++) {
            if (!((free_letters >> i) & 1)) continue;
            if (++value[i] < (1u << inner)) break;
            value[i] = 0;
        }
        if (i == set_var_count) return 1;
    }
}

/* 15f, con la sua verifica e il suo testo: decide l'enunciato root contando
 * gli elementi delle regioni, e completa verdict.
 *
 * Il conto non viene creduto sulla parola. Se dice "vero", l'enunciato deve
 * valere in tutti gli universi piccoli di concrete_valid_freely(); se dice
 * "falso", gli insiemi del controesempio vengono costruiti e l'enunciato
 * calcolato su di loro. Sono controlli parziali, perché l'universo è
 * piccolo: un enunciato vero che ha bisogno di molti oggetti fuori dagli
 * insiemi, o un controesempio con più di qualche elemento, non vengono
 * confermati, e allora il verdetto è NON DIMOSTRATO. */
static Verdict prove_sets_by_counting(const SetNode *root, Verdict verdict) {
    unsigned char count[1u << MAX_SET_VARS];
    unsigned free_letters = set_free_letters(root, 0), value[MAX_SET_VARS] = {0};
    int depth = set_depth(root);
    verdict.outcome = NOT_PROVED;

    /* Con le lettere che si possono riusare i quantificatori uno dentro
     * l'altro non hanno un limite, ma i numeri di elementi (fino a 2^q) e la
     * verifica (32^q casi) sì. */
    int valid = depth <= MAX_SET_VARS ? counts_valid(root, count) : -1;
    if (valid < 0) {
        verdict.reason = "troppi casi da esaminare, contando gli elementi delle regioni";
        return verdict;
    }

    /* Falso: gli insiemi liberi con, in ogni regione, gli elementi contati
     * ("almeno" diventa proprio quel numero), più quanti oggetti esterni
     * stanno in un universo di 5. */
    if (!valid) {
        int size = 0;
        for (unsigned region = 1; region < (1u << set_var_count); region++)
            for (int e = 0; e < count[region] && size <= 5; e++, size++)
                for (int i = 0; i < set_var_count; i++)
                    if ((region >> i) & 1) value[i] |= 1u << size;
        if (size > 5 || concrete_holds(root, value, 5)) {
            verdict.reason = "la verifica indipendente non conferma il controesempio trovato contando gli elementi delle regioni";
            return verdict;
        }
        /* Senza insiemi liberi non c'è una scelta da riportare. */
        sets_describe(value, size, free_letters);
        if (free_letters) put_counterexample(value, size, free_letters);
        else proof_add("The statement is false: no letter is left free, and counting the elements of the regions shows that it fails.");
        verdict.outcome = REFUTED;
        verdict.detail = free_letters ? counterexample_text : NULL;
        verdict.proof = proof_text;
        return verdict;
    }

    /* Vero: verifica indipendente su un universo piccolo, che per il
     * quantificatore più esterno ha cinque elementi (quattro quando i
     * quantificatori annidati sono tre o più, perché i casi crescono in
     * fretta: 32 * 64 * 128 * ...). */
    if (!concrete_valid_freely(root, free_letters, 3, depth <= 2 ? 4 : 3)) {
        verdict.reason = "la verifica indipendente ha trovato un caso in cui l'enunciato non vale";
        return verdict;
    }
    proof_add("\\textbf{Proof.} The statement has quantifiers over sets, at most $%d$ inside one another. Whether it holds for given "
              "sets depends only on the number of elements of each region of their Venn diagram, and only up to $%d$: two "
              "choices of the sets whose regions have the same numbers of elements, or both at least $%d$, cannot be told apart, "
              "because a set that works for one choice divides each region into two parts, and the corresponding region of the "
              "other choice can be divided into parts with the same numbers of elements, or both at least half of $%d$. So each "
              "region is given $0, 1, \\ldots$ or at least $%d$ elements, the part outside all the sets always at least $%d$, and for "
              "each quantified set every way of dividing the regions is tried. The statement holds in all these cases. $\\Box$",
              depth, 1 << depth, 1 << depth, 1 << depth, 1 << depth, 1 << depth);
    verdict.outcome = PROVED;
    verdict.proof = proof_text;
    return verdict;
}

/* Decide l'enunciato sugli insiemi root, già letto e con i tipi controllati
 * (set_check()), e ne ritorna il verdetto, con la dimostrazione scritta o il
 * controesempio. È la seconda metà di prove_sets(), che serve anche a
 * prove_parts() (17r). */
static Verdict prove_set_tree(SetNode *root) {
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, "per ogni scelta degli insiemi", NULL, NULL};
    set_prepare(root);
    if (failure) { verdict.reason = failure; return verdict; }

    /* Il quantificatore, se c'è: uno solo, e solo come enunciato intero o come
     * uno dei due lati di un'equivalenza o di un'implicazione. */
    const SetNode *exists = NULL, *other = NULL;
    int as_hypothesis = 0, as_thesis = 0;
    if (root->kind == SET_EXISTS) {
        exists = root;
        as_thesis = 1;
    } else if (root->kind == SET_IFF || root->kind == SET_IMPLIES) {
        if (root->a->kind == SET_EXISTS) { exists = root->a; other = root->b; as_hypothesis = 1; as_thesis = root->kind == SET_IFF; }
        else if (root->b->kind == SET_EXISTS) { exists = root->b; other = root->a; as_thesis = 1; as_hypothesis = root->kind == SET_IFF; }
    }
    int quantifiers = 0;
    for (const SetNode *stack[64], **top = stack, *n = root; n || top > stack; ) {
        if (!n) { n = *--top; continue; }
        if (n->kind == SET_EXISTS) quantifiers++;
        if (n->b && top < stack + 64) *top++ = n->b;
        n = n->a;
    }
    /* 15f. Più quantificatori, o uno in un'altra posizione: contando gli
     * elementi delle regioni. */
    if (quantifiers > (exists ? 1 : 0)) return prove_sets_by_counting(root, verdict);

    /* Decisione per regioni (capitolo 15). */
    unsigned all = (1u << (1u << set_var_count)) - 1, failing = 0, mask = 0;
    int valid, found = 1;
    if (!exists) {
        valid = set_valid(root, all, &failing);
    } else {
        /* 15d: "esiste V" come ipotesi, con V arbitrario. */
        SetNode to_other = {SET_IMPLIES, TY_FORMULA, 0, (SetNode *)exists, (SetNode *)other, NULL, 0};
        SetNode to_exists = {SET_IMPLIES, TY_FORMULA, 0, (SetNode *)other, (SetNode *)exists, NULL, 0};
        valid = !as_hypothesis || set_valid(&to_other, all, &failing);

        /* 15e: "esiste V" come tesi, cercando V tra le unioni di regioni. */
        if (valid && as_thesis) {
            unsigned ignored = 0, candidates = 1u << (1u << (set_var_count - 1));
            const SetNode *goal = other ? &to_exists : exists;
            found = 0;
            for (mask = 0; mask < candidates && !found; mask++)
                found = set_valid(goal, witness_regions(exists->var, mask), &ignored);
            mask--;
        }
    }
    /* 15f. Nessuna unione di regioni va bene: l'insieme cercato, se c'è,
     * divide una regione, e lo si trova contando. */
    if (valid && !found) return prove_sets_by_counting(root, verdict);

    /* Enunciato falso: il controesempio, ricontrollato calcolando davvero. */
    if (!valid) {
        unsigned value[MAX_SET_VARS];
        int size;
        counterexample(failing, exists ? exists->var : -1, value, &size);
        if (size > 5 || concrete_holds(root, value, size)) {
            verdict.outcome = NOT_PROVED;
            verdict.reason = "la verifica indipendente non conferma il controesempio";
            return verdict;
        }
        put_counterexample(value, size, exists ? ~(1u << exists->var) : ~0u);
        verdict.outcome = REFUTED;
        verdict.detail = counterexample_text;
        verdict.proof = proof_text;
        return verdict;
    }

    /* Enunciato vero: verifica indipendente su un universo piccolo. Con più
     * insiemi l'universo è più piccolo, perché le assegnazioni restino
     * poche migliaia. */
    int free_sets = set_var_count - (exists ? 1 : 0), universe = free_sets >= 4 ? 3 : 4;
    if (!concrete_valid(root, exists ? exists->var : -1, universe)) {
        verdict.outcome = NOT_PROVED;
        verdict.reason = "la verifica indipendente ha trovato un caso in cui l'enunciato non vale";
        return verdict;
    }

    /* Dimostrazione scritta (capitolo 16), con il controllo di ciò che
     * afferma: se nemmeno la forma generale lo supera, non c'è un testo di
     * cui fidarsi e il verdetto non viene emesso. */
    int written = 1;
    if (exists || (!put_narrative_proof(root) && !put_table_proof(root) && !put_comparison_proof(root)))
        written = (!as_thesis || witness_confirmed(exists, other, mask, universe)) &&
                  put_general_proof(root, as_thesis ? exists : NULL, mask);
    if (!written) {
        verdict.outcome = NOT_PROVED;
        verdict.reason = "la dimostrazione scritta non ha superato il controllo dei suoi passi";
        return verdict;
    }

    /* Il certificato: l'enunciato, che il verificatore indipendente decide
     * da capo con il suo conto (capitolo 10 di checker.c). Se lo trova
     * falso, i due programmi non sono d'accordo: nel dubbio non è
     * dimostrato. "Esiste un insieme" il verificatore non lo tratta. */
    certificate_length = 0;
    certificate_broken = exists != NULL;
    cert_add("certificate sets\nstatement ");
    cert_set(root);
    cert_add("\nend\n");
    if (!certificate_broken) {
        const char *text = certificate_text, *why;
        CkAnswer answer = ck_check(&text, &why, checker_steps());
        if (answer == CK_REJECTED) {
            unjustified_steps++;
            snprintf(certificate_problem, sizeof certificate_problem, "il verificatore indipendente ha respinto il certificato: %s", why);
            verdict.outcome = NOT_PROVED;
            verdict.reason = certificate_problem;
            return verdict;
        }
        if (answer == CK_ACCEPTED) verdict.certificate = certificate_text;
    }
    verdict.outcome = PROVED;
    verdict.proof = proof_text;
    return verdict;
}

/* Decide l'enunciato sugli insiemi scritto in formula e ne ritorna il
 * verdetto, con la dimostrazione scritta o il controesempio.
 *
 * Svuota l'arena: i risultati di chiamate precedenti non sono più validi. */
Verdict prove_sets(const char *formula) {
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, "per ogni scelta degli insiemi", NULL, NULL};

    /* Ripartenza da zero e parsing. */
    proof_reset();
    arena_used = arena_keep;
    failure = NULL;
    set_var_count = 0;
    syntax_error = NULL;
    cursor = formula;
    next_token();
    SetNode *root = set_formula();
    if (token.kind != T_END) syntax("testo inatteso dopo l'enunciato");
    if (syntax_error) { verdict.reason = syntax_error; return verdict; }
    if (failure) { verdict.reason = failure; return verdict; }
    if (set_check(root) != TY_FORMULA) {
        verdict.reason = "enunciato sugli insiemi mal formato: operandi di tipo diverso, o manca una relazione";
        return verdict;
    }
    return prove_set_tree(root);
}

/* 17r. Il controllo dello svolgimento di un enunciato su relazioni e
 * applicazioni tra parti (vedi la testa di 17r in parser.c). written è
 * l'enunciato com'è scritto, con le sue letters lettere; unfolded quello
 * svolto, con le lettere di parts_reindex(), e free_map[] dice l'indice
 * nuovo di ogni lettera libera. Per ogni scelta delle lettere libere tra le
 * parti di un universo piccolo, i due enunciati devono avere lo stesso
 * valore: written calcolato con le regole (concrete_holds() su SET_PAIR_IN e
 * SET_APPLY), unfolded con le regole già sostituite. Ritorna quante scelte
 * ha confrontato, o -1 se in una i due valori sono diversi.
 *
 * Gli universi hanno uno, due e, se i quantificatori uno dentro l'altro
 * sono al più due, tre elementi: ogni quantificatore li fa crescere di uno
 * (concrete_holds()), e le scelte crescono in fretta. */
static long long parts_check(const SetNode *written, int letters, const SetNode *unfolded, const int *free_map) {
    unsigned book[MAX_SET_LETTERS], plain[MAX_SET_LETTERS];
    long long compared = 0;
    int frees = 0, depth = set_depth(unfolded);
    for (int i = 0; i < letters; i++) frees += free_map[i] >= 0;
    for (int size = 1; size <= (depth <= 2 ? 3 : 2); size++) {
        unsigned choices = 1u << (size * frees);
        for (unsigned code = 0; code < choices; code++) {
            /* La scelta code: le parti delle lettere libere, size bit l'una,
             * le stesse nei due enunciati. */
            memset(book, 0, sizeof book);
            memset(plain, 0, sizeof plain);
            for (int i = 0; i < letters; i++) {
                if (free_map[i] < 0) continue;
                book[i] = plain[free_map[i]] = (code >> (size * free_map[i])) & ((1u << size) - 1);
            }
            if (concrete_holds(written, book, size) != concrete_holds(unfolded, plain, size)) return -1;
            compared++;
        }
    }
    return compared;
}

/* 17r. Decide l'enunciato su relazioni e applicazioni tra le parti di un
 * insieme scritto in formula: lo legge con il lettore del capitolo 14 e le
 * scritture di 17r, lo svolge, ricontrolla lo svolgimento (parts_check()) e
 * passa l'enunciato svolto al capitolo 15. Il verdetto è quello del capitolo
 * 15, e la dimostrazione dice in più che cosa è stato svolto e come lo si è
 * ricontrollato.
 *
 * Svuota l'arena: i risultati di chiamate precedenti non sono più validi. */
Verdict prove_parts(const char *formula) {
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, "per ogni scelta degli insiemi", NULL, NULL};
    int free_map[MAX_SET_LETTERS];

    /* Ripartenza da zero e parsing, con le scritture di 17r. */
    proof_reset();
    arena_used = arena_keep;
    failure = NULL;
    set_var_count = part_rule_count = 0;
    syntax_error = NULL;
    cursor = formula;
    next_token();
    parts_world = 1;
    SetNode *written = set_formula();
    parts_world = 0;
    if (token.kind != T_END) syntax("testo inatteso dopo l'enunciato");
    for (int i = 0; i < part_rule_count && !syntax_error; i++)
        if (!part_rules[i].rule) syntax("un'applicazione tra parti dichiarata va data con la sua regola, \\forall X \\in \\mathcal{P}(S)\\ (f(X) = ...)");
    if (syntax_error || failure) { verdict.reason = syntax_error ? syntax_error : failure; return verdict; }
    if (set_check(written) != TY_FORMULA) {
        verdict.reason = "enunciato sugli insiemi mal formato: operandi di tipo diverso, o manca una relazione";
        return verdict;
    }

    /* Lo svolgimento, le lettere nuove, e il controllo. */
    int letters = set_var_count;
    memset(parts_to, 0, sizeof parts_to);
    SetNode *root = parts_unfold(written);
    if (root == &parts_declared) { verdict.reason = "l'enunciato dichiara delle relazioni o delle applicazioni tra parti, ma non ne dice nulla"; return verdict; }
    if (parts_declaration_left(root)) {
        verdict.reason = "una relazione o un'applicazione tra parti si dichiara solo tra le ipotesi, in cima all'enunciato";
        return verdict;
    }
    parts_reindex(root, free_map);
    if (syntax_error) { verdict.reason = syntax_error; return verdict; }
    if (set_check(root) != TY_FORMULA) {
        verdict.reason = "enunciato sugli insiemi mal formato, una volta svolte le relazioni e le applicazioni tra parti";
        return verdict;
    }
    long long compared = parts_check(written, letters, root, free_map);
    if (compared < 0) {
        unjustified_steps++;
        verdict.outcome = NOT_PROVED;
        verdict.reason = "lo svolgimento delle relazioni e delle applicazioni tra parti, ricalcolato su universi piccoli, non dà lo stesso enunciato";
        return verdict;
    }

    /* La decisione del capitolo 15, e nella dimostrazione ciò che è stato
     * svolto. */
    verdict = prove_set_tree(root);
    if (verdict.outcome == PROVED || verdict.outcome == REFUTED)
        proof_add(" The relations and maps between parts of a set are read as their rules, with the arguments in place of the "
                  "letters of each rule, and (A, B) in a relation as A and B parts of its set that satisfy the rule; the statement "
                  "decided above is the result. The statement as written and that one take the same value for each of the %lld "
                  "choices of the free sets tried in universes of one, two and three elements.", compared);
    return verdict;
}
