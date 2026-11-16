/* MODULO engine_multivariable: funzioni di più variabili: derivate parziali,
 * gradiente, hessiana, punti critici (capitoli 35-36).
 *
 * Un'unità di compilazione a sé. Dei moduli che usa vede solo le interfacce
 * incluse qui sotto; ciò che gli altri usano di lui è in
 * engine_multivariable.h, e il resto è static. */
#include "engine_multivariable.h"
#include "engine_foundations.h"
#include "parser.h"
#include "engine_evaluation.h"
#include "engine_induction.h"
#include "engine_intervals.h"
#include "engine_sign_tables.h"
#include "engine_explanation.h"
#include "engine_quantifiers_verdict.h"
#include "engine_sequences.h"
#include "engine_derivatives.h"

/* =============================================================================
 * 35. FUNZIONI DI PIÙ VARIABILI: DERIVATE PARZIALI, GRADIENTE, HESSIANA
 * ============================================================================
 *
 * A che cosa serve. "Il gradiente di x^2 y in (1, 2) è (4, 1)"; "la derivata
 * mista di e^{xy} è e^{xy} + xy e^{xy}"; "ln(x^2 + y^2) soddisfa u_xx + u_yy =
 * 0"; "calcola l'hessiana di x^3 + y^3 - 3xy". L'enunciato arriva nella
 * notazione del capitolo 34 (parser.c): funzioni dichiarate, e tesi che sono
 * uguaglianze tra espressioni in cui compaiono degli operandi, cioè derivate
 * parziali, se serve calcolate in un punto. Un gradiente o un'hessiana sono
 * già una tesi per componente.
 *
 * Qui non c'è una regola di derivazione nuova: derivare rispetto a x una
 * funzione di x e y è derivare una funzione di x in cui y è una costante, e
 * questo derive() (27c-27g) lo fa già. C'è ciò che il capitolo 27 non ha:
 * più lettere che variano insieme, e quindi un controllo indipendente che
 * non fissa le altre lettere una volta per tutte, il valore in un punto, più
 * derivate nella stessa uguaglianza, e un certificato che le porta tutte.
 *
 * IL TEOREMA
 *
 * Sia F un'espressione nelle lettere x_1, ..., x_m (variabili e parametri:
 * qui non c'è differenza), e sia U l'insieme dei punti in cui F è regolare:
 * definita, con i radicandi e gli argomenti dei valori assoluti diversi da
 * zero. U è aperto, perché ogni condizione è stretta e riguarda funzioni
 * continue, e in U la funzione F ha derivate parziali continue di ogni
 * ordine: è composta di funzioni che ne hanno. La derivata rispetto a x_i,
 * per definizione, è la derivata della funzione di una variabile che si
 * ottiene tenendo ferme le altre lettere: le regole del capitolo 27 la
 * danno in ogni punto di U. Derivando ancora, rispetto a un'altra lettera,
 * si resta in U: le derivate di ordine più alto, miste comprese, sono quelle
 * che le regole danno una dopo l'altra, nell'ordine scritto.
 *
 * COME SI DECIDE UN ENUNCIATO
 *
 *   35a. Gli operandi, nell'ordine in cui sono stati letti: la funzione, con
 *        gli operandi precedenti già al loro posto, si deriva con derive()
 *        rispetto alle lettere scritte, una dopo l'altra; il risultato si
 *        scrive in ordine (partial_tidy()), e se c'è un punto vi si mettono le
 *        coordinate al posto delle variabili.
 *   35b. Il controllo indipendente: ogni derivata delle regole si confronta
 *        con quella letta dalle serie di Taylor della funzione lungo delle
 *        rette, con gli intervalli (vedi "Le derivate miste lungo le rette",
 *        più sotto), in sei punti di prova. Una smentita è un errore di una
 *        regola; in almeno un punto le due devono coincidere.
 *   35c. Le tesi, con gli operandi al loro posto, sono uguaglianze tra
 *        espressioni senza segni di derivata. Ognuna si guarda nei punti di
 *        prova in cui sono confermati gli operandi da cui dipende. Prima con
 *        i numeri: se in un punto i due membri sono di sicuro diversi
 *        l'enunciato è FALSO, con quel punto come controesempio; devono
 *        coincidere almeno in uno. Poi con l'algebra esatta: la differenza
 *        dei due membri si riduce a zero dove sono definiti, e dove lo sono
 *        le funzioni di quegli operandi (27a, derivative_identity()).
 *   35d. La dimostrazione scritta: ogni derivata e ogni tesi scritta si
 *        rilegge dal testo e si ricalcola con i numeri (13g).
 *   35e. Il certificato: le funzioni, le lettere rispetto a cui si deriva,
 *        le derivate delle regole, i punti e le tesi, per il capitolo 18 di
 *        checker.c, che deriva da sé e rifà i conti con la sua algebra.
 *   35f. Una richiesta, senza il segno di uguale: la risposta si scrive, e
 *        l'enunciato completato dalla risposta si rilegge e si dimostra come
 *        se l'avesse scritto l'utente. Solo allora la risposta si consegna.
 *   35g. Una tesi con un confronto (<, >, \le, \ge, \neq) tra due numeri,
 *        cioè con ogni derivata calcolata in un punto: è il segno di un
 *        numero, e si decide con gli intervalli, due volte, o con l'algebra
 *        esatta se il numero è zero. Sono le condizioni del secondo ordine
 *        in un punto critico: \det H_{f}(1, 1) > 0. Vedi 35g, più sotto.
 *   35h. Una scrittura della definitezza, H_{f}(1, 1) \succ 0: il lettore
 *        l'ha già svolta nei confronti sui minori principali, che si
 *        decidono con 35g; qui c'è solo ciò che dice a chi legge che cosa
 *        abbreviava, nella dimostrazione e nella nota del verdetto.
 *
 * Il punto d'ingresso, prove_partial(), sta in fondo al capitolo 36, che
 * aggiunge la richiesta dei punti critici e usa tutto ciò che è qui.
 *
 * Un FALSO poggia, come nel capitolo 27 (27i, 27j), su due conti scritti in
 * modo diverso che in quel punto concordano: le regole e le serie di Taylor
 * per ogni derivata, e poi gli intervalli sui due membri. Un punto in cui la
 * funzione non è definita, o in cui le serie non confermano le regole, non
 * si guarda: lì l'enunciato non dice nulla, o non si sa.
 *
 * Dove vale ciò che si dimostra. Un'uguaglianza senza punti vale dove le
 * funzioni degli operandi che contiene sono regolari e i due membri definiti; il
 * controllo con i numeri assicura che un punto così esiste. Un valore in un
 * punto è affermato in quel punto: lì le serie di Taylor devono avere un
 * valore, e gli intervalli lo danno solo dove ogni divisore, ogni argomento
 * di logaritmo e ogni radicando è di sicuro dalla parte giusta. In più, lì
 * devono essere regolari le funzioni degli operandi che la funzione nomina
 * (partial_regular_at()), e ogni potenza con l'esponente non intero deve
 * avere la base positiva (partial_powers_defined()): due cose che le serie
 * da sole non vedono.
 *
 * Che cosa non c'è, e dove andrebbe: un confronto in cui restano delle
 * lettere (f_xx > 0 ovunque: una disequazione in più variabili, da
 * consegnare alla tabella dei segni come fa il capitolo 36 con il sistema
 * del gradiente), le funzioni definite per casi e la derivata in un punto
 * come limite del rapporto incrementale (capitolo 29), la regola della
 * catena con una funzione senza espressione.
 */

/* Il nome interno della lettera t che percorre una retta (35b): fuori dai
 * caratteri, dagli altri nomi interni e dai posti degli operandi
 * (VAR_OPERAND, capitolo 34). */
#define VAR_LINE 6399

/* I punti di prova. Ogni riga è un punto: la lettera di posto r, tra quelle
 * dell'enunciato in ordine alfabetico, vi prende il valore della colonna
 * r modulo 4, più 1 per ogni giro (così cinque lettere non hanno mai due
 * valori uguali). Le righe sono scelte perché le funzioni degli esercizi
 * siano definite in almeno una: tutte le lettere piccole e positive (il
 * logaritmo e la radice di 1 - x - y, di 1 - x^2 - y^2), tutte più grandi
 * di 1 (la radice di x^2 + y^2 - 1), tutte negative, e i segni misti. Con
 * un solo valore per lettera, come in sample_tree() (27h), che dà 2 a x, la
 * radice di 1 - x^2 - y^2 non è definita in nessun punto di prova. */
#define PARTIAL_POINTS 6
#define PARTIAL_COLUMNS 4
static const Frac partial_points[PARTIAL_POINTS][PARTIAL_COLUMNS] = {
    {{3, 10}, {1, 5}, {2, 7}, {1, 9}},
    {{7, 5}, {13, 10}, {9, 4}, {11, 6}},
    {{-9, 10}, {-3, 5}, {-5, 4}, {-1, 7}},
    {{13, 5}, {-11, 5}, {17, 6}, {-7, 3}},
    {{-1, 4}, {1, 3}, {-2, 9}, {2, 5}},
    {{23, 4}, {17, 5}, {31, 7}, {19, 3}},
};

/* Un operando calcolato (35a) e controllato (35b): è lo stato del motore per
 * l'operando con lo stesso numero d'ordine dell'enunciato in corso. Gli
 * alberi stanno nell'arena, e nessuno contiene il posto di un operando. */
typedef struct {
    Node *body;                    /* la funzione da derivare, con gli operandi precedenti al loro posto */
    Node *domain;                  /* body, con le coordinate al posto delle variabili se c'è un punto: definita dove l'operando esiste */
    Node *slope;                   /* la derivata data dalle regole, come funzione delle lettere, scritta in ordine */
    Node *value;                   /* ciò che l'operando vale: slope, con le coordinate al posto delle variabili se c'è un punto */
    Range taylor[PARTIAL_POINTS];  /* [p]: la derivata letta dalle serie di Taylor nel punto di prova p (partial_taylor()), o "non so" */
    unsigned agree;                /* il bit p è acceso se nel punto di prova p value coincide con taylor[p]
                                      (numbers_agree() = 1) */
    unsigned needs;                /* il bit j è acceso se l'operando dipende dall'operando j: lui stesso, quelli scritti
                                      nella sua funzione o nel suo punto, e quelli da cui dipendono loro */
} PartialValue;

static _Thread_local PartialValue partial_value[MAX_OPERANDS];
_Static_assert(MAX_OPERANDS <= 32, "PartialValue.needs ha un bit per ogni operando");

/* Le lettere dell'enunciato in corso, in ordine alfabetico: variabili e
 * parametri, senza la lettera e. Il posto di una lettera qui decide il suo
 * valore nei punti di prova. */
static _Thread_local int partial_letter[52], partial_letter_count;

/* Riempie partial_letter[] con le lettere che compaiono in st: nelle
 * funzioni, negli operandi (anche solo come lettera rispetto a cui si
 * deriva), nelle coordinate dei punti e nelle tesi. */
static void partial_letters(const PartialStatement *st) {
    partial_letter_count = 0;
    for (int letter = 'A'; letter <= 'z'; letter++) {
        if (!isalpha(letter) || letter == 'e') continue;
        int used = 0;
        for (int i = 0; i < st->functions; i++) used |= node_has_variable(st->function[i].body, letter);
        for (int i = 0; i < st->operands; i++) {
            const PartialOperand *operand = &st->operand[i];
            used |= node_has_variable(operand->body, letter);
            for (int j = 0; j < operand->order; j++) used |= operand->by[j] == letter;
            for (int j = 0; j < MAX_FUNCTION_VARIABLES; j++) used |= node_has_variable(operand->point[j], letter);
        }
        for (int i = 0; i < st->claims; i++) used |= node_has_variable(st->claim[i].lhs, letter) || node_has_variable(st->claim[i].rhs, letter);
        if (used) partial_letter[partial_letter_count++] = letter;
    }
}

/* Ritorna il valore, nel punto di prova p, della lettera di posto rank in
 * partial_letter[] (vedi partial_points[]). */
static Frac partial_coordinate(int rank, int p) {
    Frac value = partial_points[p][rank % PARTIAL_COLUMNS];
    value.num += (long long)(rank / PARTIAL_COLUMNS) * value.den;
    return value;
}

/* Ritorna una copia di tree pronta per essere calcolata con i numeri nel
 * punto di prova p: ogni lettera dell'enunciato vale il suo razionale, e i
 * sotto-alberi interi sono già calcolati (node_fold()), come dopo
 * sample_tree(). Restano la lettera e, pi greco e la lettera delle rette. */
static Node *partial_sample(const Node *tree, int p) {
    Node *copy = (Node *)tree;
    for (int i = 0; i < partial_letter_count; i++) {
        if (!node_has_variable(copy, partial_letter[i])) continue;
        Frac value = partial_coordinate(i, p);
        copy = node_replace(copy, partial_letter[i], node_new(N_DIV, node_num(value.num), node_num(value.den)));
    }
    return node_fold(copy, &(int){1});
}

/* Ritorna un intervallo che contiene il valore di tree nel punto di prova
 * p; "non so" se non si calcola o non è definito. Non lascia nulla
 * nell'arena. */
static Range partial_range(const Node *tree, int p) {
    size_t kept = arena_used;
    Range value = sample_value(partial_sample(tree, p), VAR_LINE, range_none());
    arena_used = kept;
    return value;
}

/* Ritorna tree con gli operandi di numero minore di count sostituiti dal
 * loro valore (35a). I valori non contengono posti di operandi, quindi basta
 * un passaggio. */
static Node *partial_placed(const Node *tree, int count) {
    Node *copy = (Node *)tree;
    for (int k = 0; k < count; k++)
        if (node_has_variable(copy, VAR_OPERAND + k)) copy = node_replace(copy, VAR_OPERAND + k, partial_value[k].value);
    return copy;
}

/* Ritorna l'insieme, un bit per operando, degli operandi di numero minore di
 * count da cui tree dipende: quelli di cui contiene il posto, e quelli da
 * cui dipendono loro (PartialValue.needs, già calcolato per ognuno). */
static unsigned partial_needs(const Node *tree, int count) {
    unsigned needs = 0;
    for (int k = 0; k < count; k++)
        if (node_has_variable(tree, VAR_OPERAND + k)) needs |= partial_value[k].needs;
    return needs;
}

/* Ritorna tree scritto in ordine: node_tidy() (27k-2), ripetuta finché
 * cambia qualcosa, al più quattro volte. Una volta sola non basta dopo aver
 * messo dei numeri al posto delle lettere: node_tidy() fa i conti tra interi
 * prima di togliere i fattori 1 e gli esponenti 0, e 2 + 1 \cdot e^{0}
 * restava 2 + 1. Ogni passata conserva le condizioni di esistenza. */
static Node *partial_tidy(const Node *tree) {
    Node *tidy = node_tidy(tree);
    for (int pass = 0; pass < 3; pass++) {
        Node *again = node_tidy(tidy);
        if (node_equal(again, tidy)) break;
        tidy = again;
    }
    return tidy;
}

/* Ritorna 1 se in tree è rimasto il posto di un operando. */
static int partial_pending(const Node *tree) {
    if (!tree) return 0;
    if (tree->kind == N_VAR && tree->name >= VAR_OPERAND && tree->name < VAR_OPERAND + MAX_OPERANDS) return 1;
    return partial_pending(tree->a) || partial_pending(tree->b) || partial_pending(tree->c);
}

/* LE DERIVATE MISTE LUNGO LE RETTE (35b)
 *
 * Il problema. Per controllare derive() serve la derivata parziale di F in
 * un punto P calcolata senza le sue regole. Il capitolo 27 ha le serie di
 * Taylor con gli intervalli (27h), ma di una funzione di una variabile sola:
 * bastano per una derivata come d^2 F / dx^2, non per una mista.
 *
 * L'idea. Lungo una retta per P una funzione di più variabili diventa una
 * funzione di una sola: g(t) = F(P + t u). E la sua derivata k-esima in 0 è
 * la forma che raccoglie tutte le derivate parziali di ordine k,
 *
 *     g^(k)(0) = D^k F(P)[u, ..., u],
 *
 * dove D^k F(P)[u_1, ..., u_k] è la somma, su tutte le scelte di una
 * coordinata per ogni u_j, delle derivate parziali corrispondenti per i
 * prodotti delle coordinate scelte: per k = 2 è u^T H u, con H l'hessiana.
 * È lineare in ogni argomento, e simmetrica dove le derivate di ordine k
 * sono continue (Schwarz). La derivata parziale rispetto alle lettere v_1,
 * ..., v_k è D^k F(P)[e_1, ..., e_k], con e_j il versore di v_j.
 *
 * Una forma multilineare simmetrica L si ricava dai suoi valori sulla
 * diagonale, L[u, ..., u], con la formula di polarizzazione:
 *
 *     k! L[u_1, ..., u_k] = somma su S contenuto in {1, ..., k} di
 *                           (-1)^(k - |S|) L[u_S, ..., u_S],
 *
 * dove u_S è la somma degli u_j con j in S. (Sviluppando L[u_S, ..., u_S] per
 * linearità, il termine L[u_{j_1}, ..., u_{j_k}] compare per ogni S che
 * contiene tutti i j_i; se gli indici j_i non sono tutti diversi quegli S
 * sono in numero pari, metà con un segno e metà con l'altro, e si
 * cancellano; se sono tutti diversi resta solo S = {1, ..., k}, e le k!
 * permutazioni danno lo stesso valore per simmetria.) Per k = 2:
 * 2 F_xy = (F_xx + 2 F_xy + F_yy) - F_xx - F_yy.
 *
 * Il conto. Per ogni S non vuoto si sostituisce in F ogni lettera w con
 * w + m t, dove m è quante volte w compare tra i v_j con j in S; jet_eval()
 * dà i coefficienti della serie di Taylor in t = 0 della funzione di una
 * variabile così ottenuta, e il coefficiente c_k(S) di t^k è
 * L[u_S, ..., u_S] / k!. Quindi
 *
 *     la derivata parziale = somma su S di (-1)^(k - |S|) c_k(S),
 *
 * un intervallo che contiene la derivata vera. Se una sola delle serie è
 * "non so" lo è il risultato: lì F non è regolare, o non si sa. E dove
 * jet_eval() dà un valore F è analitica intorno a P come funzione di tutte
 * le lettere, perché ogni condizione (un divisore, l'argomento di un
 * logaritmo) è controllata in t = 0, cioè in P: le derivate sono continue,
 * e la simmetria che la formula usa c'è.
 *
 * Perché è indipendente da derive(). Le serie si costruiscono dall'albero
 * della funzione, non da quello delle derivate, con le ricorrenze di 27h; e
 * una derivata mista non passa mai per una derivata prima calcolata con le
 * regole. */

/* Ritorna un intervallo che contiene, nel punto di prova p, la derivata
 * parziale dell'operando operand, la cui funzione è body: vedi sopra.
 * coordinate[] sono le coordinate del suo punto, se ne ha uno (allora f è la
 * sua funzione dichiarata); altrimenti il punto è quello di prova. */
static Range partial_taylor(const PartialOperand *operand, const DeclaredFunction *f, const Node *body, Node *const *coordinate, int p) {
    Range total = {0, 0};
    for (unsigned subset = operand->order > 0; subset < 1u << operand->order; subset++) {
        size_t kept = arena_used;
        Node *line = (Node *)body, *step = node_new(N_VAR, NULL, NULL);
        int chosen = 0;
        step->name = VAR_LINE;

        /* Ogni lettera rispetto a cui si deriva diventa w + m t. Una
         * lettera scritta più volte si tratta alla sua prima occorrenza. */
        for (int i = 0; i < operand->order; i++) {
            int times = 0, first = 1;
            for (int j = 0; j < operand->order; j++) {
                if (operand->by[j] != operand->by[i]) continue;
                if (j < i) first = 0;
                times += subset >> j & 1;
            }
            chosen += subset >> i & 1;
            if (!first || !times) continue;
            Node *letter = node_new(N_VAR, NULL, NULL);
            letter->name = operand->by[i];
            line = node_replace(line, operand->by[i], node_new(N_ADD, letter, node_new(N_MUL, node_num(times), step)));
        }

        /* Poi le variabili della funzione prendono le coordinate del punto,
         * che non le contengono: l'ordine conta, perché una coordinata può
         * contenere un parametro rispetto a cui si deriva, e quello non deve
         * muoversi con t. */
        for (int i = 0; operand->at && i < f->variables; i++) line = node_replace(line, f->variable[i], coordinate[i]);
        Jet series = jet_eval(partial_sample(line, p), VAR_LINE, range_ratio(0, 1), operand->order);
        arena_used = kept;
        total = (operand->order - chosen) % 2 ? range_sub(total, series.c[operand->order]) : range_add(total, series.c[operand->order]);
    }
    return total;
}

/* Ritorna 1 se tree, un'espressione nelle variabili di f, è regolare nel
 * punto in cui quelle variabili valgono coordinate[] e le altre lettere il
 * loro valore nel punto di prova p. Lo dicono le serie di Taylor: per ogni
 * variabile, quella di tree lungo la retta per il punto parallela al suo
 * asse deve avere un valore fino al primo ordine (jet_eval(), 27h). Dove ce
 * l'ha ogni condizione di tree (un divisore, l'argomento di un logaritmo, un
 * radicando) è dalla parte giusta nel punto, e tree è analitica lì intorno.
 * Non lascia nulla nell'arena. */
static int partial_regular_at(const Node *tree, const DeclaredFunction *f, Node *const *coordinate, int p) {
    int regular = 1;
    for (int axis = 0; axis < f->variables && regular; axis++) {
        size_t kept = arena_used;
        Node *line = (Node *)tree, *step = node_new(N_VAR, NULL, NULL);
        step->name = VAR_LINE;
        for (int i = 0; i < f->variables; i++) line = node_replace(line, f->variable[i], i == axis ? node_new(N_ADD, coordinate[i], step) : coordinate[i]);
        regular = range_known(jet_eval(partial_sample(line, p), VAR_LINE, range_ratio(0, 1), 1).c[1]);
        arena_used = kept;
    }
    return regular;
}

/* UNA POTENZA CON L'ESPONENTE NON INTERO VUOLE LA BASE POSITIVA
 *
 * a^b, con b che non è un intero, è per definizione e^{b ln a}: esiste per
 * a > 0. Nello zero, con b > 0, molti libri la prolungano con il valore 0
 * (0^{1/2} = 0), ma lì non è regolare; e il verificatore (capitolo 13 di
 * checker.c) non la considera definita. Gli intervalli del capitolo 24
 * invece la calcolano, e le serie di Taylor, quando la base non dipende
 * dalla lettera lungo cui ci si muove, la trattano da costante: da sole
 * direbbero che f(x, y) = 0^{1/2} + x è regolare in (1, 1).
 *
 * Era un certificato respinto, già prima del capitolo 36: la tesi
 * f_x(1, 1) = 1 di quella funzione risultava dimostrata dal motore, e il
 * verificatore respingeva il certificato ("in un punto la funzione non è
 * regolare"). Il verdetto era NON DIMOSTRATO, ma con un passo scartato:
 * un disaccordo tra i due. Lo stesso con un confronto, che vuole i due
 * membri definiti: (f_y(0, 1))^{1/2} \ge 0 con f_y(0, 1) = 0. Ora il motore
 * segue la convenzione del verificatore, in un punto (partial_resolve()) e
 * in un confronto (partial_compare()), e sono test.
 *
 * Ritorna 1 se in tree, nel punto di prova p, ogni potenza il cui esponente
 * non è un intero scritto ha la base di sicuro positiva, con gli intervalli;
 * 0 se una base è zero, negativa, o non si sa. */
static int partial_powers_defined(const Node *tree, int p) {
    if (!tree) return 1;
    if (tree->kind == N_POW && tree->b->kind != N_NUM && !(tree->b->kind == N_NEG && tree->b->a->kind == N_NUM)) {
        int side = 0;
        if (!range_side(partial_range(tree->a, p), &side) || side < 0) return 0;
    }
    return partial_powers_defined(tree->a, p) && partial_powers_defined(tree->b, p) && partial_powers_defined(tree->c, p);
}

/* 35a e 35b. Calcola l'operando numero k di st, che ha già calcolati i
 * precedenti, e lo controlla con le serie di Taylor: riempie
 * partial_value[k]. Ritorna NULL se riesce; altrimenti il motivo, e mette in
 * *outcome se l'enunciato è NON SUPPORTATO (qualcosa che le regole non
 * trattano) o NON DIMOSTRATO (una derivata non confermata). Una smentita,
 * che è l'errore di una regola, conta tra i passi scartati. */
static const char *partial_resolve(const PartialStatement *st, int k, Outcome *outcome) {
    const PartialOperand *operand = &st->operand[k];
    const DeclaredFunction *f = operand->function >= 0 ? &st->function[operand->function] : NULL;
    PartialValue *v = &partial_value[k];
    Node *coordinate[MAX_FUNCTION_VARIABLES];
    memset(v, 0, sizeof *v);
    *outcome = UNSUPPORTED;

    /* La funzione e le coordinate, con gli operandi precedenti al loro
     * posto. Il posto di un operando che restasse sarebbe una lettera
     * qualsiasi per derive(), cioè una costante: la derivata sarebbe
     * sbagliata senza che nulla lo segnali. Il lettore non lo permette
     * (capitolo 34), e qui lo si controlla. */
    v->body = v->domain = partial_placed(f ? f->body : operand->body, k);
    v->needs = 1u << k | partial_needs(f ? f->body : operand->body, k);
    int pending = partial_pending(v->body);
    for (int i = 0; operand->at && i < f->variables; i++) {
        coordinate[i] = partial_placed(operand->point[i], k);
        v->needs |= partial_needs(operand->point[i], k);
        pending |= partial_pending(coordinate[i]);
        for (int j = 0; j < f->variables; j++)
            if (node_has_variable(coordinate[i], f->variable[j])) return "le coordinate di un punto non possono contenere le variabili della funzione";
    }
    if (pending) return "una derivata parziale usa un operando letto dopo di lei";
    for (int i = 0; operand->at && i < f->variables; i++) v->domain = node_replace(v->domain, f->variable[i], coordinate[i]);

    /* Le regole, una lettera dopo l'altra. */
    Node *slope = v->body;
    for (int i = 0; i < operand->order && !failure; i++) {
        slope = derive(slope, operand->by[i]);
        if (!failure && node_count(slope) > MAX_DERIVATIVE_NODES) fail("la derivata calcolata con le regole è troppo lunga");
    }
    if (failure) return failure;
    v->slope = v->value = partial_tidy(slope);
    for (int i = 0; operand->at && i < f->variables; i++) v->value = node_replace(v->value, f->variable[i], coordinate[i]);
    if (operand->at) v->value = partial_tidy(v->value);

    /* 35b. Le regole contro le serie di Taylor, in ogni punto di prova. */
    *outcome = NOT_PROVED;
    for (int p = 0; p < PARTIAL_POINTS; p++) {
        v->taylor[p] = partial_taylor(operand, f, v->body, coordinate, p);
        int agreement = numbers_agree(partial_range(v->value, p), v->taylor[p]);
        if (agreement < 0) {
            unjustified_steps++;
            return "una derivata calcolata con le regole di derivazione è smentita dalle serie di Taylor della funzione";
        }

        /* In un punto l'operando esiste solo se lì sono regolari anche le
         * funzioni degli operandi che la sua funzione nomina. Le serie di
         * qui sopra non lo vedono: sono quelle della funzione con le
         * derivate degli altri già al loro posto, e la derivata 1/x di ln x
         * ha un valore anche in x = -1, dove ln x non c'è.
         *
         * Era un falso dimostrato (anche prima di questo capitolo 36): con
         * g = ln x + arcsin y e f = g_x + x + y^2, la tesi f_x(-1, 0) = 0
         * risultava DIMOSTRATO, senza certificato perché l'arcoseno non ha
         * la sua parola; in (-1, 0) la funzione f non esiste. Con un
         * certificato controllabile lo fermava il verificatore, che queste
         * condizioni le annota. Ora è un test. */
        int exists = agreement > 0;
        for (int j = 0; operand->at && j < k && exists; j++)
            if (v->needs >> j & 1) exists = partial_regular_at(partial_value[j].domain, f, coordinate, p);

        /* E nel punto ogni potenza con l'esponente non intero, della
         * funzione e della formula della derivata, deve avere la base
         * positiva: vedi partial_powers_defined(). */
        if (operand->at && exists) exists = partial_powers_defined(v->domain, p) && partial_powers_defined(v->value, p);
        if (exists) v->agree |= 1u << p;
    }
    if (failure) return failure;
    if (v->agree) return NULL;
    return operand->at ? "non riesco a confermare con i numeri una derivata nel punto scritto: lì la funzione non è definita o non è regolare, o i numeri non bastano"
                       : "non riesco a confermare con i numeri una derivata calcolata con le regole di derivazione: nei punti di prova la funzione non è definita, o i numeri non bastano";
}

/* Rilegge con il lettore del programma il testo text, in cui è stato scritto
 * l'albero tree, come in 13g: ritorna 1 se il riletto ha, con gli
 * intervalli, lo stesso valore di tree in almeno un punto di prova, e in
 * nessuno un valore di sicuro diverso. Chi scrive parte dagli alberi, chi
 * controlla dai caratteri. */
static int partial_reread(const char *text, const Node *tree) {
    size_t kept = arena_used;
    Node *reread = parse_expression(text);
    int agreed = 0, sound = !syntax_error && !failure;
    for (int p = 0; p < PARTIAL_POINTS && sound; p++) {
        int agreement = numbers_agree(partial_range(reread, p), partial_range(tree, p));
        sound = agreement >= 0;
        agreed += agreement > 0;
    }
    sound = sound && !failure && agreed > 0;
    syntax_error = failure = NULL;
    arena_used = kept;
    return sound;
}

/* Scrive nella dimostrazione l'albero tree e lo rilegge dal testo
 * (partial_reread()): ritorna 1 se il riletto è confermato. Una formula
 * troppo lunga per essere riletta non si scrive: al suo posto resta una
 * frase, e ritorna 1. */
static int partial_put_checked(const Node *tree) {
    char text[MAX_FORMULA];
    size_t from = proof_length;
    put_node(tree, 0);
    size_t length = proof_length - from;
    if (length >= sizeof text || proof_length >= PROOF_BYTES - 1) {
        proof_cut(from);
        proof_add("\\text{(an expression too long to write here)}");
        return 1;
    }
    memcpy(text, proof_text + from, length);
    text[length] = '\0';
    return partial_reread(text, tree);
}

/* Scrive nella dimostrazione l'operando numero k di st com'è scritto nei
 * libri: la frazione con \partial, la funzione dichiarata o l'espressione
 * tra parentesi, il punto. Sotto la frazione la lettera rispetto a cui si
 * deriva per ultima è scritta per prima (capitolo 34). */
static void partial_put_operand(const PartialStatement *st, int k) {
    const PartialOperand *operand = &st->operand[k];
    const DeclaredFunction *f = operand->function >= 0 ? &st->function[operand->function] : NULL;
    if (operand->order > 1) proof_add("\\frac{\\partial^{%d}", operand->order);
    else if (operand->order) proof_add("\\frac{\\partial");
    if (f) proof_add(operand->order ? " %c" : "%c", f->name);
    if (operand->order) {
        proof_add("}{");
        for (int i = operand->order - 1; i >= 0; i--) proof_add("\\partial %c%s", operand->by[i], i ? " " : "}");
    }
    if (!f) {
        proof_add("\\left( ");
        put_node(partial_value[k].body, 0);
        proof_add(" \\right)");
    }
    for (int i = 0; operand->at && i < f->variables; i++) {
        proof_add(i ? ", " : "\\left( ");
        put_node(partial_placed(operand->point[i], k), 0);
        if (i == f->variables - 1) proof_add(" \\right)");
    }
}

/* Ritorna tree con il posto di ogni operando sostituito dalla lettera che
 * gli dà il certificato, name[k] per l'operando k (35e). */
static Node *partial_named(const Node *tree, const char *name, int count) {
    Node *copy = (Node *)tree;
    for (int k = 0; k < count; k++) {
        if (!node_has_variable(copy, VAR_OPERAND + k)) continue;
        Node *letter = node_new(N_VAR, NULL, NULL);
        letter->name = name[k];
        copy = node_replace(copy, VAR_OPERAND + k, letter);
    }
    return copy;
}

/* 35e. IL CERTIFICATO
 *
 * Porta al capitolo 18 di checker.c l'enunciato com'è stato letto, più le
 * derivate che le regole hanno dato:
 *
 *     certificate partial
 *     term A
 *     of (* (^ x 2) y)
 *     by x y
 *     is (* 2 x)
 *     at x 1 y 2
 *     statement (= A 2)
 *     end
 *
 * Una voce term per operando, nello stesso ordine: il nome (una lettera
 * maiuscola che l'enunciato non usa), la funzione (of), in cui gli operandi
 * precedenti compaiono con il loro nome, le lettere rispetto a cui si
 * deriva nell'ordine in cui si deriva (by), la derivata delle regole (is),
 * e il punto, se c'è (at). Poi una voce statement per tesi, con i nomi al
 * posto degli operandi: (= L R) per un'uguaglianza, (< L R), (<= L R) e
 * (neq L R) per un confronto (35g). Il verificatore deriva la funzione da
 * sé, controlla che il risultato sia la formula di is, che nel punto la
 * funzione sia regolare e la formula definita, che i due membri di ogni
 * uguaglianza siano uguali, e di ogni confronto legge il segno della
 * differenza dal numero stesso: non usa nulla di ciò che il motore ha
 * calcolato, tranne la formula di is, che ricontrolla. Dove non sa leggere
 * il segno (la radice di 2 meno 1) il certificato non è controllabile, e il
 * verdetto è DIMOSTRATO senza certificato.
 *
 * Scrive il certificato di st in certificate_text e ritorna NULL, oppure il
 * motivo per cui il certificato non c'è. */
static const char *partial_certificate(const PartialStatement *st) {
    char name[MAX_OPERANDS];
    int next = 'A';
    certificate_length = 0;
    certificate_broken = 0;
    certificate_sequences = 0;

    /* I nomi: le maiuscole che non sono lettere dell'enunciato. */
    for (int k = 0; k < st->operands; k++) {
        for (int i = 0; i < partial_letter_count; i++)
            if (partial_letter[i] == next) { next++; i = -1; }
        if (next > 'Z') return "troppe derivate per i nomi di un certificato";
        name[k] = (char)next++;
    }

    /* La lettera e è il numero di Nepero: nessuna variabile si chiama così
     * (capitolo 34), e a cert_node() basta un nome di variabile diverso. */
    cert_real = 'x';
    cert_add("certificate partial");
    for (int k = 0; k < st->operands; k++) {
        const PartialOperand *operand = &st->operand[k];
        const DeclaredFunction *f = operand->function >= 0 ? &st->function[operand->function] : NULL;
        cert_add("\nterm %c\nof ", name[k]);
        cert_node(partial_named(f ? f->body : operand->body, name, k));
        cert_add("\nby");
        for (int i = 0; i < operand->order; i++) cert_add(" %c", operand->by[i]);
        cert_add("\nis ");
        cert_node(partial_value[k].slope);
        for (int i = 0; operand->at && i < f->variables; i++) {
            cert_add(i ? " %c " : "\nat %c ", f->variable[i]);
            cert_node(partial_named(operand->point[i], name, k));
        }
    }
    for (int c = 0; c < st->claims; c++) {
        /* Il verificatore ha le parole =, neq, < e <=: a > b si scrive
         * b < a, e a >= b si scrive b <= a. */
        static const char *const word[] = {[CLAIM_EQ] = "=", [CLAIM_NEQ] = "neq", [CLAIM_LT] = "<", [CLAIM_LE] = "<=", [CLAIM_GT] = "<", [CLAIM_GE] = "<="};
        ClaimRelation relation = st->claim[c].relation;
        int swapped = relation == CLAIM_GT || relation == CLAIM_GE;
        cert_add("\nstatement (%s ", word[relation]);
        cert_node(partial_named(swapped ? st->claim[c].rhs : st->claim[c].lhs, name, st->operands));
        cert_add(" ");
        cert_node(partial_named(swapped ? st->claim[c].lhs : st->claim[c].rhs, name, st->operands));
        cert_add(")");
    }
    cert_add("\nend\n");
    cert_real = 0;
    return certificate_broken || certificate_sequences
               ? "la notazione dei certificati delle derivate non ha arcoseno, arcocoseno e le successioni, o il testo è troppo lungo"
               : NULL;
}

/* Ritorna 1 se in tree compare una radice, un valore assoluto che non è
 * tutto l'argomento di un logaritmo, o una potenza con l'esponente che non
 * è un intero scritto e la base che non è il numero e né un numero
 * positivo scritto: nei punti in cui la
 * loro base, o il loro argomento, vale zero la funzione non è regolare, e il
 * certificato non dice nulla (capitolo 18 di checker.c). */
static int partial_irregular(const Node *tree) {
    if (!tree) return 0;
    if (tree->kind == N_CALL && (tree->op == FN_ROOT || tree->op == FN_ABS)) return 1;
    if (tree->kind == N_CALL && (tree->op == FN_LN || tree->op == FN_LOG) && tree->a->kind == N_CALL && tree->a->op == FN_ABS)
        return partial_irregular(tree->a->a) || partial_irregular(tree->b);
    int positive = (tree->kind == N_POW && tree->a->kind == N_VAR && tree->a->name == 'e') || (tree->kind == N_POW && tree->a->kind == N_NUM && tree->a->value > 0);
    if (tree->kind == N_POW && !positive && tree->b->kind != N_NUM && !(tree->b->kind == N_NEG && tree->b->a->kind == N_NUM)) return 1;
    return partial_irregular(tree->a) || partial_irregular(tree->b) || partial_irregular(tree->c);
}

/* Scrive in text, lungo size, il punto di prova p come controesempio della
 * tesi numero claim (da 1; 0 se è la sola), i cui membri, con gli operandi
 * al loro posto, sono lhs e rhs: i valori delle lettere che vi compaiono (in
 * una tesi su un punto scritto possono non essercene), e il centro degli
 * intervalli left e right in cui stanno lì i due membri. */
static void partial_counterexample(char *text, size_t size, int p, int claim, const Node *lhs, const Node *rhs, Range left, Range right) {
    size_t length = 0;
    text[0] = '\0';
    for (int i = 0; i < partial_letter_count && length < size; i++) {
        if (!node_has_variable(lhs, partial_letter[i]) && !node_has_variable(rhs, partial_letter[i])) continue;
        Frac value = partial_coordinate(i, p);
        int written = snprintf(text + length, size - length, "%s%c = %lld", length ? ", " : "", partial_letter[i], value.num);
        length += written > 0 ? (size_t)written : 0;
        if (value.den == 1 || length >= size) continue;
        written = snprintf(text + length, size - length, "/%lld", value.den);
        length += written > 0 ? (size_t)written : 0;
    }
    if (length >= size) return;
    int written = snprintf(text + length, size - length, "%s", length ? ": lì " : "");
    length += written > 0 ? (size_t)written : 0;
    if (claim && length < size) {
        written = snprintf(text + length, size - length, "nella tesi numero %d, contando una tesi per componente, ", claim);
        length += written > 0 ? (size_t)written : 0;
    }

    /* I due valori, arrotondati: servono a chi legge, non decidono nulla
     * (lo hanno già fatto gli intervalli, in numbers_agree()). */
    if (length < size)
        snprintf(text + length, size - length, "il primo membro vale circa %.10g e il secondo circa %.10g", (left.low + left.high) / 2, (right.low + right.high) / 2);
}

/* 35g. I CONFRONTI TRA NUMERI
 *
 * A che cosa serve. "In (1, 1) il determinante dell'hessiana è positivo":
 * \det H_{f}(1, 1) > 0. È la forma in cui si scrivono le condizioni del
 * secondo ordine in un punto critico, e chiede il segno di un numero: la
 * differenza dei due membri, che non contiene lettere perché ogni derivata
 * è calcolata in un punto.
 *
 * Il segno di un numero esatto si stabilisce in due modi, e servono tutti e
 * due:
 *
 *   g1. Diverso da zero: un intervallo che contiene di sicuro il numero
 *       (capitolo 24) e non contiene lo zero ne dà il segno. Un intervallo
 *       non dimostra mai che un numero è zero: per quanto stretto, attorno
 *       allo zero ne contiene altri.
 *   g2. Zero: lo dimostra solo l'algebra esatta, come per le tesi con il
 *       segno di uguale (35c).
 *
 * Il conto di g1 si fa due volte, con due valori indipendenti di ogni
 * derivata: quello delle regole (PartialValue.value) e quello letto dalle
 * serie di Taylor (PartialValue.taylor), messo nella tesi al posto
 * dell'operando da partial_number(). I due segni devono essere certi e
 * uguali. Così un errore di una regola troppo piccolo per essere visto dal
 * confronto di 35b, che tollera AGREEMENT, non può decidere un segno.
 *
 * I verdetti. Con il segno s della differenza (g1), o con s = 0 (g2), la
 * tesi è vera o falsa secondo la sua relazione: 0 < 27 è vero, e
 * \det H_{f}(P) > 0 con il determinante nullo è falso, perché i due membri
 * sono uguali. Se né g1 né g2 riescono (un numero diverso da zero ma troppo
 * vicino a zero per gli intervalli, o uno zero che l'algebra non riconosce)
 * la tesi resta non dimostrata.
 *
 * Solo tra numeri. Una tesi come f_{xx} > 0, senza punto, dice "per ogni x
 * e y": è una disequazione in più variabili (in due lettere la decide la
 * regola 18t, scritta con i quantificatori). Qui non è trattata, e il
 * verdetto lo dice.
 *
 * CHE COSA DICONO I CONFRONTI. Il motore dimostra i confronti scritti, non
 * la natura del punto: che ne segua "minimo", "massimo" o "sella" è il
 * teorema delle condizioni sufficienti del secondo ordine, che la
 * dimostrazione scritta cita con le sue ipotesi (SECOND_ORDER_REMARK).
 *
 *   Teorema. Sia f di classe C^2 in un intorno di P, con il gradiente nullo
 *   in P. Se l'hessiana H_f(P) è definita positiva, P è un punto di minimo
 *   locale stretto; se è definita negativa, di massimo locale stretto; se è
 *   indefinita, P non è né di minimo né di massimo (una sella).
 *
 *   Perché. La formula di Taylor al secondo ordine, con il gradiente nullo:
 *   f(P + h) - f(P) = (1/2) h^T H_f(P) h + o(|h|^2). Una forma quadratica
 *   definita positiva è almeno m |h|^2 con m > 0 (il suo minimo sulla sfera
 *   unitaria, che è compatta): vicino a P il resto non la supera, e la
 *   differenza è positiva. Con una forma indefinita ci sono due direzioni
 *   lungo cui la differenza ha segni opposti.
 *
 *   Criterio di Sylvester. Una matrice simmetrica è definita positiva
 *   esattamente quando i suoi minori principali di nord-ovest (i
 *   determinanti delle sottomatrici fatte dalle prime k righe e colonne)
 *   sono tutti positivi; definita negativa quando il k-esimo ha il segno di
 *   (-1)^k. Se il determinante non è zero e non vale né l'una né l'altra
 *   cosa, la matrice ha autovalori di segno diverso, ed è indefinita. Con
 *   due variabili: det > 0 e f_xx > 0 minimo; det > 0 e f_xx < 0 massimo;
 *   det < 0 sella. Con det = 0 il teorema non decide (il "caso dubbio"):
 *   x^4 + y^4, x^4 - y^4 e -x^4 - y^4 hanno nell'origine la stessa hessiana
 *   nulla, e sono un minimo, una sella e un massimo.
 *
 * L'ipotesi C^2 qui c'è sempre: un operando in un punto si calcola solo dove
 * le serie di Taylor della funzione hanno un valore (35b), cioè dove la
 * funzione è regolare, e lì ha derivate continue di ogni ordine in un
 * intorno (il teorema in testa al capitolo). */

/* La nota che segue la dimostrazione scritta quando l'enunciato scrive un
 * confronto o un determinante (partial_second_order()): vedi "Che cosa
 * dicono i confronti". Sta dopo la dimostrazione, non dentro: non è un suo
 * passo. */
static const char *const SECOND_ORDER_REMARK =
    "\n\n\\textbf{Remark.} What is proved are the equalities and the comparisons as written, nothing more. If they are the second-order conditions "
    "at a point $P$ where the gradient of a function $f$ vanishes, the theorem on sufficient conditions gives the nature of $P$. Its hypothesis is "
    "that $f$ is of class $C^{2}$ in a neighbourhood of $P$, and it holds here: a derivative at a point is computed only where the function is "
    "regular, the set of such points is open, and there the function has continuous partial derivatives of every order. Then the Hessian matrix "
    "$H_{f}(P)$ is symmetric, and $P$ is a strict local minimum if $H_{f}(P)$ is positive definite, a strict local maximum if it is negative "
    "definite, a saddle point if it is indefinite. By Sylvester's criterion a symmetric matrix is positive definite exactly when all its leading "
    "principal minors are positive, and negative definite exactly when they alternate in sign starting from a negative one; if its determinant is "
    "not zero and it is neither, it is indefinite. With two variables: $\\det H_{f}(P) > 0$ and $f_{xx}(P) > 0$ give a minimum, "
    "$\\det H_{f}(P) > 0$ and $f_{xx}(P) < 0$ a maximum, $\\det H_{f}(P) < 0$ a saddle point. If $\\det H_{f}(P) = 0$ the theorem does not decide.";

/* Ritorna 1 se l'enunciato st scrive un confronto o un determinante: allora
 * alla sua dimostrazione segue SECOND_ORDER_REMARK. */
static int partial_second_order(const PartialStatement *st) {
    int found = st->determinant;
    for (int c = 0; c < st->claims; c++) found |= st->claim[c].rhs && st->claim[c].relation != CLAIM_EQ;
    return found;
}

/* 35h. CHE COSA ABBREVIA UNA SCRITTURA DELLA DEFINITEZZA
 *
 * H_{f}(1, 1) \succ 0 arriva qui già svolta dal lettore (34s di parser.c)
 * nei confronti sui minori principali dell'hessiana, e si decide come ogni
 * altro confronto (35g): il motore non sa nulla di matrici definite. Ma chi
 * legge il verdetto ha scritto \succ, e trova dimostrati dei determinanti,
 * o smentita "la tesi numero 2": per questo la dimostrazione comincia
 * dicendo che cosa abbreviava la scrittura, e la nota del verdetto lo
 * ripete. Che quei confronti dicano "definita positiva" è il criterio di
 * Sylvester, enunciato e giustificato in 34s; il certificato è dei
 * confronti, non del criterio. */

/* I capoversi che aprono la dimostrazione scritta di un enunciato con una
 * scrittura della definitezza: uno per il segno stretto, uno per il largo,
 * e la chiusa sull'ipotesi dei due criteri (la matrice simmetrica). */
static const char *const DEFINITE_READING_STRICT =
    "The writing $H \\succ 0$, the Hessian matrix is positive definite, is short for the conditions of Sylvester's criterion, which are what is "
    "proved below: the leading principal minors of the matrix, the determinants of its first $k$ rows and columns for $k$ from $1$ to the number "
    "of variables, are all positive. $H \\prec 0$, negative definite, is short for: those minors alternate in sign, the first one being negative. ";
static const char *const DEFINITE_READING_WEAK =
    "The writing $H \\succeq 0$, the Hessian matrix is positive semidefinite, is short for the conditions that are proved below: every principal "
    "minor of the matrix, the determinant of each submatrix made of the same rows and columns, is not negative. $H \\preceq 0$, negative "
    "semidefinite, is short for: the principal minors of odd order are not positive, and those of even order are not negative. The leading minors "
    "alone would not be enough: the matrix with rows $(0, 0)$ and $(0, -1)$ has both of them equal to $0$, and is not positive semidefinite. ";
static const char *const DEFINITE_READING_SYMMETRIC =
    "These criteria hold for a symmetric matrix, and the Hessian matrix is symmetric where the function is of class $C^{2}$ (Schwarz's theorem), "
    "as it is wherever a derivative at a point is computed here.\n\n";

/* Aggiunge alla dimostrazione in corso che cosa abbreviano le scritture
 * della definitezza kinds (PartialStatement.definite, non zero). */
static void definite_put_reading(int kinds) {
    proof_add("\\textbf{Reading.} %s%s%s", kinds & DEFINITE_STRICT ? DEFINITE_READING_STRICT : "", kinds & DEFINITE_WEAK ? DEFINITE_READING_WEAK : "",
              DEFINITE_READING_SYMMETRIC);
}

/* La nota del verdetto di un enunciato con una scrittura della definitezza:
 * il pezzo per il segno stretto, quello per il largo, e la chiusa. */
#define DEFINITE_NOTE_STRICT                                                                                                             \
    "\\succ 0 e \\prec 0 abbreviano le condizioni del criterio di Sylvester sui minori principali di testa dell'hessiana, tutti positivi " \
    "per \\succ, a segni alterni dal negativo per \\prec; "
#define DEFINITE_NOTE_WEAK                                                                                                               \
    "\\succeq 0 e \\preceq 0 abbreviano le condizioni su tutti i minori principali dell'hessiana, nessuno negativo per \\succeq, quelli " \
    "di lato dispari non positivi e quelli di lato pari non negativi per \\preceq; "
#define DEFINITE_NOTE_END "le tesi sono quelle condizioni, una per minore in ordine di lato"

/* Quanto può essere lunga la nota: i tre pezzi, più quella che il verdetto
 * aveva già (la nota di 35e sui punti che il certificato non copre). */
#define DEFINITE_NOTE_BYTES (sizeof DEFINITE_NOTE_STRICT + sizeof DEFINITE_NOTE_WEAK + sizeof DEFINITE_NOTE_END + 256)

/* Scrive in note, lungo DEFINITE_NOTE_BYTES, la nota del verdetto di un
 * enunciato con le scritture della definitezza kinds: che cosa abbreviano,
 * dopo la nota before che il verdetto aveva già, se non è NULL. Ritorna
 * note. */
static const char *definite_note(int kinds, const char *before, char *note) {
    snprintf(note, DEFINITE_NOTE_BYTES, "%s%s%s%s%s", before ? before : "", before ? "; " : "", kinds & DEFINITE_STRICT ? DEFINITE_NOTE_STRICT : "",
             kinds & DEFINITE_WEAK ? DEFINITE_NOTE_WEAK : "", DEFINITE_NOTE_END);
    return note;
}

/* L'esponente intero più grande di una potenza di operandi in un confronto
 * (partial_number()). */
#define MAX_COMPARED_POWER 64

/* Ritorna 1 se in tree compare una lettera dell'enunciato in corso
 * (partial_letter[]): allora tree non è un numero. */
static int partial_has_letters(const Node *tree) {
    for (int i = 0; i < partial_letter_count; i++)
        if (node_has_variable(tree, partial_letter[i])) return 1;
    return 0;
}

/* g1, il secondo conto. Ritorna un intervallo che contiene il valore di
 * tree, un membro di una tesi tra numeri con gli operandi ancora al loro
 * posto, calcolato senza le regole di derivazione: ogni operando vale la
 * derivata letta dalle serie di Taylor nel punto di prova p, e le operazioni
 * si fanno con gli intervalli. Sa fare somme, differenze, prodotti,
 * quozienti e potenze con l'esponente intero scritto, che è ciò di cui è
 * fatto un determinante; un sotto-albero senza operandi lo calcola
 * partial_range(). Per ogni altra scrittura (la radice di una derivata)
 * ritorna "non so". */
static Range partial_number(const Node *tree, int p) {
    if (tree->kind == N_VAR && tree->name >= VAR_OPERAND && tree->name < VAR_OPERAND + MAX_OPERANDS) return partial_value[tree->name - VAR_OPERAND].taylor[p];
    if (!partial_pending(tree)) return partial_range(tree, p);
    switch (tree->kind) {
    case N_NEG: return range_neg(partial_number(tree->a, p));
    case N_ADD: return range_add(partial_number(tree->a, p), partial_number(tree->b, p));
    case N_SUB: return range_sub(partial_number(tree->a, p), partial_number(tree->b, p));
    case N_MUL: return range_mul(partial_number(tree->a, p), partial_number(tree->b, p));
    case N_DIV: return range_div(partial_number(tree->a, p), partial_number(tree->b, p));
    case N_POW: {
        /* Un esponente intero scritto, anche con il meno davanti, e non
         * enorme: range_power() fa una moltiplicazione per ogni unità. */
        const Node *exponent = tree->b->kind == N_NEG ? tree->b->a : tree->b;
        if (exponent->kind != N_NUM || exponent->value < 0 || exponent->value > MAX_COMPARED_POWER) return range_none();
        return range_power(partial_number(tree->a, p), tree->b->kind == N_NEG ? -exponent->value : exponent->value);
    }
    default:
        return range_none();
    }
}

/* Ritorna 1 se un confronto con la relazione relation è vero quando la
 * differenza tra il primo e il secondo membro ha il segno side (-1, 0, 1). */
static int claim_holds(ClaimRelation relation, int side) {
    switch (relation) {
    case CLAIM_EQ:  return side == 0;
    case CLAIM_NEQ: return side != 0;
    case CLAIM_LT:  return side < 0;
    case CLAIM_LE:  return side <= 0;
    case CLAIM_GT:  return side > 0;
    case CLAIM_GE:  return side >= 0;
    }
    return 0;
}

/* 35g. Decide la tesi numero c di st, un confronto tra numeri: left e right
 * sono i suoi membri con gli operandi al loro posto, source la somma delle
 * funzioni dei suoi operandi (i fatti del dominio per l'algebra esatta, come
 * in 35c), inside i punti di prova in cui quegli operandi sono confermati.
 * Ritorna 1 se la tesi è dimostrata, e mette in *equal se lo è perché i due
 * membri sono uguali (g2) e non per il segno della loro differenza (g1).
 * Altrimenti ritorna 0, e mette in *verdict l'esito (FALSO, NON DIMOSTRATO
 * o NON SUPPORTATO) con il motivo, oppure con il controesempio scritto in
 * text, lungo size. */
static int partial_compare(const PartialStatement *st, int c, const Node *left, const Node *right, const Node *source, unsigned inside, int *equal,
                           Verdict *verdict, char *text, size_t size) {
    int side = 0, checked = 0, p = 0;
    *equal = 0;
    verdict->outcome = UNSUPPORTED;
    if (partial_has_letters(left) || partial_has_letters(right)) {
        verdict->reason = "un confronto (<, >, \\le, \\ge, \\neq) è trattato solo tra numeri: ogni derivata va calcolata in un punto, e non devono restare lettere";
        return 0;
    }
    verdict->outcome = NOT_PROVED;
    verdict->reason = "non riesco a calcolare con i numeri i due membri di un confronto";
    if (!inside) return 0;
    while (!(inside >> p & 1)) p++;

    /* Un confronto vuole i due membri definiti, e le funzioni dei loro
     * operandi: una potenza con l'esponente non intero lo è con la base
     * positiva (partial_powers_defined()). */
    if (!partial_powers_defined(left, p) || !partial_powers_defined(right, p) || !partial_powers_defined(source, p)) {
        verdict->reason = "in un confronto una potenza con l'esponente non intero deve avere la base positiva, e qui non risulta: con la base nulla non è "
                          "regolare, e il verificatore non la considera definita";
        return 0;
    }

    /* I due membri sono numeri: un punto di prova vale l'altro. Prima con le
     * derivate delle regole, poi con quelle delle serie di Taylor. */
    Range l = partial_range(left, p), r = partial_range(right, p), gap = range_sub(l, r);
    Range again = range_sub(partial_number(st->claim[c].lhs, p), partial_number(st->claim[c].rhs, p));
    if (failure) { verdict->reason = failure; failure = NULL; return 0; }
    if (!range_known(gap)) return 0;
    if (range_side(gap, &side)) {
        /* g1. Il segno è certo: lo devono confermare le serie di Taylor. */
        if (!range_side(again, &checked)) {
            verdict->reason = "il segno della differenza dei due membri di un confronto, certo con le derivate delle regole, non è confermato con le derivate lette "
                              "dalle serie di Taylor";
            return 0;
        }
    } else {
        /* g2. Gli intervalli non la separano da zero: è zero se lo dice
         * l'algebra esatta, e allora i due valori devono coincidere. */
        atom_count = base_poly_count = atan_count = 0;
        if (numbers_agree(l, r) <= 0 || !derivative_identity(left, right, source, 0, 0, 'x')) {
            verdict->reason = "non so stabilire il segno della differenza dei due membri di un confronto: gli intervalli non la separano da zero, e l'algebra "
                              "esatta non la riduce a zero";
            failure = NULL;
            return 0;
        }
        *equal = 1;
        range_side(again, &checked);
    }

    /* Le serie di Taylor che danno di sicuro un altro segno: un errore di
     * una regola, o di questo capitolo. */
    if (checked != side) {
        unjustified_steps++;
        verdict->reason = "il segno della differenza dei due membri di un confronto è smentito dalle derivate lette dalle serie di Taylor";
        return 0;
    }
    if (claim_holds(st->claim[c].relation, side)) return 1;

    /* Falso: i due valori, per chi legge. */
    verdict->outcome = REFUTED;
    verdict->reason = NULL;
    partial_counterexample(text, size, p, st->claims > 1 ? c + 1 : 0, left, right, l, r);
    size_t length = strlen(text);
    if (*equal && length < size) snprintf(text + length, size - length, ": sono uguali, per l'algebra esatta");
    verdict->detail = text;
    return 0;
}

/* Decide l'enunciato st, in cui ogni tesi ha i due membri, come descritto
 * in testa al capitolo (da 35a a 35e, e 35g per i confronti), e ne ritorna
 * il verdetto: verdict è quello che prove_partial() ha già preparato.
 * Aggiunge la dimostrazione al testo in corso. */
static Verdict partial_decide(const PartialStatement *st, Verdict verdict) {
    static _Thread_local char text[640];
    static const char *const sign[] = {[CLAIM_EQ] = "=", [CLAIM_NEQ] = "\\neq", [CLAIM_LT] = "<", [CLAIM_LE] = "\\le", [CLAIM_GT] = ">", [CLAIM_GE] = "\\ge"};
    Node *left[MAX_PARTIAL_CLAIMS], *right[MAX_PARTIAL_CLAIMS], *source[MAX_PARTIAL_CLAIMS];
    int equal[MAX_PARTIAL_CLAIMS], irregular = 0, comparisons = 0;
    partial_letters(st);

    /* 35a, 35b. Gli operandi, nell'ordine in cui sono stati letti. */
    for (int k = 0; k < st->operands; k++) {
        const char *problem = partial_resolve(st, k, &verdict.outcome);
        if (problem) { verdict.reason = problem; failure = NULL; return verdict; }
        irregular |= partial_irregular(partial_value[k].domain);
    }

    /* 35c. Le tesi con i numeri. Ogni tesi si guarda nei punti di prova in
     * cui sono confermati gli operandi da cui dipende, e solo loro: è
     * affermata dove le sue funzioni sono regolari, non dove lo sono anche
     * quelle di un'altra tesi dello stesso enunciato. Con "f = ln x" e
     * "g = sqrt(x^2) y", la tesi g_x = y è falsa per x < 0 anche se lì f non
     * c'è. La somma delle funzioni di quegli operandi dà poi all'algebra
     * esatta i fatti del dominio (12d). */
    verdict.outcome = NOT_PROVED;
    for (int c = 0; c < st->claims; c++) {
        unsigned needs = partial_needs(st->claim[c].lhs, st->operands) | partial_needs(st->claim[c].rhs, st->operands);
        unsigned inside = (1u << PARTIAL_POINTS) - 1;
        int compared = 0;
        left[c] = partial_placed(st->claim[c].lhs, st->operands);
        right[c] = partial_placed(st->claim[c].rhs, st->operands);
        source[c] = NULL;
        for (int k = 0; k < st->operands; k++) {
            if (!(needs >> k & 1)) continue;
            inside &= partial_value[k].agree;
            source[c] = source[c] ? node_new(N_ADD, source[c], partial_value[k].domain) : partial_value[k].domain;
        }

        /* 35g. Un confronto tra numeri si decide per conto suo. */
        equal[c] = 0;
        if (st->claim[c].relation != CLAIM_EQ) {
            if (!partial_compare(st, c, left[c], right[c], source[c], inside, &equal[c], &verdict, text, sizeof text)) return verdict;
            comparisons = 1;
            continue;
        }
        for (int p = 0; p < PARTIAL_POINTS; p++) {
            if (!(inside >> p & 1)) continue;
            Range l = partial_range(left[c], p), r = partial_range(right[c], p);
            int agreement = numbers_agree(l, r);
            if (agreement < 0) {
                partial_counterexample(text, sizeof text, p, st->claims > 1 ? c + 1 : 0, left[c], right[c], l, r);
                verdict.outcome = REFUTED;
                verdict.detail = text;
                return verdict;
            }
            compared |= agreement > 0;
        }
        if (failure) { verdict.reason = failure; failure = NULL; return verdict; }
        if (!compared) {
            snprintf(text, sizeof text, "non riesco a confermare con i numeri la tesi%s, in nessuno dei punti di prova", st->claims > 1 ? " (una delle componenti)" : "");
            verdict.reason = text;
            return verdict;
        }
    }

    /* 35d. La dimostrazione scritta: le derivate, poi le tesi con le
     * derivate al loro posto, ognuna con l'algebra esatta (35c). */
    int sound = 1, x = partial_letter_count ? partial_letter[0] : 'x';
    proof_add("\\textbf{Proof.} By the rules of differentiation, with every other letter held constant:\n\\begin{itemize}\n");
    for (int k = 0; k < st->operands; k++) {
        if (!st->operand[k].order) continue;
        proof_add("\\item $");
        partial_put_operand(st, k);
        proof_add(" = ");
        sound = partial_put_checked(partial_value[k].value) && sound;
        proof_add("$;\n");
    }
    for (int c = 0; c < st->claims; c++) {
        ClaimRelation relation = st->claim[c].relation;
        atom_count = base_poly_count = atan_count = 0;
        if (relation == CLAIM_EQ && !derivative_identity(left[c], right[c], source[c], 0, 0, x)) {
            snprintf(text, sizeof text, "con le derivate calcolate con le regole, la differenza dei due membri della tesi non si riduce a zero con l'algebra esatta%s%s",
                     failure ? ": " : "", failure ? failure : "");
            failure = NULL;
            verdict.reason = text;
            return verdict;
        }
        proof_add("\\item with these derivatives the statement reads $");
        sound = partial_put_checked(left[c]) && sound;
        proof_add(" %s ", sign[relation]);
        sound = partial_put_checked(right[c]) && sound;
        if (relation == CLAIM_EQ) proof_add("$: the two sides are equal where they are defined, because their difference reduces to $0$ by exact algebra;\n");
        else if (equal[c]) proof_add("$: the two sides are numbers, and they are equal, because their difference reduces to $0$ by exact algebra;\n");
        else proof_add("$: the two sides are numbers, and the sign of their difference is certain by interval arithmetic, computed twice: with the "
                       "derivatives given by the rules, and with those read from the Taylor series;\n");
    }
    proof_add("\\item \\emph{Check with numbers}. Each derivative agrees with the one read from the Taylor series of the function along lines "
              "through sample points, computed with interval arithmetic, and the two sides of %s agree there.\n\\end{itemize}\n$\\Box$",
              comparisons ? "each equality" : "the statement");
    if (!sound) {
        unjustified_steps++;
        verdict.reason = "una formula della dimostrazione, riletta dal testo, non è confermata";
        return verdict;
    }
    if (proof_length >= PROOF_BYTES - 1) { verdict.reason = "la dimostrazione è troppo lunga per essere scritta per intero"; return verdict; }
    verdict.outcome = PROVED;
    verdict.method = "con le regole di derivazione";
    verdict.proof = proof_text;

    /* 35e. La nota sui punti che il certificato non copre la decide questo
     * capitolo, non calculus_certify(), che guarda una variabile sola e
     * prenderebbe e^{\cos y}, con x la variabile, per una potenza con
     * l'esponente non intero: per questo riceve una funzione senza radici. */
    calculus_certify(&verdict, partial_certificate(st), node_num(0), x);
    if (verdict.certificate && irregular)
        verdict.note = "il certificato non copre i punti in cui la base di una radice o di una potenza con l'esponente non intero, o l'argomento di un valore assoluto, vale zero";
    return verdict;
}

/* 35f. Scrive in completed, lungo size, l'enunciato formula, che è la
 * richiesta st, completato dalla risposta: " = " e le componenti chieste,
 * ognuna con gli operandi al loro posto e scritta in ordine (partial_tidy()),
 * nella forma che la richiesta vuole (un'espressione, una lista, una
 * matrice). Mette in *answer l'inizio della risposta dentro completed.
 * Ritorna NULL, oppure il motivo, con *outcome come per partial_resolve(). */
static const char *partial_answer(const char *formula, const PartialStatement *st, char *completed, size_t size, const char **answer, Outcome *outcome) {
    partial_letters(st);
    for (int k = 0; k < st->operands; k++) {
        const char *problem = partial_resolve(st, k, outcome);
        if (problem) return problem;
    }

    /* La risposta si scrive nel testo della dimostrazione, che poi torna
     * com'era: put_node() scrive lì. */
    size_t from = proof_length;
    const char *between = st->request == ASKED_HESSIAN ? " & " : ", ";
    if (st->request != ASKED_VALUE) proof_add(st->request == ASKED_HESSIAN ? "\\begin{pmatrix} " : "\\left( ");
    for (int c = 0; c < st->claims; c++) {
        if (c) proof_add("%s", c % st->columns ? between : " \\\\ ");
        put_node(partial_tidy(partial_placed(st->claim[c].lhs, st->operands)), 0);
    }
    if (st->request != ASKED_VALUE) proof_add(st->request == ASKED_HESSIAN ? " \\end{pmatrix}" : " \\right)");
    int broken = failure || proof_length >= PROOF_BYTES - 1;
    int length = broken ? -1 : snprintf(completed, size, "%s = %s", formula, proof_text + from);
    proof_cut(from);
    *outcome = NOT_PROVED;
    if (failure) return failure;
    if (length < 0 || (size_t)length >= size) return "la risposta è troppo lunga per essere scritta e riletta";
    *answer = completed + strlen(formula) + 3;
    return NULL;
}

/* =============================================================================
 * 36. PUNTI CRITICI, E L'INGRESSO DELLE FUNZIONI DI PIÙ VARIABILI
 * ============================================================================
 *
 * A che cosa serve. "Trovare i punti critici di f(x, y) = x^3 + y^3 - 3xy, e
 * dirne la natura": è l'esercizio più frequente sulle funzioni di due
 * variabili. La richiesta si scrive
 *
 *     f(x, y) = x^{3} + y^{3} - 3xy \implies \{(x, y) \mid \nabla f(x, y) = (0, 0)\}
 *
 * e la risposta è RISOLTO, con la condizione che dice dove il gradiente è
 * nullo: (y = 0 \land x = 0) \lor (y = 1 \land x = 1). Un punto critico è un
 * punto in cui la funzione è regolare e il gradiente è nullo.
 *
 * Qui non c'è un metodo nuovo. Il gradiente lo calcola il capitolo 35; il
 * sistema "gradiente = 0", in due lettere reali, è un enunciato del capitolo
 * 18, e lo risolve la tabella dei segni con un parametro (18t): una lettera
 * fa da parametro, l'altra da variabile. Ciò che questo capitolo aggiunge è
 * il passaggio dall'uno all'altro, e il ricontrollo di ciò che si consegna.
 *
 *   36a. Il gradiente: gli operandi del capitolo 35 (35a), confermati dalle
 *        serie di Taylor (35b), scritti in LaTeX.
 *   36b. Il sistema. Si scrive la richiesta "per ogni y, gli x in cui le due
 *        componenti valgono zero", come la scriverebbe un utente, e la si
 *        fa risolvere a prove_quantified(). Se non riesce con y come
 *        parametro si prova con x: la regola 18t vuole grado al più 4 nella
 *        variabile, e valori critici del parametro razionali o con una
 *        radice quadrata, e una funzione può stare nei limiti per una
 *        lettera e non per l'altra. Un confronto conta come falso dove un
 *        suo membro non ha valore (18p): un punto in cui il gradiente non è
 *        definito non è una soluzione. Al sistema si aggiunge, per ogni
 *        logaritmo della funzione, che il suo argomento sia positivo
 *        (critical_domain()): il gradiente da solo non lo dice.
 *   36c. Che non ce ne siano altri. La risposta si rilegge dentro
 *        l'enunciato "per ogni y, per ogni x: il gradiente è nullo se e solo
 *        se vale la risposta", che viene dimostrato da capo, come se lo
 *        avesse scritto l'utente. È la completezza dell'elenco: la dimostra
 *        la regola 18t, che ricontrolla la sua proiezione con un altro conto
 *        (18t-h) ma non ha certificato, e il verdetto lo dice.
 *   36d. I punti, uno per uno. Se la risposta è un elenco finito di punti
 *        (critical_list()), ognuno diventa un enunciato del capitolo 35:
 *        il gradiente vi è nullo, e in più i confronti del secondo ordine
 *        (35g), cioè il segno del determinante dell'hessiana e, se è
 *        positivo, quello di f_xx. Quali confronti scrivere lo dice un conto
 *        con gli intervalli (critical_sign()), che è solo una ricerca:
 *        l'enunciato scritto lo dimostra partial_decide(), con il suo
 *        certificato. Un punto che lì non risulta critico (la funzione non
 *        vi è regolare, o i due capitoli non sono d'accordo) ferma la
 *        risposta.
 *
 * Che cosa dice il verdetto. RISOLTO con la condizione; senza certificato,
 * perché la completezza non ne ha, e il motivo dice che i punti, uno per
 * uno, ce l'hanno. La nota riporta i confronti del secondo ordine dimostrati
 * in ogni punto, senza parole: che cosa se ne conclude lo dice il teorema
 * citato nella dimostrazione (35g). Il determinante nullo resta scritto come
 * tale: è il caso in cui il teorema non decide.
 *
 * Dove la funzione non è regolare. Un punto in cui si annulla l'argomento di
 * un valore assoluto, o il radicando di una radice, non è un punto critico:
 * lì il gradiente delle regole non esiste, e la funzione può avere lo stesso
 * un minimo (|y| in y = 0). Quei punti qui non si guardano, e la nota del
 * verdetto lo dice, perché "nessun punto critico" non venga letto come
 * "nessun estremo".
 *
 * Che cosa non c'è. Più di due variabili, o un parametro nella funzione (la
 * regola 18t tratta due lettere); le funzioni il cui gradiente non è una
 * frazione di polinomi (un esponenziale che non si annulla mai andrebbe
 * tolto dal sistema prima di risolverlo: è un passo in più, qui in 36b); le
 * funzioni definite con una derivata di un'altra funzione dichiarata, di cui
 * il sistema non direbbe dove esistono; i punti critici che stanno su una
 * curva, che si consegnano come condizione ma non si ridimostrano uno per
 * uno. In ognuno di questi casi il verdetto dice che cosa manca.
 */

#define MAX_CRITICAL_POINTS 16  /* punti critici ridimostrati uno per uno */
#define CRITICAL_TEXT 65536     /* una dimostrazione riportata dentro quella dei punti critici */
#define CRITICAL_COORDINATE 128 /* una coordinata di un punto critico, scritta in LaTeX */

/* Scrive in text, lungo size, l'albero tree in LaTeX, passando dal testo
 * della dimostrazione, che torna com'era, e lo rilegge (partial_reread()):
 * ciò che questo capitolo consegna ad altri lettori, il gradiente e le
 * coordinate dei punti, deve dire ciò che dicono gli alberi. Ritorna 1 se il
 * testo ci sta e il riletto è confermato; un riletto non confermato è un
 * passo scartato. */
static int critical_text(const Node *tree, char *text, size_t size) {
    size_t from = proof_length;
    put_node(tree, 0);
    size_t length = proof_length - from;
    int fits = !failure && !proof_broken && length < size;
    if (fits) {
        memcpy(text, proof_text + from, length);
        text[length] = '\0';
    }
    proof_cut(from);
    if (!fits) return 0;
    if (partial_reread(text, tree)) return 1;
    unjustified_steps++;
    return 0;
}

/* Un valore dato a una o a tutte e due le incognite: un pezzo della
 * condizione che dice dove il gradiente è nullo. at[i] è NULL se la
 * condizione non dice nulla dell'incognita i. */
typedef struct {
    const Node *at[2];
} CriticalValues;

/* 36d. Legge la condizione w, scritta da 18t-e, come un elenco di punti: le
 * assegnazioni di un numero a un'incognita (letter[0], letter[1]), unite da
 * "e" e da "o". Mette in out[], che ha room posti, un elemento per ogni
 * alternativa, e ne ritorna il numero; ritorna -1 se w non è fatta così (un
 * confronto che non è un'uguaglianza tra un'incognita e un numero), o se i
 * posti non bastano.
 *
 * "A e B" dà ogni alternativa di A unita a ogni alternativa di B: è la
 * proprietà distributiva, (a_1 o a_2) e b = (a_1 e b) o (a_2 e b). Due
 * valori per la stessa incognita nella stessa alternativa non sono un punto:
 * 18t-e non li scrive, e qui si rinuncia. */
static int critical_list(const Formula *w, const int *letter, CriticalValues *out, int room) {
    if (w->kind == F_EQUAL) {
        for (int i = 0; i < 2 && room > 0; i++) {
            const Node *unknown = w->left->kind == N_VAR && w->left->name == letter[i] ? w->left : w->right, *value = unknown == w->left ? w->right : w->left;
            if (unknown->kind != N_VAR || unknown->name != letter[i] || node_has_variable(value, letter[0]) || node_has_variable(value, letter[1])) continue;
            out[0] = (CriticalValues){{NULL, NULL}};
            out[0].at[i] = value;
            return 1;
        }
        return -1;
    }
    if (w->kind == F_OR) {
        int first = critical_list(w->a, letter, out, room);
        int second = first < 0 ? -1 : critical_list(w->b, letter, out + first, room - first);
        return second < 0 ? -1 : first + second;
    }
    if (w->kind != F_AND) return -1;

    /* "E": le alternative dei due lati, a coppie. */
    CriticalValues left[MAX_CRITICAL_POINTS], right[MAX_CRITICAL_POINTS];
    int lefts = critical_list(w->a, letter, left, MAX_CRITICAL_POINTS), rights = critical_list(w->b, letter, right, MAX_CRITICAL_POINTS);
    if (lefts < 0 || rights < 0 || lefts * rights > room) return -1;
    for (int i = 0; i < lefts; i++)
        for (int j = 0; j < rights; j++) {
            CriticalValues *both = &out[i * rights + j];
            for (int k = 0; k < 2; k++) {
                if (left[i].at[k] && right[j].at[k]) return -1;
                both->at[k] = left[i].at[k] ? left[i].at[k] : right[j].at[k];
            }
        }
    return lefts * rights;
}

/* 36b. DOVE LA FUNZIONE C'È
 *
 * Un punto critico è un punto in cui la funzione è regolare e il gradiente è
 * nullo. Il sistema "gradiente = 0" trova i punti in cui la formula del
 * gradiente ha un valore, e vale zero: bastano, se quella formula ha un
 * valore solo dove la funzione è regolare. Per quasi tutto ciò di cui è
 * fatta una funzione è così, perché la derivata se lo porta dentro: quella
 * di un quoziente ha lo stesso divisore, quella di una radice ha la radice
 * al denominatore, quella di |u| ha |u| o u al denominatore, quella di una
 * potenza con l'esponente non intero contiene una potenza della stessa base
 * con un esponente non intero. (derive() e node_tidy() non tolgono mai un
 * divisore: 27k-2.)
 *
 * Il logaritmo no. La derivata di ln u è u' / u, che ha un valore anche dove
 * u è negativo e il logaritmo non c'è: ln x + x^2 / 2 + 2x ha la derivata
 * 1 / x + x + 2, che vale zero in x = -1, fuori dal dominio. Senza altro il
 * sistema consegnava la retta x = -1 come insieme dei punti critici di una
 * funzione che lì non esiste: un RISOLTO falso, trovato provando funzioni
 * con il logaritmo, e ora un test. Per questo al sistema si aggiunge "u > 0"
 * per ogni logaritmo ln u (o log_b u) della funzione. Il logaritmo di un
 * valore assoluto, ln |v|, è regolare proprio dove lo è la sua derivata,
 * v' / v, cioè per v diverso da zero: non serve nulla. Tutto questo vale
 * per il gradiente di una funzione scritta per intero; di una funzione
 * definita con una derivata di un'altra prove_critical() non cerca i punti
 * critici.
 *
 * Aggiunge a text, lungo size, " \land u > 0" per ogni logaritmo di tree il
 * cui argomento u non è un valore assoluto, una volta sola per argomento. Un
 * argomento che non si lascia scrivere e rileggere annota un errore
 * (failure). */
static void critical_domain(const Node *tree, char *text, size_t size) {
    static _Thread_local char argument[MAX_FORMULA], condition[MAX_FORMULA + 16];
    if (!tree || failure) return;
    if (tree->kind == N_CALL && (tree->op == FN_LN || tree->op == FN_LOG) && !(tree->a->kind == N_CALL && tree->a->op == FN_ABS)) {
        if (!critical_text(tree->a, argument, sizeof argument)) { fail("l'argomento di un logaritmo è troppo lungo per scriverne la condizione"); return; }
        snprintf(condition, sizeof condition, " \\land %s > 0", argument);
        if (!strstr(text, condition)) text_add(text, size, "%s", condition);
    }
    critical_domain(tree->a, text, size);
    critical_domain(tree->b, text, size);
    critical_domain(tree->c, text, size);
}

/* 36d, la ricerca. Ritorna il segno (1 o -1) del numero scritto da
 * expression, un'espressione di derivate calcolate in un punto, dopo le
 * definizioni prefix: 0 se gli intervalli non lo separano da zero, 2 se non
 * si calcola. Serve solo a scegliere quale confronto scrivere: che il
 * confronto valga lo dimostra poi partial_decide(). Svuota l'arena. */
static int critical_sign(const char *prefix, const char *expression) {
    static _Thread_local PartialStatement probe;
    static _Thread_local char text[2 * MAX_FORMULA];
    Outcome outcome;
    int side = 0, known = snprintf(text, sizeof text, "%s%s", prefix, expression) < (int)sizeof text;
    arena_used = arena_keep;
    atom_count = base_poly_count = atan_count = 0;
    failure = NULL;
    known = known && parse_partial_statement(text, &probe) && !failure && probe.request == ASKED_VALUE;
    if (known) partial_letters(&probe);
    for (int k = 0; known && k < probe.operands; k++) known = !partial_resolve(&probe, k, &outcome);
    Range value = known ? partial_range(partial_placed(probe.claim[0].lhs, probe.operands), 0) : range_none();
    syntax_error = failure = NULL;
    if (!range_known(value)) return 2;
    return range_side(value, &side) ? side : 0;
}

/* 36d. Decide l'enunciato del capitolo 35 scritto in text, come farebbe
 * prove_partial() con un enunciato dell'utente, e ne ritorna il verdetto; la
 * dimostrazione si aggiunge al testo in corso. Svuota l'arena. */
static Verdict critical_decide(const char *text) {
    static _Thread_local PartialStatement st;
    Verdict verdict = {NOT_PROVED, 0, 0, 0, "un enunciato scritto dal programma non si rilegge", NULL, NULL, NULL, NULL, NULL};
    arena_used = arena_keep;
    atom_count = base_poly_count = atan_count = 0;
    failure = NULL;
    if (!parse_partial_statement(text, &st) || failure || st.request) { syntax_error = failure = NULL; return verdict; }
    return partial_decide(&st, verdict);
}

/* Risponde alla richiesta dei punti critici st, letta dall'enunciato
 * formula: vedi la testa del capitolo, da 36a a 36d. Il verdetto è RISOLTO,
 * con la condizione che dice dove il gradiente è nullo; oppure dice che cosa
 * non è riuscito. Svuota l'arena più volte: al ritorno gli alberi di st non
 * valgono più. */
static Verdict prove_critical(const char *formula, const PartialStatement *st) {
    static const char *const comparison[] = {"<", "=", ">"};
    static _Thread_local char gradient[2][MAX_FORMULA], conditions[2 * MAX_FORMULA], prefix[MAX_FORMULA], system[2 * MAX_FORMULA], complete[4 * MAX_FORMULA];
    static _Thread_local char answer[2 * MAX_FORMULA], statement[2 * MAX_FORMULA];
    static _Thread_local char solving[CRITICAL_TEXT], pieces[4 * CRITICAL_TEXT], problem[1024], first[512], note[2048], missing[512];
    static _Thread_local char at[MAX_CRITICAL_POINTS][2][CRITICAL_COORDINATE];
    const DeclaredFunction *f = &st->function[st->critical];
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, NULL, NULL, NULL};
    int letter[2] = {f->variable[0], f->variable[1]}, name = f->name;

    /* Due variabili, e nessun'altra lettera: sono le due lettere di 18t. */
    if (f->variables != 2) {
        verdict.reason = "i punti critici sono trovati solo per le funzioni di due variabili: il sistema lo risolve la tabella dei segni con un parametro, "
                         "che tratta due lettere";
        return verdict;
    }
    partial_letters(st);
    for (int i = 0; i < partial_letter_count; i++)
        if (partial_letter[i] != letter[0] && partial_letter[i] != letter[1]) {
            verdict.reason = "i punti critici sono trovati solo senza parametri: il sistema lo risolve la tabella dei segni con un parametro, che tratta due lettere";
            return verdict;
        }

    /* 36a. Il gradiente, e ciò che nell'enunciato precede la richiesta. */
    for (int k = 0; k < st->operands; k++) {
        const char *why = partial_resolve(st, k, &verdict.outcome);
        if (why) { verdict.reason = why; failure = NULL; return verdict; }
    }
    int irregular = partial_irregular(partial_placed(f->body, st->operands));

    /* Una funzione definita con una derivata di un'altra (f = g_x + ...):
     * della funzione g nel sistema resterebbe solo quella derivata, che può
     * avere un valore dove g non c'è, e non solo per un logaritmo (di
     * g = ln x + 1/y resta 1/x, senza traccia di y). Dove f esiste qui non
     * si saprebbe dire: non si risponde. Una funzione usata per intero,
     * g(x, y), porta invece nel sistema tutta la sua espressione. */
    unsigned needs = partial_needs(st->claim[0].lhs, st->operands) | partial_needs(st->claim[1].lhs, st->operands);
    for (int k = 0; k < st->operands; k++)
        if ((needs >> k & 1) && st->operand[k].order > 0 && k != st->claim[0].lhs->name - VAR_OPERAND && k != st->claim[1].lhs->name - VAR_OPERAND) {
            verdict.outcome = UNSUPPORTED;
            verdict.reason = "i punti critici non sono cercati per una funzione definita con una derivata di un'altra funzione dichiarata: dove quella derivata "
                             "esiste il sistema non lo direbbe";
            return verdict;
        }
    verdict.outcome = UNSUPPORTED;
    verdict.reason = "il sistema che annulla il gradiente è troppo lungo per essere scritto, o il gradiente riletto non è confermato";
    for (int c = 0; c < 2; c++)
        if (!critical_text(partial_placed(st->claim[c].lhs, st->operands), gradient[c], sizeof gradient[c])) { failure = NULL; return verdict; }
    if (snprintf(prefix, sizeof prefix, "%.*s", (int)(st->asked_from - formula), formula) >= (int)sizeof prefix) return verdict;

    /* 36b. Le condizioni del sistema: le due componenti nulle, e i logaritmi
     * della funzione definiti. */
    conditions[0] = '\0';
    text_add(conditions, sizeof conditions, "%s = 0 \\land %s = 0", gradient[0], gradient[1]);
    critical_domain(partial_placed(f->body, st->operands), conditions, sizeof conditions);
    if (failure) { verdict.reason = failure; failure = NULL; return verdict; }

    /* Il sistema, con l'una o con l'altra lettera per parametro. Da qui in
     * poi st non si usa più: prove_quantified() svuota l'arena. */
    Verdict solved = verdict;
    int parameter = 0;
    for (int attempt = 0; attempt < 2 && solved.outcome != SOLVED; attempt++) {
        parameter = letter[1 - attempt];
        if (snprintf(system, sizeof system, "\\forall %c \\in \\mathbb{R}\\ \\{%c \\in \\mathbb{R} \\mid %s\\}", parameter, letter[attempt], conditions) >= MAX_FORMULA)
            return verdict;
        solved = prove_quantified(system);
        if (attempt == 0) snprintf(first, sizeof first, "%s", solved.reason ? solved.reason : "la richiesta non ha avuto risposta");
    }
    explanation.steps = 0;
    verdict.reason = NULL;
    if (solved.outcome != SOLVED) {
        snprintf(problem, sizeof problem, "il gradiente è calcolato, ma il sistema che lo annulla non è risolto dalla tabella dei segni con un parametro: %s", first);
        verdict.outcome = solved.outcome == UNSUPPORTED ? UNSUPPORTED : NOT_PROVED;
        verdict.reason = problem;
        return verdict;
    }
    int variable = parameter == letter[0] ? letter[1] : letter[0];
    snprintf(answer, sizeof answer, "%s", solved.detail);
    if (!solved.proof || snprintf(solving, sizeof solving, "%s", solved.proof) >= (int)sizeof solving)
        snprintf(solving, sizeof solving, "The cases are too long to be written here.");

    /* Le due risposte che non sono una condizione da rileggere (18t-e):
     * nessun punto, e tutti. */
    char nowhere[64], everywhere[64];
    snprintf(nowhere, sizeof nowhere, "\\nexists %c \\in \\mathbb{R}", variable);
    snprintf(everywhere, sizeof everywhere, "\\forall %c \\in \\mathbb{R}", variable);
    int none = strcmp(answer, nowhere) == 0, all = strcmp(answer, everywhere) == 0;

    /* 36c. La completezza: l'enunciato con la risposta dentro, da capo.
     * "Nessun punto" e "tutti" si dicono negando o affermando il sistema. */
    verdict.outcome = NOT_PROVED;
    complete[0] = '\0';
    text_add(complete, sizeof complete, "\\forall %c \\in \\mathbb{R}\\ \\forall %c \\in \\mathbb{R}\\ ", parameter, variable);
    if (none || all) text_add(complete, sizeof complete, "%s\\left( %s \\right)", none ? "\\lnot " : "", conditions);
    else text_add(complete, sizeof complete, "\\left( (%s) \\iff (%s) \\right)", conditions, answer);
    int fits = !failure && strlen(complete) < MAX_FORMULA;
    failure = NULL;
    Verdict again = verdict;
    if (fits) again = prove_quantified(complete);
    explanation.steps = 0;

    /* Dimostrato: la completezza è un enunciato dimostrato da capo. Non
     * letto (un punto con una radice tra le coordinate: 18t la scrive, ma
     * dentro un enunciato da verificare non la tratta): la completezza resta
     * quella che 18t ha controllato risolvendo, rileggendo la risposta in
     * ogni cella (18t-f), e la soluzione lo dice. Ogni altro esito ferma la
     * risposta: smentito, è un errore del programma. */
    int reproved = again.outcome == PROVED;
    if (!reproved && (again.outcome != UNSUPPORTED || !fits)) {
        if (again.outcome == REFUTED) unjustified_steps++;
        snprintf(problem, sizeof problem, "i punti critici trovati, riletti come enunciato, non sono confermati%s%s", again.reason ? ": " : "",
                 again.reason ? again.reason : fits ? "" : ": l'enunciato è troppo lungo");
        verdict.reason = problem;
        return verdict;
    }

    /* 36d. L'elenco dei punti, se la risposta lo è: le coordinate, come
     * testo, nell'ordine delle variabili. */
    CriticalValues listed[MAX_CRITICAL_POINTS];
    arena_used = arena_keep;
    failure = NULL;
    proof_reset();
    const Formula *written = none || all ? NULL : condition_reread(answer);
    int points = none ? 0 : written ? critical_list(written, letter, listed, MAX_CRITICAL_POINTS) : -1;
    for (int i = 0; i < points; i++)
        for (int k = 0; k < 2; k++)
            if (!listed[i].at[k] || !critical_text(listed[i].at[k], at[i][k], sizeof at[i][k])) { points = -1; break; }
    failure = NULL;

    /* Ogni punto, come enunciato del capitolo 35: il gradiente nullo e i
     * confronti del secondo ordine che gli intervalli suggeriscono. Se con i
     * confronti non riesce, resta il gradiente nullo. */
    int certified = 0, compared = 0;
    pieces[0] = note[0] = '\0';
    for (int i = 0; i < points; i++) {
        /* I segni che gli intervalli suggeriscono: del determinante
         * dell'hessiana (2 se non si calcola) e, se è positivo, di f_xx (0
         * se non si sa). */
        char place[2 * CRITICAL_COORDINATE + 8], hessian[sizeof place + 16], pure[sizeof place + 16];
        snprintf(place, sizeof place, "(%s, %s)", at[i][0], at[i][1]);
        snprintf(hessian, sizeof hessian, "\\det H_{%c}%s", name, place);
        snprintf(pure, sizeof pure, "%c_{%c%c}%s", name, letter[0], letter[0], place);
        int determinant = critical_sign(prefix, hessian), second = determinant == 1 ? critical_sign(prefix, pure) : 0;
        if (second == 2) second = 0;
        Verdict decided = verdict;
        for (int plain = determinant == 2; plain < 2 && decided.outcome != PROVED; plain++) {
            if (plain) determinant = 2;
            statement[0] = '\0';
            text_add(statement, sizeof statement, "%s\\nabla %c%s = (0, 0)", prefix, name, place);
            if (!plain) text_add(statement, sizeof statement, " \\land %s %s 0", hessian, comparison[determinant + 1]);
            if (!plain && second) text_add(statement, sizeof statement, " \\land %s %s 0", pure, comparison[second + 1]);
            if (failure) break;
            size_t from = proof_length;
            proof_add("\\item $%s$. ", statement + strlen(prefix));
            decided = critical_decide(statement);
            if (decided.outcome == PROVED) text_add(pieces, sizeof pieces, "%s\n", proof_text + from);
            proof_cut(from);
        }
        if (failure) { failure = NULL; verdict.reason = "la soluzione è troppo lunga per essere scritta per intero"; return verdict; }
        if (decided.outcome != PROVED) {
            if (decided.outcome == REFUTED) unjustified_steps++;
            snprintf(problem, sizeof problem, "il punto %s, trovato dalla tabella dei segni, riletto come enunciato sulle derivate non risulta critico%s%s", place,
                     decided.reason ? ": " : "", decided.reason ? decided.reason : "");
            verdict.reason = problem;
            return verdict;
        }
        certified += decided.certificate != NULL;

        /* La nota del verdetto: i confronti dimostrati, senza parole. */
        if (determinant == 2) continue;
        compared = 1;
        text_add(note, sizeof note, "%s%s: \\det H_{%c} %s 0", note[0] ? "; " : "condizioni del secondo ordine dimostrate, in ", place, name, comparison[determinant + 1]);
        if (second) text_add(note, sizeof note, " \\land %c_{%c%c} %s 0", name, letter[0], letter[0], comparison[second + 1]);
        if (failure) { failure = NULL; verdict.reason = "i punti critici sono troppi per scriverne la nota"; return verdict; }
    }

    /* La soluzione scritta: la risposta, come è stata trovata, e i punti. */
    proof_reset();
    proof_add("\\textbf{Solution.} The gradient is $\\nabla %c = \\left( %s, %s \\right)$. ", name, gradient[0], gradient[1]);
    if (none) proof_add("It vanishes at no point: there are no critical points.");
    else if (all) proof_add("It vanishes at every point.");
    else proof_add("Where the function is regular, it vanishes exactly for $%s$.", answer);
    if (irregular)
        proof_add(" The points where the function is not regular (the base of a root, or the argument of an absolute value, vanishes there) are not "
                  "critical points, and are not examined here: the function may still have an extremum at one of them.");
    proof_add("\n\n\\textbf{The system.} The critical points are the solutions of $%s$%s. %s", system,
              strstr(conditions, " > 0") ? " (the gradient vanishes, and each logarithm of the function has a positive argument)" : "", solving);
    if (reproved)
        proof_add("\n\n\\textbf{No other points.} Read again inside a statement, the answer says $%s$, which is proved from scratch by the same method, "
                  "cases on $%c$ and a sign table in $%c$ for each case. This part has no certificate.", complete, parameter, variable);
    else
        proof_add("\n\n\\textbf{No other points.} The answer was read again while solving: at the value of each case, and at two more values of each "
                  "interval, a sign table proves that the system and the answer have the same solutions in $%c$. The statement $%s$ as a whole could "
                  "not be proved from scratch: the method does not read it. This part has no certificate.", variable, complete);
    if (points > 0)
        proof_add("\n\n\\textbf{The points, one by one.} Each point is a statement of its own: the gradient vanishes there, and the determinant of the Hessian "
                  "matrix, and $%c_{%c%c}$ when that determinant is positive, has the sign written.\n\\begin{itemize}\n%s\\end{itemize}", name, letter[0],
                  letter[0], pieces);
    if (compared) proof_add("%s", SECOND_ORDER_REMARK);
    if (proof_broken) { verdict.reason = "la soluzione è troppo lunga per essere scritta per intero"; return verdict; }

    /* Il verdetto. La completezza non ha certificato: lo dice il motivo, e
     * dice se è stata ridimostrata da capo (36c) o solo riletta da 18t-f.
     * Nel motivo non ci sono due punti: in una riga RISOLTO dopo il primo
     * ": " viene la risposta, e gli script di tools/fuzz/ la cercano lì. */
    snprintf(missing, sizeof missing, "che non ci siano altri punti critici lo dimostra la tabella dei segni con un parametro, che non ha certificato%s",
             reproved ? "" : ", e solo risolvendo, perché l'enunciato con la risposta dentro non si è potuto ridimostrare da capo");
    if (points == 1) text_add(missing, sizeof missing, "; il punto trovato, riletto come enunciato, %s il certificato verificato", certified ? "ha" : "non ha");
    if (points > 1) text_add(missing, sizeof missing, "; dei %d punti trovati, riletti uno per uno come enunciati, %d hanno il certificato verificato", points, certified);
    failure = NULL;
    verdict.outcome = SOLVED;
    verdict.reason = missing;
    verdict.detail = none ? "\\emptyset" : all ? "\\mathbb{R}^{2}" : answer;
    verdict.method = "con le regole di derivazione e la tabella dei segni, per casi sul parametro";
    if (points < 0 && !all) text_add(note, sizeof note, "i punti critici non sono un elenco finito di punti, o sono troppi: non sono stati riletti uno per uno");
    if (irregular)
        text_add(note, sizeof note, "%si punti in cui la funzione non è regolare, dove si annulla la base di una radice o l'argomento di un valore assoluto, non "
                 "sono punti critici e non sono stati guardati", note[0] ? "; " : "");
    failure = NULL;
    verdict.note = note[0] ? note : NULL;
    verdict.proof = proof_text;
    return verdict;
}

/* Dimostra, smentisce o risolve l'enunciato sulle funzioni di più variabili
 * scritto in formula, come descritto in testa al capitolo 35 e, per i punti
 * critici, a questo. Il verdetto DIMOSTRATO, o RISOLTO per una richiesta,
 * porta il certificato di 35e se il verificatore lo accetta; altrimenti dice
 * perché manca, e se il verificatore lo respinge il verdetto è NON
 * DIMOSTRATO. Il RISOLTO dei punti critici non porta mai certificato: la
 * completezza dell'elenco non ne ha (36c). Svuota l'arena e la tabella degli
 * atomi: i risultati di chiamate precedenti non sono più validi. */
Verdict prove_partial(const char *formula) {
    static _Thread_local PartialStatement st;
    static _Thread_local char completed[4 * MAX_FORMULA], problem[640], reading[DEFINITE_NOTE_BYTES];
    Verdict verdict = {UNSUPPORTED, 0, 0, 0, NULL, NULL, NULL, NULL, NULL, NULL};
    const char *answer = NULL;

    /* Ripartenza da zero per il nuovo enunciato, e parsing. */
    proof_reset();
    arena_used = arena_keep;
    atom_count = base_poly_count = atan_count = 0;
    failure = NULL;
    if (!parse_partial_statement(formula, &st)) { verdict.reason = syntax_error; return verdict; }
    if (failure) { verdict.reason = failure; return verdict; }
    if (st.request == ASKED_CRITICAL) return prove_critical(formula, &st);

    /* 35f. Una richiesta: la risposta, e l'enunciato completato riletto. */
    if (st.request) {
        const char *why = partial_answer(formula, &st, completed, sizeof completed, &answer, &verdict.outcome);
        if (why) { verdict.reason = why; failure = NULL; return verdict; }
        if (!parse_partial_statement(completed, &st) || failure || st.request) {
            unjustified_steps++;
            verdict.reason = "la risposta scritta non si rilegge con il lettore del programma";
            failure = NULL;
            return verdict;
        }
        proof_add("\\textbf{Solution.} $%s$.\n\n", answer);
    }

    /* 35h. Una scrittura della definitezza: la dimostrazione comincia
     * dicendo che cosa abbreviava, e lo ripete la nota del verdetto, vero o
     * falso che sia, perché le tesi decise sono i minori. */
    if (st.definite) definite_put_reading(st.definite);
    verdict = partial_decide(&st, verdict);
    if (st.definite && (verdict.outcome == PROVED || verdict.outcome == REFUTED)) verdict.note = definite_note(st.definite, verdict.note, reading);

    /* Che cosa se ne conclude, se l'enunciato scrive le condizioni del
     * secondo ordine (35g): dopo la dimostrazione, non dentro. */
    if (verdict.outcome == PROVED && partial_second_order(&st)) {
        proof_add("%s", SECOND_ORDER_REMARK);
        verdict.proof = proof_text;
    }
    if (!answer) return verdict;

    /* La risposta si consegna solo se l'enunciato completato è dimostrato.
     * Smentito, è un errore del programma: nello scrivere o nel rileggere. */
    if (verdict.outcome == PROVED) {
        verdict.outcome = SOLVED;
        verdict.detail = answer;
        verdict.note = verdict.note ? "dove le funzioni e le derivate sono definite; il certificato non copre i punti in cui la base di una radice o di una "
                                      "potenza con l'esponente non intero, o l'argomento di un valore assoluto, vale zero"
                                    : "dove le funzioni e le derivate sono definite";
        return verdict;
    }
    if (verdict.outcome == REFUTED) unjustified_steps++;
    snprintf(problem, sizeof problem, "la risposta calcolata, riletta come enunciato, non è confermata%s%s", verdict.reason ? ": " : "", verdict.reason ? verdict.reason : "");
    return (Verdict){NOT_PROVED, 0, 0, 0, problem, NULL, NULL, NULL, NULL, NULL};
}

/* Ritorna 1 se formula è un enunciato sulle funzioni di più variabili, dei
 * capitoli 35 e 36: contiene \partial o \nabla, che nessun altro lettore
 * conosce, oppure comincia con la definizione di una funzione,
 * f(x, y) = ..., seguita più avanti da \implies. Lo usa il capitolo 20. Usa
 * il lettore di token del parser, e lascia il suo stato da reimpostare. */
int uses_partial_notation(const char *formula) {
    for (const char *p = strchr(formula, '\\'); p; p = strchr(p + 1, '\\'))
        if ((strncmp(p, "\\partial", 8) == 0 && !isalpha((unsigned char)p[8])) || (strncmp(p, "\\nabla", 6) == 0 && !isalpha((unsigned char)p[6]))) return 1;
    return strstr(formula, "\\implies") && starts_with_definition(formula);
}
